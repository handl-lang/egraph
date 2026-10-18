//! The e-graph: union-find interned representation, matching, and
//! bounded equality saturation.
//!
//! Ports the spec's `EGraph` (`core.py`) with three deliberate
//! divergences, all named:
//!
//! * **Eager per-class match enumeration.** The spec streams matches
//!   through a frozen-read `_Epoch` so `apply_rule` can union between
//!   yielded substitutions while the enumeration keeps its call-time
//!   view. An eager per-class enumeration is the *same* observable
//!   semantics — the epoch machinery exists to reproduce exactly the
//!   list the pre-streaming matcher returned. We enumerate that list
//!   directly; memory stays bounded per class by the same
//!   [`EGraph::MATCH_CAP`] the spec applies.
//! * **Structural ordering** (`ENode: Ord`) replaces the set +
//!   `_member_key` rescan, and a typed [`Subst`] replaces the
//!   `"$attr:"` key-mangling. Same total order, same determinism.
//! * **`check`/`derive` see a resolved [`BoundEnv`]** computed before
//!   the hook runs — the hooks themselves are pure, so they can never
//!   mutate the graph mid-application.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::node::{ClassId, EClass, ENode};
use crate::pattern::{PNode, Prog, compile_pattern};
use crate::rewrite::{Application, BoundEnv, Derived, ProofEdge, Rewrite};
use crate::subst::Subst;
use crate::term::{Term, TermAttr};
use crate::union_find::UnionFind;
use crate::value::AttrValue;

/// `add_term` failed: a metavariable is not a term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddTermError {
    /// A `Term::Var` (or `TermAttr::Meta` attr) reached `add_term` —
    /// the spec would leaf-intern a bare `str`; we refuse (named wart).
    MetavarInTerm,
}

impl std::fmt::Display for AddTermError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AddTermError::MetavarInTerm => f.write_str("metavariable in a concrete term position"),
        }
    }
}

impl std::error::Error for AddTermError {}

/// Why a `run` stopped — the spec's `stats["stop"]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StopReason {
    /// All rules reached a fixed point.
    FixedPoint,
    /// `stop = "improving"`: extracted cost failed to strictly improve
    /// for `patience` consecutive iterations.
    Improving,
    /// The node cap fired.
    MaxNodes,
    /// The iteration cap fired.
    MaxIterations,
}

/// `run`'s stop policy — the spec's `stop=` argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stop {
    /// Saturate to the exact fixed point (default).
    FixedPoint,
    /// Lazy saturation: extract after every iteration and stop once
    /// the cost has not strictly improved for `patience` iterations.
    /// Heuristic — can stop before the true optimum. Requires
    /// [`RunOptions::cost_fn`].
    Improving,
}

/// Options for [`EGraph::run`].
pub struct RunOptions<'a> {
    /// Iteration cap (spec default 100).
    pub max_iterations: usize,
    /// Node cap (spec default 100_000).
    pub max_nodes: usize,
    /// `rule name -> max NEW enodes the rule may contribute over the
    /// graph's lifetime` — bounded saturation for combinatorially
    /// explosive rules. Accounting persists across `run` calls (the
    /// spec's `_budget_spent`).
    pub rule_budgets: BTreeMap<String, usize>,
    /// Stop policy.
    pub stop: Stop,
    /// Patience for `Stop::Improving` (spec default 3).
    pub patience: usize,
    /// The extraction cost function — required for `Stop::Improving`,
    /// ignored otherwise.
    pub cost_fn: Option<&'a mut dyn FnMut(&Term) -> f64>,
}

impl Default for RunOptions<'_> {
    fn default() -> Self {
        RunOptions {
            max_iterations: 100,
            max_nodes: 100_000,
            rule_budgets: BTreeMap::new(),
            stop: Stop::FixedPoint,
            patience: 3,
            cost_fn: None,
        }
    }
}

/// `run`'s return — the spec's `stats` dict, typed.
#[derive(Debug, Clone)]
pub struct SaturationStats {
    /// Iterations executed.
    pub iterations: usize,
    /// Final enode count.
    pub n_enodes: usize,
    /// Final e-class count.
    pub n_classes: usize,
    /// Recorded merge witnesses.
    pub n_proof_edges: usize,
    /// The graph's truncation level.
    pub truncation_level: u8,
    /// `rule name -> enodes contributed` for budgeted rules.
    pub rule_budgets: BTreeMap<String, usize>,
    /// Budgeted rules suspended at exhaustion.
    pub budget_suspended: Vec<String>,
    /// Why the run stopped.
    pub stop: StopReason,
    /// Iterations that lowered extracted cost (`Stop::Improving`).
    pub improved: Option<usize>,
}

/// `run` failed before iterating.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunError {
    /// `Stop::Improving` without a `cost_fn` (the spec's `ValueError`).
    ImprovingNeedsCost,
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunError::ImprovingNeedsCost => {
                f.write_str("stop='improving' needs a cost_fn to extract with")
            }
        }
    }
}

impl std::error::Error for RunError {}

/// Optional merge witnesses for [`EGraph::union_with`].
///
/// `witness` is the API for *non-local passes* — transformations that
/// offer a member no LHS pattern could produce. The pass synthesises a
/// concrete [`Rewrite`] justifying *this specific* merge (typically a
/// pointwise rule whose `lhs` is a member of `a`'s class and whose
/// `rhs` is the offered term), and the merge then replays like an
/// ordinary rule application: a synthetic application record keyed on
/// the offered term's root enode lets certificate machinery expand the
/// offered member through it. [`EGraph::offer`] is the canonical
/// ritual; `union_with(witness=...)` is the primitive underneath.
#[derive(Default)]
pub struct MergeInfo<'a> {
    /// The rule name to record on the [`ProofEdge`].
    pub rule: Option<Rc<str>>,
    /// The fired binding to record.
    pub subst: Option<Subst>,
    /// Free-form note.
    pub note: String,
    /// A replayable witness for a non-local merge.
    pub witness: Option<&'a Rewrite>,
}

/// One non-local offer — the spec's `_offer_witness` ritual.
///
/// Intern `rhs_term` (or take `rhs_eid`), mint a pointwise witness
/// `oldest_member -> offered_term`, then union the two classes under
/// it — making the asserted equality replayable instead of an
/// unwitnessed `egraph_dependent` merge.
#[derive(Default)]
pub struct Offer<'a> {
    /// The offered member's class, when already interned.
    pub rhs_eid: Option<ClassId>,
    /// The offered member as a term — interned under
    /// `term_provenance` when `rhs_eid` is absent.
    pub rhs_term: Option<&'a Term>,
    /// Explicit witness LHS (defaults to the class's *oldest* member —
    /// the term the e-graph saw first).
    pub lhs_term: Option<&'a Term>,
    /// Provenance prefix for the synthesised witness name.
    pub provenance: &'a str,
    /// The law the offer asserts.
    pub law: &'a str,
    /// `false` skips the witness — the merge happens either way.
    pub witness: bool,
    /// Note for the [`ProofEdge`].
    pub note: &'a str,
    /// Anchor for the witness name (defaults to `rhs_eid`).
    pub name_eid: Option<ClassId>,
    /// ε-law bound the witness certifies.
    pub error_bound: Option<f64>,
    /// Norm for `error_bound`.
    pub bound_norm: &'a str,
    /// Provenance tag for enodes `rhs_term` interns.
    pub term_provenance: &'a str,
}

/// The equality-saturation data structure.
///
/// `truncation_level` selects how much of the program ∞-groupoid is
/// materialised (the spec's dial):
///
/// * **1 — pure quotient.** Only the partition: no `ProofEdge`s, no
///   per-enode provenance. Minimal memory.
/// * **2 — witnesses (default).** One [`ProofEdge`] per merge plus
///   per-enode provenance (`enode_origin`/`enode_birth`/`enode_app`) —
///   the cascade-forgiveness data a downstream gauntlet consumes.
///
/// Level 3 (lazy coherences — `all_proofs`/`coherent_paths`) is proof-
/// reconstruction machinery, deferred: the level-2 record this port
/// ships is exactly what it replays.
pub struct EGraph {
    uf: UnionFind,
    pub(crate) classes: FxHashMap<ClassId, EClass>,
    node_to_class: FxHashMap<ENode, ClassId>,
    next_id: ClassId,
    /// Per-rule merge counts (`rule name -> merges`).
    pub rule_fires: BTreeMap<Rc<str>, u64>,
    /// The truncation dial — see the struct docs.
    pub truncation_level: u8,
    track: bool,
    merge_log: Vec<ProofEdge>,
    applications: Vec<Application>,
    enode_origin: FxHashMap<ENode, Rc<str>>,
    enode_birth: FxHashMap<ENode, ClassId>,
    /// `enode -> applications` index: the FIRST rule application whose
    /// instantiated RHS created the enode. First discovered witness
    /// wins — a hash-consed enode keeps the application that created it.
    enode_app: FxHashMap<ENode, usize>,
    /// Rule context while instantiating an RHS (provenance tagging).
    tag_rule: Option<Rc<str>>,
    /// Enodes born mid-instantiate (collected when `tag_rule` is set).
    collect: Option<Vec<ENode>>,
    /// The enode realising the last instantiated pattern's root.
    inst_last_enode: Option<ENode>,
    /// -- incremental saturation state --------------------------------
    /// Classes needing re-search (fresh enodes, merges, ancestors).
    dirty: BTreeSet<ClassId>,
    /// Inverted child->parent adjacency: `child class -> {classes
    /// holding an enode that references it}` — dirtiness propagates up.
    parents: FxHashMap<ClassId, BTreeSet<ClassId>>,
    /// `op name -> canonical class ids containing a member with that
    /// op`.
    op_classes: FxHashMap<Rc<str>, BTreeSet<ClassId>>,
    /// `(op, arity) -> canonical class ids` — the targeted-eligibility
    /// index: a compiled pattern only scans classes holding a member
    /// of the right head shape.
    opk: FxHashMap<(Rc<str>, usize), BTreeSet<ClassId>>,
    /// `pattern term -> compiled matcher` — each distinct LHS compiles
    /// once per e-graph.
    progs: FxHashMap<Term, Rc<Prog>>,
    /// Incremental congruence: `canonical enode -> owning class`.
    cong_owner: FxHashMap<ENode, ClassId>,
    /// `(class, enode)` pairs needing an ownership pass — ordered set:
    /// the drain order is the spec's `(_member_key, eid)` sort, and
    /// merge order decides which union root survives.
    cong_pend: BTreeSet<(ENode, ClassId)>,
    /// Rules already applied to the whole graph once — after the first
    /// pass the dirty frontier suffices.
    applied_rules: BTreeSet<Rc<str>>,
    /// Cumulative `rule name -> enodes contributed` under
    /// `rule_budgets` — persists across `run` calls.
    budget_spent: FxHashMap<Rc<str>, usize>,
    /// Per-`cost_fn` shared cost memos (`(TypeId, addr) -> memo`) —
    /// each extraction pass prices each distinct term once, total.
    cost_memos: FxHashMap<(std::any::TypeId, usize), FxHashMap<Term, f64>>,
}

impl EGraph {
    /// Per-class match-enumeration cap under an `enode_budget` (the
    /// spec's `_MATCH_CAP`): large enough to cover the substitutions a
    /// non-closure class realistically produces, small enough that a
    /// combinatorially-exploded class cannot dominate a pass.
    pub const MATCH_CAP: usize = 256;

    /// A tracking e-graph (truncation level 2 — witnesses).
    pub fn new() -> EGraph {
        EGraph::with_truncation_level(2)
    }

    /// A pure-quotient e-graph (truncation level 1 — no provenance).
    pub fn quotient() -> EGraph {
        EGraph::with_truncation_level(1)
    }

    /// An e-graph at an explicit truncation level (1 or 2).
    ///
    /// # Panics
    /// Level 3 (lazy coherences) is not ported — the level-2 record is
    /// what it would replay. Pass 1 or 2.
    pub fn with_truncation_level(level: u8) -> EGraph {
        assert!(
            level == 1 || level == 2,
            "truncation_level must be 1 or 2 (3 = lazy coherences, \
             deferred); got {level}"
        );
        EGraph {
            uf: UnionFind::default(),
            classes: FxHashMap::default(),
            node_to_class: FxHashMap::default(),
            next_id: 0,
            rule_fires: BTreeMap::new(),
            truncation_level: level,
            track: level >= 2,
            merge_log: Vec::new(),
            applications: Vec::new(),
            enode_origin: FxHashMap::default(),
            enode_birth: FxHashMap::default(),
            enode_app: FxHashMap::default(),
            tag_rule: None,
            collect: None,
            inst_last_enode: None,
            dirty: BTreeSet::new(),
            parents: FxHashMap::default(),
            op_classes: FxHashMap::default(),
            opk: FxHashMap::default(),
            progs: FxHashMap::default(),
            cong_owner: FxHashMap::default(),
            cong_pend: BTreeSet::new(),
            applied_rules: BTreeSet::new(),
            budget_spent: FxHashMap::default(),
            cost_memos: FxHashMap::default(),
        }
    }

    /// The number of live e-classes.
    pub fn n_classes(&self) -> usize {
        self.classes.len()
    }

    /// The number of interned enodes.
    pub fn n_enodes(&self) -> usize {
        self.node_to_class.len()
    }

    /// The canonical e-class id of `eid` (path halving).
    pub fn find(&mut self, eid: ClassId) -> ClassId {
        self.uf.find(eid)
    }

    /// Read-only canonical lookup (no path compression).
    pub fn find_ref(&self, eid: ClassId) -> ClassId {
        self.uf.find_ref(eid)
    }

    /// The e-class containing `eid`.
    pub fn get_class(&mut self, eid: ClassId) -> &EClass {
        let r = self.find(eid);
        &self.classes[&r]
    }

    /// Read-only e-class lookup by *canonical* id.
    pub fn class(&self, canonical: ClassId) -> Option<&EClass> {
        self.classes.get(&canonical)
    }

    /// Add a leaf identified by `key`; returns its canonical class.
    pub fn add_leaf(&mut self, key: &str, provenance: Option<&str>) -> ClassId {
        let enode = ENode::leaf(key);
        if let Some(&eid) = self.node_to_class.get(&enode) {
            return self.find(eid);
        }
        self.insert_enode(enode, provenance.map(Rc::from))
    }

    /// Add an e-node with already-resolved child e-class ids.
    ///
    /// `provenance` optionally names what introduced the enode; enodes
    /// born inside a rule application are tagged with the firing rule
    /// regardless.
    pub fn add_enode(
        &mut self,
        op: &str,
        children: &[ClassId],
        attrs: Vec<(Rc<str>, AttrValue)>,
        provenance: Option<&str>,
    ) -> ClassId {
        let canon: Vec<ClassId> = children.iter().map(|&c| self.find(c)).collect();
        let enode = ENode::new(op, canon, attrs);
        if let Some(&eid) = self.node_to_class.get(&enode) {
            return self.find(eid);
        }
        self.insert_enode(enode, provenance.map(Rc::from))
    }

    /// Intern `enode` in a fresh singleton class — the spec's
    /// `_add_enode`, incremental-search bookkeeping included.
    fn insert_enode(&mut self, enode: ENode, provenance: Option<Rc<str>>) -> ClassId {
        let eid = self.next_id;
        self.next_id += 1;
        debug_assert_eq!(self.uf.make(), eid);
        let mut ec = EClass::new(eid);
        ec.nodes.insert(enode.clone());
        self.classes.insert(eid, ec);
        self.node_to_class.insert(enode.clone(), eid);
        // Incremental-search bookkeeping: a fresh class must be
        // searched (its enode may match rules), it contributes its op
        // to the class indices, and each child class gains a parent
        // edge so future changes below propagate dirtiness upward.
        self.dirty.insert(eid);
        self.op_classes
            .entry(enode.op.clone())
            .or_default()
            .insert(eid);
        self.opk
            .entry((enode.op.clone(), enode.children.len()))
            .or_default()
            .insert(eid);
        self.cong_pend.insert((enode.clone(), eid));
        for &c in enode.children.iter() {
            let canon = self.find(c);
            self.parents.entry(canon).or_default().insert(eid);
        }
        if self.track {
            self.enode_birth.insert(enode.clone(), eid);
            let origin = self
                .tag_rule
                .clone()
                .or(provenance)
                .unwrap_or_else(|| Rc::from("external"));
            self.enode_origin.insert(enode.clone(), origin);
            if let Some(collect) = &mut self.collect {
                collect.push(enode);
            }
        }
        eid
    }

    /// Add a term to the e-graph — the spec's `add_term` minus the
    /// DAG-walk memo (Rust terms are trees, not shared DAG objects).
    ///
    /// `provenance` tags every enode the term creates (`"input"` for
    /// the source program).
    ///
    /// # Errors
    /// [`AddTermError::MetavarInTerm`] when the term carries a
    /// `Var`/`Meta` — a metavariable is a pattern, not a term.
    pub fn add_term(&mut self, term: &Term, provenance: &str) -> Result<ClassId, AddTermError> {
        match term {
            Term::Var(_) => Err(AddTermError::MetavarInTerm),
            Term::Leaf(key) => Ok(self.add_leaf(key, Some(provenance))),
            Term::Op(o) => {
                let mut child_eids = Vec::with_capacity(o.args.len());
                for a in o.args.iter() {
                    child_eids.push(self.add_term(a, provenance)?);
                }
                let mut attrs = Vec::with_capacity(o.attrs.len());
                for (k, v) in o.attrs.iter() {
                    match v {
                        TermAttr::Lit(v) => attrs.push((k.clone(), v.clone())),
                        TermAttr::Meta(_) => {
                            return Err(AddTermError::MetavarInTerm);
                        }
                    }
                }
                let canon: Vec<ClassId> = child_eids.iter().map(|&c| self.find(c)).collect();
                let enode = ENode::new(o.op.clone(), canon, attrs);
                if let Some(&eid) = self.node_to_class.get(&enode) {
                    return Ok(self.find(eid));
                }
                Ok(self.insert_enode(enode, Some(Rc::from(provenance))))
            }
        }
    }

    /// Merge the e-classes of `a` and `b`; `true` if they differed.
    pub fn union(&mut self, a: ClassId, b: ClassId) -> bool {
        self.union_with(a, b, &MergeInfo::default())
    }

    /// Merge with witnesses — see [`MergeInfo`].
    pub fn union_with(&mut self, a: ClassId, b: ClassId, info: &MergeInfo) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        if !self.uf.union(ra, rb) {
            return false;
        }
        let new_canon = self.find(ra);
        let old_canon = if new_canon == rb { ra } else { rb };
        // Detach the absorbed class, fold its members into the winner.
        let source = self.classes.remove(&old_canon).expect("absorbed class");
        let moved: Vec<ENode> = source.nodes.iter().cloned().collect();
        {
            let target = self.classes.get_mut(&new_canon).expect("canonical class");
            target.nodes.extend(source.nodes);
            target.invalidate();
        }
        // -- incremental-search bookkeeping --------------------------
        // The merged class gained enodes, and every enode anywhere
        // whose child resolved to `old_canon` now resolves to
        // `new_canon` — both can enable new matches, and those can in
        // turn enable matches in their parents. The affected region is
        // exactly the upward closure over child->parent edges.
        self.dirty.insert(new_canon);
        if let Some(p_old) = self.parents.remove(&old_canon) {
            self.parents.entry(new_canon).or_default().extend(&p_old);
            // Incremental congruence: the enodes that re-key because
            // their child resolved to `old_canon` are exactly the
            // direct parents' members mentioning it.
            for p0 in p_old {
                let pc = self.find(p0);
                let pending: Vec<ENode> = self.classes[&pc]
                    .nodes
                    .iter()
                    .filter(|n| n.children.contains(&old_canon))
                    .cloned()
                    .collect();
                for n in pending {
                    self.cong_pend.insert((n, pc));
                }
            }
        }
        for n in &moved {
            if let Some(oc) = self.op_classes.get_mut(&n.op) {
                oc.remove(&old_canon);
                oc.insert(new_canon);
            }
            let key = (n.op.clone(), n.children.len());
            if let Some(ok) = self.opk.get_mut(&key) {
                ok.remove(&old_canon);
                ok.insert(new_canon);
            }
        }
        let mut stack = vec![new_canon];
        while let Some(c) = stack.pop() {
            let ps: Vec<ClassId> = self
                .parents
                .get(&c)
                .map(|s| s.iter().copied().collect())
                .unwrap_or_default();
            for p0 in ps {
                let p = self.find(p0);
                // `p in dirty` prune is sound: an already-dirty class's
                // ancestors were dirtied when it became dirty.
                if p == c || self.dirty.contains(&p) {
                    continue;
                }
                self.dirty.insert(p);
                stack.push(p);
            }
        }
        if self.track {
            if let Some(witness) = info.witness {
                // Locate the offered term's root enode and register a
                // synthetic application so target-expansion machinery
                // can replay this merge as an ordinary rule step.
                if let (_, Some(w_en)) = self.locate(&witness.rhs, None) {
                    let app_idx = self.applications.len();
                    let ma = self.find(ra);
                    let mb = self.find(rb);
                    self.applications.push(Application {
                        rule: witness.name.clone(),
                        matched_eid: ma,
                        rhs_eid: mb,
                        subst: info.subst.clone().unwrap_or_default(),
                        rhs_root_enode: Some(w_en.clone()),
                    });
                    self.enode_app.entry(w_en).or_insert(app_idx);
                }
            }
            self.merge_log.push(ProofEdge {
                rule: info
                    .rule
                    .clone()
                    .or_else(|| info.witness.map(|w| w.name.clone())),
                a: ra,
                b: rb,
                subst: info.subst.clone().unwrap_or_default(),
                note: info.note.clone(),
            });
        }
        true
    }

    // -- proof-log accessors -------------------------------------------

    /// Every recorded merge witness, in order of application.
    pub fn merge_log(&self) -> &[ProofEdge] {
        &self.merge_log
    }

    /// The number of recorded proof edges.
    pub fn n_proof_edges(&self) -> usize {
        self.merge_log.len()
    }

    /// Every rule application recorded during saturation.
    pub fn applications(&self) -> &[Application] {
        &self.applications
    }

    /// The index of the application that first created `enode`, if any
    /// — the `_enode_app` port: the cascade-forgiveness hook a
    /// certificate walk uses to expand a member through its producing
    /// rule.
    pub fn enode_app(&self, enode: &ENode) -> Option<usize> {
        self.enode_app.get(enode).copied()
    }

    /// The rule/pass that introduced `enode`, if tracked.
    pub fn enode_origin(&self, enode: &ENode) -> Option<&Rc<str>> {
        self.enode_origin.get(enode)
    }

    /// The class id `enode` was born into, if tracked.
    pub fn enode_birth(&self, enode: &ENode) -> Option<ClassId> {
        self.enode_birth.get(enode).copied()
    }

    // -- non-local offers: the pointwise-witness ritual -----------------

    /// Offer a non-locally-computed member under a pointwise witness —
    /// the spec's `_offer_witness`, the canonical ritual behind every
    /// non-local pass. Returns [`EGraph::union_with`]'s result.
    ///
    /// # Errors / panics
    /// `add_term` errors propagate verbatim (the offered term must be
    /// concrete).
    pub fn offer(&mut self, cid: ClassId, o: &Offer) -> Result<bool, AddTermError> {
        let rhs_eid = match o.rhs_eid {
            Some(e) => e,
            None => self.add_term(
                o.rhs_term.expect("offer needs rhs_eid or rhs_term"),
                if o.term_provenance.is_empty() {
                    "input"
                } else {
                    o.term_provenance
                },
            )?,
        };
        let wit = if o.witness {
            self.pointwise_witness(cid, rhs_eid, o)
        } else {
            None
        };
        Ok(self.union_with(
            cid,
            rhs_eid,
            &MergeInfo {
                witness: wit.as_ref(),
                note: o.note.to_string(),
                ..MergeInfo::default()
            },
        ))
    }

    /// Synthesise the pointwise [`Rewrite`] for an offered member —
    /// the spec's `_pointwise_witness`. `None` when either side is
    /// unresolvable (a degenerate fully-cyclic class), so the merge
    /// proceeds witness-free rather than carrying a fabricated
    /// certificate.
    fn pointwise_witness(&mut self, cid: ClassId, rhs_eid: ClassId, o: &Offer) -> Option<Rewrite> {
        let rhs_term = match o.rhs_term {
            Some(t) => t.clone(),
            None => self.any_term(rhs_eid)?,
        };
        let src = match o.lhs_term {
            Some(t) => t.clone(),
            None => {
                let canon = self.find(cid);
                self.oldest_term(canon)?
            }
        };
        let mut w = Rewrite::new(
            format!("{}#{}", o.provenance, o.name_eid.unwrap_or(rhs_eid)),
            src,
            rhs_term,
        )
        .with_law(o.law);
        w.error_bound = o.error_bound;
        if !o.bound_norm.is_empty() {
            w.bound_norm = o.bound_norm.to_string();
        }
        Some(w)
    }

    // -- pattern matching ----------------------------------------------
    //
    // Patterns compile once per e-graph into a `Prog` decision tree and
    // enumerate EAGERLY per candidate class — identical observable
    // semantics to the spec's frozen-epoch streaming (which exists to
    // reproduce the eager list under interleaved unions).

    /// The compiled matcher for `pattern` (cached per graph).
    fn prog_for(&mut self, pattern: &Term) -> Rc<Prog> {
        if let Some(p) = self.progs.get(pattern) {
            return p.clone();
        }
        let prog = Rc::new(compile_pattern(pattern));
        self.progs.insert(pattern.clone(), prog.clone());
        prog
    }

    /// Every substitution matching `pattern` at e-class `eid`.
    ///
    /// `max_results` bounds the enumeration — deterministic (first-
    /// found wins) and used by the saturation loop to enforce per-rule
    /// expansion budgets inside giant e-classes. The bounded path ports
    /// the spec's `_m_bounded` *exactly*, including the quirk that an
    /// e-node whose enumeration crosses the cap contributes ZERO
    /// substitutions.
    pub fn matches(
        &mut self,
        pattern: &Term,
        eid: ClassId,
        max_results: Option<usize>,
    ) -> Vec<Subst> {
        let prog = self.prog_for(pattern);
        let mut out = Vec::new();
        match max_results {
            Some(limit) => self.m_bounded(&prog.root, eid, Subst::default(), &mut out, limit),
            None => self.m_stream(&prog.root, eid, Subst::default(), &mut out),
        }
        out
    }

    /// Member enodes of `eid`'s class carrying `op`, in canonical
    /// order — the spec's `_nodes_of`/`_mnodes` (`by_op` lazily-indexed,
    /// invalidated on every `nodes` mutation).
    fn nodes_of(&mut self, eid: ClassId, op: &str) -> Rc<Vec<ENode>> {
        let eid = self.find(eid);
        let ec = self.classes.get_mut(&eid).expect("live class");
        if ec.by_op.is_none() {
            // BTreeSet iteration IS the canonical member order.
            let mut lists: FxHashMap<Rc<str>, Vec<ENode>> = FxHashMap::default();
            for n in &ec.nodes {
                lists.entry(n.op.clone()).or_default().push(n.clone());
            }
            ec.by_op = Some(lists.into_iter().map(|(k, v)| (k, Rc::new(v))).collect());
        }
        ec.by_op
            .as_ref()
            .and_then(|bo| bo.get(op).cloned())
            .unwrap_or_else(|| Rc::new(Vec::new()))
    }

    /// The unbounded enumeration — eager form of the spec's
    /// `_m_stream`/`_m_pos` DFS. `base` is the incoming partial
    /// substitution; each complete match pushes a clone.
    fn m_stream(&mut self, pn: &PNode, eid: ClassId, base: Subst, out: &mut Vec<Subst>) {
        match pn {
            PNode::Var(name) => {
                let ce = self.find(eid);
                match base.terms.get(name) {
                    Some(&prev) if prev == ce => out.push(base),
                    Some(_) => {}
                    None => {
                        let mut b = base;
                        b.terms.insert(name.clone(), ce);
                        out.push(b);
                    }
                }
            }
            PNode::Leaf { enode, .. } => {
                if let Some(&nid) = self.node_to_class.get(enode)
                    && self.find(nid) == self.find(eid)
                {
                    out.push(base);
                }
            }
            PNode::Op {
                op,
                children,
                attrs,
                keyset,
                ..
            } => {
                let ce = self.find(eid);
                let members = self.nodes_of(ce, op);
                for node in members.iter() {
                    if node.children.len() != children.len() {
                        continue;
                    }
                    if !node.attr_names_eq(keyset) {
                        continue;
                    }
                    // Attribute matching: literal values must `match_eq`
                    // — numerically lenient, the spec's `!=` contract.
                    // `Meta` names bind into `Subst::attrs` and must be
                    // consistent everywhere they repeat.
                    let mut s = base.clone();
                    let mut ok = true;
                    for (k, pv) in attrs.iter() {
                        let nv = node.attr(k).expect("keyset-gated");
                        match pv {
                            TermAttr::Meta(name) => match s.attrs.get(name) {
                                Some(bound) if !bound.match_eq(nv) => {
                                    ok = false;
                                    break;
                                }
                                Some(_) => {}
                                None => {
                                    s.attrs.insert(name.clone(), nv.clone());
                                }
                            },
                            TermAttr::Lit(pv) if !pv.match_eq(nv) => {
                                ok = false;
                                break;
                            }
                            TermAttr::Lit(_) => {}
                        }
                    }
                    if !ok {
                        continue;
                    }
                    // Thread the incoming bindings so shared
                    // metavariables are checked for consistency at
                    // every position.
                    let mut child_substs = vec![s];
                    for (i, cp) in children.iter().enumerate() {
                        let mut new_substs = Vec::new();
                        for cs in child_substs {
                            self.m_stream(cp, node.children[i], cs, &mut new_substs);
                        }
                        if new_substs.is_empty() {
                            child_substs = new_substs;
                            break;
                        }
                        child_substs = new_substs;
                    }
                    out.extend(child_substs);
                }
            }
        }
    }

    /// The bounded enumeration — the spec's `_m_bounded`, quirk and
    /// all: an e-node whose enumeration crosses `limit` contributes
    /// ZERO substitutions (the `ok = false` drop), while earlier nodes
    /// keep theirs. `results` never exceeds `limit`.
    fn m_bounded(
        &mut self,
        pn: &PNode,
        eid: ClassId,
        subst: Subst,
        results: &mut Vec<Subst>,
        limit: usize,
    ) {
        if results.len() >= limit {
            return;
        }
        match pn {
            PNode::Var(name) => {
                let eid = self.find(eid);
                match subst.terms.get(name) {
                    Some(&prev) if prev == eid => results.push(subst),
                    Some(_) => {}
                    None => {
                        let mut s = subst;
                        s.terms.insert(name.clone(), eid);
                        results.push(s);
                    }
                }
            }
            PNode::Op {
                op,
                children,
                attrs,
                keyset,
                ..
            } => {
                let eid = self.find(eid);
                let members = self.nodes_of(eid, op);
                for node in members.iter() {
                    // NB: no cap re-check here — `results` only reaches
                    // `limit` inside the `ok` arm below, which returns
                    // immediately, so a loop-head guard can never fire
                    // (the spec's comment, verbatim).
                    if node.children.len() != children.len() {
                        continue;
                    }
                    if !node.attr_names_eq(keyset) {
                        continue;
                    }
                    // Same `match_eq` attr compare as `m_stream`.
                    let mut attr_substs: Vec<Subst> = vec![subst.clone()];
                    let mut attr_ok = true;
                    for (k, pv) in attrs.iter() {
                        let nv = node.attr(k).expect("keyset-gated");
                        match pv {
                            TermAttr::Meta(name) => {
                                let mut nxt = Vec::with_capacity(attr_substs.len());
                                for cs in attr_substs {
                                    match cs.attrs.get(name) {
                                        Some(bound) if bound.match_eq(nv) => {
                                            nxt.push(cs);
                                        }
                                        Some(_) => {}
                                        None => {
                                            let mut cc = cs;
                                            cc.attrs.insert(name.clone(), nv.clone());
                                            nxt.push(cc);
                                        }
                                    }
                                }
                                attr_substs = nxt;
                            }
                            TermAttr::Lit(pv) if !pv.match_eq(nv) => {
                                attr_ok = false;
                                break;
                            }
                            TermAttr::Lit(_) => {}
                        }
                        if attr_substs.is_empty() {
                            attr_ok = false;
                            break;
                        }
                    }
                    if !attr_ok {
                        continue;
                    }
                    let mut child_substs = attr_substs;
                    let mut ok = true;
                    for (i, cp) in children.iter().enumerate() {
                        let mut new_substs = Vec::new();
                        for cs in child_substs.iter() {
                            if results.len() + new_substs.len() >= limit {
                                ok = false;
                                break;
                            }
                            let mut child_results = Vec::new();
                            self.m_bounded(
                                cp,
                                node.children[i],
                                cs.clone(),
                                &mut child_results,
                                limit,
                            );
                            new_substs.extend(child_results);
                        }
                        if !ok || new_substs.is_empty() {
                            ok = false;
                            break;
                        }
                        child_substs = new_substs;
                    }
                    if ok {
                        let room = limit - results.len();
                        results.extend(child_substs.into_iter().take(room));
                        if results.len() >= limit {
                            return;
                        }
                    }
                }
            }
            PNode::Leaf { enode, .. } => {
                let eid = self.find(eid);
                if let Some(&nid) = self.node_to_class.get(enode)
                    && self.find(nid) == eid
                {
                    results.push(subst);
                }
            }
        }
    }

    // -- rebuild --------------------------------------------------------

    /// Canonicalize children and merge duplicates.
    ///
    /// `classes` optionally restricts the pass to a set of class ids —
    /// the dirty frontier the run loop supplies. An unrestricted pass
    /// (`None`) also closes congruence (the whole-graph rescan, used
    /// once at the end of `run`).
    pub fn rebuild(&mut self, classes: Option<BTreeSet<ClassId>>) -> bool {
        match classes {
            Some(ids) => self.canonicalise(&ids),
            None => {
                let ids: BTreeSet<ClassId> = self.classes.keys().copied().collect();
                let changed = self.canonicalise(&ids);
                self.close_congruence() || changed
            }
        }
    }

    /// Re-canonicalize each class's enode children (one pass).
    fn canonicalise(&mut self, ids: &BTreeSet<ClassId>) -> bool {
        let mut changed = false;
        let mut seen = BTreeSet::new();
        for &eid0 in ids {
            let eid = self.find(eid0);
            if !seen.insert(eid) || !self.classes.contains_key(&eid) {
                continue;
            }
            let nodes: Vec<ENode> = self.classes[&eid].nodes.iter().cloned().collect();
            let mut new_nodes = BTreeSet::new();
            for node in nodes {
                let (nn, node_changed) = self.canonical_node(&node, eid);
                changed = changed || node_changed;
                new_nodes.insert(nn);
            }
            let ec = self.classes.get_mut(&eid).expect("seen class");
            if new_nodes != ec.nodes {
                ec.nodes = new_nodes;
                ec.invalidate();
            }
        }
        changed
    }

    /// Canonicalize one enode's children; return `(enode, changed)`.
    fn canonical_node(&mut self, node: &ENode, eid: ClassId) -> (ENode, bool) {
        if node.children.is_empty() {
            return (node.clone(), false);
        }
        let canon: Vec<ClassId> = node.children.iter().map(|&c| self.find(c)).collect();
        if canon.as_slice() == node.children.as_ref() {
            return (node.clone(), false);
        }
        for &c in &canon {
            let cc = self.find(c);
            self.parents.entry(cc).or_default().insert(eid);
        }
        let nn = ENode {
            op: node.op.clone(),
            children: Rc::from(canon),
            attrs: node.attrs.clone(),
        };
        if self.track {
            self.inherit_provenance(node, &nn, eid);
        }
        // Incremental congruence: `node` re-keyed out of `eid` — drop
        // its ownership claim if this class held it, and queue the
        // canonical `nn` for the ownership worklist.
        if let Some(&prev) = self.cong_owner.get(node)
            && self.find(prev) == eid
        {
            self.cong_owner.remove(node);
        }
        self.cong_pend.insert((nn.clone(), eid));
        (nn, true)
    }

    /// Copy `node`'s tracking metadata onto its canonical `nn`.
    fn inherit_provenance(&mut self, node: &ENode, nn: &ENode, eid: ClassId) {
        if let Some(o) = self.enode_origin.get(node).cloned() {
            self.enode_origin.entry(nn.clone()).or_insert(o);
        }
        if let Some(&b) = self.enode_birth.get(node) {
            self.enode_birth.entry(nn.clone()).or_insert(b);
        }
        if let Some(&a) = self.enode_app.get(node) {
            self.enode_app.entry(nn.clone()).or_insert(a);
        }
        self.node_to_class.entry(nn.clone()).or_insert(eid);
    }

    /// `node` with canonically-resolved children.
    fn cong_canon(&mut self, node: &ENode) -> ENode {
        let canon: Vec<ClassId> = node.children.iter().map(|&c| self.find(c)).collect();
        if canon.as_slice() == node.children.as_ref() {
            return node.clone();
        }
        ENode {
            op: node.op.clone(),
            children: Rc::from(canon),
            attrs: node.attrs.clone(),
        }
    }

    /// Union e-classes whose canonical enodes coincide — the spec's
    /// incremental `_close_congruence`.
    ///
    /// The worklist drains in canonical order — `BTreeSet<(ENode,
    /// ClassId)>` iterates in exactly the spec's `(_member_key(enode),
    /// eid)` drain order — because the batch's merge order decides
    /// which union root survives, which orders the dirty frontier,
    /// which under `rule_budgets` orders budget consumption.
    fn close_congruence(&mut self) -> bool {
        let mut changed = false;
        loop {
            if self.cong_pend.is_empty() {
                return changed;
            }
            let batch: Vec<(ENode, ClassId)> =
                std::mem::take(&mut self.cong_pend).into_iter().collect();
            let mut merges: Vec<(ClassId, ClassId)> = Vec::new();
            for (node0, eid0) in batch {
                let eid = self.find(eid0);
                if !self.classes.contains_key(&eid) {
                    continue;
                }
                let node = self.cong_canon(&node0);
                if node != node0 {
                    // Re-keyed out of the class — apply the
                    // canonicalisation pointwise.
                    let replaced = {
                        let eclass = self.classes.get_mut(&eid).expect("live");
                        if eclass.nodes.remove(&node0) {
                            eclass.nodes.insert(node.clone());
                            eclass.invalidate();
                            true
                        } else {
                            false
                        }
                    };
                    if replaced {
                        if self.track {
                            // `inherit_provenance` also hash-conses `nn`
                            // into `node_to_class`.
                            self.inherit_provenance(&node0, &node, eid);
                        }
                        for &c in node.children.iter() {
                            let cc = self.find(c);
                            self.parents.entry(cc).or_default().insert(eid);
                        }
                        // Drop the pre-canonical form's claim — a claim
                        // can only belong to the class holding the node.
                        self.cong_owner.remove(&node0);
                    }
                    if !self.classes[&eid].nodes.contains(&node) {
                        continue;
                    }
                } else if !self.classes[&eid].nodes.contains(&node) {
                    // Stale worklist item — the enode is gone.
                    continue;
                }
                let prev = *self.cong_owner.entry(node).or_insert(eid);
                if self.find(prev) != eid {
                    merges.push((prev, eid));
                }
            }
            if merges.is_empty() {
                return changed;
            }
            changed = true;
            for (a, b) in merges {
                self.union(a, b);
            }
        }
    }

    // -- rule application -------------------------------------------------

    /// Instantiate a compiled pattern (RHS) under a substitution.
    ///
    /// `inst_last_enode` records the enode realising the pattern's root
    /// (post-order: the outermost call assigns last) — `None` when the
    /// RHS is a bare metavariable/leaf binding. Returns `None` on a
    /// binding that cannot realise the RHS — the spec's `KeyError`
    /// skip: the firing cannot be built, so it is skipped like a
    /// `check` veto.
    fn instantiate(&mut self, pn: &PNode, subst: &Subst) -> Option<ClassId> {
        match pn {
            PNode::Var(name) => {
                self.inst_last_enode = None;
                subst.terms.get(name).copied()
            }
            PNode::Leaf { key, enode } => {
                let eid = self.add_leaf(key.as_ref(), None);
                self.inst_last_enode = Some(enode.clone());
                Some(eid)
            }
            PNode::Op {
                op,
                children,
                attrs,
                ..
            } => {
                let mut child_eids = Vec::with_capacity(children.len());
                for cp in children {
                    child_eids.push(self.instantiate(cp, subst)?);
                }
                let mut flat = Vec::with_capacity(attrs.len());
                for (k, v) in attrs.iter() {
                    flat.push((
                        k.clone(),
                        match v {
                            TermAttr::Meta(name) => subst
                                .attrs
                                .get(name)
                                .cloned()
                                // Spec quirk ported verbatim: an
                                // unbound attr metavar instantiates to
                                // the literal metavar string
                                // (`subst.get("$attr:"+v, v)`).
                                .unwrap_or_else(|| AttrValue::Str(name.clone())),
                            TermAttr::Lit(v) => v.clone(),
                        },
                    ));
                }
                let canon: Vec<ClassId> = child_eids.iter().map(|&c| self.find(c)).collect();
                let enode = ENode::new(op.clone(), canon, flat);
                let eid = if let Some(&eid) = self.node_to_class.get(&enode) {
                    self.find(eid)
                } else {
                    self.insert_enode(enode.clone(), None)
                };
                self.inst_last_enode = Some(enode);
                Some(eid)
            }
        }
    }

    /// Return any acyclic representative term of an e-class.
    ///
    /// Prefers leaf nodes; members are scanned in canonical order so
    /// "any" member is the same member in every process.
    pub fn any_term(&mut self, eid: ClassId) -> Option<Term> {
        let mut memo = FxHashMap::default();
        self.any_term_rec(eid, &mut BTreeSet::new(), &mut memo)
    }

    pub(crate) fn any_term_rec(
        &mut self,
        eid: ClassId,
        seen: &mut BTreeSet<ClassId>,
        memo: &mut FxHashMap<ClassId, Option<Term>>,
    ) -> Option<Term> {
        let eid = self.find(eid);
        let nodes: Vec<ENode> = self.classes[&eid].nodes.iter().cloned().collect();
        for node in &nodes {
            if node.is_leaf() {
                let key = node.leaf_key().unwrap_or("??").to_string();
                return Some(Term::leaf(key));
            }
        }
        if let Some(hit) = memo.get(&eid) {
            return hit.clone();
        }
        // `seen` is an ancestor-PATH set (the spec's `_seen` frozenset
        // copy): siblings share the parent's ancestry but not each
        // other's subtrees — remove on the way out.
        seen.insert(eid);
        let mut result = None;
        for node in nodes {
            let mut args = Vec::with_capacity(node.children.len());
            let mut ok = true;
            for &c in node.children.iter() {
                let canon = self.find(c);
                if canon == eid || seen.contains(&canon) {
                    ok = false;
                    break;
                }
                let Some(t) = self.any_term_rec(canon, seen, memo) else {
                    ok = false;
                    break;
                };
                args.push(t);
            }
            if ok {
                let attrs: Vec<(Rc<str>, TermAttr)> = node
                    .attrs
                    .iter()
                    .map(|(k, v)| (k.clone(), TermAttr::Lit(v.clone())))
                    .collect();
                let t = Term::op(node.op.clone(), Rc::from(args), attrs);
                memo.insert(eid, Some(t.clone()));
                result = Some(t);
                break;
            }
        }
        seen.remove(&eid);
        result
    }

    /// The smallest acyclic member of an e-class — `(term, size)`;
    /// fewest ops wins, members scanned in canonical order with strict
    /// `<` so equal-size members resolve identically every run.
    pub(crate) fn min_term(
        &mut self,
        eid: ClassId,
        memo: &mut FxHashMap<ClassId, Option<(Term, f64)>>,
        seen: &mut BTreeSet<ClassId>,
    ) -> Option<(Term, f64)> {
        let eid = self.find(eid);
        let nodes: Vec<ENode> = self.classes[&eid].nodes.iter().cloned().collect();
        for node in &nodes {
            if node.is_leaf() {
                let key = node.leaf_key().unwrap_or("??").to_string();
                let res = (Term::leaf(key), 1.0);
                memo.insert(eid, Some(res.clone()));
                return Some(res);
            }
        }
        if let Some(hit) = memo.get(&eid) {
            return hit.clone();
        }
        if seen.contains(&eid) {
            return None;
        }
        // Ancestor-path set — see `any_term_rec`.
        seen.insert(eid);
        let mut best: Option<(Term, f64)> = None;
        for node in nodes {
            let mut args = Vec::with_capacity(node.children.len());
            let mut sz = 1.0f64;
            let mut ok = true;
            for &c in node.children.iter() {
                let canon = self.find(c);
                if canon == eid || seen.contains(&canon) {
                    ok = false;
                    break;
                }
                let Some((t, s)) = self.min_term(canon, memo, seen) else {
                    ok = false;
                    break;
                };
                args.push(t);
                sz += s;
            }
            if ok && best.as_ref().is_none_or(|b| sz < b.1) {
                let attrs: Vec<(Rc<str>, TermAttr)> = node
                    .attrs
                    .iter()
                    .map(|(k, v)| (k.clone(), TermAttr::Lit(v.clone())))
                    .collect();
                best = Some((Term::op(node.op.clone(), Rc::from(args), attrs), sz));
            }
        }
        seen.remove(&eid);
        if best.is_some() {
            memo.insert(eid, best.clone());
        }
        best
    }

    /// Resolve a member for rewrite side conditions — the spec's
    /// `_any_term_cached`: the class's *minimum-size* member, memoised
    /// in the class so the same term survives across `apply_rule`
    /// calls and iterations.
    pub(crate) fn min_term_cached(&mut self, eid: ClassId) -> Option<Term> {
        let eid = self.find(eid);
        if let Some((t, _)) = &self.classes[&eid].min_term {
            return Some(t.clone());
        }
        let mut memo = FxHashMap::default();
        let t = self.min_term(eid, &mut memo, &mut BTreeSet::new());
        if let Some((t, s)) = t {
            self.classes.get_mut(&eid).expect("live").min_term = Some((t.clone(), s));
            Some(t)
        } else {
            None
        }
    }

    /// Cheap child-op eligibility check for one candidate class — the
    /// spec's `_head_ok`: `true` iff some `head_op` member has, at every
    /// Op-typed child position of the pattern, a child class containing
    /// a member of the required op.
    fn head_ok(&mut self, prog: &Prog, eid: ClassId) -> bool {
        let head_op = prog.head_op.as_ref().expect("child_reqs on op root");
        let members = self.nodes_of(eid, head_op);
        'outer: for node in members.iter() {
            if node.children.len() != prog.head_arity {
                continue;
            }
            for &(i, ref op) in &prog.child_reqs {
                let cc = self.find(node.children[i]);
                let Some(set) = self.op_classes.get(op) else {
                    continue 'outer;
                };
                if !set.contains(&cc) {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    /// E-classes a rule's compiled LHS could possibly match at — the
    /// spec's `_candidate_classes`. `search = None` scans the whole
    /// graph; a set restricts to the dirty frontier. Op-rooted
    /// patterns filter through the `(op, arity)` index plus `head_ok`.
    fn candidate_classes(
        &mut self,
        prog: &Prog,
        search: Option<&BTreeSet<ClassId>>,
    ) -> Vec<ClassId> {
        let eligible: Option<BTreeSet<ClassId>> = if let Some(op) = &prog.head_op {
            let raw: Vec<ClassId> = self
                .opk
                .get(&(op.clone(), prog.head_arity))
                .map(|s| s.iter().copied().collect())
                .unwrap_or_default();
            Some(raw.into_iter().map(|c| self.find(c)).collect())
        } else if let Some(key) = &prog.leaf_key {
            let leaf = ENode::leaf(key.clone());
            match self.node_to_class.get(&leaf) {
                Some(&leid) => {
                    let c = self.find(leid);
                    Some(BTreeSet::from([c]))
                }
                None => Some(BTreeSet::new()),
            }
        } else {
            None
        };
        let ids: Vec<ClassId> = match search {
            None => self.classes.keys().copied().collect(),
            Some(s) => s.iter().copied().collect(),
        };
        let mut out = Vec::new();
        for eid0 in ids {
            let eid = self.find(eid0);
            if let Some(el) = &eligible
                && !el.contains(&eid)
            {
                continue;
            }
            if !prog.child_reqs.is_empty() && !self.head_ok(prog, eid) {
                continue;
            }
            out.push(eid);
        }
        out
    }

    /// Apply a single rewrite rule across e-classes.
    ///
    /// `search` limits the scan to the given class ids (the dirty
    /// frontier supplied by `run`); `None` searches every class — the
    /// only sound choice for a rule that has never seen this graph.
    ///
    /// `enode_budget` bounds how many NEW enodes this call may create:
    /// the scan stops between candidate classes once the budget is
    /// spent, and match enumeration inside each class is capped at the
    /// smaller of the remaining budget and [`EGraph::MATCH_CAP`].
    pub fn apply_rule(
        &mut self,
        rule: &Rewrite,
        root_eid: ClassId,
        search: Option<&BTreeSet<ClassId>>,
        enode_budget: Option<usize>,
    ) -> bool {
        let _ = root_eid; // kept for spec/API parity (policy hook point)
        if search.is_none() {
            // A whole-graph scan establishes the rule's frontier; a
            // restricted scan does not.
            self.applied_rules.insert(rule.name.clone());
        }
        let mut changed = false;
        let n_start = self.n_enodes();
        let lhs_prog = self.prog_for(&rule.lhs);
        let rhs_prog = self.prog_for(&rule.rhs);
        let candidates = self.candidate_classes(&lhs_prog, search);
        for eid in candidates {
            let match_cap = match enode_budget {
                Some(budget) => {
                    let spent = self.n_enodes() - n_start;
                    if spent >= budget {
                        break;
                    }
                    Some((budget - spent).min(Self::MATCH_CAP))
                }
                None => None,
            };
            // Eager per-class enumeration: each substitution is applied
            // in canonical enumeration order, and the enumeration is a
            // call-time snapshot — matching the spec's frozen-epoch
            // stream exactly (see the module docs).
            for mut subst in self.enumerate(&lhs_prog, eid, match_cap) {
                if rule.check.is_some() || rule.derive.is_some() {
                    // Resolve every term metavar to its minimum-size
                    // member before the hooks see the binding — a class
                    // that resolves to `None` (fully cyclic) skips the
                    // substitution, conservative never-wrong.
                    let mut terms: BTreeMap<Rc<str>, Term> = BTreeMap::new();
                    let mut resolved = true;
                    for (k, &v) in subst.terms.iter() {
                        match self.min_term_cached(v) {
                            Some(t) => {
                                terms.insert(k.clone(), t);
                            }
                            None => {
                                resolved = false;
                                break;
                            }
                        }
                    }
                    if !resolved {
                        continue;
                    }
                    let env = BoundEnv {
                        terms,
                        attrs: subst.attrs.clone(),
                    };
                    if let Some(check) = &rule.check
                        && !check(&env)
                    {
                        continue;
                    }
                    if let Some(derive) = &rule.derive {
                        let Some(extra) = derive(&env) else {
                            continue;
                        };
                        for d in extra {
                            match d {
                                Derived::Attr(k, v) => {
                                    subst.attrs.insert(k, v);
                                }
                                Derived::Term(k, t) => {
                                    // Intern the minted term so the RHS
                                    // metavar resolves to an eid —
                                    // the spec's "$leaf:" channel.
                                    match self.add_term(&t, &rule.name) {
                                        Ok(e) => {
                                            subst.terms.insert(k, e);
                                        }
                                        Err(_) => {
                                            resolved = false;
                                        }
                                    }
                                    if !resolved {
                                        break;
                                    }
                                }
                                Derived::Class(k, e) => {
                                    subst.terms.insert(k, e);
                                }
                            }
                        }
                        if !resolved {
                            continue;
                        }
                    }
                }
                let (result, created) = if self.track {
                    self.tag_rule = Some(rule.name.clone());
                    self.collect = Some(Vec::new());
                    self.inst_last_enode = None;
                    let r = self.instantiate(&rhs_prog.root, &subst);
                    self.tag_rule = None;
                    (r, self.collect.take().unwrap_or_default())
                } else {
                    self.inst_last_enode = None;
                    (self.instantiate(&rhs_prog.root, &subst), Vec::new())
                };
                // A binding that cannot realise the RHS — skip like a
                // check veto (the spec's KeyError arm).
                let Some(rhs_eid) = result else {
                    continue;
                };
                let merged = self.union_with(
                    eid,
                    rhs_eid,
                    &MergeInfo {
                        rule: Some(rule.name.clone()),
                        subst: Some(subst.clone()),
                        ..MergeInfo::default()
                    },
                );
                if self.track && (merged || !created.is_empty()) {
                    // A real merge or freshly-instantiated enodes — the
                    // application is a witness worth keeping. A no-op
                    // firing adds no 2-morphism and is not recorded.
                    let app_idx = self.applications.len();
                    let ma = self.find(eid);
                    let mb = self.find(rhs_eid);
                    self.applications.push(Application {
                        rule: rule.name.clone(),
                        matched_eid: ma,
                        rhs_eid: mb,
                        subst: subst.clone(),
                        rhs_root_enode: self.inst_last_enode.clone(),
                    });
                    // First discovered witness wins — a hash-consed
                    // enode keeps the application that created it.
                    for en in &created {
                        self.enode_app.entry(en.clone()).or_insert(app_idx);
                    }
                }
                if merged {
                    changed = true;
                    *self.rule_fires.entry(rule.name.clone()).or_insert(0) += 1;
                }
            }
        }
        changed
    }

    /// `matches` against a pre-compiled program (internal).
    fn enumerate(&mut self, prog: &Prog, eid: ClassId, limit: Option<usize>) -> Vec<Subst> {
        let mut out = Vec::new();
        match limit {
            Some(l) => self.m_bounded(&prog.root, eid, Subst::default(), &mut out, l),
            None => self.m_stream(&prog.root, eid, Subst::default(), &mut out),
        }
        out
    }

    // -- saturation ------------------------------------------------------

    /// Run equality saturation until a fixed point.
    ///
    /// Incremental: each iteration re-searches only the *dirty
    /// frontier* — e-classes whose reachable subgraph changed since
    /// they were last searched. A rule that has never been applied in
    /// this e-graph searches every class once.
    ///
    /// See [`RunOptions`] for budgets, the node cap, and the lazy
    /// `Stop::Improving` policy — all ports of the spec's `run`
    /// semantics, budget accounting included.
    pub fn run(
        &mut self,
        rules: &[Rewrite],
        root_eid: ClassId,
        opts: &mut RunOptions,
    ) -> Result<SaturationStats, RunError> {
        if opts.stop == Stop::Improving && opts.cost_fn.is_none() {
            return Err(RunError::ImprovingNeedsCost);
        }
        for name in opts.rule_budgets.keys() {
            self.budget_spent
                .entry(Rc::from(name.as_str()))
                .or_insert(0);
        }
        let mut stop_reason = StopReason::MaxIterations;
        let mut best_cost = f64::INFINITY;
        let mut stall = 0usize;
        let mut improved = 0usize;
        let mut iteration = 0usize;
        for it in 0..opts.max_iterations {
            iteration = it;
            let n_before = self.n_enodes();
            // Snapshot the frontier ONCE per iteration: classes changed
            // while rules fire are re-searched next iteration.
            let dirty_ids: Vec<ClassId> = self.dirty.iter().copied().collect();
            let search: BTreeSet<ClassId> = dirty_ids.into_iter().map(|e| self.find(e)).collect();
            self.dirty.clear();
            for rule in rules {
                let budget = opts.rule_budgets.get(rule.name.as_ref()).copied();
                let remaining = match budget {
                    Some(b) => {
                        let spent = self.budget_spent[rule.name.as_ref()];
                        match b.checked_sub(spent) {
                            Some(r) if r > 0 => Some(r),
                            _ => continue, // suspended: budget exhausted
                        }
                    }
                    None => None,
                };
                let n0 = self.n_enodes();
                if self.applied_rules.contains(&rule.name) {
                    self.apply_rule(rule, root_eid, Some(&search), remaining);
                } else {
                    // Never scanned this graph: full scan once —
                    // afterwards the dirty frontier suffices.
                    self.apply_rule(rule, root_eid, None, remaining);
                }
                if budget.is_some() {
                    *self
                        .budget_spent
                        .get_mut(rule.name.as_ref())
                        .expect("seeded") += self.n_enodes() - n0;
                }
            }
            let mut rebuild_set: BTreeSet<ClassId> = search;
            rebuild_set.extend(self.dirty.iter().copied());
            self.rebuild(Some(rebuild_set));
            let n_after = self.n_enodes();
            if n_after >= opts.max_nodes {
                stop_reason = StopReason::MaxNodes;
                break;
            }
            if n_after == n_before && self.dirty.is_empty() {
                stop_reason = StopReason::FixedPoint;
                break;
            }
            if opts.stop == Stop::Improving {
                // Lazy saturation: re-extract each iteration — the
                // shared cost memo makes repeat extractions cheap on
                // an only-just-grown graph.
                let cost_fn = opts.cost_fn.as_deref_mut().expect("gated");
                let term = self.extract_best(root_eid, cost_fn, None, None);
                let cost = match &term {
                    Some(t) => cost_fn(t),
                    None => f64::INFINITY,
                };
                if cost < best_cost {
                    best_cost = cost;
                    stall = 0;
                    improved += 1;
                } else {
                    stall += 1;
                    if stall >= opts.patience {
                        stop_reason = StopReason::Improving;
                        break;
                    }
                }
            }
        }
        // Leave the graph in the same canonicalised postcondition the
        // unrestricted loop guaranteed (downstream passes and
        // extraction traverse it directly).
        self.rebuild(None);
        Ok(SaturationStats {
            iterations: iteration + 1,
            n_enodes: self.n_enodes(),
            n_classes: self.n_classes(),
            n_proof_edges: self.merge_log.len(),
            truncation_level: self.truncation_level,
            rule_budgets: opts
                .rule_budgets
                .keys()
                .map(|n| (n.clone(), *self.budget_spent.get(n.as_str()).unwrap_or(&0)))
                .collect(),
            budget_suspended: opts
                .rule_budgets
                .iter()
                .filter(|(n, b)| self.budget_spent.get(n.as_str()).copied().unwrap_or(0) >= **b)
                .map(|(n, _)| n.clone())
                .collect(),
            stop: stop_reason,
            improved: (opts.stop == Stop::Improving).then_some(improved),
        })
    }

    // -- term location / witnesses ----------------------------------------

    /// Canonical e-class id realising `term`, without mutating member
    /// sets — the spec's `_class_of_term`. Structural probe through
    /// `node_to_class`; `None` when the term is not interned.
    pub fn class_of_term(&mut self, term: &Term) -> Option<ClassId> {
        match term {
            Term::Var(_) => None,
            Term::Leaf(key) => {
                let en = ENode::leaf(key.clone());
                self.node_to_class.get(&en).copied().map(|e| self.find(e))
            }
            Term::Op(o) => {
                let mut cids = Vec::with_capacity(o.args.len());
                for a in o.args.iter() {
                    cids.push(self.class_of_term(a)?);
                }
                let mut attrs = Vec::with_capacity(o.attrs.len());
                for (k, v) in o.attrs.iter() {
                    match v {
                        TermAttr::Lit(v) => attrs.push((k.clone(), v.clone())),
                        TermAttr::Meta(_) => return None,
                    }
                }
                let canon: Vec<ClassId> = cids.iter().map(|&c| self.find(c)).collect();
                let en = ENode::new(o.op.clone(), canon, attrs);
                self.node_to_class.get(&en).copied().map(|e| self.find(e))
            }
        }
    }

    /// `(eid, enode)` realising `term` inside its e-class — the spec's
    /// `_locate`.
    ///
    /// The enode is matched by structure — op, attrs (numerically
    /// lenient), and per-child e-classes — so it pins down exactly which
    /// member of the class the term uses. Members are scanned in
    /// canonical order: two distinct members can both match, and "the
    /// first match" must be deterministic.
    pub fn locate(
        &mut self,
        term: &Term,
        eid: Option<ClassId>,
    ) -> (Option<ClassId>, Option<ENode>) {
        let eid = match eid {
            Some(e) => self.find(e),
            None => match self.class_of_term(term) {
                Some(e) => e,
                None => return (None, None),
            },
        };
        let Some(ec) = self.classes.get(&eid) else {
            return (Some(eid), None);
        };
        let nodes: Vec<ENode> = ec.nodes.iter().cloned().collect();
        match term {
            Term::Leaf(key) => {
                for n in nodes {
                    if n.leaf_key() == Some(key.as_ref()) {
                        return (Some(eid), Some(n));
                    }
                }
                (Some(eid), None)
            }
            Term::Op(o) => {
                let mut child_cls = Vec::with_capacity(o.args.len());
                for a in o.args.iter() {
                    child_cls.push(self.class_of_term(a));
                }
                for n in nodes {
                    if *n.op != *o.op || n.children.len() != o.args.len() {
                        continue;
                    }
                    // attrs compare numerically lenient (spec: dict !=
                    // on plain values).
                    if n.attrs.len() != o.attrs.len()
                        || !n
                            .attrs
                            .iter()
                            .zip(o.attrs.iter())
                            .all(|((nk, nv), (pk, pv))| {
                                nk == pk
                                    && match pv {
                                        TermAttr::Lit(pv) => pv.match_eq(nv),
                                        TermAttr::Meta(_) => false,
                                    }
                            })
                    {
                        continue;
                    }
                    if n.children
                        .iter()
                        .zip(child_cls.iter())
                        .all(|(&c, cc)| cc.is_some_and(|cc| self.find(c) == cc))
                    {
                        return (Some(eid), Some(n));
                    }
                }
                (Some(eid), None)
            }
            Term::Var(_) => (Some(eid), None),
        }
    }

    /// Creation order of an enode (its birth eid); huge if unknown.
    fn birth(&mut self, enode: &ENode) -> ClassId {
        if let Some(&b) = self.enode_birth.get(enode) {
            return b;
        }
        self.node_to_class.get(enode).copied().unwrap_or(1 << 60)
    }

    /// The earliest-created representative term of an e-class — the
    /// spec's `_oldest_term`: minimum-birth enode at every level, so
    /// witness expansion is a strictly descending recursion.
    pub fn oldest_term(&mut self, eid: ClassId) -> Option<Term> {
        let mut memo = FxHashMap::default();
        self.oldest_term_rec(eid, &mut BTreeSet::new(), &mut memo)
    }

    fn oldest_term_rec(
        &mut self,
        eid: ClassId,
        stack: &mut BTreeSet<ClassId>,
        memo: &mut FxHashMap<ClassId, Option<Term>>,
    ) -> Option<Term> {
        let eid = self.find(eid);
        if stack.contains(&eid) {
            return None;
        }
        if let Some(hit) = memo.get(&eid) {
            return hit.clone();
        }
        let ec = self.classes.get(&eid)?;
        let mut by_birth: Vec<(ClassId, ENode)> =
            ec.nodes.iter().map(|n| (0usize, n.clone())).collect();
        for (b, n) in by_birth.iter_mut() {
            *b = self.birth(n);
        }
        by_birth.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
        stack.insert(eid);
        let mut result = None;
        for (_, node) in by_birth {
            if node.is_leaf() {
                let key = node.leaf_key().unwrap_or("??").to_string();
                result = Some(Term::leaf(key));
                memo.insert(eid, result.clone());
                break;
            }
            let mut args = Vec::with_capacity(node.children.len());
            let mut ok = true;
            for &c in node.children.iter() {
                match self.oldest_term_rec(c, stack, memo) {
                    Some(t) => args.push(t),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                let attrs: Vec<(Rc<str>, TermAttr)> = node
                    .attrs
                    .iter()
                    .map(|(k, v)| (k.clone(), TermAttr::Lit(v.clone())))
                    .collect();
                let t = Term::op(node.op.clone(), Rc::from(args), attrs);
                memo.insert(eid, Some(t.clone()));
                result = Some(t);
                break;
            }
        }
        stack.remove(&eid);
        result
    }

    /// The shared content-keyed cost memo for a `cost_fn` — the spec's
    /// `_cost_memo_for`. Keyed by `(TypeId, address)` so a different
    /// cost model gets a fresh dict and an address-recycled function of
    /// a different type can never inherit a stale memo.
    pub(crate) fn take_cost_memo(
        &mut self,
        key: (std::any::TypeId, usize),
    ) -> FxHashMap<Term, f64> {
        self.cost_memos.remove(&key).unwrap_or_default()
    }

    /// Write back the memo `take_cost_memo` lent out.
    pub(crate) fn put_cost_memo(
        &mut self,
        key: (std::any::TypeId, usize),
        memo: FxHashMap<Term, f64>,
    ) {
        self.cost_memos.insert(key, memo);
    }
}

impl Default for EGraph {
    fn default() -> Self {
        EGraph::new()
    }
}
