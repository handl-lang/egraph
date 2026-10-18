//! Extraction: deterministic minimum-cost member selection.
//!
//! Ports the spec's `extract_best` core — the DAG-aware greedy walk —
//! minus its domain payload: no `FOLD_OPS` param-only discount, no
//! fusion tie-break, no roofline/overhead memo probes (those are
//! cost-model policies the domain injects, not substrate). What stays
//! is exactly the contract the domain relies on:
//!
//! * members are scanned in canonical ([`ENode`]) order;
//! * each e-class in the extracted DAG is charged **once** (the
//!   `used`-set billing — a shared child contributes its subtree cost
//!   only for classes not already accounted for);
//! * `local = max(cost(term) - Σ cost(children), 0)`;
//! * ties resolve on fewest ops (`nops`), then canonical order;
//! * cyclic classes are unextractable;
//! * `overrides`/`bans` steer the pick (coordinated extraction and
//!   bounded-ε filtering plug in here).
//!
//! `extract_min_depth`, `dag_cost`, `extract_alternatives`, and
//! `diverse_classes` port verbatim modulo the same domain strip.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::EGraph;
use crate::node::{ClassId, ENode};
use crate::term::{Term, TermAttr};
use crate::value::AttrValue;

/// Per-class extraction cache entry — the spec's
/// `(total, term, used, nops, cfn(term), local)` tuple, typed.
#[derive(Clone)]
struct CacheEnt {
    total: f64,
    term: Option<Term>,
    used: Rc<BTreeSet<ClassId>>,
    nops: usize,
    ct: f64,
    local: f64,
}

fn cycle_ent() -> CacheEnt {
    CacheEnt {
        total: f64::INFINITY,
        term: None,
        used: Rc::new(BTreeSet::new()),
        nops: 0,
        ct: 0.0,
        local: 0.0,
    }
}

struct ExtractCtx<'a> {
    cache: FxHashMap<ClassId, CacheEnt>,
    /// `eid -> billable local contribution` of the class's chosen
    /// member — the shared-class billing reads one map probe per class.
    adj_of: FxHashMap<ClassId, f64>,
    in_progress: BTreeSet<ClassId>,
    overrides: Option<&'a FxHashMap<ClassId, ENode>>,
    bans: Option<&'a FxHashMap<ClassId, BTreeSet<ENode>>>,
    memo: FxHashMap<Term, f64>,
}

fn priced(memo: &mut FxHashMap<Term, f64>, f: &mut dyn FnMut(&Term) -> f64, t: &Term) -> f64 {
    if let Some(&c) = memo.get(t) {
        c
    } else {
        let c = f(t);
        memo.insert(t.clone(), c);
        c
    }
}

/// A [`Term`] node's attrs, realised as literal enode attrs.
fn lit_attrs(attrs: &Rc<[(Rc<str>, AttrValue)]>) -> Vec<(Rc<str>, TermAttr)> {
    attrs
        .iter()
        .map(|(k, v)| (k.clone(), TermAttr::Lit(v.clone())))
        .collect()
}

impl EGraph {
    /// Extract the minimum-cost term from the e-class at `eid`.
    ///
    /// `cost_fn` prices a *term*; the extraction recovers each node's
    /// local cost as `cost(term) − Σ cost(children)` — exact for
    /// additive cost functions — and bills every e-class once across
    /// the extracted DAG.
    ///
    /// `overrides` maps canonical e-class ids to a specific [`ENode`]:
    /// extraction is then forced through it (the coordinated-
    /// extraction hook). `bans` is the dual: per-class enodes the
    /// extraction must skip.
    ///
    /// `None` when no member is extractable (all cyclic/banned).
    pub fn extract_best(
        &mut self,
        eid: ClassId,
        cost_fn: &mut dyn FnMut(&Term) -> f64,
        overrides: Option<&FxHashMap<ClassId, ENode>>,
        bans: Option<&FxHashMap<ClassId, BTreeSet<ENode>>>,
    ) -> Option<Term> {
        let key = (
            std::any::TypeId::of::<dyn FnMut(&Term) -> f64>(),
            cost_fn as *const _ as *const () as usize,
        );
        // Take the shared memo out so the recursive walk can borrow
        // `self` mutably; write it back when done.
        let memo = self.take_cost_memo(key);
        let mut ctx = ExtractCtx {
            cache: FxHashMap::default(),
            adj_of: FxHashMap::default(),
            in_progress: BTreeSet::new(),
            overrides,
            bans,
            memo,
        };
        let ent = self.extract_go(eid, cost_fn, &mut ctx);
        self.put_cost_memo(key, ctx.memo);
        ent.term
    }

    fn extract_go(
        &mut self,
        eclass_id: ClassId,
        cost_fn: &mut dyn FnMut(&Term) -> f64,
        ctx: &mut ExtractCtx,
    ) -> CacheEnt {
        let eclass_id = self.find(eclass_id);
        if let Some(ent) = ctx.cache.get(&eclass_id) {
            return ent.clone();
        }
        if ctx.in_progress.contains(&eclass_id) {
            // Cycle back to an ancestor — not extractable.
            return cycle_ent();
        }
        ctx.in_progress.insert(eclass_id);
        let ovr = ctx.overrides.and_then(|o| o.get(&eclass_id).cloned());
        // Canonical member order: equal-cost/equal-size ties resolve
        // identically every run — the determinism invariant.
        let nodes: Vec<ENode> = match ovr {
            Some(n) => vec![n],
            None => self.classes[&eclass_id].nodes.iter().cloned().collect(),
        };
        let banned = ctx.bans.and_then(|b| b.get(&eclass_id));
        let mut best: Option<CacheEnt> = None;
        for node in nodes {
            if banned.is_some_and(|b| b.contains(&node)) {
                continue;
            }
            if node.is_leaf() {
                let key = node.leaf_key().unwrap_or("??");
                let term = Term::leaf(key);
                let total = priced(&mut ctx.memo, cost_fn, &term);
                let cand = CacheEnt {
                    total,
                    term: Some(term),
                    used: Rc::new(BTreeSet::from([eclass_id])),
                    nops: 0,
                    ct: total,
                    local: total,
                };
                if better(&cand, &best) {
                    best = Some(cand);
                }
                continue;
            }
            let mut child_terms = Vec::with_capacity(node.children.len());
            let mut child_tc = 0.0f64;
            let mut child_nops = 0usize;
            let mut used: BTreeSet<ClassId> = BTreeSet::from([eclass_id]);
            let mut sub_cost = 0.0f64;
            let mut valid = true;
            for &child_eid in node.children.iter() {
                // Cached entries are keyed by canonical id — a hit
                // means `child_eid` was already canonical (in-progress
                // classes are never cached).
                let entry = match ctx.cache.get(&child_eid) {
                    Some(e) => e.clone(),
                    None => {
                        let canon = self.find(child_eid);
                        if canon == eclass_id {
                            valid = false; // direct self-reference
                            break;
                        }
                        self.extract_go(canon, cost_fn, ctx)
                    }
                };
                let Some(cterm) = entry.term.clone() else {
                    valid = false;
                    break;
                };
                child_terms.push(cterm);
                child_tc += entry.ct;
                child_nops += entry.nops;
                // Charge each distinct e-class in the DAG once.
                for u in entry.used.iter() {
                    if used.insert(*u) {
                        sub_cost += ctx.adj_of.get(u).copied().unwrap_or(0.0);
                    }
                }
            }
            if !valid {
                continue;
            }
            let term = Term::op(
                node.op.clone(),
                Rc::from(child_terms),
                lit_attrs(&node.attrs),
            );
            let ct = priced(&mut ctx.memo, cost_fn, &term);
            let mut local = ct - child_tc;
            if local < 0.0 {
                local = 0.0;
            }
            let total = local + sub_cost;
            let cand = CacheEnt {
                total,
                term: Some(term),
                used: Rc::new(used),
                nops: child_nops + 1,
                ct,
                local,
            };
            if better(&cand, &best) {
                best = Some(cand);
            }
        }
        ctx.in_progress.remove(&eclass_id);
        let ent = best.unwrap_or(CacheEnt {
            total: f64::INFINITY,
            term: None,
            used: Rc::new(BTreeSet::new()),
            nops: 0,
            ct: 0.0,
            local: 0.0,
        });
        ctx.adj_of.insert(eclass_id, ent.local);
        ctx.cache.insert(eclass_id, ent.clone());
        ent
    }

    /// Extract the minimum critical-path-depth member.
    ///
    /// Depth is not additive, so `extract_best` cannot serve it — but
    /// it is decomposable per class (`1 + max(child depths)`), which
    /// this greedy walk computes directly. Deterministic: canonical
    /// member order, strict `<`.
    pub fn extract_min_depth(&mut self, eid: ClassId) -> Option<Term> {
        let mut cache: FxHashMap<ClassId, (f64, Option<Term>)> = FxHashMap::default();
        let mut in_prog: BTreeSet<ClassId> = BTreeSet::new();
        self.min_depth_go(eid, &mut cache, &mut in_prog).1
    }

    fn min_depth_go(
        &mut self,
        cid: ClassId,
        cache: &mut FxHashMap<ClassId, (f64, Option<Term>)>,
        in_prog: &mut BTreeSet<ClassId>,
    ) -> (f64, Option<Term>) {
        let cid = self.find(cid);
        if let Some(hit) = cache.get(&cid) {
            return hit.clone();
        }
        if in_prog.contains(&cid) {
            return (f64::INFINITY, None);
        }
        in_prog.insert(cid);
        let nodes: Vec<ENode> = self.classes[&cid].nodes.iter().cloned().collect();
        let mut best: (f64, Option<Term>) = (f64::INFINITY, None);
        for node in nodes {
            let cand = if node.is_leaf() {
                let key = node.leaf_key().unwrap_or("??").to_string();
                (0.0, Some(Term::leaf(key)))
            } else {
                let mut kids = Vec::with_capacity(node.children.len());
                let mut dmax = 0.0f64;
                let mut ok = true;
                for &c in node.children.iter() {
                    let cc = self.find(c);
                    if cc == cid {
                        ok = false;
                        break;
                    }
                    let (d, t) = self.min_depth_go(cc, cache, in_prog);
                    let Some(t) = t else {
                        ok = false;
                        break;
                    };
                    kids.push(t);
                    dmax = dmax.max(d);
                }
                if !ok {
                    continue;
                }
                (
                    1.0 + dmax,
                    Some(Term::op(
                        node.op.clone(),
                        Rc::from(kids),
                        lit_attrs(&node.attrs),
                    )),
                )
            };
            if cand.0 < best.0 {
                best = cand;
            }
        }
        in_prog.remove(&cid);
        cache.insert(cid, best.clone());
        best
    }

    /// Enumerate the root e-class frontier — the top-`k` cheapest
    /// *distinct* members (the spec's `extract_alternatives`).
    ///
    /// For each non-leaf enode, force extraction through it and record
    /// the term's DAG cost. Deterministic: canonical member scan fixes
    /// insertion order; the stable sort keeps it for equal costs.
    pub fn extract_alternatives(
        &mut self,
        eid: ClassId,
        cost_fn: &mut dyn FnMut(&Term) -> f64,
        top_k: usize,
    ) -> Vec<(f64, Term)> {
        let eid = self.find(eid);
        let nodes: Vec<ENode> = self.classes[&eid].nodes.iter().cloned().collect();
        let mut seen: BTreeMap<Term, (f64, Term)> = BTreeMap::new();
        for node in nodes {
            if node.is_leaf() {
                continue;
            }
            let over: FxHashMap<ClassId, ENode> = FxHashMap::from_iter([(eid, node)]);
            let Some(term) = self.extract_best(eid, cost_fn, Some(&over), None) else {
                continue;
            };
            let cost = dag_cost(&term, cost_fn);
            match seen.get(&term) {
                Some(&(c, _)) if c <= cost => {}
                _ => {
                    seen.insert(term.clone(), (cost, term));
                }
            }
        }
        // Insertion order is the canonical member order; the stable
        // `sort_by` keeps it for equal-cost alternatives.
        let mut ranked: Vec<(f64, Term)> = seen.into_values().collect();
        ranked.sort_by(|a, b| a.0.total_cmp(&b.0));
        ranked.truncate(top_k);
        ranked
    }

    /// E-classes containing structurally distinct equivalent terms —
    /// where emergent compositions hide (the spec's `diverse_classes`).
    ///
    /// Returns classes with ≥2 distinct member ops, each with a
    /// one-line sketch of every distinct member. Order: most diverse
    /// first, then class id.
    pub fn diverse_classes(&mut self) -> Vec<(ClassId, Vec<String>)> {
        let mut out: Vec<(ClassId, Vec<String>)> = Vec::new();
        let ids: Vec<ClassId> = self.classes.keys().copied().collect();
        for eid in ids {
            let nodes: Vec<ENode> = self.classes[&eid].nodes.iter().cloned().collect();
            let mut ops = BTreeSet::new();
            for n in &nodes {
                if !n.is_leaf() {
                    ops.insert(n.op.clone());
                }
            }
            if ops.len() < 2 {
                continue;
            }
            let mut sketches = Vec::new();
            let mut seen_sketch = BTreeSet::new();
            for n in nodes {
                let sk = if n.is_leaf() {
                    n.leaf_key()
                        .unwrap_or("?")
                        .rsplit(':')
                        .next()
                        .unwrap_or("?")
                        .chars()
                        .take(24)
                        .collect::<String>()
                } else {
                    let child_ops: Vec<String> = n
                        .children
                        .iter()
                        .map(|&c| {
                            let cc = self.find(c);
                            self.classes
                                .get(&cc)
                                .and_then(|ec| ec.nodes.iter().next())
                                .map(|m| m.op.to_string())
                                .unwrap_or_else(|| "?".to_string())
                        })
                        .collect();
                    format!("{}({})", n.op, child_ops.join(","))
                };
                if seen_sketch.insert(sk.clone()) {
                    sketches.push(sk);
                }
            }
            out.push((eid, sketches));
        }
        out.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(&b.0)));
        out
    }
}

/// `true` when `cand` beats `best`: strictly cheaper, or equal cost
/// with fewer ops — the spec's `(total, nops)` selection, with
/// canonical scan order breaking the remaining ties.
fn better(cand: &CacheEnt, best: &Option<CacheEnt>) -> bool {
    match best {
        None => true,
        Some(b) => cand.total < b.total || (cand.total == b.total && cand.nops < b.nops),
    }
}

/// The DAG cost of an extracted term: `Σ cost_fn` over *distinct*
/// subterms — the generic core of the spec's `dag_cost` (dedup is
/// structural — the spec's interned `Op`s make value and identity
/// coincide; we dedup by value, the same contract).
pub fn dag_cost(term: &Term, cost_fn: &mut dyn FnMut(&Term) -> f64) -> f64 {
    let mut seen: rustc_hash::FxHashSet<Term> = rustc_hash::FxHashSet::default();
    let mut total = 0.0;
    let mut stack = vec![term.clone()];
    while let Some(t) = stack.pop() {
        if !seen.insert(t.clone()) {
            continue;
        }
        total += cost_fn(&t);
        if let Term::Op(o) = &t {
            stack.extend(o.args.iter().cloned());
        }
    }
    total
}
