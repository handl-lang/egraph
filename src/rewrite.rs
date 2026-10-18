//! Rewrite rules, side-condition environments, and provenance records.
//!
//! Ports the spec's `Rewrite` minus its domain-law bookkeeping
//! (`derivation`/`cond`/`dspec` are `catopt_core.laws.cond` machinery —
//! the crate keeps the generic core: patterns, `check`/`derive` hooks,
//! tags, and the ε-law bound fields).

use std::collections::BTreeSet;
use std::rc::Rc;

use crate::node::{ClassId, ENode};
use crate::subst::Subst;
use crate::term::Term;
use crate::value::AttrValue;

/// The resolved binding a `check`/`derive` hook sees — the spec's
/// `bound` dict: each term metavariable resolved to a representative
/// member term (`_any_term_cached`), each attr metavariable to its
/// concrete value.
#[derive(Clone, Debug, Default)]
pub struct BoundEnv {
    /// Resolved term metavariable bindings (`name -> member term`).
    pub terms: std::collections::BTreeMap<Rc<str>, Term>,
    /// Attribute metavariable bindings (`name -> value`).
    pub attrs: std::collections::BTreeMap<Rc<str>, AttrValue>,
}

/// A side condition: `bound -> bool`. `false` vetoes the firing.
pub type Check = dyn Fn(&BoundEnv) -> bool;

/// A computed-attribute hook: `bound -> Option<extra bindings>`.
///
/// `None` vetoes the rewrite; `Some` merges extra entries into the
/// substitution before RHS instantiation — the port of the spec's
/// `derive` contract (the `"$attr:"` and `"$leaf:"` channels, typed).
pub type Derive = dyn Fn(&BoundEnv) -> Option<Vec<Derived>>;

/// One extra binding a `derive` hook contributes.
#[derive(Clone, Debug)]
pub enum Derived {
    /// Bind an attribute metavariable (`"$attr:"` in the spec).
    Attr(Rc<str>, AttrValue),
    /// Bind a term metavariable to a freshly minted term — interned via
    /// `add_term` under the firing rule's provenance (the spec's
    /// `"$leaf:"` channel).
    Term(Rc<str>, Term),
    /// Bind a term metavariable directly to an e-class id (the spec's
    /// `isinstance(v, int)` passthrough).
    Class(Rc<str>, ClassId),
}

/// A rewrite rule: `lhs -> rhs`, both pattern terms.
///
/// `lhs`/`rhs` are [`Term`]s where [`crate::Term::Var`] names
/// metavariables and [`crate::TermAttr::Meta`] names attribute
/// metavariables. A `Term` carrying neither is a *concrete* pattern —
/// used by the non-local-witness ritual (see [`crate::EGraph::offer`]).
pub struct Rewrite {
    /// The rule's unique name (provenance + budget key).
    pub name: Rc<str>,
    /// Left-hand pattern.
    pub lhs: Term,
    /// Right-hand pattern.
    pub rhs: Term,
    /// The law/lemma name this rule certifies (metadata).
    pub law: String,
    /// Optional side condition over the resolved binding.
    pub check: Option<Box<Check>>,
    /// Optional computed-attribute hook.
    pub derive: Option<Box<Derive>>,
    /// Intrinsic classification (symmetry / expansive / subsumed /
    /// fusion / …) — domain metadata carried opaquely.
    pub tags: BTreeSet<String>,
    /// Bounded-error axis (ε-laws): when set, this rewrite is a
    /// *certified approximation* — `‖lhs − rhs‖ ≤ error_bound` in the
    /// norm named by `bound_norm`. Exact rules leave it `None`.
    pub error_bound: Option<f64>,
    /// The norm `error_bound` is measured in (e.g. `"spectral"`).
    pub bound_norm: String,
}

impl Rewrite {
    /// A rule `name: lhs -> rhs` with no hooks or metadata.
    pub fn new(name: impl Into<Rc<str>>, lhs: Term, rhs: Term) -> Rewrite {
        Rewrite {
            name: name.into(),
            lhs,
            rhs,
            law: String::new(),
            check: None,
            derive: None,
            tags: BTreeSet::new(),
            error_bound: None,
            bound_norm: "spectral".to_string(),
        }
    }

    /// Builder: attach a `check` side condition.
    pub fn with_check(mut self, check: impl Fn(&BoundEnv) -> bool + 'static) -> Rewrite {
        self.check = Some(Box::new(check));
        self
    }

    /// Builder: attach a `derive` computed-attribute hook.
    pub fn with_derive(
        mut self,
        derive: impl Fn(&BoundEnv) -> Option<Vec<Derived>> + 'static,
    ) -> Rewrite {
        self.derive = Some(Box::new(derive));
        self
    }

    /// Builder: set `law`.
    pub fn with_law(mut self, law: impl Into<String>) -> Rewrite {
        self.law = law.into();
        self
    }

    /// Builder: mark as an ε-rule.
    pub fn with_error_bound(mut self, bound: f64, norm: &str) -> Rewrite {
        self.error_bound = Some(bound);
        self.bound_norm = norm.to_string();
        self
    }
}

impl std::fmt::Debug for Rewrite {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Rewrite")
            .field("name", &self.name)
            .field("lhs", &self.lhs)
            .field("rhs", &self.rhs)
            .field("law", &self.law)
            .field("error_bound", &self.error_bound)
            .finish_non_exhaustive()
    }
}

/// One recorded rule application — the spec's `_applications` entry.
///
/// Recorded only for firings that changed the graph (a real merge or
/// freshly-instantiated enodes); a no-op firing adds no 2-morphism and
/// is not recorded — the spec's rule verbatim.
#[derive(Clone, Debug)]
pub struct Application {
    /// The firing rule's name.
    pub rule: Rc<str>,
    /// Canonical id of the matched (LHS) class, post-merge.
    pub matched_eid: ClassId,
    /// Canonical id of the instantiated-RHS class, post-merge.
    pub rhs_eid: ClassId,
    /// The fired binding (post-`derive` extras included).
    pub subst: Subst,
    /// The enode realising the instantiated pattern's root — `None`
    /// when the RHS was a bare metavariable or leaf binding.
    pub rhs_root_enode: Option<ENode>,
}

/// One recorded merge: the 2-morphism witnessing two e-classes.
///
/// `rule` is the `Rewrite::name` that fired — `None` for merges
/// performed outside rule application (non-local passes, direct
/// `union` calls), or the name of a *synthesised* `Rewrite` when the
/// caller attached a replayable `witness` (see
/// [`crate::EGraph::union_with`]).
#[derive(Clone, Debug)]
pub struct ProofEdge {
    /// The rule that produced this merge, if any.
    pub rule: Option<Rc<str>>,
    /// Canonical id of the matched (LHS) side before the merge.
    pub a: ClassId,
    /// Canonical id of the produced (RHS) side before the merge.
    pub b: ClassId,
    /// The fired binding; empty for unwitnessed/manual merges.
    pub subst: Subst,
    /// Free-form note.
    pub note: String,
}
