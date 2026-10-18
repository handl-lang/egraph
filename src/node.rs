//! E-nodes and e-classes: the interned node representation.
//!
//! An [`ENode`] is a `(op, children, attrs)` triple where children are
//! *canonical* e-class ids. Ordering is structural —
//! `(op, children, attrs)` lexicographic — which *is* the spec's
//! `_member_key` contract: a total, process-independent member order
//! consumed by every decision-reaching member scan (matching order,
//! congruence drain, `any_term`, extraction tie-breaks). The spec
//! computed it as `(op, children, repr(attrs))`; structural `Ord` keeps
//! the invariant without the repr (named divergence — strictly better
//! complexity, same determinism guarantee).

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::term::Term;
use crate::value::AttrValue;

/// An e-class identifier.
pub type ClassId = usize;

/// The leaf pseudo-op: leaf enodes are `("leaf", (), (("key", k),))`.
pub const LEAF_OP: &str = "leaf";

/// The attr name leaf enodes carry their key under.
pub const LEAF_KEY: &str = "key";

/// A term node in the e-graph: an op name with e-class children.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ENode {
    /// The head operator name.
    pub op: Rc<str>,
    /// Canonical child e-class ids.
    pub children: Rc<[ClassId]>,
    /// Sorted, unique-keyed attributes — spelling-strict under `Eq`
    /// (see [`AttrValue`]).
    pub attrs: Rc<[(Rc<str>, AttrValue)]>,
}

impl ENode {
    /// Build an e-node; `attrs` is normalised (sorted by key, unique —
    /// a repeated key keeps the last value).
    pub fn new(
        op: impl Into<Rc<str>>,
        children: impl Into<Rc<[ClassId]>>,
        attrs: impl IntoIterator<Item = (Rc<str>, AttrValue)>,
    ) -> ENode {
        let mut map: BTreeMap<Rc<str>, AttrValue> = BTreeMap::new();
        for (k, v) in attrs {
            map.insert(k, v);
        }
        ENode {
            op: op.into(),
            children: children.into(),
            attrs: map.into_iter().collect(),
        }
    }

    /// The canonical leaf e-node for `key`.
    pub fn leaf(key: impl Into<Rc<str>>) -> ENode {
        let key: Rc<str> = key.into();
        ENode {
            op: Rc::from(LEAF_OP),
            children: Rc::from(Vec::new()),
            attrs: Rc::from(vec![(Rc::from(LEAF_KEY), AttrValue::Str(key))]),
        }
    }

    /// Whether this is a leaf e-node.
    pub fn is_leaf(&self) -> bool {
        &*self.op == LEAF_OP
    }

    /// A leaf e-node's key, if it is one.
    pub fn leaf_key(&self) -> Option<&str> {
        if self.is_leaf() {
            match self.attrs.first().map(|(_, v)| v) {
                Some(AttrValue::Str(s)) => Some(s),
                _ => None,
            }
        } else {
            None
        }
    }

    /// Look up an attribute by name (attrs are sorted — binary search).
    pub fn attr(&self, key: &str) -> Option<&AttrValue> {
        self.attrs
            .binary_search_by(|(k, _)| k.as_ref().cmp(key))
            .ok()
            .map(|i| &self.attrs[i].1)
    }

    /// The sorted attr-name set of this node — the spec's `keyset`
    /// exact-equality gate compares this to a pattern's attr names.
    /// Both sides are stored sorted, so a slice compare suffices.
    pub fn attr_names_eq(&self, names: &[Rc<str>]) -> bool {
        self.attrs.len() == names.len() && self.attrs.iter().map(|(k, _)| k).eq(names.iter())
    }
}

/// An equivalence class of semantically-equal terms.
#[derive(Debug)]
pub struct EClass {
    /// Canonical id of this class.
    pub id: ClassId,
    /// Member e-nodes, in canonical (structural `Ord`) order — the
    /// spec's `sorted(nodes, key=_member_key)` made a property of the
    /// container.
    pub nodes: BTreeSet<ENode>,
    /// Lazily-built `op -> member enodes` index used by the matcher;
    /// invalidated whenever `nodes` is mutated (union / rebuild /
    /// congruence replace) — the spec's `by_op` cache, verbatim.
    pub(crate) by_op: Option<FxHashMap<Rc<str>, Rc<Vec<ENode>>>>,
    /// The `_any_term_cached` port: the class's minimum-size member
    /// memo, persisted across `apply_rule` calls and iterations.
    pub(crate) min_term: Option<(Term, f64)>,
}

impl EClass {
    pub(crate) fn new(id: ClassId) -> EClass {
        EClass {
            id,
            nodes: BTreeSet::new(),
            by_op: None,
            min_term: None,
        }
    }

    /// Drop every lazily-built index — call on any `nodes` mutation.
    pub(crate) fn invalidate(&mut self) {
        self.by_op = None;
        self.min_term = None;
    }
}
