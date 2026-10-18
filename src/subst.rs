//! Substitutions: metavariable bindings produced by a match.
//!
//! The spec keeps one flat dict with two namespaces — term
//! metavariables under their own names, attribute metavariables under
//! `"$attr:<name>"` keys. The Rust port splits the namespaces into two
//! ordered maps (named divergence — typed beats key-mangled), which is
//! also what `derive` hooks and the recorded `ProofEdge` subst see.

use std::collections::BTreeMap;
use std::rc::Rc;

use crate::node::ClassId;
use crate::value::AttrValue;

/// A match substitution.
///
/// `terms` maps term metavariable names to e-class ids; `attrs` maps
/// attribute metavariable names to concrete values. BTreeMap iteration
/// is canonical order — deterministic everywhere a subst is recorded
/// or replayed.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Subst {
    /// Term metavariable bindings (`name -> e-class id`).
    pub terms: BTreeMap<Rc<str>, ClassId>,
    /// Attribute metavariable bindings (`name -> value`).
    pub attrs: BTreeMap<Rc<str>, AttrValue>,
}
