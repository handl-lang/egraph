//! The crate's term type — patterns and concrete terms share it.
//!
//! Mirrors the spec's dual use of `Op` trees: a rule's `lhs`/`rhs`, the
//! terms interned into the graph, and the terms extraction produces are
//! all [`Term`]. Two positions are pattern-only:
//!
//! * [`Term::Var`] — a metavariable binding an e-class (the spec's bare
//!   `str` leaf).
//! * [`TermAttr::Meta`] — an attribute metavariable (the spec's
//!   string-valued attr, bound under the `"$attr:"` namespace — the
//!   separate [`crate::Subst::attrs`] map replaces that key-mangling).
//!
//! `EGraph::add_term` rejects both — a metavariable is not a term —
//! where the spec would silently leaf-intern a `str` (named wart).

use std::rc::Rc;

use crate::value::AttrValue;

/// A term: metavariable, leaf, or operator node.
///
/// Ordering is structural and total (variant rank `Var < Leaf < Op`,
/// contents second) — it feeds deterministic dedup and BTree keys.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    /// Pattern metavariable — binds an e-class id at match time.
    /// Illegal in a concrete term (`add_term` rejects it).
    Var(Rc<str>),
    /// A concrete leaf, interned by key (the spec's `("leaf", (),
    /// (("key", k),))` enode). Kernel-`Term` leaves encode
    /// self-describing keys — see [`crate`] docs and `term_bridge`.
    Leaf(Rc<str>),
    /// An operator node: head op name, child terms, attributes.
    Op(Op),
}

/// An operator node of a [`Term`].
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Op {
    /// The head operator name (the domain alphabet — injected as data).
    pub op: Rc<str>,
    /// Child terms.
    pub args: Rc<[Term]>,
    /// Sorted, unique-keyed attributes.
    pub attrs: Rc<[(Rc<str>, TermAttr)]>,
}

/// An attribute entry in a term/pattern.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TermAttr {
    /// A concrete attribute value.
    Lit(AttrValue),
    /// An attribute metavariable (pattern position only).
    Meta(Rc<str>),
}

impl Term {
    /// A metavariable (pattern position only).
    pub fn var(name: impl Into<Rc<str>>) -> Term {
        Term::Var(name.into())
    }

    /// A concrete leaf by key.
    pub fn leaf(key: impl Into<Rc<str>>) -> Term {
        Term::Leaf(key.into())
    }

    /// An operator node; `attrs` is normalised (sorted, unique-keyed —
    /// a repeated key keeps the last value, `dict` semantics).
    pub fn op(
        op: impl Into<Rc<str>>,
        args: impl Into<Rc<[Term]>>,
        attrs: impl IntoIterator<Item = (Rc<str>, TermAttr)>,
    ) -> Term {
        let mut map: std::collections::BTreeMap<Rc<str>, TermAttr> =
            std::collections::BTreeMap::new();
        for (k, v) in attrs {
            map.insert(k, v);
        }
        Term::Op(Op {
            op: op.into(),
            args: args.into(),
            attrs: map.into_iter().collect(),
        })
    }

    /// An attribute-free operator node.
    pub fn opl(op: impl Into<Rc<str>>, args: impl Into<Rc<[Term]>>) -> Term {
        Term::Op(Op {
            op: op.into(),
            args: args.into(),
            attrs: Rc::from(Vec::new()),
        })
    }

    /// Structural size — the spec's `nops` tie-break count: leaves and
    /// metavariables are 0, an `Op` is 1 plus its children.
    ///
    /// Note the spec counts a leaf enode as `nops = 0` and each op as
    /// `1 + Σ children` — this matches exactly.
    pub fn size(&self) -> usize {
        match self {
            Term::Var(_) | Term::Leaf(_) => 0,
            Term::Op(o) => 1 + o.args.iter().map(Term::size).sum::<usize>(),
        }
    }

    /// The head op name, when this is an operator node.
    pub fn head_op(&self) -> Option<&str> {
        match self {
            Term::Op(o) => Some(&o.op),
            _ => None,
        }
    }

    /// Whether this term is concrete — no metavariables anywhere.
    ///
    /// `add_term` requires it.
    pub fn is_concrete(&self) -> bool {
        match self {
            Term::Var(_) => false,
            Term::Leaf(_) => true,
            Term::Op(o) => {
                o.args.iter().all(Term::is_concrete)
                    && o.attrs.iter().all(|(_, v)| matches!(v, TermAttr::Lit(_)))
            }
        }
    }
}

/// `(key, literal)` attr pair — construction sugar.
pub fn attr(key: &str, value: impl Into<AttrValue>) -> (Rc<str>, TermAttr) {
    (Rc::from(key), TermAttr::Lit(value.into()))
}

/// `(key, metavariable)` attr pair — construction sugar.
pub fn attr_meta(key: &str, name: &str) -> (Rc<str>, TermAttr) {
    (Rc::from(key), TermAttr::Meta(Rc::from(name)))
}
