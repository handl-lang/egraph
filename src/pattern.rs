//! Compiled patterns — the spec's `_PVar`/`_PLeaf`/`_POp`/`_Prog`.
//!
//! Each rule's pattern compiles **once per e-graph** into a `PNode`
//! tree carrying everything the match needs precomputed: the normalised
//! attr tuple, the attr-name keyset for the exact-equality gate, the
//! prebuilt leaf [`ENode`] for the registry probe, and the per-child op
//! constraints feeding targeted eligibility (`_opk`).

use std::rc::Rc;

use crate::node::ENode;
use crate::term::{Op, Term, TermAttr};

/// A compiled pattern node.
#[derive(Debug)]
pub(crate) enum PNode {
    /// Metavariable leaf — binds an e-class id (the spec's `_PVar`).
    Var(Rc<str>),
    /// Concrete leaf — matches by interned-enode probe (`_PLeaf`).
    /// `key` is the leaf key; `enode` is the prebuilt `("leaf", (),
    /// (("key", key),))` node the matcher probes in `node_to_class`.
    Leaf { key: Rc<str>, enode: ENode },
    /// Operator pattern (`_POp`): head op, children, attr program.
    Op {
        /// The head operator name.
        op: Rc<str>,
        /// Compiled child patterns.
        children: Vec<PNode>,
        /// Sorted attr program — `Lit` values must `match_eq`, `Meta`
        /// names bind into [`crate::Subst::attrs`].
        attrs: Rc<[(Rc<str>, TermAttr)]>,
        /// Sorted attr names — the `keyset` exact-equality gate.
        keyset: Rc<[Rc<str>]>,
        /// `(position, op)` for every Op-typed child — targeted
        /// eligibility constraints consumed by `_candidate_classes`.
        child_reqs: Vec<(usize, Rc<str>)>,
    },
}

/// A compiled pattern plus its eligibility metadata (`_Prog`).
#[derive(Debug)]
pub(crate) struct Prog {
    /// The compiled pattern tree.
    pub root: PNode,
    /// Root head op for the `(op, arity)` class index (`None` for
    /// non-op roots).
    pub head_op: Option<Rc<str>>,
    /// Root arity (`usize::MAX` sentinel for non-op roots — the spec's
    /// `-1`).
    pub head_arity: usize,
    /// Registry key for concrete-leaf roots.
    pub leaf_key: Option<Rc<str>>,
    /// The root's child-op constraints.
    pub child_reqs: Vec<(usize, Rc<str>)>,
}

fn pnode(pattern: &Term) -> PNode {
    match pattern {
        Term::Var(name) => PNode::Var(name.clone()),
        Term::Leaf(key) => PNode::Leaf {
            key: key.clone(),
            enode: ENode::leaf(key.clone()),
        },
        Term::Op(Op { op, args, attrs }) => {
            let children: Vec<PNode> = args.iter().map(pnode).collect();
            let child_reqs: Vec<(usize, Rc<str>)> = children
                .iter()
                .enumerate()
                .filter_map(|(i, c)| match c {
                    PNode::Op { op, .. } => Some((i, op.clone())),
                    _ => None,
                })
                .collect();
            PNode::Op {
                op: op.clone(),
                children,
                attrs: attrs.clone(), // Term::op already normalised.
                keyset: attrs.iter().map(|(k, _)| k.clone()).collect(),
                child_reqs,
            }
        }
    }
}

/// Compile a whole pattern term into a [`Prog`].
pub(crate) fn compile_pattern(pattern: &Term) -> Prog {
    let root = pnode(pattern);
    match &root {
        PNode::Op {
            op,
            children,
            child_reqs,
            ..
        } => Prog {
            head_op: Some(op.clone()),
            head_arity: children.len(),
            leaf_key: None,
            child_reqs: child_reqs.clone(),
            root,
        },
        PNode::Var(_) => Prog {
            head_op: None,
            head_arity: usize::MAX,
            leaf_key: None,
            child_reqs: Vec::new(),
            root,
        },
        PNode::Leaf { key, .. } => Prog {
            head_op: None,
            head_arity: usize::MAX,
            leaf_key: Some(key.clone()),
            child_reqs: Vec::new(),
            root,
        },
    }
}
