//! Attribute values: the hashable, totally-ordered scalar/composite
//! domain carried by e-node attributes.
//!
//! Ports the Python spec's two-tier attr semantics:
//!
//! * **Identity is spelling-strict.** The spec's `ENode._sig` repr-keys
//!   every attr value, so `0` and `0.0` (and `0.0` and `-0.0`) are
//!   *distinct* enode payloads. `AttrValue`'s `Eq`/`Hash` mirror that:
//!   floats compare by bit pattern, ints never equal floats.
//! * **Matching is numerically lenient.** The spec compares pattern
//!   attrs to node attrs with `!=` — Python's value equality, where
//!   `1 == 1.0`, `True == 1`, and `(1, "a") == (1.0, "a")`. That is
//!   [`AttrValue::match_eq`]: recursive numeric leniency, including the
//!   bool↔int coercion the Python tower admits.
//!
//! Ordering is *structural*, not repr-derived — the deliberate fix for
//! the spec's `repr(attrs)` sort keys. The invariant the spec protects
//! is a total, process-independent member order; structural `Ord`
//! provides it directly (and without recomputing a repr per compare).

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

/// A hashable, totally-ordered attribute value.
///
/// The JSON-shaped scalar/composite domain: `serde_json::Value` and
/// `handl_value::TaggedValue` both convert in (see the `From` impls and
/// [`AttrValue::from_tagged`]).
#[derive(Clone, Debug)]
pub enum AttrValue {
    /// JSON `null` / Python `None`.
    Null,
    /// Boolean.
    Bool(bool),
    /// Signed integer.
    Int(i64),
    /// Unsigned integer (JSON numbers `> i64::MAX`).
    UInt(u64),
    /// IEEE-754 double. Identity is bit-strict (`0.0 != -0.0`); matching
    /// is numerically lenient via [`AttrValue::match_eq`].
    Float(f64),
    /// UTF-8 string.
    Str(Rc<str>),
    /// Sequence — the port of the spec's tuple-normalised list attrs.
    Array(Rc<[AttrValue]>),
    /// String-keyed map (extension over the spec's flat attr values —
    /// needed to carry `Value`-shaped payloads such as `Term::Opaque`
    /// records).
    Object(Rc<BTreeMap<Rc<str>, AttrValue>>),
}

impl AttrValue {
    /// The match-time comparison: Python `!=` semantics.
    ///
    /// Numerically lenient — `Int(1)` matches `Float(1.0)`, `Bool(true)`
    /// matches `Int(1)`, arrays compare elementwise, objects pointwise.
    /// Everything else is strict.
    pub fn match_eq(&self, other: &AttrValue) -> bool {
        use AttrValue::*;
        match (self, other) {
            (Null, Null) => true,
            (Bool(a), Bool(b)) => a == b,
            // Python bool/int/float coercion: True == 1 == 1.0.
            (Bool(b), Int(n)) | (Int(n), Bool(b)) => (*b as i64) == *n,
            (Bool(b), UInt(n)) | (UInt(n), Bool(b)) => (*b as u64) == *n,
            (Bool(b), Float(f)) | (Float(f), Bool(b)) => int_eq_float(*b as i64, *f),
            (Int(a), Int(b)) => a == b,
            (UInt(a), UInt(b)) => a == b,
            (Int(a), UInt(b)) | (UInt(b), Int(a)) => u64::try_from(*a).ok() == Some(*b),
            (Int(n), Float(f)) | (Float(f), Int(n)) => int_eq_float(*n, *f),
            (UInt(n), Float(f)) | (Float(f), UInt(n)) => uint_eq_float(*n, *f),
            (Float(a), Float(b)) => a == b, // Python numeric eq: NaN != NaN.
            (Str(a), Str(b)) => a == b,
            (Array(a), Array(b)) => {
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.match_eq(y))
            }
            (Object(a), Object(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .all(|(k, v)| b.get(k).is_some_and(|w| v.match_eq(w)))
            }
            _ => false,
        }
    }

    /// Convert a kernel `TaggedValue` through its JSON wire form.
    ///
    /// `TaggedValue` carries non-portable shapes (resources, arrows);
    /// this is a best-effort structural import — whatever
    /// `handl_value::tagged_to_value` emits is representable here.
    pub fn from_tagged(v: &handl_value::TaggedValue) -> AttrValue {
        AttrValue::from(&handl_value::tagged_to_value(v))
    }

    /// The JSON wire form of this value.
    pub fn to_json(&self) -> serde_json::Value {
        use AttrValue::*;
        match self {
            Null => serde_json::Value::Null,
            Bool(b) => serde_json::Value::Bool(*b),
            Int(n) => serde_json::Value::from(*n),
            UInt(n) => serde_json::Value::from(*n),
            Float(f) => serde_json::Value::from(*f),
            Str(s) => serde_json::Value::from(s.as_ref()),
            Array(a) => serde_json::Value::Array(a.iter().map(AttrValue::to_json).collect()),
            Object(o) => serde_json::Value::Object(
                o.iter()
                    .map(|(k, v)| (k.to_string(), v.to_json()))
                    .collect(),
            ),
        }
    }
}

/// `int == float` in Python semantics: exact integer equality.
///
/// A naive `n as f64 == f` is wrong at the edges (`i64::MAX as f64`
/// rounds to `2^63`, which `i64::MAX` does not equal). Range-check the
/// float first, then compare exactly.
fn int_eq_float(n: i64, f: f64) -> bool {
    const TWO63: f64 = 9_223_372_036_854_775_808.0;
    f.fract() == 0.0 && (-TWO63..TWO63).contains(&f) && (f as i64) == n
}

fn uint_eq_float(n: u64, f: f64) -> bool {
    const TWO64: f64 = 18_446_744_073_709_551_616.0;
    f.fract() == 0.0 && (0.0..TWO64).contains(&f) && (f as u64) == n
}

impl PartialEq for AttrValue {
    /// Spelling-strict identity — the `ENode._sig` contract.
    ///
    /// `Int(0) != Float(0.0)`, `Float(0.0) != Float(-0.0)`. Divergence
    /// from the spec, named: `repr` collapses every NaN spelling to
    /// `"nan"`; bit-strictness keeps distinct NaN payloads distinct
    /// (strictly *more* conservative for hash-consing).
    fn eq(&self, other: &AttrValue) -> bool {
        use AttrValue::*;
        match (self, other) {
            (Null, Null) => true,
            (Bool(a), Bool(b)) => a == b,
            (Int(a), Int(b)) => a == b,
            (UInt(a), UInt(b)) => a == b,
            (Float(a), Float(b)) => a.to_bits() == b.to_bits(),
            (Str(a), Str(b)) => a == b,
            (Array(a), Array(b)) => a == b,
            (Object(a), Object(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for AttrValue {}

impl Hash for AttrValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use AttrValue::*;
        std::mem::discriminant(self).hash(state);
        match self {
            Null => {}
            Bool(b) => b.hash(state),
            Int(n) => n.hash(state),
            UInt(n) => n.hash(state),
            Float(f) => f.to_bits().hash(state),
            Str(s) => s.hash(state),
            Array(a) => a.hash(state),
            Object(o) => {
                // BTreeMap: hash in (already-canonical) key order.
                for (k, v) in o.iter() {
                    k.hash(state);
                    v.hash(state);
                }
            }
        }
    }
}

impl PartialOrd for AttrValue {
    fn partial_cmp(&self, other: &AttrValue) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AttrValue {
    /// Structural total order — the `_member_key` port.
    ///
    /// Variant rank first (`Null < Bool < Int < UInt < Float < Str <
    /// Array < Object`), contents second (`total_cmp` for floats,
    /// lexicographic for composites). Deterministic across processes by
    /// construction — no `repr`, no hash order.
    fn cmp(&self, other: &AttrValue) -> Ordering {
        use AttrValue::*;
        fn rank(v: &AttrValue) -> u8 {
            match v {
                Null => 0,
                Bool(_) => 1,
                Int(_) => 2,
                UInt(_) => 3,
                Float(_) => 4,
                Str(_) => 5,
                Array(_) => 6,
                Object(_) => 7,
            }
        }
        rank(self)
            .cmp(&rank(other))
            .then_with(|| match (self, other) {
                (Bool(a), Bool(b)) => a.cmp(b),
                (Int(a), Int(b)) => a.cmp(b),
                (UInt(a), UInt(b)) => a.cmp(b),
                (Float(a), Float(b)) => a.total_cmp(b),
                (Str(a), Str(b)) => a.cmp(b),
                (Array(a), Array(b)) => a.cmp(b),
                (Object(a), Object(b)) => a.cmp(b),
                _ => Ordering::Equal,
            })
    }
}

impl From<&serde_json::Value> for AttrValue {
    fn from(v: &serde_json::Value) -> AttrValue {
        use serde_json::Value as J;
        match v {
            J::Null => AttrValue::Null,
            J::Bool(b) => AttrValue::Bool(*b),
            J::Number(n) => {
                if let Some(i) = n.as_i64() {
                    AttrValue::Int(i)
                } else if let Some(u) = n.as_u64() {
                    AttrValue::UInt(u)
                } else {
                    AttrValue::Float(n.as_f64().unwrap_or(f64::NAN))
                }
            }
            J::String(s) => AttrValue::Str(Rc::from(s.as_str())),
            J::Array(a) => AttrValue::Array(a.iter().map(AttrValue::from).collect()),
            J::Object(o) => AttrValue::Object(Rc::new(
                o.iter()
                    .map(|(k, v)| (Rc::from(k.as_str()), AttrValue::from(v)))
                    .collect(),
            )),
        }
    }
}

impl From<serde_json::Value> for AttrValue {
    fn from(v: serde_json::Value) -> AttrValue {
        AttrValue::from(&v)
    }
}

impl From<&str> for AttrValue {
    fn from(s: &str) -> AttrValue {
        AttrValue::Str(Rc::from(s))
    }
}

impl From<String> for AttrValue {
    fn from(s: String) -> AttrValue {
        AttrValue::Str(Rc::from(s.as_str()))
    }
}

impl From<i64> for AttrValue {
    fn from(n: i64) -> AttrValue {
        AttrValue::Int(n)
    }
}

impl From<u64> for AttrValue {
    fn from(n: u64) -> AttrValue {
        AttrValue::UInt(n)
    }
}

impl From<f64> for AttrValue {
    fn from(f: f64) -> AttrValue {
        AttrValue::Float(f)
    }
}

impl From<bool> for AttrValue {
    fn from(b: bool) -> AttrValue {
        AttrValue::Bool(b)
    }
}
