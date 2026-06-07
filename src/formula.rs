//! Core LTL formula representation.
//!
//! Defines the [`LtlFormula`] enum covering all standard LTL operators:
//! propositional connectives (`Not`, `And`, `Or`, `Implies`) and temporal
//! operators (`Next`, `Finally`, `Globally`, `Until`, `Release`).

use serde::{Deserialize, Serialize};
use std::fmt;

/// A Linear Temporal Logic formula.
///
/// # Operators
///
/// | Variant | Symbol | Meaning |
/// |---------|--------|---------|
/// | `Atomic(s)` | `s` | Proposition `s` holds now |
/// | `Not(φ)` | `!φ` | Negation |
/// | `And(φ, ψ)` | `φ & ψ` | Conjunction |
/// | `Or(φ, ψ)` | `φ \| ψ` | Disjunction |
/// | `Implies(φ, ψ)` | `φ -> ψ` | Implication |
/// | `Next(φ)` | `X φ` | φ holds at the next step |
/// | `Finally(φ)` | `F φ` | φ holds at some future step |
/// | `Globally(φ)` | `G φ` | φ holds at every future step |
/// | `Until(φ, ψ)` | `φ U ψ` | ψ eventually holds; φ holds until then |
/// | `Release(φ, ψ)` | `φ R ψ` | ψ holds forever, or until φ releases it |
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LtlFormula {
    /// Atomic proposition.
    Atomic(String),
    /// Logical negation.
    Not(Box<LtlFormula>),
    /// Logical conjunction.
    And(Box<LtlFormula>, Box<LtlFormula>),
    /// Logical disjunction.
    Or(Box<LtlFormula>, Box<LtlFormula>),
    /// Material implication.
    Implies(Box<LtlFormula>, Box<LtlFormula>),
    /// Next (tomorrow) operator — `X φ`.
    Next(Box<LtlFormula>),
    /// Eventually (finally) operator — `F φ`.
    Finally(Box<LtlFormula>),
    /// Always (globally) operator — `G φ`.
    Globally(Box<LtlFormula>),
    /// Strong Until — `φ U ψ`.
    Until(Box<LtlFormula>, Box<LtlFormula>),
    /// Release (dual of Until) — `φ R ψ`.
    Release(Box<LtlFormula>, Box<LtlFormula>),
}

impl fmt::Display for LtlFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LtlFormula::Atomic(s) => write!(f, "{s}"),
            LtlFormula::Not(inner) => match inner.as_ref() {
                LtlFormula::Atomic(_)
                | LtlFormula::Finally(_)
                | LtlFormula::Globally(_)
                | LtlFormula::Next(_) => {
                    write!(f, "!{}", inner)
                }
                _ => write!(f, "!({})", inner),
            },
            LtlFormula::And(l, r) => write!(f, "({} & {})", l, r),
            LtlFormula::Or(l, r) => write!(f, "({} | {})", l, r),
            LtlFormula::Implies(l, r) => write!(f, "({} -> {})", l, r),
            LtlFormula::Next(inner) => write!(f, "X({})", inner),
            LtlFormula::Finally(inner) => write!(f, "F({})", inner),
            LtlFormula::Globally(inner) => write!(f, "G({})", inner),
            LtlFormula::Until(l, r) => write!(f, "({} U {})", l, r),
            LtlFormula::Release(l, r) => write!(f, "({} R {})", l, r),
        }
    }
}

impl LtlFormula {
    /// Returns `true` if this is an atomic proposition.
    pub fn is_atomic(&self) -> bool {
        matches!(self, LtlFormula::Atomic(_))
    }

    /// Assign a stable numeric id for visited-set tracking.
    /// Uses a simple recursive hash. NOT cryptographic — just for cycle detection.
    pub fn formula_id(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        std::mem::discriminant(self).hash(&mut hasher);
        match self {
            LtlFormula::Atomic(s) => s.hash(&mut hasher),
            LtlFormula::Not(a) => {
                0u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
            }
            LtlFormula::And(a, b) => {
                1u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
                b.formula_id().hash(&mut hasher);
            }
            LtlFormula::Or(a, b) => {
                2u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
                b.formula_id().hash(&mut hasher);
            }
            LtlFormula::Implies(a, b) => {
                3u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
                b.formula_id().hash(&mut hasher);
            }
            LtlFormula::Next(a) => {
                4u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
            }
            LtlFormula::Finally(a) => {
                5u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
            }
            LtlFormula::Globally(a) => {
                6u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
            }
            LtlFormula::Until(a, b) => {
                7u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
                b.formula_id().hash(&mut hasher);
            }
            LtlFormula::Release(a, b) => {
                8u8.hash(&mut hasher);
                a.formula_id().hash(&mut hasher);
                b.formula_id().hash(&mut hasher);
            }
        }
        hasher.finish()
    }
}
