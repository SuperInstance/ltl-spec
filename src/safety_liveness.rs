//! Safety and liveness classification of LTL formulas.
//!
//! Classifies formulas according to the safety/liveness taxonomy:
//!
//! - **Safety** — "something bad never happens" (`G(φ)`, `R`)
//! - **Liveness** — "something good eventually happens" (`F(φ)`, `U`)
//!
//! A formula can be purely safety, purely liveness, both, or neither.

use crate::formula::LtlFormula;
use serde::{Deserialize, Serialize};

/// Classification of an LTL formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SafetyLiveness {
    /// Pure safety property (e.g., `G(p)`).
    Safety,
    /// Pure liveness property (e.g., `F(p)`).
    Liveness,
    /// Contains both safety and liveness aspects.
    Both,
    /// Neither safety nor liveness (e.g., a bare atomic proposition).
    Neither,
}

impl std::fmt::Display for SafetyLiveness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SafetyLiveness::Safety => write!(f, "Safety"),
            SafetyLiveness::Liveness => write!(f, "Liveness"),
            SafetyLiveness::Both => write!(f, "Both"),
            SafetyLiveness::Neither => write!(f, "Neither"),
        }
    }
}

/// Classify an LTL formula as safety, liveness, both, or neither.
///
/// # Rules
///
/// - `Globally(φ)` → Safety
/// - `Release(a, b)` → Safety
/// - `Finally(φ)` → Liveness
/// - `Until(a, b)` → Liveness
/// - Combinations are merged: `And(Safety, Liveness)` → Both
/// - `Atomic`, `Not`, `Next` → Neither
///
/// # Examples
///
/// ```
/// use ltl_spec::{classify, parse, SafetyLiveness};
/// let f = parse("G(p)").unwrap();
/// assert_eq!(classify(&f), SafetyLiveness::Safety);
///
/// let f = parse("F(q)").unwrap();
/// assert_eq!(classify(&f), SafetyLiveness::Liveness);
///
/// let f = parse("G(p) & F(q)").unwrap();
/// assert_eq!(classify(&f), SafetyLiveness::Both);
/// ```
pub fn classify(formula: &LtlFormula) -> SafetyLiveness {
    let (safety, liveness) = classify_inner(formula);
    match (safety, liveness) {
        (true, true) => SafetyLiveness::Both,
        (true, false) => SafetyLiveness::Safety,
        (false, true) => SafetyLiveness::Liveness,
        (false, false) => SafetyLiveness::Neither,
    }
}

/// Returns (is_safety, is_liveness) flags.
fn classify_inner(formula: &LtlFormula) -> (bool, bool) {
    match formula {
        LtlFormula::Atomic(_) | LtlFormula::Not(_) | LtlFormula::Next(_) => (false, false),

        LtlFormula::And(a, b) | LtlFormula::Or(a, b) => {
            let (sa, la) = classify_inner(a);
            let (sb, lb) = classify_inner(b);
            (sa || sb, la || lb)
        }

        LtlFormula::Implies(a, b) => {
            let (sa, la) = classify_inner(a);
            let (sb, lb) = classify_inner(b);
            (sa || sb, la || lb)
        }

        LtlFormula::Globally(inner) => {
            let (_s, l) = classify_inner(inner);
            (true, l) // Globally is always at least safety
        }

        LtlFormula::Finally(inner) => {
            let (s, _l) = classify_inner(inner);
            (s, true) // Finally is always at least liveness
        }

        LtlFormula::Release(_, _) => {
            // Release is a safety property
            (true, false)
        }

        LtlFormula::Until(_, _) => {
            // Until is a liveness property
            (false, true)
        }
    }
}
