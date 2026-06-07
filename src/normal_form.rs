//! Negation Normal Form (NNF) conversion.
//!
//! Transforms an LTL formula so that negation appears only directly
//! in front of atomic propositions. All other operators are pushed
//! inward using De Morgan's laws and temporal dualities:
//!
//! | Original | NNF |
//! |----------|-----|
//! | `!(a & b)` | `!a \| !b` |
//! | `!(a \| b)` | `!a & !b` |
//! | `!G(φ)` | `F(!φ)` |
//! | `!F(φ)` | `G(!φ)` |
//! | `!X(φ)` | `X(!φ)` |
//! | `!(a U b)` | `!a R !b` |
//! | `!(a R b)` | `!a U !b` |
//! | `a -> b` | `!a \| b` |
//!
//! After NNF conversion, the formula uses only `&`, `|`, `U`, `R`,
//! `X`, `F`, `G`, and negated atoms.

use crate::formula::LtlFormula;

/// Convert a formula to Negation Normal Form.
///
/// # Examples
///
/// ```
/// use ltl_spec::{LtlFormula, to_nnf};
/// let f = LtlFormula::Not(Box::new(LtlFormula::And(
///     Box::new(LtlFormula::Atomic("p".into())),
///     Box::new(LtlFormula::Atomic("q".into())),
/// )));
/// let nnf = to_nnf(f);
/// // !(p & q) => !p | !q
/// assert!(matches!(nnf, LtlFormula::Or(_, _)));
/// ```
pub fn to_nnf(formula: LtlFormula) -> LtlFormula {
    match formula {
        // Base cases
        LtlFormula::Atomic(_) => formula,

        // Push negation inward
        LtlFormula::Not(inner) => push_negation(*inner),

        // Eliminate implication: a -> b ≡ !a | b
        LtlFormula::Implies(a, b) => {
            let a_nnf = to_nnf(*a);
            let b_nnf = to_nnf(*b);
            let not_a = negate_atom_or_propagate(a_nnf);
            LtlFormula::Or(Box::new(not_a), Box::new(b_nnf))
        }

        // Binary propositional: recurse
        LtlFormula::And(a, b) => LtlFormula::And(Box::new(to_nnf(*a)), Box::new(to_nnf(*b))),
        LtlFormula::Or(a, b) => LtlFormula::Or(Box::new(to_nnf(*a)), Box::new(to_nnf(*b))),

        // Unary temporal: recurse
        LtlFormula::Next(a) => LtlFormula::Next(Box::new(to_nnf(*a))),
        LtlFormula::Finally(a) => LtlFormula::Finally(Box::new(to_nnf(*a))),
        LtlFormula::Globally(a) => LtlFormula::Globally(Box::new(to_nnf(*a))),

        // Binary temporal: recurse
        LtlFormula::Until(a, b) => LtlFormula::Until(Box::new(to_nnf(*a)), Box::new(to_nnf(*b))),
        LtlFormula::Release(a, b) => {
            LtlFormula::Release(Box::new(to_nnf(*a)), Box::new(to_nnf(*b)))
        }
    }
}

/// Push a negation one level inward (De Morgan + temporal duals).
fn push_negation(formula: LtlFormula) -> LtlFormula {
    match formula {
        // Double negation elimination
        LtlFormula::Not(inner) => to_nnf(*inner),

        // De Morgan
        LtlFormula::And(a, b) => {
            LtlFormula::Or(Box::new(push_negation(*a)), Box::new(push_negation(*b)))
        }
        LtlFormula::Or(a, b) => {
            LtlFormula::And(Box::new(push_negation(*a)), Box::new(push_negation(*b)))
        }

        // Temporal duals
        LtlFormula::Globally(a) => LtlFormula::Finally(Box::new(push_negation(*a))),
        LtlFormula::Finally(a) => LtlFormula::Globally(Box::new(push_negation(*a))),
        LtlFormula::Next(a) => LtlFormula::Next(Box::new(push_negation(*a))),
        LtlFormula::Until(a, b) => {
            LtlFormula::Release(Box::new(push_negation(*a)), Box::new(push_negation(*b)))
        }
        LtlFormula::Release(a, b) => {
            LtlFormula::Until(Box::new(push_negation(*a)), Box::new(push_negation(*b)))
        }

        // Implication: !(a -> b) = a & !b
        LtlFormula::Implies(a, b) => {
            LtlFormula::And(Box::new(to_nnf(*a)), Box::new(push_negation(*b)))
        }

        // Negated atom: keep as Not(Atomic)
        LtlFormula::Atomic(_) => LtlFormula::Not(Box::new(formula)),
    }
}

/// Negate a formula that is already in (or being converted to) NNF.
/// If it's an atom, wrap in Not. Otherwise, push negation.
fn negate_atom_or_propagate(f: LtlFormula) -> LtlFormula {
    match f {
        LtlFormula::Atomic(_) => LtlFormula::Not(Box::new(f)),
        other => push_negation(other),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nnf_double_negation() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic(
            "p".into(),
        )))));
        assert_eq!(to_nnf(f), LtlFormula::Atomic("p".into()));
    }

    #[test]
    fn test_nnf_not_and() {
        let f = LtlFormula::Not(Box::new(LtlFormula::And(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        )));
        let result = to_nnf(f);
        assert!(matches!(result, LtlFormula::Or(_, _)));
    }

    #[test]
    fn test_nnf_not_or() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Or(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        )));
        let result = to_nnf(f);
        assert!(matches!(result, LtlFormula::And(_, _)));
    }

    #[test]
    fn test_nnf_not_globally() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Globally(Box::new(
            LtlFormula::Atomic("p".into()),
        ))));
        let result = to_nnf(f);
        assert!(matches!(result, LtlFormula::Finally(_)));
    }

    #[test]
    fn test_nnf_not_finally() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atomic(
            "p".into(),
        )))));
        let result = to_nnf(f);
        assert!(matches!(result, LtlFormula::Globally(_)));
    }

    #[test]
    fn test_nnf_not_until() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Until(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        )));
        let result = to_nnf(f);
        assert!(matches!(result, LtlFormula::Release(_, _)));
    }

    #[test]
    fn test_nnf_not_release() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Release(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        )));
        let result = to_nnf(f);
        assert!(matches!(result, LtlFormula::Until(_, _)));
    }

    #[test]
    fn test_nnf_implies() {
        let f = LtlFormula::Implies(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        );
        let result = to_nnf(f);
        assert!(matches!(result, LtlFormula::Or(_, _)));
    }
}
