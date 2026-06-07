#[cfg(test)]
mod tests {
    use ltl_spec::{LtlFormula, SafetyLiveness, Trace, classify, parse, satisfies, to_nnf};

    // ─── Formula tests ─────────────────────────────────────────

    #[test]
    fn formula_display_atomic() {
        let f = LtlFormula::Atomic("p".into());
        assert_eq!(f.to_string(), "p");
    }

    #[test]
    fn formula_display_not() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())));
        assert_eq!(f.to_string(), "!p");
    }

    #[test]
    fn formula_display_and() {
        let f = LtlFormula::And(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        );
        assert_eq!(f.to_string(), "(p & q)");
    }

    #[test]
    fn formula_display_or() {
        let f = LtlFormula::Or(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        );
        assert_eq!(f.to_string(), "(p | q)");
    }

    #[test]
    fn formula_display_implies() {
        let f = LtlFormula::Implies(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        );
        assert_eq!(f.to_string(), "(p -> q)");
    }

    #[test]
    fn formula_display_next() {
        let f = LtlFormula::Next(Box::new(LtlFormula::Atomic("p".into())));
        assert_eq!(f.to_string(), "X(p)");
    }

    #[test]
    fn formula_display_finally() {
        let f = LtlFormula::Finally(Box::new(LtlFormula::Atomic("p".into())));
        assert_eq!(f.to_string(), "F(p)");
    }

    #[test]
    fn formula_display_globally() {
        let f = LtlFormula::Globally(Box::new(LtlFormula::Atomic("p".into())));
        assert_eq!(f.to_string(), "G(p)");
    }

    #[test]
    fn formula_display_until() {
        let f = LtlFormula::Until(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        );
        assert_eq!(f.to_string(), "(p U q)");
    }

    #[test]
    fn formula_display_release() {
        let f = LtlFormula::Release(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        );
        assert_eq!(f.to_string(), "(p R q)");
    }

    #[test]
    fn formula_is_atomic() {
        assert!(LtlFormula::Atomic("p".into()).is_atomic());
        assert!(!LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into()))).is_atomic());
    }

    #[test]
    fn formula_serde_roundtrip() {
        let f = LtlFormula::Until(
            Box::new(LtlFormula::Globally(Box::new(LtlFormula::Atomic(
                "p".into(),
            )))),
            Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atomic(
                "q".into(),
            )))),
        );
        let json = serde_json::to_string(&f).unwrap();
        let f2: LtlFormula = serde_json::from_str(&json).unwrap();
        assert_eq!(f, f2);
    }

    // ─── Parser tests ──────────────────────────────────────────

    #[test]
    fn parse_atomic() {
        let f = parse("p").unwrap();
        assert_eq!(f, LtlFormula::Atomic("p".into()));
    }

    #[test]
    fn parse_not() {
        let f = parse("!p").unwrap();
        assert_eq!(f, LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into()))));
    }

    #[test]
    fn parse_and() {
        let f = parse("p & q").unwrap();
        assert_eq!(
            f,
            LtlFormula::And(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn parse_or() {
        let f = parse("p | q").unwrap();
        assert_eq!(
            f,
            LtlFormula::Or(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn parse_implies() {
        let f = parse("p -> q").unwrap();
        assert_eq!(
            f,
            LtlFormula::Implies(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn parse_globally() {
        let f = parse("G(p)").unwrap();
        assert_eq!(
            f,
            LtlFormula::Globally(Box::new(LtlFormula::Atomic("p".into())))
        );
    }

    #[test]
    fn parse_finally() {
        let f = parse("F(p)").unwrap();
        assert_eq!(
            f,
            LtlFormula::Finally(Box::new(LtlFormula::Atomic("p".into())))
        );
    }

    #[test]
    fn parse_next() {
        let f = parse("X(p)").unwrap();
        assert_eq!(
            f,
            LtlFormula::Next(Box::new(LtlFormula::Atomic("p".into())))
        );
    }

    #[test]
    fn parse_until() {
        let f = parse("p U q").unwrap();
        assert_eq!(
            f,
            LtlFormula::Until(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn parse_release() {
        let f = parse("p R q").unwrap();
        assert_eq!(
            f,
            LtlFormula::Release(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn parse_complex() {
        let f = parse("G(p -> F(q))").unwrap();
        assert!(matches!(f, LtlFormula::Globally(_)));
    }

    #[test]
    fn parse_keyword_globally() {
        let f = parse("globally(p)").unwrap();
        assert_eq!(
            f,
            LtlFormula::Globally(Box::new(LtlFormula::Atomic("p".into())))
        );
    }

    #[test]
    fn parse_keyword_eventually() {
        let f = parse("eventually(p)").unwrap();
        assert_eq!(
            f,
            LtlFormula::Finally(Box::new(LtlFormula::Atomic("p".into())))
        );
    }

    #[test]
    fn parse_keyword_next() {
        let f = parse("next(p)").unwrap();
        assert_eq!(
            f,
            LtlFormula::Next(Box::new(LtlFormula::Atomic("p".into())))
        );
    }

    #[test]
    fn parse_keyword_until() {
        let f = parse("p until q").unwrap();
        assert_eq!(
            f,
            LtlFormula::Until(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn parse_keyword_release() {
        let f = parse("p release q").unwrap();
        assert_eq!(
            f,
            LtlFormula::Release(
                Box::new(LtlFormula::Atomic("p".into())),
                Box::new(LtlFormula::Atomic("q".into())),
            )
        );
    }

    #[test]
    fn parse_error_empty() {
        assert!(parse("").is_err());
    }

    #[test]
    fn parse_nested() {
        let f = parse("!(G(p) & F(q))").unwrap();
        assert!(matches!(f, LtlFormula::Not(_)));
    }

    // ─── Trace tests ───────────────────────────────────────────

    #[test]
    fn trace_simple() {
        let t = Trace::simple(vec![vec!["p".into()]]);
        assert_eq!(t.props_at(0), &["p".to_string()]);
    }

    #[test]
    fn trace_loop() {
        let t = Trace::new(
            vec![vec!["a".into()], vec!["b".into()], vec!["c".into()]],
            1,
        );
        assert_eq!(t.resolve_index(0), 0);
        assert_eq!(t.resolve_index(1), 1);
        assert_eq!(t.resolve_index(2), 2);
        assert_eq!(t.resolve_index(3), 1); // loops: (3-1)%2+1=2... let's check
        assert_eq!(t.resolve_index(4), 2);
    }

    #[test]
    fn trace_holds() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["q".into()]]);
        assert!(t.holds(0, "p"));
        assert!(!t.holds(0, "q"));
        assert!(t.holds(1, "q"));
    }

    #[test]
    fn trace_from_props() {
        let t = Trace::from_props(&["p", "q", "r"]);
        assert_eq!(t.len(), 3);
        assert!(t.holds(0, "p"));
        assert!(t.holds(1, "q"));
        assert!(t.holds(2, "r"));
    }

    #[test]
    fn trace_all_propositions() {
        let t = Trace::simple(vec![vec!["p".into(), "q".into()], vec!["r".into()]]);
        let props = t.all_propositions();
        assert_eq!(props.len(), 3);
    }

    #[test]
    fn trace_loop_period() {
        let t = Trace::new(
            vec![vec!["a".into()], vec!["b".into()], vec!["c".into()]],
            1,
        );
        assert_eq!(t.loop_period(), 2);
    }

    // ─── Normal form tests ─────────────────────────────────────

    #[test]
    fn nnf_atomic() {
        let f = LtlFormula::Atomic("p".into());
        assert_eq!(to_nnf(f.clone()), f);
    }

    #[test]
    fn nnf_not_atom() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())));
        assert_eq!(to_nnf(f.clone()), f);
    }

    #[test]
    fn nnf_implies_to_or() {
        let f = LtlFormula::Implies(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        );
        let nnf = to_nnf(f);
        // a -> b ≡ !a | b
        assert!(matches!(nnf, LtlFormula::Or(_, _)));
    }

    #[test]
    fn nnf_not_and_to_or() {
        let f = LtlFormula::Not(Box::new(LtlFormula::And(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        )));
        let nnf = to_nnf(f);
        assert!(matches!(nnf, LtlFormula::Or(_, _)));
    }

    #[test]
    fn nnf_not_or_to_and() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Or(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        )));
        let nnf = to_nnf(f);
        assert!(matches!(nnf, LtlFormula::And(_, _)));
    }

    #[test]
    fn nnf_not_globally_to_finally() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Globally(Box::new(
            LtlFormula::Atomic("p".into()),
        ))));
        assert!(matches!(to_nnf(f), LtlFormula::Finally(_)));
    }

    #[test]
    fn nnf_not_finally_to_globally() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Finally(Box::new(LtlFormula::Atomic(
            "p".into(),
        )))));
        assert!(matches!(to_nnf(f), LtlFormula::Globally(_)));
    }

    #[test]
    fn nnf_not_until_to_release() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Until(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        )));
        assert!(matches!(to_nnf(f), LtlFormula::Release(_, _)));
    }

    #[test]
    fn nnf_not_release_to_until() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Release(
            Box::new(LtlFormula::Atomic("p".into())),
            Box::new(LtlFormula::Atomic("q".into())),
        )));
        assert!(matches!(to_nnf(f), LtlFormula::Until(_, _)));
    }

    #[test]
    fn nnf_double_negation() {
        let f = LtlFormula::Not(Box::new(LtlFormula::Not(Box::new(LtlFormula::Atomic(
            "p".into(),
        )))));
        assert_eq!(to_nnf(f), LtlFormula::Atomic("p".into()));
    }

    // ─── Satisfaction tests ────────────────────────────────────

    #[test]
    fn sat_atomic_true() {
        let t = Trace::simple(vec![vec!["p".into()]]);
        let f = LtlFormula::Atomic("p".into());
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_atomic_false() {
        let t = Trace::simple(vec![vec!["q".into()]]);
        let f = LtlFormula::Atomic("p".into());
        assert!(!satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_not() {
        let t = Trace::simple(vec![vec!["q".into()]]);
        let f = LtlFormula::Not(Box::new(LtlFormula::Atomic("p".into())));
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_and() {
        let t = Trace::simple(vec![vec!["p".into(), "q".into()]]);
        let f = parse("p & q").unwrap();
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_and_false() {
        let t = Trace::simple(vec![vec!["p".into()]]);
        let f = parse("p & q").unwrap();
        assert!(!satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_or() {
        let t = Trace::simple(vec![vec!["p".into()]]);
        let f = parse("p | q").unwrap();
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_implies() {
        let t = Trace::simple(vec![vec!["q".into()]]);
        let f = parse("p -> q").unwrap();
        assert!(satisfies(&t, &f, 0)); // !p | q, p is false
    }

    #[test]
    fn sat_next() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["q".into()]]);
        let f = parse("X(q)").unwrap();
        assert!(satisfies(&t, &f, 0));
        assert!(!satisfies(&t, &f, 1)); // wraps back to state 0
    }

    #[test]
    fn sat_finally() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["q".into()]]);
        let f = parse("F(q)").unwrap();
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_finally_false() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["p".into()]]);
        let f = parse("F(q)").unwrap();
        assert!(!satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_globally_true() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["p".into()]]);
        let f = parse("G(p)").unwrap();
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_globally_false() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["q".into()]]);
        let f = parse("G(p)").unwrap();
        assert!(!satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_until() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["q".into()]]);
        let f = parse("p U q").unwrap();
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_until_immediate() {
        let t = Trace::simple(vec![vec!["q".into()]]);
        let f = parse("p U q").unwrap();
        assert!(satisfies(&t, &f, 0)); // q holds immediately
    }

    #[test]
    fn sat_complex_response() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["q".into()]]);
        let f = parse("G(p -> F(q))").unwrap();
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn sat_with_loop() {
        let t = Trace::new(vec![vec!["p".into()], vec!["p".into(), "q".into()]], 0);
        let f = parse("G(p)").unwrap();
        assert!(satisfies(&t, &f, 0));
    }

    // ─── Safety/Liveness tests ─────────────────────────────────

    #[test]
    fn classify_globally_is_safety() {
        let f = parse("G(p)").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Safety);
    }

    #[test]
    fn classify_finally_is_liveness() {
        let f = parse("F(p)").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Liveness);
    }

    #[test]
    fn classify_until_is_liveness() {
        let f = parse("p U q").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Liveness);
    }

    #[test]
    fn classify_release_is_safety() {
        let f = parse("p R q").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Safety);
    }

    #[test]
    fn classify_atomic_is_neither() {
        let f = parse("p").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Neither);
    }

    #[test]
    fn classify_not_is_neither() {
        let f = parse("!p").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Neither);
    }

    #[test]
    fn classify_next_is_neither() {
        let f = parse("X(p)").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Neither);
    }

    #[test]
    fn classify_and_safety_liveness_is_both() {
        let f = parse("G(p) & F(q)").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Both);
    }

    #[test]
    fn classify_or_safety_liveness_is_both() {
        let f = parse("G(p) | F(q)").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Both);
    }

    #[test]
    fn classify_implies_safety() {
        let f = parse("G(p -> q)").unwrap();
        assert_eq!(classify(&f), SafetyLiveness::Safety);
    }

    #[test]
    fn classify_display() {
        assert_eq!(SafetyLiveness::Safety.to_string(), "Safety");
        assert_eq!(SafetyLiveness::Liveness.to_string(), "Liveness");
        assert_eq!(SafetyLiveness::Both.to_string(), "Both");
        assert_eq!(SafetyLiveness::Neither.to_string(), "Neither");
    }

    #[test]
    fn classify_serde_roundtrip() {
        let c = SafetyLiveness::Both;
        let json = serde_json::to_string(&c).unwrap();
        let c2: SafetyLiveness = serde_json::from_str(&json).unwrap();
        assert_eq!(c, c2);
    }

    // ─── Integration tests ─────────────────────────────────────

    #[test]
    fn integration_parse_and_satisfy() {
        let t = Trace::simple(vec![
            vec!["ready".into()],
            vec!["running".into()],
            vec!["done".into()],
        ]);
        let f = parse("ready & X(running)").unwrap();
        assert!(satisfies(&t, &f, 0));
    }

    #[test]
    fn integration_nnf_then_satisfy() {
        let t = Trace::simple(vec![vec!["p".into()], vec!["p".into()]]);
        // !(G(p)) should be F(!p), which is false on this trace
        let f = LtlFormula::Not(Box::new(LtlFormula::Globally(Box::new(
            LtlFormula::Atomic("p".into()),
        ))));
        let nnf = to_nnf(f);
        assert!(!satisfies(&t, &nnf, 0));
    }

    #[test]
    fn integration_response_pattern() {
        // "Every request is eventually granted"
        let t = Trace::simple(vec![vec!["request".into()], vec!["granted".into()]]);
        let f = parse("G(request -> F(granted))").unwrap();
        assert!(satisfies(&t, &f, 0));
    }
}
