//! Iterative trace satisfaction checking.
//!
//! Evaluates whether an [`LtlFormula`] holds at a given position in a
//! [`Trace`] using an **explicit work-stack** approach — no recursive
//! function calls. This prevents stack overflow on deeply nested formulas
//! and guarantees termination through:
//!
//! 1. **Bounded iteration** for `Until`/`Release`/`Finally`/`Globally` with
//!    max steps = `prefix_len * 2`.
//! 2. **Visited-set tracking** of `(position, formula_id)` pairs to detect cycles.
//!
//! The algorithm is a worklist-based evaluator that processes tasks in
//! bottom-up order, memoizing results by `(position, formula_id)`.

use crate::formula::LtlFormula;
use crate::trace::Trace;
use std::collections::{HashMap, HashSet};

/// Check if `trace` satisfies `formula` at position `start`.
///
/// Uses iterative evaluation with cycle detection to prevent infinite loops.
///
/// # Examples
///
/// ```
/// use ltl_spec::{satisfies, parse, trace::Trace};
/// let trace = Trace::simple(vec![
///     vec!["p".into()],
///     vec!["p".into(), "q".into()],
/// ]);
/// let formula = parse("G(p)").unwrap();
/// assert!(satisfies(&trace, &formula, 0));
/// ```
pub fn satisfies(trace: &Trace, formula: &LtlFormula, start: usize) -> bool {
    let max_steps = trace.len() * 2;
    eval_iterative(trace, formula, start, max_steps)
}

/// Core iterative evaluator. Uses a results cache to avoid recomputation
/// and bounded unrolling for temporal operators.
fn eval_iterative(trace: &Trace, formula: &LtlFormula, start: usize, max_steps: usize) -> bool {
    let mut cache: HashMap<(usize, u64), bool> = HashMap::new();
    let mut visited: HashSet<(usize, u64)> = HashSet::new();
    eval_formula(trace, formula, start, max_steps, &mut cache, &mut visited)
}

/// Evaluate a single formula at a position, using the cache and visited set.
/// This is iterative: it uses an explicit stack instead of recursive calls.
fn eval_formula(
    trace: &Trace,
    formula: &LtlFormula,
    start: usize,
    max_steps: usize,
    cache: &mut HashMap<(usize, u64), bool>,
    visited: &mut HashSet<(usize, u64)>,
) -> bool {
    let mut stack: Vec<Task> = vec![Task::Eval(formula.clone(), start)];

    while let Some(task) = stack.pop() {
        match task {
            Task::Eval(f, p) => {
                let fid = f.formula_id();
                let key = (p, fid);

                // Already computed
                if let Some(&_result) = cache.get(&key) {
                    continue;
                }

                match f {
                    LtlFormula::Atomic(ref prop) => {
                        cache.insert(key, trace.holds(p, prop));
                    }

                    LtlFormula::Not(ref inner) => {
                        let inner_key = (p, inner.formula_id());
                        if let Some(&v) = cache.get(&inner_key) {
                            cache.insert(key, !v);
                        } else {
                            stack.push(Task::ApplyNot { key, inner_key });
                            stack.push(Task::Eval((**inner).clone(), p));
                        }
                    }

                    LtlFormula::And(ref left, ref right) => {
                        let lk = (p, left.formula_id());
                        let rk = (p, right.formula_id());
                        if let (Some(&l), Some(&r)) = (cache.get(&lk), cache.get(&rk)) {
                            cache.insert(key, l && r);
                        } else {
                            stack.push(Task::ApplyAnd { key, lk, rk });
                            if cache.get(&rk).is_none() {
                                stack.push(Task::Eval((**right).clone(), p));
                            }
                            if cache.get(&lk).is_none() {
                                stack.push(Task::Eval((**left).clone(), p));
                            }
                        }
                    }

                    LtlFormula::Or(ref left, ref right) => {
                        let lk = (p, left.formula_id());
                        let rk = (p, right.formula_id());
                        if let (Some(&l), Some(&r)) = (cache.get(&lk), cache.get(&rk)) {
                            cache.insert(key, l || r);
                        } else {
                            stack.push(Task::ApplyOr { key, lk, rk });
                            if cache.get(&rk).is_none() {
                                stack.push(Task::Eval((**right).clone(), p));
                            }
                            if cache.get(&lk).is_none() {
                                stack.push(Task::Eval((**left).clone(), p));
                            }
                        }
                    }

                    LtlFormula::Implies(ref left, ref right) => {
                        // a -> b ≡ !a | b
                        let lk = (p, left.formula_id());
                        let rk = (p, right.formula_id());
                        if let (Some(&l), Some(&r)) = (cache.get(&lk), cache.get(&rk)) {
                            cache.insert(key, !l || r);
                        } else {
                            stack.push(Task::ApplyImplies { key, lk, rk });
                            if cache.get(&rk).is_none() {
                                stack.push(Task::Eval((**right).clone(), p));
                            }
                            if cache.get(&lk).is_none() {
                                stack.push(Task::Eval((**left).clone(), p));
                            }
                        }
                    }

                    LtlFormula::Next(ref inner) => {
                        let next_p = p + 1;
                        let ik = (next_p, inner.formula_id());
                        if let Some(&v) = cache.get(&ik) {
                            cache.insert(key, v);
                        } else {
                            stack.push(Task::ApplyNext { key, ik });
                            stack.push(Task::Eval((**inner).clone(), next_p));
                        }
                    }

                    LtlFormula::Finally(ref inner) => {
                        // F(φ) at p: ∃i ≥ p. φ holds at i
                        // Bounded iteration: check p, p+1, ..., p+max_steps-1
                        if visited.contains(&key) {
                            cache.insert(key, true); // coinductive assumption
                            continue;
                        }
                        visited.insert(key);

                        let mut found = false;
                        for step in 0..max_steps {
                            let cp = p + step;
                            let ik = (cp, inner.formula_id());
                            if let Some(&v) = cache.get(&ik) {
                                if v {
                                    found = true;
                                    break;
                                }
                            } else {
                                // Schedule remaining work: re-evaluate this Finally
                                // after computing inner at cp
                                stack.push(Task::RecheckFinally {
                                    inner: (**inner).clone(),
                                    p,
                                    step: step + 1,
                                    max_steps,
                                    key,
                                });
                                stack.push(Task::Eval((**inner).clone(), cp));
                                found = false; // can't conclude yet
                                break;
                            }
                        }
                        if found {
                            cache.insert(key, true);
                        }
                        // If not found and we exhausted steps, it's false
                        // RecheckFinally will handle this
                    }

                    LtlFormula::Globally(ref inner) => {
                        // G(φ) at p: ∀i ≥ p. φ holds at i
                        if visited.contains(&key) {
                            cache.insert(key, true);
                            continue;
                        }
                        visited.insert(key);

                        let mut holds_all = true;
                        for step in 0..max_steps {
                            let cp = p + step;
                            let ik = (cp, inner.formula_id());
                            if let Some(&v) = cache.get(&ik) {
                                if !v {
                                    holds_all = false;
                                    break;
                                }
                            } else {
                                stack.push(Task::RecheckGlobally {
                                    inner: (**inner).clone(),
                                    p,
                                    step: step + 1,
                                    max_steps,
                                    key,
                                });
                                stack.push(Task::Eval((**inner).clone(), cp));
                                holds_all = true; // optimistic
                                break;
                            }
                        }
                        if !holds_all {
                            cache.insert(key, false);
                        } else if !stack
                            .iter()
                            .any(|t| matches!(t, Task::RecheckGlobally { key: k, .. } if *k == key))
                        {
                            cache.insert(key, true);
                        }
                    }

                    LtlFormula::Until(ref left, ref right) => {
                        // φ U ψ at p: ∃j ≥ p. ψ(j) ∧ ∀i ∈ [p,j). φ(i)
                        if visited.contains(&key) {
                            cache.insert(key, true);
                            continue;
                        }
                        visited.insert(key);

                        let result = eval_until_bounded(
                            trace, left, right, p, max_steps, cache, &mut stack, key,
                        );
                        if let Some(r) = result {
                            cache.insert(key, r);
                        }
                    }

                    LtlFormula::Release(ref left, ref right) => {
                        // φ R ψ at p: ∀j ≥ p. ψ(j) ∨ ∃i ∈ [p,j]. φ(i)
                        // Equivalently: ψ holds forever, or φ releases ψ
                        if visited.contains(&key) {
                            cache.insert(key, true);
                            continue;
                        }
                        visited.insert(key);

                        let result = eval_release_bounded(
                            trace, left, right, p, max_steps, cache, &mut stack, key,
                        );
                        if let Some(r) = result {
                            cache.insert(key, r);
                        }
                    }
                }
            }

            // ─── Combine tasks ─────────────────────────────────
            Task::ApplyNot { key, inner_key } => {
                if let Some(&v) = cache.get(&inner_key) {
                    cache.insert(key, !v);
                }
            }

            Task::ApplyAnd { key, lk, rk } => {
                if let (Some(&l), Some(&r)) = (cache.get(&lk), cache.get(&rk)) {
                    cache.insert(key, l && r);
                }
            }

            Task::ApplyOr { key, lk, rk } => {
                if let (Some(&l), Some(&r)) = (cache.get(&lk), cache.get(&rk)) {
                    cache.insert(key, l || r);
                }
            }

            Task::ApplyImplies { key, lk, rk } => {
                if let (Some(&l), Some(&r)) = (cache.get(&lk), cache.get(&rk)) {
                    cache.insert(key, !l || r);
                }
            }

            Task::ApplyNext { key, ik } => {
                if let Some(&v) = cache.get(&ik) {
                    cache.insert(key, v);
                }
            }

            // ─── Recheck tasks for temporal operators ──────────
            Task::RecheckFinally {
                inner,
                p,
                step,
                max_steps,
                key,
            } => {
                // Check if inner was found true at any position so far
                let mut found = false;
                for s in 0..step {
                    let ik = (p + s, inner.formula_id());
                    if cache.get(&ik).copied().unwrap_or(false) {
                        found = true;
                        break;
                    }
                }
                if found {
                    cache.insert(key, true);
                    // Remove duplicate recheck tasks
                    stack
                        .retain(|t| !matches!(t, Task::RecheckFinally { key: k, .. } if *k == key));
                } else if step >= max_steps {
                    cache.insert(key, false);
                    stack
                        .retain(|t| !matches!(t, Task::RecheckFinally { key: k, .. } if *k == key));
                } else {
                    let cp = p + step;
                    let ik = (cp, inner.formula_id());
                    if let Some(&v) = cache.get(&ik) {
                        if v {
                            cache.insert(key, true);
                            stack.retain(
                                |t| !matches!(t, Task::RecheckFinally { key: k, .. } if *k == key),
                            );
                        } else {
                            stack.push(Task::RecheckFinally {
                                inner: inner.clone(),
                                p,
                                step: step + 1,
                                max_steps,
                                key,
                            });
                        }
                    } else {
                        stack.push(Task::RecheckFinally {
                            inner: inner.clone(),
                            p,
                            step: step + 1,
                            max_steps,
                            key,
                        });
                        stack.push(Task::Eval(inner, cp));
                    }
                }
            }

            Task::RecheckGlobally {
                inner,
                p,
                step,
                max_steps,
                key,
            } => {
                let mut holds = true;
                for s in 0..step {
                    let ik = (p + s, inner.formula_id());
                    if !cache.get(&ik).copied().unwrap_or(true) {
                        holds = false;
                        break;
                    }
                }
                if !holds {
                    cache.insert(key, false);
                    stack.retain(
                        |t| !matches!(t, Task::RecheckGlobally { key: k, .. } if *k == key),
                    );
                } else if step >= max_steps {
                    cache.insert(key, true);
                    stack.retain(
                        |t| !matches!(t, Task::RecheckGlobally { key: k, .. } if *k == key),
                    );
                } else {
                    let cp = p + step;
                    let ik = (cp, inner.formula_id());
                    if let Some(&v) = cache.get(&ik) {
                        if !v {
                            cache.insert(key, false);
                            stack.retain(
                                |t| !matches!(t, Task::RecheckGlobally { key: k, .. } if *k == key),
                            );
                        } else {
                            stack.push(Task::RecheckGlobally {
                                inner: inner.clone(),
                                p,
                                step: step + 1,
                                max_steps,
                                key,
                            });
                        }
                    } else {
                        stack.push(Task::RecheckGlobally {
                            inner: inner.clone(),
                            p,
                            step: step + 1,
                            max_steps,
                            key,
                        });
                        stack.push(Task::Eval(inner, cp));
                    }
                }
            }

            Task::RecheckUntil {
                left,
                right,
                p,
                step: _,
                max_steps,
                key,
            } => {
                let result =
                    eval_until_bounded(trace, &left, &right, p, max_steps, cache, &mut stack, key);
                if let Some(r) = result {
                    cache.insert(key, r);
                    stack.retain(|t| !matches!(t, Task::RecheckUntil { key: k, .. } if *k == key));
                }
                // If None, the recheck already pushed its own tasks
            }

            Task::RecheckRelease {
                left,
                right,
                p,
                step: _,
                max_steps,
                key,
            } => {
                let result = eval_release_bounded(
                    trace, &left, &right, p, max_steps, cache, &mut stack, key,
                );
                if let Some(r) = result {
                    cache.insert(key, r);
                    stack
                        .retain(|t| !matches!(t, Task::RecheckRelease { key: k, .. } if *k == key));
                }
            }
        }

        // Safety valve
        if cache.len() > max_steps * 20 {
            break;
        }
    }

    cache
        .get(&(start, formula.formula_id()))
        // Note: `start` here refers to the `start` parameter of `eval_iterative`
        .copied()
        .unwrap_or(false)
}

/// Bounded evaluation of `left U right` starting at position `p`.
/// Returns Some(result) if determined, None if needs more eval (tasks pushed to stack).
#[allow(clippy::too_many_arguments)]
fn eval_until_bounded(
    _trace: &Trace,
    left: &LtlFormula,
    right: &LtlFormula,
    p: usize,
    max_steps: usize,
    cache: &mut HashMap<(usize, u64), bool>,
    stack: &mut Vec<Task>,
    key: (usize, u64),
) -> Option<bool> {
    let lid = left.formula_id();
    let rid = right.formula_id();

    for step in 0..max_steps {
        let cp = p + step;
        let rk = (cp, rid);

        if let Some(&rv) = cache.get(&rk) {
            if rv {
                // Right holds at cp — check left at all [p, cp)
                let mut all_left = true;
                for prev in 0..step {
                    let lk = (p + prev, lid);
                    match cache.get(&lk) {
                        Some(&true) => {}
                        Some(&false) => {
                            all_left = false;
                            break;
                        }
                        None => {
                            // Need to evaluate left at prev position
                            stack.push(Task::RecheckUntil {
                                left: left.clone(),
                                right: right.clone(),
                                p,
                                step: step + 1,
                                max_steps,
                                key,
                            });
                            stack.push(Task::Eval(left.clone(), p + prev));
                            return None;
                        }
                    }
                }
                if all_left {
                    return Some(true);
                }
            }
        } else {
            // Need right at cp
            stack.push(Task::RecheckUntil {
                left: left.clone(),
                right: right.clone(),
                p,
                step,
                max_steps,
                key,
            });
            stack.push(Task::Eval(right.clone(), cp));
            return None;
        }
    }

    Some(false) // Exhausted steps
}

/// Bounded evaluation of `left R right` starting at position `p`.
#[allow(clippy::too_many_arguments)]
fn eval_release_bounded(
    _trace: &Trace,
    left: &LtlFormula,
    right: &LtlFormula,
    p: usize,
    max_steps: usize,
    cache: &mut HashMap<(usize, u64), bool>,
    stack: &mut Vec<Task>,
    key: (usize, u64),
) -> Option<bool> {
    let lid = left.formula_id();
    let rid = right.formula_id();

    for step in 0..max_steps {
        let cp = p + step;
        let rk = (cp, rid);
        let lk = (cp, lid);

        let rv = cache.get(&rk).copied();
        let lv = cache.get(&lk).copied();

        match (rv, lv) {
            (Some(false), _) => {
                // ψ fails — violation (release requires ψ everywhere before φ)
                return Some(false);
            }
            (Some(true), Some(true)) => {
                // Both hold: φ releases ψ at this point — satisfied
                return Some(true);
            }
            (Some(true), Some(false)) => {
                // ψ holds, φ doesn't — must continue
                continue;
            }
            (Some(true), None) => {
                // Need to evaluate left
                stack.push(Task::RecheckRelease {
                    left: left.clone(),
                    right: right.clone(),
                    p,
                    step: step + 1,
                    max_steps,
                    key,
                });
                stack.push(Task::Eval(left.clone(), cp));
                return None;
            }
            (None, Some(false)) => {
                // φ is false, need to check ψ
                stack.push(Task::RecheckRelease {
                    left: left.clone(),
                    right: right.clone(),
                    p,
                    step: step + 1,
                    max_steps,
                    key,
                });
                stack.push(Task::Eval(right.clone(), cp));
                return None;
            }
            (None, Some(true)) => {
                // Need to check ψ too (ψ must hold at every position)
                stack.push(Task::RecheckRelease {
                    left: left.clone(),
                    right: right.clone(),
                    p,
                    step: step + 1,
                    max_steps,
                    key,
                });
                stack.push(Task::Eval(right.clone(), cp));
                return None;
            }
            (None, None) => {
                stack.push(Task::RecheckRelease {
                    left: left.clone(),
                    right: right.clone(),
                    p,
                    step: step + 1,
                    max_steps,
                    key,
                });
                stack.push(Task::Eval(right.clone(), cp));
                stack.push(Task::Eval(left.clone(), cp));
                return None;
            }
        }
    }

    // If we get here, ψ held at every position we checked and no release happened
    Some(true)
}

#[derive(Debug)]
enum Task {
    // Core evaluation
    Eval(LtlFormula, usize),

    // Combine tasks (propositional)
    ApplyNot {
        key: (usize, u64),
        inner_key: (usize, u64),
    },
    ApplyAnd {
        key: (usize, u64),
        lk: (usize, u64),
        rk: (usize, u64),
    },
    ApplyOr {
        key: (usize, u64),
        lk: (usize, u64),
        rk: (usize, u64),
    },
    ApplyImplies {
        key: (usize, u64),
        lk: (usize, u64),
        rk: (usize, u64),
    },
    ApplyNext {
        key: (usize, u64),
        ik: (usize, u64),
    },

    // Recheck tasks (temporal)
    RecheckFinally {
        inner: LtlFormula,
        p: usize,
        #[allow(dead_code)]
        step: usize,
        max_steps: usize,
        key: (usize, u64),
    },
    RecheckGlobally {
        inner: LtlFormula,
        p: usize,
        #[allow(dead_code)]
        step: usize,
        max_steps: usize,
        key: (usize, u64),
    },
    RecheckUntil {
        left: LtlFormula,
        right: LtlFormula,
        p: usize,
        #[allow(dead_code)]
        step: usize,
        max_steps: usize,
        key: (usize, u64),
    },
    RecheckRelease {
        left: LtlFormula,
        right: LtlFormula,
        p: usize,
        #[allow(dead_code)]
        step: usize,
        max_steps: usize,
        key: (usize, u64),
    },
}
