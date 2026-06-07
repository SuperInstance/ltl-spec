# ltl-spec

**Linear Temporal Logic (LTL) for Rust agents.**

Parse, normalize, classify, and verify execution traces against temporal
specifications. Built for model checking, runtime verification, and
agent-based systems where correctness matters.

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Theory](#theory)
   - [Syntax](#syntax)
   - [Semantics](#semantics)
   - [Negation Normal Form](#negation-normal-form)
   - [Safety and Liveness](#safety-and-liveness)
4. [Quick Start](#quick-start)
5. [Module Reference](#module-reference)
6. [Examples](#examples)
   - [Example 1: Request-Response Pattern](#example-1-request-response-pattern)
   - [Example 2: Mutual Exclusion](#example-2-mutual-exclusion)
   - [Example 3: Liveness in a Protocol](#example-3-liveness-in-a-protocol)
7. [API Reference](#api-reference)
8. [Design Decisions](#design-decisions)
9. [Performance](#performance)
10. [Limitations](#limitations)
11. [References](#references)
12. [License](#license)

---

## Overview

**ltl-spec** is a no-std-compatible (with `serde`) library for working with
Linear Temporal Logic (LTL) formulas in Rust. LTL extends classical
propositional logic with temporal operators that reason about the future
evolution of a system over time.

Originally introduced by Amir Pnueli in 1977 \[1\], LTL has become a
foundational tool in formal verification, model checking, and runtime
monitoring. This library provides:

- **Parsing**: Convert human-readable strings like `G(p -> F(q))` into
  structured formula representations.
- **Normalization**: Transform formulas into Negation Normal Form (NNF)
  where negation appears only on atoms.
- **Classification**: Determine whether a formula represents a safety
  property, a liveness property, or both.
- **Trace Verification**: Check whether an execution trace satisfies an
  LTL formula using an iterative (non-recursive) evaluation algorithm.

The library uses zero external dependencies beyond `serde` for
serialization.

### When to Use This

- **Runtime verification**: Monitor agent behavior against temporal
  specifications at runtime.
- **Model checking**: Verify finite-state system models against LTL
  properties.
- **Specification testing**: Write tests that check temporal properties
  of your system traces.
- **Education**: Learn about temporal logic through a clean, documented
  implementation.

---

## Architecture

```
                         ┌─────────────────────────────────────────┐
                         │              ltl-spec                    │
                         └────────────┬────────────────────────────┘
                                      │
              ┌───────────────────────┼───────────────────────┐
              │                       │                       │
    ┌─────────▼──────────┐ ┌─────────▼──────────┐ ┌──────────▼─────────┐
    │      formula       │ │       parser        │ │       trace        │
    │                    │ │                     │ │                    │
    │  LtlFormula enum   │ │  Recursive-descent  │ │  Finite prefix +   │
    │  Display impl      │ │  tokenizer + parser │ │  loop-back index   │
    │  Serialize/Deserialize│  Keyword aliases   │ │  Infinite trace    │
    └────────────────────┘ └─────────────────────┘ │  model             │
                                                └────────────────────┘
              │                       │                       │
    ┌─────────▼──────────┐ ┌─────────▼──────────┐ ┌──────────▼─────────┐
    │   normal_form      │ │  safety_liveness    │ │   satisfaction     │
    │                    │ │                     │ │                    │
    │  NNF conversion    │ │  Safety/Liveness    │ │  Iterative trace   │
    │  De Morgan's laws  │ │  classification     │ │  evaluation with   │
    │  Temporal duals    │ │                     │ │  explicit stack    │
    └────────────────────┘ └─────────────────────┘ │  Cycle detection   │
                                                │  Bounded iteration  │
                                                └────────────────────┘

    Data flow:
    ┌────────┐    ┌────────┐    ┌──────────┐    ┌─────────────┐
    │ String │───▶│ Parser │───▶│ LtlFormula│───▶│ Normal Form │
    └────────┘    └────────┘    └─────┬─────┘    └──────┬──────┘
                                      │                  │
                                      ▼                  ▼
                               ┌─────────────┐   ┌──────────────┐
                               │ Classify    │   │ Evaluate on  │
                               │ Safety/     │   │ Trace        │
                               │ Liveness    │   │ (iterative)  │
                               └─────────────┘   └──────────────┘
```

### Module Table

| Module | Purpose | Key Types |
|--------|---------|-----------|
| `formula` | Core LTL formula representation | `LtlFormula` enum |
| `parser` | String → formula conversion | `parse()` function |
| `trace` | Execution trace model | `Trace` struct |
| `normal_form` | Negation Normal Form | `to_nnf()` function |
| `satisfaction` | Trace verification | `satisfies()` function |
| `safety_liveness` | Property classification | `SafetyLiveness` enum, `classify()` |

---

## Theory

### Syntax

LTL formulas are built from atomic propositions, Boolean connectives,
and temporal operators. The formal grammar is:

```
φ ::= p                           (atomic proposition)
    | ¬φ                           (negation)
    | φ ∧ ψ                        (conjunction)
    | φ ∨ ψ                        (disjunction)
    | φ → ψ                        (implication)
    | X φ                          (next)
    | F φ                          (eventually / finally)
    | G φ                          (always / globally)
    | φ U ψ                        (strong until)
    | φ R ψ                        (release)
```

**Operator Precedence** (highest to lowest):

1. Atoms, parenthesized expressions
2. Unary operators: `¬`, `X`, `F`, `G`
3. `∧`
4. `∨`
5. `U`, `R`
6. `→`

### Semantics

Given an infinite sequence of states σ = s₀, s₁, s₂, ..., where each
state sᵢ is a set of atomic propositions, the satisfaction relation
σ ⊧ φ (trace σ satisfies formula φ) is defined as follows:

| Formula | Meaning |
|---------|---------|
| σ ⊧ p | p ∈ s₀ (proposition p is true at the current state) |
| σ ⊧ ¬φ | σ ⊭ φ (φ does not hold) |
| σ ⊧ φ ∧ ψ | σ ⊧ φ and σ ⊧ ψ |
| σ ⊧ φ ∨ ψ | σ ⊧ φ or σ ⊧ ψ |
| σ ⊧ φ → ψ | σ ⊧ ¬φ or σ ⊧ ψ |
| σ ⊧ X φ | σ¹ ⊧ φ (φ holds at the next state) |
| σ ⊧ F φ | ∃i ≥ 0. σⁱ ⊧ φ (φ holds at some future state) |
| σ ⊧ G φ | ∀i ≥ 0. σⁱ ⊧ φ (φ holds at every future state) |
| σ ⊧ φ U ψ | ∃j ≥ 0. σʲ ⊧ ψ ∧ ∀0 ≤ i < j. σⁱ ⊧ φ |
| σ ⊧ φ R ψ | ∀j ≥ 0. (σʲ ⊧ ψ ∨ ∃0 ≤ i ≤ j. σⁱ ⊧ φ) |

Where σⁱ denotes the suffix of σ starting at position i.

**Dualities:**

- `F φ ≡ true U φ` (eventually is "true until")
- `G φ ≡ false R φ` (globally is "false releases")
- `φ U ψ ≡ ¬(¬ψ R ¬φ)` (until and release are duals)
- `X φ ≡ ¬X ¬φ` (next is self-dual)

### Negation Normal Form

Negation Normal Form (NNF) is a canonical representation where negation
(¬) appears only directly in front of atomic propositions. All other
operators are preserved.

**Transformation rules:**

| Original | NNF equivalent |
|----------|---------------|
| ¬¬φ | φ |
| ¬(φ ∧ ψ) | ¬φ ∨ ¬ψ |
| ¬(φ ∨ ψ) | ¬φ ∧ ¬ψ |
| ¬G(φ) | F(¬φ) |
| ¬F(φ) | G(¬φ) |
| ¬X(φ) | X(¬φ) |
| ¬(φ U ψ) | ¬φ R ¬ψ |
| ¬(φ R ψ) | ¬φ U ¬ψ |
| φ → ψ | ¬φ ∨ ψ |

After NNF conversion, the formula uses only: `∧`, `∨`, `U`, `R`, `X`,
`F`, `G`, atoms, and negated atoms.

### Safety and Liveness

LTL properties can be classified into two fundamental categories \[4\]:

**Safety properties** assert that "something bad never happens."
Formally, a safety property is violated by a finite prefix — there
exists a "bad prefix" after which no extension can satisfy the
property.

- `G(φ)` — always safety
- `φ R ψ` — release safety

**Liveness properties** assert that "something good eventually happens."
A liveness property cannot be violated by any finite prefix — every
finite trace can be extended to satisfy the property.

- `F(φ)` — eventually liveness
- `φ U ψ` — until liveness

**Decomposition theorem** (Alpern & Schneider, 1987 \[4\]):
Every LTL property is the intersection of a safety property and a
liveness property. In practice, many interesting properties are purely
safety or purely liveness.

Our classifier returns:

| Result | Meaning |
|--------|---------|
| `Safety` | Pure safety (only G, R) |
| `Liveness` | Pure liveness (only F, U) |
| `Both` | Contains both safety and liveness aspects |
| `Neither` | No temporal classification (e.g., bare atoms) |

---

## Quick Start

Add to your `Cargo.toml`:

```toml
[dependencies]
ltl-spec = "0.1"
serde = { version = "1", features = ["derive"] }
```

Basic usage:

```rust
use ltl_spec::{parse, satisfies, classify, to_nnf, SafetyLiveness, Trace};

// Parse a formula
let formula = parse("G(request -> F(response))").unwrap();
println!("Formula: {}", formula);

// Classify it
assert_eq!(classify(&formula), SafetyLiveness::Safety);

// Create a trace
let trace = Trace::simple(vec![
    vec!["request".into()],
    vec!["response".into()],
]);

// Verify
assert!(satisfies(&trace, &formula, 0));
```

---

## Module Reference

### `formula` — Core Types

The `LtlFormula` enum is the central data type. All operators are
represented as enum variants:

```rust
use ltl_spec::LtlFormula;

let p = LtlFormula::Atomic("p".into());
let not_p = LtlFormula::Not(Box::new(p.clone()));
let p_and_q = LtlFormula::And(
    Box::new(p.clone()),
    Box::new(LtlFormula::Atomic("q".into())),
);
let always_p = LtlFormula::Globally(Box::new(p.clone()));

// Display formatting
assert_eq!(p.to_string(), "p");
assert_eq!(not_p.to_string(), "!p");
assert_eq!(p_and_q.to_string(), "(p & q)");
assert_eq!(always_p.to_string(), "G(p)");
```

All variants derive `Debug`, `Clone`, `PartialEq`, `Serialize`, and
`Deserialize`.

### `parser` — String Parsing

The parser supports multiple syntax conventions:

```rust
use ltl_spec::parse;

// Standard notation
parse("G(p -> F(q))")?;

// Keyword aliases
parse("globally(p -> eventually(q))")?;
parse("always(p -> eventually(q))")?;

// Operators
parse("p U q")?;        // until
parse("p R q")?;        // release
parse("p until q")?;    // keyword alias
parse("!p & (q | r)")?; // propositional
```

### `trace` — Execution Traces

Traces model infinite executions as finite prefixes with a loop point:

```rust
use ltl_spec::Trace;

// Simple trace: loops from the beginning
let t = Trace::simple(vec![
    vec!["p".into()],
    vec!["q".into()],
]);

// Lasso trace: prefix [0,1), loop [1,3)
let t = Trace::new(vec![
    vec!["init".into()],      // position 0 (prefix)
    vec!["ready".into()],     // position 1 (loop start)
    vec!["running".into()],   // position 2
    vec!["ready".into()],     // position 3
], 1);
// Positions 4,5,6,... map to 1,2,3,1,2,3,...
```

### `normal_form` — NNF Conversion

```rust
use ltl_spec::{parse, to_nnf};

let f = parse("!(G(p) & F(q))")?;
let nnf = to_nnf(f);
// !(G(p) & F(q)) → F(!p) | G(!q)
println!("NNF: {}", nnf);
```

### `satisfaction` — Trace Verification

```rust
use ltl_spec::{parse, satisfies, Trace};

let trace = Trace::simple(vec![
    vec!["a".into()],
    vec!["b".into()],
]);

assert!(satisfies(&trace, &parse("a")?, 0));
assert!(satisfies(&trace, &parse("F(b)")?, 0));
assert!(satisfies(&trace, &parse("G(a | b)")?, 0));
assert!(!satisfies(&trace, &parse("G(a)")?, 0));
```

### `safety_liveness` — Classification

```rust
use ltl_spec::{parse, classify, SafetyLiveness};

assert_eq!(classify(&parse("G(p)")?), SafetyLiveness::Safety);
assert_eq!(classify(&parse("F(q)")?), SafetyLiveness::Liveness);
assert_eq!(classify(&parse("G(p) & F(q)")?), SafetyLiveness::Both);
assert_eq!(classify(&parse("p")?), SafetyLiveness::Neither);
```

---

## Examples

### Example 1: Request-Response Pattern

A classic specification: every request must eventually receive a
response.

```rust
use ltl_spec::{parse, satisfies, classify, SafetyLiveness, Trace};

fn main() {
    // Specification: "Globally, if request then eventually response"
    let spec = parse("G(request -> F(response))").unwrap();
    println!("Spec: {}", spec);
    println!("Classification: {}", classify(&spec));

    // Good trace: every request is followed by a response
    let good = Trace::simple(vec![
        vec!["request".into()],
        vec!["response".into()],
    ]);
    assert!(satisfies(&good, &spec, 0), "Good trace should satisfy spec");

    // Bad trace: request with no response
    let bad = Trace::simple(vec![
        vec!["request".into()],
        vec!["request".into()], // no response!
    ]);
    assert!(!satisfies(&bad, &spec, 0), "Bad trace should violate spec");

    // Empty trace: no request, vacuously true
    let empty = Trace::simple(vec![
        vec!["idle".into()],
        vec!["idle".into()],
    ]);
    assert!(satisfies(&empty, &spec, 0), "Vacuous satisfaction");

    println!("All request-response checks passed!");
}
```

### Example 2: Mutual Exclusion

Verify that two processes never enter their critical sections
simultaneously.

```rust
use ltl_spec::{parse, satisfies, Trace};

fn main() {
    // Safety: it is always the case that NOT (p1_cs AND p2_cs)
    let mutex = parse("G(!(p1_cs & p2_cs))").unwrap();

    // Valid trace: processes take turns
    let valid = Trace::simple(vec![
        vec!["idle".into()],
        vec!["p1_cs".into()],
        vec!["idle".into()],
        vec!["p2_cs".into()],
    ]);
    assert!(satisfies(&valid, &mutex, 0));

    // Invalid trace: both in CS at position 1
    let invalid = Trace::simple(vec![
        vec!["idle".into()],
        vec!["p1_cs".into(), "p2_cs".into()], // both in CS!
        vec!["idle".into()],
    ]);
    assert!(!satisfies(&invalid, &mutex, 0));

    // Liveness: each process eventually enters its CS
    let liveness_p1 = parse("G(F(p1_cs))").unwrap();
    let liveness_p2 = parse("G(F(p2_cs))").unwrap();

    let fair = Trace::simple(vec![
        vec!["p1_cs".into()],
        vec!["p2_cs".into()],
    ]);
    assert!(satisfies(&fair, &liveness_p1, 0));
    assert!(satisfies(&fair, &liveness_p2, 0));

    println!("Mutual exclusion verification complete!");
}
```

### Example 3: Liveness in a Protocol

A network protocol where messages must eventually be delivered, using
Until and Release operators.

```rust
use ltl_spec::{parse, satisfies, to_nnf, classify, SafetyLiveness, Trace};

fn main() {
    // "Sent messages are eventually received" using Until
    // send U ack: send holds until ack becomes true
    let delivery = parse("send U ack").unwrap();
    println!("Delivery spec: {}", delivery);
    println!("Classification: {}", classify(&delivery));

    // Trace where message is sent then acknowledged
    let trace1 = Trace::simple(vec![
        vec!["send".into()],  // send is true
        vec!["ack".into()],   // ack becomes true
    ]);
    assert!(satisfies(&trace1, &delivery, 0));

    // Using Release for safety: "connection stays open until close releases it"
    let conn_safety = parse("open R close").unwrap();
    println!("Connection safety: {}", conn_safety);
    println!("Classification: {}", classify(&conn_safety));

    // Convert to NNF for analysis
    let complex = parse("!(send U ack)").unwrap();
    let nnf = to_nnf(complex);
    println!("NNF of !(send U ack): {}", nnf);
    // Expected: !send R !ack

    // Combined spec: always eventually deliver
    let combined = parse("G(send -> F(ack))").unwrap();
    let trace2 = Trace::simple(vec![
        vec!["send".into()],
        vec!["ack".into()],
    ]);
    assert!(satisfies(&trace2, &combined, 0));

    println!("Protocol verification complete!");
}
```

---

## API Reference

### Core Functions

#### `parse(input: &str) -> Result<LtlFormula, String>`

Parse an LTL formula from a string.

```rust
let f = parse("G(p -> F(q))")?;
```

#### `to_nnf(formula: LtlFormula) -> LtlFormula`

Convert a formula to Negation Normal Form.

```rust
let nnf = to_nnf(parse("!(p & q)")?);
```

#### `satisfies(trace: &Trace, formula: &LtlFormula, position: usize) -> bool`

Check if a trace satisfies a formula at a given position. Uses
iterative evaluation with bounded iteration and cycle detection.

```rust
let holds = satisfies(&trace, &formula, 0);
```

#### `classify(formula: &LtlFormula) -> SafetyLiveness`

Classify a formula as safety, liveness, both, or neither.

```rust
match classify(&formula) {
    SafetyLiveness::Safety => println!("Safety property"),
    SafetyLiveness::Liveness => println!("Liveness property"),
    SafetyLiveness::Both => println!("Mixed property"),
    SafetyLiveness::Neither => println!("No classification"),
}
```

### Types

#### `LtlFormula`

```rust
pub enum LtlFormula {
    Atomic(String),
    Not(Box<LtlFormula>),
    And(Box<LtlFormula>, Box<LtlFormula>),
    Or(Box<LtlFormula>, Box<LtlFormula>),
    Implies(Box<LtlFormula>, Box<LtlFormula>),
    Next(Box<LtlFormula>),
    Finally(Box<LtlFormula>),
    Globally(Box<LtlFormula>),
    Until(Box<LtlFormula>, Box<LtlFormula>),
    Release(Box<LtlFormula>, Box<LtlFormula>),
}
```

Implements: `Debug`, `Clone`, `PartialEq`, `Display`, `Serialize`,
`Deserialize`.

#### `Trace`

```rust
pub struct Trace {
    pub prefix: Vec<Vec<String>>,
    pub loop_start: usize,
}
```

Represents an infinite trace as a finite prefix with a loop point.

#### `SafetyLiveness`

```rust
pub enum SafetyLiveness {
    Safety,
    Liveness,
    Both,
    Neither,
}
```

---

## Design Decisions

### Iterative Satisfaction Checking

The satisfaction checker uses an **explicit work-stack** approach
instead of recursive function calls. This was chosen for several
reasons:

1. **Stack safety**: Deep formula nesting (e.g., `G(F(G(F(...))))`)
   won't overflow the call stack.
2. **Cycle detection**: Temporal operators like `G(G(p))` can cause
   infinite recursion. The iterative approach tracks visited
   `(position, formula_id)` pairs to detect and break cycles.
3. **Bounded evaluation**: `Until`, `Release`, `Finally`, and `Globally`
   are evaluated over a bounded number of steps (2× prefix length),
   guaranteeing termination.

### Trace as Lasso

Rather than requiring truly infinite traces, we represent them as
finite prefixes with a loop-back point. This "lasso" (or ultimately
periodic) structure is sufficient for most model-checking scenarios:

```
prefix[0] ... prefix[loop_start-1] → prefix[loop_start] ... prefix[n-1]
                                         ↑_________________________|
```

### Serde-Only Dependencies

The only external dependency is `serde`. This keeps the crate lean
while enabling serialization for formula persistence, network
transmission, and debugging.

### Keyword Aliases

The parser supports both single-letter (`G`, `F`, `X`, `U`, `R`) and
full-word (`globally`, `eventually`, `next`, `until`, `release`)
variants. This makes formulas readable in both compact and verbose
styles.

### No Implies in NNF

Implication (`→`) is eliminated during NNF conversion using the
equivalence `φ → ψ ≡ ¬φ ∨ ψ`. This reduces the operator set and
simplifies downstream analysis.

---

## Performance

The iterative evaluator has the following complexity characteristics:

| Operator | Time Complexity | Notes |
|----------|----------------|-------|
| `Atomic` | O(1) | Direct lookup |
| `Not`, `And`, `Or`, `Implies` | O(1) per combine | Memoized |
| `Next` | O(1) | Single position shift |
| `Finally`, `Globally` | O(n) | Bounded to 2n steps |
| `Until`, `Release` | O(n²) worst case | Bounded iteration with left-checking |

Where `n` = trace prefix length.

The memoization cache ensures each `(position, formula_id)` pair is
computed at most once.

---

## Limitations

1. **Finite trace approximation**: The satisfaction checker evaluates
   over a bounded number of steps (2× prefix length). For traces with
   complex looping behavior, this may give incorrect results for
   deeply nested temporal formulas.

2. **No past-time operators**: Only future-time LTL is supported.
   Past-time operators (Yesterday, Since, Previously) are not included.

3. **No quantitative reasoning**: No support for metric temporal logic
   (MTL) or timed specifications.

4. **Simple cycle detection**: The coinductive assumption (treating
   revisited states as true) may give false positives in rare cases.
   For production model checking, consider dedicated model checkers
   like NuSMV or SPIN.

5. **No LTL-to-Büchi conversion**: Does not convert formulas to Büchi
   automata for automata-theoretic model checking.

---

## References

1. **Pnueli, A.** (1977). "The temporal logic of programs." *18th
   Annual Symposium on Foundations of Computer Science (FOCS)*, IEEE,
   pp. 46–57. — The foundational paper introducing Linear Temporal Logic
   for program verification.

2. **Baier, C. & Katoen, J.-P.** (2008). *Principles of Model
   Checking*. MIT Press. — Comprehensive textbook covering LTL, CTL,
   and model-checking algorithms.

3. **Clarke, E.M., Grumberg, O., & Peled, D.A.** (1999). *Model
   Checking*. MIT Press. — Classical reference on model checking
   techniques and temporal logics.

4. **Alpern, B. & Schneider, F.B.** (1987). "Recognizing safety and
   liveness." *Distributed Computing*, 2(3), pp. 117–126. — The
   foundational paper on the safety-liveness classification.

5. **Vardi, M.Y.** (1996). "An automata-theoretic approach to linear
   temporal logic." *Logics for Concurrency*, Springer, pp. 238–266.
   — Automata-theoretic approach to LTL model checking.

6. **Emerson, E.A.** (1990). "Temporal and modal logic." *Handbook of
   Theoretical Computer Science, Volume B*, Elsevier, pp. 995–1072.
   — Comprehensive survey of temporal logics.

7. **Manna, Z. & Pnueli, A.** (1995). *Temporal Verification of
   Reactive Systems: Safety*. Springer. — Definitive treatment of
   safety properties in temporal logic.

---

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or
  http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this work by you, as defined in the
Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
