//! # ltl-spec: Linear Temporal Logic for Agents
//!
//! A library for parsing, normalizing, classifying, and verifying
//! Linear Temporal Logic (LTL) formulas against execution traces.
//!
//! ## Modules
//!
//! - [`formula`] — Core LTL formula types
//! - [`parser`] — String-to-formula parsing
//! - [`trace`] — Execution trace representation
//! - [`normal_form`] — Negation Normal Form conversion
//! - [`satisfaction`] — Trace satisfaction checking (iterative)
//! - [`safety_liveness`] — Safety/liveness classification

pub mod formula;
pub mod normal_form;
pub mod parser;
pub mod safety_liveness;
pub mod satisfaction;
pub mod trace;

pub use formula::LtlFormula;
pub use normal_form::to_nnf;
pub use parser::parse;
pub use safety_liveness::{SafetyLiveness, classify};
pub use satisfaction::satisfies;
pub use trace::Trace;
