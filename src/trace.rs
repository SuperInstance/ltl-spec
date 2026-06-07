//! Execution trace representation for LTL model checking.
//!
//! A [`Trace`] models an infinite execution as a finite prefix with an
//! identified loop-back point. Positions ≥ `loop_start` wrap around to
//! form a lasso-shaped (ultimately periodic) infinite trace.

use serde::{Deserialize, Serialize};
use std::collections::HashSet;

/// A finite representation of an infinite execution trace.
///
/// The trace consists of a `prefix` of states, where each state is
/// represented as the set of atomic propositions that are true at that
/// position. The `loop_start` index identifies where the trace loops
/// back, forming an ultimately periodic infinite trace:
///
/// ```text
/// prefix[0], prefix[1], ..., prefix[loop_start-1], prefix[loop_start], ..., prefix[n-1]
///                                                        ^                                    |
///                                                        +------------------------------------+
/// ```
///
/// # Examples
///
/// ```
/// use ltl_spec::trace::Trace;
/// let trace = Trace::new(vec![
///     vec!["p".into()],
///     vec!["q".into()],
///     vec!["p".into(), "q".into()],
/// ], 1);
/// assert_eq!(trace.props_at(0), &["p".to_string()][..]);
/// // Position 4 wraps within loop [1,3): (4-1)%2+1 = 2 -> props[2] = [p, q]
/// assert_eq!(trace.props_at(4), &["p".to_string(), "q".to_string()]);
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Trace {
    /// Sequence of states. Each state is the set of true propositions.
    pub prefix: Vec<Vec<String>>,
    /// Index where the infinite loop begins.
    pub loop_start: usize,
}

impl Trace {
    /// Create a new trace.
    ///
    /// # Panics
    ///
    /// Panics if `prefix` is empty or `loop_start >= prefix.len()`.
    pub fn new(prefix: Vec<Vec<String>>, loop_start: usize) -> Self {
        assert!(!prefix.is_empty(), "prefix must not be empty");
        assert!(
            loop_start < prefix.len(),
            "loop_start must be < prefix length"
        );
        Self { prefix, loop_start }
    }

    /// Create a simple trace with no loop (loop at start).
    pub fn simple(states: Vec<Vec<String>>) -> Self {
        assert!(!states.is_empty());
        Self {
            prefix: states,
            loop_start: 0,
        }
    }

    /// Create a trace where each state is a single proposition.
    pub fn from_props(props: &[&str]) -> Self {
        Self {
            prefix: props.iter().map(|p| vec![(*p).to_string()]).collect(),
            loop_start: 0,
        }
    }

    /// Get the set of true propositions at position `i`.
    ///
    /// For positions beyond the prefix, the index wraps around within
    /// the looping portion `[loop_start, prefix.len())`.
    pub fn props_at(&self, i: usize) -> &[String] {
        let actual = self.resolve_index(i);
        &self.prefix[actual]
    }

    /// Check whether proposition `prop` is true at position `i`.
    pub fn holds(&self, i: usize, prop: &str) -> bool {
        self.props_at(i).iter().any(|p| p == prop)
    }

    /// Resolve an absolute index into the actual prefix index,
    /// accounting for the loop.
    pub fn resolve_index(&self, i: usize) -> usize {
        if i < self.prefix.len() {
            i
        } else {
            let loop_len = self.prefix.len() - self.loop_start;
            if loop_len == 0 {
                self.loop_start
            } else {
                self.loop_start + (i - self.loop_start) % loop_len
            }
        }
    }

    /// Returns the total prefix length.
    pub fn len(&self) -> usize {
        self.prefix.len()
    }

    /// Returns true if the prefix is empty (should never happen with valid construction).
    pub fn is_empty(&self) -> bool {
        self.prefix.is_empty()
    }

    /// Returns the effective loop period length.
    pub fn loop_period(&self) -> usize {
        self.prefix.len() - self.loop_start
    }

    /// Returns the set of all propositions appearing in this trace.
    pub fn all_propositions(&self) -> HashSet<String> {
        self.prefix
            .iter()
            .flat_map(|state| state.iter().cloned())
            .collect()
    }
}
