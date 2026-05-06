-- ID 099: Multi-Constraint Enumeration Delayed-Failure Instance
--
-- Catalog ID 99 (Hallucinations paper).
-- Concrete witness for delayed-constraint failure under exact-count
-- enumeration constraints.
--
-- Statement: a generation task imposing an exact-count constraint
-- (output exactly K items satisfying property P) can be locally
-- satisfied at every individual step (each item passes the plausibility
-- check) while becoming globally non-extendable once the running count
-- of committed items exceeds K. From any prefix with running count n > K,
-- no completion can reduce the count back to K because emitted items
-- cannot be retracted. The constraint requirement is therefore active
-- on enumeration tasks: local item-level validity does not certify
-- global compliance with the exact-count constraint.
--
-- Witness: target count K = 3, items committed n = 4 with remaining
-- steps r ≥ 0. The prefix has already exceeded the count constraint;
-- no completion of any length recovers exactness.
--
-- Corresponds to Section 4 / Mitigation Sufficiency Table of:
--   "Language Model Hallucinations: An Impossibility Theorem and Its
--    Architectural Consequences"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- The running item count: number of items committed so far that satisfy
    the local plausibility property P. -/
def runningCount (n : ℕ) : ℕ := n

/-- The target count constraint: exactly K = 3 items must be present in
    the final output. -/
def targetK : ℕ := 3

/-- An item-emission step. The emitted item is `0` (count-preserving, e.g.
    a non-P item or a no-op) or `1` (count-incrementing, e.g. a P-item).
    Encoded as `Fin 2`. -/
def emissionValue (e : Fin 2) : ℕ := e.val

/-- Local plausibility: every individual emission is structurally valid.
    Both options are locally acceptable. The constraint is purely
    compositional: the failure lies in the running count, not in any
    individual step's content. -/
theorem every_emission_locally_valid :
    ∀ e : Fin 2, emissionValue e ≤ 1 := by
  intro e
  unfold emissionValue
  have : e.val < 2 := e.isLt
  omega

/-- From running count 4 (one over the target K = 3), no further emission
    of any kind reaches an exact-K final count. Each emission either
    preserves the count at 4 (failing exactness on the high side) or
    increases it to 5 (failing more strongly). The non-extendability is
    independent of how many further steps remain. -/
theorem count_exceeded_non_extendable :
    ¬ ∃ e : Fin 2, runningCount 4 + emissionValue e = targetK := by
  rintro ⟨e, hcount⟩
  unfold runningCount targetK emissionValue at hcount
  have : e.val < 2 := e.isLt
  omega

/-- Stronger non-extendability: from any running count n > K, no single-
    step completion reaches the exact target K. -/
theorem count_strictly_exceeded_non_extendable
    (n : ℕ) (h_exceeded : n > targetK) :
    ¬ ∃ e : Fin 2, runningCount n + emissionValue e = targetK := by
  rintro ⟨e, hcount⟩
  unfold runningCount targetK emissionValue at *
  have : e.val < 2 := e.isLt
  omega

/-- Multi-step non-extendability: from running count n > K, no completion
    of any length using emissions in {0, 1} can reduce the count back to K.
    Once the count is exceeded, the prefix is non-extendable regardless of
    remaining horizon. -/
theorem count_exceeded_non_extendable_any_length
    (n : ℕ) (h_exceeded : n > targetK)
    (completion : List (Fin 2)) :
    runningCount n + (completion.map emissionValue).sum > targetK := by
  unfold runningCount targetK at *
  have h_sum_nonneg : (completion.map emissionValue).sum ≥ 0 := Nat.zero_le _
  omega

/-- The delayed-failure witness: an enumeration task with exact-count
    target K = 3 admits prefixes (running count > 3) where every individual
    emission is locally valid, yet the prefix is non-extendable to the
    exact target. Local validity does not certify global compliance with
    multi-constraint enumeration tasks. -/
theorem multi_constraint_enumeration_delayed_failure :
    (∀ e : Fin 2, emissionValue e ≤ 1) ∧
    (¬ ∃ e : Fin 2, runningCount 4 + emissionValue e = targetK) := by
  exact ⟨every_emission_locally_valid, count_exceeded_non_extendable⟩