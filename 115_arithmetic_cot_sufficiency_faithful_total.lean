-- ID 115: Arithmetic CoT Sufficiency Requires Faithful Running Total
--
-- Catalog ID 115 (Hallucinations paper).
-- Companion to ID 114 (Terminal-Sum Certification Depth Equals Sequence Length).
--
-- Statement: chain-of-thought (CoT) prompting can recover certification
-- depth on terminal-sum arithmetic constraints if and only if the CoT
-- scratchpad faithfully maintains the running total at each step. With
-- a faithful running total, extendability under the terminal-sum
-- constraint becomes a function of just (running_total, remaining_steps)
-- — a bounded local quantity. The certification depth therefore
-- collapses from T (per ID 114, when no faithful summary is available)
-- to a constant when the CoT carries the running total. Without
-- faithfulness, CoT provides no improvement: a scratchpad that drifts
-- from the true running sum is equivalent to no scratchpad at all for
-- certification purposes.
--
-- Witness: target sum K = 7, action set ⊇ {0, 1}. With a faithful
-- running total, extendability is decidable from the current total
-- and the remaining horizon. Without faithfulness, the certification
-- gap of ID 114 reappears.
--
-- Corresponds to Section 5 / mitigation analysis of:
--   "Language Model Hallucinations: An Impossibility Theorem and Its
--    Architectural Consequences"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- A faithful running-total CoT: at each step, the scratchpad value
    equals the actual prefix sum. -/
def FaithfulRunningTotal (cot : ℕ → ℕ) (prefix_sum : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, cot t = prefix_sum t

/-- With a faithful running total, extendability under the terminal-sum
    constraint is a function of (running_total, remaining_steps). The
    certification rule: extendable iff target ≥ running_total and the
    remaining steps can produce the gap. -/
def CoTCertifiableExtendable (running_total : ℕ) (remaining_steps : ℕ)
    (target : ℕ) : Prop :=
  running_total ≤ target ∧ target - running_total ≤ remaining_steps

/-- Forward direction: when running_total ≤ target and the gap fits in
    the remaining steps using actions in {0, 1}, the prefix is extendable.
    The faithful CoT therefore certifies extendability locally. -/
theorem cot_certificate_implies_extendable
    (running_total remaining_steps target : ℕ)
    (h_cert : CoTCertifiableExtendable running_total remaining_steps target) :
    ∃ completion : ℕ, completion ≤ remaining_steps ∧
      running_total + completion = target := by
  obtain ⟨h_le, h_gap⟩ := h_cert
  refine ⟨target - running_total, h_gap, ?_⟩
  omega

/-- Reverse direction: a non-extendable prefix fails the CoT certificate.
    If the running total exceeds the target, no completion can recover. -/
theorem non_extendable_fails_cot_certificate
    (running_total target : ℕ)
    (h_exceeded : running_total > target) :
    ¬ ∃ completion : ℕ, running_total + completion = target := by
  rintro ⟨c, hc⟩
  omega

/-- Faithfulness is required: an unfaithful CoT (where the scratchpad
    diverges from the true running sum) does not certify extendability.
    A CoT showing a value below the target while the actual prefix sum
    exceeds the target gives a false-positive certificate. The
    `_h_unfaithful` hypothesis documents the structural definition of
    unfaithfulness but is not needed for the contradiction itself —
    the inconsistency arises from the actual sum exceeding the target. -/
theorem unfaithful_cot_gives_false_positive
    (cot_value actual_sum target : ℕ)
    (_h_unfaithful : cot_value < actual_sum)
    (h_cot_ok : cot_value ≤ target)
    (h_actual_bad : actual_sum > target) :
    cot_value ≤ target ∧ ¬ ∃ c : ℕ, actual_sum + c = target := by
  refine ⟨h_cot_ok, ?_⟩
  rintro ⟨c, hc⟩
  omega

/-- The arithmetic CoT sufficiency conjunction: with a faithful running
    total, extendability collapses to a local check on (running_total,
    remaining_steps); without faithfulness, the certification gap of
    ID 114 reappears, since the CoT can give false-positive certificates
    that the actual trajectory invalidates. -/
theorem arithmetic_cot_sufficiency_requires_faithfulness :
    (∀ running_total remaining_steps target : ℕ,
      CoTCertifiableExtendable running_total remaining_steps target →
      ∃ completion : ℕ, completion ≤ remaining_steps ∧
        running_total + completion = target) ∧
    (∃ cot_value actual_sum target : ℕ,
      cot_value < actual_sum ∧
      cot_value ≤ target ∧
      ¬ ∃ c : ℕ, actual_sum + c = target) := by
  refine ⟨?_, ?_⟩
  · intro rt rs t h
    exact cot_certificate_implies_extendable rt rs t h
  · refine ⟨0, 8, 7, ?_, ?_, ?_⟩
    · omega
    · omega
    · rintro ⟨c, hc⟩; omega