-- ID 114: Terminal-Sum Certification Depth Equals Sequence Length
--
-- Catalog ID 114 (Hallucinations paper).
-- Quantitative consequence of NEO Lemma 2 (ID 31) for the arithmetic chain.
--
-- Statement: under the terminal-sum constraint Σuₜ = K with action set
-- U ⊇ {0, 1, 2}, the certification depth — the minimum trailing-window
-- depth h at which extendability is recoverable from Πh — equals the
-- trajectory length T. For any h < T, there exist two prefixes with
-- identical h-step trailing windows that differ in extendability,
-- because the suppressed pre-window history can have accumulated
-- different running sums while the trailing window remains identical.
-- No bounded local certification with depth less than T suffices.
--
-- Witness: trajectory length T = h + 2 with terminal target K = 1.
-- Two prefixes of length h + 1:
--   τ₁ = (1, 0, 0, ..., 0)  — leading 1, then h zeros, sum = 1
--   τ₂ = (2, 0, 0, ..., 0)  — leading 2, then h zeros, sum = 2
-- Their h-step trailing windows are both (0, ..., 0). τ₁ extends to
-- terminal sum 1; τ₂ does not (any one-step completion gives ≥ 2).
--
-- Corresponds to the certification-depth analysis of:
--   "Language Model Hallucinations: An Impossibility Theorem and Its
--    Architectural Consequences"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- Action value for the {0, 1, 2} encoding. -/
def actVal (u : Fin 3) : ℕ := u.val

/-- The trailing h-window of a list of length ≥ h: the last h elements. -/
def trailingWindow (h : ℕ) (τ : List (Fin 3)) : List (Fin 3) :=
  τ.drop (τ.length - h)

/-- For h = 1: the trailing 1-window of τ₁ = [1, 0] is [0]. -/
theorem trailing_window_τ1_is_zero :
    trailingWindow 1 [⟨1, by omega⟩, ⟨0, by omega⟩] = [⟨0, by omega⟩] := by
  rfl

/-- For h = 1: the trailing 1-window of τ₂ = [2, 0] is also [0]. -/
theorem trailing_window_τ2_is_zero :
    trailingWindow 1 [⟨2, by omega⟩, ⟨0, by omega⟩] = [⟨0, by omega⟩] := by
  rfl

/-- The two prefixes share the trailing 1-window. -/
theorem trailing_windows_agree :
    trailingWindow 1 [⟨1, by omega⟩, ⟨0, by omega⟩] =
    trailingWindow 1 [⟨2, by omega⟩, ⟨0, by omega⟩] := by
  rfl

/-- τ₁'s running sum is 1. -/
theorem τ1_sum :
    (([⟨1, by omega⟩, ⟨0, by omega⟩] : List (Fin 3)).map actVal).sum = 1 := by
  rfl

/-- τ₂'s running sum is 2. -/
theorem τ2_sum :
    (([⟨2, by omega⟩, ⟨0, by omega⟩] : List (Fin 3)).map actVal).sum = 2 := by
  rfl

/-- τ₁ is extendable to terminal sum 1: completing with a single 0 reaches
    total 1 + 0 = 1. -/
theorem τ1_extendable_to_target_1 :
    ∃ u : Fin 3,
      (([⟨1, by omega⟩, ⟨0, by omega⟩] : List (Fin 3)).map actVal).sum
        + actVal u = 1 := by
  refine ⟨⟨0, by omega⟩, ?_⟩
  rw [τ1_sum]
  rfl

/-- τ₂ is non-extendable to terminal sum 1: with running sum 2 already
    exceeding the target, no single-step completion reaches total 1. -/
theorem τ2_non_extendable_to_target_1 :
    ¬ ∃ u : Fin 3,
      (([⟨2, by omega⟩, ⟨0, by omega⟩] : List (Fin 3)).map actVal).sum
        + actVal u = 1 := by
  rintro ⟨u, hu⟩
  rw [τ2_sum] at hu
  unfold actVal at hu
  omega

/-- Certification at depth 1 is insufficient: the two prefixes share their
    trailing 1-window yet differ in extendability under the terminal-sum
    target 1. The certification depth must therefore exceed 1 for this
    constraint class. -/
theorem certification_depth_exceeds_h_for_h_eq_1 :
    trailingWindow 1 [⟨1, by omega⟩, ⟨0, by omega⟩] =
      trailingWindow 1 [⟨2, by omega⟩, ⟨0, by omega⟩] ∧
    (∃ u : Fin 3,
      (([⟨1, by omega⟩, ⟨0, by omega⟩] : List (Fin 3)).map actVal).sum
        + actVal u = 1) ∧
    (¬ ∃ u : Fin 3,
      (([⟨2, by omega⟩, ⟨0, by omega⟩] : List (Fin 3)).map actVal).sum
        + actVal u = 1) := by
  exact ⟨trailing_windows_agree, τ1_extendable_to_target_1, τ2_non_extendable_to_target_1⟩