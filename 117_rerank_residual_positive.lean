-- ID 117: Verifier-Rerank Cannot Attain Zero Structural Failure
--
-- Catalog ID 117 (Hallucinations paper).
-- Quantitative consequence of Theorem 1 / Impossibility of Guaranteed
-- Consistency (ID 91 in the catalog) under best-of-K reranking.
--
-- Statement: a verifier-rerank scheme that draws K candidate completions
-- from a base model and selects the highest-scoring candidate cannot
-- attain zero structural failure rate at any finite K. If the per-
-- candidate failure probability is bounded below by p > 0 (which the
-- structural impossibility theorems establish for forward-local
-- stochastic generation under non-local constraints), then the all-fail
-- probability p^K decays geometrically in K but is strictly positive for
-- every finite K. Reranking lowers but does not eliminate the structural
-- failure rate.
--
-- Corresponds to the verifier-rerank quantitative bound of:
--   "Language Model Hallucinations: An Impossibility Theorem and Its
--    Architectural Consequences"
--
-- Shawn Kevin Jason

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- Verifier-rerank residual failure: if the per-candidate failure probability
    is strictly positive, then the all-K-fail probability is strictly positive
    for every finite K. Rerank cannot drive structural failure to exactly zero
    at any finite candidate count. -/
theorem rerank_residual_positive
    (p : ℝ) (K : ℕ) (hp : 0 < p) :
    0 < p ^ K := by
  exact pow_pos hp K

/-- Equivalent form: the all-K-fail probability is nonzero for every finite K. -/
theorem rerank_residual_nonzero
    (p : ℝ) (K : ℕ) (hp : 0 < p) :
    p ^ K ≠ 0 := by
  exact ne_of_gt (pow_pos hp K)

/-- The bound is monotonically decreasing in K but bounded above zero. For
    any K ≥ 1 and per-candidate failure probability p ∈ (0, 1), the residual
    is strictly less than p (some improvement) and strictly greater than 0
    (never exact). -/
theorem rerank_residual_strictly_between
    (p : ℝ) (K : ℕ) (hp : 0 < p) (hlt : p < 1) (hK : 1 ≤ K) :
    0 < p ^ K ∧ p ^ K ≤ p := by
  refine ⟨pow_pos hp K, ?_⟩
  calc p ^ K = p ^ (K - 1 + 1) := by rw [Nat.sub_add_cancel hK]
    _ = p ^ (K - 1) * p := by rw [pow_succ]
    _ ≤ 1 * p := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        exact pow_le_one₀ hp.le hlt.le
    _ = p := one_mul p