-- ID 018: Language-Model Hallucination Ceiling
--
-- Catalog ID 18 (Projection Insufficiency paper, Section 9.1).
-- Specialization of Theorem 2 (PIT, ID 4) to autoregressive language models.
--
-- Statement: a language model with bounded context window of depth h is a
-- forward-local system whose next-token selection is a function of the
-- bounded context projection. When the global consistency constraint
-- (factual accuracy, logical closure, task completion) depends on
-- information outside the context window, two prefixes can agree on the
-- context projection while differing in admissibility. No function of the
-- context window alone can determine which next tokens preserve global
-- consistency in all such cases. This is the structural ceiling that
-- bounded-context language models cannot exceed by training improvement
-- alone, formalizing the delayed-constraint subclass of hallucination.
--
-- Corresponds to Section 9.1 of:
--   "Projection Insufficiency and Trajectory Realization: A Unified
--    Constraint-Based Framework for Bounded Systems"
--
-- Shawn Kevin Jason

import Mathlib.Tactic
import Mathlib.Data.Set.Basic

variable {Prefix Window Token : Type*}

/-- A bounded context-window projection mapping full token prefixes to a
    fixed-depth trailing window. The relevant property here is that two
    distinct prefixes can share the same context window. -/
def NonInjectiveContext (_ctx : Prefix → Window) : Prop :=
  ∃ p1 p2 : Prefix, p1 ≠ p2 ∧ _ctx p1 = _ctx p2

/-- Admissibility-preserving next-token sets. `T_adm p` is the set of next
    tokens that, when appended to prefix p, preserve global consistency. -/
def AdmissibleTokens (_T_adm : Prefix → Set Token) : Prop := True

/-- Same-context admissibility conflict: two prefixes share their context
    window but have disjoint admissibility-preserving next-token sets.
    This is the structural condition under which delayed-constraint
    hallucination is unavoidable for any context-window-bounded model. -/
def SameContextHallucinationRisk
    (ctx : Prefix → Window) (T_adm : Prefix → Set Token) : Prop :=
  ∃ p1 p2 : Prefix, ctx p1 = ctx p2 ∧ T_adm p1 ∩ T_adm p2 = ∅

/-- Deterministic decoder form. No deterministic next-token decoder defined
    solely on the context window can guarantee selection of an
    admissibility-preserving token in all prefixes when a same-context
    hallucination risk exists. This is the structural ceiling on
    bounded-context language models for delayed-constraint consistency. -/
theorem lm_hallucination_ceiling_deterministic
    (ctx : Prefix → Window) (T_adm : Prefix → Set Token)
    (h : SameContextHallucinationRisk ctx T_adm) :
    ¬ ∃ decode : Window → Token, ∀ p : Prefix, decode (ctx p) ∈ T_adm p := by
  obtain ⟨p1, p2, hctx, hdisj⟩ := h
  rintro ⟨decode, hdec⟩
  have h1 : decode (ctx p1) ∈ T_adm p1 := hdec p1
  have h2 : decode (ctx p2) ∈ T_adm p2 := hdec p2
  rw [hctx] at h1
  have hboth : decode (ctx p2) ∈ T_adm p1 ∩ T_adm p2 := ⟨h1, h2⟩
  rw [hdisj] at hboth
  exact hboth

/-- Stochastic decoder form. No sampling distribution whose support at a
    given context must be inside the admissibility-preserving token set
    can satisfy this requirement for both prefixes in a same-context
    hallucination risk pair. Temperature, top-k, top-p, and similar
    sampling controls do not escape the obstruction; they only redistribute
    probability mass within the same context-conditioned support. -/
theorem lm_hallucination_ceiling_stochastic
    (ctx : Prefix → Window) (T_adm : Prefix → Set Token)
    (h : SameContextHallucinationRisk ctx T_adm) :
    ¬ ∃ supp : Window → Set Token,
      (∀ w : Window, (supp w).Nonempty) ∧
      (∀ p : Prefix, supp (ctx p) ⊆ T_adm p) := by
  obtain ⟨p1, p2, hctx, hdisj⟩ := h
  rintro ⟨supp, hne, hsub⟩
  obtain ⟨t, ht1⟩ := hne (ctx p1)
  have h1 : t ∈ T_adm p1 := hsub p1 ht1
  have ht2 : t ∈ supp (ctx p2) := by rw [← hctx]; exact ht1
  have h2 : t ∈ T_adm p2 := hsub p2 ht2
  have hboth : t ∈ T_adm p1 ∩ T_adm p2 := ⟨h1, h2⟩
  rw [hdisj] at hboth
  exact hboth