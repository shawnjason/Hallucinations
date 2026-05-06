-- ID 119: Intrinsic and Extrinsic Hallucinations as DCF Taxonomy
--
-- Catalog ID 119 (Hallucinations paper).
-- Synthesis result connecting the standard hallucination taxonomy to the
-- delayed-constraint-failure (DCF) abstract structure of Definition 13
-- in NEO and Section 4 of the Hallucinations paper.
--
-- Statement: the standard taxonomy distinguishing intrinsic hallucinations
-- (output contradicts content verifiable in the input/context) from
-- extrinsic hallucinations (output makes claims not verifiable from the
-- input/context) maps onto the framework's delayed-constraint-failure
-- structure as two sub-cases. Both are instances of admissibility failure
-- relative to a global consistency constraint; they differ only in
-- whether the relevant consistency information is inside or outside the
-- model's context window.
--
-- Intrinsic hallucination: the consistency constraint is in-context but
-- the output violates it. The constraint is in principle locally
-- certifiable (the relevant information is available) but the model
-- failed to enforce it. This is the certification-failure sub-case.
--
-- Extrinsic hallucination: the consistency constraint is out-of-context
-- and the output makes a non-verifiable claim. The constraint is not
-- locally certifiable (the relevant information is suppressed). This is
-- the projection-insufficiency sub-case proper.
--
-- Both reduce to the abstract failure schema: a step's commitment
-- violates the global consistency predicate, and the failure mode of
-- forward-local generation is unable to prevent both cases.
--
-- Corresponds to Section 4 / hallucination taxonomy of:
--   "Language Model Hallucinations: An Impossibility Theorem and Its
--    Architectural Consequences"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

variable {Output Context : Type*}

/-- Intrinsic hallucination: the output violates a consistency constraint
    that is in-context (verifiable from the available information). This
    is the certification-failure sub-case — the constraint is locally
    decidable but the model failed to enforce it. -/
def IntrinsicHallucination
    (in_context_admissible : Context → Output → Prop)
    (ctx : Context) (out : Output) : Prop :=
  ¬ in_context_admissible ctx out

/-- Extrinsic hallucination: the output makes a claim whose consistency
    requires out-of-context information. This is the projection-
    insufficiency sub-case proper — the constraint depends on
    information outside the available context. -/
def ExtrinsicHallucination
    (out_of_context_admissible : Output → Prop)
    (out : Output) : Prop :=
  ¬ out_of_context_admissible out

/-- Delayed constraint failure (DCF): the abstract failure schema
    encompassing both sub-cases. A commitment violates a global
    admissibility predicate, regardless of whether the predicate is
    in-context certifiable. -/
def DelayedConstraintFailure
    (admissible : Output → Prop) (out : Output) : Prop :=
  ¬ admissible out

/-- Intrinsic hallucinations are DCF instances: when an output violates
    its in-context admissibility predicate, lifting that predicate to
    an output-only function (by partial application of the context)
    yields a DCF instance. -/
theorem intrinsic_is_dcf
    (in_context_admissible : Context → Output → Prop)
    (ctx : Context) (out : Output)
    (h : IntrinsicHallucination in_context_admissible ctx out) :
    DelayedConstraintFailure (in_context_admissible ctx) out := by
  exact h

/-- Extrinsic hallucinations are DCF instances: by definition, an
    extrinsic hallucination is a violation of an out-of-context
    admissibility predicate, which is itself a DCF instance with
    that predicate as the admissibility check. -/
theorem extrinsic_is_dcf
    (out_of_context_admissible : Output → Prop)
    (out : Output)
    (h : ExtrinsicHallucination out_of_context_admissible out) :
    DelayedConstraintFailure out_of_context_admissible out := by
  exact h

/-- Unified DCF taxonomy: both intrinsic and extrinsic hallucinations
    instantiate the same abstract DCF schema. The taxonomy distinction
    is about whether the consistency constraint is in-context or
    out-of-context, not about a fundamentally different failure mode.
    Both share the same architectural cause (forward-local generation
    cannot guarantee admissibility under non-locally certifiable
    constraints) and require the same architectural remedy (constraint
    enforcement at trajectory level rather than local evaluation). -/
theorem hallucination_taxonomy_unified_under_dcf :
    (∀ (in_context_admissible : Context → Output → Prop)
        (ctx : Context) (out : Output),
        IntrinsicHallucination in_context_admissible ctx out →
        DelayedConstraintFailure (in_context_admissible ctx) out) ∧
    (∀ (out_of_context_admissible : Output → Prop) (out : Output),
        ExtrinsicHallucination out_of_context_admissible out →
        DelayedConstraintFailure out_of_context_admissible out) := by
  refine ⟨?_, ?_⟩
  · intros ic ctx out h
    exact intrinsic_is_dcf ic ctx out h
  · intros oc out h
    exact extrinsic_is_dcf oc out h