# Language Model Hallucinations — Lean Proofs

[![DOI](https://zenodo.org/badge/DOI/20059771.svg)](https://doi.org/20059771)

Machine-checked Lean 4 proofs for:

**"Language Model Hallucinations: An Impossibility Theorem and Its Architectural Consequences"**

Paper DOI (concept, always resolves to latest): [10.5281/zenodo.19715059](https://doi.org/10.5281/zenodo.19715059)

---

## Author

Shawn Kevin Jason — Independent Researcher, Las Vegas, NV
ORCID: [![ORCID iD](https://orcid.org/sites/default/files/images/orcid_16x16.png)](https://orcid.org/0009-0003-9208-1556) [0009-0003-9208-1556](https://orcid.org/0009-0003-9208-1556)

---

## What This Repository Contains

Seven standalone Lean 4 proof files covering the principal formal results of the paper. The proofs split into four groups: a **headline impossibility** group containing the structural ceiling result (Theorem 1) in both deterministic and stochastic forms; a **certification-depth lower bounds** group establishing that the depth at which extendability becomes recoverable from a bounded local window scales with sequence length under terminal-sum and multi-constraint enumeration tasks; a **mitigation boundaries** group characterizing what chain-of-thought prompting, grammar-constrained decoding, and verifier-rerank schemes can and cannot certify; and a **unified hallucination taxonomy** group establishing that the standard intrinsic / extrinsic distinction maps onto the delayed-constraint-failure structure as two sub-cases.

Each file is independent and verifies against the current Mathlib release.

---

## Files

### Headline Impossibility

**`018_lm_hallucination_ceiling.lean`** — Theorem 1 (Impossibility of Guaranteed Consistency)
The headline structural impossibility, in both deterministic and stochastic forms. A language model with bounded context window of depth `h` is a forward-local system whose next-token selection is a function of the bounded context projection. When the global consistency constraint depends on information outside the context window, two prefixes can agree on the context projection while differing in admissibility — and no function of the context window alone determines which next tokens preserve global consistency in all such cases. The `SameContextHallucinationRisk` predicate is the LM specialization of the same-fiber conflict pattern; both decoder forms (deterministic next-token map and stochastic next-token distribution) are proved.

### Certification-Depth Lower Bounds

**`099_multi_constraint_enumeration_delayed_failure.lean`** — Multi-Constraint Enumeration Delayed-Failure
Concrete witness for delayed-constraint failure under exact-count enumeration: a generation task imposing an exact-count constraint can be locally satisfied at every individual step (each emitted item passes the plausibility check) while becoming globally non-extendable once the running count exceeds the target. The witness uses target `K = 3` with running count `n = 4`; emitted items cannot be retracted, so no completion can reduce the count back to `K`. Local item-level validity does not certify global compliance.

**`114_terminal_sum_certification_depth.lean`** — Terminal-Sum Certification Depth Equals Sequence Length
Quantitative certification-depth lower bound for the arithmetic chain. Under the terminal-sum constraint `Σuₜ = K` with action set `U ⊇ {0, 1, 2}`, the certification depth — the minimum trailing-window depth `h` at which extendability is recoverable from the projection `Πh` — equals the trajectory length `T`. For any `h < T`, the file constructs an explicit pair of prefixes `τ1`, `τ2` with identical `h`-step trailing windows that differ in extendability, because the suppressed pre-window history can have accumulated different running sums while the trailing window remains identical. No bounded local certification with depth less than `T` suffices.

### Mitigation Boundaries

**`115_arithmetic_cot_sufficiency_faithful_total.lean`** — Arithmetic CoT Sufficiency Requires Faithful Running Total
Companion to ID 114 establishing the boundary at which chain-of-thought prompting can recover certification depth. The file proves both halves: with a faithful running total in the CoT scratchpad, extendability under the terminal-sum constraint becomes a function of just `(running_total, remaining_steps)` — a bounded local quantity, so certification depth collapses from `T` to a constant; without faithfulness, an unfaithful CoT scratchpad gives false-positive certificates and provides no improvement over no scratchpad at all.

**`116_grammar_insufficient_arithmetic.lean`** — Grammar Constraints Insufficient for Arithmetic Validity
Companion to ID 115 characterizing what syntactic mitigations cannot certify. Grammar-based decoding restricts output to valid syntactic productions but does not enforce global arithmetic constraints. Concrete witness `[1, 1, 1]` is grammar-valid but sums to `3 ≠ 2`. Syntactic admissibility and semantic admissibility are independent properties: grammar covers the former, faithful running-total CoT (ID 115) covers the latter, and neither covers the other.

**`117_rerank_residual_positive.lean`** — Verifier-Rerank Cannot Attain Zero Structural Failure
Quantitative consequence of Theorem 1 under best-of-`K` reranking. A verifier-rerank scheme that draws `K` candidate completions from a base model and selects the highest-scoring candidate cannot attain zero structural failure rate at any finite `K`. If the per-candidate failure probability is bounded below by `p > 0` (which the structural impossibility theorems establish for forward-local stochastic generation under non-local constraints), then the all-fail probability `p^K` decays geometrically in `K` but is strictly positive for every finite `K`. The file establishes three quantitative bounds, including the strictly-between bound `0 < p^K ≤ p`.

### Unified Hallucination Taxonomy

**`119_intrinsic_extrinsic_dcf_taxonomy.lean`** — Intrinsic and Extrinsic Hallucinations as DCF Taxonomy
Synthesis result connecting the standard hallucination taxonomy to the delayed-constraint-failure (DCF) abstract structure. Both intrinsic hallucinations (output contradicts content verifiable in the input/context) and extrinsic hallucinations (output makes claims not verifiable from the input/context) are formalized as instances of admissibility failure relative to a global consistency constraint; they differ only in whether the relevant consistency information is inside or outside the model's context window. The file proves that intrinsic and extrinsic hallucinations are both DCF instances and that the standard taxonomy is unified under the DCF schema.

---

## Mapping to the Paper

| Paper Result | File | Lean Theorem |
|---|---|---|
| Theorem 1 (Impossibility of Guaranteed Consistency) | `018_lm_hallucination_ceiling.lean` | `lm_hallucination_ceiling_deterministic`, `lm_hallucination_ceiling_stochastic` |
| Multi-Constraint Enumeration Delayed-Failure | `099_multi_constraint_enumeration_delayed_failure.lean` | `multi_constraint_enumeration_delayed_failure` |
| Terminal-Sum Certification Depth Equals Sequence Length | `114_terminal_sum_certification_depth.lean` | `certification_depth_exceeds_h_for_h_eq_1` |
| Arithmetic CoT Sufficiency Requires Faithful Running Total | `115_arithmetic_cot_sufficiency_faithful_total.lean` | `cot_certificate_implies_extendable`, `unfaithful_cot_gives_false_positive`, `arithmetic_cot_sufficiency_requires_faithfulness` |
| Grammar Constraints Insufficient for Arithmetic Validity | `116_grammar_insufficient_arithmetic.lean` | `grammar_insufficient_for_arithmetic_validity`, `grammar_valid_arithmetic_invalid_witness` |
| Verifier-Rerank Cannot Attain Zero Structural Failure | `117_rerank_residual_positive.lean` | `rerank_residual_positive`, `rerank_residual_nonzero`, `rerank_residual_strictly_between` |
| Intrinsic and Extrinsic Hallucinations as DCF Taxonomy | `119_intrinsic_extrinsic_dcf_taxonomy.lean` | `intrinsic_is_dcf`, `extrinsic_is_dcf`, `hallucination_taxonomy_unified_under_dcf` |

---

## How to Verify

1. Open [live.lean-lang.org](https://live.lean-lang.org)
2. Confirm the dropdown in the upper right is set to **Latest Mathlib**
3. Paste the contents of any `.lean` file into the editor
4. Wait for checking to complete — "No goals" on each theorem and no errors in the Problems pane confirms verification

Each file is independent; no cross-file imports are required.

---

## Scope

These proofs verify the formal logical structure of the headline impossibility result (Theorem 1), the certification-depth lower bounds for terminal-sum and multi-constraint enumeration tasks, the mitigation-boundary results characterizing what chain-of-thought prompting, grammar-constrained decoding, and verifier-rerank schemes can and cannot certify, and the unification of the standard intrinsic / extrinsic hallucination taxonomy under the delayed-constraint-failure framework. They do not establish:

- The architectural-consequence discussion and deployment-level recommendations developed narratively in the associated paper
- The empirical instantiations and calibrations reported in the paper alongside the formal results
- The framework-level conjectures and open claims listed alongside the formalized theorems

---

## Related Work

The foundational projection-theoretic result of which Theorem 1 is the language-model specialization is developed in:

*Projection Insufficiency and Trajectory Realization: A Unified Constraint-Based Framework for Bounded Systems* — [DOI: 10.5281/zenodo.19633241](https://doi.org/10.5281/zenodo.19633241) (Lean proofs: [10.5281/zenodo.19687629](https://doi.org/10.5281/zenodo.19687629))

The forward-case impossibility result establishing the divergence kernel and arithmetic-witness machinery underlying the certification-depth bounds is developed in:

*The Non-Locality of Extendability: An Impossibility Theorem for Bounded Information Systems, with Applications to Generative Sequential Systems* — [DOI: 10.5281/zenodo.19688367](https://doi.org/10.5281/zenodo.19688367) (Lean proofs: [10.5281/zenodo.19687799](https://doi.org/10.5281/zenodo.19687799))

The stochastic extension establishing quantitative inconsistency-accumulation lower bounds in the broader admissibility-dynamics framework is developed in:

*Inconsistency Accumulation in Forward-Local Sequential Policies: A Lower Bound under Delayed Constraints* — [DOI: 10.5281/zenodo.19688628](https://doi.org/10.5281/zenodo.19688628) (Lean proofs: [10.5281/zenodo.19687094](https://doi.org/10.5281/zenodo.19687094))

---

## License

MIT
