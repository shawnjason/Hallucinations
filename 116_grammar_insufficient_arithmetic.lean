-- ID 116: Grammar Constraints Insufficient for Arithmetic Validity
--
-- Catalog ID 116 (Hallucinations paper).
-- Companion to ID 115 (Arithmetic CoT Sufficiency Requires Faithful
-- Running Total) — together they characterize the boundary of what
-- syntactic vs semantic mitigations can certify.
--
-- Statement: grammar-based decoding restricts output to valid syntactic
-- productions but does not enforce global arithmetic constraints. An
-- output can be grammar-valid (every token in the allowed vocabulary,
-- expression well-formed) while violating the terminal arithmetic
-- constraint (sum ≠ target, count exceeds bound, etc.). Syntactic
-- admissibility and semantic admissibility are independent properties:
-- grammar covers the former, faithful running-total CoT (ID 115)
-- covers the latter.
--
-- Witness: vocabulary V = {0, 1, +} with grammar producing well-formed
-- expressions of length T. Every grammar-valid expression passes the
-- syntactic check, but only those summing to the target K satisfy
-- the arithmetic constraint. The set of grammar-valid expressions is
-- strictly larger than the set of arithmetic-valid expressions.
--
-- Corresponds to Section 5 / mitigation analysis of:
--   "Language Model Hallucinations: An Impossibility Theorem and Its
--    Architectural Consequences"
--
-- Shawn Kevin Jason

import Mathlib.Tactic

/-- A token in the simplified arithmetic vocabulary V = {0, 1}.
    The grammar is "any sequence of tokens" — every sequence is
    syntactically valid. -/
def TokenValue (t : Fin 2) : ℕ := t.val

/-- Grammar validity: every token is in the allowed vocabulary. For
    the simple grammar where every Fin 2 is allowed, this is trivially
    true for any sequence. -/
def GrammarValid (_seq : List (Fin 2)) : Prop := True

/-- Arithmetic validity: the sum of tokens equals the target K. This
    is the global terminal constraint that grammar checking does not
    address. -/
def ArithmeticValid (seq : List (Fin 2)) (target : ℕ) : Prop :=
  (seq.map TokenValue).sum = target

/-- Every sequence is grammar-valid: the syntactic check is satisfied
    by construction whenever the tokens come from the allowed
    vocabulary. -/
theorem all_sequences_grammar_valid (seq : List (Fin 2)) :
    GrammarValid seq := by
  trivial

/-- Concrete grammar-valid but arithmetic-invalid witness: the sequence
    [1, 1, 1] is well-formed under the grammar (every token in {0, 1})
    but sums to 3, not the target value 2. Grammar validity does not
    imply arithmetic validity. -/
theorem grammar_valid_arithmetic_invalid_witness :
    let seq : List (Fin 2) := [⟨1, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩]
    GrammarValid seq ∧ ¬ ArithmeticValid seq 2 := by
  refine ⟨trivial, ?_⟩
  unfold ArithmeticValid TokenValue
  simp

/-- Grammar validity does not imply arithmetic validity: there exist
    sequences satisfying the grammar but violating the arithmetic
    constraint. The mitigations are therefore orthogonal — grammar
    covers syntax, arithmetic CoT covers semantics, and neither
    subsumes the other. -/
theorem grammar_does_not_imply_arithmetic :
    ∃ seq : List (Fin 2), GrammarValid seq ∧ ¬ ArithmeticValid seq 2 := by
  refine ⟨[⟨1, by omega⟩, ⟨1, by omega⟩, ⟨1, by omega⟩], trivial, ?_⟩
  unfold ArithmeticValid TokenValue
  simp

/-- The arithmetic insufficiency conjunction: every grammar-valid
    sequence passes syntax checking, but at least one grammar-valid
    sequence fails the arithmetic constraint. Grammar constraints are
    therefore strictly weaker than arithmetic constraints — they're
    orthogonal mitigations addressing different failure modes. -/
theorem grammar_insufficient_for_arithmetic_validity :
    (∀ seq : List (Fin 2), GrammarValid seq) ∧
    (∃ seq : List (Fin 2), GrammarValid seq ∧ ¬ ArithmeticValid seq 2) := by
  refine ⟨all_sequences_grammar_valid, ?_⟩
  exact grammar_does_not_imply_arithmetic