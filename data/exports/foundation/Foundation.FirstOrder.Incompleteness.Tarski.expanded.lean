module

public import Foundation.FirstOrder.Bootstrapping.FixedPoint
public import Foundation.Meta.ClProver


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-7 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L9-9 verbatim
variable {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]


-- @@ L11-17 verbatim
/-- There is no predicate `τ`, s.t. for any sentence `σ`, `σ` is provable in `T` iff `τ/[⌜σ⌝]` is so. -/
lemma not_exists_tarski_predicate : ¬∃ τ : ArithmeticSemisentence 1, ∀ σ, T ⊢ σ 🡘 τ/[⌜σ⌝] := by
  rintro ⟨τ, hτ⟩;
  apply Entailment.Consistent.not_bot (𝓢 := T);
  have h₁ : T ⊢ fixedpoint (∼τ) 🡘 τ/[⌜fixedpoint (∼τ)⌝] := by simpa using hτ $ fixedpoint “x. ¬!τ x”;;
  have h₂ : T ⊢ fixedpoint (∼τ) 🡘 ∼τ/[⌜fixedpoint (∼τ)⌝] := by simpa using diagonal (T := T) “x. ¬!τ x”;
  cl_prover [h₁, h₂];


-- @@ L19-27 verbatim
/-- Tarski's Undefinability of Truth Theorem. -/
theorem undefinability_of_truth : ¬∃ τ : ArithmeticSemisentence 1, ∀ σ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ σ ↔ ℕ↓[ℒₒᵣ] ⊧ τ/[⌜σ⌝] := by
  have := not_exists_tarski_predicate (T := 𝗧𝗔);
  contrapose! this;
  obtain ⟨τ, hτ⟩ := this;
  use τ;
  intro σ;
  apply TA.provable_iff.mpr;
  simpa using hτ σ;


-- @@ L29-29 verbatim
end FFL.FirstOrder.Arithmetic
