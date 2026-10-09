import OAI.RepresentationTheory.FoulkesHowe.Model
import OAI.RepresentationTheory.FoulkesHowe.AlgebraEvaluation


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
universe u

-- @@ L8-8 verbatim
namespace Problem346


-- @@ L10-10 verbatim
variable (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


-- @@ L12-25 verbatim
/-- A symmetric-power duality map is injective as soon as evaluation on pure powers agrees
with evaluation in the symmetric algebra. -/
theorem symPowDual_injective_of_pure_evaluation (n : ℕ)
    (B : SymPow n (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (SymPow n V))
    (hB : ∀ (p : SymPow n (Module.Dual ℂ V)) (x : V),
      B p (symMonomial n V (fun _ => x)) =
        SymmetricAlgebra.lift (Module.Dual.eval ℂ V x) p.val) :
    Function.Injective B := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply symAlg_dual_eq_zero_of_eval_eq_zero V
  intro x
  rw [map_sub, ← hB p x, ← hB q x, hpq, sub_self]


-- @@ L27-27 verbatim
end Problem346


-- @@ L29-29 verbatim
end


-- @@ L31-31 verbatim
end OAI
