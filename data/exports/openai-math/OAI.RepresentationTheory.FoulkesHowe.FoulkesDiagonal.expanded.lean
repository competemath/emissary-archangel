import OAI.RepresentationTheory.FoulkesHowe.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators

-- @@ L7-7 verbatim
universe u

-- @@ L8-8 verbatim
namespace Problem346


-- @@ L10-10 verbatim
variable (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]

 
-- @@ L12-17 verbatim
theorem foulkesFormula_diagonal (u : Fin b → V) :
    foulkesFormula a b V (fun j _ => u j) =
      symMonomial a (SymPow b V) (fun _ => symMonomial b V u) := by
  classical
  simp [foulkesFormula, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    Nat.factorial_ne_zero]

 
-- @@ L19-24 verbatim
theorem IsFoulkesMap.map_diagonal
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V))
    (hμ : IsFoulkesMap a b V μ) (u : Fin b → V) :
    μ (symMonomial b (SymPow a V) (fun j => symMonomial a V (fun _ => u j))) =
      symMonomial a (SymPow b V) (fun _ => symMonomial b V u) := by
  rw [hμ, foulkesFormula_diagonal]


-- @@ L26-26 verbatim
end Problem346


-- @@ L28-28 verbatim
end


-- @@ L30-30 verbatim
end OAI
