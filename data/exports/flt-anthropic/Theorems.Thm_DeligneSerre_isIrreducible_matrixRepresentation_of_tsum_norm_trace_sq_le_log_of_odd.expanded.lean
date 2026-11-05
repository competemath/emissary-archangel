import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_DeligneSerre_isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd

-- @@ L6-6 verbatim
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G

-- @@ L7-7 verbatim
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec


-- @@ L9-9 verbatim
set_option autoImplicit false


-- @@ L11-11 verbatim
open scoped MatrixGroups


-- @@ L13-13 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L15-30 expanded
theorem DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd (N : ℕ)
    [NeZero N] (ε : DirichletCharacter ℂ N) (hε : ε (-1) = -1) (a : ℕ → ℂ) (C₀ : ℝ)
    (ha :
      ∀ s : ℝ,
        1 < s →
          s < 2 →
            Summable
                (fun p : { p : ℕ // p.Prime ∧ ¬p ∣ N } => ‖a (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s)) ∧
              ∑' p : { p : ℕ // p.Prime ∧ ¬p ∣ N }, ‖a (p : ℕ)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-s) ≤
                Real.log (1 / (s - 1)) + C₀)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (hρa :
      ∀ p : ℕ,
        p.Prime →
          ¬p ∣ N →
            ∀ A : ValuationSubring (AlgebraicClosure ℚ),
              A.LiesOverPrime p →
                (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
                  ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
                    A.IsFrobeniusAt σ p →
                      ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = a p ∧
                        ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = ε (p : ZMod N)) :
    (Deformation.matrixRepresentation ρ).IsIrreducible := by
  p2m_exact_reverting
    @_root_.P2MW.S_DeligneSerre_isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd.solution

