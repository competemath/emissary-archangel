import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range

-- @@ L6-6 verbatim
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois

-- @@ L7-7 verbatim
attribute [-simp] ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec


-- @@ L9-9 verbatim
set_option autoImplicit false


-- @@ L11-11 verbatim
open Polynomial


-- @@ L13-13 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L15-27 expanded
theorem GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range
    (κ : Type) [Field κ] [Finite κ] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ι : κ →+* Ω)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) Ω)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (S : Finset ℕ)
    (hfrob :
      ∀ p : ℕ,
        p.Prime →
          p ∉ S →
            ∀ A : ValuationSubring (AlgebraicClosure ℚ),
              A.LiesOverPrime p →
                ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
                  A.IsFrobeniusAt σ p →
                    Matrix.trace ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range ∧
                      Matrix.det ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range) :
    ∃ ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ,
      GaloisFactorsThroughFiniteLevel ρ₀ ∧
        (Deformation.matrixRepresentation ρ₀).IsSemisimpleRepresentation ∧
          (∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρ σ = 1 → ρ₀ σ = 1) ∧
            ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
              (((ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
                ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω).charpoly :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range.solution

