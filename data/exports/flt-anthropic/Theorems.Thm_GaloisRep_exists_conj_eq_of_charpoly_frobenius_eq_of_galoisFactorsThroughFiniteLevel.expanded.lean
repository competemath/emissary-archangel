import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel

-- @@ L5-5 verbatim
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois

-- @@ L6-6 verbatim
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec BrauerNesbitt.actionEndoHom_apply BrauerNesbitt.actionTrace_apply BrauerNesbitt.actionEndo_apply


-- @@ L8-8 verbatim
set_option autoImplicit false


-- @@ L10-10 verbatim
open scoped MatrixGroups


-- @@ L12-12 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L14-23 expanded
theorem GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
    (ρ ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ)
    (h :
      ∀ p : ℕ,
        p.Prime →
          p ∉ S →
            ∀ A : ValuationSubring (AlgebraicClosure ℚ),
              A.LiesOverPrime p →
                ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
                  A.IsFrobeniusAt σ p →
                    ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
                      ((ρ' σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρ' σ = P * ρ σ * P⁻¹ :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.solution

