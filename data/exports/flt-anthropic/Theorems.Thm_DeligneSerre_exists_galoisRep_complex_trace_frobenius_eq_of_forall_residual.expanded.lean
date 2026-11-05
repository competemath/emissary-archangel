import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual

-- @@ L5-5 verbatim
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois

-- @@ L6-6 verbatim
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec BrauerNesbitt.actionEndoHom_apply BrauerNesbitt.actionTrace_apply BrauerNesbitt.actionEndo_apply


-- @@ L8-8 verbatim
set_option autoImplicit false


-- @@ L10-10 verbatim
open Polynomial

-- @@ L11-11 verbatim
open scoped MatrixGroups


-- @@ L13-13 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L15-35 expanded
theorem DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual (N : ℕ)
    (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (hζR : ζ ∈ R) (t d : ℕ → ℂ) (ht : ∀ p : ℕ, p.Prime → ¬p ∣ N → t p ∈ R)
    (hd : ∀ p : ℕ, p.Prime → ¬p ∣ N → d p ∈ R)
    (hfam :
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (φ : R →+* ZMod ℓ),
        ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod ℓ),
          GaloisFactorsThroughFiniteLevel ρ ∧
            Nat.card (MonoidHom.range ρ) ∣ m ∧
              ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬p ∣ N),
                p ≠ ℓ →
                  ∀ A : ValuationSubring (AlgebraicClosure ℚ),
                    A.LiesOverPrime p →
                      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
                        ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
                          A.IsFrobeniusAt σ p →
                            ((ρ σ : GL (Fin 2) (ZMod ℓ)) :
                                  Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly =
                              X ^ 2 - C (φ ⟨t p, ht p hp hpN⟩) * X + C (φ ⟨d p, hd p hp hpN⟩)) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) ℂ,
      GaloisFactorsThroughFiniteLevel ρ ∧
        ∀ p : ℕ,
          p.Prime →
            ¬p ∣ N →
              ∀ A : ValuationSubring (AlgebraicClosure ℚ),
                A.LiesOverPrime p →
                  (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
                    ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
                      A.IsFrobeniusAt σ p →
                        ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace = t p ∧
                          ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = d p :=
  by
  p2m_exact_reverting
    @_root_.P2MW.S_DeligneSerre_exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual.solution

