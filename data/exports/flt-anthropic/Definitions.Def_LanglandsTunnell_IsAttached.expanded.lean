import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace


-- @@ L7-7 verbatim
set_option autoImplicit false


-- @@ L9-9 verbatim
namespace LanglandsTunnell


-- @@ L11-11 verbatim
open NumberField AutomorphicForm IsDedekindDomain EisensteinWeightOne FLT.ExplicitLift


-- @@ L13-13 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L15-22 verbatim
def IsAttachedExact (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ T →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (π₀.a ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
          = ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3)).trace


-- @@ L24-32 verbatim
def IsAttachedTwisted (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ T →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (π₀.a ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
          = ((chiNegThree (p : ℕ) : ℤ) : ZMod 3)
            * ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
                Matrix (Fin 2) (Fin 2) (ZMod 3)).trace


-- @@ L34-36 verbatim
def IsAttachedUpToTwist (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  IsAttachedExact ρ π₀ T ∨ IsAttachedTwisted ρ π₀ T


-- @@ L38-42 verbatim
theorem isAttachedUpToTwist_one :
    IsAttachedUpToTwist 1 ⟨⊤, by simp, fun _ => 2, fun _ => 0⟩ ∅ :=
  Or.inl fun _ _ _ _ _ _ => by
    simp [Matrix.trace]
    exact map_ofNat red 2


-- @@ L44-44 verbatim
end LanglandsTunnell
