import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SpecializationWitness
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JZeroGoodReductionV2


-- @@ L8-8 verbatim
set_option autoImplicit false


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
open ModularCurve AlgebraicCurve IsLocalRing


-- @@ L14-14 verbatim
namespace ModularCurve


-- @@ L16-16 verbatim
local notation "Qbar" => AlgebraicClosure ℚ


-- @@ L18-18 verbatim
variable {A : ValuationSubring Qbar} {ℓ : ℕ} {hℓ : ℓ.Prime} {N : ℕ} [NeZero N]


-- @@ L20-20 verbatim
attribute [local instance] ModularCurve.instDecEqResidueFieldF3nrp


-- @@ L22-22 verbatim
attribute [local instance] ModularCurve.instAlgebraResidueFieldModularFunctionFieldCF3nrp

-- @@ L23-23 verbatim
variable [Module HeckeAlg (JZero N)]


-- @@ L25-25 verbatim
variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]


-- @@ L27-49 verbatim
variable (A) (ℓ) (hℓ) (N) in

structure JZeroGoodReductionSpecialization_alt where

  sp : JZero N →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  F : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
    →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  hsurj : Function.Surjective sp

  hecke_comm : ∀ (T : HeckeAlg) (x : JZero N), sp (T • x) = T • sp x

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero N, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt σ ℓ →
    ∀ x : JZero N, sp (σ • x) = F (sp x)

  injective_torsion : ∀ (p : ℕ), ¬ ℓ ∣ p → ∀ (x : JZero N),
    (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0

  sfr : SpecialFibreRelation
    (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ F


-- @@ L51-51 verbatim
namespace JZeroGoodReductionSpecialization_alt


-- @@ L53-56 verbatim
theorem hgen (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    (q : Nat.Primes) (a : JZero N) (ha : D.sp a = 0) :
    D.sp (heckeGen q • a) = 0 := by
  rw [D.hecke_comm, ha, smul_zero]


-- @@ L58-66 verbatim
theorem toIsSpecialization (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    {p : ℕ} (hℓp : ¬ ℓ ∣ p) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
      (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
      A ℓ D.sp D.F where
  hecke_comm := D.hecke_comm
  inertia_comm := D.inertia_comm
  frobenius_comm := D.frobenius_comm
  injective_torsion := fun x hx hker => D.injective_torsion p hℓp x hx hker


-- @@ L68-74 verbatim
theorem toSpecializationExistsBody (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    {p : ℕ} (hℓp : ¬ ℓ ∣ p) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
        (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) A ℓ D.sp D.F
      ∧ SpecialFibreRelation
          (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ D.F :=
  ⟨D.toIsSpecialization hℓp, D.sfr⟩


-- @@ L76-76 verbatim
end JZeroGoodReductionSpecialization_alt


-- @@ L78-78 verbatim
end ModularCurve


-- @@ L80-80 verbatim
end
