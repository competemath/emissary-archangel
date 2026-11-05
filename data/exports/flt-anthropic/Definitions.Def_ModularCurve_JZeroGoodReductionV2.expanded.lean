import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SpecializationWitness
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_EllipticCurve_FrobeniusTrace


-- @@ L7-7 verbatim
set_option autoImplicit false


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open ModularCurve AlgebraicCurve IsLocalRing


-- @@ L13-13 verbatim
namespace ModularCurve


-- @@ L15-15 verbatim
local notation "Qbar" => AlgebraicClosure ℚ


-- @@ L17-17 verbatim
variable {A : ValuationSubring Qbar} {ℓ : ℕ} {hℓ : ℓ.Prime} {N : ℕ} [NeZero N]


-- @@ L19-20 verbatim
noncomputable local instance instDecEqResidueFieldF3nrp : DecidableEq (ResidueField A) :=
  Classical.decEq _


-- @@ L22-26 verbatim
set_option synthInstance.maxHeartbeats 80000 in

noncomputable local instance instAlgebraResidueFieldModularFunctionFieldCF3nrp :
    Algebra (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
  inferInstance


-- @@ L28-28 verbatim
variable [Module HeckeAlg (JZero N)]


-- @@ L30-30 verbatim
variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]


-- @@ L32-54 verbatim
variable (A) (ℓ) (hℓ) (N) in

structure JZeroGoodReductionSpecialization where

  sp : JZero N →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  F : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
    →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  hsurj : Function.Surjective sp

  hecke_comm : ∀ (T : HeckeAlg) (x : JZero N), sp (T • x) = T • sp x

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero N, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt σ ℓ →
    ∀ x : JZero N, sp (σ • x) = F (sp x)

  injective_torsion : ∀ (p : ℕ), p.Prime → p ≠ ℓ → ∀ (x : JZero N),
    (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0

  sfr : SpecialFibreRelation
    (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ F


-- @@ L56-56 verbatim
namespace JZeroGoodReductionSpecialization


-- @@ L58-61 verbatim
theorem hgen (D : JZeroGoodReductionSpecialization A ℓ hℓ N)
    (q : Nat.Primes) (a : JZero N) (ha : D.sp a = 0) :
    D.sp (heckeGen q • a) = 0 := by
  rw [D.hecke_comm, ha, smul_zero]


-- @@ L63-71 verbatim
theorem toIsSpecialization (D : JZeroGoodReductionSpecialization A ℓ hℓ N)
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
      (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
      A ℓ D.sp D.F where
  hecke_comm := D.hecke_comm
  inertia_comm := D.inertia_comm
  frobenius_comm := D.frobenius_comm
  injective_torsion := fun x hx hker => D.injective_torsion p hp hpℓ x hx hker


-- @@ L73-79 verbatim
theorem toSpecializationExistsBody (D : JZeroGoodReductionSpecialization A ℓ hℓ N)
    {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
        (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) A ℓ D.sp D.F
      ∧ SpecialFibreRelation
          (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ D.F :=
  ⟨D.toIsSpecialization hp hpℓ, D.sfr⟩


-- @@ L81-81 verbatim
end JZeroGoodReductionSpecialization


-- @@ L83-83 verbatim
end ModularCurve


-- @@ L85-85 verbatim
end
