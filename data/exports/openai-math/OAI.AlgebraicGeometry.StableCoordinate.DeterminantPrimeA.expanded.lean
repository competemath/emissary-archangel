import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDomains
import Mathlib.RingTheory.MvPolynomial.Basic


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-13 verbatim
/-!
# The first determinant coordinate is prime

This file proves the exact residual presentation obtained by setting `a=0`,
then its domain property. Consequently `a` is a prime element of the determinant
ring. Combined with the explicit `a`-chart, this is the algebraic input to the
prime-element localization criterion for unique factorization.
-/


-- @@ L15-15 verbatim
namespace StableCoordinate.DeterminantPrimeA


-- @@ L17-17 verbatim
open MvPolynomial

-- @@ L18-18 verbatim
open DeterminantRing


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
variable (k : Type*) [CommRing k]


-- @@ L24-25 verbatim
/-- The residual relation after setting `a=0`; variables are `d,b,c,u`. -/
def residualRelation : MvPolynomial (Fin 4) k := X 1 * X 0 + 1


-- @@ L27-27 verbatim
def residualIdeal : Ideal (MvPolynomial (Fin 4) k) := Ideal.span {residualRelation k}

-- @@ L28-28 verbatim
abbrev ResidualRing := MvPolynomial (Fin 4) k ⧸ residualIdeal k


-- @@ L30-31 verbatim
def residualMk : MvPolynomial (Fin 4) k →ₐ[k] ResidualRing k :=
  Ideal.Quotient.mkₐ k (residualIdeal k)


-- @@ L33-33 verbatim
def rX (i : Fin 4) : ResidualRing k := residualMk k (X i)


-- @@ L35-38 verbatim
theorem residual_relation : rX k 1 * rX k 0 + 1 = 0 := by
  have h : residualMk k (residualRelation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa [residualRelation, rX] using h


-- @@ L40-40 verbatim
def aIdeal : Ideal (C k) := Ideal.span {a k}

-- @@ L41-41 verbatim
abbrev ModA := C k ⧸ aIdeal k


-- @@ L43-43 verbatim
def modAMk : C k →ₐ[k] ModA k := Ideal.Quotient.mkₐ k (aIdeal k)


-- @@ L45-46 verbatim
@[simp] theorem modAMk_a : modAMk k (a k) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))


-- @@ L48-51 verbatim
theorem modA_relation : modAMk k (b k) * modAMk k (d k) + 1 = 0 := by
  have h := congrArg (modAMk k) (determinant_relation k)
  simp only [map_sub, map_mul, map_one, modAMk_a] at h
  linear_combination -h


-- @@ L53-56 verbatim
def toResidual : C k →ₐ[k] ResidualRing k :=
  DeterminantRing.lift (k := k) 0 (rX k 0) (rX k 1) (rX k 2) (rX k 3) (by
    have h := residual_relation k
    linear_combination -h)


-- @@ L58-58 verbatim
@[simp] theorem toResidual_a : toResidual k (a k) = 0 := by simp [toResidual]

-- @@ L59-59 verbatim
@[simp] theorem toResidual_d : toResidual k (d k) = rX k 0 := by simp [toResidual]

-- @@ L60-60 verbatim
@[simp] theorem toResidual_b : toResidual k (b k) = rX k 1 := by simp [toResidual]

-- @@ L61-61 verbatim
@[simp] theorem toResidual_c : toResidual k (c k) = rX k 2 := by simp [toResidual]

-- @@ L62-62 verbatim
@[simp] theorem toResidual_u : toResidual k (u k) = rX k 3 := by simp [toResidual]


-- @@ L64-70 verbatim
def modAToResidual : ModA k →ₐ[k] ResidualRing k :=
  Ideal.Quotient.liftₐ (aIdeal k) (toResidual k) (by
    intro p hp
    have h : aIdeal k ≤ RingHom.ker (toResidual k).toRingHom := by
      rw [aIdeal, Ideal.span_singleton_le_iff_mem]
      simp [RingHom.mem_ker]
    exact h hp)


-- @@ L72-73 verbatim
@[simp] theorem modAToResidual_mk (p : C k) :
    modAToResidual k (modAMk k p) = toResidual k p := rfl


-- @@ L75-83 verbatim
def residualToModA : ResidualRing k →ₐ[k] ModA k :=
  Ideal.Quotient.liftₐ (residualIdeal k)
    (aeval ![modAMk k (d k), modAMk k (b k), modAMk k (c k), modAMk k (u k)]) (by
      intro p hp
      have h : residualIdeal k ≤ RingHom.ker
          (aeval ![modAMk k (d k), modAMk k (b k), modAMk k (c k), modAMk k (u k)]).toRingHom := by
        rw [residualIdeal, Ideal.span_singleton_le_iff_mem]
        simp [RingHom.mem_ker, residualRelation, modA_relation]
      exact h hp)


-- @@ L85-89 verbatim
@[simp] theorem residualToModA_rX (i : Fin 4) :
    residualToModA k (rX k i) =
      (![modAMk k (d k), modAMk k (b k), modAMk k (c k), modAMk k (u k)] : Fin 4 → ModA k) i := by
  change (aeval ![modAMk k (d k), modAMk k (b k), modAMk k (c k), modAMk k (u k)]) (X i) = _
  simp


-- @@ L91-97 verbatim
theorem residualToModA_comp_modAToResidual :
    (residualToModA k).comp (modAToResidual k) = AlgHom.id k (ModA k) := by
  apply Ideal.Quotient.algHom_ext
  apply DeterminantRing.hom_ext (k := k) (S := ModA k)
  all_goals
    change residualToModA k (modAToResidual k (modAMk k _)) = modAMk k _
    simp


-- @@ L99-105 verbatim
theorem modAToResidual_comp_residualToModA :
    (modAToResidual k).comp (residualToModA k) = AlgHom.id k (ResidualRing k) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change modAToResidual k (residualToModA k (rX k i)) = rX k i
  fin_cases i <;> simp


-- @@ L107-110 verbatim
/-- Setting `a=0` gives the domain presentation `k[d,b,c,u]/(bd+1)`. -/
def modAEquivResidual : ModA k ≃ₐ[k] ResidualRing k :=
  AlgEquiv.ofAlgHom (modAToResidual k) (residualToModA k)
    (modAToResidual_comp_residualToModA k) (residualToModA_comp_modAToResidual k)


-- @@ L112-112 verbatim
section Domain

-- @@ L113-113 verbatim
variable [IsDomain k] [UniqueFactorizationMonoid k]


-- @@ L115-119 verbatim
omit [UniqueFactorizationMonoid k] in
theorem residualRelation_irreducible : Irreducible (residualRelation k) := by
  simpa [residualRelation, mul_comm] using
    MvPolynomial.irreducible_mul_X_add (X (0 : Fin 4) : MvPolynomial (Fin 4) k)
      1 1 (X_ne_zero 0) (by simp) (by simp) isRelPrime_one_right


-- @@ L121-122 verbatim
instance residualIdeal_isPrime : (residualIdeal k).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (residualRelation_irreducible k).prime


-- @@ L124-124 verbatim
instance residualRing_isDomain : IsDomain (ResidualRing k) := inferInstance


-- @@ L126-127 verbatim
instance modA_isDomain : IsDomain (ModA k) :=
  Function.Injective.isDomain (modAEquivResidual k).toRingHom (modAEquivResidual k).injective


-- @@ L129-129 verbatim
end Domain


-- @@ L131-131 verbatim
end


-- @@ L133-133 verbatim
end StableCoordinate.DeterminantPrimeA


-- @@ L135-135 verbatim
namespace StableCoordinate.DeterminantRing


-- @@ L137-137 verbatim
variable (k : Type*) [CommRing k] [IsDomain k] [UniqueFactorizationMonoid k]


-- @@ L139-144 verbatim
/-- The first coordinate of the determinant hypersurface is a prime element. -/
theorem a_prime : Prime (a k) := by
  have ha : a k ≠ 0 := Obstruction.cX_ne_zero k 0
  apply (Ideal.span_singleton_prime ha).mp
  exact (Ideal.Quotient.isDomain_iff_prime (DeterminantPrimeA.aIdeal k)).mp
    (DeterminantPrimeA.modA_isDomain k)


-- @@ L146-146 verbatim
end StableCoordinate.DeterminantRing


-- @@ L148-148 verbatim
end OAI
