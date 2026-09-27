/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Divisor
public import Mathlib.NumberTheory.FunctionField

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Valuation.AlgebraInstances
public import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.ArchimedeanDensely


-- @@ L17-32 verbatim
/-!
# Coordinate places of a function field

This file gives the coordinate presentation of the places of a finite separable extension of
`k(X)`. Finite places are the height-one primes of the integral closure of `k[X]`; infinite
places are the height-one primes of the integral closure of the valuation subring at infinity.

## Main definitions

* `FunctionField.inftyValuationSubring`: the valuation subring at infinity of `k(X)`.
* `FunctionField.infiniteIntegers`: its integral closure in a function field `K`.
* `FunctionField.PlaceA`: the sum of the finite and infinite height-one spectra.
* `FunctionField.placeValuation`: the valuation of a coordinate place.
* `FunctionField.DivisorA`: divisors in the coordinate presentation.
* `FunctionField.principalDivisorA`: the principal divisor on both coordinate charts.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open scoped nonZeroDivisors Polynomial RatFunc WithZero


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
namespace FractionalIdeal


-- @@ L42-43 verbatim
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]


-- @@ L45-71 verbatim
/-- The multiplicative adic valuation of a nonzero element is the exponential of the negative
coefficient of its principal fractional ideal. -/
theorem valuation_eq_exp_neg_count (v : IsDedekindDomain.HeightOneSpectrum R) (x : Kˣ) :
    v.valuation K (x : K) =
      WithZero.exp (-count K v (spanSingleton R⁰ (x : K))) := by
  let n : R := Classical.choose (IsLocalization.exists_mk'_eq R⁰ (x : K))
  let d : R⁰ := Classical.choose
    (Classical.choose_spec (IsLocalization.exists_mk'_eq R⁰ (x : K)))
  have hx : IsLocalization.mk' K n d = (x : K) :=
    Classical.choose_spec
      (Classical.choose_spec (IsLocalization.exists_mk'_eq R⁰ (x : K)))
  have hn : n ≠ 0 := by
    intro hn
    rw [hn, IsLocalization.mk'_zero] at hx
    exact x.ne_zero hx.symm
  have hI : spanSingleton R⁰ (x : K) =
      spanSingleton R⁰ (algebraMap R K (d : R))⁻¹ *
        (Ideal.span {n} : Ideal R) := by
    rw [← hx, IsFractionRing.mk'_eq_div, div_eq_mul_inv,
      coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, mul_comm]
  conv_lhs =>
    rw [← hx, v.valuation_of_mk', v.intValuation_if_neg hn,
      v.intValuation_if_neg (nonZeroDivisors.ne_zero d.property)]
  rw [count_well_defined K v (spanSingleton_ne_zero_iff.mpr x.ne_zero) hI,
    ← WithZero.exp_sub]
  congr 1
  ring


-- @@ L73-73 verbatim
end FractionalIdeal


-- @@ L75-75 verbatim
namespace RatFunc


-- @@ L77-77 verbatim
variable {k : Type*} [Field k]


-- @@ L79-129 verbatim
/-- A rational function regular at infinity has a unique constant residue: after subtracting
the ratio of the leading coefficients of its numerator and denominator, its degree at infinity
is strictly negative (unless the difference is zero). -/
theorem exists_sub_C_intDegree_neg (z : k⟮X⟯) (hzdeg : z.intDegree ≤ 0) :
    ∃ c : k, z - C c = 0 ∨ (z - C c).intDegree < 0 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  by_cases hneg : z.intDegree < 0
  · exact ⟨0, Or.inr (by simpa using hneg)⟩
  have hzdeg0 : z.intDegree = 0 := by omega
  let c : k := z.num.leadingCoeff / z.denom.leadingCoeff
  let p : k[X] := z.num - Polynomial.C c * z.denom
  have hrepr : z - C c =
      algebraMap k[X] k⟮X⟯ p / algebraMap k[X] k⟮X⟯ z.denom := by
    conv_lhs => lhs; rw [← z.num_div_denom]
    rw [← RatFunc.algebraMap_C]
    simp only [p, map_sub, map_mul]
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero z.denom_ne_zero)).2
    rw [sub_mul, div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero z.denom_ne_zero)]
  by_cases hp : p = 0
  · exact ⟨c, Or.inl (by rw [hrepr, hp, map_zero, zero_div])⟩
  refine ⟨c, Or.inr ?_⟩
  have hnumdeg : z.num.natDegree = z.denom.natDegree := by
    simp only [RatFunc.intDegree] at hzdeg0
    omega
  have hnum0 : z.num ≠ 0 := RatFunc.num_ne_zero hz
  have hden0 : z.denom ≠ 0 := z.denom_ne_zero
  have hlcnum : z.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hnum0
  have hlcden : z.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hden0
  have hc : c ≠ 0 := div_ne_zero hlcnum hlcden
  have hCmul0 : Polynomial.C c * z.denom ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hden0
  have hdegree : z.num.degree = (Polynomial.C c * z.denom).degree := by
    rw [Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_mul,
      Polynomial.degree_C hc, zero_add, Polynomial.degree_eq_natDegree hden0, hnumdeg]
  have hlc : z.num.leadingCoeff =
      (Polynomial.C c * z.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    dsimp only [c]
    field_simp
  have hpdeg : p.degree < z.num.degree := by
    simpa only [p] using Polynomial.degree_sub_lt_left hdegree hnum0 hlc
  have hpnat : p.natDegree < z.denom.natDegree := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hp]
    rw [← hnumdeg]
    simpa [Polynomial.degree_eq_natDegree hnum0] using hpdeg
  rw [hrepr, RatFunc.intDegree_div]
  · simp only [RatFunc.intDegree_polynomial]
    omega
  · exact RatFunc.algebraMap_ne_zero hp
  · exact RatFunc.algebraMap_ne_zero hden0


-- @@ L131-131 verbatim
end RatFunc


-- @@ L133-133 verbatim
namespace FunctionField


-- @@ L135-135 verbatim
variable (k K : Type*) [Field k] [Field K]


-- @@ L137-137 verbatim
open MonoidWithZeroHom


-- @@ L139-163 verbatim
/-- The ordered multiplicative group with zero `ℤᵐ⁰` has no nontrivial ordered monoid
automorphisms. -/
private noncomputable def withZeroMulIntLogAddEquiv
    (e : ℤᵐ⁰ ≃*o ℤᵐ⁰) : ℤ ≃+ ℤ := by
  let f : ℤ →+ ℤ :=
    { toFun := fun z => WithZero.log (e (WithZero.exp z))
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [WithZero.exp_add, map_mul]
        rw [WithZero.log_mul]
        · simp
        · simp }
  refine AddEquiv.ofBijective f ?_
  constructor
  · intro x y h
    apply WithZero.exp_injective
    apply e.injective
    simpa [f] using congrArg WithZero.exp h
  · intro y
    refine ⟨WithZero.log (e.symm (WithZero.exp y)), ?_⟩
    dsimp [f]
    rw [WithZero.exp_log]
    · simp
    · simp


-- @@ L165-191 verbatim
/-- A normalized discrete rank-one value group has a unique order-preserving normalization. -/
theorem orderMonoidIso_withZeroMulInt_eq_refl (e : ℤᵐ⁰ ≃*o ℤᵐ⁰) :
    e = OrderMonoidIso.refl ℤᵐ⁰ := by
  have hmono : Monotone (withZeroMulIntLogAddEquiv e) := by
    intro x y hxy
    dsimp [withZeroMulIntLogAddEquiv]
    change WithZero.log (e (WithZero.exp x)) ≤
      WithZero.log (e (WithZero.exp y))
    apply WithZero.exp_le_exp.mp
    rw [WithZero.exp_log, WithZero.exp_log]
    · exact e.toOrderIso.monotone (WithZero.exp_le_exp.mpr hxy)
    · simp
    · simp
  rcases Int.addEquiv_eq_refl_or_neg (withZeroMulIntLogAddEquiv e) with h | h
  · ext x
    by_cases hx : x = 0
    · simp [hx]
    · have ht := DFunLike.congr_fun h (WithZero.log x)
      change WithZero.log (e (WithZero.exp (WithZero.log x))) = WithZero.log x at ht
      rw [WithZero.exp_log hx] at ht
      have hex : e x ≠ 0 := by simpa using hx
      have hexp := congrArg WithZero.exp ht
      rw [WithZero.exp_log hex, WithZero.exp_log hx] at hexp
      simpa using hexp
  · have hle := hmono (show (0 : ℤ) ≤ 1 by omega)
    rw [h] at hle
    norm_num at hle


-- @@ L193-199 verbatim
/-- Any two order-preserving normalizations of the same value group are equal. -/
theorem orderMonoidIso_withZeroMulInt_unique {G : Type*}
    [LinearOrderedCommGroupWithZero G] (e f : G ≃*o ℤᵐ⁰) : e = f := by
  have h := orderMonoidIso_withZeroMulInt_eq_refl (e.symm.trans f)
  ext x
  have hx := DFunLike.congr_fun h (e x)
  simpa using hx.symm


-- @@ L201-214 verbatim
/-- A coordinate-free place of `K/k`: a nontrivial valuation subring of `K` containing the
constant field, together with the proposition that its value group admits the discrete rank-one
normalization.  The normalization is stored only through `Nonempty`, so a place is determined by
its valuation subring rather than by a choice of uniformizer. -/
structure Place [Algebra k K] where
  /-- The valuation subring underlying the place. -/
  toValuationSubring : ValuationSubring K
  /-- A place is nontrivial. -/
  ne_top : toValuationSubring ≠ ⊤
  /-- Constants are integral at every place. -/
  triv_on_k : ∀ c : k, algebraMap k K c ∈ toValuationSubring
  /-- The value group is discrete of rank one, expressed without choosing a normalization. -/
  isDiscrete : Nonempty
    (ValueGroup₀ (.ofClass toValuationSubring.valuation) ≃*o ℤᵐ⁰)


-- @@ L216-216 verbatim
namespace Place


-- @@ L218-218 verbatim
variable {k K : Type*} [Field k] [Field K] [Algebra k K]


-- @@ L220-227 verbatim
/-- Two places are equal when their valuation subrings are equal. -/
@[ext]
theorem ext {v w : Place k K}
    (h : v.toValuationSubring = w.toValuationSubring) : v = w := by
  cases v
  cases w
  cases h
  rfl


-- @@ L229-234 verbatim
/-- Places inherit the membership coercion of their valuation subrings. -/
instance : SetLike (Place k K) K where
  coe v := v.toValuationSubring
  coe_injective := by
    intro v w h
    exact ext (SetLike.coe_injective h)


-- @@ L236-238 verbatim
@[simp]
theorem mem_toValuationSubring (v : Place k K) (x : K) :
    x ∈ v.toValuationSubring ↔ x ∈ v := Iff.rfl


-- @@ L240-243 verbatim
/-- A normalization of the value group of a coordinate-free place. -/
noncomputable def normalization (v : Place k K) :
    ValueGroup₀ (.ofClass v.toValuationSubring.valuation) ≃*o ℤᵐ⁰ :=
  Classical.choice v.isDiscrete


-- @@ L245-248 verbatim
/-- The normalized `ℤᵐ⁰`-valued valuation associated to a coordinate-free place. -/
noncomputable def valuation (v : Place k K) : Valuation K ℤᵐ⁰ :=
  v.toValuationSubring.valuation.restrict.map
    v.normalization.toMonoidWithZeroHom v.normalization.toOrderIso.monotone


-- @@ L250-256 verbatim
/-- The normalized valuation is equivalent to the canonical valuation of the valuation
subring. -/
theorem valuation_isEquiv_canonical (v : Place k K) :
    v.valuation.IsEquiv v.toValuationSubring.valuation := by
  exact (Valuation.isEquiv_map_self_of_strictMono
    v.normalization.toMonoidWithZeroHom v.normalization.strictMono).trans
      v.toValuationSubring.valuation.isEquiv_restrict.symm


-- @@ L258-264 verbatim
/-- Recovering the valuation subring from the normalized valuation gives the original place. -/
@[simp]
theorem valuationSubring_valuation (v : Place k K) :
    v.valuation.valuationSubring = v.toValuationSubring := by
  exact (Valuation.isEquiv_iff_valuationSubring _ _).mp
    v.valuation_isEquiv_canonical |>.trans
      v.toValuationSubring.valuationSubring_valuation


-- @@ L266-282 verbatim
/-- The normalized valuation of a place is trivial on the constant field. -/
instance valuation_isTrivialOn (v : Place k K) : v.valuation.IsTrivialOn k where
  eq_one c hc := by
    let w := v.toValuationSubring.valuation
    have hc_le : w (algebraMap k K c) ≤ 1 := by
      rw [v.toValuationSubring.valuation_le_one_iff]
      exact v.triv_on_k c
    have hc_inv_le : w (algebraMap k K c⁻¹) ≤ 1 := by
      rw [v.toValuationSubring.valuation_le_one_iff]
      exact v.triv_on_k c⁻¹
    have hmap_ne : w (algebraMap k K c) ≠ 0 := by simp [hc]
    have hmap_pos : 0 < w (algebraMap k K c) := zero_lt_iff.mpr hmap_ne
    have hinv_le : (w (algebraMap k K c))⁻¹ ≤ 1 := by
      simpa only [map_inv₀, map_inv] using hc_inv_le
    have hw : w (algebraMap k K c) = 1 :=
      le_antisymm hc_le ((inv_le_one₀ hmap_pos).1 hinv_le)
    exact v.valuation_isEquiv_canonical.eq_one_iff_eq_one.mpr hw


-- @@ L284-290 verbatim
/-- The normalized valuation of a place is nontrivial. -/
instance valuation_isNontrivial (v : Place k K) : v.valuation.IsNontrivial := by
  have hcanonical : v.toValuationSubring.valuation.IsNontrivial := by
    by_contra h
    exact v.ne_top (v.toValuationSubring.eq_top_iff.mpr h)
  exact Valuation.isNontrivial_of_isEquiv
    v.valuation_isEquiv_canonical.symm hcanonical


-- @@ L292-294 verbatim
/-- The valuation ring itself, viewed as a `k`-algebra. -/
instance algebraValuationSubring (v : Place k K) : Algebra k v.toValuationSubring :=
  (algebraMap k K).codRestrict v.toValuationSubring (fun c ↦ v.triv_on_k c) |>.toAlgebra


-- @@ L296-298 verbatim
/-- The residue field of a coordinate-free place. -/
abbrev residueField (v : Place k K) :=
  IsLocalRing.ResidueField v.toValuationSubring


-- @@ L300-302 verbatim
/-- The intrinsic degree of a place is the dimension of its residue field over `k`. -/
noncomputable def degree (v : Place k K) : ℕ :=
  Module.finrank k v.residueField


-- @@ L304-306 verbatim
end Place

-- Coordinate-chart infrastructure; the intrinsic API is `FunctionField.Place`.

-- @@ L307-307 verbatim
namespace Chart


-- @@ L309-310 verbatim
/-- The classical decidable equality used to define the valuation at infinity. -/
local instance instDecidableEqRatFuncRiemannRoch : DecidableEq k⟮X⟯ := Classical.decEq _


-- @@ L312-313 verbatim
/-- The valuation subring at infinity of the rational function field `k(X)`. -/
abbrev inftyValuationSubring := (RatFunc.inftyValuation k).valuationSubring


-- @@ L315-315 verbatim
namespace inftyValuationSubring


-- @@ L317-317 verbatim
instance : IsDedekindDomain (inftyValuationSubring k) := by infer_instance


-- @@ L319-324 verbatim
instance : Algebra k (inftyValuationSubring k) :=
  (RatFunc.C.codRestrict (inftyValuationSubring k) fun c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (RatFunc.inftyValuation.C k hc).le).toAlgebra


-- @@ L326-326 verbatim
local notation "ᵐ∞" => IsLocalRing.maximalIdeal (inftyValuationSubring k)


-- @@ L328-329 verbatim
/-- The residue field at infinity. -/
local instance : Field (inftyValuationSubring k ⧸ ᵐ∞) := Ideal.Quotient.field ᵐ∞


-- @@ L331-370 verbatim
/-- The residue map at infinity is onto the constant field. -/
theorem residue_algebraMap_surjective :
    Function.Surjective (algebraMap k (inftyValuationSubring k ⧸ ᵐ∞)) := by
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  let z : k⟮X⟯ := (a : k⟮X⟯)
  have hzdeg : z.intDegree ≤ 0 := by
    by_cases hz : z = 0
    · simp [hz]
    have ha := a.property
    rw [Valuation.mem_valuationSubring_iff] at ha
    change RatFunc.inftyValuation k z ≤ 1 at ha
    have hv : RatFunc.inftyValuation k z = WithZero.exp z.intDegree :=
      RatFunc.inftyValuation_of_nonzero k hz
    rw [hv] at ha
    exact WithZero.exp_le_exp.mp (by simpa only [WithZero.exp_zero] using ha)
  obtain ⟨c, hc | hc⟩ := RatFunc.exists_sub_C_intDegree_neg z hzdeg
  · refine ⟨c, ?_⟩
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hzero : algebraMap k (inftyValuationSubring k) c - a = 0 := by
      apply Subtype.ext
      change RatFunc.C c - z = 0
      rw [show RatFunc.C c - z = -(z - RatFunc.C c) by ring, hc, neg_zero]
    rw [hzero]
    exact ᵐ∞.zero_mem
  · refine ⟨c, ?_⟩
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hne : z - RatFunc.C c ≠ 0 := by
      intro h
      rw [h, RatFunc.intDegree_zero] at hc
      omega
    have hpos : a - algebraMap k (inftyValuationSubring k) c ∈ ᵐ∞ := by
      rw [Valuation.mem_maximalIdeal_iff]
      change RatFunc.inftyValuation k (z - RatFunc.C c) < 1
      have hv : RatFunc.inftyValuation k (z - RatFunc.C c) =
          WithZero.exp (z - RatFunc.C c).intDegree :=
        RatFunc.inftyValuation_of_nonzero k hne
      rw [hv]
      exact WithZero.exp_lt_exp.mpr hc
    simpa only [neg_sub] using ᵐ∞.neg_mem hpos


-- @@ L372-377 verbatim
/-- The residue field of the valuation ring at infinity is canonically the constant field. -/
noncomputable def residueAlgEquiv :
    k ≃ₐ[k] (inftyValuationSubring k ⧸ ᵐ∞) :=
  AlgEquiv.ofBijective (Algebra.ofId k (inftyValuationSubring k ⧸ ᵐ∞))
    ⟨(Algebra.ofId k (inftyValuationSubring k ⧸ ᵐ∞)).injective,
      residue_algebraMap_surjective k⟩


-- @@ L379-381 verbatim
instance finiteDimensionalResidueField :
    FiniteDimensional k (inftyValuationSubring k ⧸ ᵐ∞) :=
  (residueAlgEquiv k).toLinearEquiv.finiteDimensional


-- @@ L383-387 verbatim
@[simp]
theorem finrank_residueField :
    Module.finrank k (inftyValuationSubring k ⧸ ᵐ∞) = 1 := by
  rw [← (residueAlgEquiv k).toLinearEquiv.finrank_eq]
  exact Module.finrank_self k


-- @@ L389-389 verbatim
end inftyValuationSubring


-- @@ L391-393 verbatim
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]


-- @@ L395-396 verbatim
/-- The integral closure in `K` of the valuation subring at infinity of `k(X)`. -/
abbrev infiniteIntegers := integralClosure (inftyValuationSubring k) K


-- @@ L398-398 verbatim
namespace infiniteIntegers


-- @@ L400-402 verbatim
instance isTorsionFreeOverInfinityRing :
    Module.IsTorsionFree (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsIntegralClosure.isTorsionFree (inftyValuationSubring k) K


-- @@ L404-406 verbatim
instance : IsFractionRing (infiniteIntegers k K) K :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (inftyValuationSubring k) k⟮X⟯ K (infiniteIntegers k K)


-- @@ L408-409 verbatim
instance : IsDedekindDomain (infiniteIntegers k K) :=
  integralClosure.isDedekindDomain (inftyValuationSubring k) k⟮X⟯ K


-- @@ L411-412 verbatim
instance : Module.Finite (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsIntegralClosure.finite (inftyValuationSubring k) k⟮X⟯ K (infiniteIntegers k K)


-- @@ L414-416 verbatim
instance : Algebra k (infiniteIntegers k K) :=
  ((algebraMap (inftyValuationSubring k) (infiniteIntegers k K)).comp
    (algebraMap k (inftyValuationSubring k))).toAlgebra


-- @@ L418-420 verbatim
instance : IsScalarTower k (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := inftyValuationSubring k)
    (A := infiniteIntegers k K) fun _ => rfl


-- @@ L422-422 verbatim
end infiniteIntegers


-- @@ L424-424 verbatim
namespace ringOfIntegers


-- @@ L426-431 verbatim
instance isTorsionFreeOverPolynomial :
    Module.IsTorsionFree k[X] (ringOfIntegers k K) := by
  let : FaithfulSMul k[X] K :=
    (faithfulSMul_iff_algebraMap_injective k[X] K).2
      (FunctionField.algebraMap_injective k K)
  exact IsIntegralClosure.isTorsionFree k[X] K


-- @@ L433-434 verbatim
instance algebraOverConstants : Algebra k (ringOfIntegers k K) :=
  ((algebraMap k[X] (ringOfIntegers k K)).comp (algebraMap k k[X])).toAlgebra


-- @@ L436-437 verbatim
instance isScalarTowerConstants : IsScalarTower k k[X] (ringOfIntegers k K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl


-- @@ L439-440 verbatim
instance finiteTypeOverConstants : Algebra.FiniteType k (ringOfIntegers k K) :=
  Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance


-- @@ L442-443 verbatim
instance moduleFiniteOverPolynomial : Module.Finite k[X] (ringOfIntegers k K) :=
  IsIntegralClosure.finite k[X] k⟮X⟯ K (ringOfIntegers k K)


-- @@ L445-445 verbatim
end ringOfIntegers


-- @@ L447-450 verbatim
/-- Coordinate places of `K`: finite places on the `k[X]` chart and places above infinity. -/
abbrev PlaceA :=
  IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K) ⊕
    IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)


-- @@ L452-455 verbatim
/-- The discrete valuation associated to a coordinate place. -/
def placeValuation : PlaceA k K → Valuation K ℤᵐ⁰
  | Sum.inl v => v.valuation K
  | Sum.inr v => v.valuation K


-- @@ L457-458 verbatim
/-- Divisors on `K` in the two-chart coordinate presentation. -/
abbrev DivisorA := PlaceA k K →₀ ℤ


-- @@ L460-460 verbatim
namespace PlaceA


-- @@ L462-468 verbatim
/-- The residue field at a finite coordinate place is finite-dimensional over the constant
field. -/
instance finiteDimensionalResidueFieldFinite
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    FiniteDimensional k (ringOfIntegers k K ⧸ v.asIdeal) := by
  let : Field (ringOfIntegers k K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  exact finite_of_finite_type_of_isJacobsonRing k _


-- @@ L470-495 verbatim
/-- The residue field at an infinite coordinate place is finite-dimensional over the constant
field. -/
instance finiteDimensionalResidueFieldInfinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    FiniteDimensional k (infiniteIntegers k K ⧸ v.asIdeal) := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p : Ideal A := v.asIdeal.under A
  let : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  let : p.IsMaximal := Ideal.IsMaximal.under A v.asIdeal
  let : v.asIdeal.LiesOver p := ⟨rfl⟩
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Field (S ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Algebra (A ⧸ p) (S ⧸ v.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def v.asIdeal p).ge
  have hp : p = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
  let : FiniteDimensional k (A ⧸ p) := by
    rw [hp]
    exact inftyValuationSubring.finiteDimensionalResidueField k
  let : FiniteDimensional (A ⧸ p) (S ⧸ v.asIdeal) := by
    have hfin := Ideal.inertiaDeg_pos v.asIdeal A
    rw [Ideal.inertiaDeg_eq_of_isMaximal p v.asIdeal] at hfin
    exact FiniteDimensional.of_finrank_pos hfin
  let : IsScalarTower k (A ⧸ p) (S ⧸ v.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact FiniteDimensional.trans k (A ⧸ p) (S ⧸ v.asIdeal)


-- @@ L497-500 verbatim
/-- The degree of a finite coordinate place over the constant field. -/
noncomputable def finiteDegree
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) : ℕ :=
  Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal)


-- @@ L502-502 verbatim
end PlaceA


-- @@ L504-509 verbatim
/-- The principal divisor of a nonzero function, combining its finite and infinite parts. -/
noncomputable def principalDivisorA : Additive Kˣ →+ DivisorA k K :=
  (Finsupp.mapDomain.addMonoidHom Sum.inl).comp
      (FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K)) +
    (Finsupp.mapDomain.addMonoidHom Sum.inr).comp
      (FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K))


-- @@ L511-527 verbatim
@[simp]
theorem principalDivisorA_apply_finite (x : Additive Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    principalDivisorA k K x (Sum.inl v) =
      FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K) x v := by
  simp only [principalDivisorA, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  change Finsupp.mapDomain Sum.inl
      (FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K) x) (Sum.inl v) +
    Finsupp.mapDomain Sum.inr
      (FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K) x)
        (Sum.inl v) = _
  rw [Finsupp.mapDomain_apply_of_injective Sum.inl_injective]
  rw [Finsupp.mapDomain_of_notMem_range]
  · simp
  · rintro ⟨w, h⟩
    cases h


-- @@ L529-545 verbatim
@[simp]
theorem principalDivisorA_apply_infinite (x : Additive Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    principalDivisorA k K x (Sum.inr v) =
      FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K) x v := by
  simp only [principalDivisorA, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  change Finsupp.mapDomain Sum.inl
      (FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K) x) (Sum.inr v) +
    Finsupp.mapDomain Sum.inr
      (FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K) x)
        (Sum.inr v) = _
  rw [Finsupp.mapDomain_apply_of_injective Sum.inr_injective]
  rw [Finsupp.mapDomain_of_notMem_range]
  · simp
  · rintro ⟨w, h⟩
    cases h


-- @@ L547-555 verbatim
/-- A principal-divisor coefficient is the negative logarithm of the corresponding valuation. -/
theorem placeValuation_eq_exp_neg_principalDivisor (x : Additive Kˣ) (v : PlaceA k K) :
    placeValuation k K v (x.toMul : K) =
      WithZero.exp (-(principalDivisorA k K x v)) := by
  rcases v with v | v
  · rw [principalDivisorA_apply_finite, FractionalIdeal.principalDivisor_apply]
    exact FractionalIdeal.valuation_eq_exp_neg_count v x.toMul
  · rw [principalDivisorA_apply_infinite, FractionalIdeal.principalDivisor_apply]
    exact FractionalIdeal.valuation_eq_exp_neg_count v x.toMul


-- @@ L557-557 verbatim
section ConstantField


-- @@ L559-559 verbatim
variable [Algebra k K] [IsScalarTower k k[X] K]


-- @@ L561-566 verbatim
instance ringOfIntegers.isScalarTowerConstantsFractions :
    IsScalarTower k (ringOfIntegers k K) K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] (ringOfIntegers k K) K,
      ← IsScalarTower.algebraMap_apply k k[X] (ringOfIntegers k K)]


-- @@ L568-580 verbatim
instance infiniteIntegers.isScalarTowerConstantsFractions :
    IsScalarTower k (infiniteIntegers k K) K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    have h₁ : algebraMap k (infiniteIntegers k K) c =
        algebraMap (inftyValuationSubring k) (infiniteIntegers k K)
          (algebraMap k (inftyValuationSubring k) c) := rfl
    have h₂ : algebraMap (inftyValuationSubring k) k⟮X⟯
        (algebraMap k (inftyValuationSubring k) c) = RatFunc.C c := rfl
    rw [h₁, ← IsScalarTower.algebraMap_apply (inftyValuationSubring k) (infiniteIntegers k K) K,
      IsScalarTower.algebraMap_apply (inftyValuationSubring k) k⟮X⟯ K, h₂,
      IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, Polynomial.algebraMap_eq,
      RatFunc.algebraMap_C]


-- @@ L582-591 verbatim
/-- Constants have valuation at most one at every coordinate place. -/
theorem placeValuation_algebraMap_le_one (v : PlaceA k K) (c : k) :
    placeValuation k K v (algebraMap k K c) ≤ 1 := by
  obtain w | w := v
  · change w.valuation K (algebraMap k K c) ≤ 1
    rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K]
    exact w.valuation_le_one _
  · change w.valuation K (algebraMap k K c) ≤ 1
    rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K]
    exact w.valuation_le_one _


-- @@ L593-605 verbatim
/-- A nonzero constant has trivial valuation at every coordinate place. -/
theorem placeValuation_algebraMap_eq_one (v : PlaceA k K) (c : kˣ) :
    placeValuation k K v (algebraMap k K (c : k)) = 1 := by
  have hc_le := placeValuation_algebraMap_le_one k K v (c : k)
  have hc_inv_le := placeValuation_algebraMap_le_one k K v ((c⁻¹ : kˣ) : k)
  have hmap_ne : placeValuation k K v (algebraMap k K (c : k)) ≠ 0 := by
    rw [map_ne_zero]
    exact (map_ne_zero (algebraMap k K)).2 c.ne_zero
  have hmap_pos : 0 < placeValuation k K v (algebraMap k K (c : k)) :=
    WithZero.pos_iff_ne_zero.2 hmap_ne
  have hinv_le : (placeValuation k K v (algebraMap k K (c : k)))⁻¹ ≤ 1 := by
    simpa using hc_inv_le
  exact le_antisymm hc_le ((inv_le_one₀ hmap_pos).1 hinv_le)


-- @@ L607-623 verbatim
/-- Multiplying by a nonzero constant does not change a principal divisor. -/
@[simp]
theorem principalDivisorA_algebraMap (c : kˣ) :
    principalDivisorA k K
        (Additive.ofMul (Units.map (algebraMap k K) c)) = 0 := by
  ext v
  simp only [Finsupp.zero_apply]
  have hv := placeValuation_eq_exp_neg_principalDivisor k K
    (Additive.ofMul (Units.map (algebraMap k K) c)) v
  change placeValuation k K v (algebraMap k K (c : k)) = _ at hv
  rw [placeValuation_algebraMap_eq_one k K v c] at hv
  have hexp : WithZero.exp (0 : ℤ) =
      WithZero.exp
        (-(principalDivisorA k K
          (Additive.ofMul (Units.map (algebraMap k K) c)) v)) := by
    simpa using hv
  exact neg_eq_zero.mp (WithZero.exp_injective hexp.symm)


-- @@ L625-625 verbatim
end ConstantField


-- @@ L627-627 verbatim
end Chart


-- @@ L629-629 verbatim
end FunctionField
