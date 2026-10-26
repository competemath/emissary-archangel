/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import RiemannRoch.Divisor
public import RiemannRoch.SeparableRelNorm
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.AlgebraInstances
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.GroupTheory.ArchimedeanDensely


-- @@ L19-34 verbatim
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


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
open scoped nonZeroDivisors Polynomial RatFunc WithZero


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
namespace FractionalIdeal


-- @@ L44-45 verbatim
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]


-- @@ L47-73 verbatim
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


-- @@ L75-75 verbatim
end FractionalIdeal


-- @@ L77-77 verbatim
namespace RatFunc


-- @@ L79-79 verbatim
variable {k : Type*} [Field k]


-- @@ L81-131 verbatim
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
    simpa only [p] using Polynomial.degree_sub_lt hdegree hnum0 hlc
  have hpnat : p.natDegree < z.denom.natDegree := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hp]
    rw [← hnumdeg]
    simpa [Polynomial.degree_eq_natDegree hnum0] using hpdeg
  rw [hrepr, RatFunc.intDegree_div]
  · simp only [RatFunc.intDegree_polynomial]
    omega
  · exact RatFunc.algebraMap_ne_zero hp
  · exact RatFunc.algebraMap_ne_zero hden0


-- @@ L133-133 verbatim
end RatFunc


-- @@ L135-135 verbatim
namespace FunctionField


-- @@ L137-137 verbatim
variable (k K : Type*) [Field k] [Field K]


-- @@ L139-139 verbatim
open MonoidWithZeroHom


-- @@ L141-165 verbatim
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


-- @@ L167-191 verbatim
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
    · rw [← WithZero.exp_log hx]
      apply WithZero.exp_injective
      have ht := congrArg WithZero.exp
        (DFunLike.congr_fun h (WithZero.log x))
      simpa [withZeroMulIntLogAddEquiv] using ht
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


-- @@ L250-263 verbatim
/-- The normalized valuation of an intrinsic place is surjective.  This is the
coordinate-free source of uniformizers: the canonical valuation is surjective onto its
value group, restriction to the value group with zero is surjective, and the stored
normalization is an equivalence. -/
theorem valuation_surjective (v : Place k K) : Function.Surjective v.valuation := by
  intro z
  obtain ⟨x, hx⟩ := ValueGroup₀.restrict₀_surjective
    (.ofClass v.toValuationSubring.valuation) (v.normalization.symm z)
  refine ⟨x, ?_⟩
  change v.toValuationSubring.valuation.restrict x =
    v.normalization.symm z at hx
  change v.normalization
      (v.toValuationSubring.valuation.restrict x) = z
  rw [hx, v.normalization.apply_symm_apply]


-- @@ L265-267 verbatim
/-- A coordinate-free uniformizer of an intrinsic place. -/
noncomputable def uniformizer (v : Place k K) : K :=
  Classical.choose (v.valuation_surjective (WithZero.exp (-1)))


-- @@ L269-273 verbatim
/-- The normalized value of the coordinate-free uniformizer is `exp (-1)`. -/
@[simp]
theorem valuation_uniformizer (v : Place k K) :
    v.valuation v.uniformizer = WithZero.exp (-1) :=
  Classical.choose_spec (v.valuation_surjective (WithZero.exp (-1)))


-- @@ L275-280 verbatim
/-- A coordinate-free uniformizer is nonzero. -/
theorem uniformizer_ne_zero (v : Place k K) : v.uniformizer ≠ 0 := by
  intro h
  have hv := v.valuation_uniformizer
  rw [h, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm


-- @@ L282-288 verbatim
/-- The normalized valuation is equivalent to the canonical valuation of the valuation
subring. -/
theorem valuation_isEquiv_canonical (v : Place k K) :
    v.valuation.IsEquiv v.toValuationSubring.valuation := by
  exact (Valuation.isEquiv_map_self_of_strictMono
    v.normalization.toMonoidWithZeroHom v.normalization.strictMono).trans
      v.toValuationSubring.valuation.isEquiv_restrict.symm


-- @@ L290-296 verbatim
/-- Recovering the valuation subring from the normalized valuation gives the original place. -/
@[simp]
theorem valuationSubring_valuation (v : Place k K) :
    v.valuation.valuationSubring = v.toValuationSubring := by
  exact (Valuation.isEquiv_iff_valuationSubring _ _).mp
    v.valuation_isEquiv_canonical |>.trans
      v.toValuationSubring.valuationSubring_valuation


-- @@ L298-304 verbatim
/-- Membership in the maximal ideal of a place is detected by its normalized valuation. -/
theorem mem_maximalIdeal_iff_valuation_lt_one (v : Place k K)
    (x : v.toValuationSubring) :
    x ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔
      v.valuation (x : K) < 1 := by
  rw [v.toValuationSubring.valuation_lt_one_iff]
  exact v.valuation_isEquiv_canonical.lt_one_iff_lt_one.symm


-- @@ L306-322 verbatim
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


-- @@ L324-330 verbatim
/-- The normalized valuation of a place is nontrivial. -/
instance valuation_isNontrivial (v : Place k K) : v.valuation.IsNontrivial := by
  have hcanonical : v.toValuationSubring.valuation.IsNontrivial := by
    by_contra h
    exact v.ne_top (v.toValuationSubring.eq_top_iff.mpr h)
  exact Valuation.isNontrivial_of_isEquiv
    v.valuation_isEquiv_canonical.symm hcanonical


-- @@ L332-334 verbatim
/-- The valuation ring itself, viewed as a `k`-algebra. -/
instance algebraValuationSubring (v : Place k K) : Algebra k v.toValuationSubring :=
  (algebraMap k K).codRestrict v.toValuationSubring (fun c ↦ v.triv_on_k c) |>.toAlgebra


-- @@ L336-338 verbatim
/-- The residue field of a coordinate-free place. -/
abbrev residueField (v : Place k K) :=
  IsLocalRing.ResidueField v.toValuationSubring


-- @@ L340-342 verbatim
/-- The intrinsic degree of a place is the dimension of its residue field over `k`. -/
noncomputable def degree (v : Place k K) : ℕ :=
  Module.finrank k v.residueField


-- @@ L344-346 verbatim
end Place

-- Coordinate-chart infrastructure; the intrinsic API is `FunctionField.Place`.

-- @@ L347-347 verbatim
namespace Chart


-- @@ L349-350 verbatim
/-- The classical decidable equality used to define the valuation at infinity. -/
local instance instDecidableEqRatFuncRiemannRoch : DecidableEq k⟮X⟯ := Classical.decEq _


-- @@ L352-353 verbatim
/-- The valuation subring at infinity of the rational function field `k(X)`. -/
abbrev inftyValuationSubring := (RatFunc.inftyValuation k).valuationSubring


-- @@ L355-355 verbatim
namespace inftyValuationSubring


-- @@ L357-357 verbatim
instance : IsDedekindDomain (inftyValuationSubring k) := by infer_instance


-- @@ L359-364 verbatim
instance : Algebra k (inftyValuationSubring k) :=
  (RatFunc.C.codRestrict (inftyValuationSubring k) fun c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (RatFunc.inftyValuation.C k hc).le).toAlgebra


-- @@ L366-366 verbatim
local notation "ᵐ∞" => IsLocalRing.maximalIdeal (inftyValuationSubring k)


-- @@ L368-369 verbatim
/-- The residue field at infinity. -/
local instance : Field (inftyValuationSubring k ⧸ ᵐ∞) := Ideal.Quotient.field ᵐ∞


-- @@ L371-410 verbatim
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


-- @@ L412-417 verbatim
/-- The residue field of the valuation ring at infinity is canonically the constant field. -/
noncomputable def residueAlgEquiv :
    k ≃ₐ[k] (inftyValuationSubring k ⧸ ᵐ∞) :=
  AlgEquiv.ofBijective (Algebra.ofId k (inftyValuationSubring k ⧸ ᵐ∞))
    ⟨(Algebra.ofId k (inftyValuationSubring k ⧸ ᵐ∞)).injective,
      residue_algebraMap_surjective k⟩


-- @@ L419-421 verbatim
instance finiteDimensionalResidueField :
    FiniteDimensional k (inftyValuationSubring k ⧸ ᵐ∞) :=
  (residueAlgEquiv k).toLinearEquiv.finiteDimensional


-- @@ L423-427 verbatim
@[simp]
theorem finrank_residueField :
    Module.finrank k (inftyValuationSubring k ⧸ ᵐ∞) = 1 := by
  rw [← (residueAlgEquiv k).toLinearEquiv.finrank_eq]
  exact Module.finrank_self k


-- @@ L429-429 verbatim
end inftyValuationSubring


-- @@ L431-433 verbatim
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]


-- @@ L435-436 verbatim
/-- The integral closure in `K` of the valuation subring at infinity of `k(X)`. -/
abbrev infiniteIntegers := integralClosure (inftyValuationSubring k) K


-- @@ L438-438 verbatim
namespace infiniteIntegers


-- @@ L440-442 verbatim
instance isTorsionFreeOverInfinityRing :
    Module.IsTorsionFree (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsIntegralClosure.isTorsionFree (inftyValuationSubring k) K


-- @@ L444-446 verbatim
instance : IsFractionRing (infiniteIntegers k K) K :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (inftyValuationSubring k) k⟮X⟯ K (infiniteIntegers k K)


-- @@ L448-449 verbatim
instance : IsDedekindDomain (infiniteIntegers k K) :=
  integralClosure.isDedekindDomain (inftyValuationSubring k) k⟮X⟯ K


-- @@ L451-452 verbatim
instance : Module.Finite (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsIntegralClosure.finite (inftyValuationSubring k) k⟮X⟯ K (infiniteIntegers k K)


-- @@ L454-456 verbatim
instance : Algebra k (infiniteIntegers k K) :=
  ((algebraMap (inftyValuationSubring k) (infiniteIntegers k K)).comp
    (algebraMap k (inftyValuationSubring k))).toAlgebra


-- @@ L458-460 verbatim
instance : IsScalarTower k (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := inftyValuationSubring k)
    (A := infiniteIntegers k K) fun _ => rfl


-- @@ L462-462 verbatim
end infiniteIntegers


-- @@ L464-464 verbatim
namespace ringOfIntegers


-- @@ L466-471 verbatim
instance isTorsionFreeOverPolynomial :
    Module.IsTorsionFree k[X] (ringOfIntegers k K) := by
  letI : FaithfulSMul k[X] K :=
    (faithfulSMul_iff_algebraMap_injective k[X] K).2
      (FunctionField.algebraMap_injective k K)
  exact IsIntegralClosure.isTorsionFree k[X] K


-- @@ L473-474 verbatim
instance algebraOverConstants : Algebra k (ringOfIntegers k K) :=
  ((algebraMap k[X] (ringOfIntegers k K)).comp (algebraMap k k[X])).toAlgebra


-- @@ L476-477 verbatim
instance isScalarTowerConstants : IsScalarTower k k[X] (ringOfIntegers k K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl


-- @@ L479-480 verbatim
instance finiteTypeOverConstants : Algebra.FiniteType k (ringOfIntegers k K) :=
  Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance


-- @@ L482-483 verbatim
instance moduleFiniteOverPolynomial : Module.Finite k[X] (ringOfIntegers k K) :=
  IsIntegralClosure.finite k[X] k⟮X⟯ K (ringOfIntegers k K)


-- @@ L485-485 verbatim
end ringOfIntegers


-- @@ L487-490 verbatim
/-- Coordinate places of `K`: finite places on the `k[X]` chart and places above infinity. -/
abbrev PlaceA :=
  IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K) ⊕
    IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)


-- @@ L492-495 verbatim
/-- The discrete valuation associated to a coordinate place. -/
def placeValuation : PlaceA k K → Valuation K ℤᵐ⁰
  | Sum.inl v => v.valuation K
  | Sum.inr v => v.valuation K


-- @@ L497-498 verbatim
/-- Divisors on `K` in the two-chart coordinate presentation. -/
abbrev DivisorA := PlaceA k K →₀ ℤ


-- @@ L500-500 verbatim
namespace PlaceA


-- @@ L502-508 verbatim
/-- The residue field at a finite coordinate place is finite-dimensional over the constant
field. -/
instance finiteDimensionalResidueFieldFinite
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    FiniteDimensional k (ringOfIntegers k K ⧸ v.asIdeal) := by
  letI : Field (ringOfIntegers k K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  exact finite_of_finite_type_of_isJacobsonRing k _


-- @@ L510-535 verbatim
/-- The residue field at an infinite coordinate place is finite-dimensional over the constant
field. -/
instance finiteDimensionalResidueFieldInfinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    FiniteDimensional k (infiniteIntegers k K ⧸ v.asIdeal) := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p : Ideal A := v.asIdeal.under A
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : p.IsMaximal := Ideal.IsMaximal.under A v.asIdeal
  letI : v.asIdeal.LiesOver p := ⟨rfl⟩
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Algebra (A ⧸ p) (S ⧸ v.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def v.asIdeal p).ge
  have hp : p = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
  letI : FiniteDimensional k (A ⧸ p) := by
    rw [hp]
    exact inftyValuationSubring.finiteDimensionalResidueField k
  letI : FiniteDimensional (A ⧸ p) (S ⧸ v.asIdeal) := by
    have hfin := Ideal.inertiaDeg_pos p v.asIdeal
    rw [Ideal.inertiaDeg_algebraMap] at hfin
    exact FiniteDimensional.of_finrank_pos hfin
  letI : IsScalarTower k (A ⧸ p) (S ⧸ v.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact FiniteDimensional.trans k (A ⧸ p) (S ⧸ v.asIdeal)


-- @@ L537-540 verbatim
/-- The degree of a finite coordinate place over the constant field. -/
noncomputable def finiteDegree
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) : ℕ :=
  Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal)


-- @@ L542-542 verbatim
end PlaceA


-- @@ L544-549 verbatim
/-- The principal divisor of a nonzero function, combining its finite and infinite parts. -/
noncomputable def principalDivisorA : Additive Kˣ →+ DivisorA k K :=
  (Finsupp.mapDomain.addMonoidHom Sum.inl).comp
      (FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K)) +
    (Finsupp.mapDomain.addMonoidHom Sum.inr).comp
      (FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K))


-- @@ L551-567 verbatim
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
  rw [Finsupp.mapDomain_apply Sum.inl_injective]
  rw [Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨w, h⟩
    cases h


-- @@ L569-585 verbatim
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
  rw [Finsupp.mapDomain_apply Sum.inr_injective]
  rw [Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨w, h⟩
    cases h


-- @@ L587-595 verbatim
/-- A principal-divisor coefficient is the negative logarithm of the corresponding valuation. -/
theorem placeValuation_eq_exp_neg_principalDivisor (x : Additive Kˣ) (v : PlaceA k K) :
    placeValuation k K v (x.toMul : K) =
      WithZero.exp (-(principalDivisorA k K x v)) := by
  rcases v with v | v
  · rw [principalDivisorA_apply_finite, FractionalIdeal.principalDivisor_apply]
    exact FractionalIdeal.valuation_eq_exp_neg_count v x.toMul
  · rw [principalDivisorA_apply_infinite, FractionalIdeal.principalDivisor_apply]
    exact FractionalIdeal.valuation_eq_exp_neg_count v x.toMul


-- @@ L597-597 verbatim
section ConstantField


-- @@ L599-599 verbatim
variable [Algebra k K] [IsScalarTower k k[X] K]


-- @@ L601-606 verbatim
instance ringOfIntegers.isScalarTowerConstantsFractions :
    IsScalarTower k (ringOfIntegers k K) K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] (ringOfIntegers k K) K,
      ← IsScalarTower.algebraMap_apply k k[X] (ringOfIntegers k K)]


-- @@ L608-620 verbatim
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


-- @@ L622-631 verbatim
/-- Constants have valuation at most one at every coordinate place. -/
theorem placeValuation_algebraMap_le_one (v : PlaceA k K) (c : k) :
    placeValuation k K v (algebraMap k K c) ≤ 1 := by
  obtain w | w := v
  · show w.valuation K (algebraMap k K c) ≤ 1
    rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K]
    exact w.valuation_le_one _
  · show w.valuation K (algebraMap k K c) ≤ 1
    rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K]
    exact w.valuation_le_one _


-- @@ L633-645 verbatim
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


-- @@ L647-663 verbatim
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


-- @@ L665-665 verbatim
end ConstantField


-- @@ L667-667 verbatim
end Chart


-- @@ L669-669 verbatim
end FunctionField
