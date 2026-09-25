/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation


-- @@ L12-16 verbatim
/-!
# Height One Spectrum

Material destined for Mathlib.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open IsDedekindDomain HeightOneSpectrum adicCompletion NumberField UniformSpace.Completion


-- @@ L22-22 verbatim
local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩


-- @@ L24-24 verbatim
variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]


-- @@ L26-26 verbatim
namespace Rat.HeightOneSpectrum.IsIntegralClosure


-- @@ L28-28 verbatim
instance : Module.Free ℤ R := .of_equiv (IsIntegralClosure.intEquiv R).toIntLinearEquiv.symm


-- @@ L30-30 verbatim
instance : Module.Finite ℤ R := .equiv (IsIntegralClosure.intEquiv R).toIntLinearEquiv.symm


-- @@ L32-32 verbatim
instance : IsPrincipalIdealRing R := .of_surjective _ (IsIntegralClosure.intEquiv R).symm.surjective


-- @@ L34-38 verbatim
@[simp]
theorem intEquiv_apply_coe (z : R) :
    (IsIntegralClosure.intEquiv R z : R) = z := by
  obtain ⟨z, rfl⟩ := (IsIntegralClosure.intEquiv R).symm.surjective z
  simp


-- @@ L40-42 verbatim
end IsIntegralClosure

-- `Ideal.absNorm` needs this; local because the discrimination key is just `Infinite _`.

-- @@ L43-43 verbatim
local instance : Infinite R := .of_injective _ (IsIntegralClosure.intEquiv R).symm.injective


-- @@ L45-48 verbatim
theorem pow_natGenerator_dvd_iff (v : HeightOneSpectrum R) {n : ℕ} (m : ℕ) :
    natGenerator v ^ m ∣ n ↔ ↑n ∈ (v.asIdeal.map (IsIntegralClosure.intEquiv R)) ^ m := by
  rw [← span_natGenerator, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm


-- @@ L50-50 verbatim
variable [IsDedekindDomain R]


-- @@ L52-69 verbatim
theorem natGenerator_eq_absNorm (v : HeightOneSpectrum R) :
    natGenerator v = Ideal.absNorm v.asIdeal := by
  rw [natGenerator]
  conv_lhs =>
    enter[1, 1]
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.map (IsIntegralClosure.intEquiv R) v.asIdeal)]
  rw [Int.natAbs_eq_iff_associated.2 <| Submodule.IsPrincipal.associated_generator_span_self _]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal v.asIdeal
  simp only [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton,
    Ideal.absNorm_span_singleton]
  -- ❌️ at reducible transparency,
  --   Ring.toIntAlgebra ℤ
  -- and
  --   Algebra.id ℤ
  -- are not defeq, but they are at default transparency.
  erw [Algebra.norm_self ℤ]
  rw [← Algebra.norm_eq_of_ringEquiv (IsIntegralClosure.intEquiv R) (by ext; simp)]
  simp [-Nat.cast_natAbs]


-- @@ L71-78 verbatim
theorem intValuation_eq_padicValuation_iff_multiplicity_eq_multiplicity {x : R}
    (v : HeightOneSpectrum R) (hx : x ≠ 0) :
    intValuation v x = padicValuation (primesEquiv v) (IsIntegralClosure.intEquiv R x) ↔
      multiplicity v.asIdeal (Ideal.span {x}) = multiplicity (primesEquiv v).1
        (IsIntegralClosure.intEquiv R x).natAbs := by
  simp [intValuation_eq_coe_neg_multiplicity _ hx, padicValuation, hx,
    padicValInt, padicValNat_def <| Int.natAbs_ne_zero.2 <|
      (IsIntegralClosure.intEquiv R).map_ne_zero_iff.2 hx]


-- @@ L80-80 verbatim
variable [IsFractionRing R ℚ]


-- @@ L82-92 verbatim
set_option backward.isDefEq.respectTransparency.types false in
theorem valuation_apply_coe_eq_padicValuation (x : R)
    (v : HeightOneSpectrum R) :
    v.valuation ℚ (algebraMap R ℚ x) = padicValuation (primesEquiv v)
      (IsIntegralClosure.intEquiv R x) := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [intValuation_eq_padicValuation_iff_multiplicity_eq_multiplicity v hx]
    exact multiplicity_eq_of_emultiplicity_eq <| emultiplicity_eq_emultiplicity_iff.2
      fun n ↦ by simp [primesEquiv, pow_natGenerator_dvd_iff v n, ← Ideal.map_pow]


-- @@ L94-99 verbatim
theorem valuation_apply_eq_padicValuation (v : HeightOneSpectrum R) (x : ℚ) :
    v.valuation ℚ x = padicValuation (primesEquiv v) x := by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' ℚ n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  simp [IsFractionRing.mk'_eq_div, map_div₀, valuation_apply_coe_eq_padicValuation,
    IsIntegralClosure.intEquiv, RingOfIntegers.equiv]


-- @@ L101-106 verbatim
theorem adicCompletion.padicEquiv_cast
    (v : IsDedekindDomain.HeightOneSpectrum R) (x : WithVal (v.valuation ℚ)) :
    (padicEquiv v) x = Padic.withValRingEquiv (mapEquiv (withValEquiv v) x) := by
  rfl

-- Only have `Norm (v.adicCompletion ℚ)` for `R = 𝓞 ℚ` so specialise from here


-- @@ L108-125 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma adicCompletion.padicEquiv_norm_coe_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (x : WithVal (v.valuation ℚ)) :
    ‖(padicEquiv v) x‖ = ‖algebraMap _ (v.adicCompletion ℚ) x‖ := by
  rw [padicEquiv_cast v x, mapEquiv_coe, Padic.coe_withValRingEquiv,
    extension_coe (
      by simpa using Padic.isUniformInducing_cast_withVal (p := primesEquiv v) |>.uniformContinuous
    )]
  obtain ⟨x⟩ := x
  change _ = ‖FinitePlace.embedding v x‖
  rw [NumberField.FinitePlace.norm_embedding']
  rcases eq_or_ne x 0 with rfl | hx
  · simp [withValEquiv, Valuation.IsEquiv.uniformEquiv]
  · simp [padicValuation, withValEquiv, Valuation.IsEquiv.uniformEquiv,
      valuation_apply_eq_padicValuation, hx, primesEquiv, natGenerator_eq_absNorm v,
      WithZero.exp_neg, -WithZero.inv_exp]
    -- TODO: need to fix some defeq abuse upstream in FinitePlace.norm_def' to avoid the next line
    rfl


-- @@ L127-139 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma adicCompletion.padicEquiv_norm_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    ‖(padicEquiv v) x‖ = ‖x‖ := by
  obtain ⟨x, rfl⟩ := adicCompletion.ofCompletion_surjective ℚ v x
  induction x using induction_on with
  | hp =>
    apply isClosed_eq
    · exact continuous_norm.comp ((padicEquiv v).continuous.comp (continuous_ofCompletion ℚ v))
    · exact continuous_norm.comp (continuous_ofCompletion ℚ v)
  | ih a =>
    rw [padicEquiv_norm_coe_eq v]
    congr 1


-- @@ L141-141 verbatim
end Rat.HeightOneSpectrum
