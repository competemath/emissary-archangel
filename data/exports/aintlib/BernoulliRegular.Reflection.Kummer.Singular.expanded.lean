module

public import BernoulliRegular.Reflection.Kummer.Basic
public import BernoulliRegular.Reflection.SingularKummer.IntegralNormalization


-- @@ L6-39 verbatim
/-!
# Concrete cyclotomic + Kummer instantiation (REF-15b)

This file instantiates REF-15a's abstract Kummer-extension API with the
concrete singular `η` produced by REF-13/14 over a cyclotomic field
`K = ℚ(ζ_p)`.

## Bridge

The singular nontriviality `[s] ≠ 1` in `SingularGroup` is equivalent to
`(generator s : K) ∉ K^{×p}`. The forward direction is immediate
(`principalPair γ = s ⟹ generator s = γ^p`); the backward direction
combines the singular pair relation `(generator s) = (ideal s)^p` with
the fact that the multiplicative group of nonzero fractional ideals over a
Dedekind domain is torsion-free, so `(γ^p) = (ideal s)^p` forces
`(γ) = ideal s`. Combined with REF-15a's `finrank_splittingField_eq_one_iff_isPow`,
this gives `Module.finrank K (SplittingField (X^p - C (generator s : K))) ≠ 1`,
i.e. the Kummer extension is degree-`p`.

## Main results

* `FractionalIdeal.eq_of_count_eq`: nonzero fractional ideals are determined
  by their `count` at every height-one prime.
* `FractionalIdeal.pow_left_inj_of_ne_zero`: `I^n = J^n` (with `n ≠ 0`,
  `I, J ≠ 0`) implies `I = J`.
* `FractionalIdeal.units_pow_left_inj`: same at the level of units.
* `BernoulliRegular.Reflection.SingularKummer.SingularPair.mk_quotient_eq_one_iff_isPow`:
  for `s : SingularPair`, `[s] = 1` in `SingularGroup` iff
  `∃ γ : Kˣ, generator s = γ^p`.
* `BernoulliRegular.Kummer.Singular.exists_singularEta_not_isPow`: the
  integrally-normalized singular `η` of REF-14 satisfies `η ∉ K^{×p}`.
* `BernoulliRegular.Kummer.Singular.exists_singularEta_with_nontrivial_kummer`:
  the same `η` has `Module.finrank K (SplittingField (X^p - C η)) ≠ 1`.
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
noncomputable section


-- @@ L45-45 verbatim
open NumberField IsCyclotomicExtension Polynomial

-- @@ L46-46 verbatim
open scoped NumberField nonZeroDivisors


-- @@ L48-48 verbatim
namespace FractionalIdeal


-- @@ L50-50 verbatim
variable {R K : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

-- @@ L51-51 verbatim
variable [Field K] [Algebra R K] [IsFractionRing R K]


-- @@ L53-63 verbatim
omit [IsDomain R] in
/-- Nonzero fractional ideals over a Dedekind domain are determined by their
`count` at each height-one prime. -/
theorem eq_of_count_eq
    {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hI,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hJ]
  exact finprod_congr (fun v ↦ by rw [h v])


-- @@ L65-78 verbatim
omit [IsDomain R] in
/-- `I^n = J^n` for nonzero fractional ideals over a Dedekind domain forces
`I = J` whenever `n ≠ 0`: the multiplicative monoid of nonzero fractional
ideals is `n`-torsion-free. -/
theorem pow_left_inj_of_ne_zero
    {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (h : I ^ n = J ^ n) : I = J := by
  apply eq_of_count_eq hI hJ
  intro v
  have h_count : (n : ℤ) * FractionalIdeal.count K v I =
      (n : ℤ) * FractionalIdeal.count K v J := by
    rw [← FractionalIdeal.count_pow (K := K) (v := v),
        ← FractionalIdeal.count_pow (K := K) (v := v), h]
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) h_count


-- @@ L80-87 verbatim
omit [IsDomain R] in
/-- `I^n = J^n` for fractional-ideal units forces `I = J` whenever `n ≠ 0`. -/
theorem units_pow_left_inj
    {I J : (FractionalIdeal R⁰ K)ˣ} {n : ℕ} (hn : n ≠ 0) (h : I ^ n = J ^ n) :
    I = J := by
  apply Units.ext
  apply pow_left_inj_of_ne_zero (I.ne_zero) (J.ne_zero) hn
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h]


-- @@ L89-89 verbatim
end FractionalIdeal


-- @@ L91-91 verbatim
namespace BernoulliRegular


-- @@ L93-93 verbatim
namespace Reflection


-- @@ L95-95 verbatim
namespace SingularKummer


-- @@ L97-97 verbatim
namespace SingularPair


-- @@ L99-99 verbatim
variable {R K : Type*} [CommRing R] [IsDedekindDomain R]

-- @@ L100-100 verbatim
variable [Field K] [Algebra R K] [IsFractionRing R K]


-- @@ L102-128 verbatim
/-- For a singular pair `s = (I, α)`, `[s] = 1` in `SingularGroup` iff
`∃ γ : Kˣ, α = γ^p`. The forward direction is immediate; the backward
direction uses that the fractional-ideal group is torsion-free, so
`(γ^p) = (ideal s)^p` forces `(γ) = ideal s` and hence `s = principalPair γ`. -/
theorem mk_quotient_eq_one_iff_isPow {p : ℕ} (hp : p ≠ 0) (s : SingularPair R K p) :
    (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) = 1 ↔
      ∃ γ : Kˣ, generator s = γ ^ p := by
  rw [QuotientGroup.eq_one_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    rw [← hγ]
    rfl
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · -- ideal s = toPrincipalIdeal γ
      change toPrincipalIdeal R K γ = ideal s
      apply FractionalIdeal.units_pow_left_inj hp
      have hs := principal_eq_ideal_pow (R := R) (K := K) s
      -- hs : toPrincipalIdeal R K (generator s) = (ideal s) ^ p
      rw [hγ, map_pow] at hs
      -- hs : (toPrincipalIdeal R K γ) ^ p = (ideal s) ^ p
      exact hs
    · change γ ^ p = generator s
      exact hγ.symm


-- @@ L130-130 verbatim
end SingularPair


-- @@ L132-132 verbatim
end SingularKummer


-- @@ L134-134 verbatim
end Reflection


-- @@ L136-136 verbatim
namespace Kummer


-- @@ L138-138 verbatim
namespace Singular


-- @@ L140-140 verbatim
variable (K : Type*) [Field K] [NumberField K]

-- @@ L141-141 verbatim
variable (p : ℕ) [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]


-- @@ L143-175 verbatim
open Reflection.SingularKummer.SingularPair in
/-- **REF-15b: the singular `η` is not a global `p`-th power.**

Under the reflection hypotheses (V_i ≠ 0 for the right component), the
integrally-normalized singular `η : Kˣ` produced by REF-14 satisfies
`(η : K) ∉ K^{×p}`. This follows from singular nontriviality
`[t] ≠ 1` in `SingularGroup` via the iff
`mk_quotient_eq_one_iff_isPow`. -/
theorem exists_singularEta_not_isPow
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥) :
    ∃ η : Kˣ, ¬ ∃ β : K, β ^ p = (η : K) := by
  obtain ⟨_s, t, _gamma, _J, _ht_gen, _ht_ideal, _ht_principal, _hclass,
      _ht_component, ht_ne, _ht_loc, _ht_eigen⟩ :=
    exists_integral_normalized_singularPair_in_concrete_completed_localization_kernel
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot
  refine ⟨generator t, ?_⟩
  rintro ⟨β, hβ⟩
  apply ht_ne
  rw [mk_quotient_eq_one_iff_isPow hp.out.ne_zero]
  have hβ_ne : β ≠ 0 := by
    intro hβ0
    rw [hβ0, zero_pow hp.out.ne_zero] at hβ
    exact (generator t).ne_zero hβ.symm
  refine ⟨Units.mk0 β hβ_ne, ?_⟩
  apply Units.ext
  simp [Units.val_pow_eq_pow_val, hβ]


-- @@ L177-201 verbatim
open Reflection.SingularKummer.SingularPair in
/-- **REF-15b: the Kummer extension of the singular `η` is nontrivial.**

Under the reflection hypotheses, the splitting field of `X^p - C η` over `K`
for the singular `η` from REF-14 has degree ≠ 1 over `K`. -/
theorem exists_singularEta_with_nontrivial_kummer
    (hp_ne_two : p ≠ 2)
    (hζ : (primitiveRoots p K).Nonempty)
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥) :
    ∃ η : Kˣ,
      Module.finrank K (SplittingField (X ^ p - C ((η : K)))) ≠ 1 := by
  obtain ⟨η, hη⟩ :=
    exists_singularEta_not_isPow K p hp_gt_two hi_even hi_low hi_high hA_ne_bot
  refine ⟨η, ?_⟩
  rw [Ne, BernoulliRegular.Kummer.finrank_splittingField_eq_one_iff_isPow
    hp.out hp_ne_two hζ ((η : K))]
  rintro ⟨β, hβ⟩
  exact hη ⟨β, hβ⟩


-- @@ L203-203 verbatim
end Singular


-- @@ L205-205 verbatim
end Kummer


-- @@ L207-207 verbatim
end BernoulliRegular
