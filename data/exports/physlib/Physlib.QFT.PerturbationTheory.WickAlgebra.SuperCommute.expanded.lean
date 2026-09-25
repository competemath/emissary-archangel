/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.WickAlgebra.Basic

-- @@ L9-13 verbatim
/-!

# SuperCommute on Field operator algebra

-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace FieldSpecification

-- @@ L18-18 verbatim
open FieldOpFreeAlgebra

-- @@ L19-19 verbatim
open Physlib.List

-- @@ L20-20 verbatim
open FieldStatistic


-- @@ L22-22 verbatim
namespace WickAlgebra

-- @@ L23-23 verbatim
variable {𝓕 : FieldSpecification}


-- @@ L25-28 verbatim
lemma ι_superCommuteF_eq_zero_of_ι_right_zero (a b : 𝓕.FieldOpFreeAlgebra) (h : ι b = 0) :
    ι [a, b]ₛF = 0 := by
  obtain ⟨h1, h2⟩ := (ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero b).mp h
  simp [superCommuteF_expand_bosonicProjF_fermionicProjF, h1, h2]


-- @@ L30-33 verbatim
lemma ι_superCommuteF_eq_zero_of_ι_left_zero (a b : 𝓕.FieldOpFreeAlgebra) (h : ι a = 0) :
    ι [a, b]ₛF = 0 := by
  obtain ⟨h1, h2⟩ := (ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero a).mp h
  simp [superCommuteF_expand_bosonicProjF_fermionicProjF, h1, h2]


-- @@ L35-39 verbatim
/-!

## Defining normal order for `FiedOpAlgebra`.

-/


-- @@ L41-43 verbatim
lemma ι_superCommuteF_right_zero_of_mem_ideal (a b : 𝓕.FieldOpFreeAlgebra)
    (h : b ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι [a, b]ₛF = 0 :=
  ι_superCommuteF_eq_zero_of_ι_right_zero a b ((ι_eq_zero_iff_mem_ideal b).mpr h)


-- @@ L45-48 verbatim
lemma ι_superCommuteF_eq_of_equiv_right (a b1 b2 : 𝓕.FieldOpFreeAlgebra) (h : b1 ≈ b2) :
    ι [a, b1]ₛF = ι [a, b2]ₛF := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  exact ι_superCommuteF_right_zero_of_mem_ideal a _ ((equiv_iff_sub_mem_ideal _ _).mp h)


-- @@ L50-67 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The super commutator on the `WickAlgebra` defined as a linear map `[a,_]ₛ`. -/
noncomputable def superCommuteRight (a : 𝓕.FieldOpFreeAlgebra) :
  WickAlgebra 𝓕 →ₗ[ℂ] WickAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ superCommuteF a)
    (ι_superCommuteF_eq_of_equiv_right a)
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp


-- @@ L69-70 verbatim
lemma superCommuteRight_apply_ι (a b : 𝓕.FieldOpFreeAlgebra) :
    superCommuteRight a (ι b) = ι [a, b]ₛF := by rfl


-- @@ L72-73 verbatim
lemma superCommuteRight_apply_quot (a b : 𝓕.FieldOpFreeAlgebra) :
    superCommuteRight a ⟦b⟧= ι [a, b]ₛF := by rfl


-- @@ L75-81 verbatim
lemma superCommuteRight_eq_of_equiv (a1 a2 : 𝓕.FieldOpFreeAlgebra) (h : a1 ≈ a2) :
    superCommuteRight a1 = superCommuteRight a2 := by
  ext b
  obtain ⟨b, rfl⟩ := ι_surjective b
  simpa [superCommuteRight_apply_ι, sub_eq_zero] using
    ι_superCommuteF_eq_zero_of_ι_left_zero (a1 - a2) b
      ((ι_eq_zero_iff_mem_ideal _).mpr ((equiv_iff_sub_mem_ideal _ _).mp h))


-- @@ L83-116 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- For a field specification `𝓕`, `superCommute` is the linear map

  `WickAlgebra 𝓕 →ₗ[ℂ] WickAlgebra 𝓕 →ₗ[ℂ] WickAlgebra 𝓕`

  defined as the descent of `ι ∘ superCommuteF` in both arguments.
  In particular for `φs` and `φs'` lists of `𝓕.CrAnFieldOp` in `WickAlgebra 𝓕` the following
  relation holds:

  `superCommute φs φs' = φs * φs' - 𝓢(φs, φs') • φs' * φs`

  The notation `[a, b]ₛ` is used for `superCommute a b`.
  -/
noncomputable def superCommute : WickAlgebra 𝓕 →ₗ[ℂ]
    WickAlgebra 𝓕 →ₗ[ℂ] WickAlgebra 𝓕 where
  toFun := Quotient.lift superCommuteRight superCommuteRight_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, rfl⟩ := ι_surjective x
    obtain ⟨y, rfl⟩ := ι_surjective y
    ext b
    obtain ⟨b, rfl⟩ := ι_surjective b
    rw [← map_add, ι_apply, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp only [LinearMap.add_apply]
    rw [superCommuteRight_apply_quot, superCommuteRight_apply_quot, superCommuteRight_apply_quot]
    simp
  map_smul' c y := by
    obtain ⟨y, rfl⟩ := ι_surjective y
    ext b
    obtain ⟨b, rfl⟩ := ι_surjective b
    rw [← map_smul, ι_apply, ι_apply, ι_apply]
    simp only [Quotient.lift_mk, RingHom.id_apply, LinearMap.smul_apply]
    rw [superCommuteRight_apply_quot, superCommuteRight_apply_quot]
    simp


-- @@ L118-119 verbatim
@[inherit_doc superCommute]
scoped[FieldSpecification.WickAlgebra] notation "[" a "," b "]ₛ" => superCommute a b


-- @@ L121-122 verbatim
lemma superCommute_eq_ι_superCommuteF (a b : 𝓕.FieldOpFreeAlgebra) :
    [ι a, ι b]ₛ = ι [a, b]ₛF := rfl


-- @@ L124-128 verbatim
/-!

## Properties of `superCommute`.

-/


-- @@ L130-134 verbatim
/-!

## Properties from the definition of WickAlgebra

-/


-- @@ L136-139 verbatim
lemma superCommute_create_create {φ φ' : 𝓕.CrAnFieldOp}
    (h : 𝓕 |>ᶜ φ = .create) (h' : 𝓕 |>ᶜ φ' = .create) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = 0 :=
  ι_superCommuteF_of_create_create _ _ h h'


-- @@ L141-144 verbatim
lemma superCommute_annihilate_annihilate {φ φ' : 𝓕.CrAnFieldOp}
    (h : 𝓕 |>ᶜ φ = .annihilate) (h' : 𝓕 |>ᶜ φ' = .annihilate) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = 0 :=
  ι_superCommuteF_of_annihilate_annihilate _ _ h h'


-- @@ L146-148 verbatim
lemma superCommute_diff_statistic {φ φ' : 𝓕.CrAnFieldOp} (h : (𝓕 |>ₛ φ) ≠ 𝓕 |>ₛ φ') :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = 0 :=
  ι_superCommuteF_of_diff_statistic h


-- @@ L150-155 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma superCommute_ofCrAnOp_ofFieldOp_diff_stat_zero (φ : 𝓕.CrAnFieldOp) (ψ : 𝓕.FieldOp)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) : [ofCrAnOp φ, ofFieldOp ψ]ₛ = 0 := by
  rw [ofFieldOp_eq_sum, map_sum]
  refine Finset.sum_eq_zero fun x _ => superCommute_diff_statistic ?_
  simpa [crAnStatistics] using h


-- @@ L157-163 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma superCommute_anPart_ofFieldOpF_diff_grade_zero (φ ψ : 𝓕.FieldOp)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) : [anPart φ, ofFieldOp ψ]ₛ = 0 := by
  cases φ
  · simp
  all_goals
    exact superCommute_ofCrAnOp_ofFieldOp_diff_stat_zero _ _ (by simpa [crAnStatistics] using h)


-- @@ L165-167 verbatim
lemma superCommute_ofCrAnOp_ofCrAnOp_mem_center (φ φ' : 𝓕.CrAnFieldOp) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ ∈ Subalgebra.center ℂ (WickAlgebra 𝓕) :=
  ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_mem_center φ φ'


-- @@ L169-172 verbatim
lemma superCommute_ofCrAnOp_ofCrAnOp_commute (φ φ' : 𝓕.CrAnFieldOp)
    (a : WickAlgebra 𝓕) :
    a * [ofCrAnOp φ, ofCrAnOp φ']ₛ = [ofCrAnOp φ, ofCrAnOp φ']ₛ * a :=
  Subalgebra.mem_center_iff.mp (superCommute_ofCrAnOp_ofCrAnOp_mem_center φ φ') a


-- @@ L174-177 verbatim
lemma superCommute_ofCrAnOp_ofFieldOp_mem_center (φ : 𝓕.CrAnFieldOp) (φ' : 𝓕.FieldOp) :
    [ofCrAnOp φ, ofFieldOp φ']ₛ ∈ Subalgebra.center ℂ (WickAlgebra 𝓕) := by
  rw [ofFieldOp_eq_sum, map_sum]
  exact Subalgebra.sum_mem _ fun x _ => superCommute_ofCrAnOp_ofCrAnOp_mem_center φ ⟨φ', x⟩


-- @@ L179-182 verbatim
lemma superCommute_ofCrAnOp_ofFieldOp_commute (φ : 𝓕.CrAnFieldOp) (φ' : 𝓕.FieldOp)
    (a : WickAlgebra 𝓕) : a * [ofCrAnOp φ, ofFieldOp φ']ₛ =
    [ofCrAnOp φ, ofFieldOp φ']ₛ * a :=
  Subalgebra.mem_center_iff.mp (superCommute_ofCrAnOp_ofFieldOp_mem_center φ φ') a


-- @@ L184-188 verbatim
lemma superCommute_anPart_ofFieldOp_mem_center (φ φ' : 𝓕.FieldOp) :
    [anPart φ, ofFieldOp φ']ₛ ∈ Subalgebra.center ℂ (WickAlgebra 𝓕) := by
  cases φ
  · simp
  all_goals exact superCommute_ofCrAnOp_ofFieldOp_mem_center _ _


-- @@ L190-194 verbatim
/-!

### `superCommute` on different constructors.

-/


-- @@ L196-199 verbatim
lemma superCommute_ofCrAnList_ofCrAnList (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnList φs, ofCrAnList φs']ₛ =
    ofCrAnList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList (φs' ++ φs) :=
  congrArg ι (superCommuteF_ofCrAnListF_ofCrAnListF φs φs')


-- @@ L201-204 verbatim
lemma superCommute_ofCrAnOp_ofCrAnOp (φ φ' : 𝓕.CrAnFieldOp) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = ofCrAnOp φ * ofCrAnOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofCrAnOp φ' * ofCrAnOp φ :=
  congrArg ι (superCommuteF_ofCrAnOpF_ofCrAnOpF φ φ')


-- @@ L206-210 verbatim
lemma superCommute_ofCrAnList_ofFieldOpList (φcas : List 𝓕.CrAnFieldOp)
    (φs : List 𝓕.FieldOp) :
    [ofCrAnList φcas, ofFieldOpList φs]ₛ = ofCrAnList φcas * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φcas, 𝓕 |>ₛ φs) • ofFieldOpList φs * ofCrAnList φcas :=
  congrArg ι (superCommuteF_ofCrAnListF_ofFieldOpFsList φcas φs)


-- @@ L212-215 verbatim
lemma superCommute_ofFieldOpList_ofFieldOpList (φs φs' : List 𝓕.FieldOp) :
    [ofFieldOpList φs, ofFieldOpList φs']ₛ = ofFieldOpList φs * ofFieldOpList φs' -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOpList φs :=
  congrArg ι (superCommuteF_ofFieldOpListF_ofFieldOpFsList φs φs')


-- @@ L217-220 verbatim
lemma superCommute_ofFieldOp_ofFieldOpList (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [ofFieldOp φ, ofFieldOpList φs]ₛ = ofFieldOp φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * ofFieldOp φ :=
  congrArg ι (superCommuteF_ofFieldOpF_ofFieldOpFsList φ φs)


-- @@ L222-225 verbatim
lemma superCommute_ofFieldOpList_ofFieldOp (φs : List 𝓕.FieldOp) (φ : 𝓕.FieldOp) :
    [ofFieldOpList φs, ofFieldOp φ]ₛ = ofFieldOpList φs * ofFieldOp φ -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOp φ * ofFieldOpList φs :=
  congrArg ι (superCommuteF_ofFieldOpListF_ofFieldOpF φs φ)


-- @@ L227-230 verbatim
lemma superCommute_anPart_crPart (φ φ' : 𝓕.FieldOp) :
    [anPart φ, crPart φ']ₛ = anPart φ * crPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * anPart φ :=
  congrArg ι (superCommuteF_anPartF_crPartF φ φ')


-- @@ L232-235 verbatim
lemma superCommute_crPart_anPart (φ φ' : 𝓕.FieldOp) :
    [crPart φ, anPart φ']ₛ = crPart φ * anPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * crPart φ :=
  congrArg ι (superCommuteF_crPartF_anPartF φ φ')


-- @@ L237-241 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma superCommute_crPart_crPart (φ φ' : 𝓕.FieldOp) : [crPart φ, crPart φ']ₛ = 0 := by
  cases φ <;> cases φ' <;>
    simp [superCommute_create_create, crAnFieldOpToCreateAnnihilate]


-- @@ L243-247 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma superCommute_anPart_anPart (φ φ' : 𝓕.FieldOp) : [anPart φ, anPart φ']ₛ = 0 := by
  cases φ <;> cases φ' <;>
    simp [superCommute_annihilate_annihilate, crAnFieldOpToCreateAnnihilate]


-- @@ L249-252 verbatim
lemma superCommute_crPart_ofFieldOpList (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [crPart φ, ofFieldOpList φs]ₛ = crPart φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * crPart φ :=
  congrArg ι (superCommuteF_crPartF_ofFieldOpListF φ φs)


-- @@ L254-257 verbatim
lemma superCommute_anPart_ofFieldOpList (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [anPart φ, ofFieldOpList φs]ₛ = anPart φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * anPart φ :=
  congrArg ι (superCommuteF_anPartF_ofFieldOpListF φ φs)


-- @@ L259-262 verbatim
lemma superCommute_crPart_ofFieldOp (φ φ' : 𝓕.FieldOp) :
    [crPart φ, ofFieldOp φ']ₛ = crPart φ * ofFieldOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOp φ' * crPart φ :=
  congrArg ι (superCommuteF_crPartF_ofFieldOpF φ φ')


-- @@ L264-267 verbatim
lemma superCommute_anPart_ofFieldOp (φ φ' : 𝓕.FieldOp) :
    [anPart φ, ofFieldOp φ']ₛ = anPart φ * ofFieldOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOp φ' * anPart φ :=
  congrArg ι (superCommuteF_anPartF_ofFieldOpF φ φ')


-- @@ L269-276 verbatim
/-!

## Mul equal superCommute

Lemmas which rewrite a multiplication of two elements of the algebra as their commuted
multiplication with a sign plus the super commutator.

-/


-- @@ L278-282 verbatim
lemma ofCrAnList_mul_ofCrAnList_eq_superCommute (φs φs' : List 𝓕.CrAnFieldOp) :
    ofCrAnList φs * ofCrAnList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnList φs
    + [ofCrAnList φs, ofCrAnList φs']ₛ := by
  simp [superCommute_ofCrAnList_ofCrAnList, ofCrAnList_append]


-- @@ L284-289 verbatim
lemma ofCrAnOp_mul_ofCrAnList_eq_superCommute (φ : 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.CrAnFieldOp) : ofCrAnOp φ * ofCrAnList φs' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnOp φ
    + [ofCrAnOp φ, ofCrAnList φs']ₛ := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommute]
  simp


-- @@ L291-295 verbatim
lemma ofFieldOpList_mul_ofFieldOpList_eq_superCommute (φs φs' : List 𝓕.FieldOp) :
    ofFieldOpList φs * ofFieldOpList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOpList φs
    + [ofFieldOpList φs, ofFieldOpList φs']ₛ := by
  simp [superCommute_ofFieldOpList_ofFieldOpList]


-- @@ L297-300 verbatim
lemma ofFieldOp_mul_ofFieldOpList_eq_superCommute (φ : 𝓕.FieldOp) (φs' : List 𝓕.FieldOp) :
    ofFieldOp φ * ofFieldOpList φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOp φ
    + [ofFieldOp φ, ofFieldOpList φs']ₛ := by
  simp [superCommute_ofFieldOp_ofFieldOpList]


-- @@ L302-306 verbatim
lemma ofFieldOp_mul_ofFieldOp_eq_superCommute (φ φ' : 𝓕.FieldOp) :
    ofFieldOp φ * ofFieldOp φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOp φ' * ofFieldOp φ
    + [ofFieldOp φ, ofFieldOp φ']ₛ := by
  rw [← ofFieldOpList_singleton φ', ofFieldOp_mul_ofFieldOpList_eq_superCommute]
  simp


-- @@ L308-311 verbatim
lemma ofFieldOpList_mul_ofFieldOp_eq_superCommute (φs : List 𝓕.FieldOp) (φ : 𝓕.FieldOp) :
    ofFieldOpList φs * ofFieldOp φ = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOp φ * ofFieldOpList φs
    + [ofFieldOpList φs, ofFieldOp φ]ₛ := by
  simp [superCommute_ofFieldOpList_ofFieldOp]


-- @@ L313-317 verbatim
lemma ofCrAnList_mul_ofFieldOpList_eq_superCommute (φs : List 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.FieldOp) : ofCrAnList φs * ofFieldOpList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofCrAnList φs
    + [ofCrAnList φs, ofFieldOpList φs']ₛ := by
  simp [superCommute_ofCrAnList_ofFieldOpList]


-- @@ L319-322 verbatim
lemma crPart_mul_anPart_eq_superCommute (φ φ' : 𝓕.FieldOp) :
    crPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * crPart φ
    + [crPart φ, anPart φ']ₛ := by
  simp [superCommute_crPart_anPart]


-- @@ L324-327 verbatim
lemma anPart_mul_crPart_eq_superCommute (φ φ' : 𝓕.FieldOp) :
    anPart φ * crPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * anPart φ
    + [anPart φ, crPart φ']ₛ := by
  simp [superCommute_anPart_crPart]


-- @@ L329-332 verbatim
lemma crPart_mul_crPart_swap (φ φ' : 𝓕.FieldOp) :
    crPart φ * crPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * crPart φ := by
  rw [← sub_eq_zero, ← superCommute_crPart_crPart φ φ']
  exact (congrArg ι (superCommuteF_crPartF_crPartF φ φ')).symm


-- @@ L334-337 verbatim
lemma anPart_mul_anPart_swap (φ φ' : 𝓕.FieldOp) :
    anPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ := by
  rw [← sub_eq_zero, ← superCommute_anPart_anPart φ φ']
  exact (congrArg ι (superCommuteF_anPartF_anPartF φ φ')).symm


-- @@ L339-343 verbatim
/-!

## Symmetry of the super commutator.

-/


-- @@ L345-348 verbatim
lemma superCommute_ofCrAnList_ofCrAnList_symm (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnList φs, ofCrAnList φs']ₛ =
    (- 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs')) • [ofCrAnList φs', ofCrAnList φs]ₛ :=
  congrArg ι (superCommuteF_ofCrAnListF_ofCrAnListF_symm φs φs')


-- @@ L350-353 verbatim
lemma superCommute_ofCrAnOp_ofCrAnOp_symm (φ φ' : 𝓕.CrAnFieldOp) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ =
    (- 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ')) • [ofCrAnOp φ', ofCrAnOp φ]ₛ :=
  congrArg ι (superCommuteF_ofCrAnOpF_ofCrAnOpF_symm φ φ')


-- @@ L355-359 verbatim
/-!

## splitting the super commute into sums

-/


-- @@ L361-368 verbatim
lemma superCommute_ofCrAnList_ofCrAnList_eq_sum (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnList φs, ofCrAnList φs']ₛ =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
    ofCrAnList (φs'.take n) * [ofCrAnList φs, ofCrAnOp (φs'.get n)]ₛ *
    ofCrAnList (φs'.drop (n + 1)) := by
  rw [ofCrAnList, ofCrAnList, superCommute_eq_ι_superCommuteF,
    superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum, map_sum]
  rfl


-- @@ L370-377 verbatim
lemma superCommute_ofCrAnOp_ofCrAnList_eq_sum (φ : 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.CrAnFieldOp) : [ofCrAnOp φ, ofCrAnList φs']ₛ =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs'.take n) •
    [ofCrAnOp φ, ofCrAnOp (φs'.get n)]ₛ * ofCrAnList (φs'.eraseIdx n) := by
  conv_lhs => rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList_eq_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ofCrAnList_singleton, superCommute_ofCrAnOp_ofCrAnOp_commute]
  simp [mul_assoc, ← ofCrAnList_append, ← List.eraseIdx_eq_take_drop_succ, ofList_singleton]


-- @@ L379-386 verbatim
lemma superCommute_ofCrAnList_ofFieldOpList_eq_sum (φs : List 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.FieldOp) : [ofCrAnList φs, ofFieldOpList φs']ₛ =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
    ofFieldOpList (φs'.take n) * [ofCrAnList φs, ofFieldOp (φs'.get n)]ₛ *
    ofFieldOpList (φs'.drop (n + 1)) := by
  rw [ofCrAnList, ofFieldOpList, superCommute_eq_ι_superCommuteF,
    superCommuteF_ofCrAnListF_ofFieldOpListF_eq_sum, map_sum]
  rfl


-- @@ L388-395 verbatim
lemma superCommute_ofCrAnOp_ofFieldOpList_eq_sum (φ : 𝓕.CrAnFieldOp) (φs' : List 𝓕.FieldOp) :
    [ofCrAnOp φ, ofFieldOpList φs']ₛ =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs'.take n) •
    [ofCrAnOp φ, ofFieldOp (φs'.get n)]ₛ * ofFieldOpList (φs'.eraseIdx n) := by
  conv_lhs => rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofFieldOpList_eq_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ofCrAnList_singleton, superCommute_ofCrAnOp_ofFieldOp_commute]
  simp [mul_assoc, ← ofFieldOpList_append, ← List.eraseIdx_eq_take_drop_succ, ofList_singleton]


-- @@ L397-397 verbatim
end WickAlgebra

-- @@ L398-398 verbatim
end FieldSpecification
