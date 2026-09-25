/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SpeedOfLight
public import Physlib.Relativity.Tensors.RealTensor.Vector.Tensorial
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Physlib.SpaceAndTime.Time.InnerProductSpace
public import Physlib.Meta.Informal.Basic

-- @@ L13-66 verbatim
/-!
# Spacetime

## i. Overview

In this file we define the type `SpaceTime d` which corresponds to `d+1` dimensional
spacetime. This is equipped with an instance of the action of a Lorentz group,
corresponding to Minkowski-spacetime.

It is defined through `Lorentz.Vector d`, and carries the tensorial instance,
allowing it to be used in tensorial expressions.

## ii. Key results

- `SpaceTime d` : The type corresponding to `d+1` dimensional spacetime.
- `toTimeAndSpace` : A continuous linear equivalence between `SpaceTime d`
  and `Time × Space d`.

## iii. Table of contents

- A. The definition of `SpaceTime d`
- C. Continuous linear map to coordinates
- D. Measures on `SpaceTime d`
  - D.1. Instance of a measurable space
  - D.2. Instance of a borel space
  - D.4. Instance of a measure space
  - D.5. Volume measure is positive on non-empty open sets
  - D.6. Volume measure is a finite measure on compact sets
  - D.7. Volume measure is an additive Haar measure
- B. Maps to and from `Space` and `Time`
  - B.1. Linear map to `Space d`
    - B.1.1. Explicit expansion of map to space
    - B.1.2. Equivariance of the to space under rotations
  - B.2. Linear map to `Time`
    - B.2.1. Explicit expansion of map to time in terms of coordinates
  - B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`
    - B.3.1. Derivative of `toTimeAndSpace`
    - B.3.2. Derivative of the inverse of `toTimeAndSpace`
    - B.3.3. `toTimeAndSpace` acting on spatial basis vectors
    - B.3.4. `toTimeAndSpace` acting on the temporal basis vectors
  - B.4. Time space basis
    - B.4.1. Elements of the basis
    - B.4.2. Equivalence adjusting time basis vector
    - B.4.3. Determinant of the equivalence
    - B.4.4. Time space basis expressed in terms of the Lorentz basis
    - B.4.5. The additive Haar measure associated to the time space basis
  - B.5. Integrals over `SpaceTime d`
    - B.5.1. Measure preserving property of `toTimeAndSpace.symm`
    - B.5.2. Integrals over `SpaceTime d` expressed as integrals over `Time` and `Space d`

## iv. References

* None.
-/


-- @@ L68-68 verbatim
@[expose] public section


-- @@ L70-70 verbatim
noncomputable section


-- @@ L72-76 verbatim
/-!

## A. The definition of `SpaceTime d`

-/


-- @@ L78-78 verbatim
TODO "SpaceTime should be refactored into a structure, or similar, to prevent casting."


-- @@ L80-83 verbatim
/-- `SpaceTime d` corresponds to `d+1` dimensional space-time.
  This is equipped with an instance of the action of a Lorentz group,
  corresponding to Minkowski-spacetime. -/
abbrev SpaceTime (d : ℕ := 3) := Lorentz.Vector d


-- @@ L85-85 verbatim
namespace SpaceTime


-- @@ L87-87 verbatim
open Manifold

-- @@ L88-88 verbatim
open Matrix

-- @@ L89-89 verbatim
open Complex

-- @@ L90-90 verbatim
open ComplexConjugate

-- @@ L91-91 verbatim
open TensorSpecies


-- @@ L93-97 verbatim
/-!

## C. Continuous linear map to coordinates

-/


-- @@ L99-108 verbatim
/-- For a given `μ : Fin (1 + d)` `coord μ p` is the coordinate of
  `p` in the direction `μ`.

  This is denoted `𝔁 μ p`, where `𝔁` is typed with `\MCx`. -/
def coord {d : ℕ} (μ : Fin (1 + d)) : SpaceTime d →ₗ[ℝ] ℝ where
  toFun x := x (finSumFinEquiv.symm μ)
  map_add' x1 x2 := by
    simp
  map_smul' c x := by
    simp


-- @@ L110-111 verbatim
@[inherit_doc coord]
scoped notation "𝔁" => coord


-- @@ L113-115 verbatim
lemma coord_apply {d : ℕ} (μ : Fin (1 + d)) (y : SpaceTime d) :
    𝔁 μ y = y (finSumFinEquiv.symm μ) := by
  rfl


-- @@ L117-125 verbatim
/-- The continuous linear map from a point in space time to one of its coordinates. -/
def coordCLM (μ : Fin 1 ⊕ Fin d) : SpaceTime d →L[ℝ] ℝ where
  toFun x := x μ
  map_add' x1 x2 := by
    simp
  map_smul' c x := by
    simp
  cont := by
    fun_prop


-- @@ L127-131 verbatim
/-!

## D. Measures on `SpaceTime d`

-/

-- @@ L132-132 verbatim
open MeasureTheory


-- @@ L134-138 verbatim
/-!

### D.1. Instance of a measurable space

-/


-- @@ L140-140 verbatim
instance {d : ℕ} : MeasurableSpace (SpaceTime d) := borel (SpaceTime d)


-- @@ L142-146 verbatim
/-!

### D.2. Instance of a borel space

-/


-- @@ L148-149 verbatim
instance {d : ℕ} : BorelSpace (SpaceTime d) where
  measurable_eq := by rfl


-- @@ L151-155 verbatim
/-!

### D.4. Instance of a measure space

-/


-- @@ L157-158 verbatim
instance {d : ℕ} : MeasureSpace (SpaceTime d) where
  volume := Lorentz.Vector.basis.addHaar


-- @@ L160-164 verbatim
/-!

### D.5. Volume measure is positive on non-empty open sets

-/


-- @@ L166-167 verbatim
instance {d : ℕ} : (volume (α := SpaceTime d)).IsOpenPosMeasure :=
  inferInstanceAs ((Lorentz.Vector.basis.addHaar).IsOpenPosMeasure)


-- @@ L169-173 verbatim
/-!

### D.6. Volume measure is a finite measure on compact sets

-/


-- @@ L175-176 verbatim
instance {d : ℕ} : IsFiniteMeasureOnCompacts (volume (α := SpaceTime d)) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (Lorentz.Vector.basis.addHaar))


-- @@ L178-182 verbatim
/-!

### D.7. Volume measure is an additive Haar measure

-/


-- @@ L184-185 verbatim
instance {d : ℕ} : Measure.IsAddHaarMeasure (volume (α := SpaceTime d)) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (Lorentz.Vector.basis.addHaar))


-- @@ L187-191 verbatim
/-!

## B. Maps to and from `Space` and `Time`

-/


-- @@ L193-197 verbatim
/-!

### B.1. Linear map to `Space d`

-/


-- @@ L199-209 verbatim
/-- The space part of spacetime. -/
def space {d : ℕ} : SpaceTime d →L[ℝ] Space d where
  toFun x := ⟨Lorentz.Vector.spatialPart x⟩
  map_add' x1 x2 := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp
  cont := by
    fun_prop


-- @@ L211-215 verbatim
/-!

#### B.1.1. Explicit expansion of map to space

-/


-- @@ L217-220 verbatim
lemma space_toCoord_symm {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    space f = fun i => f (Sum.inr i) := by
  funext i
  simp [space]


-- @@ L222-226 verbatim
/-!

#### B.1.2. Equivariance of the to space under rotations

-/


-- @@ L228-228 verbatim
open realLorentzTensor

-- @@ L229-229 verbatim
open Tensor


-- @@ L231-234 expanded
/-- The function `space` is equivariant with respect to rotations. -/
def space_equivariant : InformalLemma where
  deps := [``space]
  tag := "7MTYX"


-- @@ L236-240 verbatim
/-!

### B.2. Linear map to `Time`

-/


-- @@ L242-252 verbatim
/-- The time part of spacetime. -/
def time {d : ℕ} (c : SpeedOfLight := 1) : SpaceTime d →ₗ[ℝ] Time where
  toFun x := ⟨Lorentz.Vector.timeComponent x / c⟩
  map_add' x1 x2 := by
    ext
    simp [Lorentz.Vector.timeComponent]
    grind
  map_smul' c x := by
    ext
    simp [Lorentz.Vector.timeComponent]
    grind


-- @@ L254-258 verbatim
/-!

#### B.2.1. Explicit expansion of map to time in terms of coordinates

-/


-- @@ L260-263 verbatim
@[simp]
lemma time_val_toCoord_symm {d : ℕ} (c : SpeedOfLight) (f : Fin 1 ⊕ Fin d → ℝ) :
    (time c f).val = f (Sum.inl 0) / c := by
  simp [time, Lorentz.Vector.timeComponent]


-- @@ L265-269 verbatim
/-!

### B.3. `toTimeAndSpace`: Continuous linear equivalence to `Time × Space d`

-/


-- @@ L271-301 verbatim
/-- A continuous linear equivalence between `SpaceTime d` and
  `Time × Space d`. -/
def toTimeAndSpace {d : ℕ} (c : SpeedOfLight := 1) : SpaceTime d ≃L[ℝ] Time × Space d :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun x := (x.time c, x.space)
    invFun tx := (fun i =>
      match i with
      | Sum.inl _ => c * tx.1.val
      | Sum.inr i => tx.2 i)
    left_inv x := by
      simp only [time, LinearMap.coe_mk, AddHom.coe_mk, space]
      funext i
      match i with
      | Sum.inl 0 =>
        simp [Lorentz.Vector.timeComponent]
        field_simp
      | Sum.inr i => simp
    right_inv tx := by
      simp only [time, Lorentz.Vector.timeComponent, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk,
        ne_eq, SpeedOfLight.val_ne_zero, not_false_eq_true, mul_div_cancel_left₀, space,
        ContinuousLinearMap.coe_mk']
    map_add' x y := by
      simp only [Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · ext
        simp
      ext i
      simp
    map_smul' := by
      simp
  }


-- @@ L303-306 verbatim
@[simp]
lemma toTimeAndSpace_symm_apply_time_space {d : ℕ} {c : SpeedOfLight} (x : SpaceTime d) :
    (toTimeAndSpace c).symm (x.time c, x.space) = x :=
  (toTimeAndSpace c).left_inv x


-- @@ L308-312 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma space_toTimeAndSpace_symm {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    ((toTimeAndSpace c).symm (t, s)).space = s := by
  simp [space, toTimeAndSpace]


-- @@ L314-318 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma time_toTimeAndSpace_symm {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    ((toTimeAndSpace c).symm (t, s)).time c = t := by
  simp [time, toTimeAndSpace]


-- @@ L320-322 verbatim
@[simp]
lemma toTimeAndSpace_symm_apply_inl {d : ℕ} {c : SpeedOfLight} (t : Time) (s : Space d) :
    (toTimeAndSpace c).symm (t, s) (Sum.inl 0) = c * t := by rfl


-- @@ L324-327 verbatim
@[simp]
lemma toTimeAndSpace_symm_apply_inr {d : ℕ} {c : SpeedOfLight} (t : Time) (x : Space d)
    (i : Fin d) :
    (toTimeAndSpace c).symm (t, x) (Sum.inr i) = x i := by rfl

-- @@ L328-332 verbatim
/-!

#### B.3.1. Derivative of `toTimeAndSpace`

-/


-- @@ L334-337 verbatim
@[simp]
lemma toTimeAndSpace_fderiv {d : ℕ} {c : SpeedOfLight} (x : SpaceTime d) :
    fderiv ℝ (toTimeAndSpace c) x = (toTimeAndSpace c).toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]


-- @@ L339-343 verbatim
/-!

#### B.3.2. Derivative of the inverse of `toTimeAndSpace`

-/


-- @@ L345-348 verbatim
@[simp]
lemma toTimeAndSpace_symm_fderiv {d : ℕ} {c : SpeedOfLight} (x : Time × Space d) :
    fderiv ℝ (toTimeAndSpace c).symm x = (toTimeAndSpace c).symm.toContinuousLinearMap := by
  rw [ContinuousLinearEquiv.fderiv]


-- @@ L350-354 verbatim
/-!

#### B.3.3. `toTimeAndSpace` acting on spatial basis vectors

-/

-- @@ L355-362 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma toTimeAndSpace_basis_inr {d : ℕ} {c : SpeedOfLight} (i : Fin d) :
    toTimeAndSpace c (Lorentz.Vector.basis (Sum.inr i))
    = (0, Space.basis i) := by
  refine Prod.ext ?_ ?_
  · simp [toTimeAndSpace, time]
  · ext j
    simp [toTimeAndSpace, space, Space.basis_apply]


-- @@ L364-368 verbatim
/-!

#### B.3.4. `toTimeAndSpace` acting on the temporal basis vectors

-/


-- @@ L370-376 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma toTimeAndSpace_basis_inl {d : ℕ} {c : SpeedOfLight} :
    toTimeAndSpace (d := d) c (Lorentz.Vector.basis (Sum.inl 0)) = (⟨1/c.val⟩, 0) := by
  refine Prod.ext ?_ ?_
  · simp [toTimeAndSpace, time]
  · ext j
    simp [toTimeAndSpace, space]


-- @@ L378-381 verbatim
lemma toTimeAndSpace_basis_inl' {d : ℕ} {c : SpeedOfLight} :
    toTimeAndSpace (d := d) c (Lorentz.Vector.basis (Sum.inl 0)) = (1/c.val) • (1, 0) := by
  rw [toTimeAndSpace_basis_inl]
  simp [Prod.ext_iff, Time.ext_iff, Time.smul_real_val, Time.one_val]


-- @@ L383-387 verbatim
/-!

### B.4. Time space basis

-/


-- @@ L389-394 verbatim
/-- The basis of `SpaceTime` where the first component is `(c, 0, 0, ...)` instead
of `(1, 0, 0, ....).`-/
def timeSpaceBasis {d : ℕ} (c : SpeedOfLight := 1) :
    Module.Basis (Fin 1 ⊕ Fin d) ℝ (SpaceTime d) where
  repr := (toTimeAndSpace (d := d) c).toLinearEquiv.trans <|
      (Time.basis.toBasis.prod (Space.basis (d := d)).toBasis).repr


-- @@ L396-400 verbatim
/-!

#### B.4.1. Elements of the basis

-/


-- @@ L402-408 verbatim
@[simp]
lemma timeSpaceBasis_apply_inl {d : ℕ} (c : SpeedOfLight) :
    timeSpaceBasis (d := d) c (Sum.inl 0) = c.val • Lorentz.Vector.basis (Sum.inl 0) := by
  simp [timeSpaceBasis]
  apply (toTimeAndSpace (d := d) c).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, map_smul, toTimeAndSpace_basis_inl]
  ext <;> simp


-- @@ L410-415 verbatim
@[simp]
lemma timeSpaceBasis_apply_inr {d : ℕ} (c : SpeedOfLight) (i : Fin d) :
    timeSpaceBasis (d := d) c (Sum.inr i) = Lorentz.Vector.basis (Sum.inr i) := by
  simp [timeSpaceBasis]
  apply (toTimeAndSpace (d := d) c).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, toTimeAndSpace_basis_inr]


-- @@ L417-421 verbatim
/-!

#### B.4.2. Equivalence adjusting time basis vector

-/


-- @@ L423-486 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The equivalence on of `SpaceTime` taking `(1, 0, 0, ...)` to
of `(c, 0, 0, ....)` and keeping all other components the same. -/
def timeSpaceBasisEquiv {d : ℕ} (c : SpeedOfLight) :
    SpaceTime d ≃L[ℝ] SpaceTime d where
  toFun x := fun μ =>
    match μ with
    | Sum.inl 0 => c.val * x (Sum.inl 0)
    | Sum.inr i => x (Sum.inr i)
  invFun x := fun μ =>
    match μ with
    | Sum.inl 0 => (1 / c.val) * x (Sum.inl 0)
    | Sum.inr i => x (Sum.inr i)
  left_inv x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      field_simp
    | Sum.inr i =>
      rfl
  right_inv x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      field_simp
    | Sum.inr i =>
      rfl
  map_add' x y := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue, Lorentz.Vector.apply_add]
      ring
    | Sum.inr i =>
      simp
  map_smul' c x := by
    funext μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue, Lorentz.Vector.apply_smul, RingHom.id_apply]
      ring
    | Sum.inr i =>
      simp
  continuous_invFun := by
    simp only [one_div, Fin.isValue]
    apply Lorentz.Vector.continuous_of_apply
    intro μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue]
      fun_prop
    | Sum.inr i =>
      simp only
      fun_prop
  continuous_toFun := by
    apply Lorentz.Vector.continuous_of_apply
    intro μ
    match μ with
    | Sum.inl 0 =>
      simp only [Fin.isValue]
      fun_prop
    | Sum.inr i =>
      simp only
      fun_prop


-- @@ L488-492 verbatim
/-!

#### B.4.3. Determinant of the equivalence

-/


-- @@ L494-506 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma det_timeSpaceBasisEquiv {d : ℕ} (c : SpeedOfLight) :
    (timeSpaceBasisEquiv (d := d) c).det = c.val := by
  rw [@LinearEquiv.coe_det]
  let e := toTimeAndSpace (d := d) c
  trans LinearMap.det (e.toLinearMap ∘ₗ (timeSpaceBasisEquiv (d := d) c).toLinearMap ∘ₗ
    e.symm.toLinearMap)
  · simp only [ContinuousLinearEquiv.toLinearEquiv_symm, LinearMap.det_conj]
  have h1 : e.toLinearMap ∘ₗ (timeSpaceBasisEquiv (d := d) c).toLinearMap ∘ₗ
    e.symm.toLinearMap = (c.val • LinearMap.id).prodMap LinearMap.id := by
    ext tx <;> simp [e, timeSpaceBasisEquiv, toTimeAndSpace, space]
  rw [h1, LinearMap.det_prodMap]
  simp


-- @@ L508-512 verbatim
/-!

#### B.4.4. Time space basis expressed in terms of the Lorentz basis

-/


-- @@ L514-527 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma timeSpaceBasis_eq_map_basis {d : ℕ} (c : SpeedOfLight) :
    timeSpaceBasis (d := d) c =
    Module.Basis.map (Lorentz.Vector.basis (d := d)) (timeSpaceBasisEquiv c).toLinearEquiv := by
  ext1 μ
  match μ with
  | Sum.inl 0 =>
    simp [timeSpaceBasisEquiv]
    funext ν
    rcases ν with _ | j <;> simp [Fin.fin_one_eq_zero]
  | Sum.inr i =>
    simp [timeSpaceBasisEquiv]
    funext ν
    rcases ν with _ | j <;> simp [Fin.fin_one_eq_zero]


-- @@ L529-533 verbatim
/-!

#### B.4.5. The additive Haar measure associated to the time space basis

-/


-- @@ L535-545 verbatim
lemma timeSpaceBasis_addHaar {d : ℕ} (c : SpeedOfLight := 1) :
    (timeSpaceBasis (d := d) c).addHaar = (ENNReal.ofReal (c⁻¹)) • volume := by
  rw [timeSpaceBasis_eq_map_basis c, ← Module.Basis.map_addHaar]
  have h1 := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (f := (timeSpaceBasisEquiv (d := d) c).toLinearMap) (μ := Lorentz.Vector.basis.addHaar)
    (by simp [← LinearEquiv.coe_det, det_timeSpaceBasisEquiv])
  simp at h1
  rw [h1]
  simp [← LinearEquiv.coe_det, det_timeSpaceBasisEquiv]
  congr
  simp


-- @@ L547-550 verbatim
/-!
### B.5. Integrals over `SpaceTime d`

-/


-- @@ L552-556 verbatim
/-!

#### B.5.1. Measure preserving property of `toTimeAndSpace.symm`

-/


-- @@ L558-558 verbatim
open MeasureTheory

-- @@ L559-566 verbatim
lemma toTimeAndSpace_symm_measurePreserving {d : ℕ} (c : SpeedOfLight) :
    MeasurePreserving (toTimeAndSpace c).symm (volume.prod (volume (α := Space d)))
    (ENNReal.ofReal c⁻¹ • volume) := by
  refine { measurable := ?_, map_eq := ?_ }
  · fun_prop
  rw [Space.volume_eq_addHaar, Time.volume_eq_basis_addHaar, ← Module.Basis.prod_addHaar,
    Module.Basis.map_addHaar, ← timeSpaceBasis_addHaar c]
  rfl


-- @@ L568-572 verbatim
/-!

#### B.5.2. Integrals over `SpaceTime d` expressed as integrals over `Time` and `Space d`

-/


-- @@ L574-586 verbatim
lemma spaceTime_integral_eq_time_space_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M) :
    ∫ x : SpaceTime d, f x ∂(volume) =
    c.val • ∫ tx : Time × Space d, f ((toTimeAndSpace c).symm tx) ∂(volume.prod volume) := by
  symm
  have h1 : ∫ tx : Time × Space d, f ((toTimeAndSpace c).symm tx) ∂(volume.prod volume)
    = ∫ x : SpaceTime d, f x ∂((ENNReal.ofReal (c⁻¹)) • volume) := by
    apply MeasureTheory.MeasurePreserving.integral_comp
    · exact toTimeAndSpace_symm_measurePreserving c
    · exact (toTimeAndSpace c).symm.toHomeomorph.measurableEmbedding
  rw [h1]
  simp


-- @@ L588-599 verbatim
lemma spaceTime_integrable_iff_space_time_integrable {M} [NormedAddCommGroup M]
    {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M) :
    Integrable f volume ↔ Integrable (f ∘ ((toTimeAndSpace c).symm)) (volume.prod volume) := by
  symm
  trans Integrable f (ENNReal.ofReal (c⁻¹) • volume); swap
  · rw [MeasureTheory.integrable_smul_measure]
    · simp
    · simp
  apply MeasureTheory.MeasurePreserving.integrable_comp_emb
  · exact toTimeAndSpace_symm_measurePreserving c
  · exact (toTimeAndSpace c).symm.toHomeomorph.measurableEmbedding


-- @@ L601-608 verbatim
lemma spaceTime_integral_eq_time_integral_space_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M)
    (h : Integrable f volume) :
    ∫ x : SpaceTime d, f x =
    c.val • ∫ t : Time, ∫ x : Space d, f ((toTimeAndSpace c).symm (t, x)) := by
  rw [spaceTime_integral_eq_time_space_integral, MeasureTheory.integral_prod]
  exact (spaceTime_integrable_iff_space_time_integrable c f).mp h


-- @@ L610-617 verbatim
lemma spaceTime_integral_eq_space_integral_time_integral {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} (c : SpeedOfLight)
    (f : SpaceTime d → M)
    (h : Integrable f volume) :
    ∫ x : SpaceTime d, f x =
    c.val • ∫ x : Space d, ∫ t : Time, f ((toTimeAndSpace c).symm (t, x)) := by
  rw [spaceTime_integral_eq_time_space_integral, MeasureTheory.integral_prod_symm]
  exact (spaceTime_integrable_iff_space_time_integrable c f).mp h


-- @@ L619-619 verbatim
end SpaceTime


-- @@ L621-621 verbatim
end
