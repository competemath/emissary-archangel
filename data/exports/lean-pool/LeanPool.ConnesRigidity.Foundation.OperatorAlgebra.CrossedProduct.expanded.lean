/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 13496-14516.
Modifications: extracted the generic crossed-product Hilbert model, removed
paper-specific instances, and changed local vocabulary. Paper: §3. See
the upstream PORT_MAP.md.
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import LeanPool.ConnesRigidity.Core


-- @@ L20-22 verbatim
/-!
The crossed product component of the Connes rigidity formalization.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace Connes

-- @@ L27-27 verbatim
namespace CrossedProduct


-- @@ L29-29 verbatim
open MeasureTheory

-- @@ L30-30 verbatim
open scoped NNReal ENNReal


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
universe u v w x


-- @@ L36-54 verbatim
/-- A probability Haar action is the base input for a crossed-product model.
Paper: §3. -/
structure HaarProbabilityAction
    (K : Type u) (Ω : Type v)
    [Group K] [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω] where
  /--
  The `measure` component of `HaarProbabilityAction`.
  -/
  measure : Measure Ω
  haar : Measure.IsAddHaarMeasure measure
  probability : IsProbabilityMeasure measure
  /--
  The `action` component of `HaarProbabilityAction`.
  -/
  action : K →* Equiv.Perm Ω
  action_add :
    ∀ (k : K) (z z' : Ω), action k (z + z') = action k z + action k z'
  action_preserves_measure :
    ∀ k : K, MeasurePreserving (action k : Ω → Ω) measure measure


-- @@ L56-73 verbatim
/-- An equivariant Haar equivalence transports a crossed-product base.
Paper: §3. -/
structure EquivariantHaarEquiv
    {K : Type u} {Ω : Type v} {Ξ : Type w}
    [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]
    (X : HaarProbabilityAction K Ω)
    (Y : HaarProbabilityAction K Ξ) where
  /--
  The `toMeasurableEquiv` component of `EquivariantHaarEquiv`.
  -/
  toMeasurableEquiv : Ω ≃ᵐ Ξ
  measure_preserving : MeasurePreserving toMeasurableEquiv X.measure Y.measure
  equivariant :
    ∀ (k : K) (z : Ω),
      toMeasurableEquiv (X.action k z) =
        Y.action k (toMeasurableEquiv z)


-- @@ L75-75 verbatim
namespace EquivariantHaarEquiv


-- @@ L77-77 verbatim
variable {K : Type u} {Ω : Type v} {Ξ : Type w} {Ζ : Type x}

-- @@ L78-78 verbatim
variable [Group K]

-- @@ L79-79 verbatim
variable [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]

-- @@ L80-80 verbatim
variable [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]

-- @@ L81-84 verbatim
variable [AddCommGroup Ζ] [TopologicalSpace Ζ] [MeasurableSpace Ζ]

/- The identity equivalence is an equivariant Haar equivalence. Paper: §3.
-/

-- @@ L85-93 verbatim
/--
The `refl` construction used in the Connes rigidity formalization.
-/
def refl (X : HaarProbabilityAction K Ω) : EquivariantHaarEquiv X X where
  toMeasurableEquiv := MeasurableEquiv.refl Ω
  measure_preserving := MeasurePreserving.id X.measure
  equivariant := by
    intro k z
    rfl


-- @@ L95-109 verbatim
/-- Equivariant Haar equivalences are closed under inverse. Paper: §3.
-/
def symm
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    EquivariantHaarEquiv Y X where
  toMeasurableEquiv := e.toMeasurableEquiv.symm
  measure_preserving :=
    MeasurePreserving.symm e.toMeasurableEquiv e.measure_preserving
  equivariant := by
    intro k z
    apply e.toMeasurableEquiv.injective
    simpa only [MeasurableEquiv.apply_symm_apply] using
      (e.equivariant k (e.toMeasurableEquiv.symm z)).symm


-- @@ L111-128 verbatim
/-- Equivariant Haar equivalences are closed under composition. Paper: §3.
-/
def trans
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    {Z : HaarProbabilityAction K Ζ}
    (e : EquivariantHaarEquiv X Y)
    (f : EquivariantHaarEquiv Y Z) :
    EquivariantHaarEquiv X Z where
  toMeasurableEquiv := e.toMeasurableEquiv.trans f.toMeasurableEquiv
  measure_preserving := e.measure_preserving.trans f.measure_preserving
  equivariant := by
    intro k z
    change
      f.toMeasurableEquiv (e.toMeasurableEquiv (X.action k z)) =
        Z.action k (f.toMeasurableEquiv (e.toMeasurableEquiv z))
    rw [e.equivariant k z,
      f.equivariant k (e.toMeasurableEquiv z)]


-- @@ L130-130 verbatim
end EquivariantHaarEquiv


-- @@ L132-138 verbatim
/-- The base and crossed-product Hilbert carriers. Paper: §3.
-/
abbrev crossedBaseHilbert
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) :=
  MeasureTheory.Lp ℂ 2 X.measure


-- @@ L140-147 verbatim
/--
The `crossedHilbert` construction used in the Connes rigidity formalization.
-/
abbrev crossedHilbert
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) :=
  lp (fun _ : K ↦ crossedBaseHilbert X) 2


-- @@ L149-156 verbatim
/--
The `crossedCoefficient` construction used in the Connes rigidity formalization.
-/
abbrev crossedCoefficient
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) :=
  MeasureTheory.Lp ℂ ⊤ X.measure


-- @@ L158-167 verbatim
/-- Multiplication on the base Hilbert space supplies crossed multipliers.
Paper: §3.
-/
def crossedBaseMultiplier
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω)
    (f : crossedCoefficient X) :
    crossedBaseHilbert X →L[ℂ] crossedBaseHilbert X :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL X.measure ⊤ 2 2 f


-- @@ L169-181 verbatim
/-- The multiplier has its pointwise representative almost everywhere.
Paper: §3. -/
theorem crossedBaseMultiplier_apply_ae
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω)
    (f : crossedCoefficient X) (ξ : crossedBaseHilbert X) :
    crossedBaseMultiplier X f ξ =ᵐ[X.measure] fun z ↦ f z * ξ z :=
  ContinuousLinearMap.coeFn_holder (ContinuousLinearMap.mul ℂ ℂ) f ξ

/- Fiberwise continuous operators act on the crossed Hilbert space.
Paper: §3.
-/

-- @@ L182-216 verbatim
/--
The `crossedFiberwiseOperator` construction used in the Connes rigidity formalization.
-/
def crossedFiberwiseOperator
    {K : Type u} {H : Type v}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : H →L[ℂ] H) :
    lp (fun _ : K ↦ H) 2 →L[ℂ] lp (fun _ : K ↦ H) 2 := by
  let F : lp (fun _ : K ↦ H) 2 →ₗ[ℂ] lp (fun _ : K ↦ H) 2 :=
    { toFun := fun ξ ↦
        ⟨fun k ↦ T (ξ k), by
          apply ((lp.memℓp ξ).const_smul (‖T‖ : ℂ)).mono'
          intro k
          change ‖T (ξ k)‖ ≤ ‖(‖T‖ : ℂ) • ξ k‖
          simpa only [Complex.coe_smul, norm_smul, norm_norm] using
            T.le_opNorm (ξ k)⟩
      map_add' := by
        intro ξ η
        ext k
        exact map_add T (ξ k) (η k)
      map_smul' := by
        intro c ξ
        ext k
        exact map_smul T c (ξ k) }
  exact F.mkContinuous ‖T‖ (by
    intro ξ
    calc
      ‖F ξ‖ ≤ ‖(‖T‖ : ℂ) • ξ‖ := lp.norm_mono (by norm_num) (by
        intro k
        change ‖T (ξ k)‖ ≤ ‖(‖T‖ : ℂ) • ξ k‖
        simpa only [Complex.coe_smul, norm_smul, norm_norm] using
          T.le_opNorm (ξ k))
      _ = ‖T‖ * ‖ξ‖ := by
        rw [lp.norm_const_smul (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
        simp only [Complex.norm_real, norm_norm])


-- @@ L218-222 verbatim
@[simp] theorem crossedFiberwiseOperator_apply
    {K : Type u} {H : Type v}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : H →L[ℂ] H) (ξ : lp (fun _ : K ↦ H) 2) (k : K) :
    crossedFiberwiseOperator T ξ k = T (ξ k) := rfl


-- @@ L224-233 verbatim
/-- Base multipliers are lifted fiberwise to the crossed Hilbert space.
Paper: §3.
-/
def crossedMultiplier
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω)
    (f : crossedCoefficient X) :
    crossedHilbert X →L[ℂ] crossedHilbert X :=
  crossedFiberwiseOperator (crossedBaseMultiplier X f)


-- @@ L235-240 verbatim
@[simp] theorem crossedMultiplier_apply
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω)
    (f : crossedCoefficient X) (ξ : crossedHilbert X) (k : K) :
    crossedMultiplier X f ξ k = crossedBaseMultiplier X f (ξ k) := rfl


-- @@ L242-289 verbatim
/-- A fiberwise linear isometry is lifted to the crossed Hilbert space.
Paper: §3.
-/
def crossedFiberwiseEquiv
    {K : Type u} {H : Type v} {J : Type w}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup J] [NormedSpace ℂ J]
    (e : H ≃ₗᵢ[ℂ] J) :
    lp (fun _ : K ↦ H) 2 ≃ₗᵢ[ℂ] lp (fun _ : K ↦ J) 2 where
  toLinearEquiv :=
    { toFun := fun ξ ↦
        ⟨fun k ↦ e (ξ k), by
          change Memℓp (fun k ↦ e (ξ k)) 2
          rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
          simpa only [norm_map, ENNReal.toReal_ofNat, Real.rpow_ofNat] using
            (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)⟩
      invFun := fun ξ ↦
        ⟨fun k ↦ e.symm (ξ k), by
          change Memℓp (fun k ↦ e.symm (ξ k)) 2
          rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
          simpa only [norm_map, ENNReal.toReal_ofNat, Real.rpow_ofNat] using
            (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)⟩
      left_inv := by
        intro ξ
        ext k
        exact e.symm_apply_apply (ξ k)
      right_inv := by
        intro ξ
        ext k
        exact e.apply_symm_apply (ξ k)
      map_add' := by
        intro ξ η
        ext k
        exact map_add e (ξ k) (η k)
      map_smul' := by
        intro c ξ
        ext k
        exact map_smul e c (ξ k) }
  norm_map' := by
    intro ξ
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change
      (∑' k : K, ‖e (ξ k)‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) =
        (∑' k : K, ‖ξ k‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal)
    simp only [LinearIsometryEquiv.norm_map]


-- @@ L291-296 verbatim
@[simp] theorem crossedFiberwiseEquiv_apply
    {K : Type u} {H : Type v} {J : Type w}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup J] [NormedSpace ℂ J]
    (e : H ≃ₗᵢ[ℂ] J) (ξ : lp (fun _ : K ↦ H) 2) (k : K) :
    crossedFiberwiseEquiv e ξ k = e (ξ k) := rfl


-- @@ L298-331 verbatim
/-- The crossed Hilbert space reindexes under a group equivalence. Paper: §3.
-/
def crossedIndexEquiv
    {K : Type u} {H : Type v}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (e : K ≃ K) :
    lp (fun _ : K ↦ H) 2 ≃ₗᵢ[ℂ] lp (fun _ : K ↦ H) 2 where
  toLinearEquiv :=
    { toFun := fun ξ ↦
        ⟨fun k ↦ ξ (e.symm k), memℓp_reindex e (by norm_num) ξ⟩
      invFun := fun ξ ↦
        ⟨fun k ↦ ξ (e k), memℓp_reindex e.symm (by norm_num) ξ⟩
      left_inv := by
        intro ξ
        ext k
        exact congrArg ξ (e.symm_apply_apply k)
      right_inv := by
        intro ξ
        ext k
        exact congrArg ξ (e.apply_symm_apply k)
      map_add' := by
        intro ξ η
        ext k
        rfl
      map_smul' := by
        intro c ξ
        ext k
        rfl }
  norm_map' := by
    intro ξ
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun k ↦ ‖ξ k‖ ^ (2 : ℝ≥0∞).toReal)


-- @@ L333-337 verbatim
@[simp] theorem crossedIndexEquiv_apply
    {K : Type u} {H : Type v}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (e : K ≃ K) (ξ : lp (fun _ : K ↦ H) 2) (k : K) :
    crossedIndexEquiv e ξ k = ξ (e.symm k) := rfl


-- @@ L339-383 verbatim
/-- The base Haar equivalence acts fiberwise on the crossed Hilbert space.
Paper: §3.
-/
def crossedBaseHaarEquiv
    {K : Type u} {Ω : Type v} {Ξ : Type w} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]
    {X : HaarProbabilityAction K Ω} {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    crossedBaseHilbert X ≃ₗᵢ[ℂ] crossedBaseHilbert Y where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving e.toMeasurableEquiv.symm
        (EquivariantHaarEquiv.symm e).measure_preserving
      invFun := Lp.compMeasurePreserving e.toMeasurableEquiv
        e.measure_preserving
      left_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (EquivariantHaarEquiv.symm e).measure_preserving
          e.measure_preserving
        simpa only [EquivariantHaarEquiv.symm, Function.comp_def,
          MeasurableEquiv.symm_apply_apply,
          show (fun z : Ω ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
          AddMonoidHom.id_apply] using h.symm
      right_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          e.measure_preserving
          (EquivariantHaarEquiv.symm e).measure_preserving
        simpa only [EquivariantHaarEquiv.symm, Function.comp_def,
          MeasurableEquiv.apply_symm_apply,
          show (fun z : Ξ ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
          AddMonoidHom.id_apply] using h.symm
      map_add' := by
        intro f g
        exact map_add
          (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
            (EquivariantHaarEquiv.symm e).measure_preserving) f g
      map_smul' := by
        intro c f
        exact map_smul
          (Lp.compMeasurePreservingₗ ℂ e.toMeasurableEquiv.symm
            (EquivariantHaarEquiv.symm e).measure_preserving) c f }
  norm_map' := fun f ↦ Lp.norm_compMeasurePreserving f
    (EquivariantHaarEquiv.symm e).measure_preserving


-- @@ L385-393 verbatim
@[simp] theorem crossedBaseHaarEquiv_apply
    {K : Type u} {Ω : Type v} {Ξ : Type w} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]
    {X : HaarProbabilityAction K Ω} {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) (f : crossedBaseHilbert X) :
    crossedBaseHaarEquiv e f =
      Lp.compMeasurePreserving e.toMeasurableEquiv.symm
        (EquivariantHaarEquiv.symm e).measure_preserving f := rfl


-- @@ L395-435 verbatim
/-- The crossed-product group unitary implements the action on the base.
Paper: §3.
-/
def crossedActionL2Equiv
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) (k : K) :
    crossedBaseHilbert X ≃ₗᵢ[ℂ] crossedBaseHilbert X where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving (X.action k⁻¹)
        (X.action_preserves_measure k⁻¹)
      invFun := Lp.compMeasurePreserving (X.action k)
        (X.action_preserves_measure k)
      left_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (X.action_preserves_measure k⁻¹)
          (X.action_preserves_measure k)
        simpa only [map_inv, Equiv.Perm.coe_inv, Function.comp_def,
          Equiv.symm_apply_apply, show (fun z : Ω ↦ z) = id from rfl,
          Lp.compMeasurePreserving_id, AddMonoidHom.id_apply] using h.symm
      right_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (X.action_preserves_measure k)
          (X.action_preserves_measure k⁻¹)
        simpa only [map_inv, Equiv.Perm.coe_inv, Function.comp_def,
          Equiv.apply_symm_apply, show (fun z : Ω ↦ z) = id from rfl,
          Lp.compMeasurePreserving_id, AddMonoidHom.id_apply] using h.symm
      map_add' := by
        intro f g
        exact map_add
          (Lp.compMeasurePreserving (X.action k⁻¹)
            (X.action_preserves_measure k⁻¹)) f g
      map_smul' := by
        intro c f
        exact map_smul
          (Lp.compMeasurePreservingₗ ℂ (X.action k⁻¹)
            (X.action_preserves_measure k⁻¹)) c f }
  norm_map' := fun f ↦ Lp.norm_compMeasurePreserving f
    (X.action_preserves_measure k⁻¹)


-- @@ L437-444 verbatim
@[simp] theorem crossedActionL2Equiv_apply
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) (k : K)
    (f : crossedBaseHilbert X) :
    crossedActionL2Equiv X k f =
      Lp.compMeasurePreserving (X.action k⁻¹)
        (X.action_preserves_measure k⁻¹) f := rfl


-- @@ L446-455 verbatim
/-- The crossed-product group unitary on the indexed Hilbert space.
Paper: §3.
-/
def crossedGroupUnitary
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) (k : K) :
    crossedHilbert X ≃ₗᵢ[ℂ] crossedHilbert X :=
  (crossedIndexEquiv (Equiv.mulLeft k)).trans
    (crossedFiberwiseEquiv (crossedActionL2Equiv X k))


-- @@ L457-463 verbatim
@[simp] theorem crossedGroupUnitary_apply
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) (k : K)
    (ξ : crossedHilbert X) (h : K) :
    crossedGroupUnitary X k ξ h =
      crossedActionL2Equiv X k (ξ (k⁻¹ * h)) := rfl


-- @@ L465-475 verbatim
/-- The standard two-family crossed-product generator set.
Paper: §3.
-/
def crossedGeneratorSet
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) :
    Set (crossedHilbert X →L[ℂ] crossedHilbert X) :=
  Set.range (crossedMultiplier X) ∪
    Set.range fun k : K ↦
      (crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap


-- @@ L477-486 verbatim
/-- The crossed-product vacuum is the constant base vector at the identity.
Paper: §3.
-/
def crossedVacuum
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) : crossedHilbert X := by
  classical
  let _ : IsProbabilityMeasure X.measure := X.probability
  exact lp.single 2 (1 : K) (Lp.const 2 X.measure (1 : ℂ))


-- @@ L488-501 verbatim
/-- The crossed-product model packages its generated algebra and vacuum state.
Paper: §3. -/
structure CrossedProductModel
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) where
  /--
  The `algebra` component of `CrossedProductModel`.
  -/
  algebra : VonNeumannAlgebra (crossedHilbert X)
  /--
  The `trace` component of `CrossedProductModel`.
  -/
  trace : algebra.toStarSubalgebra → ℂ


-- @@ L503-514 verbatim
/--
The `crossedProductModel` construction used in the Connes rigidity formalization.
-/
def crossedProductModel
    {K : Type u} {Ω : Type v} [Group K]
    [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (X : HaarProbabilityAction K Ω) :
    CrossedProductModel X where
  algebra := vonNeumannClosure (crossedGeneratorSet X)
  trace := fun T ↦ inner ℂ (crossedVacuum X)
    ((T : crossedHilbert X →L[ℂ] crossedHilbert X)
      (crossedVacuum X))


-- @@ L516-516 verbatim
end

-- @@ L517-517 verbatim
end CrossedProduct

-- @@ L518-518 verbatim
end Connes
