/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Measure.RestrictedVolume
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Data.Set.Function
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.MetricSpace.Bounded


-- @@ L22-28 verbatim
/-!
# Geometry for ball Poincare estimates

Adapted from CoarseGraining (LeanIntoHomogenization, 2026) with the author's
permission.  This file keeps the bounded convex-domain and affine-segment
interfaces needed by the ball estimate while using the established CKN carriers.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace CKN


-- @@ L34-34 verbatim
open MeasureTheory


-- @@ L36-38 verbatim
/-- A coordinatewise bounded domain in the native finite-dimensional carrier. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R


-- @@ L40-47 verbatim
theorem IsBoundedDomain.isBounded {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) : Bornology.IsBounded U := by
  rcases hU with ⟨R, hR, hU⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg hR.le).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hU x hx i


-- @@ L49-51 verbatim
theorem IsBoundedDomain.volume_lt_top {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) : MeasureTheory.volume U < ⊤ :=
  hU.isBounded.measure_lt_top


-- @@ L53-57 verbatim
theorem IsBoundedDomain.isFiniteMeasure_restrict_volume
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) := by
  let _ : Fact (MeasureTheory.volume U < ⊤) := ⟨hU.volume_lt_top⟩
  infer_instance


-- @@ L59-61 verbatim
/-- The average of a scalar function over a restricted volume measure. -/
noncomputable def integralAverage {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  MeasureTheory.average (MeasureTheory.volume.restrict U) u


-- @@ L63-65 verbatim
/-- Measurable bounded domain on which the Sobolev estimates are formulated. -/
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U


-- @@ L67-67 verbatim
namespace IsSobolevRegularDomain


-- @@ L69-71 verbatim
theorem measurableSet {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MeasurableSet U :=
  hU.1


-- @@ L73-75 verbatim
theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    IsBoundedDomain U :=
  hU.2


-- @@ L77-79 verbatim
theorem volume_lt_top {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBoundedDomain.volume_lt_top


-- @@ L81-84 verbatim
theorem isFiniteMeasure_restrict_volume {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
  hU.isBoundedDomain.isFiniteMeasure_restrict_volume


-- @@ L86-86 verbatim
end IsSobolevRegularDomain


-- @@ L88-90 verbatim
/-- An open bounded convex domain in the native carrier. -/
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U


-- @@ L92-92 verbatim
namespace IsOpenBoundedConvexDomain


-- @@ L94-96 verbatim
theorem isOpen {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    IsOpen U :=
  hU.1


-- @@ L98-100 verbatim
theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : IsBoundedDomain U :=
  hU.2.1


-- @@ L102-104 verbatim
theorem convex {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    Convex ℝ U :=
  hU.2.2


-- @@ L106-108 verbatim
theorem measurableSet {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    MeasurableSet U :=
  hU.isOpen.measurableSet


-- @@ L110-113 verbatim
theorem isFiniteMeasure_restrict_volume {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
  hU.isBoundedDomain.isFiniteMeasure_restrict_volume


-- @@ L115-118 verbatim
theorem isSobolevRegularDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsSobolevRegularDomain U :=
  ⟨hU.measurableSet, hU.isBoundedDomain⟩


-- @@ L120-120 verbatim
end IsOpenBoundedConvexDomain


-- @@ L122-130 verbatim
theorem IsBoundedDomain.norm_le_choose {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) {x : Vec d} (hx : x ∈ U) :
    ‖x‖ ≤ Classical.choose hU := by
  have hRpos : 0 < Classical.choose hU := (Classical.choose_spec hU).1
  have hR : ∀ z ∈ U, ∀ i, |z i| ≤ Classical.choose hU :=
    (Classical.choose_spec hU).2
  refine (pi_norm_le_iff_of_nonneg hRpos.le).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hR x hx i


-- @@ L132-139 verbatim
theorem IsBoundedDomain.norm_sub_le_two_mul_choose {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    ‖x - y‖ ≤ 2 * Classical.choose hU := by
  calc
    ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    _ ≤ Classical.choose hU + Classical.choose hU :=
      add_le_add (hU.norm_le_choose hx) (hU.norm_le_choose hy)
    _ = 2 * Classical.choose hU := by ring


-- @@ L141-143 verbatim
/-- Translate a set by a vector in the native finite-dimensional carrier. -/
def translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) : Set (Vec d) :=
  {x | ∃ y ∈ U, x = y + z}


-- @@ L145-153 verbatim
theorem mem_translateSet_iff_sub_mem {d : ℕ} {z x : Vec d} {U : Set (Vec d)} :
    x ∈ translateSet z U ↔ x - z ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [sub_eq_add_neg, add_assoc]
  · intro hx
    refine ⟨x - z, hx, ?_⟩
    ext i
    simp [sub_eq_add_neg, add_assoc]


-- @@ L155-158 verbatim
theorem preimage_addNeg_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + -z) ⁻¹' U = translateSet z U := by
  ext x
  simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]


-- @@ L160-167 verbatim
theorem translateSet_translateSet {d : ℕ} (z w : Vec d) (U : Set (Vec d)) :
    translateSet w (translateSet z U) = translateSet (z + w) U := by
  ext x
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by simp [add_assoc]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u + z, ⟨u, hu, rfl⟩, by simp [add_assoc]⟩


-- @@ L169-172 verbatim
@[simp] theorem translateSet_zero {d : ℕ} (U : Set (Vec d)) :
    translateSet (0 : Vec d) U = U := by
  ext x
  simp [translateSet]


-- @@ L174-182 verbatim
theorem measurePreserving_subRight_restrict_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x - z)
      (MeasureTheory.volume.restrict (translateSet z U))
      (MeasureTheory.volume.restrict U) := by
  let hμ : MeasurePreserving (fun x : Vec d => x + -z)
      (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
    measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) (-z)
  simpa [preimage_addNeg_eq_translateSet (z := z) U, sub_eq_add_neg] using
    MeasurePreserving.restrict_preimage_emb hμ (Homeomorph.subRight z).measurableEmbedding U


-- @@ L184-187 verbatim
theorem image_addRight_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + z) '' U = translateSet z U := by
  ext x
  constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩


-- @@ L189-198 verbatim
theorem measurePreserving_addRight_restrict_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x + z)
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict (translateSet z U)) := by
  let hμ : MeasurePreserving (fun x : Vec d => x + z)
      (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
    measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) z
  simpa [preimage_addNeg_eq_translateSet (z := z) U, image_addRight_eq_translateSet (z := z) U,
    sub_eq_add_neg] using
    MeasurePreserving.restrict_image_emb hμ (Homeomorph.addRight z).measurableEmbedding U


-- @@ L200-207 verbatim
theorem setIntegral_comp_subRight_translateSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ x in translateSet z U, f (x - z) ∂MeasureTheory.volume =
      ∫ y in U, f y ∂MeasureTheory.volume := by
  simpa using
    (measurePreserving_subRight_restrict_translateSet (d := d) z U).integral_comp
      (Homeomorph.subRight z).measurableEmbedding f


-- @@ L209-216 verbatim
theorem setIntegral_comp_addRight_translateSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ y in U, f (y + z) ∂MeasureTheory.volume =
      ∫ x in translateSet z U, f x ∂MeasureTheory.volume := by
  simpa using
    (measurePreserving_addRight_restrict_translateSet (d := d) z U).integral_comp
      (Homeomorph.addRight z).measurableEmbedding f


-- @@ L218-232 verbatim
theorem isOpenBoundedConvexDomain_ball {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (Metric.ball x₀ r) := by
  refine ⟨Metric.isOpen_ball, ?_, convex_ball x₀ r⟩
  refine ⟨‖x₀‖ + r + 1, ?_, ?_⟩
  · positivity
  · intro x hx i
    have hx' : ‖x - x₀‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hxi : |x i| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    have hnorm : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
      calc
        ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
    linarith only [hxi, hx', hnorm]


-- @@ L234-236 verbatim
/-- The affine map which sends the unit ball to the ball of radius `r`. -/
def ballAffineMap {d : ℕ} (x₀ : Vec d) (r : ℝ) (x : Vec d) : Vec d :=
  x₀ + r • x


-- @@ L238-240 verbatim
/-- The point on the segment from `y` to `x` with parameter `t`. -/
noncomputable def segmentBlend {d : ℕ} (x : Vec d) (t : ℝ) (y : Vec d) : Vec d :=
  AffineMap.lineMap y x t


-- @@ L242-244 verbatim
@[simp] theorem segmentBlend_zero {d : ℕ} (x y : Vec d) :
    segmentBlend x 0 y = y := by
  simp [segmentBlend]


-- @@ L246-248 verbatim
@[simp] theorem segmentBlend_one {d : ℕ} (x y : Vec d) :
    segmentBlend x 1 y = x := by
  simp [segmentBlend]


-- @@ L250-252 verbatim
theorem segmentBlend_eq_add_smul_sub {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = y + t • (x - y) := by
  simpa [segmentBlend, add_comm] using (AffineMap.lineMap_apply_module' y x t)


-- @@ L254-256 verbatim
@[simp] theorem segmentBlend_self {d : ℕ} (x : Vec d) (t : ℝ) :
    segmentBlend x t x = x := by
  simp [segmentBlend]


-- @@ L258-262 verbatim
theorem segmentBlend_mem {d : ℕ} {U : Set (Vec d)} (hU : Convex ℝ U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U := by
  simpa [segmentBlend] using hU.lineMap_mem hy hx ⟨ht0, ht1⟩


-- @@ L264-268 verbatim
theorem segmentBlend_mem_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x y : Vec d}
    (hx : x ∈ U) (hy : y ∈ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U :=
  segmentBlend_mem hU.convex hx hy ht0 ht1


-- @@ L270-270 verbatim
end CKN
