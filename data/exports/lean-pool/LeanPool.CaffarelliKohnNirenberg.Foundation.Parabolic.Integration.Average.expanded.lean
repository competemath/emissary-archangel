/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith


-- @@ L16-25 verbatim
/-!
# Integration and averages on parabolic cylinders

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent module records generic average identities and
the product-measure formulas used on balls and parabolic cylinders.

The source-facing scale-invariant quantities are intentionally not defined
here.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open MeasureTheory MeasureTheory.Measure Set

-- @@ L30-30 verbatim
open scoped ENNReal


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace CKN.Foundation.Parabolic.Integration


-- @@ L36-39 verbatim
private theorem continuous_vec3EuclideanNorm_sub (x : Vec3) :
    Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
  unfold vec3EuclideanNorm
  fun_prop


-- @@ L41-49 verbatim
private theorem norm_vec3_sub_le_euclideanNorm (x y : Vec3) :
    ‖y - x‖ ≤ vec3EuclideanNorm (y - x) := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |(y - x) i| ≤ vec3EuclideanNorm (y - x)
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg ((y - x) j)) (Finset.mem_univ i)


-- @@ L51-51 verbatim
/-! ### Measures and cylinder Fubini -/


-- @@ L53-57 verbatim
/-- The volume measure on `ParabolicPoint` is the product of spatial and time volume. -/
theorem volume_parabolicPoint_eq_prod :
    (volume : Measure ParabolicPoint) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) :=
  rfl


-- @@ L59-65 verbatim
/-- A positive-radius Euclidean spatial ball has positive volume. -/
theorem volume_vec3Ball_pos {x : Vec3} {r : ℝ} (hr : 0 < r) :
    0 < volume (vec3Ball x r) := by
  have hopen : IsOpen (vec3Ball x r) := by
    unfold vec3Ball
    exact isOpen_lt (continuous_vec3EuclideanNorm_sub x) continuous_const
  exact hopen.measure_pos volume ⟨x, by simp [vec3EuclideanNorm_zero, hr]⟩


-- @@ L67-78 verbatim
/-- A Euclidean spatial ball has finite volume. -/
theorem volume_vec3Ball_lt_top {x : Vec3} {r : ℝ} :
    volume (vec3Ball x r) < ∞ := by
  have hsub : vec3Ball x r ⊆ Metric.ball x r := by
    intro y hy
    change ‖y - x‖ < r
    exact lt_of_le_of_lt (norm_vec3_sub_le_euclideanNorm x y)
      (by
        change vec3EuclideanNorm (y - x) < r at hy
        exact hy)
  exact (measure_mono hsub).trans_lt
    (measure_ball_lt_top (μ := volume) (x := x) (r := r))


-- @@ L80-85 verbatim
/-- A positive-radius parabolic cylinder has positive volume. -/
theorem volume_parabolicCylinder_pos {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    0 < volume (parabolicCylinder x t r) := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_pos (ne_of_gt (volume_vec3Ball_pos hr))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)))


-- @@ L87-93 verbatim
/-- A parabolic cylinder has finite volume. -/
theorem volume_parabolicCylinder_lt_top {x : Vec3} {t r : ℝ} :
    volume (parabolicCylinder x t r) < ∞ := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_lt_top
    (volume_vec3Ball_lt_top (x := x) (r := r))
    ENNReal.ofReal_lt_top


-- @@ L95-121 verbatim
/-- Fubini's theorem on a parabolic cylinder for Bochner-integrable functions. -/
theorem integral_parabolicCylinder {x : Vec3} {t r : ℝ}
    {g : ParabolicPoint → ℝ}
    (hg : IntegrableOn g (parabolicCylinder x t r) volume) :
    ∫ z in parabolicCylinder x t r, g z ∂volume =
      ∫ s in Ioc (t - r ^ 2) t, ∫ y in vec3Ball x r, g (y, s) := by
  rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
  change
    ∫ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) = _
  change IntegrableOn g (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) at hg
  have hgs :
      IntegrableOn (fun z : ℝ × Vec3 => g z.swap)
        (Ioc (t - r ^ 2) t ×ˢ vec3Ball x r)
        ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    exact hg.swap
  calc
    ∫ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) =
        ∫ z in Ioc (t - r ^ 2) t ×ˢ vec3Ball x r, g z.swap ∂
          (volume : Measure ℝ).prod (volume : Measure Vec3) :=
      (setIntegral_prod_swap (μ := (volume : Measure Vec3))
        (ν := (volume : Measure ℝ)) (vec3Ball x r) (Ioc (t - r ^ 2) t) g).symm
    _ = ∫ s in Ioc (t - r ^ 2) t, ∫ y in vec3Ball x r, g (y, s) := by
      rw [setIntegral_prod _ hgs]
      rfl


-- @@ L123-133 verbatim
/-- Tonelli's theorem on a parabolic cylinder for nonnegative extended-real functions. -/
theorem lintegral_parabolicCylinder {x : Vec3} {t r : ℝ}
    {g : ParabolicPoint → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict (parabolicCylinder x t r))) :
    ∫⁻ z in parabolicCylinder x t r, g z ∂volume =
      ∫⁻ s in Ioc (t - r ^ 2) t, ∫⁻ y in vec3Ball x r, g (y, s) := by
  rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
  change
    ∫⁻ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) = _
  exact setLIntegral_prod_symm g hg


-- @@ L135-135 verbatim
/-! ### Generic averages -/


-- @@ L137-143 verbatim
/-- The set average is the integral against the reciprocal real measure. -/
theorem setAverage_eq_toReal_inv_smul {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure α) (s : Set α) (f : α → E) :
    ⨍ x in s, f x ∂μ = (μ s).toReal⁻¹ • ∫ x in s, f x ∂μ := by
  simpa [MeasureTheory.measureReal_def] using
    (MeasureTheory.setAverage_eq μ f s)


-- @@ L145-152 verbatim
/-- Set averages are additive when both summands are integrable. -/
theorem setAverage_add_of_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    ⨍ x in s, (f + g) x ∂μ =
      ⨍ x in s, f x ∂μ + ⨍ x in s, g x ∂μ :=
  MeasureTheory.setAverage_add hf hg


-- @@ L154-161 verbatim
/-- Set averages commute with subtraction under integrability. -/
theorem setAverage_sub_of_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    ⨍ x in s, (f - g) x ∂μ =
      ⨍ x in s, f x ∂μ - ⨍ x in s, g x ∂μ :=
  MeasureTheory.setAverage_sub hf hg


-- @@ L163-168 verbatim
/-- The average of a constant on a positive finite-measure set is that constant. -/
theorem setAverage_const_of_pos_of_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} (hsPos : 0 < μ s) (hsTop : μ s < ∞) (c : ℝ) :
    ⨍ _x in s, c ∂μ = c := by
  exact MeasureTheory.setAverage_const hsPos.ne' hsTop.ne c


-- @@ L170-175 verbatim
/-- Set averages preserve nonnegativity almost everywhere. -/
theorem setAverage_nonneg_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f) :
    0 ≤ ⨍ x in s, f x ∂μ :=
  MeasureTheory.average_nonneg_of_ae hf


-- @@ L177-187 verbatim
/-- The norm of an average is bounded by the average of the norm. -/
theorem setAverage_norm_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (f : α → E) :
    ‖⨍ x in s, f x ∂μ‖ ≤ ⨍ x in s, ‖f x‖ ∂μ := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)]
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.norm_integral_le_integral_norm
      (μ := μ.restrict s) f)
    (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)


-- @@ L189-199 verbatim
/-- Set averages are monotone almost everywhere. -/
theorem setAverage_mono_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hfg : f ≤ᵐ[μ.restrict s] g) :
    ⨍ x in s, f x ∂μ ≤ ⨍ x in s, g x ∂μ := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  exact smul_le_smul_of_nonneg_left
    (MeasureTheory.setIntegral_mono_ae_restrict hf hg hfg)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)


-- @@ L201-201 verbatim
end CKN.Foundation.Parabolic.Integration
