/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOneSided
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays


-- @@ L11-15 verbatim
/-!
# Pressure Gradient One Sided Cell

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open MeasureTheory MeasureTheory.Measure Set Filter Metric

-- @@ L20-20 verbatim
open scoped BigOperators ENNReal NNReal Topology

-- @@ L21-21 verbatim
open CKN.Foundation.Parabolic

-- @@ L22-22 verbatim
open CKN.Foundation.Parabolic.Morrey


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace CKN.Core.Step4


-- @@ L28-29 verbatim
/-- Origin used for the normalized pressure-gradient estimate. -/
def oneSidedPressureGradientOrigin : ParabolicPoint := ((0 : Vec3), 0)


-- @@ L31-31 verbatim
/-! The cell is carried by the inner half of a symmetric parabolic ball. -/


-- @@ L33-39 verbatim
/-- Componentwise Morrey-cell bound for the gradient restricted to a smaller parabolic ball. -/
def oneSidedPressureGradientCellOutput
    (z₀ : ParabolicPoint) (R κ : ℝ) (KP : ℝ≥0∞)
    (Dp : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3, ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
    morreyCell (6 / 5 : ℝ) κ
      ((Metric.ball z₀ (R / 2)).indicator (fun w => Dp w i)) z r.1 ≤ KP


-- @@ L41-51 verbatim
/-! The old origin carrier is a consequence of the free-centre carrier.

The carrier of the pressure-gradient estimate is the backward cylinder about
the origin, not the symmetric parabolic ball of `eq:pressure-gradient-morrey`.
The hypothesis of `thm:A` is `closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I`,
and a symmetric parabolic ball about any point contains times strictly after
that point, so no symmetric ball about the origin is known to lie in the
domain. `oneSidedPressureGradientOriginCellOutput` is therefore the cell form
of `eq:pressure-gradient-morrey` with the indicator of that backward
cylinder; the Morrey seminorm is recovered as the supremum of the cells.
-/


-- @@ L53-59 verbatim
/-- Componentwise Morrey-cell bound for the gradient restricted to the normalized cylinder. -/
def oneSidedPressureGradientOriginCellOutput
    (R₁ κ : ℝ) (KP : ℝ≥0∞) (Dp : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3, ∀ z : ParabolicPoint, ∀ r : {r : ℝ // 0 < r},
    morreyCell (6 / 5 : ℝ) κ
      ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
        (fun w => Dp w i)) z r.1 ≤ KP


-- @@ L61-86 verbatim
theorem oneSidedPressureGradientOriginCellOutput_of_free_centre
    {R₁ κ : ℝ} {KP : ℝ≥0∞} {Dp : ParabolicPoint → Vec3}
    (hR₁ : 0 < R₁)
    (hfree : oneSidedPressureGradientCellOutput oneSidedPressureGradientOrigin
      (2 * R₁) κ KP Dp) :
    oneSidedPressureGradientOriginCellOutput R₁ κ KP Dp := by
  let z₀ : ParabolicPoint := oneSidedPressureGradientOrigin
  intro i z r
  have hmono : morreyCell (6 / 5 : ℝ) κ
      ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
        (fun w => Dp w i)) z r.1 ≤
      morreyCell (6 / 5 : ℝ) κ
        ((Metric.ball z₀ ((2 * R₁) / 2)).indicator
          (fun w => Dp w i)) z r.1 := by
    apply morreyCell_mono (p := (6 / 5 : ℝ)) (q := κ) (by norm_num)
    intro w hw
    by_cases hmem : w ∈ parabolicCylinder (0 : Vec3) 0 R₁
    · rw [indicator_of_mem hmem]
      have hball : w ∈ Metric.ball z₀ R₁ := by
        simpa [z₀, oneSidedPressureGradientOrigin] using
          (parabolicCylinder_subset_metricBall_sameCenter ((0 : Vec3), 0) hR₁ hmem)
      rw [show (2 * R₁) / 2 = R₁ by ring, indicator_of_mem hball]
    · rw [indicator_of_notMem hmem]
      simp only [abs_zero]
      exact abs_nonneg _
  exact hmono.trans (by simpa only [z₀] using hfree i z r)


-- @@ L88-88 verbatim
end CKN.Core.Step4
