/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem


-- @@ L10-14 verbatim
/-!
# Zero

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open MeasureTheory MeasureTheory.Measure Set Metric

-- @@ L19-19 verbatim
open scoped ENNReal NNReal Topology

-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic



-- @@ L23-27 verbatim
/-! # Parabolic Morrey quantities of the zero function

This module records the cylinder and ball power integrals, Morrey cells and Morrey
seminorms of the zero function.
-/


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace CKN.Foundation.Parabolic.Morrey


-- @@ L33-37 verbatim
/-- The cylinder power integral of the zero function vanishes at every centre and radius. -/
theorem cylinderPowerIntegral_zero {p : ℝ} (hp : 0 < p) (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral p (fun _ => (0 : ℝ)) z r = 0 := by
  unfold cylinderPowerIntegral
  simp only [abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp, lintegral_zero]


-- @@ L39-43 verbatim
/-- The ball power integral of the zero function vanishes at every centre and radius. -/
theorem ballPowerIntegral_zero {p : ℝ} (hp : 0 < p) (z : ParabolicPoint) (r : ℝ) :
    ballPowerIntegral p (fun _ => (0 : ℝ)) z r = 0 := by
  unfold ballPowerIntegral
  simp only [abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp, lintegral_zero]


-- @@ L45-52 verbatim
/-- The Morrey cell quantity of the zero function vanishes at every centre and radius. -/
theorem morreyCell_zero {p q : ℝ} (hp : 0 < p) (z : ParabolicPoint) (r : ℝ) :
    morreyCell p q (fun _ => (0 : ℝ)) z r = 0 := by
  unfold morreyCell
  rw [cylinderPowerIntegral_zero hp z r]
  have hone_div_pos : 0 < 1 / p := one_div_pos.mpr hp
  rw [ENNReal.zero_rpow_of_pos hone_div_pos]
  simp


-- @@ L54-61 verbatim
/-- The Morrey ball cell quantity of the zero function vanishes at every centre and radius. -/
theorem morreyBallCell_zero {p q : ℝ} (hp : 0 < p) (z : ParabolicPoint) (r : ℝ) :
    morreyBallCell p q (fun _ => (0 : ℝ)) z r = 0 := by
  unfold morreyBallCell
  rw [ballPowerIntegral_zero hp z r]
  have hone_div_pos : 0 < 1 / p := one_div_pos.mpr hp
  rw [ENNReal.zero_rpow_of_pos hone_div_pos]
  simp


-- @@ L63-70 verbatim
/-- The Morrey norm of the zero function vanishes identically. -/
theorem morreyNorm_zero {p q : ℝ} (hp : 0 < p) :
    morreyNorm p q (fun _ => (0 : ℝ)) = 0 := by
  unfold morreyNorm
  apply le_antisymm
  · refine iSup_le fun z => iSup_le fun r => ?_
    rw [morreyCell_zero hp z r.1]
  · simp


-- @@ L72-79 verbatim
/-- The Morrey ball norm of the zero function vanishes identically. -/
theorem morreyBallNorm_zero {p q : ℝ} (hp : 0 < p) :
    morreyBallNorm p q (fun _ => (0 : ℝ)) = 0 := by
  unfold morreyBallNorm
  apply le_antisymm
  · refine iSup_le fun z => iSup_le fun r => ?_
    rw [morreyBallCell_zero hp z r.1]
  · simp


-- @@ L81-81 verbatim
end CKN.Foundation.Parabolic.Morrey
