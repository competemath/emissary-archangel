/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Exponents
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.IntegralBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge


-- @@ L13-17 verbatim
/-!
# Near

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
section


-- @@ L23-27 verbatim
/-!
# Morrey

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L29-29 verbatim
open scoped BigOperators ENNReal NNReal Topology


-- @@ L31-31 verbatim
open MeasureTheory MeasureTheory.Measure Set



-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace CKN.Core.HeatPotential


-- @@ L38-38 verbatim
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey


-- @@ L40-72 verbatim
lemma morrey_cylinder_lp_bound {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ)
    {f : ParabolicPoint → ℝ} (_ : AEMeasurable f volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    (cylinderPowerIntegral P f z r) ^ (1 / P) ≤
      (ENNReal.ofReal r) ^ (5 * (1 / P - 1 / θ)) * morreyNorm P θ f := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hθ0 : 0 < θ := lt_of_lt_of_le hP0 hPθ
  let A : ℝ≥0∞ := ENNReal.ofReal r
  let d : ℝ := 5 * (1 / P - 1 / θ)
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hcell : morreyCell P θ f z r ≤ morreyNorm P θ f := by
    unfold morreyNorm
    exact le_iSup_of_le z
      (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell P θ f z s.1)
        ⟨r, hr⟩)
  have hexp : -(5 * (1 - P / θ) / P) = -d := by
    dsimp [d]
    field_simp [hP0.ne', hθ0.ne']
  have hcell' : A ^ (-d) * (cylinderPowerIntegral P f z r) ^ (1 / P) ≤
      morreyNorm P θ f := by
    simpa only [morreyCell, A, hexp] using hcell
  have hcancel : A ^ d * A ^ (-d) = 1 := by
    rw [← ENNReal.rpow_add _ _ hA0 hAtop, add_neg_cancel, ENNReal.rpow_zero]
  calc
    (cylinderPowerIntegral P f z r) ^ (1 / P) =
        A ^ d * (A ^ (-d) * (cylinderPowerIntegral P f z r) ^ (1 / P)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ A ^ d * morreyNorm P θ f := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_left hcell' (A ^ d))
    _ = (ENNReal.ofReal r) ^ (5 * (1 / P - 1 / θ)) * morreyNorm P θ f := by
      rfl


-- @@ L74-74 verbatim
end CKN.Core.HeatPotential

-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
end


-- @@ L79-79 verbatim
open scoped BigOperators ENNReal NNReal Topology


-- @@ L81-81 verbatim
open MeasureTheory MeasureTheory.Measure Set Metric



-- @@ L84-84 verbatim
noncomputable section


-- @@ L86-86 verbatim
namespace CKN.Core.HeatPotential


-- @@ L88-88 verbatim
open CKN.Foundation.Heat CKN.Foundation.Parabolic

-- @@ L89-89 verbatim
open CKN.Foundation.Parabolic.Morrey


-- @@ L91-95 verbatim
/-!
The source block used for the local part of a heat potential.  The radius is
written with the gauge `parabolicRho₂`, whose time component is symmetric;
this is the geometry needed for a genuine parabolic metric ball.
-/

-- @@ L96-98 verbatim
/-- Near region separated from the far shells at parabolic distance `64 * r`. -/
def heatPotentialNearSet (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  {v | parabolicRho₂ z v < (64 : ℝ) * r}





-- @@ L103-103 verbatim
end CKN.Core.HeatPotential
