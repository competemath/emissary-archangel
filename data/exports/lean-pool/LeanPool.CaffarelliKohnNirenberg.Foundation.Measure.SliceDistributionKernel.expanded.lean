/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic
public import Mathlib.Topology.MetricSpace.Thickening


-- @@ L11-21 verbatim
/-!
# Translated mollifiers as spatial test functions

The slice form of a distributional identity is obtained by testing the
space-time identity against the countable family of mollifier bumps centred at
the points of a countable dense set.  This file records the elementary
properties of a single translated bump `x ↦ mollifier ε (x - y)`: it is smooth,
compactly supported with topological support the closed ball `closedBall y ε`,
and its coordinate derivative is the translate of the coordinate derivative of
the kernel.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
open MeasureTheory Metric



-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace CKN


-- @@ L32-40 verbatim
/-- The mollifier vanishes outside its closed ball of radius `ε`. -/
theorem mollifier_eq_zero_of_lt_norm {d : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Vec d}
    (hz : ε < ‖z‖) : mollifier (d := d) ε hε z = 0 := by
  have hts : tsupport (mollifier (d := d) ε hε) = closedBall (0 : Vec d) ε :=
    (standardMollifier (d := d) ε hε).tsupport_normed_eq
  have hz' : z ∉ tsupport (mollifier (d := d) ε hε) := by
    rw [hts, mem_closedBall, dist_zero_right]
    exact not_le.2 hz
  exact image_eq_zero_of_notMem_tsupport hz'


-- @@ L42-53 verbatim
/-- Each coordinate derivative of the mollifier vanishes outside the closed ball
of radius `ε`. -/
theorem fderiv_mollifier_apply_eq_zero {d : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Vec d}
    (hz : ε < ‖z‖) (i : Fin d) :
    (fderiv ℝ (mollifier (d := d) ε hε) z) (basisVec i) = 0 := by
  have hts : tsupport (mollifier (d := d) ε hε) = closedBall (0 : Vec d) ε :=
    (standardMollifier (d := d) ε hε).tsupport_normed_eq
  have hz' : z ∉ tsupport (mollifier (d := d) ε hε) := by
    rw [hts, mem_closedBall, dist_zero_right]
    exact not_le.2 hz
  rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hz']
  simp


-- @@ L55-61 verbatim
/-- Each coordinate derivative of the mollifier is continuous. -/
theorem continuous_fderiv_mollifier_apply {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (i : Fin d) :
    Continuous fun z : Vec d => (fderiv ℝ (mollifier (d := d) ε hε) z) (basisVec i) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (mollifier (d := d) ε hε) :=
    mollifier_contDiff (d := d) hε
  simpa using (hk.continuous_fderiv (by simp)).clm_apply continuous_const


-- @@ L63-66 verbatim
/-- The translated mollifier is smooth. -/
theorem contDiff_mollifier_sub {d : ℕ} {ε : ℝ} (hε : 0 < ε) (y : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => mollifier (d := d) ε hε (x - y) :=
  (mollifier_contDiff (d := d) hε).comp (contDiff_id.sub contDiff_const)


-- @@ L68-72 verbatim
/-- The translated mollifier has compact support. -/
theorem hasCompactSupport_mollifier_sub {d : ℕ} {ε : ℝ} (hε : 0 < ε) (y : Vec d) :
    HasCompactSupport fun x : Vec d => mollifier (d := d) ε hε (x - y) := by
  simpa [Function.comp_def] using
    (mollifier_hasCompactSupport (d := d) hε).comp_homeomorph (Homeomorph.subRight y)


-- @@ L74-86 verbatim
/-- The topological support of the translated mollifier is the closed ball of
radius `ε` about the translation point. -/
theorem tsupport_mollifier_sub_eq {d : ℕ} {ε : ℝ} (hε : 0 < ε) (y : Vec d) :
    tsupport (fun x : Vec d => mollifier (d := d) ε hε (x - y)) = closedBall y ε := by
  have hts : tsupport (fun x : Vec d => mollifier (d := d) ε hε (x - y))
      = (Homeomorph.subRight y) ⁻¹' tsupport (mollifier (d := d) ε hε) := by
    simpa [Function.comp_def] using
      tsupport_comp_eq_preimage (mollifier (d := d) ε hε) (Homeomorph.subRight y)
  have hk : tsupport (mollifier (d := d) ε hε) = closedBall (0 : Vec d) ε :=
    (standardMollifier (d := d) ε hε).tsupport_normed_eq
  rw [hts, hk]
  ext x
  simp [Homeomorph.subRight, mem_closedBall, dist_eq_norm]


-- @@ L88-101 verbatim
/-- The coordinate derivative of a translated mollifier is the translate of the
coordinate derivative of the mollifier. -/
theorem fderiv_mollifier_sub_apply {d : ℕ} {ε : ℝ} (hε : 0 < ε) (y x : Vec d)
    (i : Fin d) :
    (fderiv ℝ (fun z : Vec d => mollifier (d := d) ε hε (z - y)) x) (basisVec i)
      = (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (basisVec i) := by
  have hinner : HasFDerivAt (fun z : Vec d => z - y)
      (ContinuousLinearMap.id ℝ (Vec d)) x := (hasFDerivAt_id x).sub_const y
  have houter : HasFDerivAt (mollifier (d := d) ε hε)
      (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (x - y) :=
    ((mollifier_contDiff (d := d) (n := 1) hε).differentiable (by simp) (x - y)).hasFDerivAt
  have hcomp := houter.comp x hinner
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using
    congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hcomp.fderiv


-- @@ L103-103 verbatim
end CKN


-- @@ L105-105 verbatim
end
