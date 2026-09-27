/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanPool.LeanModularForms.ValenceFormula.Definitions
import Mathlib.CategoryTheory.Category.Init


-- @@ L11-26 verbatim
/-!
# Fundamental Domain Boundary – Basic Definitions

Definitions and continuity for the boundary of the standard fundamental domain
for SL₂(ℤ), both at fixed height `heightCutoff` and at variable height `H`.

## Main Definitions

* `heightCutoff` — fixed cutoff height (√3/2 + 1)
* `fdBoundary` — 5-segment boundary at fixed height
* `fdBoundaryH` — 5-segment boundary at variable height H
* `fdPartition` — interior partition points
* `fdBoundaryFullPartition` — full partition including endpoints
* `fdBoundaryHPartition` — partition for H-parameterized boundary
* `seg5QRadiusH` — q-expansion radius e^(-2πH)
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
open Complex MeasureTheory Set Filter Topology

-- @@ L31-31 verbatim
open scoped Real Interval


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-36 verbatim
/-- Height cutoff for the finite-height fundamental domain boundary. -/
def heightCutoff : ℝ := Real.sqrt 3 / 2 + 1


-- @@ L38-39 verbatim
lemma one_lt_heightCutoff : 1 < heightCutoff := by
  unfold heightCutoff; linarith [Real.sqrt_pos_of_pos (show (3 : ℝ) > 0 by norm_num)]


-- @@ L41-42 verbatim
lemma sqrt3_div2_lt_heightCutoff :
    Real.sqrt 3 / 2 < heightCutoff := by unfold heightCutoff; linarith


-- @@ L44-46 verbatim
/-- Segment 1: right vertical from (1/2 + H·i) down to ρ+1. -/
def fdBoundarySeg1 : ℝ → ℂ := fun t =>
  1 / 2 + (heightCutoff - t * (heightCutoff - Real.sqrt 3 / 2)) * I


-- @@ L48-50 verbatim
/-- Segment 2: arc from ρ+1 to i (angle π/3 → π/2). -/
def fdBoundarySeg2 : ℝ → ℂ := fun t =>
  Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)


-- @@ L52-54 verbatim
/-- Segment 3: arc from i to ρ (angle π/2 → 2π/3). -/
def fdBoundarySeg3 : ℝ → ℂ := fun t =>
  Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)


-- @@ L56-58 verbatim
/-- Segment 4: left vertical from ρ up to (-1/2 + H·i). -/
def fdBoundarySeg4 : ℝ → ℂ := fun t =>
  -1 / 2 + (Real.sqrt 3 / 2 + (t - 3) * (heightCutoff - Real.sqrt 3 / 2)) * I


-- @@ L60-62 verbatim
/-- Segment 5: horizontal from (-1/2 + H·i) to (1/2 + H·i). -/
def fdBoundarySeg5 : ℝ → ℂ := fun t =>
  (t - 9 / 2) + heightCutoff * I


-- @@ L64-83 verbatim
/-- Boundary of the standard fundamental domain at fixed
height `heightCutoff`, parameterized over [0, 5]. -/
def fdBoundary : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    1 / 2 +
      (heightCutoff - t * (heightCutoff - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    Complex.exp
      ((Real.pi / 3 +
        (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    Complex.exp
      ((Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1 / 2 +
      (Real.sqrt 3 / 2 +
        (t - 3) * (heightCutoff - Real.sqrt 3 / 2)) * I
  else
    (t - 9 / 2) + heightCutoff * I


-- @@ L85-86 verbatim
/-- Interior partition points of fdBoundary. -/
def fdPartition : Finset ℝ := {1, 2, 3, 4}


-- @@ L88-89 verbatim
/-- Full partition including endpoints. -/
def fdBoundaryFullPartition : Finset ℝ := {0, 1, 2, 3, 4, 5}


-- @@ L91-94 verbatim
lemma fdBoundary_at_zero :
    fdBoundary 0 = 1 / 2 + heightCutoff * I := by
  simp only [fdBoundary, show (0 : ℝ) ≤ 1 from by norm_num, ite_true]
  push_cast; ring


-- @@ L96-101 verbatim
lemma fdBoundary_at_one :
    fdBoundary 1 = ellipticPointRhoPlusOne := by
  simp only [fdBoundary, show (1 : ℝ) ≤ 1 from le_refl _, ite_true,
    ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
    UpperHalfPlane.coe_mk, heightCutoff]
  push_cast; ring


-- @@ L103-111 verbatim
lemma fdBoundary_at_two :
    fdBoundary 2 = ellipticPointI := by
  simp only [fdBoundary, show ¬(2 : ℝ) ≤ 1 from by norm_num,
    show (2 : ℝ) ≤ 2 from le_refl _, ite_true, ite_false]
  have h : (↑Real.pi / 3 + (↑(2 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 2) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp [ellipticPointI, ellipticPointI']


-- @@ L113-124 verbatim
lemma fdBoundary_at_three :
    fdBoundary 3 = ellipticPointRho := by
  simp only [fdBoundary, show ¬(3 : ℝ) ≤ 1 from by norm_num,
    show ¬(3 : ℝ) ≤ 2 from by norm_num, show (3 : ℝ) ≤ 3 from le_refl _,
    ite_true, ite_false]
  have h : (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  ring


-- @@ L126-131 verbatim
lemma fdBoundary_at_four :
    fdBoundary 4 = -1 / 2 + heightCutoff * I := by
  simp only [fdBoundary, show ¬(4 : ℝ) ≤ 1 from by norm_num,
    show ¬(4 : ℝ) ≤ 2 from by norm_num, show ¬(4 : ℝ) ≤ 3 from by norm_num,
    show (4 : ℝ) ≤ 4 from le_refl _, ite_true, ite_false, heightCutoff]
  push_cast; ring


-- @@ L133-138 verbatim
lemma fdBoundary_at_five :
    fdBoundary 5 = 1 / 2 + heightCutoff * I := by
  simp only [fdBoundary, show ¬(5 : ℝ) ≤ 1 from by norm_num,
    show ¬(5 : ℝ) ≤ 2 from by norm_num, show ¬(5 : ℝ) ≤ 3 from by norm_num,
    show ¬(5 : ℝ) ≤ 4 from by norm_num, ite_false]
  push_cast; ring


-- @@ L140-141 verbatim
lemma fdBoundary_closed : fdBoundary 0 = fdBoundary 5 := by
  rw [fdBoundary_at_zero, fdBoundary_at_five]


-- @@ L143-146 verbatim
/-- Segment 1 at height H: right vertical from (1/2 + H·i) down
to ρ+1. -/
def fdBoundarySeg1H (H : ℝ) : ℝ → ℂ := fun t =>
  1 / 2 + (H - t * (H - Real.sqrt 3 / 2)) * I


-- @@ L148-149 verbatim
/-- Segment 2 at height H (H-independent): arc from ρ+1 to i. -/
def fdBoundarySeg2H : ℝ → ℂ := fdBoundarySeg2


-- @@ L151-152 verbatim
/-- Segment 3 at height H (H-independent): arc from i to ρ. -/
def fdBoundarySeg3H : ℝ → ℂ := fdBoundarySeg3


-- @@ L154-156 verbatim
/-- Segment 4 at height H: left vertical from ρ up to (-1/2 + H·i). -/
def fdBoundarySeg4H (H : ℝ) : ℝ → ℂ := fun t =>
  -1 / 2 + (Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I


-- @@ L158-159 verbatim
/-- Segment 5 at height H: horizontal from (-1/2 + H·i) to (1/2 + H·i). -/
def fdBoundarySeg5H (H : ℝ) : ℝ → ℂ := fun t => (t - 9 / 2) + H * I


-- @@ L161-179 verbatim
/-- Boundary of the standard fundamental domain at variable height H,
parameterized over [0, 5]. -/
def fdBoundaryH (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    1 / 2 + (H - t * (H - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    Complex.exp
      ((Real.pi / 3 +
        (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    Complex.exp
      ((Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1 / 2 +
      (Real.sqrt 3 / 2 +
        (t - 3) * (H - Real.sqrt 3 / 2)) * I
  else
    (t - 9 / 2) + H * I


-- @@ L181-183 verbatim
/-- Non-differentiable corner points of fdBoundaryH (excluding smooth
transitions at t = 2). -/
def fdBoundaryHPartition : Finset ℝ := {1, 3, 4}


-- @@ L185-186 verbatim
/-- The q-expansion radius at height H: e^(-2πH). -/
def seg5QRadiusH (H : ℝ) : ℝ := Real.exp (-2 * Real.pi * H)


-- @@ L188-190 verbatim
theorem fdBoundary_eq_fdBoundary_H :
    fdBoundary = fdBoundaryH heightCutoff := by
  ext t; simp only [fdBoundary, fdBoundaryH, heightCutoff]


-- @@ L192-195 verbatim
lemma fdBoundary_H_at_zero (H : ℝ) :
    fdBoundaryH H 0 = 1 / 2 + H * I := by
  simp only [fdBoundaryH, show (0 : ℝ) ≤ 1 from by norm_num, ite_true]
  push_cast; ring


-- @@ L197-202 verbatim
lemma fdBoundary_H_at_one (H : ℝ) :
    fdBoundaryH H 1 = ellipticPointRhoPlusOne := by
  simp only [fdBoundaryH, show (1 : ℝ) ≤ 1 from le_refl _, ite_true,
    ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
    UpperHalfPlane.coe_mk]
  push_cast; ring


-- @@ L204-212 verbatim
lemma fdBoundary_H_at_two (H : ℝ) :
    fdBoundaryH H 2 = ellipticPointI := by
  simp only [fdBoundaryH, show ¬(2 : ℝ) ≤ 1 from by norm_num,
    show (2 : ℝ) ≤ 2 from le_refl _, ite_true, ite_false]
  have h : (↑Real.pi / 3 + (↑(2 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 2) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp [ellipticPointI, ellipticPointI']


-- @@ L214-225 verbatim
lemma fdBoundary_H_at_three (H : ℝ) :
    fdBoundaryH H 3 = ellipticPointRho := by
  simp only [fdBoundaryH, show ¬(3 : ℝ) ≤ 1 from by norm_num,
    show ¬(3 : ℝ) ≤ 2 from by norm_num, show (3 : ℝ) ≤ 3 from le_refl _,
    ite_true, ite_false]
  have h : (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  ring


-- @@ L227-232 verbatim
lemma fdBoundary_H_at_four (H : ℝ) :
    fdBoundaryH H 4 = -1 / 2 + H * I := by
  simp only [fdBoundaryH, show ¬(4 : ℝ) ≤ 1 from by norm_num,
    show ¬(4 : ℝ) ≤ 2 from by norm_num, show ¬(4 : ℝ) ≤ 3 from by norm_num,
    show (4 : ℝ) ≤ 4 from le_refl _, ite_true, ite_false]
  push_cast; ring


-- @@ L234-239 verbatim
lemma fdBoundary_H_at_five (H : ℝ) :
    fdBoundaryH H 5 = 1 / 2 + H * I := by
  simp only [fdBoundaryH, show ¬(5 : ℝ) ≤ 1 from by norm_num,
    show ¬(5 : ℝ) ≤ 2 from by norm_num, show ¬(5 : ℝ) ≤ 3 from by norm_num,
    show ¬(5 : ℝ) ≤ 4 from by norm_num, ite_false]
  push_cast; ring


-- @@ L241-242 verbatim
lemma fdBoundary_H_closed (H : ℝ) :
    fdBoundaryH H 0 = fdBoundaryH H 5 := by rw [fdBoundary_H_at_zero, fdBoundary_H_at_five]


-- @@ L244-247 verbatim
private lemma fdBoundary_H_seg1_cont (H : ℝ) :
    Continuous (fun t : ℝ => (1 : ℂ) / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I) :=
  (continuous_const.add ((continuous_const.sub
    (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const))


-- @@ L249-254 verbatim
private lemma fdBoundary_H_seg23_cont :
    Continuous (fun t : ℝ => exp
      ((↑Real.pi / 3 + (↑t - 1) *
        (↑Real.pi / 2 - ↑Real.pi / 3)) * I)) :=
  Complex.continuous_exp.comp ((continuous_const.add
    ((Complex.continuous_ofReal.sub continuous_const).mul continuous_const)).mul continuous_const)


-- @@ L256-261 verbatim
private lemma fdBoundary_H_seg23b_cont :
    Continuous (fun t : ℝ => exp
      ((↑Real.pi / 2 + (↑t - 2) *
        (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)) :=
  Complex.continuous_exp.comp ((continuous_const.add
    ((Complex.continuous_ofReal.sub continuous_const).mul continuous_const)).mul continuous_const)


-- @@ L263-268 verbatim
private lemma fdBoundary_H_seg4_cont (H : ℝ) :
    Continuous (fun t : ℝ =>
      (-1 : ℂ) / 2 + (↑(Real.sqrt 3) / 2 +
        (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I) :=
  (continuous_const.add ((continuous_const.add
    ((Complex.continuous_ofReal.sub continuous_const).mul continuous_const)).mul continuous_const))


-- @@ L270-272 verbatim
private lemma fdBoundary_H_seg5_cont (H : ℝ) :
    Continuous (fun t : ℝ => (↑t - 9 / 2 : ℂ) + ↑H * I) :=
  (Complex.continuous_ofReal.sub continuous_const).add continuous_const


-- @@ L274-277 verbatim
private def fdBoundary_H_inner34 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 4 then
    -1 / 2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I
  else (↑t - 9 / 2 : ℂ) + ↑H * I


-- @@ L279-281 verbatim
private lemma fdBoundary_H_inner34_cont (H : ℝ) : Continuous (fdBoundary_H_inner34 H) :=
  Continuous.if_le (fdBoundary_H_seg4_cont H) (fdBoundary_H_seg5_cont H)
    continuous_id continuous_const (fun t (ht : t = 4) => by subst ht; push_cast; ring)


-- @@ L283-286 verbatim
private def fdBoundary_H_inner234 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 3 then
    exp ((↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)
  else fdBoundary_H_inner34 H t


-- @@ L288-300 verbatim
private lemma fdBoundary_H_inner234_cont (H : ℝ) : Continuous (fdBoundary_H_inner234 H) := by
  apply Continuous.if_le fdBoundary_H_seg23b_cont
    (fdBoundary_H_inner34_cont H) continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 3 := by linarith
  subst this; unfold fdBoundary_H_inner34
  simp only [show (3 : ℝ) ≤ 4 from by norm_num, ite_true]
  have h : (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  push_cast; ring


-- @@ L302-305 verbatim
private def fdBoundary_H_inner1234 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 2 then
    exp ((↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)
  else fdBoundary_H_inner234 H t


-- @@ L307-316 verbatim
private lemma fdBoundary_H_inner1234_cont (H : ℝ) : Continuous (fdBoundary_H_inner1234 H) := by
  apply Continuous.if_le fdBoundary_H_seg23_cont
    (fdBoundary_H_inner234_cont H) continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 2 := by linarith
  subst this; unfold fdBoundary_H_inner234
  simp only [show (2 : ℝ) ≤ 3 from by norm_num, ite_true]
  have h1 : (↑Real.pi / 3 + (↑(2 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 2) * I := by push_cast; ring
  simp_all


-- @@ L318-323 verbatim
private lemma fdBoundary_H_eq_layered (H : ℝ) (t : ℝ) :
    fdBoundaryH H t =
      (if t ≤ 1 then 1 / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
       else fdBoundary_H_inner1234 H t) := by
  unfold fdBoundaryH fdBoundary_H_inner1234 fdBoundary_H_inner234 fdBoundary_H_inner34
  split_ifs <;> rfl


-- @@ L325-341 verbatim
theorem fdBoundary_H_continuous (H : ℝ) :
    Continuous (fdBoundaryH H) := by
  have : (fdBoundaryH H) = (fun t => if t ≤ 1 then
      1 / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
      else fdBoundary_H_inner1234 H t) := by ext t; exact fdBoundary_H_eq_layered H t
  rw [this]
  apply Continuous.if_le (fdBoundary_H_seg1_cont H) (fdBoundary_H_inner1234_cont H)
    continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 1 := by linarith
  subst this; unfold fdBoundary_H_inner1234
  simp only [show (1 : ℝ) ≤ 2 from by norm_num, ite_true]
  have h : (↑Real.pi / 3 + (↑(1 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring


-- @@ L343-343 verbatim
end
