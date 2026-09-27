/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.Theta
public import LeanPool.CaffarelliKohnNirenberg.Statements.Gamma
public import LeanPool.CaffarelliKohnNirenberg.Statements.Lambda


-- @@ L12-16 verbatim
/-!
# Scaling Quantity Nonneg

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open MeasureTheory

-- @@ L21-21 verbatim
open scoped ENNReal

-- @@ L22-22 verbatim
open CKN.Foundation.Parabolic



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace CKN


-- @@ L29-35 verbatim
/-- The velocity energy quantity α is nonnegative. -/
theorem alpha_nonneg (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ alpha u z r := by
  unfold alpha
  refine Real.rpow_nonneg ?_ (1 / 2 : ℝ)
  refine mul_nonneg (inv_nonneg.mpr hr) ?_
  exact ENNReal.toReal_nonneg


-- @@ L37-44 verbatim
/-- The gradient quantity β is nonnegative. -/
theorem beta_nonneg (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ beta u Du z r := by
  unfold beta
  refine Real.rpow_nonneg ?_ (1 / 2 : ℝ)
  refine mul_nonneg (inv_nonneg.mpr hr) ?_
  exact ENNReal.toReal_nonneg


-- @@ L46-52 verbatim
/-- The velocity cubic quantity γ is nonnegative. -/
theorem gamma_nonneg (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gamma u z r := by
  unfold gamma
  refine Real.rpow_nonneg ?_ (1 / 3 : ℝ)
  refine mul_nonneg (Real.rpow_nonneg hr (-2 : ℝ)) ?_
  exact ENNReal.toReal_nonneg


-- @@ L54-60 verbatim
/-- The pressure quantity δ is nonnegative. -/
theorem delta_nonneg (p : ParabolicPoint → ℝ) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ delta p z r := by
  unfold delta
  refine Real.rpow_nonneg ?_ (1 / 3 : ℝ)
  refine mul_nonneg (Real.rpow_nonneg hr (-2 : ℝ)) ?_
  exact ENNReal.toReal_nonneg


-- @@ L62-67 verbatim
/-- The force quantity λ is nonnegative. -/
theorem lambda_nonneg (q : ℝ) (f : ParabolicPoint → Vec3) (z : ParabolicPoint)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ lambda q f z r := by
  unfold lambda
  refine mul_nonneg (Real.rpow_nonneg hr (3 - 5 / q)) ?_
  refine Real.rpow_nonneg ENNReal.toReal_nonneg (1 / q : ℝ)


-- @@ L69-69 verbatim
end CKN
