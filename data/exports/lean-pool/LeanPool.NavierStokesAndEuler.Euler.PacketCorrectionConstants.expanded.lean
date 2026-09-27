/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds


-- @@ L11-11 verbatim
/-! Fixed source costs for the normalized packet and its smaller transport drift. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerPacketCorrectionConstants


-- @@ L20-20 verbatim
open EulerPacketCylinderField


-- @@ L22-24 verbatim
/-- Velocity, given by `C*(fixedVelocityGradeCost R H 1+fixedVelocityGradeCost R H 2+1)`. -/
def velocity (R H C : ℝ) : ℝ :=
  C*(fixedVelocityGradeCost R H 1+fixedVelocityGradeCost R H 2+1)


-- @@ L26-27 verbatim
/-- Normal, given by `C*(fixedVelocityGradeCost R H 2+2)`. -/
def normal (R H C : ℝ) : ℝ := C*(fixedVelocityGradeCost R H 2+2)


-- @@ L29-30 verbatim
/-- Drift, given by `2*(3*velocity R H C+normal R H C)`. -/
def drift (R H C : ℝ) : ℝ := 2*(3*velocity R H C+normal R H C)


-- @@ L32-37 verbatim
theorem velocity_nonneg (R H C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    0 ≤ velocity R H C := by
  have h₁ := fixedVelocityGradeCost_nonneg R H hR 1
  have h₂ := fixedVelocityGradeCost_nonneg R H hR 2
  unfold velocity
  positivity


-- @@ L39-43 verbatim
theorem normal_nonneg (R H C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    0 ≤ normal R H C := by
  have h₂ := fixedVelocityGradeCost_nonneg R H hR 2
  unfold normal
  positivity


-- @@ L45-50 verbatim
theorem drift_nonneg (R H C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) :
    0 ≤ drift R H C := by
  have hv := velocity_nonneg R H C hR hC
  have hn := normal_nonneg R H C hR hC
  unfold drift
  positivity


-- @@ L52-56 verbatim
theorem drift_div_frequency (R H C k : ℝ) (hk : 0 < k) :
    2*(3*|k⁻¹| * velocity R H C+normal R H C/k) = drift R H C/k := by
  rw [abs_of_pos (inv_pos.mpr hk)]
  unfold drift
  ring


-- @@ L58-58 verbatim
end EulerPacketCorrectionConstants
