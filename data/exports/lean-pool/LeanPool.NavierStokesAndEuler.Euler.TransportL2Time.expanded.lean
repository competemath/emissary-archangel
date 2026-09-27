/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevMetricTransport


-- @@ L11-11 verbatim
/-! Genuine time-continuous transport operators at the H¹→L² metric-energy level. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerTransportL2Time


-- @@ L20-22 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerSobolevMetricTransport
  EulerSobolevL2Product EulerSobolevTransport

-- @@ L23-23 verbatim
open scoped Topology


-- @@ L25-25 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L27-29 verbatim
/-- A named local normed-group instance for the actual Sobolev scale. -/
local instance transportL2Group (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance


-- @@ L31-32 verbatim
/-- A named local real normed-space instance for the actual Sobolev scale. -/
local instance transportL2Space (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance


-- @@ L34-39 verbatim
/-- Actual lifted transport as a bounded bilinear map Hq×H¹→L² for q≥3. -/
def transportL2Bilinear {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3) :
    SobolevSpace period q →L[ℝ] SobolevSpace period 1 →L[ℝ] LiftL2 period :=
  ∑ i : Fin 4, (scalarProductBilinear period hq (velocityComponents κ m i)).bilinearComp
    (ContinuousLinearMap.id ℝ (SobolevSpace period q))
    ((valueOperator period 0).comp (derivativeOperator period 0 i))


-- @@ L41-50 verbatim
/-- This actual bilinear map is exactly the transport operator used in the proved metric
cancellation. -/
theorem transportL2Bilinear_apply {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3)
    (z : SobolevSpace period q) : transportL2Bilinear period hq κ m z = transportOperator period hq
        κ m z := by
  apply ContinuousLinearMap.ext
  intro e
  simp only [transportL2Bilinear, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, transportOperator,
    scalarProductBilinear_apply]


-- @@ L52-56 verbatim
/-- A continuous actual velocity determines the time-continuous H¹→L² transport operator path. -/
def transportL2Path {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3) (T : ℝ)
    (z : C(Icc (0 : ℝ) T, SobolevSpace period q)) :
    C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period) :=
  (transportL2Bilinear period hq κ m).compLeftContinuous ℝ (Icc (0 : ℝ) T) z


-- @@ L58-62 verbatim
/-- The actual transport path has exactly the pointwise metric-energy operator. -/
theorem transportL2Path_apply {q : ℕ} (hq : 3 ≤ q) (κ : ℝ) (m : Vector3) (T : ℝ)
    (z : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : Icc (0 : ℝ) T) :
    transportL2Path period hq κ m T z t = transportOperator period hq κ m (z t) :=
  transportL2Bilinear_apply period hq κ m (z t)


-- @@ L64-64 verbatim
end EulerTransportL2Time
