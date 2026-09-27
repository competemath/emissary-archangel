/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevCoefficientPressure
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder


-- @@ L13-13 verbatim
/-! The literal transport and order-zero quadratic operators in the Euler correction equation. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerCorrectionOperators


-- @@ L22-25 verbatim
open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
    EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevL2Product EulerSobolevTransport
  EulerSobolevCoefficientPressure EulerVectorCylinder EulerMetricTransport

-- @@ L26-26 verbatim
open scoped Topology ContDiff ENNReal


-- @@ L28-29 verbatim
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]


-- @@ L31-33 verbatim
/-- Postcompose an actual continuous bilinear map by an actual bounded operator. -/
def postcompose (A : Y →L[ℝ] Y) (B : X →L[ℝ] X →L[ℝ] Y) : X →L[ℝ] X →L[ℝ] Y :=
  (ContinuousLinearMap.compL ℝ X Y Y A).comp B


-- @@ L35-36 verbatim
@[simp] theorem postcompose_apply (A : Y →L[ℝ] Y) (B : X →L[ℝ] X →L[ℝ] Y) (u v : X) :
    postcompose A B u v = A (B u v) := rfl


-- @@ L38-40 verbatim
/-- Linearization of a quadratic term about the actual approximate solution. -/
def linearize (B : X →L[ℝ] X →L[ℝ] Y) (C : X →L[ℝ] Y) (z : X) : X →L[ℝ] Y :=
  B z + B.flip z + C


-- @@ L42-43 verbatim
@[simp] theorem linearize_apply (B : X →L[ℝ] X →L[ℝ] Y) (C : X →L[ℝ] Y) (z e : X) :
    linearize B C z e = B z e + B e z + C e := rfl


-- @@ L45-49 verbatim
/-- The correction source is exactly the difference of the full quadratic equations. -/
theorem quadratic_correction_identity (B : X →L[ℝ] X →L[ℝ] Y) (C : X →L[ℝ] Y) (z e : X) :
    C (z+e) + B (z+e) (z+e) - (C z + B z z) = linearize B C z e + B e e := by
  simp only [linearize_apply, map_add, add_apply]
  abel


-- @@ L51-58 verbatim
/-- Continuous data give continuous linearized operators. -/
theorem linearize_continuous {T : Type*} [TopologicalSpace T]
    (B : T → X →L[ℝ] X →L[ℝ] Y) (C : T → X →L[ℝ] Y) (z : T → X)
    (hB : Continuous B) (hC : Continuous C) (hz : Continuous z) :
    Continuous (fun t => linearize (B t) (C t) (z t)) := by
  have hflip : Continuous (fun t => (B t).flip) := (ContinuousLinearMap.flipₗᵢ ℝ X X
      Y).continuous.comp hB
  exact ((hB.clm_apply hz).add (hflip.clm_apply hz)).add hC


-- @@ L60-60 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L62-64 verbatim
/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance sobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance

-- @@ L65-67 verbatim
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance sobolevRealSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

-- @@ L68-72 verbatim
/-- Cache the standard `SeminormedAddCommGroup (SobolevSpace period (q+1) →L[ℝ] SobolevSpace
period (q+1) →L[ℝ] SobolevSpace period q)` instance to shorten typeclass synthesis. -/
local instance sobolevBilinearGroup (q : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q) :=
        inferInstance


-- @@ L74-78 verbatim
/-- The actual derivative-free coordinate product on the input Sobolev level. -/
def coordinateProduct {q : ℕ} (hq : 6 ≤ q) (i : Fin 3) :
    SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q :=
  (productHqBilinear period hq (coordinate 3 i) (coordinate_norm_le 3 i)).bilinearComp
    (truncateOperator period q) (truncateOperator period q)


-- @@ L80-84 verbatim
@[simp] theorem coordinateProduct_apply {q : ℕ} (hq : 6 ≤ q) (i : Fin 3)
    (u v : SobolevSpace period (q + 1)) :
    coordinateProduct period hq i u v = productHq period hq (coordinate 3 i) (coordinate_norm_le 3
        i)
      (truncateOperator period q u) (truncateOperator period q v) := rfl


-- @@ L86-90 verbatim
/-- The actual order-zero quadratic coefficient terms, Σ Cᵢ(uᵢ v). -/
def algebraicBilinear {q : ℕ} (hq : 6 ≤ q)
    (C : Fin 3 → SobolevSpace period q →L[ℝ] SobolevSpace period q) :
    SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q :=
  ∑ i : Fin 3, postcompose (C i) (coordinateProduct period hq i)


-- @@ L92-96 verbatim
theorem algebraicBilinear_apply {q : ℕ} (hq : 6 ≤ q)
    (C : Fin 3 → SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (u v : SobolevSpace period (q + 1)) :
    algebraicBilinear period hq C u v = ∑ i : Fin 3, C i (coordinateProduct period hq i u v) := by
  simp only [algebraicBilinear, sum_apply, postcompose_apply]


-- @@ L98-103 verbatim
/-- The full bilinear nonlinearity of the transformed Euler equation. -/
def eulerBilinear {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C : Fin 3 → SobolevSpace period q →L[ℝ] SobolevSpace period q) :
    SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q :=
  transportBilinear period hq L hL + algebraicBilinear period hq C


-- @@ L105-140 verbatim
/-- Actual coefficient multiplication gives precisely the classical order-zero quadratic field. -/
theorem algebraicBilinear_ae {q : ℕ} (hq : 6 ≤ q)
    (C : Fin 3 → SmoothCoefficient period) (K : ∀ i, CoefficientJet period standardDirection q (C
        i))
    (u v : SobolevSpace period (q + 1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g) :
    (value period (algebraicBilinear period hq (fun i => coefficientSobolevOperator period (K i)) u
        v) :
      LiftDomain period → Vector3) =ᵐ[liftMeasure period]
        (fun x => ∑ i : Fin 3, f x i • (C i).coefficient x (g x)) := by
  rw [algebraicBilinear_apply]
  change ((valueOperator period q) (∑ i : Fin 3, _) : LiftDomain period → Vector3) =ᵐ[liftMeasure
      period] _
  rw [map_sum]
  have hi (i : Fin 3) :
      (value period (coefficientSobolevOperator period (K i) (coordinateProduct period hq i u v)) :
        LiftDomain period → Vector3) =ᵐ[liftMeasure period]
          (fun x => f x i • (C i).coefficient x (g x)) := by
    rw [coefficientSobolevOperator_value]
    have hpr := productHq_ae period hq (coordinate 3 i) (coordinate_norm_le 3 i)
      (truncateOperator period q u) (truncateOperator period q v)
    filter_upwards [(C i).operator_ae (value period (coordinateProduct period hq i u v)), hpr, hu,
        hv]
      with x h1 h2 h3 h4
    rw [h1]
    change (C i).coefficient x (value period (productHq period hq (coordinate 3 i)
        (coordinate_norm_le 3 i)
      (truncateOperator period q u) (truncateOperator period q v)) x) = _
    rw [h2, value_truncateOperator, value_truncateOperator, h3, h4, map_smul]
    rfl
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 => value period
    (coefficientSobolevOperator period (K i) (coordinateProduct period hq i u v))), ae_all_iff.mpr
        hi] with x hx hall
  simp only [Finset.sum_apply] at hx
  exact hx.trans (Finset.sum_congr rfl (fun i _ => hall i))


-- @@ L142-142 verbatim
end EulerCorrectionOperators
