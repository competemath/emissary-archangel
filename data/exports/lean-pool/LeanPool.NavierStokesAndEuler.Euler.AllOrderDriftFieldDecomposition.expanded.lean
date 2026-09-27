/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedExactLifted
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftGraph


-- @@ L13-15 verbatim
/-! Pointwise decomposition of the actual corrected velocity and pressure.
The identities concern the constructed exact packet, not an arbitrary
pair satisfying an energy bound. -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace EulerAllOrderDriftCorrection


-- @@ L24-24 verbatim
open Set EulerAllOrderCorrectionData EulerLiftedGradientSpace


-- @@ L26-27 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A)


-- @@ L29-30 verbatim
theorem Budget.correctedFieldTower_eq :
    B.correctedFieldTower P = A.approximation.add (B.fieldTower P) := rfl


-- @@ L32-33 verbatim
theorem Budget.correctedPressureTower_eq (R : ApproximationResidual P hT A) :
    B.correctedPressureTower P R = R.pressure.add (B.pressureTower P) := rfl


-- @@ L35-39 verbatim
theorem Budget.correctedFieldTower_pointField (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (B.correctedFieldTower P).pointField t x =
      A.approximation.pointField t x + B.pointField P t x := by
  rw [B.correctedFieldTower_eq P, FieldTower.add_pointField,
    B.correctionTower_pointField P t]


-- @@ L41-46 verbatim
theorem Budget.correctedPressureTower_pointField (R : ApproximationResidual P hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (B.correctedPressureTower P R).pointField t x =
      R.pressure.pointField t x + B.pointPressure P t x := by
  rw [B.correctedPressureTower_eq P R, FieldTower.add_pointField,
    B.pressureTower_pointField P t]


-- @@ L48-52 verbatim
theorem exactPacketOfResidual_velocity_pointField (R : ApproximationResidual P hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (exactPacketOfResidual P B R).velocity.pointField t x =
      A.approximation.pointField t x + B.pointField P t x :=
  B.correctedFieldTower_pointField P t x


-- @@ L54-58 verbatim
theorem exactPacketOfResidual_pressure_pointField (R : ApproximationResidual P hT A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    (exactPacketOfResidual P B R).pressure.pointField t x =
      R.pressure.pointField t x + B.pointPressure P t x :=
  B.correctedPressureTower_pointField P R t x


-- @@ L60-60 verbatim
end EulerAllOrderDriftCorrection
