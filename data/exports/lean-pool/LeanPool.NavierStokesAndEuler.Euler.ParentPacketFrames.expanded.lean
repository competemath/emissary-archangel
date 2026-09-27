/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldPrecomp
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldBilinear
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketCofactorOperator
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets


-- @@ L16-19 verbatim
/-! The packet coefficients are constructed from the actual parent
particle-map displacement and its two time derivatives. The inverse is
the polynomial cofactor, and the strain and Jacobi curvature are their
literal products; no separate inverse or coefficient evolution is assumed. -/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace EulerParentPacketFrames


-- @@ L28-29 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketCofactor
  EulerPacketPiola

-- @@ L30-30 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L32-53 verbatim
/-- Parent data, collecting `T`, `T_pos`, `ell`, `ell_pos`, `ell_le_one`, `displacement` and
their compatibility conditions. -/
structure Parent where
  /-- Time horizon of `Parent`, of type `ℝ`. -/
  T : ℝ
  T_pos : 0 < T
  /-- Ell of `Parent`, of type `ℝ`. -/
  ell : ℝ
  ell_pos : 0 < ell
  ell_le_one : ell ≤ 1
  /-- Displacement of `Parent`, of type `SmoothTimeField (Icc (0 : ℝ) T) Space Space`. -/
  displacement : SmoothTimeField (Icc (0 : ℝ) T) Space Space
  /-- Velocity field of `Parent`, of type `SmoothTimeField (Icc (0 : ℝ) T) Space Space`. -/
  velocity : SmoothTimeField (Icc (0 : ℝ) T) Space Space
  /-- Acceleration of `Parent`, of type `SmoothTimeField (Icc (0 : ℝ) T) Space Space`. -/
  acceleration : SmoothTimeField (Icc (0 : ℝ) T) Space Space
  displacement_time : SmoothTimeField.TimeDerivative T T_pos.le displacement velocity
  velocity_time : SmoothTimeField.TimeDerivative T T_pos.le velocity acceleration
  initial : ∀ x, displacement.field ⟨0,le_rfl,T_pos.le⟩ x=0
  determinant : ∀ (t : Icc (0 : ℝ) T) x,
    (operatorMatrix (ContinuousLinearMap.id ℝ Space +
      fderiv ℝ (displacement.field t : Space → Space) (ell • x))).det=1


-- @@ L55-55 verbatim
namespace Parent


-- @@ L57-57 verbatim
variable (G : Parent)


-- @@ L59-60 verbatim
/-- Zero time, given by `⟨0,le_rfl,G.T_pos.le⟩`. -/
def zeroTime : Icc (0 : ℝ) G.T := ⟨0,le_rfl,G.T_pos.le⟩


-- @@ L62-65 verbatim
/-- Frame as an element of `SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace`. -/
def frame : SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace :=
  (SmoothTimeField.boundConstant (ContinuousLinearMap.id ℝ Space)).add
    (G.displacement.derivative.precompLinear (G.ell • ContinuousLinearMap.id ℝ Space))


-- @@ L67-70 verbatim
/-- First, given by `G.velocity.derivative.precompLinear (G.ell • ContinuousLinearMap.id ℝ
Space)`. -/
def first : SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace :=
  G.velocity.derivative.precompLinear (G.ell • ContinuousLinearMap.id ℝ Space)


-- @@ L72-75 verbatim
/-- Second, given by `G.acceleration.derivative.precompLinear (G.ell • ContinuousLinearMap.id ℝ
Space)`. -/
def second : SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace :=
  G.acceleration.derivative.precompLinear (G.ell • ContinuousLinearMap.id ℝ Space)


-- @@ L77-79 verbatim
/-- Inverse, given by `SmoothTimeField.bilinear cofactorBilinear G.frame G.frame`. -/
def inverse : SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace :=
  SmoothTimeField.bilinear cofactorBilinear G.frame G.frame


-- @@ L81-83 verbatim
/-- Strain, given by `SmoothTimeField.bilinear (compL ℝ Space Space Space) G.first G.inverse`. -/
def strain : SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace :=
  SmoothTimeField.bilinear (compL ℝ Space Space Space) G.first G.inverse


-- @@ L85-89 verbatim
/-- Curvature, given by `(SmoothTimeField.bilinear (compL ℝ Space Space Space) G.second
G.inverse).map (-ContinuousLinearMap.id ℝ EndSpace)`. -/
def curvature : SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace :=
  (SmoothTimeField.bilinear (compL ℝ Space Space Space) G.second G.inverse).map
    (-ContinuousLinearMap.id ℝ EndSpace)


-- @@ L91-95 verbatim
@[simp] theorem frame_apply (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.frame.field t x = ContinuousLinearMap.id ℝ Space +
      fderiv ℝ (G.displacement.field t : Space → Space) (G.ell • x) := by
  change ContinuousLinearMap.id ℝ Space+G.displacement.derivativeField t (G.ell • x) = _
  rw [SmoothTimeField.derivativeField_eq]


-- @@ L97-99 verbatim
@[simp] theorem first_apply (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.first.field t x = fderiv ℝ (G.velocity.field t : Space → Space) (G.ell • x) :=
  G.velocity.derivativeField_eq t (G.ell • x)


-- @@ L101-103 verbatim
@[simp] theorem second_apply (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.second.field t x = fderiv ℝ (G.acceleration.field t : Space → Space) (G.ell • x) :=
  G.acceleration.derivativeField_eq t (G.ell • x)


-- @@ L105-106 verbatim
@[simp] theorem inverse_apply (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.inverse.field t x = adjugate (G.frame.field t x) := rfl


-- @@ L108-109 verbatim
@[simp] theorem strain_apply (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.strain.field t x = (G.first.field t x).comp (G.inverse.field t x) := rfl


-- @@ L111-112 verbatim
@[simp] theorem curvature_apply (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.curvature.field t x = -((G.second.field t x).comp (G.inverse.field t x)) := rfl


-- @@ L114-117 verbatim
theorem frame_det (t : Icc (0 : ℝ) G.T) (x : Space) : (operatorMatrix (G.frame.field t x)).det=1 :=
    by
  rw [G.frame_apply]
  exact G.determinant t x


-- @@ L119-121 verbatim
theorem inverse_left (t : Icc (0 : ℝ) G.T) (x v : Space) :
    G.inverse.field t x (G.frame.field t x v)=v :=
  congrArg (fun A : EndSpace => A v) (adjugate_comp (G.frame.field t x) (G.frame_det t x))


-- @@ L123-125 verbatim
theorem inverse_right (t : Icc (0 : ℝ) G.T) (x v : Space) :
    G.frame.field t x (G.inverse.field t x v)=v :=
  congrArg (fun A : EndSpace => A v) (comp_adjugate (G.frame.field t x) (G.frame_det t x))


-- @@ L127-132 verbatim
theorem frame_time : SmoothTimeField.TimeDerivative G.T G.T_pos.le G.frame G.first := by
  have h := (SmoothTimeField.TimeDerivative.derivative G.T G.T_pos.le
    G.displacement G.velocity G.displacement_time).precompLinear (G.ell • ContinuousLinearMap.id ℝ
        Space)
  intro t x
  exact (h t x).const_add (ContinuousLinearMap.id ℝ Space)


-- @@ L134-137 verbatim
theorem first_time : SmoothTimeField.TimeDerivative G.T G.T_pos.le G.first G.second :=
  (SmoothTimeField.TimeDerivative.derivative G.T G.T_pos.le G.velocity G.acceleration
      G.velocity_time).precompLinear
    (G.ell • ContinuousLinearMap.id ℝ Space)


-- @@ L139-145 verbatim
theorem frame_initial (x : Space) : G.frame.field G.zeroTime x = ContinuousLinearMap.id ℝ Space :=
    by
  rw [G.frame_apply]
  have he : (G.displacement.field G.zeroTime : Space → Space) = fun _ => 0 := funext G.initial
  have hd : fderiv ℝ (fun _ : Space => (0 : Space)) (G.ell • x) = 0 :=
    (hasFDerivAt_const (0 : Space) (G.ell • x)).fderiv
  rw [he,hd,add_zero]


-- @@ L147-149 verbatim
theorem inverse_initial (x v : Space) : G.inverse.field G.zeroTime x v=v := by
  have h := G.inverse_left G.zeroTime x v
  rwa [G.frame_initial,ContinuousLinearMap.id_apply] at h


-- @@ L151-153 verbatim
theorem strain_equation (t : Icc (0 : ℝ) G.T) (x v : Space) :
    G.first.field t x v = G.strain.field t x (G.frame.field t x v) := by
  rw [G.strain_apply,comp_apply,G.inverse_left]


-- @@ L155-157 verbatim
theorem second_equation (t : Icc (0 : ℝ) G.T) (x v : Space) :
    G.second.field t x v = -(G.curvature.field t x (G.frame.field t x v)) := by
  rw [G.curvature_apply,neg_apply,comp_apply,G.inverse_left,neg_neg]


-- @@ L159-165 verbatim
/-- Initial strain, bundling `field`, `smooth`, `bounded`. -/
def initialStrain : BoundedSmoothField EndSpace where
  field := G.first.field G.zeroTime
  smooth := G.first.smooth G.zeroTime
  bounded n := ⟨‖G.first.jet n G.zeroTime‖,fun x => by
    rw [← G.first.jet_eq]
    exact (G.first.jet n G.zeroTime).norm_coe_le_norm x⟩


-- @@ L167-168 verbatim
@[simp] theorem initialStrain_apply (x : Space) :
    G.initialStrain.field x = G.first.field G.zeroTime x := rfl


-- @@ L170-170 verbatim
end Parent

-- @@ L171-171 verbatim
end EulerParentPacketFrames
