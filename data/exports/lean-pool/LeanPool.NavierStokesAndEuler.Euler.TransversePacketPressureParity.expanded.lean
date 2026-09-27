/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider
import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity


-- @@ L14-14 verbatim
/-! Even parity of the actual normalized transverse pressure from the odd solved velocity. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerTransversePacketProvider


-- @@ L23-25 verbatim
open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketProfileRecursion EulerCylinderFieldReflection EulerLpCylinderTranslation
  EulerCylinderScalarPrimitive


-- @@ L27-27 verbatim
namespace Forcing


-- @@ L29-31 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)


-- @@ L33-37 verbatim
/-- Normal residual field type used in transverse packet pressure parity. -/
abbrev normalResidualField := EulerSourceCylinderClassical.normalResidual
  P D.support D.support_measurable D.support_compact D.T D.T_pos.le
  D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value
  G.path_orbit I.orbit D.M D.normal


-- @@ L39-45 verbatim
theorem normalResidualField_formula (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.normalResidualField I t (x,(θ : AddCircle P)) =
      (⟪D.normal.field t x,raw (t,(x,θ))⟫_ℝ -
        2*⟪D.normal.field t x,D.M.field t x (G.vector I (t,(x,θ)))⟫_ℝ) / ‖D.normal.field t x‖^2 :=
            by
  simp only [normalResidualField,EulerSourceCylinderClassical.normalResidual,
    vector,Data.clamp_coe,G.raw_eq]


-- @@ L47-51 verbatim
variable (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))
  (hinit : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U))


-- @@ L53-60 verbatim
include hSym hF hM hraw hinit in
theorem normalResidualField_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.normalResidualField I t (-x,((-θ : ℝ) : AddCircle P)) =
      -G.normalResidualField I t (x,(θ : AddCircle P)) := by
  rw [G.normalResidualField_formula,G.normalResidualField_formula,
    D.normal_even hF,hM,hraw,G.vector_odd I hSym hF hM hraw hinit]
  simp only [map_neg,inner_neg_right]
  ring


-- @@ L62-68 verbatim
include hSym hF hM hraw hinit in
theorem scalar_even (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.scalar I (t,(-x,-θ)) = G.scalar I (t,(x,θ)) := by
  unfold scalar
  simp only [Data.clamp_coe]
  exact classicalPrimitive_joint_even P (G.normalResidualField I t) _ _
    (G.normalResidualField_odd I hSym hF hM hraw hinit t) x θ


-- @@ L70-70 verbatim
end Forcing


-- @@ L72-74 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (I : InitialData P D) (raw : VectorField) (h : Nonempty (Forcing P D raw))


-- @@ L76-88 verbatim
include h in
theorem highSolve_parity (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))
    (hinit : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U)) :
    (∀ (t : Icc (0 : ℝ) D.T) x θ,
      (highSolve P D I raw).1 (t,(-x,-θ)) = -(highSolve P D I raw).1 (t,(x,θ))) ∧
    (∀ (t : Icc (0 : ℝ) D.T) x θ,
      (highSolve P D I raw).2 (t,(-x,-θ)) = (highSolve P D I raw).2 (t,(x,θ))) := by
  rw [highSolve_of_admissible D I raw h]
  exact ⟨(Classical.choice h).vector_odd I hSym hF hM hraw hinit,
    (Classical.choice h).scalar_even I hSym hF hM hraw hinit⟩


-- @@ L90-90 verbatim
end EulerTransversePacketProvider
