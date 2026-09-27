/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradient
public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPaths
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageTime
import LeanPool.NavierStokesAndEuler.Euler.CylinderCoveringDerivative
import LeanPool.NavierStokesAndEuler.Euler.CylinderRawSupport
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryEquation
import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedSupport
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketParity


-- @@ L20-21 verbatim
/-! Canonical raw fields for the actual terminal-history/forward primary
solution, with genuine time derivative, support, mean and tangent constraints. -/


-- @@ L23-23 verbatim
section


-- @@ L25-25 verbatim
/-! Odd compact terminal data propagate through the genuine history and forward primary solve. -/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace EulerTransversePacketPrimary


-- @@ L33-35 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
  EulerTransversePacketProvider EulerTimeIntervalRestriction EulerElapsedTimePathGluing


-- @@ L37-45 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U))


-- @@ L47-47 verbatim
include hF hM hH hY


-- @@ L49-57 verbatim
theorem forwardInitial_reflection_neg :
    reflection P ((forwardInitial τ hτ hτT B Y).value : CylinderL2 P U) =
      -((forwardInitial τ hτ hτT B Y).value : CylinderL2 P U) :=
  B.coefficients.endpointCoordinate_odd P
    ((D.initial τ hτ hτT.le).frame_even (fun t x => hF (initialInclusion D.T τ hτT.le t) x))
    ((D.initial τ hτ hτT.le).frameDerivative_even
      (fun t x => hF (initialInclusion D.T τ hτT.le t) x)
      (fun t x => hM (initialInclusion D.T τ hτT.le t) x))
    hH Y.value hY ⟨τ,hτ.le,le_rfl⟩


-- @@ L59-66 verbatim
theorem pastVelocity_reflection_neg (t : Icc (0 : ℝ) τ) :
    reflection P (pastVelocity τ hτ hτT B Y t) = -pastVelocity τ hτ hτT B Y t :=
  B.coefficients.endpointVelocity_odd P
    ((D.initial τ hτ hτT.le).frame_even (fun s x => hF (initialInclusion D.T τ hτT.le s) x))
    ((D.initial τ hτ hτT.le).frameDerivative_even
      (fun s x => hF (initialInclusion D.T τ hτT.le s) x)
      (fun s x => hM (initialInclusion D.T τ hτT.le s) x))
    hH Y.value hY t


-- @@ L68-75 verbatim
theorem pastDerivative_reflection_neg (t : Icc (0 : ℝ) τ) :
    reflection P (pastDerivative τ hτ hτT B Y t) = -pastDerivative τ hτ hτT B Y t :=
  B.coefficients.endpointDerivative_odd P
    ((D.initial τ hτ hτT.le).frame_even (fun s x => hF (initialInclusion D.T τ hτT.le s) x))
    ((D.initial τ hτ hτT.le).frameDerivative_even
      (fun s x => hF (initialInclusion D.T τ hτT.le s) x)
      (fun s x => hM (initialInclusion D.T τ hτT.le s) x))
    hH Y.value hY t


-- @@ L77-77 verbatim
include hSym


-- @@ L79-85 verbatim
theorem futureVelocity_reflection_neg (t : Icc (0 : ℝ) (D.T - τ)) :
    reflection P (futureVelocity τ hτ hτT B Y t) = -futureVelocity τ hτ hτT B Y t :=
  (zeroForcing (D.tail τ hτ.le hτT)).velocityPath_reflection_neg (forwardInitial τ hτ hτT B Y) hSym
    (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
    (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
    (by intro s x θ; simp only [Pi.zero_apply,neg_zero])
    (forwardInitial_reflection_neg τ hτ hτT B Y hF hM hH hY) t


-- @@ L87-94 verbatim
theorem futureDerivative_reflection_neg (t : Icc (0 : ℝ) (D.T - τ)) :
    reflection P (futureDerivative τ hτ hτT B Y t) = -futureDerivative τ hτ hτT B Y t :=
  (zeroForcing (D.tail τ hτ.le hτT)).derivativePath_reflection_neg (forwardInitial τ hτ hτT B Y)
      hSym
    (fun s x => hF (tailInclusion D.T τ hτ.le s) x)
    (fun s x => hM (tailInclusion D.T τ hτ.le s) x)
    (by intro s x θ; simp only [Pi.zero_apply,neg_zero])
    (forwardInitial_reflection_neg τ hτ hτT B Y hF hM hH hY) t


-- @@ L96-100 verbatim
theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (velocityPath τ hτ hτT B Y t) = -velocityPath τ hτ hτT B Y t :=
  join_mem D.T τ hτ.le hτT.le _ _ (velocity_match τ hτ hτT B Y) {u | reflection P u = -u}
    (pastVelocity_reflection_neg τ hτ hτT B Y hF hM hH hY)
    (futureVelocity_reflection_neg τ hτ hτT B Y hSym hF hM hH hY) t


-- @@ L102-106 verbatim
theorem derivativePath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (derivativePath τ hτ hτT B Y t) = -derivativePath τ hτ hτT B Y t :=
  join_mem D.T τ hτ.le hτT.le _ _ (derivative_match τ hτ hτT B Y) {u | reflection P u = -u}
    (pastDerivative_reflection_neg τ hτ hτT B Y hF hM hH hY)
    (futureDerivative_reflection_neg τ hτ hτT B Y hSym hF hM hH hY) t


-- @@ L108-108 verbatim
end EulerTransversePacketPrimary


-- @@ L110-110 verbatim
end

-- @@ L111-111 verbatim
end


-- @@ L113-113 verbatim
end


-- @@ L115-115 verbatim
@[expose] public section


-- @@ L117-117 verbatim
noncomputable section


-- @@ L119-119 verbatim
namespace EulerTransversePacketPrimary


-- @@ L121-125 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerCylinderSmoothOrbit EulerCylinderScalarPrimitive EulerCylinderAngleAverage
  EulerPacketProfileRecursion EulerTransversePacketProvider EulerPacketCylinderField
  EulerMetricTransport EulerCylinderFieldReflection

-- @@ L126-126 verbatim
open scoped ContDiff


-- @@ L128-131 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) (Y : InitialData P D)


-- @@ L133-137 verbatim
/-- Vector, defined pointwise by `pointField P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ
hτ hτT B Y) (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def vector : VectorField := fun z =>
  pointField P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))


-- @@ L139-143 verbatim
/-- Vector derivative, defined pointwise by `pointField P (derivativePath τ hτ hτT B Y)
(derivativePath_orbit τ hτ hτT B Y) (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def vectorDerivative : VectorField := fun z =>
  pointField P (derivativePath τ hτ hτT B Y) (derivativePath_orbit τ hτ hτT B Y)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))


-- @@ L145-149 verbatim
/-- Scalar, defined pointwise by `scalarPointField P (pressurePath τ hτ hτT B Y)
(pressurePath_orbit τ hτ hτT B Y) (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))`. -/
def scalar : ScalarField := fun z =>
  scalarPointField P (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y)
    (D.clamp z.1) (z.2.1,(z.2.2 : AddCircle P))


-- @@ L151-155 verbatim
/-- Vector field, bundling `path`, `orbit`, `raw_eq`. -/
def vectorField : Field P D.T (vector τ hτ hτT B Y) where
  path := velocityPath τ hτ hτT B Y
  orbit := velocityPath_orbit τ hτ hτT B Y
  raw_eq t x θ := by simp only [vector,Data.clamp_coe]


-- @@ L157-161 verbatim
/-- Vector derivative field, bundling `path`, `orbit`, `raw_eq`. -/
def vectorDerivativeField : Field P D.T (vectorDerivative τ hτ hτT B Y) where
  path := derivativePath τ hτ hτT B Y
  orbit := derivativePath_orbit τ hτ hτT B Y
  raw_eq t x θ := by simp only [vectorDerivative,Data.clamp_coe]


-- @@ L163-164 verbatim
theorem vectorField_time : TimeDerivative D.T_pos.le (vectorField τ hτ hτT B Y)
    (vectorDerivativeField τ hτ hτT B Y) := velocityPath_time τ hτ hτT B Y


-- @@ L166-170 verbatim
theorem vector_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    HasDerivWithinAt (fun s => vector τ hτ hτT B Y (s,(x,θ)))
      (vectorDerivative τ hτ hτT B Y (t,(x,θ))) (Icc (0 : ℝ) D.T) t :=
  (vectorField τ hτ hτT B Y).raw_hasDerivWithinAt D.T_pos.le
    (vectorDerivativeField τ hτ hτT B Y) (vectorField_time τ hτ hτT B Y) t x θ


-- @@ L172-175 verbatim
theorem scalar_eq_pointField (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    scalar τ hτ hτT B Y (t,(x,θ)) =
      scalarPointField P (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y)
        t (x,(θ : AddCircle P)) := by simp only [scalar,Data.clamp_coe]


-- @@ L177-181 verbatim
/-- Scalar gradient field, constructed using `EulerPacketCylinderField.scalarGradientField`. -/
def scalarGradientField : Field P D.T (pressureGradient (scalar τ hτ hτT B Y)) :=
  EulerPacketCylinderField.scalarGradientField (scalar τ hτ hτT B Y)
    (pressurePath τ hτ hτT B Y) (pressurePath_orbit τ hτ hτT B Y)
    (scalar_eq_pointField τ hτ hτT B Y)


-- @@ L183-186 verbatim
theorem scalar_smooth (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Space × ℝ => scalar τ hτ hτT B Y (t,y)) :=
  coverField_contDiff P _ (scalarPointField_smooth P (pressurePath τ hτ hτT B Y)
    (pressurePath_orbit τ hτ hτT B Y) (D.clamp t))


-- @@ L188-194 verbatim
theorem vector_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    vector τ hτ hτT B Y (t,(x,θ)) = 0 := by
  change pointField P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y)
    (D.clamp t) (x,(θ : AddCircle P)) = 0
  rw [pointField_eq_representative]
  exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
    _ _ (velocityPath_supported τ hτ hτT B Y (D.clamp t)) (x,(θ : AddCircle P)) hx


-- @@ L196-202 verbatim
theorem vectorDerivative_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    vectorDerivative τ hτ hτT B Y (t,(x,θ)) = 0 := by
  change pointField P (derivativePath τ hτ hτT B Y) (derivativePath_orbit τ hτ hτT B Y)
    (D.clamp t) (x,(θ : AddCircle P)) = 0
  rw [pointField_eq_representative]
  exact representative_zero_outside P D.support D.support_measurable D.support_compact.isClosed
    _ _ (derivativePath_supported τ hτ hτT B Y (D.clamp t)) (x,(θ : AddCircle P)) hx


-- @@ L204-208 verbatim
theorem vector_mean_zero (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, vector τ hτ hτT B Y (t,(x,θ))) = 0 :=
  (pointField_mean_zero_iff P (velocityPath τ hτ hτT B Y)
    (velocityPath_orbit τ hτ hτT B Y) (D.clamp t)).mp
      (velocityPath_mean_zero τ hτ hτT B Y (D.clamp t)) x


-- @@ L210-213 verbatim
theorem vector_periodic (t : ℝ) (x : Space) :
    Function.Periodic (fun θ => vector τ hτ hτT B Y (t,(x,θ))) P := by
  intro θ
  simp only [vector,AddCircle.coe_add_period]


-- @@ L215-218 verbatim
theorem scalar_periodic (t : ℝ) (x : Space) :
    Function.Periodic (fun θ => scalar τ hτ hτT B Y (t,(x,θ))) P := by
  intro θ
  simp only [scalar,AddCircle.coe_add_period]


-- @@ L220-234 verbatim
theorem vector_tangent (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    ⟪D.normalField (t,(x,θ)),vector τ hτ hτT B Y (t,(x,θ))⟫_ℝ = 0 := by
  have hae : (fun z : LiftDomain P => ⟪D.normal.field t z.1,
      pointField P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t z⟫_ℝ)
      =ᵐ[liftMeasure P] (fun _ => (0 : ℝ)) := by
    filter_upwards [tangent_ae τ hτ hτT B Y t,
      pointField_ae P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t]
      with z hz hv
    rwa [hv] at hz
  have hm : Continuous (fun z : LiftDomain P => D.normal.field t z.1) :=
    (D.normal.field t).continuous.comp continuous_fst
  have hv := smoothField_continuous P _
    (pointField_smooth P (velocityPath τ hτ hτT B Y) (velocityPath_orbit τ hτ hτT B Y) t)
  have he := congrFun (Measure.eq_of_ae_eq hae (hm.inner hv) continuous_const) (x,(θ : AddCircle P))
  simpa only [vector,Data.normalField,Data.clamp_coe] using he


-- @@ L236-240 verbatim
variable (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U))


-- @@ L242-242 verbatim
include hSym hF hM hH hY


-- @@ L244-247 verbatim
theorem vector_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vector τ hτ hτT B Y (t,(-x,-θ)) = -vector τ hτ hτT B Y (t,(x,θ)) :=
  (vectorField τ hτ hτT B Y).raw_odd_of_reflection_neg t
    (velocityPath_reflection_neg τ hτ hτT B Y hSym hF hM hH hY t) x θ


-- @@ L249-252 verbatim
theorem vectorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    vectorDerivative τ hτ hτT B Y (t,(-x,-θ)) = -vectorDerivative τ hτ hτT B Y (t,(x,θ)) :=
  (vectorDerivativeField τ hτ hτT B Y).raw_odd_of_reflection_neg t
    (derivativePath_reflection_neg τ hτ hτT B Y hSym hF hM hH hY t) x θ


-- @@ L254-254 verbatim
end EulerTransversePacketPrimary
