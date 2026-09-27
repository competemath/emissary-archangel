/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphGevrey
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Operator.Prod
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
import LeanPool.NavierStokesAndEuler.Euler.GevreyJetCompositionLp
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowGevrey
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.Euler.LpParameterIntegral
import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDescentJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift
import LeanPool.NavierStokesAndEuler.Euler.GevreyProductLp
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.SmoothBanachFlow
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowVolume
public import LeanPool.NavierStokesAndEuler.Euler.CylinderCoverDescent
public import LeanPool.NavierStokesAndEuler.Euler.BoundedLipschitzFlow
import LeanPool.NavierStokesAndEuler.Euler.BoundedFlowContinuity
import Mathlib.Analysis.Calculus.Deriv.Add
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldPrecomp
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Trace
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricTransport
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.MeanValue


-- @@ L40-43 verbatim
/-! The actual physical graph flow has smooth square-integrable
displacement, velocity and acceleration, with explicit Gevrey bounds.
Every input estimate is on the original lifted velocity or its genuine
time derivative; no regularity of the output flow is assumed. -/


-- @@ L45-45 verbatim
section


-- @@ L47-49 verbatim
/-! The true physical graph flow and its first two time derivatives.
The change of labels is an actual ODE conjugacy, and the resulting
three-dimensional flow preserves ordinary Lebesgue volume. -/


-- @@ L51-51 verbatim
section


-- @@ L53-55 verbatim
/-! The graph restriction of the actual lifted flow is the actual flow
of a smooth three-dimensional velocity. It preserves ordinary spatial
volume when the original lifted velocity has zero trace. -/


-- @@ L57-57 verbatim
section


-- @@ L59-61 verbatim
/-! A lifted flow tangent to the oscillating graph gives an actual
three-dimensional flow, with inverse and the projected differential
equation. Graph invariance follows from a conserved linear functional. -/


-- @@ L63-63 verbatim
@[expose] public section


-- @@ L65-65 verbatim
noncomputable section


-- @@ L67-67 verbatim
namespace EulerGraphInvariantFlow


-- @@ L69-69 verbatim
open Set InnerProductSpace ContinuousLinearMap EulerLiftedGradientSpace EulerMetricTransport


-- @@ L71-73 verbatim
/-- Graph linear, given by `(ContinuousLinearMap.id ℝ Vector3).prod (k • toDual ℝ Vector3 m)`. -/
def graphLinear (k : ℝ) (m : Vector3) : Vector3 →L[ℝ] LiftTangent :=
  (ContinuousLinearMap.id ℝ Vector3).prod (k • toDual ℝ Vector3 m)


-- @@ L75-76 verbatim
@[simp] theorem graphLinear_apply (k : ℝ) (m x : Vector3) :
    graphLinear k m x = (x,k*inner ℝ m x) := rfl


-- @@ L78-81 verbatim
/-- Graph constraint, given by `snd ℝ Vector3 ℝ - k • (toDual ℝ Vector3 m).comp (fst ℝ Vector3
ℝ)`. -/
def graphConstraint (k : ℝ) (m : Vector3) : LiftTangent →L[ℝ] ℝ :=
  snd ℝ Vector3 ℝ - k • (toDual ℝ Vector3 m).comp (fst ℝ Vector3 ℝ)


-- @@ L83-84 verbatim
@[simp] theorem graphConstraint_apply (k : ℝ) (m : Vector3) (z : LiftTangent) :
    graphConstraint k m z = z.2-k*inner ℝ m z.1 := rfl


-- @@ L86-87 verbatim
theorem graphConstraint_graph (k : ℝ) (m x : Vector3) :
    graphConstraint k m (graphLinear k m x)=0 := by simp


-- @@ L89-93 verbatim
theorem graphConstraint_transport (k κ : ℝ) (hk : k * κ = 1) (m v : Vector3) :
    graphConstraint k m (transportDirection κ m v)=0 := by
  change inner ℝ m v-k*inner ℝ m (κ • v)=0
  rw [inner_smul_right]
  simp only [← mul_assoc,hk,one_mul,sub_self]


-- @@ L95-96 verbatim
variable (k : ℝ) (m : Vector3) (V : EulerBoundedLipschitzFlow.Data LiftTangent)
  (hV : ∀ t z, graphConstraint k m (V.velocity t z) = 0)


-- @@ L98-107 verbatim
include hV in
theorem graphConstraint_flow (s t : ℝ) (z : LiftTangent) :
    graphConstraint k m (V.flow s t z)=graphConstraint k m z := by
  have hd (r : ℝ) : HasDerivAt (fun q => graphConstraint k m (V.flow s q z)) 0 r := by
    have h := (graphConstraint k m).hasFDerivAt.comp_hasDerivAt r (V.flow_hasDerivAt s r z)
    rw [hV] at h
    convert! h using 1
  have he := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t s
  simpa only [V.flow_initial] using he


-- @@ L109-110 verbatim
/-- Graph flow, given by `(V.flow s t (graphLinear k m x)).1`. -/
def graphFlow (s t : ℝ) (x : Vector3) : Vector3 := (V.flow s t (graphLinear k m x)).1


-- @@ L112-119 verbatim
include hV in
theorem graphFlow_invariant (s t : ℝ) (x : Vector3) :
    V.flow s t (graphLinear k m x)=graphLinear k m (graphFlow k m V s t x) := by
  have he := graphConstraint_flow k m V hV s t (graphLinear k m x)
  rw [graphConstraint_graph,graphConstraint_apply,sub_eq_zero] at he
  apply Prod.ext
  · rfl
  · exact he


-- @@ L121-122 verbatim
@[simp] theorem graphFlow_initial (s : ℝ) (x : Vector3) : graphFlow k m V s s x=x := by
  simp [graphFlow]


-- @@ L124-129 verbatim
include hV in
theorem graphFlow_inverse (s t : ℝ) (x : Vector3) :
    graphFlow k m V t s (graphFlow k m V s t x)=x := by
  change (V.flow t s (graphLinear k m (graphFlow k m V s t x))).1=x
  rw [← graphFlow_invariant k m V hV,V.flow_inverse]
  rfl


-- @@ L131-136 verbatim
include hV in
theorem graphFlow_hasDerivAt (s t : ℝ) (x : Vector3) :
    HasDerivAt (fun r => graphFlow k m V s r x)
      (V.velocity t (graphLinear k m (graphFlow k m V s t x))).1 t := by
  have hd := (V.flow_hasDerivAt s t (graphLinear k m x)).fst
  rwa [graphFlow_invariant k m V hV] at hd


-- @@ L138-139 verbatim
theorem graphFlow_continuous (s t : ℝ) : Continuous (graphFlow k m V s t) :=
  continuous_fst.comp ((V.flowHomeomorph s t).continuous.comp (graphLinear k m).continuous)


-- @@ L141-144 verbatim
theorem graphFlow_forward_joint_continuous :
    Continuous (fun r : ℝ × Vector3 => graphFlow k m V 0 r.1 r.2) :=
  continuous_fst.comp (V.forward_joint_continuous.comp
    (continuous_fst.prodMk ((graphLinear k m).continuous.comp continuous_snd)))


-- @@ L146-149 verbatim
theorem graphFlow_backward_joint_continuous :
    Continuous (fun r : ℝ × Vector3 => graphFlow k m V r.1 0 r.2) :=
  continuous_fst.comp (V.backward_joint_continuous.comp
    (continuous_fst.prodMk ((graphLinear k m).continuous.comp continuous_snd)))


-- @@ L151-151 verbatim
end EulerGraphInvariantFlow


-- @@ L153-153 verbatim
end

-- @@ L154-154 verbatim
end


-- @@ L156-156 verbatim
end


-- @@ L158-158 verbatim
section


-- @@ L160-162 verbatim
/-! A graph-tangent lifted velocity has the same ordinary divergence
as its three-dimensional graph restriction. This identifies the
volume-preservation hypothesis for the actual physical-label flow. -/


-- @@ L164-164 verbatim
@[expose] public section


-- @@ L166-166 verbatim
noncomputable section


-- @@ L168-168 verbatim
namespace EulerGraphInvariantFlow


-- @@ L170-170 verbatim
open ContinuousLinearMap EulerLiftedGradientSpace


-- @@ L172-172 verbatim
variable (k : ℝ) (m : Vector3) (f : LiftTangent → LiftTangent)


-- @@ L174-175 verbatim
/-- Graph velocity, given by `(f (graphLinear k m x)).1`. -/
def graphVelocity (x : Vector3) : Vector3 := (f (graphLinear k m x)).1


-- @@ L177-199 verbatim
theorem graphVelocity_trace (hf : Differentiable ℝ f)
    (hgraph : ∀ z, graphConstraint k m (f z) = 0) (x : Vector3) :
    LinearMap.trace ℝ Vector3 (fderiv ℝ (graphVelocity k m f) x).toLinearMap =
      LinearMap.trace ℝ LiftTangent (fderiv ℝ f (graphLinear k m x)).toLinearMap := by
  let J := graphLinear k m
  let F := fst ℝ Vector3 ℝ
  let D := fderiv ℝ f (J x)
  have hfun : (J.comp F) ∘ f = f := by
    funext z
    apply Prod.ext
    · rfl
    · exact (sub_eq_zero.mp (hgraph z)).symm
  have hD : D = J.comp (F.comp D) := by
    have hd := ((J.comp F).hasFDerivAt.comp (J x) (hf (J x)).hasFDerivAt).fderiv
    rw [hfun] at hd
    exact hd
  have hg := (F.hasFDerivAt.comp x ((hf (J x)).hasFDerivAt.comp x J.hasFDerivAt)).fderiv
  change fderiv ℝ (graphVelocity k m f) x = F.comp (D.comp J) at hg
  rw [hg]
  calc
    _ = LinearMap.trace ℝ LiftTangent (J.comp (F.comp D)).toLinearMap :=
      LinearMap.trace_comp_comm' J.toLinearMap (F.comp D).toLinearMap
    _ = LinearMap.trace ℝ LiftTangent D.toLinearMap := by rw [← hD]


-- @@ L201-207 verbatim
theorem graphVelocity_trace_zero (hf : Differentiable ℝ f)
    (hgraph : ∀ z, graphConstraint k m (f z) = 0)
    (hdiv : ∀ z, LinearMap.trace ℝ LiftTangent (fderiv ℝ f z).toLinearMap = 0)
    (x : Vector3) :
    LinearMap.trace ℝ Vector3 (fderiv ℝ (graphVelocity k m f) x).toLinearMap=0 := by
  rw [graphVelocity_trace k m f hf hgraph]
  exact hdiv _


-- @@ L209-209 verbatim
end EulerGraphInvariantFlow


-- @@ L211-211 verbatim
end

-- @@ L212-212 verbatim
end


-- @@ L214-214 verbatim
end


-- @@ L216-216 verbatim
@[expose] public section


-- @@ L218-218 verbatim
noncomputable section


-- @@ L220-220 verbatim
namespace EulerGraphInvariantFlow


-- @@ L222-222 verbatim
open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothBanachFlow

-- @@ L223-223 verbatim
open scoped ContDiff


-- @@ L225-226 verbatim
variable (k : ℝ) (m : Vector3) (T : ℝ) (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)


-- @@ L228-230 verbatim
/-- Graph coefficient, given by `(A.precompLinear (graphLinear k m)).map (fst ℝ Vector3 ℝ)`. -/
def graphCoefficient : SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  (A.precompLinear (graphLinear k m)).map (fst ℝ Vector3 ℝ)


-- @@ L232-233 verbatim
@[simp] theorem graphCoefficient_apply (t : Icc (0 : ℝ) T) (x : Vector3) :
    (graphCoefficient k m T A).field t x = (A.field t (graphLinear k m x)).1 := rfl


-- @@ L235-239 verbatim
theorem graphCoefficient_timeDerivative
    (A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
    (htime : SmoothTimeField.TimeDerivative T hT A A₁) :
    SmoothTimeField.TimeDerivative T hT (graphCoefficient k m T A) (graphCoefficient k m T A₁) :=
  (htime.precompLinear (graphLinear k m)).map (fst ℝ Vector3 ℝ)


-- @@ L241-241 verbatim
variable (hgraph : ∀ t z, graphConstraint k m (A.field t z) = 0)


-- @@ L243-246 verbatim
include hgraph in
theorem flowData_tangent (r : ℝ) (z : LiftTangent) :
    graphConstraint k m ((flowData T hT A).velocity r z)=0 :=
  hgraph (projIcc 0 T hT r) z


-- @@ L248-257 verbatim
include hgraph in
theorem graph_flow_eq (s t : ℝ) (x : Vector3) :
    graphFlow k m (flowData T hT A) s t x =
      (flowData T hT (graphCoefficient k m T A)).flow s t x := by
  let V := flowData T hT (graphCoefficient k m T A)
  have hd (r : ℝ) : HasDerivAt (fun q => graphFlow k m (flowData T hT A) s q x)
      (V.velocity r (graphFlow k m (flowData T hT A) s r x)) r :=
    graphFlow_hasDerivAt k m (flowData T hT A) (flowData_tangent k m T hT A hgraph) s r x
  exact congrFun (V.flow_unique s x (fun q => graphFlow k m (flowData T hT A) s q x)
    hd (graphFlow_initial k m (flowData T hT A) s x)) t


-- @@ L259-264 verbatim
include hgraph in
theorem graph_flow_cover (s t : ℝ) (x : Vector3) :
    (flowData T hT A).flow s t (graphLinear k m x) =
      graphLinear k m ((flowData T hT (graphCoefficient k m T A)).flow s t x) := by
  rw [graphFlow_invariant k m (flowData T hT A) (flowData_tangent k m T hT A hgraph),
    graph_flow_eq k m T hT A hgraph]


-- @@ L266-273 verbatim
include hgraph in
theorem graph_displacement_eq (t : Icc (0 : ℝ) T) (x : Vector3) :
    (displacement T hT A t (graphLinear k m x)).1 =
      displacement T hT (graphCoefficient k m T A) t x := by
  rw [displacement_eq,displacement_eq]
  change ((flowData T hT A).flow 0 t (graphLinear k m x)-graphLinear k m x).1 = _
  rw [graph_flow_cover k m T hT A hgraph]
  rfl


-- @@ L275-282 verbatim
include hgraph in
theorem graph_forward_contDiff (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (graphFlow k m (flowData T hT A) 0 t) := by
  have he : graphFlow k m (flowData T hT A) 0 t =
      (flowData T hT (graphCoefficient k m T A)).forward t :=
    funext (graph_flow_eq k m T hT A hgraph 0 t)
  rw [he]
  exact forward_contDiff T hT (graphCoefficient k m T A) t


-- @@ L284-286 verbatim
variable (hdiv : ∀ t z,
  LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) z).toLinearMap =
      0)


-- @@ L288-293 verbatim
include hgraph hdiv in
theorem graphCoefficient_trace_zero (t : Icc (0 : ℝ) T) (x : Vector3) :
    LinearMap.trace ℝ Vector3
      (fderiv ℝ ((graphCoefficient k m T A).field t : Vector3 → Vector3) x).toLinearMap=0 :=
  graphVelocity_trace_zero k m (A.field t) ((A.smooth t).differentiable (by simp))
    (hgraph t) (hdiv t) x


-- @@ L295-303 verbatim
include hgraph hdiv in
theorem graph_forward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving (graphFlow k m (flowData T hT A) 0 t) volume volume := by
  have he : graphFlow k m (flowData T hT A) 0 t =
      (flowData T hT (graphCoefficient k m T A)).forward t :=
    funext (graph_flow_eq k m T hT A hgraph 0 t)
  rw [he]
  exact forward_measurePreserving T hT (graphCoefficient k m T A)
    (graphCoefficient_trace_zero k m T A hgraph hdiv) volume t


-- @@ L305-313 verbatim
include hgraph hdiv in
theorem graph_backward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving (graphFlow k m (flowData T hT A) t 0) volume volume := by
  have he : graphFlow k m (flowData T hT A) t 0 =
      (flowData T hT (graphCoefficient k m T A)).backward t :=
    funext (graph_flow_eq k m T hT A hgraph t 0)
  rw [he]
  exact backward_measurePreserving T hT (graphCoefficient k m T A)
    (graphCoefficient_trace_zero k m T A hgraph hdiv) volume t


-- @@ L315-315 verbatim
end EulerGraphInvariantFlow


-- @@ L317-317 verbatim
end

-- @@ L318-318 verbatim
end


-- @@ L320-320 verbatim
end


-- @@ L322-322 verbatim
section


-- @@ L324-326 verbatim
/-! A physical label dilation of a smooth velocity has the conjugate
actual flow. Displacement, material velocity and material acceleration
are the literal dilations of the corresponding original fields. -/


-- @@ L328-328 verbatim
@[expose] public section


-- @@ L330-330 verbatim
noncomputable section


-- @@ L332-332 verbatim
namespace EulerSmoothBanachFlow


-- @@ L334-334 verbatim
open Set ContinuousLinearMap MeasureTheory EulerSmoothFlowGevrey

-- @@ L335-335 verbatim
open scoped ContDiff


-- @@ L337-338 verbatim
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E) (ell : ℝ)


-- @@ L340-343 verbatim
/-- Scaled coefficient, given by `(A.precompLinear (ell⁻¹ • ContinuousLinearMap.id ℝ E)).map
(ell • ContinuousLinearMap.id ℝ E)`. -/
def scaledCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  (A.precompLinear (ell⁻¹ • ContinuousLinearMap.id ℝ E)).map (ell • ContinuousLinearMap.id ℝ E)


-- @@ L345-346 verbatim
@[simp] theorem scaledCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (scaledCoefficient T A ell).field t x = ell • A.field t (ell⁻¹ • x) := rfl


-- @@ L348-352 verbatim
theorem scaledCoefficient_timeDerivative
    (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
    (htime : SmoothTimeField.TimeDerivative T hT A A₁) :
    SmoothTimeField.TimeDerivative T hT (scaledCoefficient T A ell) (scaledCoefficient T A₁ ell) :=
  (htime.precompLinear (ell⁻¹ • ContinuousLinearMap.id ℝ E)).map (ell • ContinuousLinearMap.id ℝ E)


-- @@ L354-354 verbatim
variable [FiniteDimensional ℝ E]


-- @@ L356-370 verbatim
theorem scaled_flow_eq (hell : ell ≠ 0) (s t : ℝ) (x : E) :
    (flowData T hT (scaledCoefficient T A ell)).flow s t x =
      ell • (flowData T hT A).flow s t (ell⁻¹ • x) := by
  let V := flowData T hT (scaledCoefficient T A ell)
  have hd (r : ℝ) : HasDerivAt (fun q => ell • (flowData T hT A).flow s q (ell⁻¹ • x))
      (V.velocity r (ell • (flowData T hT A).flow s r (ell⁻¹ • x))) r := by
    have h := ((flowData T hT A).flow_hasDerivAt s r (ell⁻¹ • x)).const_smul ell
    convert h using 1
    · change ell • A.field (projIcc 0 T hT r)
        (ell⁻¹ • (ell • (flowData T hT A).flow s r (ell⁻¹ • x))) = _
      simp only [smul_smul,inv_mul_cancel₀ hell,one_smul]
      rfl
  have hi : ell • (flowData T hT A).flow s s (ell⁻¹ • x) = x := by
    simp only [EulerBoundedLipschitzFlow.Data.flow_initial,smul_smul,mul_inv_cancel₀ hell,one_smul]
  exact (congrFun (V.flow_unique s x _ hd hi) t).symm


-- @@ L372-378 verbatim
theorem scaled_displacement_eq (hell : ell ≠ 0) (t : Icc (0 : ℝ) T) (x : E) :
    displacement T hT (scaledCoefficient T A ell) t x =
      ell • displacement T hT A t (ell⁻¹ • x) := by
  rw [displacement_eq,displacement_eq]
  change (flowData T hT (scaledCoefficient T A ell)).flow 0 t x-x = _
  rw [scaled_flow_eq T hT A ell hell,smul_sub,smul_smul,mul_inv_cancel₀ hell,one_smul]
  rfl


-- @@ L380-387 verbatim
theorem scaled_materialVelocity_eq (hell : ell ≠ 0) (t : Icc (0 : ℝ) T) (x : E) :
    materialVelocity T hT (scaledCoefficient T A ell) t x =
      ell • materialVelocity T hT A t (ell⁻¹ • x) := by
  unfold materialVelocity
  rw [scaledCoefficient_apply]
  change ell • A.field t (ell⁻¹ • (flowData T hT (scaledCoefficient T A ell)).flow 0 t x) = _
  rw [scaled_flow_eq T hT A ell hell,smul_smul,inv_mul_cancel₀ hell,one_smul]
  rfl


-- @@ L389-400 verbatim
omit [FiniteDimensional ℝ E] in
theorem scaledCoefficient_fderiv (hell : ell ≠ 0) (t : Icc (0 : ℝ) T) (x : E) :
    fderiv ℝ ((scaledCoefficient T A ell).field t : E → E) x =
      fderiv ℝ (A.field t : E → E) (ell⁻¹ • x) := by
  have h := ((((A.smooth t).differentiable (by simp) (ell⁻¹ • x)).hasFDerivAt).comp x
    ((ell⁻¹ • ContinuousLinearMap.id ℝ E).hasFDerivAt)).const_smul ell
  change HasFDerivAt (fun y => ell • A.field t (ell⁻¹ • y)) _ x at h
  change fderiv ℝ (fun y => ell • A.field t (ell⁻¹ • y)) x = _
  rw [h.fderiv]
  ext v
  simp only [FunLike.coe_smul,Pi.smul_apply,comp_apply,id_apply,map_smul,smul_smul,mul_inv_cancel₀
      hell,one_smul]


-- @@ L402-409 verbatim
omit [FiniteDimensional ℝ E] in
theorem scaled_accelerationField_eq
    (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : E) :
    accelerationField T (scaledCoefficient T A ell) (scaledCoefficient T A₁ ell) t x =
      ell • accelerationField T A A₁ t (ell⁻¹ • x) := by
  simp only [accelerationField,scaledCoefficient_apply,scaledCoefficient_fderiv T A ell hell,
    map_smul,smul_add]


-- @@ L411-421 verbatim
theorem scaled_materialAcceleration_eq
    (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : E) :
    materialAcceleration T hT (scaledCoefficient T A ell) (scaledCoefficient T A₁ ell) t x =
      ell • materialAcceleration T hT A A₁ t (ell⁻¹ • x) := by
  unfold materialAcceleration
  rw [scaled_accelerationField_eq T A ell A₁ hell]
  change ell • accelerationField T A A₁ t
    (ell⁻¹ • (flowData T hT (scaledCoefficient T A ell)).flow 0 t x) = _
  rw [scaled_flow_eq T hT A ell hell,smul_smul,inv_mul_cancel₀ hell,one_smul]
  rfl


-- @@ L423-430 verbatim
omit [FiniteDimensional ℝ E] in
theorem scaledCoefficient_trace_zero (hell : ell ≠ 0)
    (hdiv : ∀ t x, LinearMap.trace ℝ E (fderiv ℝ (A.field t : E → E) x).toLinearMap = 0)
    (t : Icc (0 : ℝ) T) (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ ((scaledCoefficient T A ell).field t : E → E) x).toLinearMap=0 :=
        by
  rw [scaledCoefficient_fderiv T A ell hell]
  exact hdiv t _


-- @@ L432-432 verbatim
end EulerSmoothBanachFlow


-- @@ L434-434 verbatim
end

-- @@ L435-435 verbatim
end


-- @@ L437-437 verbatim
end


-- @@ L439-439 verbatim
@[expose] public section


-- @@ L441-441 verbatim
noncomputable section


-- @@ L443-443 verbatim
namespace EulerGraphInvariantFlow


-- @@ L445-446 verbatim
open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothBanachFlow
  EulerSmoothFlowGevrey

-- @@ L447-447 verbatim
open scoped ContDiff


-- @@ L449-451 verbatim
variable (k : ℝ) (m : Vector3) (T : ℝ) (hT : 0 ≤ T)
  (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hgraph : ∀ t z, graphConstraint k m (A.field t z) = 0)


-- @@ L453-460 verbatim
include hgraph in
theorem graph_materialVelocity_eq (t : Icc (0 : ℝ) T) (x : Vector3) :
    materialVelocity T hT (graphCoefficient k m T A) t x =
      (materialVelocity T hT A t (graphLinear k m x)).1 := by
  change (A.field t (graphLinear k m
    ((flowData T hT (graphCoefficient k m T A)).flow 0 t x))).1 = _
  rw [← graph_flow_cover k m T hT A hgraph]
  rfl


-- @@ L462-479 verbatim
include hgraph in
theorem graph_accelerationField_eq (t : Icc (0 : ℝ) T) (x : Vector3) :
    accelerationField T (graphCoefficient k m T A) (graphCoefficient k m T A₁) t x =
      (accelerationField T A A₁ t (graphLinear k m x)).1 := by
  let J := graphLinear k m
  let L := fst ℝ Vector3 ℝ
  have hd := (L.hasFDerivAt.comp x
    (((A.smooth t).differentiable (by simp) (J x)).hasFDerivAt.comp x J.hasFDerivAt)).fderiv
  change fderiv ℝ ((graphCoefficient k m T A).field t : Vector3 → Vector3) x =
    L.comp ((fderiv ℝ (A.field t : LiftTangent → LiftTangent) (J x)).comp J) at hd
  have hval : J (A.field t (J x)).1 = A.field t (J x) := by
    apply Prod.ext
    · rfl
    · exact (sub_eq_zero.mp (hgraph t (J x))).symm
  change (A₁.field t (J x)).1 +
    fderiv ℝ ((graphCoefficient k m T A).field t : Vector3 → Vector3) x (A.field t (J x)).1 = _
  rw [hd,comp_apply,comp_apply,hval]
  rfl


-- @@ L481-490 verbatim
include hgraph in
theorem graph_materialAcceleration_eq (t : Icc (0 : ℝ) T) (x : Vector3) :
    materialAcceleration T hT (graphCoefficient k m T A) (graphCoefficient k m T A₁) t x =
      (materialAcceleration T hT A A₁ t (graphLinear k m x)).1 := by
  unfold materialAcceleration
  rw [graph_accelerationField_eq k m T A A₁ hgraph]
  change (accelerationField T A A₁ t (graphLinear k m
    ((flowData T hT (graphCoefficient k m T A)).flow 0 t x))).1 = _
  rw [← graph_flow_cover k m T hT A hgraph]
  rfl


-- @@ L492-494 verbatim
/-- Physical coefficient, given by `scaledCoefficient T (graphCoefficient k m T A) ell`. -/
def physicalCoefficient (ell : ℝ) : SmoothTimeField (Icc (0 : ℝ) T) Vector3 Vector3 :=
  scaledCoefficient T (graphCoefficient k m T A) ell


-- @@ L496-498 verbatim
@[simp] theorem physicalCoefficient_apply (ell : ℝ) (t : Icc (0 : ℝ) T) (x : Vector3) :
    (physicalCoefficient k m T A ell).field t x = ell • (A.field t (graphLinear k m (ell⁻¹ • x))).1
        := rfl


-- @@ L500-505 verbatim
theorem physicalCoefficient_timeDerivative (ell : ℝ)
    (htime : SmoothTimeField.TimeDerivative T hT A A₁) :
    SmoothTimeField.TimeDerivative T hT (physicalCoefficient k m T A ell)
      (physicalCoefficient k m T A₁ ell) :=
  scaledCoefficient_timeDerivative T hT (graphCoefficient k m T A) ell
    (graphCoefficient k m T A₁) (graphCoefficient_timeDerivative k m T hT A A₁ htime)


-- @@ L507-513 verbatim
include hgraph in
theorem physical_flow_eq (ell : ℝ) (hell : ell ≠ 0) (s t : ℝ) (x : Vector3) :
    (flowData T hT (physicalCoefficient k m T A ell)).flow s t x =
      ell • ((flowData T hT A).flow s t (graphLinear k m (ell⁻¹ • x))).1 := by
  rw [physicalCoefficient,scaled_flow_eq T hT (graphCoefficient k m T A) ell hell]
  rw [← graph_flow_eq k m T hT A hgraph]
  rfl


-- @@ L515-521 verbatim
include hgraph in
theorem physical_displacement_eq (ell : ℝ) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    displacement T hT (physicalCoefficient k m T A ell) t x =
      ell • (displacement T hT A t (graphLinear k m (ell⁻¹ • x))).1 := by
  rw [physicalCoefficient,scaled_displacement_eq T hT (graphCoefficient k m T A) ell hell,
    ← graph_displacement_eq k m T hT A hgraph]


-- @@ L523-529 verbatim
include hgraph in
theorem physical_materialVelocity_eq (ell : ℝ) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    materialVelocity T hT (physicalCoefficient k m T A ell) t x =
      ell • (materialVelocity T hT A t (graphLinear k m (ell⁻¹ • x))).1 := by
  rw [physicalCoefficient,scaled_materialVelocity_eq T hT (graphCoefficient k m T A) ell hell,
    graph_materialVelocity_eq k m T hT A hgraph]


-- @@ L531-539 verbatim
include hgraph in
theorem physical_materialAcceleration_eq (ell : ℝ) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    materialAcceleration T hT (physicalCoefficient k m T A ell) (physicalCoefficient k m T A₁ ell)
        t x =
      ell • (materialAcceleration T hT A A₁ t (graphLinear k m (ell⁻¹ • x))).1 := by
  rw [physicalCoefficient,physicalCoefficient,
    scaled_materialAcceleration_eq T hT (graphCoefficient k m T A) ell
      (graphCoefficient k m T A₁) hell,graph_materialAcceleration_eq k m T hT A A₁ hgraph]


-- @@ L541-543 verbatim
variable (hdiv : ∀ t z,
  LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) z).toLinearMap =
      0)


-- @@ L545-551 verbatim
include hgraph hdiv in
theorem physicalCoefficient_trace_zero (ell : ℝ) (hell : ell ≠ 0)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    LinearMap.trace ℝ Vector3
      (fderiv ℝ ((physicalCoefficient k m T A ell).field t : Vector3 → Vector3) x).toLinearMap=0 :=
  scaledCoefficient_trace_zero T (graphCoefficient k m T A) ell hell
    (graphCoefficient_trace_zero k m T A hgraph hdiv) t x


-- @@ L553-558 verbatim
include hgraph hdiv in
theorem physical_forward_measurePreserving (ell : ℝ) (hell : ell ≠ 0) (t : Icc (0 : ℝ) T) :
    MeasurePreserving ((flowData T hT (physicalCoefficient k m T A ell)).forward t) volume volume
        := by
  exact forward_measurePreserving T hT (physicalCoefficient k m T A ell)
    (physicalCoefficient_trace_zero k m T A hgraph hdiv ell hell) volume t


-- @@ L560-560 verbatim
end EulerGraphInvariantFlow


-- @@ L562-562 verbatim
end

-- @@ L563-563 verbatim
end


-- @@ L565-565 verbatim
end


-- @@ L567-567 verbatim
section


-- @@ L569-570 verbatim
/-! A smooth periodic divergence-free cover velocity constructs an actual
volume-preserving cylinder flow with continuous inverse. -/


-- @@ L572-572 verbatim
section


-- @@ L574-575 verbatim
/-! The actual flow of a periodic cover velocity descends to a genuine
continuous cylinder flow with two-sided inverse. -/


-- @@ L577-577 verbatim
section


-- @@ L579-580 verbatim
/-! Periodicity of the prescribed velocity gives exact translation
equivariance of the constructed global flow, by ODE uniqueness. -/


-- @@ L582-582 verbatim
@[expose] public section


-- @@ L584-584 verbatim
noncomputable section


-- @@ L586-586 verbatim
namespace EulerBoundedLipschitzFlow.Data


-- @@ L588-589 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (V : EulerBoundedLipschitzFlow.Data E)


-- @@ L591-596 verbatim
theorem flow_add_eq (c : E) (hc : ∀ t x, V.velocity t (x + c) = V.velocity t x)
    (s t : ℝ) (x : E) : V.flow s t (x+c)=V.flow s t x+c := by
  have h := V.flow_unique s (x+c) (fun r => V.flow s r x+c)
    (fun r => by simpa only [hc] using (V.flow_hasDerivAt s r x).add_const c)
    (by rw [V.flow_initial])
  exact (congrFun h t).symm


-- @@ L598-598 verbatim
end EulerBoundedLipschitzFlow.Data


-- @@ L600-600 verbatim
end

-- @@ L601-601 verbatim
end


-- @@ L603-603 verbatim
end


-- @@ L605-605 verbatim
@[expose] public section


-- @@ L607-607 verbatim
noncomputable section


-- @@ L609-609 verbatim
namespace EulerCylinderPeriodicFlow


-- @@ L611-611 verbatim
open Set Function MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent


-- @@ L613-615 verbatim
variable (P : ℝ) [Fact (0 < P)] (V : EulerBoundedLipschitzFlow.Data LiftTangent)
  (hV : ∀ (c : AddSubgroup.zmultiples P) t z,
    V.velocity t (z.1, (c : ℝ) + z.2) = V.velocity t z)


-- @@ L617-627 verbatim
include hV in
omit [Fact (0 < P)] in
theorem flow_deck (s t : ℝ) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    V.flow s t (z.1,(c : ℝ)+z.2) = ((V.flow s t z).1,(c : ℝ)+(V.flow s t z).2) := by
  have shift (w : LiftTangent) : w+(0,(c : ℝ)) = (w.1,(c : ℝ)+w.2) := by
    apply Prod.ext <;> simp [add_comm]
  have hp : ∀ r w, V.velocity r (w+(0,(c : ℝ)))=V.velocity r w := by
    intro r w
    rw [shift]
    exact hV c r w
  simpa only [shift] using V.flow_add_eq (0,(c : ℝ)) hp s t z


-- @@ L629-630 verbatim
/-- Flow, given by `descendMap P (V.flow s t)`. -/
def flow (s t : ℝ) : LiftDomain P → LiftDomain P := descendMap P (V.flow s t)


-- @@ L632-635 verbatim
include hV in
theorem flow_cover (s t : ℝ) (z : LiftTangent) :
    flow P V s t (coveringMap P z) = coveringMap P (V.flow s t z) :=
  descendMap_cover P (V.flow s t) (flow_deck P V hV s t) z


-- @@ L637-639 verbatim
include hV in
theorem flow_continuous (s t : ℝ) : Continuous (flow P V s t) :=
  descendMap_continuous P (V.flow s t) (flow_deck P V hV s t) (V.flowHomeomorph s t).continuous


-- @@ L641-644 verbatim
include hV in
theorem flow_initial (s : ℝ) (q : LiftDomain P) : flow P V s s q=q := by
  obtain ⟨z,rfl⟩ := (coveringMap_isOpenQuotient P).surjective q
  rw [flow_cover P V hV,V.flow_initial]


-- @@ L646-649 verbatim
include hV in
theorem flow_inverse (s t : ℝ) : Function.LeftInverse (flow P V t s) (flow P V s t) :=
  descendMap_leftInverse P (V.flow s t) (flow_deck P V hV s t)
    (V.flow t s) (flow_deck P V hV t s) (V.flow_inverse s t)


-- @@ L651-655 verbatim
include hV in
theorem flow_cocycle (r s t : ℝ) (q : LiftDomain P) :
    flow P V s t (flow P V r s q)=flow P V r t q := by
  obtain ⟨z,rfl⟩ := (coveringMap_isOpenQuotient P).surjective q
  rw [flow_cover P V hV,flow_cover P V hV,flow_cover P V hV,V.flow_cocycle]


-- @@ L657-665 verbatim
/-- Flow homeomorph, bundling `toFun`, `invFun`, `left_inv`, `right_inv` and the required
compatibility proofs. -/
def flowHomeomorph (s t : ℝ) : LiftDomain P ≃ₜ LiftDomain P where
  toFun := flow P V s t
  invFun := flow P V t s
  left_inv := flow_inverse P V hV s t
  right_inv := flow_inverse P V hV t s
  continuous_toFun := flow_continuous P V hV s t
  continuous_invFun := flow_continuous P V hV t s


-- @@ L667-672 verbatim
include hV in
theorem forward_joint_continuous : Continuous (fun z : ℝ × LiftDomain P => flow P V 0 z.1 z.2) := by
  have hf : Continuous (fun z : ℝ × LiftTangent => coveringMap P (V.forward z.1 z.2)) :=
    (coveringMap_isOpenQuotient P).continuous.comp V.forward_joint_continuous
  exact descend_joint_continuous P (fun t z => coveringMap P (V.forward t z)) hf
    (fun t => map_fiber_constant P (V.flow 0 t) (flow_deck P V hV 0 t))


-- @@ L674-680 verbatim
include hV in
theorem backward_joint_continuous : Continuous (fun z : ℝ × LiftDomain P => flow P V z.1 0 z.2) :=
    by
  have hf : Continuous (fun z : ℝ × LiftTangent => coveringMap P (V.backward z.1 z.2)) :=
    (coveringMap_isOpenQuotient P).continuous.comp V.backward_joint_continuous
  exact descend_joint_continuous P (fun t z => coveringMap P (V.backward t z)) hf
    (fun t => map_fiber_constant P (V.flow t 0) (flow_deck P V hV t 0))


-- @@ L682-685 verbatim
include hV in
theorem flow_measurePreserving (s t : ℝ) (hf : MeasurePreserving (V.flow s t) volume volume) :
    MeasurePreserving (flow P V s t) (liftMeasure P) (liftMeasure P) :=
  descendMap_measurePreserving P (V.flow s t) (flow_deck P V hV s t) hf


-- @@ L687-687 verbatim
end EulerCylinderPeriodicFlow


-- @@ L689-689 verbatim
end

-- @@ L690-690 verbatim
end


-- @@ L692-692 verbatim
end


-- @@ L694-694 verbatim
@[expose] public section


-- @@ L696-696 verbatim
noncomputable section


-- @@ L698-698 verbatim
namespace EulerSmoothCylinderFlow


-- @@ L700-700 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerSmoothBanachFlow


-- @@ L702-705 verbatim
local instance instSmoothCylinderFlow1 : Measure.IsAddHaarMeasure (volume : Measure LiftTangent) :=
    by
  change Measure.IsAddHaarMeasure ((volume : Measure Vector3).prod (volume : Measure ℝ))
  infer_instance


-- @@ L707-710 verbatim
variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)


-- @@ L712-716 verbatim
include hA in
omit [Fact (0 < P)] in
theorem velocity_deck (c : AddSubgroup.zmultiples P) (t : ℝ) (z : LiftTangent) :
    (flowData T hT A).velocity t (z.1,(c : ℝ)+z.2)=(flowData T hT A).velocity t z :=
  hA c (projIcc 0 T hT t) z


-- @@ L718-720 verbatim
/-- Forward, given by `EulerCylinderPeriodicFlow.flow P (flowData T hT A) 0 t`. -/
def forward (t : ℝ) : LiftDomain P → LiftDomain P :=
  EulerCylinderPeriodicFlow.flow P (flowData T hT A) 0 t


-- @@ L722-724 verbatim
/-- Backward, given by `EulerCylinderPeriodicFlow.flow P (flowData T hT A) t 0`. -/
def backward (t : ℝ) : LiftDomain P → LiftDomain P :=
  EulerCylinderPeriodicFlow.flow P (flowData T hT A) t 0


-- @@ L726-729 verbatim
include hA in
theorem forward_cover (t : ℝ) (z : LiftTangent) :
    forward P T hT A t (coveringMap P z)=coveringMap P ((flowData T hT A).forward t z) :=
  EulerCylinderPeriodicFlow.flow_cover P (flowData T hT A) (velocity_deck P T hT A hA) 0 t z


-- @@ L731-734 verbatim
include hA in
theorem backward_cover (t : ℝ) (z : LiftTangent) :
    backward P T hT A t (coveringMap P z)=coveringMap P ((flowData T hT A).backward t z) :=
  EulerCylinderPeriodicFlow.flow_cover P (flowData T hT A) (velocity_deck P T hT A hA) t 0 z


-- @@ L736-738 verbatim
include hA in
theorem forward_joint_continuous : Continuous (Function.uncurry (forward P T hT A)) :=
  EulerCylinderPeriodicFlow.forward_joint_continuous P (flowData T hT A) (velocity_deck P T hT A hA)


-- @@ L740-743 verbatim
include hA in
theorem backward_joint_continuous : Continuous (Function.uncurry (backward P T hT A)) :=
  EulerCylinderPeriodicFlow.backward_joint_continuous P (flowData T hT A) (velocity_deck P T hT A
      hA)


-- @@ L745-748 verbatim
include hA in
theorem backward_forward (t : ℝ) : Function.LeftInverse (backward P T hT A t) (forward P T hT A t)
    :=
  EulerCylinderPeriodicFlow.flow_inverse P (flowData T hT A) (velocity_deck P T hT A hA) 0 t


-- @@ L750-753 verbatim
include hA in
theorem forward_backward (t : ℝ) : Function.RightInverse (backward P T hT A t) (forward P T hT A t)
    :=
  EulerCylinderPeriodicFlow.flow_inverse P (flowData T hT A) (velocity_deck P T hT A hA) t 0


-- @@ L755-757 verbatim
variable (hdiv : ∀ t x,
  LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) x).toLinearMap =
      0)


-- @@ L759-764 verbatim
include hA hdiv in
theorem forward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving (forward P T hT A t) (liftMeasure P) (liftMeasure P) :=
  EulerCylinderPeriodicFlow.flow_measurePreserving P (flowData T hT A) (velocity_deck P T hT A hA)
      0 t
    (EulerSmoothBanachFlow.forward_measurePreserving T hT A hdiv volume t)


-- @@ L766-771 verbatim
include hA hdiv in
theorem backward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving (backward P T hT A t) (liftMeasure P) (liftMeasure P) :=
  EulerCylinderPeriodicFlow.flow_measurePreserving P (flowData T hT A) (velocity_deck P T hT A hA)
      t 0
    (EulerSmoothBanachFlow.backward_measurePreserving T hT A hdiv volume t)


-- @@ L773-773 verbatim
end EulerSmoothCylinderFlow


-- @@ L775-775 verbatim
end

-- @@ L776-776 verbatim
end


-- @@ L778-778 verbatim
end


-- @@ L780-780 verbatim
section


-- @@ L782-783 verbatim
/-! Actual L² composition of any smooth periodic field with the
constructed cylinder flow. The outer amplitude is retained. -/


-- @@ L785-785 verbatim
@[expose] public section


-- @@ L787-787 verbatim
noncomputable section


-- @@ L789-789 verbatim
namespace EulerSmoothCylinderFlow


-- @@ L791-792 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey

-- @@ L793-793 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L795-799 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderComposition1 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance

-- @@ L800-804 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderComposition2 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ] LiftTangent))
    := inferInstance

-- @@ L805-808 verbatim
/-- The `MeasurableSpace (LiftTangent [×n]→L[ℝ] LiftTangent)` structure used in smooth cylinder
composition. -/
local instance instSmoothCylinderComposition3 (n : ℕ) : MeasurableSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := borel _

-- @@ L809-810 verbatim
local instance instSmoothCylinderComposition4 (n : ℕ) : BorelSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := ⟨rfl⟩

-- @@ L811-816 verbatim
local instance instSmoothCylinderComposition5 (n : ℕ) : FiniteDimensional ℝ (LiftTangent [×n]→L[ℝ]
    LiftTangent) := by
  let J : (LiftTangent [×n]→L[ℝ] LiftTangent) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin n => LiftTangent) LiftTangent :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective


-- @@ L818-824 verbatim
variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)
  (hdiv : ∀ t x,
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent)
        x).toLinearMap = 0)


-- @@ L826-859 verbatim
include hA hdiv in
theorem composeJet_memLp_and_bound
    (f : LiftTangent → LiftTangent) (hf : ContDiff ℝ ∞ f)
    (hperiod : ∀ (c : AddSubgroup.zmultiples P) z, f (z.1, (c : ℝ) + z.2) = f z)
    (B R C S : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ)
    (hLp : ∀ j ≤ n, MemLp (fun q => jetSeries P f q j) 2 (liftMeasure P))
    (hNorm : ∀ j ≤ n,
      (eLpNorm (fun q => jetSeries P f q j) 2 (liftMeasure P)).toReal ≤ C * S ^ j * (j.factorial :
          ℝ)
          ^
          2)
    (t : Icc (0 : ℝ) T) :
    MemLp (fun q => jetSeries P (f ∘ (flowData T hT A).forward t) q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (f ∘ (flowData T hT A).forward t) q n)
        2 (liftMeasure P)).toReal ≤ C*(flowRadius B R T S)^n*(n.factorial : ℝ)^2 := by
  have he : (fun q => jetSeries P (f ∘ (flowData T hT A).forward t) q n) =
      fun q => (jetSeries P f (forward P T hT A t q)).taylorComp
        (jetSeries P ((flowData T hT A).forward t) q) n :=
    funext (fun q => jetSeries_comp P f hperiod ((flowData T hT A).forward t)
      hf (forward_contDiff T hT A t) q n)
  have hm : AEStronglyMeasurable
      (fun q => jetSeries P (f ∘ (flowData T hT A).forward t) q n) (liftMeasure P) :=
    (((hf.comp (forward_contDiff T hT A t)).continuous_iteratedFDeriv
      (m := n) (by simp)).measurable.comp (sectionPoint_measurable P)).aestronglyMeasurable
  rw [he] at hm ⊢
  apply EulerGevreyJetCompositionLp.composition_memLp_and_bound (liftMeasure P)
    (forward P T hT A t) (forward_measurePreserving P T hT A hA hdiv t)
    (jetSeries P ((flowData T hT A).forward t)) (jetSeries P f) n hm
    C (1+B*T) (4*R+1) S hC (by positivity) (by positivity) hS hLp hNorm
  intro j hj _ q
  exact forward_positive_bound T hT A B R hB hR hsmall hb j hj t (sectionPoint P q)


-- @@ L861-861 verbatim
end EulerSmoothCylinderFlow


-- @@ L863-863 verbatim
end

-- @@ L864-864 verbatim
end


-- @@ L866-866 verbatim
end


-- @@ L868-868 verbatim
section


-- @@ L870-871 verbatim
/-! The actual composed acceleration field of the constructed periodic
flow has L² Gevrey jets with its original source amplitudes. -/


-- @@ L873-873 verbatim
section


-- @@ L875-877 verbatim
/-! The actual material acceleration has cylinder L² bounds with the
small source amplitudes retained. The product term uses one bounded
derivative coefficient and one L² velocity factor. -/


-- @@ L879-879 verbatim
@[expose] public section


-- @@ L881-881 verbatim
noncomputable section


-- @@ L883-883 verbatim
namespace EulerSmoothCylinderFlow


-- @@ L885-886 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey EulerGevrey EulerOperatorGevreyCalculus

-- @@ L887-887 verbatim
open scoped ContDiff BoundedContinuousFunction ENNReal


-- @@ L889-893 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderAccelerationLp1 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance

-- @@ L894-898 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderAccelerationLp2 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ] LiftTangent))
    := inferInstance

-- @@ L899-902 verbatim
/-- The `MeasurableSpace (LiftTangent [×n]→L[ℝ] LiftTangent)` structure used in smooth cylinder
acceleration lᵖ. -/
local instance instSmoothCylinderAccelerationLp3 (n : ℕ) : MeasurableSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := borel _

-- @@ L903-904 verbatim
local instance instSmoothCylinderAccelerationLp4 (n : ℕ) : BorelSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := ⟨rfl⟩

-- @@ L905-910 verbatim
local instance instSmoothCylinderAccelerationLp5 (n : ℕ) : FiniteDimensional ℝ (LiftTangent
    [×n]→L[ℝ] LiftTangent) := by
  let J : (LiftTangent [×n]→L[ℝ] LiftTangent) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin n => LiftTangent) LiftTangent :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective


-- @@ L912-913 verbatim
variable (P T : ℝ) [Fact (0 < P)]
  (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)


-- @@ L915-916 verbatim
/-- Acceleration Lᵖ radius, given by `4*R+S+S₁`. -/
def accelerationLpRadius (R S S₁ : ℝ) : ℝ := 4*R+S+S₁


-- @@ L918-1013 verbatim
theorem accelerationField_memLp_and_bound (B R C S C₁ S₁ : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hC₁ : 0 ≤ C₁) (hS₁ : 0 ≤ S₁)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hLp : ∀ (t : Icc (0 : ℝ) T) j,
      MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm : ∀ (t : Icc (0 : ℝ) T) j,
      (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C * S ^ j * (j.factorial : ℝ) ^ 2)
    (hLp₁ : ∀ (t : Icc (0 : ℝ) T) j,
      MemLp (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm₁ : ∀ (t : Icc (0 : ℝ) T) j,
      (eLpNorm (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C₁ * S₁ ^ j * (j.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    MemLp (fun q => jetSeries P (accelerationField T A A₁ t) q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (accelerationField T A A₁ t) q n)
        2 (liftMeasure P)).toReal ≤
          (C₁+3*B*R*C)*(accelerationLpRadius R S S₁)^n*(n.factorial : ℝ)^2 := by
  let U := accelerationLpRadius R S S₁
  have hU : 0 ≤ U := by dsimp [U,accelerationLpRadius]; positivity
  have hRU : 4*R ≤ U := by dsimp [U,accelerationLpRadius]; linarith
  have hSU : S ≤ U := by dsimp [U,accelerationLpRadius]; linarith
  have hS₁U : S₁ ≤ U := by dsimp [U,accelerationLpRadius]; linarith
  let f : LiftTangent → LiftTangent →L[ℝ] LiftTangent := fderiv ℝ (A.field t : LiftTangent →
      LiftTangent)
  let g : LiftTangent → LiftTangent := A.field t
  have hf : ContDiff ℝ ∞ f := (A.smooth t).fderiv_right (m := ∞) (by simp)
  have hg : ContDiff ℝ ∞ g := A.smooth t
  have hfB (j : ℕ) (q : LiftDomain P) :
      ‖iteratedFDeriv ℝ j f (sectionPoint P q)‖ ≤ (B*R)*majorant U 0 j := by
    rw [norm_iteratedFDeriv_fderiv]
    have h := field_jet_bound T A B R hb (j+1) t (sectionPoint P q)
    calc
      _ ≤ B*majorant R 1 j := by simpa only [majorant,mul_assoc] using h
      _ ≤ B*(R*majorant (4*R) 0 j) :=
        mul_le_mul_of_nonneg_left (majorant_one_le_radius_four R hR j) hB
      _ ≤ (B*R)*majorant U 0 j := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (majorant_radius_mono (4*R) U (by positivity) hRU 0 j)
          (mul_nonneg hB hR)
  have hgC (j : ℕ) :
      (eLpNorm (fun q => iteratedFDeriv ℝ j g (sectionPoint P q)) 2 (liftMeasure P)).toReal ≤
        C*majorant U 0 j := by
    calc
      _ ≤ C*S^j*(j.factorial : ℝ)^2 := hNorm t j
      _ = C*majorant S 0 j := by simp only [majorant,Nat.add_zero,mul_assoc]
      _ ≤ C*majorant U 0 j :=
        mul_le_mul_of_nonneg_left (majorant_radius_mono S U hS hSU 0 j) hC
  have hm : AEStronglyMeasurable
      (fun q => iteratedFDeriv ℝ n (fun y => f y (g y)) (sectionPoint P q)) (liftMeasure P) :=
    (((hf.clm_apply hg).continuous_iteratedFDeriv (m := n) (by simp)).measurable.comp
      (sectionPoint_measurable P)).aestronglyMeasurable
  obtain ⟨hp,hn⟩ := EulerGevreyProductLp.clm_apply_memLp_and_bound (liftMeasure P) (sectionPoint P)
    f g hf hg n hm U (B*R) C hU (mul_nonneg hB hR) hC 0 0
    (fun j _ => hfB j) (fun j _ => hLp t j) (fun j _ => hgC j)
  let v : LiftDomain P → LiftTangent [×n]→L[ℝ] LiftTangent :=
    fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q n
  let w : LiftDomain P → LiftTangent [×n]→L[ℝ] LiftTangent :=
    fun q => iteratedFDeriv ℝ n (fun y => f y (g y)) (sectionPoint P q)
  have he : (fun q => jetSeries P (accelerationField T A A₁ t) q n) = v+w := by
    funext q
    exact fun_iteratedFDeriv_add_apply ((A₁.smooth t).contDiffAt.of_le (by simp))
      ((hf.clm_apply hg).contDiffAt.of_le (by simp))
  have hv : MemLp v 2 (liftMeasure P) := hLp₁ t n
  have hw : MemLp w 2 (liftMeasure P) := hp
  let H : Fin 2 → LiftDomain P → ℝ := fun i q => if i=0 then ‖v q‖ else ‖w q‖
  have hH (i : Fin 2) : MemLp (H i) 2 (liftMeasure P) := by
    fin_cases i
    · exact hv.norm
    · exact hw.norm
  have hmacc : AEStronglyMeasurable
      (fun q => jetSeries P (accelerationField T A A₁ t) q n) (liftMeasure P) :=
    (((accelerationField_contDiff T A A₁ t).continuous_iteratedFDeriv (m := n) (by
        simp)).measurable.comp
      (sectionPoint_measurable P)).aestronglyMeasurable
  have hdom (q : LiftDomain P) : ‖jetSeries P (accelerationField T A A₁ t) q n‖ ≤
      ∑ i : Fin 2, H i q := by
    rw [congrFun he q]
    simpa only [Fin.sum_univ_two,H,ite_true,Fin.isValue,one_ne_zero,ite_false,Pi.add_apply]
      using norm_add_le (v q) (w q)
  obtain ⟨hacc,hreal⟩ := EulerGevreyProductLp.finite_domination (liftMeasure P) Finset.univ
    (fun q => jetSeries P (accelerationField T A A₁ t) q n) hmacc H (fun i _ => hH i) hdom
  refine ⟨hacc,?_⟩
  have hreal' : (eLpNorm (fun q => jetSeries P (accelerationField T A A₁ t) q n)
      2 (liftMeasure P)).toReal ≤ (eLpNorm v 2 (liftMeasure P)).toReal+(eLpNorm w 2 (liftMeasure
          P)).toReal := by
    simpa only [Fin.sum_univ_two,H,ite_true,Fin.isValue,one_ne_zero,ite_false,
      eLpNorm_norm _ hv.aestronglyMeasurable, eLpNorm_norm _ hw.aestronglyMeasurable] using
        hreal
  have hn₁ : (eLpNorm v 2 (liftMeasure P)).toReal ≤ C₁*majorant U 0 n := by
    apply (hNorm₁ t n).trans
    simpa only [majorant,Nat.add_zero,mul_assoc] using
      mul_le_mul_of_nonneg_left (majorant_radius_mono S₁ U hS₁ hS₁U 0 n) hC₁
  exact hreal'.trans ((add_le_add hn₁ hn).trans_eq (by
    simp only [majorant,Nat.add_zero]; dsimp [U]; ring))


-- @@ L1015-1018 verbatim
variable (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)
  (hA₁ : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A₁.field t (z.1, (c : ℝ) + z.2) = A₁.field t z)


-- @@ L1020-1032 verbatim
include hA hA₁ in
omit [Fact (0 < P)] in
theorem accelerationField_deck (t : Icc (0 : ℝ) T) (c : AddSubgroup.zmultiples P) (z : LiftTangent)
    :
    accelerationField T A A₁ t (z.1,(c : ℝ)+z.2)=accelerationField T A A₁ t z := by
  have hd : fderiv ℝ (A.field t : LiftTangent → LiftTangent) (z.1,(c : ℝ)+z.2) =
      fderiv ℝ (A.field t : LiftTangent → LiftTangent) z := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun L : LiftTangent [×1]→L[ℝ] LiftTangent => L (fun _ => v))
      (iteratedFDeriv_deck P (A.field t : LiftTangent → LiftTangent) (fun d w => hA d t w) 1 c z)
    simpa only [iteratedFDeriv_one_apply] using h
  simp only [accelerationField,hA,hA₁,hd]


-- @@ L1034-1034 verbatim
end EulerSmoothCylinderFlow


-- @@ L1036-1036 verbatim
end

-- @@ L1037-1037 verbatim
end


-- @@ L1039-1039 verbatim
end


-- @@ L1041-1041 verbatim
@[expose] public section


-- @@ L1043-1043 verbatim
noncomputable section


-- @@ L1045-1045 verbatim
namespace EulerSmoothCylinderFlow


-- @@ L1047-1048 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey

-- @@ L1049-1049 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L1051-1055 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderAccelerationComposition1 (n : ℕ) : NormedAddCommGroup (LiftTangent
    →ᵇ (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance

-- @@ L1056-1060 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderAccelerationComposition2 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ] LiftTangent))
    := inferInstance


-- @@ L1062-1070 verbatim
variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)
  (hA₁ : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A₁.field t (z.1, (c : ℝ) + z.2) = A₁.field t z)
  (hdiv : ∀ t x,
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent)
        x).toLinearMap = 0)


-- @@ L1072-1075 verbatim
/-- Material acceleration jet, given by `jetSeries P (materialAcceleration T hT A A₁ t) q n`. -/
def materialAccelerationJet (t : Icc (0 : ℝ) T) (q : LiftDomain P) (n : ℕ) :
    LiftTangent [×n]→L[ℝ] LiftTangent :=
  jetSeries P (materialAcceleration T hT A A₁ t) q n


-- @@ L1077-1085 verbatim
include hA hA₁ in
theorem materialAccelerationJet_local (t : Icc (0 : ℝ) T) (q : LiftDomain P) (n : ℕ) :
    materialAccelerationJet P T hT A A₁ t q n =
      iteratedFDeriv ℝ n (EulerMetricTransport.localFieldLift P
        (descend P (materialAcceleration T hT A A₁ t)) q) 0 := by
  apply jetSeries_eq_local
  exact comp_deck P (accelerationField T A A₁ t)
    (accelerationField_deck P T A A₁ hA hA₁ t) ((flowData T hT A).forward t)
    (EulerCylinderPeriodicFlow.flow_deck P (flowData T hT A) (velocity_deck P T hT A hA) 0 t)


-- @@ L1087-1113 verbatim
include hA hA₁ hdiv in
theorem materialAccelerationJet_memLp_and_bound (B R C S C₁ S₁ : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hC₁ : 0 ≤ C₁) (hS₁ : 0 ≤ S₁) (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hLp : ∀ (t : Icc (0 : ℝ) T) j,
      MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm : ∀ (t : Icc (0 : ℝ) T) j,
      (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C * S ^ j * (j.factorial : ℝ) ^ 2)
    (hLp₁ : ∀ (t : Icc (0 : ℝ) T) j,
      MemLp (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm₁ : ∀ (t : Icc (0 : ℝ) T) j,
      (eLpNorm (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C₁ * S₁ ^ j * (j.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    MemLp (fun q => materialAccelerationJet P T hT A A₁ t q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => materialAccelerationJet P T hT A A₁ t q n)
        2 (liftMeasure P)).toReal ≤
          (C₁+3*B*R*C)*(flowRadius B R T (accelerationLpRadius R S S₁))^n*(n.factorial : ℝ)^2 := by
  have hout := accelerationField_memLp_and_bound P T A A₁ B R C S C₁ S₁
    hB hR.le hC hS hC₁ hS₁ hb hLp hNorm hLp₁ hNorm₁
  apply composeJet_memLp_and_bound P T hT A hA hdiv (accelerationField T A A₁ t)
    (accelerationField_contDiff T A A₁ t) (accelerationField_deck P T A A₁ hA hA₁ t)
    B R (C₁+3*B*R*C) (accelerationLpRadius R S S₁)
    hB hR (by positivity) (by unfold accelerationLpRadius; positivity)
    hsmall hb n (fun j _ => (hout j t).1) (fun j _ => (hout j t).2) t


-- @@ L1115-1115 verbatim
end EulerSmoothCylinderFlow


-- @@ L1117-1117 verbatim
end

-- @@ L1118-1118 verbatim
end


-- @@ L1120-1120 verbatim
end


-- @@ L1122-1122 verbatim
section


-- @@ L1124-1126 verbatim
/-! Actual periodic displacement jets and their differentiated integral
equation. The real covering displacement is periodic, so its descent is
a vector-valued field, including its angular displacement component. -/


-- @@ L1128-1128 verbatim
@[expose] public section


-- @@ L1130-1130 verbatim
noncomputable section


-- @@ L1132-1132 verbatim
namespace EulerSmoothCylinderFlow


-- @@ L1134-1135 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerFinitePathTensor EulerVolterraConvolution

-- @@ L1136-1136 verbatim
open scoped ContDiff Interval


-- @@ L1138-1141 verbatim
/-- The `MeasurableSpace (LiftTangent [×n]→L[ℝ] LiftTangent)` structure used in smooth cylinder
jets. -/
local instance instSmoothCylinderJets1 (n : ℕ) : MeasurableSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := borel _

-- @@ L1142-1143 verbatim
local instance instSmoothCylinderJets2 (n : ℕ) : BorelSpace (LiftTangent [×n]→L[ℝ] LiftTangent) :=
    ⟨rfl⟩


-- @@ L1145-1148 verbatim
variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)


-- @@ L1150-1151 verbatim
/-- Velocity cover, given by `A.field (projIcc 0 T hT t)`. -/
def velocityCover (t : ℝ) : LiftTangent → LiftTangent := A.field (projIcc 0 T hT t)


-- @@ L1153-1155 verbatim
/-- Forward cover, given by `(flowData T hT A).forward (projIcc 0 T hT t)`. -/
def forwardCover (t : ℝ) : LiftTangent → LiftTangent :=
  (flowData T hT A).forward (projIcc 0 T hT t)


-- @@ L1157-1163 verbatim
include hA in
omit [Fact (0 < P)] in
theorem forwardCover_deck (t : ℝ) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    forwardCover T hT A t (z.1,(c : ℝ)+z.2) =
      ((forwardCover T hT A t z).1,(c : ℝ)+(forwardCover T hT A t z).2) :=
  EulerCylinderPeriodicFlow.flow_deck P (flowData T hT A) (velocity_deck P T hT A hA)
    0 (projIcc 0 T hT t) c z


-- @@ L1165-1173 verbatim
include hA in
omit [Fact (0 < P)] in
theorem coverDisplacement_deck (t : ℝ) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    EulerSmoothBanachFlow.displacement T hT A t (z.1,(c : ℝ)+z.2) =
      EulerSmoothBanachFlow.displacement T hT A t z := by
  change forwardCover T hT A t (z.1,(c : ℝ)+z.2)-(z.1,(c : ℝ)+z.2) =
    forwardCover T hT A t z-z
  rw [forwardCover_deck P T hT A hA]
  apply Prod.ext <;> simp


-- @@ L1175-1177 verbatim
/-- Displacement, given by `descend P (EulerSmoothBanachFlow.displacement T hT A t)`. -/
def displacement (t : ℝ) : LiftDomain P → LiftTangent :=
  descend P (EulerSmoothBanachFlow.displacement T hT A t)


-- @@ L1179-1181 verbatim
/-- Displacement jet, given by `jetSeries P (EulerSmoothBanachFlow.displacement T hT A t) q n`. -/
def displacementJet (t : ℝ) (q : LiftDomain P) (n : ℕ) : LiftTangent [×n]→L[ℝ] LiftTangent :=
  jetSeries P (EulerSmoothBanachFlow.displacement T hT A t) q n


-- @@ L1183-1186 verbatim
/-- Composition jet as an element of `LiftTangent [×n]→L[ℝ] LiftTangent`. -/
def compositionJet (t : ℝ) (q : LiftDomain P) (n : ℕ) : LiftTangent [×n]→L[ℝ] LiftTangent :=
  (jetSeries P (velocityCover T hT A t) (forward P T hT A (projIcc 0 T hT t) q)).taylorComp
    (jetSeries P (forwardCover T hT A t) q) n


-- @@ L1188-1191 verbatim
include hA in
theorem displacement_cover (t : ℝ) (z : LiftTangent) :
    displacement P T hT A t (coveringMap P z)=EulerSmoothBanachFlow.displacement T hT A t z :=
  descend_cover P _ (fiber_constant_of_deck P _ (coverDisplacement_deck P T hT A hA t)) z


-- @@ L1193-1197 verbatim
include hA in
theorem displacement_smooth (t : ℝ) (q : LiftDomain P) :
    ContDiff ℝ ∞ (EulerMetricTransport.localFieldLift P (displacement P T hT A t) q) :=
  descend_smooth P _ (coverDisplacement_deck P T hT A hA t)
    (EulerSmoothBanachFlow.displacement_contDiff T hT A t) q


-- @@ L1199-1203 verbatim
include hA in
theorem displacementJet_local (t : ℝ) (q : LiftDomain P) (n : ℕ) :
    displacementJet P T hT A t q n =
      iteratedFDeriv ℝ n (EulerMetricTransport.localFieldLift P (displacement P T hT A t) q) 0 :=
  jetSeries_eq_local P _ (coverDisplacement_deck P T hT A hA t) q n


-- @@ L1205-1211 verbatim
include hA in
theorem compositionJet_eq (t : ℝ) (q : LiftDomain P) (n : ℕ) :
    compositionJet P T hT A t q n =
      iteratedFDeriv ℝ n (velocityCover T hT A t ∘ forwardCover T hT A t) (sectionPoint P q) := by
  exact (jetSeries_comp P (velocityCover T hT A t)
    (fun c z => hA c (projIcc 0 T hT t) z) (forwardCover T hT A t)
    (A.smooth _) (forward_contDiff T hT A _) q n).symm


-- @@ L1213-1218 verbatim
include hA in
theorem compositionJet_path (t : ℝ) (q : LiftDomain P) (n : ℕ) :
    compositionJet P T hT A t q n =
      extendPath T hT (velocityJetPath T hT A n (sectionPoint P q)) t := by
  rw [compositionJet_eq P T hT A hA]
  exact (velocityJetPath_apply T hT A n (sectionPoint P q) (projIcc 0 T hT t)).symm


-- @@ L1220-1223 verbatim
theorem displacementJet_path (t : ℝ) (q : LiftDomain P) (n : ℕ) :
    displacementJet P T hT A t q n =
      extendPath T hT (displacementJetPath T hT A n (sectionPoint P q)) t :=
  (displacementJetPath_apply T hT A n (sectionPoint P q) t).symm


-- @@ L1225-1233 verbatim
include hA in
theorem displacementJet_integral (t : Icc (0 : ℝ) T) (q : LiftDomain P) (n : ℕ) :
    displacementJet P T hT A t q n = ∫ s in (0 : ℝ)..(t : ℝ), compositionJet P T hT A s q n := by
  rw [displacementJet_path,displacementJetPath_integral]
  simp only [extendPath,projIcc_of_mem hT t.property,EulerContinuousTimeIntegral.integral_apply,
    EulerContinuousTimeIntegral.realIntegral]
  apply intervalIntegral.integral_congr
  intro s _
  exact (compositionJet_path P T hT A hA s q n).symm


-- @@ L1235-1239 verbatim
omit [Fact (0 < P)] in
theorem velocityJetPath_label_continuous (n : ℕ) :
    Continuous (velocityJetPath T hT A n) :=
  (tensorPathMap n).continuous.comp
    (ContDiff.continuous_iteratedFDeriv (by simp) (velocityFamily_contDiff T hT A))


-- @@ L1241-1245 verbatim
omit [Fact (0 < P)] in
theorem displacementJetPath_label_continuous (n : ℕ) :
    Continuous (displacementJetPath T hT A n) :=
  (tensorPathMap n).continuous.comp
    (ContDiff.continuous_iteratedFDeriv (by simp) (displacementFamily_contDiff T hT A))


-- @@ L1247-1256 verbatim
include hA in
theorem compositionJet_joint_measurable (n : ℕ) :
    Measurable (fun z : ℝ × LiftDomain P => compositionJet P T hT A z.1 z.2 n) := by
  have hc : Continuous (fun z : ℝ × LiftTangent =>
      extendPath T hT (velocityJetPath T hT A n z.2) z.1) :=
    ((velocityJetPath_label_continuous T hT A n).comp continuous_snd).eval
      (continuous_projIcc.comp continuous_fst)
  have hm := hc.measurable.comp (measurable_fst.prodMk
    ((sectionPoint_measurable P).comp measurable_snd))
  simpa only [compositionJet_path P T hT A hA,Function.comp_def] using hm


-- @@ L1258-1266 verbatim
theorem displacementJet_joint_measurable (n : ℕ) :
    Measurable (fun z : ℝ × LiftDomain P => displacementJet P T hT A z.1 z.2 n) := by
  have hc : Continuous (fun z : ℝ × LiftTangent =>
      extendPath T hT (displacementJetPath T hT A n z.2) z.1) :=
    ((displacementJetPath_label_continuous T hT A n).comp continuous_snd).eval
      (continuous_projIcc.comp continuous_fst)
  have hm := hc.measurable.comp (measurable_fst.prodMk
    ((sectionPoint_measurable P).comp measurable_snd))
  simpa only [displacementJet_path,Function.comp_def] using hm


-- @@ L1268-1268 verbatim
end EulerSmoothCylinderFlow


-- @@ L1270-1270 verbatim
end

-- @@ L1271-1271 verbatim
end


-- @@ L1273-1273 verbatim
end


-- @@ L1275-1275 verbatim
section


-- @@ L1277-1279 verbatim
/-! The actual periodic flow displacement has simultaneous uniform and
L² Gevrey bounds. The L² estimate uses the cylinder's own Haar measure
and the differentiated equation of the constructed flow. -/


-- @@ L1281-1281 verbatim
section


-- @@ L1283-1286 verbatim
/-! The all-order L² step for a volume-preserving flow.  The spatial base
may be a periodic cylinder.  The output is the actual time integral of
the finite Taylor composition; identifying it with the displacement jet
uses the already constructed flow's differentiated integral equation. -/


-- @@ L1288-1288 verbatim
@[expose] public section


-- @@ L1290-1290 verbatim
noncomputable section


-- @@ L1292-1292 verbatim
open Set MeasureTheory Filter

-- @@ L1293-1293 verbatim
open scoped ENNReal Interval


-- @@ L1295-1295 verbatim
namespace EulerGevreyFlowLpIntegration


-- @@ L1297-1299 verbatim
variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L1301-1332 verbatim
/-- Uniform positive inner-jet bounds and the outer L² bounds imply an
L² bound for the actual integrated composition at every finite order. -/
theorem integrated_composition_bound
    (T : ℝ) (hT : 0 ≤ T) (μ : Measure X) [SFinite μ]
    (φ : ℝ → X → X) (hφ : ∀ t ∈ Icc 0 T, MeasurePreserving (φ t) μ μ)
    (P : ℝ → X → FormalMultilinearSeries ℝ E E)
    (Q : ℝ → X → FormalMultilinearSeries ℝ E F) (n : ℕ)
    (hm : AEStronglyMeasurable
      (fun p : ℝ × X => (Q p.1 (φ p.1 p.2)).taylorComp (P p.1 p.2) n)
      ((volume.restrict (Icc 0 T)).prod μ))
    (A B R S : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hQLp : ∀ t ∈ Icc 0 T, ∀ j ≤ n, MemLp (fun x => Q t x j) 2 μ)
    (hQ : ∀ t ∈ Icc 0 T, ∀ j ≤ n,
      (eLpNorm (fun x => Q t x j) 2 μ).toReal ≤ A*S^j*(j.factorial : ℝ)^2)
    (hP : ∀ t ∈ Icc 0 T, ∀ j, 0 < j → j ≤ n → ∀ x,
      ‖P t x j‖ ≤ B*R^j*(j.factorial : ℝ)^2) :
    MemLp (fun x => ∫ t in 0..T, (Q t (φ t x)).taylorComp (P t x) n) 2 μ ∧
      (eLpNorm (fun x => ∫ t in 0..T, (Q t (φ t x)).taylorComp (P t x) n) 2 μ).toReal ≤
        T*A*(R*(B*S+2))^n*(n.factorial : ℝ)^2 := by
  let C := A*(R*(B*S+2))^n*(n.factorial : ℝ)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      MemLp (fun x => (Q t (φ t x)).taylorComp (P t x) n) 2 μ ∧
        (eLpNorm (fun x => (Q t (φ t x)).taylorComp (P t x) n) 2 μ).toReal ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hm.prodMk_left] with t ht hmt
    exact EulerGevreyJetCompositionLp.composition_memLp_and_bound μ (φ t) (hφ t ht)
      (P t) (Q t) n hmt A B R S hA hB hR hS (hQLp t ht) (hQ t ht) (hP t ht)
  obtain ⟨hLp,hNorm⟩ := EulerLpParameterIntegral.intervalIntegral_memLp_and_bound
    T hT μ (fun p : ℝ × X => (Q p.1 (φ p.1 p.2)).taylorComp (P p.1 p.2) n) hm C hC hbound
  refine ⟨hLp,hNorm.trans_eq ?_⟩
  dsimp [C]
  ring


-- @@ L1334-1334 verbatim
end EulerGevreyFlowLpIntegration


-- @@ L1336-1336 verbatim
end

-- @@ L1337-1337 verbatim
end


-- @@ L1339-1339 verbatim
end


-- @@ L1341-1341 verbatim
@[expose] public section


-- @@ L1343-1343 verbatim
noncomputable section


-- @@ L1345-1345 verbatim
namespace EulerSmoothCylinderFlow


-- @@ L1347-1348 verbatim
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey

-- @@ L1349-1349 verbatim
open scoped ContDiff Interval BoundedContinuousFunction


-- @@ L1351-1355 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] LiftTangent)` instance to
shorten typeclass synthesis. -/
local instance instSmoothCylinderGevrey1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    LiftTangent) :=
    inferInstance

-- @@ L1356-1359 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] LiftTangent)` instance to shorten
typeclass synthesis. -/
local instance instSmoothCylinderGevrey2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ]
    LiftTangent) := inferInstance

-- @@ L1360-1364 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderGevrey3 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ]
    LiftTangent)) := inferInstance

-- @@ L1365-1369 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderGevrey4 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ] LiftTangent))
    := inferInstance

-- @@ L1370-1373 verbatim
/-- The `MeasurableSpace (LiftTangent [×n]→L[ℝ] LiftTangent)` structure used in smooth cylinder
gevrey. -/
local instance instSmoothCylinderGevrey5 (n : ℕ) : MeasurableSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := borel _

-- @@ L1374-1375 verbatim
local instance instSmoothCylinderGevrey6 (n : ℕ) : BorelSpace (LiftTangent [×n]→L[ℝ] LiftTangent)
    := ⟨rfl⟩

-- @@ L1376-1381 verbatim
local instance instSmoothCylinderGevrey7 (n : ℕ) : FiniteDimensional ℝ (LiftTangent [×n]→L[ℝ]
    LiftTangent) := by
  let J : (LiftTangent [×n]→L[ℝ] LiftTangent) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin n => LiftTangent) LiftTangent :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective


-- @@ L1383-1386 verbatim
variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)


-- @@ L1388-1394 verbatim
theorem displacementJet_bound (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) (q : LiftDomain P) :
    ‖displacementJet P T hT A t q n‖ ≤ B*(t : ℝ)*(4*R)^n*(n.factorial : ℝ)^2 :=
  EulerSmoothFlowGevrey.displacement_bound T hT A B R hB hR hsmall hb
    n t t.property (sectionPoint P q)


-- @@ L1396-1398 verbatim
variable (hdiv : ∀ t x,
  LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) x).toLinearMap =
      0)


-- @@ L1400-1426 verbatim
include hA hdiv in
theorem compositionJet_memLp_and_bound (B R C S : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ)
    (hLp : ∀ t : Icc (0 : ℝ) T, ∀ j ≤ n,
      MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm : ∀ t : Icc (0 : ℝ) T, ∀ j ≤ n,
      (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C*S^j*(j.factorial : ℝ)^2)
    (t : ℝ) :
    MemLp (fun q => compositionJet P T hT A t q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => compositionJet P T hT A t q n) 2 (liftMeasure P)).toReal ≤
        C*(flowRadius B R T S)^n*(n.factorial : ℝ)^2 := by
  apply EulerGevreyJetCompositionLp.composition_memLp_and_bound (liftMeasure P)
    (forward P T hT A (projIcc 0 T hT t))
    (forward_measurePreserving P T hT A hA hdiv (projIcc 0 T hT t))
    (jetSeries P (forwardCover T hT A t)) (jetSeries P (velocityCover T hT A t)) n
    ((compositionJet_joint_measurable P T hT A hA n).comp (measurable_const.prodMk
        measurable_id)).aestronglyMeasurable
    C (1+B*T) (4*R+1) S hC (by positivity) (by positivity) hS
  · exact hLp (projIcc 0 T hT t)
  · exact hNorm (projIcc 0 T hT t)
  · intro j hj _ q
    exact forward_positive_bound T hT A B R hB hR hsmall hb j hj
      (projIcc 0 T hT t) (sectionPoint P q)


-- @@ L1428-1461 verbatim
include hA hdiv in
theorem displacementJet_memLp_and_bound (B R C S : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ)
    (hLp : ∀ t : Icc (0 : ℝ) T, ∀ j ≤ n,
      MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm : ∀ t : Icc (0 : ℝ) T, ∀ j ≤ n,
      (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C*S^j*(j.factorial : ℝ)^2)
    (t : Icc (0 : ℝ) T) :
    MemLp (fun q => displacementJet P T hT A t q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => displacementJet P T hT A t q n) 2 (liftMeasure P)).toReal ≤
        (t : ℝ)*C*(flowRadius B R T S)^n*(n.factorial : ℝ)^2 := by
  have hm := (compositionJet_joint_measurable P T hT A hA n).aestronglyMeasurable
    (μ := (volume.restrict (Icc 0 (t : ℝ))).prod (liftMeasure P))
  have hi := EulerGevreyFlowLpIntegration.integrated_composition_bound (t : ℝ) t.property.1
    (liftMeasure P) (fun s => forward P T hT A (projIcc 0 T hT s))
    (fun s _ => forward_measurePreserving P T hT A hA hdiv (projIcc 0 T hT s))
    (fun s => jetSeries P (forwardCover T hT A s))
    (fun s => jetSeries P (velocityCover T hT A s)) n hm
    C (1+B*T) (4*R+1) S hC (by positivity) (by positivity) hS
    (fun s _ => hLp (projIcc 0 T hT s)) (fun s _ => hNorm (projIcc 0 T hT s))
    (fun s _ j hj _ q => forward_positive_bound T hT A B R hB hR hsmall hb j hj
      (projIcc 0 T hT s) (sectionPoint P q))
  have he : (fun q => ∫ s in (0 : ℝ)..(t : ℝ), compositionJet P T hT A s q n) =
      fun q => displacementJet P T hT A t q n :=
    funext (fun q => (displacementJet_integral P T hT A hA t q n).symm)
  change MemLp (fun q => ∫ s in (0 : ℝ)..(t : ℝ), compositionJet P T hT A s q n)
      2 (liftMeasure P) ∧
    (eLpNorm (fun q => ∫ s in (0 : ℝ)..(t : ℝ), compositionJet P T hT A s q n)
      2 (liftMeasure P)).toReal ≤ (t : ℝ)*C*(flowRadius B R T S)^n*(n.factorial : ℝ)^2 at hi
  rwa [he] at hi


-- @@ L1463-1463 verbatim
end EulerSmoothCylinderFlow


-- @@ L1465-1465 verbatim
end

-- @@ L1466-1466 verbatim
end


-- @@ L1468-1468 verbatim
end


-- @@ L1470-1470 verbatim
@[expose] public section


-- @@ L1472-1472 verbatim
noncomputable section


-- @@ L1474-1474 verbatim
namespace EulerPhysicalGraphFlowBounds


-- @@ L1476-1479 verbatim
open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey EulerGraphInvariantFlow
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerPhysicalGraphGevrey
  EulerCylinderGraphGevrey

-- @@ L1480-1480 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L1482-1486 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instPhysicalGraphFlowBounds1 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance

-- @@ L1487-1491 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instPhysicalGraphFlowBounds2 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ] LiftTangent))
    := inferInstance


-- @@ L1493-1537 verbatim
/-- Data, collecting `time_nonneg`, `A`, `A₁`, `time_derivative`, `periodic`, `periodic_time`
and their compatibility conditions. -/
structure Data (P T : ℝ) [Fact (0 < P)] where
  time_nonneg : 0 ≤ T
  /-- A of `Data`, of type `SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent`. -/
  A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent
  /-- A₁ of `Data`, of type `SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent`. -/
  A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent
  time_derivative : SmoothTimeField.TimeDerivative T time_nonneg A A₁
  periodic : ∀ (c : AddSubgroup.zmultiples P) t z, A.field t (z.1,(c : ℝ)+z.2)=A.field t z
  periodic_time : ∀ (c : AddSubgroup.zmultiples P) t z, A₁.field t (z.1,(c : ℝ)+z.2)=A₁.field t z
  divergence : ∀ t z,
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) z).toLinearMap=0
  /-- Bound parameter of `Data`, of type `ℝ`. -/
  B : ℝ
  /-- Radius parameter of `Data`, of type `ℝ`. -/
  R : ℝ
  /-- Bound coefficient of `Data`, of type `ℝ`. -/
  C : ℝ
  /-- Parameter `S` of `Data`, of type `ℝ`. -/
  S : ℝ
  /-- First-derivative bound coefficient of `Data`, of type `ℝ`. -/
  C₁ : ℝ
  /-- Parameter `S₁` of `Data`, of type `ℝ`. -/
  S₁ : ℝ
  B_nonneg : 0 ≤ B
  R_pos : 0 < R
  C_nonneg : 0 ≤ C
  S_nonneg : 0 ≤ S
  C₁_nonneg : 0 ≤ C₁
  S₁_nonneg : 0 ≤ S₁
  small : B*R*T ≤ 1/8
  sup_bound : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2
  integrable : ∀ t n,
    MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure P)
  lp_bound : ∀ t n,
    (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure
        P)).toReal ≤
      C*S^n*(n.factorial : ℝ)^2
  integrable_time : ∀ t n,
    MemLp (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure P)
  lp_bound_time : ∀ t n,
    (eLpNorm (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q n) 2 (liftMeasure
        P)).toReal ≤
      C₁*S₁^n*(n.factorial : ℝ)^2


-- @@ L1539-1539 verbatim
namespace Data


-- @@ L1541-1541 verbatim
variable {P T : ℝ} [Fact (0 < P)] (G : Data P T)


-- @@ L1543-1544 verbatim
/-- Velocity radius, given by `flowRadius G.B G.R T G.S`. -/
def velocityRadius : ℝ := flowRadius G.B G.R T G.S

-- @@ L1545-1546 verbatim
/-- Acceleration radius, given by `flowRadius G.B G.R T (4*G.R+G.S+G.S₁)`. -/
def accelerationRadius : ℝ := flowRadius G.B G.R T (4*G.R+G.S+G.S₁)

-- @@ L1547-1548 verbatim
/-- Acceleration amplitude, given by `G.C₁+3*G.B*G.R*G.C`. -/
def accelerationAmplitude : ℝ := G.C₁+3*G.B*G.R*G.C


-- @@ L1550-1556 verbatim
theorem velocityRadius_nonneg : 0 ≤ G.velocityRadius := by
  have := G.B_nonneg
  have := G.R_pos
  have := G.S_nonneg
  have := G.time_nonneg
  unfold velocityRadius flowRadius
  positivity


-- @@ L1558-1565 verbatim
theorem accelerationRadius_nonneg : 0 ≤ G.accelerationRadius := by
  have := G.B_nonneg
  have := G.R_pos
  have := G.S_nonneg
  have := G.S₁_nonneg
  have := G.time_nonneg
  unfold accelerationRadius flowRadius
  positivity


-- @@ L1567-1573 verbatim
theorem accelerationAmplitude_nonneg : 0 ≤ G.accelerationAmplitude := by
  have := G.B_nonneg
  have := G.R_pos
  have := G.C_nonneg
  have := G.C₁_nonneg
  unfold accelerationAmplitude
  positivity


-- @@ L1575-1586 verbatim
theorem displacement_cylinder_bound (t : Icc (0 : ℝ) T) (n : ℕ) :
    MemLp (fun q => jetSeries P (displacement T G.time_nonneg G.A t) q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (displacement T G.time_nonneg G.A t) q n)
        2 (liftMeasure P)).toReal ≤ (T*G.C)*G.velocityRadius^n*(n.factorial : ℝ)^2 := by
  obtain ⟨hi,hn⟩ := EulerSmoothCylinderFlow.displacementJet_memLp_and_bound
    P T G.time_nonneg G.A G.periodic G.divergence G.B G.R G.C G.S
    G.B_nonneg G.R_pos G.C_nonneg G.S_nonneg G.small G.sup_bound n
    (fun s j _ => G.integrable s j) (fun s j _ => G.lp_bound s j) t
  refine ⟨hi,hn.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right t.property.2 G.C_nonneg)
      (pow_nonneg G.velocityRadius_nonneg n)) (sq_nonneg _)


-- @@ L1588-1594 verbatim
theorem velocity_periodic (t : Icc (0 : ℝ) T) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    materialVelocity T G.time_nonneg G.A t (z.1,(c : ℝ)+z.2) =
      materialVelocity T G.time_nonneg G.A t z :=
  comp_deck P (G.A.field t : LiftTangent → LiftTangent) (fun d y => G.periodic d t y)
    ((flowData T G.time_nonneg G.A).forward t)
    (EulerCylinderPeriodicFlow.flow_deck P (flowData T G.time_nonneg G.A)
      (EulerSmoothCylinderFlow.velocity_deck P T G.time_nonneg G.A G.periodic) 0 t) c z


-- @@ L1596-1598 verbatim
theorem velocity_smooth (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (materialVelocity T G.time_nonneg G.A t) :=
  (G.A.smooth t).comp (forward_contDiff T G.time_nonneg G.A t)


-- @@ L1600-1607 verbatim
theorem velocity_cylinder_bound (t : Icc (0 : ℝ) T) (n : ℕ) :
    MemLp (fun q => jetSeries P (materialVelocity T G.time_nonneg G.A t) q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (materialVelocity T G.time_nonneg G.A t) q n)
        2 (liftMeasure P)).toReal ≤ G.C*G.velocityRadius^n*(n.factorial : ℝ)^2 :=
  EulerSmoothCylinderFlow.composeJet_memLp_and_bound P T G.time_nonneg G.A G.periodic G.divergence
    (G.A.field t) (G.A.smooth t) (fun c z => G.periodic c t z) G.B G.R G.C G.S
    G.B_nonneg G.R_pos G.C_nonneg G.S_nonneg G.small G.sup_bound n
    (fun j _ => G.integrable t j) (fun j _ => G.lp_bound t j) t


-- @@ L1609-1616 verbatim
theorem acceleration_periodic (t : Icc (0 : ℝ) T) (c : AddSubgroup.zmultiples P) (z : LiftTangent) :
    materialAcceleration T G.time_nonneg G.A G.A₁ t (z.1,(c : ℝ)+z.2) =
      materialAcceleration T G.time_nonneg G.A G.A₁ t z :=
  comp_deck P (accelerationField T G.A G.A₁ t)
    (EulerSmoothCylinderFlow.accelerationField_deck P T G.A G.A₁ G.periodic G.periodic_time t)
    ((flowData T G.time_nonneg G.A).forward t)
    (EulerCylinderPeriodicFlow.flow_deck P (flowData T G.time_nonneg G.A)
      (EulerSmoothCylinderFlow.velocity_deck P T G.time_nonneg G.A G.periodic) 0 t) c z


-- @@ L1618-1620 verbatim
theorem acceleration_smooth (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (materialAcceleration T G.time_nonneg G.A G.A₁ t) :=
  (accelerationField_contDiff T G.A G.A₁ t).comp (forward_contDiff T G.time_nonneg G.A t)


-- @@ L1622-1631 verbatim
theorem acceleration_cylinder_bound (t : Icc (0 : ℝ) T) (n : ℕ) :
    MemLp (fun q => jetSeries P (materialAcceleration T G.time_nonneg G.A G.A₁ t) q n)
      2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (materialAcceleration T G.time_nonneg G.A G.A₁ t) q n)
        2 (liftMeasure P)).toReal ≤ G.accelerationAmplitude*G.accelerationRadius^n*(n.factorial :
            ℝ)^2 :=
  EulerSmoothCylinderFlow.materialAccelerationJet_memLp_and_bound P T G.time_nonneg G.A G.A₁
    G.periodic G.periodic_time G.divergence G.B G.R G.C G.S G.C₁ G.S₁
    G.B_nonneg G.R_pos G.C_nonneg G.S_nonneg G.C₁_nonneg G.S₁_nonneg
    G.small G.sup_bound G.integrable G.lp_bound G.integrable_time G.lp_bound_time n t


-- @@ L1633-1642 verbatim
/-- Displacement field, constructed using `physicalField`. -/
def displacementField (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) :
    SmoothL2Field Vector3 :=
  physicalField P (displacement T G.time_nonneg G.A t)
    (EulerSmoothCylinderFlow.coverDisplacement_deck P T G.time_nonneg G.A G.periodic t)
    (displacement_contDiff T G.time_nonneg G.A t) k m (T*G.C) G.velocityRadius
    (mul_nonneg G.time_nonneg G.C_nonneg) G.velocityRadius_nonneg
    (fun n => (G.displacement_cylinder_bound t n).1) (fun n => (G.displacement_cylinder_bound t
        n).2)
    ell hell (fst ℝ Vector3 ℝ)


-- @@ L1644-1651 verbatim
/-- Velocity field, constructed using `physicalField`. -/
def velocityField (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) :
    SmoothL2Field Vector3 :=
  physicalField P (materialVelocity T G.time_nonneg G.A t) (G.velocity_periodic t)
      (G.velocity_smooth t)
    k m G.C G.velocityRadius G.C_nonneg G.velocityRadius_nonneg
    (fun n => (G.velocity_cylinder_bound t n).1) (fun n => (G.velocity_cylinder_bound t n).2)
    ell hell (fst ℝ Vector3 ℝ)


-- @@ L1653-1662 verbatim
/-- Acceleration field L², constructed using `physicalField`. -/
def accelerationFieldL2 (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) :
    SmoothL2Field Vector3 :=
  physicalField P (materialAcceleration T G.time_nonneg G.A G.A₁ t)
    (G.acceleration_periodic t) (G.acceleration_smooth t) k m G.accelerationAmplitude
        G.accelerationRadius
    G.accelerationAmplitude_nonneg G.accelerationRadius_nonneg
    (fun n => (G.acceleration_cylinder_bound t n).1) (fun n => (G.acceleration_cylinder_bound t
        n).2)
    ell hell (fst ℝ Vector3 ℝ)


-- @@ L1664-1671 verbatim
theorem displacementField_bound (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.displacementField k m ell hell t).HasJetBound
      (Real.sqrt (2/P+2*P)*(T*G.C)*(1+G.velocityRadius)) (ell⁻¹*(4*G.velocityRadius*graphFactor k
          m)) :=
  physicalField_bound P _ _ _ k m (T*G.C) G.velocityRadius
    (mul_nonneg G.time_nonneg G.C_nonneg) G.velocityRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..)


-- @@ L1673-1678 verbatim
theorem velocityField_bound (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.velocityField k m ell hell t).HasJetBound
      (Real.sqrt (2/P+2*P)*G.C*(1+G.velocityRadius)) (ell⁻¹*(4*G.velocityRadius*graphFactor k m)) :=
  physicalField_bound P _ _ _ k m G.C G.velocityRadius G.C_nonneg G.velocityRadius_nonneg
    _ _ ell hell hell1 (fst ℝ Vector3 ℝ) (norm_fst_le ..)


-- @@ L1680-1687 verbatim
theorem accelerationField_bound (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (t : Icc (0 : ℝ) T) :
    (G.accelerationFieldL2 k m ell hell t).HasJetBound
      (Real.sqrt (2/P+2*P)*G.accelerationAmplitude*(1+G.accelerationRadius))
      (ell⁻¹*(4*G.accelerationRadius*graphFactor k m)) :=
  physicalField_bound P _ _ _ k m G.accelerationAmplitude G.accelerationRadius
    G.accelerationAmplitude_nonneg G.accelerationRadius_nonneg _ _ ell hell hell1
    (fst ℝ Vector3 ℝ) (norm_fst_le ..)


-- @@ L1689-1690 verbatim
variable (k : ℝ) (m : Vector3)
  (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)


-- @@ L1692-1696 verbatim
include hgraph in
theorem displacementField_eq (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.displacementField k m ell hell t).field x =
      displacement T G.time_nonneg (physicalCoefficient k m T G.A ell) t x :=
  (physical_displacement_eq k m T G.time_nonneg G.A hgraph ell hell.ne' t x).symm


-- @@ L1698-1702 verbatim
include hgraph in
theorem velocityField_eq (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.velocityField k m ell hell t).field x =
      materialVelocity T G.time_nonneg (physicalCoefficient k m T G.A ell) t x :=
  (physical_materialVelocity_eq k m T G.time_nonneg G.A hgraph ell hell.ne' t x).symm


-- @@ L1704-1709 verbatim
include hgraph in
theorem accelerationField_eq (ell : ℝ) (hell : 0 < ell) (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.accelerationFieldL2 k m ell hell t).field x =
      materialAcceleration T G.time_nonneg (physicalCoefficient k m T G.A ell)
        (physicalCoefficient k m T G.A₁ ell) t x :=
  (physical_materialAcceleration_eq k m T G.time_nonneg G.A G.A₁ hgraph ell hell.ne' t x).symm


-- @@ L1711-1711 verbatim
end Data

-- @@ L1712-1712 verbatim
end EulerPhysicalGraphFlowBounds
