/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowGevrey
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.SmoothPathTimeJets
import Mathlib.Analysis.Calculus.MeanValue
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJacobian
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.SmoothImplicitLift
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import LeanPool.NavierStokesAndEuler.Euler.SeparatingTimeDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Comp


-- @@ L28-29 verbatim
/-! The actual flow displacement and material velocity, with every spatial
jet in the uniform continuous-time bounded-field space. -/


-- @@ L31-31 verbatim
section


-- @@ L33-35 verbatim
/-! Genuine joint time-space regularity of the constructed flow and its
inverse. Interior C² uses only the actual first time derivative of the
velocity coefficient, together with its existing smooth spatial jets. -/


-- @@ L37-37 verbatim
section


-- @@ L39-40 verbatim
/-! Joint time-space differentiability of a genuine smooth family of
continuous paths, and the actual mixed derivative of its spatial Jacobian. -/


-- @@ L42-42 verbatim
@[expose] public section


-- @@ L44-44 verbatim
noncomputable section


-- @@ L46-46 verbatim
open scoped ContDiff Topology


-- @@ L48-48 verbatim
namespace EulerSmoothPathJoint


-- @@ L50-50 verbatim
open Set Filter EulerVolterraConvolution EulerSmoothPathTimeJets


-- @@ L52-55 verbatim
variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : E → C(Icc (0 : ℝ) T, V))


-- @@ L57-58 verbatim
/-- Time slice, given by `extendPath T hT (f x) t`. -/
def timeSlice (t : ℝ) (x : E) : V := extendPath T hT (f x) t


-- @@ L60-64 verbatim
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem timeSlice_joint_continuous (hf : Continuous f) :
    Continuous (Function.uncurry (timeSlice T hT f)) := by
  unfold timeSlice extendPath
  fun_prop


-- @@ L66-70 verbatim
/-- Spatial derivative as an element of `C(Icc (0 : ℝ) T,E →L[ℝ] V)`. -/
def spatialDerivative (x : E) : C(Icc (0 : ℝ) T,E →L[ℝ] V) :=
  ((continuousMultilinearCurryFin1 ℝ E
      V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
    ℝ (Icc (0 : ℝ) T)) (jetFamily T f 1 x)


-- @@ L72-78 verbatim
theorem spatialDerivative_contDiff (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (spatialDerivative T f) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,E [×1]→L[ℝ] V)) (F := C(Icc (0 : ℝ) T,E →L[ℝ] V))
    ((continuousMultilinearCurryFin1 ℝ E
        V).toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous
      ℝ (Icc (0 : ℝ) T))).comp (jetFamily_contDiff T f hf 1)


-- @@ L80-87 verbatim
theorem spatialDerivative_apply (hf : ContDiff ℝ ∞ f) (x : E) (t : Icc (0 : ℝ) T) :
    spatialDerivative T f x t = fderiv ℝ (fun y => f y t) x := by
  change continuousMultilinearCurryFin1 ℝ E V (jetFamily T f 1 x t) = _
  rw [jetFamily_apply T f hf]
  apply ContinuousLinearMap.ext
  intro v
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp


-- @@ L89-93 verbatim
theorem timeSlice_hasFDerivAt (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    HasFDerivAt (timeSlice T hT f t) (spatialDerivative T f x (projIcc 0 T hT t)) x := by
  rw [spatialDerivative_apply T f hf]
  exact (((ContinuousMap.evalCLM ℝ (projIcc 0 T hT t)).contDiff.comp hf).differentiable
    (by simp) x).hasFDerivAt


-- @@ L95-99 verbatim
/-- Joint derivative, given by `(ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q t
x)).coprod (timeSlice T hT (spatialDerivative T f) t x)`. -/
def jointDerivative (t : ℝ) (x : E) : (ℝ × E) →L[ℝ] V :=
  (ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q t x)).coprod
    (timeSlice T hT (spatialDerivative T f) t x)


-- @@ L101-106 verbatim
theorem jointDerivative_continuous (hf : ContDiff ℝ ∞ f) (hq : Continuous q) :
    Continuous (Function.uncurry (jointDerivative T hT f q)) := by
  exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
    (timeSlice_joint_continuous T hT q hq)).continuousLinearMapCoprod
      (timeSlice_joint_continuous T hT (spatialDerivative T f)
        (spatialDerivative_contDiff T f hf).continuous)


-- @@ L108-110 verbatim
variable (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)


-- @@ L112-136 verbatim
include hf hq hd in
theorem joint_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    HasFDerivAt (Function.uncurry (timeSlice T hT f)) (jointDerivative T hT f q t x) (t,x) := by
  have hloc : ∀ᶠ p : ℝ × E in 𝓝 (t,x), p.1 ∈ Ioo 0 T :=
    (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f := timeSlice T hT f) (u := (t,x))
    (f₁ := fun s y => ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q s y))
    (f₂ := timeSlice T hT (spatialDerivative T f))
  · filter_upwards [hloc] with p hp
    change HasFDerivAt (fun s => timeSlice T hT f s p.2)
      (ContinuousLinearMap.toSpanSingleton ℝ (timeSlice T hT q p.1 p.2)) p.1
    have hh := (hd p.2 ⟨p.1,hp.1.le,hp.2.le⟩).hasDerivAt (Icc_mem_nhds hp.1 hp.2)
    have he : timeSlice T hT q p.1 p.2 = q p.2 ⟨p.1,hp.1.le,hp.2.le⟩ := by
      simp only [timeSlice, extendPath, projIcc_of_mem hT ⟨hp.1.le,hp.2.le⟩]
    rw [he]
    exact hh.hasFDerivAt
  · apply Eventually.of_forall
    intro p
    exact timeSlice_hasFDerivAt T hT f hf p.1 p.2
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ V).continuous.comp
      (timeSlice_joint_continuous T hT q hq.continuous)).continuousAt
  · exact (timeSlice_joint_continuous T hT (spatialDerivative T f)
      (spatialDerivative_contDiff T f hf).continuous).continuousAt


-- @@ L138-146 verbatim
include hf hq hd in
theorem joint_contDiffAt_one (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (timeSlice T hT f)) (t,x) := by
  rw [contDiffAt_one_iff]
  refine ⟨Function.uncurry (jointDerivative T hT f q), {p : ℝ × E | p.1 ∈ Ioo 0 T}, ?_,
    (jointDerivative_continuous T hT f q hf hq.continuous).continuousOn, ?_⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact joint_hasFDerivAt T hT f q hf hq hd p.1 hp p.2


-- @@ L148-155 verbatim
include hf hq hd in
theorem spatialDerivative_time (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (spatialDerivative T f x))
      (spatialDerivative T q x t) (Icc (0 : ℝ) T) t := by
  have h := (continuousMultilinearCurryFin1 ℝ E
      V).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) (jetFamily_hasDerivWithinAt T hT f q hf hq hd 1 x t)
  exact h


-- @@ L157-157 verbatim
end EulerSmoothPathJoint


-- @@ L159-159 verbatim
end

-- @@ L160-160 verbatim
end


-- @@ L162-162 verbatim
end


-- @@ L164-164 verbatim
section


-- @@ L166-168 verbatim
/-! The actual acceleration of the constructed nonlinear flow is the
material derivative of its velocity, including the one-sided endpoint
identities. All coefficient time derivatives are literal hypotheses. -/


-- @@ L170-170 verbatim
@[expose] public section


-- @@ L172-172 verbatim
noncomputable section


-- @@ L174-174 verbatim
open scoped ContDiff Topology


-- @@ L176-176 verbatim
namespace EulerSmoothBanachFlow


-- @@ L178-178 verbatim
open Set Filter EulerVolterraConvolution EulerContinuousTimeIntegral


-- @@ L180-181 verbatim
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)


-- @@ L183-187 verbatim
/-- Acceleration family, given by `A₁.superposition (pathFamily T hT A x) + multiplier
(A.derivative.superposition (pathFamily T hT A x)) (velocityFamily T hT A x)`. -/
def accelerationFamily (x : E) : C(Icc (0 : ℝ) T,E) :=
  A₁.superposition (pathFamily T hT A x) +
    multiplier (A.derivative.superposition (pathFamily T hT A x)) (velocityFamily T hT A x)


-- @@ L189-197 verbatim
theorem accelerationFamily_apply (x : E) (t : Icc (0 : ℝ) T) :
    accelerationFamily T hT A A₁ x t =
      A₁.field t ((flowData T hT A).forward t x) +
        fderiv ℝ (A.field t : E → E) ((flowData T hT A).forward t x)
          (A.field t ((flowData T hT A).forward t x)) := by
  change A₁.field t ((flowData T hT A).forward t x) +
    A.derivativeField t ((flowData T hT A).forward t x)
      (A.field t ((flowData T hT A).forward t x)) = _
  rw [A.derivativeField_eq]


-- @@ L199-204 verbatim
theorem pathFamily_time_derivative (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (pathFamily T hT A x))
      (velocityFamily T hT A x t) (Icc (0 : ℝ) T) t := by
  apply (pathFamily_hasDerivWithinAt T hT A x t).congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs, pathFamily_apply]


-- @@ L206-222 verbatim
theorem velocityFamily_time_derivative_interior
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT (velocityFamily T hT A x))
      (accelerationFamily T hT A A₁ x ⟨t,ht.1.le,ht.2.le⟩) t := by
  have hf := (pathFamily_time_derivative T hT A x ⟨t,ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  have hd := SmoothTimeField.realField_hasFDerivAt T hT A A₁ htime t ht
    (extendPath T hT (pathFamily T hT A x) t)
  have h := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hf)
  convert h using 1
  · rfl
  · simp only [SmoothTimeField.jointDerivative, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    simp only [SmoothTimeField.realField, extendPath,
      projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩]
    rfl


-- @@ L224-235 verbatim
theorem velocityFamily_time_derivative
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (velocityFamily T hT A x))
      (accelerationFamily T hT A A₁ x t) (Icc (0 : ℝ) T) t := by
  apply EulerSeparatingTimeDerivative.hasDerivWithinAt T hT
    (velocityFamily T hT A x) (accelerationFamily T hT A A₁ x)
    (fun _ : Unit => ContinuousLinearMap.id ℝ E)
  · intro u v h
    exact congrFun h ()
  · intro _ s hs
    exact velocityFamily_time_derivative_interior T hT A A₁ htime x s hs


-- @@ L237-249 verbatim
theorem forward_second_time_derivative
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => deriv (fun r => (flowData T hT A).forward r x) s)
      (accelerationFamily T hT A A₁ x t) (Icc (0 : ℝ) T) t := by
  apply (velocityFamily_time_derivative T hT A A₁ htime x t).congr_of_mem _ t.property
  intro s hs
  rw [((flowData T hT A).forward_hasDerivAt s x).deriv]
  change (flowData T hT A).velocity s ((flowData T hT A).forward s x) =
    velocityFamily T hT A x (projIcc 0 T hT s)
  rw [projIcc_of_mem hT hs]
  exact EulerBoundedLipschitzFlow.ofTimeInterval_velocity T hT A.field
    ‖A.derivative.field‖₊ (velocity_lipschitz T A) ⟨s,hs⟩ _


-- @@ L251-251 verbatim
end EulerSmoothBanachFlow


-- @@ L253-253 verbatim
end

-- @@ L254-254 verbatim
end


-- @@ L256-256 verbatim
end


-- @@ L258-258 verbatim
@[expose] public section


-- @@ L260-260 verbatim
noncomputable section


-- @@ L262-262 verbatim
open scoped ContDiff Topology


-- @@ L264-264 verbatim
namespace EulerSmoothBanachFlow


-- @@ L266-267 verbatim
open Set Filter EulerVolterraConvolution EulerContinuousTimeIntegral
  EulerSmoothPathJoint EulerContinuousPathCalculus


-- @@ L269-270 verbatim
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)


-- @@ L272-276 verbatim
theorem accelerationFamily_contDiff : ContDiff ℝ ∞ (accelerationFamily T hT A A₁) := by
  have hp := pathFamily_contDiff T hT A
  exact (A₁.superposition_contDiff.comp hp).add
    (contDiff_apply _ _ (A.derivative.superposition_contDiff.comp hp)
      (velocityFamily_contDiff T hT A))


-- @@ L278-288 verbatim
theorem forward_joint_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    HasFDerivAt (Function.uncurry (flowData T hT A).forward)
      (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A) t x) (t,x) := by
  have h := joint_hasFDerivAt T hT (pathFamily T hT A) (velocityFamily T hT A)
    (pathFamily_contDiff T hT A) (velocityFamily_contDiff T hT A)
    (pathFamily_time_derivative T hT A) t ht x
  apply h.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)] with p hp
  change (flowData T hT A).forward p.1 p.2 =
    extendPath T hT (pathFamily T hT A p.2) p.1
  simp only [extendPath, projIcc_of_mem hT ⟨hp.1.le,hp.2.le⟩, pathFamily_apply]


-- @@ L290-299 verbatim
theorem forward_joint_contDiffAt_one (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (flowData T hT A).forward) (t,x) := by
  rw [contDiffAt_one_iff]
  refine ⟨Function.uncurry (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A)),
    {p : ℝ × E | p.1 ∈ Ioo 0 T}, ?_,
    (jointDerivative_continuous T hT _ _ (pathFamily_contDiff T hT A)
      (velocityFamily_contDiff T hT A).continuous).continuousOn, ?_⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact forward_joint_hasFDerivAt T hT A p.1 hp p.2


-- @@ L301-323 verbatim
theorem forward_jointDerivative_contDiffAt_one
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1
      (Function.uncurry (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A))) (t,x)
          := by
  have hq := joint_contDiffAt_one T hT (velocityFamily T hT A) (accelerationFamily T hT A A₁)
    (velocityFamily_contDiff T hT A) (accelerationFamily_contDiff T hT A A₁)
    (velocityFamily_time_derivative T hT A A₁ htime) t ht x
  have hJ := joint_contDiffAt_one T hT (spatialDerivative T (pathFamily T hT A))
    (spatialDerivative T (velocityFamily T hT A))
    (spatialDerivative_contDiff T _ (pathFamily_contDiff T hT A))
    (spatialDerivative_contDiff T _ (velocityFamily_contDiff T hT A))
    (spatialDerivative_time T hT _ _ (pathFamily_contDiff T hT A)
      (velocityFamily_contDiff T hT A) (pathFamily_time_derivative T hT A)) t ht x
  have hs := (ContinuousLinearMap.toSpanSingletonLIE ℝ
      E).toContinuousLinearEquiv.contDiff.contDiffAt.comp
    (t,x) hq
  let L : ((ℝ →L[ℝ] E) × (E →L[ℝ] E)) →L[ℝ] ((ℝ × E) →L[ℝ] E) :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ) (F := E) (G := E) ℝ).toContinuousLinearMap
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
    (E := (ℝ →L[ℝ] E) × (E →L[ℝ] E)) (F := (ℝ × E) →L[ℝ] E) L).contDiffAt.comp
    (t,x) (hs.prodMk hJ)


-- @@ L325-335 verbatim
theorem forward_joint_contDiffAt_two
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (Function.uncurry (flowData T hT A).forward) (t,x) := by
  rw [show (2 : ℕ∞ω) = ((1 : ℕ) + 1) from rfl, contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨Function.uncurry (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A)),
    ⟨{p : ℝ × E | p.1 ∈ Ioo 0 T}, ?_, ?_⟩,
    forward_jointDerivative_contDiffAt_one T hT A A₁ htime t ht x⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact forward_joint_hasFDerivAt T hT A p.1 hp p.2


-- @@ L337-349 verbatim
omit [FiniteDimensional ℝ E] in
/-- Time lift equiv, constructed using `ContinuousLinearEquiv.equivOfInverse`. -/
def timeLiftEquiv (J : E ≃L[ℝ] E) (v : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ ℝ E).prod
      (((ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ E)) +
        J.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ E)))
    ((ContinuousLinearMap.fst ℝ ℝ E).prod
      (J.symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.snd ℝ ℝ E) -
          (ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ E))))
    (by intro p; ext <;> simp)
    (by intro p; ext <;> simp)


-- @@ L351-352 verbatim
/-- Lift forward, given by `(p.1, (flowData T hT A).forward p.1 p.2)`. -/
def liftForward (p : ℝ × E) : ℝ × E := (p.1, (flowData T hT A).forward p.1 p.2)

-- @@ L353-354 verbatim
/-- Lift backward, given by `(p.1, (flowData T hT A).backward p.1 p.2)`. -/
def liftBackward (p : ℝ × E) : ℝ × E := (p.1, (flowData T hT A).backward p.1 p.2)


-- @@ L356-383 verbatim
theorem liftForward_hasFDerivAt (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    HasFDerivAt (liftForward T hT A)
      (timeLiftEquiv (jacobianEquiv T hT A ⟨t,ht.1.le,ht.2.le⟩ x)
        (velocityFamily T hT A x ⟨t,ht.1.le,ht.2.le⟩)).toContinuousLinearMap (t,x) := by
  have h : HasFDerivAt (liftForward T hT A)
      ((ContinuousLinearMap.fst ℝ ℝ E).prod
        (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A) t x)) (t,x) :=
    hasFDerivAt_fst.prodMk (forward_joint_hasFDerivAt T hT A t ht x)
  have he : (timeLiftEquiv (jacobianEquiv T hT A ⟨t,ht.1.le,ht.2.le⟩ x)
      (velocityFamily T hT A x ⟨t,ht.1.le,ht.2.le⟩)).toContinuousLinearMap =
      (ContinuousLinearMap.fst ℝ ℝ E).prod
        (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A) t x) := by
    apply ContinuousLinearMap.ext
    intro p
    ext
    · rfl
    · change p.1 • velocityFamily T hT A x ⟨t,ht.1.le,ht.2.le⟩ +
        (jacobianEvolution T hT A x).forward ⟨t,ht.1.le,ht.2.le⟩ p.2 =
        (jointDerivative T hT (pathFamily T hT A) (velocityFamily T hT A) t x) p
      simp only [jointDerivative, timeSlice, extendPath,
        projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩, ContinuousLinearMap.coprod_apply,
        ContinuousLinearMap.toSpanSingleton_apply]
      rw [spatialDerivative_apply T _ (pathFamily_contDiff T hT A)]
      change _ = p.1 • velocityFamily T hT A x ⟨t,ht.1.le,ht.2.le⟩ +
        fderiv ℝ (fun y => (flowData T hT A).forward t y) x p.2
      rw [forward_fderiv T hT A ⟨t,ht.1.le,ht.2.le⟩ x]
  rw [he]
  exact h


-- @@ L385-402 verbatim
theorem liftBackward_contDiffAt_two
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (liftBackward T hT A) (t,x) := by
  let y := (flowData T hT A).backward t x
  have hg : ContDiffAt ℝ 2 (liftForward T hT A) (t,y) :=
    contDiffAt_fst.prodMk (forward_joint_contDiffAt_two T hT A A₁ htime t ht y)
  apply EulerSmoothImplicitLift.contDiffAt_of_identity
    (liftBackward T hT A) (liftForward T hT A) id (t,x) 2 (by norm_num)
    ((continuous_fst.prodMk (flowData T hT A).backward_joint_continuous).continuousAt)
    hg contDiff_id.contDiffAt
    (timeLiftEquiv (jacobianEquiv T hT A ⟨t,ht.1.le,ht.2.le⟩ y)
      (velocityFamily T hT A y ⟨t,ht.1.le,ht.2.le⟩))
  · exact liftForward_hasFDerivAt T hT A t ht y
  · intro p
    ext
    · rfl
    · exact (flowData T hT A).forward_backward p.1 p.2


-- @@ L404-408 verbatim
theorem backward_joint_contDiffAt_two
    (htime : SmoothTimeField.TimeDerivative T hT A A₁)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (Function.uncurry (flowData T hT A).backward) (t,x) :=
  (liftBackward_contDiffAt_two T hT A A₁ htime t ht x).snd


-- @@ L410-410 verbatim
end EulerSmoothBanachFlow


-- @@ L412-412 verbatim
end

-- @@ L413-413 verbatim
end


-- @@ L415-415 verbatim
end


-- @@ L417-417 verbatim
section


-- @@ L419-420 verbatim
/-! Constructing literal bounded smooth coefficient paths from an actual
smooth path family and uniform bounds on its differentiated evolution. -/


-- @@ L422-422 verbatim
section


-- @@ L424-425 verbatim
/-! Uniform bounds on a genuine time derivative turn a continuous family
of paths into a continuous path of bounded fields. -/


-- @@ L427-427 verbatim
@[expose] public section


-- @@ L429-429 verbatim
noncomputable section


-- @@ L431-431 verbatim
open scoped BoundedContinuousFunction


-- @@ L433-433 verbatim
namespace EulerBoundedPathFamily


-- @@ L435-435 verbatim
open Set EulerVolterraConvolution


-- @@ L437-444 verbatim
variable {X V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : X → C(Icc (0 : ℝ) T, V))
  (hf : Continuous f) (C D : ℝ)
  (hC : ∀ t x, ‖f x t‖ ≤ C)
  (hD : 0 ≤ D) (hq : ∀ t x, ‖q x t‖ ≤ D)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)


-- @@ L446-450 verbatim
/-- Bounded slice, given by `BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f x t)
((ContinuousMap.evalCLM ℝ t).continuous.comp hf) C (hC t)`. -/
def boundedSlice (t : Icc (0 : ℝ) T) : X →ᵇ V :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f x t)
    ((ContinuousMap.evalCLM ℝ t).continuous.comp hf) C (hC t)


-- @@ L452-468 verbatim
include hq hd in
theorem boundedSlice_lipschitz :
    LipschitzWith ⟨D,hD⟩ (boundedSlice T f hf C hC) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hD dist_nonneg)).2
  intro x
  change ‖f x s - f x t‖ ≤ D * dist s t
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := extendPath T hT (f x)) (f' := extendPath T hT (q x)) (C := D)
    (fun r hr => by simpa only [extendPath, projIcc_of_mem hT hr] using hd x ⟨r,hr⟩)
    (fun r hr => by simpa only [extendPath, projIcc_of_mem hT hr] using hq ⟨r,hr⟩ x)
    (convex_Icc (0 : ℝ) T) t.property s.property
  simpa only [extendPath,
    projIcc_of_mem hT t.property, projIcc_of_mem hT s.property,
    dist_eq_norm, Subtype.dist_eq] using h


-- @@ L470-473 verbatim
/-- Bounded path, bundling `toFun`, `continuous_toFun`. -/
def boundedPath : C(Icc (0 : ℝ) T,X →ᵇ V) where
  toFun := boundedSlice T f hf C hC
  continuous_toFun := (boundedSlice_lipschitz T hT f q hf C D hC hD hq hd).continuous


-- @@ L475-476 verbatim
@[simp] theorem boundedPath_apply (t : Icc (0 : ℝ) T) (x : X) :
    boundedPath T hT f q hf C D hC hD hq hd t x = f x t := rfl


-- @@ L478-482 verbatim
theorem boundedPath_norm (hCnonneg : 0 ≤ C) :
    ‖boundedPath T hT f q hf C D hC hD hq hd‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hCnonneg).2
  intro t
  exact (BoundedContinuousFunction.norm_le hCnonneg).2 (hC t)


-- @@ L484-484 verbatim
end EulerBoundedPathFamily


-- @@ L486-486 verbatim
end

-- @@ L487-487 verbatim
end


-- @@ L489-489 verbatim
end


-- @@ L491-491 verbatim
@[expose] public section


-- @@ L493-493 verbatim
noncomputable section


-- @@ L495-495 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L497-497 verbatim
namespace SmoothTimeField


-- @@ L499-499 verbatim
open Set EulerSmoothPathTimeJets EulerBoundedPathFamily EulerVolterraConvolution


-- @@ L501-510 verbatim
variable {E V : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : E → C(Icc (0 : ℝ) T, V))
  (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)
  (C D : ℕ → ℝ)
  (hC : ∀ n t x, ‖iteratedFDeriv ℝ n (fun y => f y t) x‖ ≤ C n)
  (hD : ∀ n t x, ‖iteratedFDeriv ℝ n (fun y => q y t) x‖ ≤ D n)


-- @@ L512-515 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldFromPaths1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance

-- @@ L516-518 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeFieldFromPaths2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) :=
    inferInstance

-- @@ L519-522 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldFromPaths3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

-- @@ L523-526 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldFromPaths4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance


-- @@ L528-531 verbatim
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
include hC in
theorem value_bound (t : Icc (0 : ℝ) T) (x : E) : ‖f x t‖ ≤ C 0 := by
  simpa only [norm_iteratedFDeriv_zero] using hC 0 t x


-- @@ L533-536 verbatim
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
include hT hD in
theorem derivativeBound_nonneg (n : ℕ) : 0 ≤ D n :=
  (norm_nonneg _).trans (hD n ⟨0,le_rfl,hT⟩ 0)


-- @@ L538-553 verbatim
/-- Of path family, bundling `field`, `smooth`, `change`, `jet` and the required compatibility
proofs. -/
def ofPathFamily : SmoothTimeField (Icc (0 : ℝ) T) E V where
  field := boundedPath T hT f q hf.continuous (C 0) (D 0)
    (value_bound T f C hC) (derivativeBound_nonneg T hT q D hD 0)
    (value_bound T q D hD) hd
  smooth t := by
    change ContDiff ℝ ∞ (fun x => f x t)
    exact (ContinuousMap.evalCLM ℝ t).contDiff.comp hf
  jet n := boundedPath T hT (jetFamily T f n) (jetFamily T q n)
    (jetFamily_contDiff T f hf n).continuous (C n) (D n)
    (fun t x => by rw [jetFamily_apply T f hf]; exact hC n t x)
    (derivativeBound_nonneg T hT q D hD n)
    (fun t x => by rw [jetFamily_apply T q hq]; exact hD n t x)
    (jetFamily_hasDerivWithinAt T hT f q hf hq hd n)
  jet_eq n t x := jetFamily_apply T f hf n x t


-- @@ L555-556 verbatim
@[simp] theorem ofPathFamily_apply (t : Icc (0 : ℝ) T) (x : E) :
    (ofPathFamily T hT f q hf hq hd C D hC hD).field t x = f x t := rfl


-- @@ L558-561 verbatim
@[simp] theorem ofPathFamily_jet_apply (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    (ofPathFamily T hT f q hf hq hd C D hC hD).jet n t x =
      iteratedFDeriv ℝ n (fun y => f y t) x :=
  jetFamily_apply T f hf n x t


-- @@ L563-571 verbatim
theorem ofPathFamily_jet_norm (n : ℕ) :
    ‖(ofPathFamily T hT f q hf hq hd C D hC hD).jet n‖ ≤ C n := by
  have hnonneg : 0 ≤ C n := (norm_nonneg _).trans (hC n ⟨0,le_rfl,hT⟩ 0)
  apply (ContinuousMap.norm_le _ hnonneg).2
  intro t
  apply (BoundedContinuousFunction.norm_le hnonneg).2
  intro x
  rw [ofPathFamily_jet_apply]
  exact hC n t x


-- @@ L573-580 verbatim
theorem ofPathFamily_field_norm :
    ‖(ofPathFamily T hT f q hf hq hd C D hC hD).field‖ ≤ C 0 := by
  have hnonneg : 0 ≤ C 0 := (norm_nonneg _).trans (hC 0 ⟨0,le_rfl,hT⟩ 0)
  apply (ContinuousMap.norm_le _ hnonneg).2
  intro t
  apply (BoundedContinuousFunction.norm_le hnonneg).2
  intro x
  exact value_bound T f C hC t x


-- @@ L582-582 verbatim
end SmoothTimeField


-- @@ L584-584 verbatim
end

-- @@ L585-585 verbatim
end


-- @@ L587-587 verbatim
end


-- @@ L589-589 verbatim
@[expose] public section


-- @@ L591-591 verbatim
noncomputable section


-- @@ L593-593 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L595-595 verbatim
namespace EulerSmoothBanachFlow


-- @@ L597-597 verbatim
open Set EulerVolterraConvolution EulerContinuousTimeIntegral EulerSmoothFlowGevrey


-- @@ L599-601 verbatim
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)
  (B R : ℝ)


-- @@ L603-606 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E) :=
    inferInstance

-- @@ L607-609 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instSmoothFlowCoefficientPaths2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E) :=
    inferInstance

-- @@ L610-613 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] E))
    := inferInstance

-- @@ L614-617 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instSmoothFlowCoefficientPaths4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] E)) :=
    inferInstance


-- @@ L619-620 verbatim
variable (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B * R * T ≤ 1 / 8)
  (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)


-- @@ L622-626 verbatim
theorem displacementFamily_time_derivative (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (displacementFamily T hT A x))
      (velocityFamily T hT A x t) (Icc (0 : ℝ) T) t := by
  rw [displacementFamily_integral]
  exact integral_hasDerivWithinAt T hT _ t


-- @@ L628-639 verbatim
include hB hR hsmall hb in
theorem displacementFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => displacementFamily T hT A y t) x‖ ≤
      B*T*(4*R)^n*(n.factorial : ℝ)^2 := by
  have he : (fun y => displacementFamily T hT A y t) = displacement T hT A t := by
    funext y
    simp only [displacement, extendPath, projIcc_of_mem hT t.property]
  rw [he]
  apply (displacement_bound T hT A B R hB hR hsmall hb n t t.property x).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left t.property.2 hB)
      (pow_nonneg (by positivity) n)) (sq_nonneg _)


-- @@ L641-645 verbatim
include hB hR hsmall hb in
theorem velocityFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => velocityFamily T hT A y t) x‖ ≤
      B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2 :=
  materialVelocity_bound T hT A B R hB hR hsmall hb n t x


-- @@ L647-656 verbatim
/-- Displacement coefficient, constructed using `SmoothTimeField.ofPathFamily`. -/
def displacementCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  SmoothTimeField.ofPathFamily T hT
    (displacementFamily T hT A) (velocityFamily T hT A)
    (displacementFamily_contDiff T hT A) (velocityFamily_contDiff T hT A)
    (displacementFamily_time_derivative T hT A)
    (fun n => B*T*(4*R)^n*(n.factorial : ℝ)^2)
    (fun n => B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2)
    (displacementFamily_jet_bound T hT A B R hB hR hsmall hb)
    (velocityFamily_jet_bound T hT A B R hB hR hsmall hb)


-- @@ L658-660 verbatim
@[simp] theorem displacementCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (displacementCoefficient T hT A B R hB hR hsmall hb).field t x =
      (flowData T hT A).forward t x-x := rfl


-- @@ L662-665 verbatim
theorem displacementCoefficient_jet_norm (n : ℕ) :
    ‖(displacementCoefficient T hT A B R hB hR hsmall hb).jet n‖ ≤
      B*T*(4*R)^n*(n.factorial : ℝ)^2 := by
  apply SmoothTimeField.ofPathFamily_jet_norm


-- @@ L667-670 verbatim
variable (A₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
  (htime : SmoothTimeField.TimeDerivative T hT A A₁)
  (B₁ R₁ : ℝ) (hB₁ : 0 ≤ B₁) (hR₁ : 0 ≤ R₁)
  (hb₁ : ∀ n, ‖A₁.jet n‖ ≤ B₁ * R₁ ^ n * (n.factorial : ℝ) ^ 2)


-- @@ L672-679 verbatim
include hB hR hsmall hb hB₁ hR₁ hb₁ in
theorem accelerationFamily_jet_bound (n : ℕ) (t : Icc (0 : ℝ) T) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => accelerationFamily T hT A A₁ y t) x‖ ≤
      (B₁+3*B^2*R)*(flowRadius B R T (4*R+R₁))^n*(n.factorial : ℝ)^2 := by
  have he : (fun y => accelerationFamily T hT A A₁ y t) =
      materialAcceleration T hT A A₁ t := funext (fun y => accelerationFamily_apply T hT A A₁ y t)
  rw [he]
  exact materialAcceleration_bound T hT A A₁ B R B₁ R₁ hB hR hB₁ hR₁ hsmall hb hb₁ n t x


-- @@ L681-690 verbatim
/-- Velocity coefficient, constructed using `SmoothTimeField.ofPathFamily`. -/
def velocityCoefficient : SmoothTimeField (Icc (0 : ℝ) T) E E :=
  SmoothTimeField.ofPathFamily T hT
    (velocityFamily T hT A) (accelerationFamily T hT A A₁)
    (velocityFamily_contDiff T hT A) (accelerationFamily_contDiff T hT A A₁)
    (velocityFamily_time_derivative T hT A A₁ htime)
    (fun n => B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2)
    (fun n => (B₁+3*B^2*R)*(flowRadius B R T (4*R+R₁))^n*(n.factorial : ℝ)^2)
    (velocityFamily_jet_bound T hT A B R hB hR hsmall hb)
    (accelerationFamily_jet_bound T hT A B R hB hR hsmall hb A₁ B₁ R₁ hB₁ hR₁ hb₁)


-- @@ L692-694 verbatim
@[simp] theorem velocityCoefficient_apply (t : Icc (0 : ℝ) T) (x : E) :
    (velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁).field t x =
      A.field t ((flowData T hT A).forward t x) := rfl


-- @@ L696-699 verbatim
theorem velocityCoefficient_jet_norm (n : ℕ) :
    ‖(velocityCoefficient T hT A B R hB hR hsmall hb A₁ htime B₁ R₁ hB₁ hR₁ hb₁).jet n‖ ≤
      B*(flowRadius B R T R)^n*(n.factorial : ℝ)^2 := by
  apply SmoothTimeField.ofPathFamily_jet_norm


-- @@ L701-701 verbatim
end EulerSmoothBanachFlow
