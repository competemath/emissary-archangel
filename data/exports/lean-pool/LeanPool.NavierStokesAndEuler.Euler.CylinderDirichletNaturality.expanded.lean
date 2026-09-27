/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderTranslationAdjoint
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedEvolution
import LeanPool.NavierStokesAndEuler.Euler.TimeH1ReconstructionNaturality
public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedSpaceInverse


-- @@ L16-22 verbatim
/-!
# Spatial intertwiners for the actual cylinder history

These are consequences of the constructed variational inverse and Gram
inverse. Subsequent support and translation lemmas discharge the displayed
coefficient identities for their actual spatial maps.
-/


-- @@ L24-24 verbatim
section


-- @@ L26-32 verbatim
/-!
# Naturality of the genuine continuous Dirichlet velocity

The constructed coordinate acceleration and its bounded H¹ reconstruction
commute with the same spatial intertwiners as the variational inverse. This
transports the actual continuous history path, including its endpoint values.
-/


-- @@ L34-34 verbatim
section


-- @@ L36-42 verbatim
/-!
# Naturality of the actual fixed-frame Dirichlet inverse

Bounded spatial maps preserving the coefficients and their adjoint test maps
commute with the constructed coercive solve. This covers translations and
spatial support projections on actual L², not just pointwise model solutions.
-/


-- @@ L44-44 verbatim
@[expose] public section


-- @@ L46-46 verbatim
noncomputable section


-- @@ L48-48 verbatim
namespace EulerFixedFrameNaturality


-- @@ L50-52 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerTerminalTimePrimitive EulerVolterraConvolution EulerTimeH1OperatorProduct
  EulerTimeH1FrameTransport EulerTransverseFixedSpaceInverse EulerTimeLpBoundedMap


-- @@ L54-59 verbatim
variable {U V E F : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (T : ℝ) (hT : 0 ≤ T)


-- @@ L61-68 verbatim
/-- The genuine bounded spatial map on the fixed zero-trace derivative space. -/
def zeroTraceMap (A : U →L[ℝ] V) :
    zeroTraceDerivatives (U := U) T hT →L[ℝ] zeroTraceDerivatives (U := V) T hT :=
  ((timeLift T A).comp (zeroTraceDerivatives (U := U) T hT).subtypeL).codRestrict
    (zeroTraceDerivatives (U := V) T hT) (fun u => by
      change initialTrace T hT (timeLift T A (u : TimeLp T U)) = 0
      have hu : initialTrace T hT (u : TimeLp T U) = 0 := u.property
      rw [initialTrace_timeLift,hu,map_zero])


-- @@ L70-71 verbatim
@[simp] theorem zeroTraceMap_coe (A : U →L[ℝ] V) (u : zeroTraceDerivatives (U := U) T hT) :
    (zeroTraceMap T hT A u : TimeLp T V) = timeLift T A (u : TimeLp T U) := rfl


-- @@ L73-76 verbatim
theorem zeroTraceMap_norm (A : U →L[ℝ] V) : ‖zeroTraceMap T hT A‖ ≤ ‖A‖ := by
  apply opNorm_le_bound _ (norm_nonneg A)
  intro u
  exact timeLift_apply_norm_le T A (u : TimeLp T U)


-- @@ L78-87 verbatim
omit [CompleteSpace U] [CompleteSpace V] [CompleteSpace E] [CompleteSpace F] in
theorem timeMultiplier_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u)) (u : TimeLp T U) :
    timeMultiplier T hT R (timeLift T A u) = timeLift T B (timeMultiplier T hT Q u) := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT R (timeLift T A u),timeLift_ae T A u,
    timeLift_ae T B (timeMultiplier T hT Q u),timeMultiplier_ae T hT Q u] with t hr ha hb hq
  rw [hr,ha,hb,hq]
  exact hQR (projIcc 0 T hT t) (u t)


-- @@ L89-100 verbatim
omit [CompleteSpace E] [CompleteSpace F] in
theorem productDerivative_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u)) (u : TimeLp T U) :
    productDerivative T hT R R₁ (timeLift T A u) = timeLift T B (productDerivative T hT Q Q₁ u) :=
        by
  change timeMultiplier T hT R₁ (primitiveTimeLp T hT (timeLift T A u)) +
      timeMultiplier T hT R (timeLift T A u) =
    timeLift T B (timeMultiplier T hT Q₁ (primitiveTimeLp T hT u)+timeMultiplier T hT Q u)
  rw [primitiveTimeLp_timeLift,timeMultiplier_intertwines T hT A B Q₁ R₁ hQR₁,
    timeMultiplier_intertwines T hT A B Q R hQR,map_add]


-- @@ L102-109 verbatim
omit [CompleteSpace E] [CompleteSpace F] in
theorem fixedDerivative_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u)) (u : zeroTraceDerivatives (U := U) T hT) :
    fixedFrameDerivative T hT R R₁ (zeroTraceMap T hT A u) =
      timeLift T B (fixedFrameDerivative T hT Q Q₁ u) :=
  productDerivative_intertwines T hT A B Q Q₁ R R₁ hQR hQR₁ (u : TimeLp T U)


-- @@ L111-120 verbatim
theorem fixedPrimitive_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u)) (u : zeroTraceDerivatives (U := U) T hT) :
    fixedFramePrimitive T hT R R₁ (zeroTraceMap T hT A u) =
      timeLift T B (fixedFramePrimitive T hT Q Q₁ u) := by
  change primitiveTimeLp T hT (fixedFrameDerivative T hT R R₁ (zeroTraceMap T hT A u)) = _
  rw [fixedDerivative_intertwines T hT A B Q Q₁ R R₁ hQR hQR₁,
    primitiveTimeLp_timeLift]
  rfl


-- @@ L122-152 verbatim
/-- A coefficient intertwiner and its adjoint preserve the actual variational
solve, as follows by testing against the genuine pulled-back test field. -/
theorem fixedFrameSolver_intertwines
    (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (J : C(Icc (0 : ℝ) T, F →L[ℝ] F))
    (c : ℝ) (hc : 0 < c) (hQ : ∀ t u, c * ‖u‖ ^ 2 ≤ ‖Q t u‖ ^ 2)
    (d : ℝ) (hd : 0 < d) (hR : ∀ t v, d * ‖v‖ ^ 2 ≤ ‖R t v‖ ^ 2)
    (hQtime : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hRtime : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT R) (R₁ t) (Icc (0 : ℝ) T) t)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hH : ∀ t u, ⟪H t u,u⟫_ℝ ≤ K*‖u‖^2) (hJ : ∀ t v, ⟪J t v,v⟫_ℝ ≤ L*‖v‖^2)
    (hsmall : K*(T^2/2) ≤ 1/2) (hsmall' : L*(T^2/2) ≤ 1/2)
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u))
    (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v))
    (hRQ₁ : ∀ t v, Q₁ t (A.adjoint v) = B.adjoint (R₁ t v))
    (hHJ : ∀ t u, J t (B u) = B (H t u)) (f : TimeLp T E) :
    zeroTraceMap T hT A (fixedFrameSolver T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f) =
      fixedFrameSolver T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f) := by
  apply fixedFrameSolver_unique T hT R R₁ J d hd hR hRtime L hL hJ hsmall'
  intro v
  have hw := fixedFrameSolver_weak T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f
    (zeroTraceMap T hT A.adjoint v)
  rw [fixedDerivative_intertwines T hT A.adjoint B.adjoint R R₁ Q Q₁ hRQ hRQ₁,
    fixedPrimitive_intertwines T hT A.adjoint B.adjoint R R₁ Q Q₁ hRQ hRQ₁] at hw
  simp only [← timeLift_adjoint,adjoint_inner_right] at hw
  rw [fixedDerivative_intertwines T hT A B Q Q₁ R R₁ hQR hQR₁,
    fixedPrimitive_intertwines T hT A B Q Q₁ R R₁ hQR hQR₁,
    timeMultiplier_intertwines T hT B B H J hHJ]
  exact hw


-- @@ L154-154 verbatim
end EulerFixedFrameNaturality


-- @@ L156-156 verbatim
end

-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end


-- @@ L161-161 verbatim
@[expose] public section


-- @@ L163-163 verbatim
noncomputable section


-- @@ L165-165 verbatim
namespace EulerFixedFrameNaturality


-- @@ L167-170 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerVolterraConvolution EulerTimeLpBoundedMap EulerTimeLpGramInverse
  EulerCoerciveProjection EulerTransverseFixedEvolution EulerTimeH1Reconstruction
  EulerTimeH1FrameTransport


-- @@ L172-177 verbatim
variable {U V E F : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (T : ℝ) (hT : 0 ≤ T)


-- @@ L179-189 verbatim
/-- The backward test intertwiner gives the actual adjoint-multiplier identity. -/
theorem adjointMultiplier_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v)) (f : TimeLp T E) :
    (timeMultiplier T hT R).adjoint (timeLift T B f) =
      timeLift T A ((timeMultiplier T hT Q).adjoint f) := by
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left,← adjoint_inner_right, timeLift_adjoint,
    ← timeMultiplier_intertwines T hT A.adjoint B.adjoint R Q hRQ,
    ← adjoint_inner_left,← timeLift_adjoint,adjoint_inner_right]


-- @@ L191-200 verbatim
/-- The true Gram operator commutes with compatible rectangular intertwiners. -/
theorem gramOperator_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v)) (u : TimeLp T U) :
    gramOperator T hT R (timeLift T A u) = timeLift T A (gramOperator T hT Q u) := by
  change (timeMultiplier T hT R).adjoint (timeMultiplier T hT R (timeLift T A u)) = _
  rw [timeMultiplier_intertwines T hT A B Q R hQR,
    adjointMultiplier_intertwines T hT A B Q R hRQ]
  rfl


-- @@ L202-221 verbatim
/-- The constructed Gram inverse inherits the intertwining identity by its
two-sided inverse property. -/
theorem gramSolver_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R : C(Icc (0 : ℝ) T, V →L[ℝ] F))
    (c : ℝ) (hc : 0 < c) (hQ : ∀ t u, c * ‖u‖ ^ 2 ≤ ‖Q t u‖ ^ 2)
    (d : ℝ) (hd : 0 < d) (hR : ∀ t v, d * ‖v‖ ^ 2 ≤ ‖R t v‖ ^ 2)
    (hQR : ∀ t u, R t (A u) = B (Q t u))
    (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v)) (f : TimeLp T U) :
    gramSolver T hT R d hd hR (timeLift T A f) =
      timeLift T A (gramSolver T hT Q c hc hQ f) := by
  have he := gramOperator_intertwines T hT A B Q R hQR hRQ
    (gramSolver T hT Q c hc hQ f)
  change gramOperator T hT R (timeLift T A (gramSolver T hT Q c hc hQ f)) =
    timeLift T A (gramOperator T hT Q (coerciveInverse (gramOperator T hT Q) c hc
      (gramOperator_coercive T hT Q c hQ) f)) at he
  rw [operator_inverse_apply] at he
  have hi := inverse_operator_apply (gramOperator T hT R) d hd
    (gramOperator_coercive T hT R d hR) (timeLift T A (gramSolver T hT Q c hc hQ f))
  rw [he] at hi
  exact hi


-- @@ L223-237 verbatim
variable (A : U →L[ℝ] V) (B : E →L[ℝ] F)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (R R₁ : C(Icc (0 : ℝ) T, V →L[ℝ] F))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (J : C(Icc (0 : ℝ) T, F →L[ℝ] F))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t u, c * ‖u‖ ^ 2 ≤ ‖Q t u‖ ^ 2)
  (d : ℝ) (hd : 0 < d) (hR : ∀ t v, d * ‖v‖ ^ 2 ≤ ‖R t v‖ ^ 2)
  (hQtime : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (hRtime : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT R) (R₁ t) (Icc (0 : ℝ) T) t)
  (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
  (hH : ∀ t u, ⟪H t u, u⟫_ℝ ≤ K * ‖u‖ ^ 2) (hJ : ∀ t v, ⟪J t v, v⟫_ℝ ≤ L * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2) (hsmall' : L * (T ^ 2 / 2) ≤ 1 / 2)
  (hQR : ∀ t u, R t (A u) = B (Q t u))
  (hQR₁ : ∀ t u, R₁ t (A u) = B (Q₁ t u))
  (hRQ : ∀ t v, Q t (A.adjoint v) = B.adjoint (R t v))
  (hRQ₁ : ∀ t v, Q₁ t (A.adjoint v) = B.adjoint (R₁ t v))
  (hHJ : ∀ t u, J t (B u) = B (H t u))


-- @@ L239-247 verbatim
include hQR hQR₁ hRQ hRQ₁ hHJ in
theorem velocityLp_intertwines (f : TimeLp T E) :
    velocityLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f) =
      timeLift T A (velocityLp T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f) := by
  have he := fixedFrameSolver_intertwines T hT A B Q Q₁ R R₁ H J
    c hc hQ d hd hR hQtime hRtime K L hK hL hH hJ hsmall hsmall'
    hQR hQR₁ hRQ hRQ₁ hHJ f
  have he' := congrArg (fun z : zeroTraceDerivatives (U := V) T hT => (z : TimeLp T V)) he
  exact he'.symm


-- @@ L249-261 verbatim
include hQR hQR₁ hRQ hRQ₁ hHJ in
theorem accelerationLp_intertwines (f : TimeLp T E) :
    accelerationLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f) =
      timeLift T A (accelerationLp T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f) := by
  change gramSolver T hT R d hd hR ((timeMultiplier T hT R).adjoint
    (timeLift T B f-(2 : ℝ) • timeMultiplier T hT R₁
      (velocityLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f)))) = _
  rw [velocityLp_intertwines T hT A B Q Q₁ R R₁ H J c hc hQ d hd hR hQtime hRtime
    K L hK hL hH hJ hsmall hsmall' hQR hQR₁ hRQ hRQ₁ hHJ,
    timeMultiplier_intertwines T hT A B Q₁ R₁ hQR₁,
    ← map_smul,← map_sub,adjointMultiplier_intertwines T hT A B Q R hRQ,
    gramSolver_intertwines T hT A B Q R c hc hQ d hd hR hQR hRQ]
  rfl


-- @@ L263-277 verbatim
include hQR hQR₁ hRQ hRQ₁ hHJ in
/-- The identity holds at every time, including the endpoint used by the
subsequent forward solve. -/
theorem velocityPath_intertwines (f : TimeLp T E) (t : Icc (0 : ℝ) T) :
    velocityPath T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f) t =
      A (velocityPath T hT Q Q₁ H c hc hQ hQtime K hK hH hsmall f t) := by
  change reconstruction T hT
    (velocityLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f),
      accelerationLp T hT R R₁ J d hd hR hRtime L hL hJ hsmall' (timeLift T B f)) t = _
  rw [velocityLp_intertwines T hT A B Q Q₁ R R₁ H J c hc hQ d hd hR hQtime hRtime
    K L hK hL hH hJ hsmall hsmall' hQR hQR₁ hRQ hRQ₁ hHJ,
    accelerationLp_intertwines T hT A B Q Q₁ R R₁ H J c hc hQ d hd hR hQtime hRtime
    K L hK hL hH hJ hsmall hsmall' hQR hQR₁ hRQ hRQ₁ hHJ,
    reconstruction_timeLift]
  rfl


-- @@ L279-279 verbatim
end EulerFixedFrameNaturality


-- @@ L281-281 verbatim
end

-- @@ L282-282 verbatim
end


-- @@ L284-284 verbatim
end


-- @@ L286-286 verbatim
section


-- @@ L288-288 verbatim
/-! Compatible spatial maps commute with the genuine positive Gram inverse. -/


-- @@ L290-290 verbatim
@[expose] public section


-- @@ L292-292 verbatim
noncomputable section


-- @@ L294-294 verbatim
namespace EulerGramNaturality


-- @@ L296-296 verbatim
open ContinuousLinearMap InnerProductSpace EulerTransverseGramInverse


-- @@ L298-302 verbatim
variable {U V E F : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]


-- @@ L304-311 verbatim
theorem adjoint_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : U →L[ℝ] E) (R : V →L[ℝ] F)
    (hback : ∀ v, Q (A.adjoint v) = B.adjoint (R v)) (f : E) :
    R.adjoint (B f) = A (Q.adjoint f) := by
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left,← adjoint_inner_right,← hback,
    ← adjoint_inner_left,adjoint_inner_right]


-- @@ L313-320 verbatim
theorem gram_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : U →L[ℝ] E) (R : V →L[ℝ] F)
    (hforward : ∀ u, R (A u) = B (Q u))
    (hback : ∀ v, Q (A.adjoint v) = B.adjoint (R v)) (u : U) :
    gram R (A u) = A (gram Q u) := by
  change R.adjoint (R (A u)) = _
  rw [hforward,adjoint_intertwines A B Q R hback]
  rfl


-- @@ L322-333 verbatim
theorem gramInverse_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q : U →L[ℝ] E) (R : V →L[ℝ] F)
    (c : ℝ) (hc : 0 < c) (hQ : ∀ u, c * ‖u‖ ^ 2 ≤ ‖Q u‖ ^ 2)
    (d : ℝ) (hd : 0 < d) (hR : ∀ v, d * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2)
    (hforward : ∀ u, R (A u) = B (Q u))
    (hback : ∀ v, Q (A.adjoint v) = B.adjoint (R v)) (f : U) :
    gramInverse R d hd hR (A f) = A (gramInverse Q c hc hQ f) := by
  have he := gram_intertwines A B Q R hforward hback (gramInverse Q c hc hQ f)
  rw [gram_inverse_apply] at he
  have hi := congrArg (gramInverse R d hd hR) he
  rw [inverse_gram_apply] at hi
  exact hi.symm


-- @@ L335-347 verbatim
/-- In particular the actual acceleration formula respects a compatible
coordinate map and physical map. -/
theorem acceleration_intertwines (A : U →L[ℝ] V) (B : E →L[ℝ] F)
    (Q Q₁ : U →L[ℝ] E) (R R₁ : V →L[ℝ] F)
    (c : ℝ) (hc : 0 < c) (hQ : ∀ u, c * ‖u‖ ^ 2 ≤ ‖Q u‖ ^ 2)
    (d : ℝ) (hd : 0 < d) (hR : ∀ v, d * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2)
    (hforward : ∀ u, R (A u) = B (Q u))
    (hforward₁ : ∀ u, R₁ (A u) = B (Q₁ u))
    (hback : ∀ v, Q (A.adjoint v) = B.adjoint (R v)) (f : E) (v : U) :
    gramInverse R d hd hR (R.adjoint (B f-(2 : ℝ) • R₁ (A v))) =
      A (gramInverse Q c hc hQ (Q.adjoint (f-(2 : ℝ) • Q₁ v))) := by
  rw [hforward₁,← map_smul,← map_sub,adjoint_intertwines A B Q R hback,
    gramInverse_intertwines A B Q R c hc hQ d hd hR hforward hback]


-- @@ L349-349 verbatim
end EulerGramNaturality


-- @@ L351-351 verbatim
end

-- @@ L352-352 verbatim
end


-- @@ L354-354 verbatim
end


-- @@ L356-356 verbatim
@[expose] public section


-- @@ L358-358 verbatim
noncomputable section


-- @@ L360-362 verbatim
namespace EulerCylinderDirichlet.Coefficients

-- Naturality uses the solver identities without unfolding the constructed inverse.

-- @@ L363-365 verbatim
attribute [local irreducible] EulerTransverseFixedSpaceInverse.fixedFrameSolver
  EulerTransverseFixedEvolution.velocityLp EulerTransverseFixedEvolution.accelerationLp
  EulerTransverseFixedEvolution.velocityPath


-- @@ L367-369 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerVolterraConvolution EulerLpCylinderTranslation EulerTimeLpBoundedMap
  EulerTransverseGramInverse


-- @@ L371-383 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U V E F : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (D : Coefficients T U E) (G : Coefficients T V F)
  (A : CylinderL2 P U →L[ℝ] CylinderL2 P V)
  (B : CylinderL2 P E →L[ℝ] CylinderL2 P F)
  (hQ : ∀ t u, G.frame P t (A u) = B (D.frame P t u))
  (hQ₁ : ∀ t u, G.frameDerivative P t (A u) = B (D.frameDerivative P t u))
  (hback : ∀ t v, D.frame P t (A.adjoint v) = B.adjoint (G.frame P t v))
  (hback₁ : ∀ t v, D.frameDerivative P t (A.adjoint v) = B.adjoint (G.frameDerivative P t v))
  (hH : ∀ t u, G.hessian P t (B u) = B (D.hessian P t u))


-- @@ L385-385 verbatim
include hQ hQ₁ hback hback₁ hH


-- @@ L387-394 verbatim
theorem velocityLp_intertwines (f : TimeLp T (CylinderL2 P E)) :
    G.velocityLp P (timeLift T B f) = timeLift T A (D.velocityLp P f) :=
  EulerFixedFrameNaturality.velocityLp_intertwines T D.time_pos.le A B
    (D.frame P) (D.frameDerivative P) (G.frame P) (G.frameDerivative P) (D.hessian P) (G.hessian P)
    D.lower D.lower_pos (D.frame_lower P) G.lower G.lower_pos (G.frame_lower P)
    (D.frame_derivative P) (G.frame_derivative P) D.potential G.potential
    D.potential_nonneg G.potential_nonneg (D.hessian_upper P) (G.hessian_upper P)
    D.small G.small hQ hQ₁ hback hback₁ hH f


-- @@ L396-403 verbatim
theorem accelerationLp_intertwines (f : TimeLp T (CylinderL2 P E)) :
    G.accelerationLp P (timeLift T B f) = timeLift T A (D.accelerationLp P f) :=
  EulerFixedFrameNaturality.accelerationLp_intertwines T D.time_pos.le A B
    (D.frame P) (D.frameDerivative P) (G.frame P) (G.frameDerivative P) (D.hessian P) (G.hessian P)
    D.lower D.lower_pos (D.frame_lower P) G.lower G.lower_pos (G.frame_lower P)
    (D.frame_derivative P) (G.frame_derivative P) D.potential G.potential
    D.potential_nonneg G.potential_nonneg (D.hessian_upper P) (G.hessian_upper P)
    D.small G.small hQ hQ₁ hback hback₁ hH f


-- @@ L405-412 verbatim
theorem velocityPath_intertwines (f : TimeLp T (CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.velocityPath P (timeLift T B f) t = A (D.velocityPath P f t) :=
  EulerFixedFrameNaturality.velocityPath_intertwines T D.time_pos.le A B
    (D.frame P) (D.frameDerivative P) (G.frame P) (G.frameDerivative P) (D.hessian P) (G.hessian P)
    D.lower D.lower_pos (D.frame_lower P) G.lower G.lower_pos (G.frame_lower P)
    (D.frame_derivative P) (G.frame_derivative P) D.potential G.potential
    D.potential_nonneg G.potential_nonneg (D.hessian_upper P) (G.hessian_upper P)
    D.small G.small hQ hQ₁ hback hback₁ hH f t


-- @@ L414-418 verbatim
theorem continuousVelocity_intertwines (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.velocityPath P (pathLp T G.time_pos.le (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) t =
      A (D.velocityPath P (pathLp T D.time_pos.le f) t) := by
  rw [pathLp_timeLift]
  exact D.velocityPath_intertwines P G A B hQ hQ₁ hback hback₁ hH _ t


-- @@ L420-430 verbatim
theorem accelerationPath_intertwines (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.accelerationPath P (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) t =
      A (D.accelerationPath P f t) := by
  change gramInverse (G.frame P t) G.lower G.lower_pos (G.frame_lower P t)
    ((G.frame P t).adjoint (B (f t)-(2 : ℝ) • G.frameDerivative P t
      (G.velocityPath P (pathLp T G.time_pos.le (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) t))) = _
  rw [continuousVelocity_intertwines P D G A B hQ hQ₁ hback hback₁ hH]
  exact EulerGramNaturality.acceleration_intertwines A B
    (D.frame P t) (D.frameDerivative P t) (G.frame P t) (G.frameDerivative P t)
    D.lower D.lower_pos (D.frame_lower P t) G.lower G.lower_pos (G.frame_lower P t)
    (hQ t) (hQ₁ t) (hback t) (f t) (D.velocityPath P (pathLp T D.time_pos.le f) t)


-- @@ L432-438 verbatim
theorem physicalVelocity_intertwines (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.physicalVelocity P (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) t =
      B (D.physicalVelocity P f t) := by
  change G.frame P t
    (G.velocityPath P (pathLp T G.time_pos.le (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) t) = _
  rw [continuousVelocity_intertwines P D G A B hQ hQ₁ hback hback₁ hH,hQ]
  rfl


-- @@ L440-448 verbatim
theorem physicalDerivative_intertwines (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.physicalDerivative P (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) t =
      B (D.physicalDerivative P f t) := by
  change G.frameDerivative P t
      (G.velocityPath P (pathLp T G.time_pos.le (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) t) +
    G.frame P t (G.accelerationPath P (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) t) = _
  rw [continuousVelocity_intertwines P D G A B hQ hQ₁ hback hback₁ hH,
    accelerationPath_intertwines P D G A B hQ hQ₁ hback hback₁ hH,hQ₁,hQ,← map_add]
  rfl


-- @@ L450-450 verbatim
end EulerCylinderDirichlet.Coefficients
