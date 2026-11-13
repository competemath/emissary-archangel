import Submission.ConcreteZeroPairCassiniFrameAdapter
import Submission.ConcreteZeroPairSaddle
import Submission.PTEndpointLedgerStability


-- @@ L5-20 verbatim
/-!
# Exact intrinsic frame ledger of the twisted Cassini zero-pair saddle

The endpoint zero sets of the twisted Cassini cobordism are the usual two
incoming ovals and one outgoing oval.  The defining maps, however, carry a
nontrivial normal-plane coefficient.  This file combines the intrinsic-frame
adapter with the explicit coefficient winding:

* each incoming frame loop is `coefficient(1 turn) * standard(1 turn)`, hence
  has class zero;
* the outgoing frame loop is `coefficient(2 turns) * standard(1 turn)`, hence
  has class one.

It then enumerates all orbit components and proves the literal all-positive
endpoint ledgers `[0, 0]` and `[1]`.
-/


-- @@ L22-22 verbatim
set_option autoImplicit false

-- @@ L23-23 verbatim
set_option maxHeartbeats 1600000


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace Submission

-- @@ L28-28 verbatim
namespace ConcreteZeroPairCassiniFrameLedger


-- @@ L30-30 verbatim
open Set Function Matrix InnerProductSpace

-- @@ L31-31 verbatim
open scoped Topology Matrix RealInnerProductSpace unitInterval


-- @@ L33-33 verbatim
open ConcreteZeroPairCassiniTwist

-- @@ L34-34 verbatim
open ConcreteZeroPairCassiniWinding

-- @@ L35-35 verbatim
open ConcreteZeroPairCassiniCoefficientSO

-- @@ L36-36 verbatim
open ConcreteZeroPairCassiniFrameAdapter


-- @@ L38-38 verbatim
variable (m : ℕ)


-- @@ L40-40 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L42-42 verbatim
/-! ## The standard orbit curves in the twisted endpoint fibers -/


-- @@ L44-47 verbatim
theorem sourcePointRight_mem_source_fiber (hm : 0 < m) (theta : ℝ) :
    StandardSaddle.sourcePointRight m theta ∈ (sourceFLS m hm).fiber := by
  rw [source_fiber_eq_standard m hm]
  exact StandardSaddle.sourcePointRight_mem_source_fiber m theta


-- @@ L49-52 verbatim
theorem sourcePointLeft_mem_source_fiber (hm : 0 < m) (theta : ℝ) :
    StandardSaddle.sourcePointLeft m theta ∈ (sourceFLS m hm).fiber := by
  rw [source_fiber_eq_standard m hm]
  exact StandardSaddle.sourcePointLeft_mem_source_fiber m theta


-- @@ L54-57 verbatim
theorem targetPoint_mem_target_fiber (hm : 0 < m) (theta : ℝ) :
    StandardSaddle.targetPoint m theta ∈ (targetFLS m hm).fiber := by
  rw [target_fiber_eq_standard m hm]
  exact StandardSaddle.targetPoint_mem_target_fiber m theta


-- @@ L59-65 verbatim
theorem sourcePointRight_mem_orbit (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) (theta : ℝ) :
    StandardSaddle.sourcePointRight m theta ∈
      V.orbit (StandardSaddle.sourcePointRight m 0) := by
  exact V.continuousCurve_mem_orbit (StandardSaddle.sourcePointRight m)
    (StandardSaddle.continuous_sourcePointRight m)
    (sourcePointRight_mem_source_fiber m hm) theta


-- @@ L67-73 verbatim
theorem sourcePointLeft_mem_orbit (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) (theta : ℝ) :
    StandardSaddle.sourcePointLeft m theta ∈
      V.orbit (StandardSaddle.sourcePointLeft m 0) := by
  exact V.continuousCurve_mem_orbit (StandardSaddle.sourcePointLeft m)
    (StandardSaddle.continuous_sourcePointLeft m)
    (sourcePointLeft_mem_source_fiber m hm) theta


-- @@ L75-81 verbatim
theorem targetPoint_mem_orbit (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) (theta : ℝ) :
    StandardSaddle.targetPoint m theta ∈
      V.orbit (StandardSaddle.targetPoint m 0) := by
  exact V.continuousCurve_mem_orbit (StandardSaddle.targetPoint m)
    (StandardSaddle.continuous_targetPoint m)
    (targetPoint_mem_target_fiber m hm) theta


-- @@ L83-92 verbatim
def sourceRightSimpleClosedOrbitParam (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    SimpleClosedOrbitParam (sourceFLS m hm) V where
  p := StandardSaddle.sourcePointRight m 0
  hp := sourcePointRight_mem_source_fiber m hm 0
  curve := StandardSaddle.sourceCurveRight m
  curve_zero := StandardSaddle.sourceCurveRight_zero m
  curve_closed := StandardSaddle.sourceCurveRight_closed m
  curve_mem_orbit := fun _ => sourcePointRight_mem_orbit m hm V _
  curve_eq_cases := StandardSaddle.sourceCurveRight_eq_cases m


-- @@ L94-103 verbatim
def sourceLeftSimpleClosedOrbitParam (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    SimpleClosedOrbitParam (sourceFLS m hm) V where
  p := StandardSaddle.sourcePointLeft m 0
  hp := sourcePointLeft_mem_source_fiber m hm 0
  curve := StandardSaddle.sourceCurveLeft m
  curve_zero := StandardSaddle.sourceCurveLeft_zero m
  curve_closed := StandardSaddle.sourceCurveLeft_closed m
  curve_mem_orbit := fun _ => sourcePointLeft_mem_orbit m hm V _
  curve_eq_cases := StandardSaddle.sourceCurveLeft_eq_cases m


-- @@ L105-114 verbatim
def targetSimpleClosedOrbitParam (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) :
    SimpleClosedOrbitParam (targetFLS m hm) V where
  p := StandardSaddle.targetPoint m 0
  hp := targetPoint_mem_target_fiber m hm 0
  curve := StandardSaddle.targetCurve m
  curve_zero := StandardSaddle.targetCurve_zero m
  curve_closed := StandardSaddle.targetCurve_closed m
  curve_mem_orbit := fun _ => targetPoint_mem_orbit m hm V _
  curve_eq_cases := StandardSaddle.targetCurve_eq_cases m


-- @@ L116-116 verbatim
/-! ## Pointwise intrinsic frame-loop factorization -/


-- @@ L118-153 verbatim
theorem sourceRight_paramFrameLoop_apply (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) (u : I) :
    ((sourceRightSimpleClosedOrbitParam m hm V).paramFrameLoop u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      (sourceCoefficientLoop m u :
          Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
        rowsMatrix (StandardSaddle.endpointUnitFrame m (-1 / 2)
          (StandardSaddle.sourcePointRight m
            (2 * Real.pi * (u : ℝ)))) := by
  change frameLoop (sourceFLS m hm)
      (sourceRightSimpleClosedOrbitParam m hm V).realCurve (u : ℝ) = _
  unfold frameLoop
  rw [(sourceRightSimpleClosedOrbitParam m hm V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (sourceFLS m hm)
        (StandardSaddle.sourcePointRight m
          (2 * Real.pi * (u : ℝ))))) = _
  rw [gramSchmidtNormed_frameAt_source m hm
      (sourcePointRight_mem_source_fiber m hm _),
    rowsMatrix_frameRowAction]
  have hcoeff :
      ((coefficientSO m
          (twistRe m (spaceTime (StandardSaddle.sourcePointRight m
            (2 * Real.pi * (u : ℝ))) 0))
          (twistIm m (spaceTime (StandardSaddle.sourcePointRight m
            (2 * Real.pi * (u : ℝ))) 0))
          (sourceCoefficient_normSq_pos m hm
            (sourcePointRight_mem_source_fiber m hm _)) : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      fullCoefficientBlock m
        (Real.cos (2 * Real.pi * (u : ℝ)))
        (Real.sin (2 * Real.pi * (u : ℝ))) := by
    simpa only [twistRe_sourceRight, twistIm_sourceRight] using
      coefficientSO_smul_polar m StandardSaddle.sourceScale_pos
        (2 * Real.pi * (u : ℝ))
  rw [hcoeff, sourceCoefficientLoop_coe]


-- @@ L155-190 verbatim
theorem sourceLeft_paramFrameLoop_apply (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) (u : I) :
    ((sourceLeftSimpleClosedOrbitParam m hm V).paramFrameLoop u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      (sourceCoefficientLoop m u :
          Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
        rowsMatrix (StandardSaddle.endpointUnitFrame m (-1 / 2)
          (StandardSaddle.sourcePointLeft m
            (2 * Real.pi * (u : ℝ)))) := by
  change frameLoop (sourceFLS m hm)
      (sourceLeftSimpleClosedOrbitParam m hm V).realCurve (u : ℝ) = _
  unfold frameLoop
  rw [(sourceLeftSimpleClosedOrbitParam m hm V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (sourceFLS m hm)
        (StandardSaddle.sourcePointLeft m
          (2 * Real.pi * (u : ℝ))))) = _
  rw [gramSchmidtNormed_frameAt_source m hm
      (sourcePointLeft_mem_source_fiber m hm _),
    rowsMatrix_frameRowAction]
  have hcoeff :
      ((coefficientSO m
          (twistRe m (spaceTime (StandardSaddle.sourcePointLeft m
            (2 * Real.pi * (u : ℝ))) 0))
          (twistIm m (spaceTime (StandardSaddle.sourcePointLeft m
            (2 * Real.pi * (u : ℝ))) 0))
          (sourceCoefficient_normSq_pos m hm
            (sourcePointLeft_mem_source_fiber m hm _)) : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      fullCoefficientBlock m
        (Real.cos (2 * Real.pi * (u : ℝ)))
        (Real.sin (2 * Real.pi * (u : ℝ))) := by
    simpa only [twistRe_sourceLeft, twistIm_sourceLeft] using
      coefficientSO_smul_polar m StandardSaddle.sourceScale_pos
        (2 * Real.pi * (u : ℝ))
  rw [hcoeff, sourceCoefficientLoop_coe]


-- @@ L192-225 verbatim
theorem target_paramFrameLoop_apply (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) (u : I) :
    ((targetSimpleClosedOrbitParam m hm V).paramFrameLoop u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      (targetCoefficientLoop m u :
          Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
        rowsMatrix (StandardSaddle.endpointUnitFrame m (1 / 2)
          (StandardSaddle.targetPoint m
            (2 * Real.pi * (u : ℝ)))) := by
  change frameLoop (targetFLS m hm)
      (targetSimpleClosedOrbitParam m hm V).realCurve (u : ℝ) = _
  unfold frameLoop
  rw [(targetSimpleClosedOrbitParam m hm V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (targetFLS m hm)
        (StandardSaddle.targetPoint m
          (2 * Real.pi * (u : ℝ))))) = _
  rw [gramSchmidtNormed_frameAt_target m hm
      (targetPoint_mem_target_fiber m hm _),
    rowsMatrix_frameRowAction]
  have hcoeff :
      ((coefficientSO m
          (twistRe m (spaceTime (StandardSaddle.targetPoint m
            (2 * Real.pi * (u : ℝ))) 1))
          (twistIm m (spaceTime (StandardSaddle.targetPoint m
            (2 * Real.pi * (u : ℝ))) 1))
          (targetCoefficient_normSq_pos m hm
            (targetPoint_mem_target_fiber m hm _)) : SOGroup (m + 3)) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      (targetCoefficientLoop m u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) := by
    rw [coefficientSO_coe, targetCoefficientLoop_coe]
    simp only [twistRe_target, twistIm_target]
  rw [hcoeff]


-- @@ L227-241 verbatim
theorem sourceRight_paramFrameLoop_eq_mul_standard (hm : 0 < m)
    (V : TamedField (sourceFLS m hm))
    (W : TamedField (StandardSaddle.sourceFLS m)) :
    (sourceRightSimpleClosedOrbitParam m hm V).paramFrameLoop =
      sourceCoefficientLoop m *
        (StandardSaddle.sourceRightSimpleClosedOrbitParam m W).paramFrameLoop := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [sourceRight_paramFrameLoop_apply m hm V u]
  change _ = (sourceCoefficientLoop m u :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
    ((StandardSaddle.sourceRightSimpleClosedOrbitParam m W).paramFrameLoop u :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
  rw [StandardSaddle.sourceRight_paramFrameLoop_apply m W u]


-- @@ L243-257 verbatim
theorem sourceLeft_paramFrameLoop_eq_mul_standard (hm : 0 < m)
    (V : TamedField (sourceFLS m hm))
    (W : TamedField (StandardSaddle.sourceFLS m)) :
    (sourceLeftSimpleClosedOrbitParam m hm V).paramFrameLoop =
      sourceCoefficientLoop m *
        (StandardSaddle.sourceLeftSimpleClosedOrbitParam m W).paramFrameLoop := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [sourceLeft_paramFrameLoop_apply m hm V u]
  change _ = (sourceCoefficientLoop m u :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
    ((StandardSaddle.sourceLeftSimpleClosedOrbitParam m W).paramFrameLoop u :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
  rw [StandardSaddle.sourceLeft_paramFrameLoop_apply m W u]


-- @@ L259-273 verbatim
theorem target_paramFrameLoop_eq_mul_standard (hm : 0 < m)
    (V : TamedField (targetFLS m hm))
    (W : TamedField (StandardSaddle.targetFLS m)) :
    (targetSimpleClosedOrbitParam m hm V).paramFrameLoop =
      targetCoefficientLoop m *
        (StandardSaddle.targetSimpleClosedOrbitParam m W).paramFrameLoop := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [target_paramFrameLoop_apply m hm V u]
  change _ = (targetCoefficientLoop m u :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) *
    ((StandardSaddle.targetSimpleClosedOrbitParam m W).paramFrameLoop u :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
  rw [StandardSaddle.target_paramFrameLoop_apply m W u]


-- @@ L275-275 verbatim
/-! ## The three intrinsic frame classes -/


-- @@ L277-303 verbatim
theorem sourceRight_paramFrameClass_eq_zero (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    loopClassZ2 (sourceRightSimpleClosedOrbitParam m hm V).paramFrameLoop
        (sourceRightSimpleClosedOrbitParam m hm V).paramFrameLoop_closed = 0 := by
  let W : TamedField (StandardSaddle.sourceFLS m) :=
    (StandardSaddle.sourceFLS m).exists_tamedField.some
  let P := sourceRightSimpleClosedOrbitParam m hm V
  let Q := StandardSaddle.sourceRightSimpleClosedOrbitParam m W
  let R := sourceCoefficientLoop m * Q.paramFrameLoop
  have hRclosed : R 0 = R 1 := by
    change sourceCoefficientLoop m 0 * Q.paramFrameLoop 0 =
      sourceCoefficientLoop m 1 * Q.paramFrameLoop 1
    rw [sourceCoefficientLoop_closed, Q.paramFrameLoop_closed]
  have heq : P.paramFrameLoop = R :=
    sourceRight_paramFrameLoop_eq_mul_standard m hm V W
  calc
    loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
        loopClassZ2 R hRclosed :=
      loopClassZ2_congr_fun P.paramFrameLoop_closed hRclosed heq
    _ = loopClassZ2 (sourceCoefficientLoop m)
          (sourceCoefficientLoop_closed m) +
        loopClassZ2 Q.paramFrameLoop Q.paramFrameLoop_closed := by
      exact loopClassZ2_mul _ _ _ _ _
    _ = 1 + 1 := by
      rw [loopClassZ2_sourceCoefficientLoop,
        StandardSaddle.sourceRight_paramFrameClass_eq_one]
    _ = 0 := by decide


-- @@ L305-331 verbatim
theorem sourceLeft_paramFrameClass_eq_zero (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    loopClassZ2 (sourceLeftSimpleClosedOrbitParam m hm V).paramFrameLoop
        (sourceLeftSimpleClosedOrbitParam m hm V).paramFrameLoop_closed = 0 := by
  let W : TamedField (StandardSaddle.sourceFLS m) :=
    (StandardSaddle.sourceFLS m).exists_tamedField.some
  let P := sourceLeftSimpleClosedOrbitParam m hm V
  let Q := StandardSaddle.sourceLeftSimpleClosedOrbitParam m W
  let R := sourceCoefficientLoop m * Q.paramFrameLoop
  have hRclosed : R 0 = R 1 := by
    change sourceCoefficientLoop m 0 * Q.paramFrameLoop 0 =
      sourceCoefficientLoop m 1 * Q.paramFrameLoop 1
    rw [sourceCoefficientLoop_closed, Q.paramFrameLoop_closed]
  have heq : P.paramFrameLoop = R :=
    sourceLeft_paramFrameLoop_eq_mul_standard m hm V W
  calc
    loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
        loopClassZ2 R hRclosed :=
      loopClassZ2_congr_fun P.paramFrameLoop_closed hRclosed heq
    _ = loopClassZ2 (sourceCoefficientLoop m)
          (sourceCoefficientLoop_closed m) +
        loopClassZ2 Q.paramFrameLoop Q.paramFrameLoop_closed := by
      exact loopClassZ2_mul _ _ _ _ _
    _ = 1 + 1 := by
      rw [loopClassZ2_sourceCoefficientLoop,
        StandardSaddle.sourceLeft_paramFrameClass_eq_one]
    _ = 0 := by decide


-- @@ L333-359 verbatim
theorem target_paramFrameClass_eq_one (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) :
    loopClassZ2 (targetSimpleClosedOrbitParam m hm V).paramFrameLoop
        (targetSimpleClosedOrbitParam m hm V).paramFrameLoop_closed = 1 := by
  let W : TamedField (StandardSaddle.targetFLS m) :=
    (StandardSaddle.targetFLS m).exists_tamedField.some
  let P := targetSimpleClosedOrbitParam m hm V
  let Q := StandardSaddle.targetSimpleClosedOrbitParam m W
  let R := targetCoefficientLoop m * Q.paramFrameLoop
  have hRclosed : R 0 = R 1 := by
    change targetCoefficientLoop m 0 * Q.paramFrameLoop 0 =
      targetCoefficientLoop m 1 * Q.paramFrameLoop 1
    rw [targetCoefficientLoop_closed, Q.paramFrameLoop_closed]
  have heq : P.paramFrameLoop = R :=
    target_paramFrameLoop_eq_mul_standard m hm V W
  calc
    loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
        loopClassZ2 R hRclosed :=
      loopClassZ2_congr_fun P.paramFrameLoop_closed hRclosed heq
    _ = loopClassZ2 (targetCoefficientLoop m)
          (targetCoefficientLoop_closed m) +
        loopClassZ2 Q.paramFrameLoop Q.paramFrameLoop_closed := by
      exact loopClassZ2_mul _ _ _ _ _
    _ = 0 + 1 := by
      rw [loopClassZ2_targetCoefficientLoop,
        StandardSaddle.target_paramFrameClass_eq_one]
    _ = 1 := by decide


-- @@ L361-375 verbatim
/-- The twisted local saddle has precisely the `0,0 -> 1` frame splice. -/
theorem cassini_zeroPair_frame_class_splice (hm : 0 < m)
    (Vsource : TamedField (sourceFLS m hm))
    (Vtarget : TamedField (targetFLS m hm)) :
    loopClassZ2 (targetSimpleClosedOrbitParam m hm Vtarget).paramFrameLoop
        (targetSimpleClosedOrbitParam m hm Vtarget).paramFrameLoop_closed =
      loopClassZ2
          (sourceRightSimpleClosedOrbitParam m hm Vsource).paramFrameLoop
          (sourceRightSimpleClosedOrbitParam m hm Vsource).paramFrameLoop_closed +
        loopClassZ2
          (sourceLeftSimpleClosedOrbitParam m hm Vsource).paramFrameLoop
          (sourceLeftSimpleClosedOrbitParam m hm Vsource).paramFrameLoop_closed + 1 := by
  rw [target_paramFrameClass_eq_one, sourceRight_paramFrameClass_eq_zero,
    sourceLeft_paramFrameClass_eq_zero]
  decide


-- @@ L377-429 verbatim
/-- Transport the local twisted Cassini identity to three complete actual
orbits.  This is the direct production/installed-saddle reuse boundary: only
the three exterior-relative closed homotopies remain geometric input. -/
theorem actual_orbitFrameClass_splice (hm : 0 < m)
    {Xbefore Xafter : FramedLevelSet (m + 2)}
    (Vbefore : TamedField Xbefore) (Vafter : TamedField Xafter)
    (O₁ O₂ : Vbefore.OrbitIndex) (Ohat : Vafter.OrbitIndex)
    (Vsource : TamedField (sourceFLS m hm))
    (Vtarget : TamedField (targetFLS m hm))
    (H₁ : ContinuousMap.Homotopy (Vbefore.orbitFrameLoop O₁)
      (sourceRightSimpleClosedOrbitParam m hm Vsource).paramFrameLoop)
    (H₂ : ContinuousMap.Homotopy (Vbefore.orbitFrameLoop O₂)
      (sourceLeftSimpleClosedOrbitParam m hm Vsource).paramFrameLoop)
    (Hhat : ContinuousMap.Homotopy (Vafter.orbitFrameLoop Ohat)
      (targetSimpleClosedOrbitParam m hm Vtarget).paramFrameLoop)
    (H₁_closed : ∀ s : I, H₁ (s, 0) = H₁ (s, 1))
    (H₂_closed : ∀ s : I, H₂ (s, 0) = H₂ (s, 1))
    (Hhat_closed : ∀ s : I, Hhat (s, 0) = Hhat (s, 1)) :
    Vafter.orbitFrameClass Ohat =
      Vbefore.orbitFrameClass O₁ + Vbefore.orbitFrameClass O₂ + 1 := by
  have h₁ : Vbefore.orbitFrameClass O₁ =
      loopClassZ2
        (sourceRightSimpleClosedOrbitParam m hm Vsource).paramFrameLoop
        (sourceRightSimpleClosedOrbitParam m hm Vsource).paramFrameLoop_closed :=
    loopClassZ2_congr (Vbefore.orbitFrameLoop_closed O₁)
      (sourceRightSimpleClosedOrbitParam m hm Vsource).paramFrameLoop_closed
      H₁ H₁_closed
  have h₂ : Vbefore.orbitFrameClass O₂ =
      loopClassZ2
        (sourceLeftSimpleClosedOrbitParam m hm Vsource).paramFrameLoop
        (sourceLeftSimpleClosedOrbitParam m hm Vsource).paramFrameLoop_closed :=
    loopClassZ2_congr (Vbefore.orbitFrameLoop_closed O₂)
      (sourceLeftSimpleClosedOrbitParam m hm Vsource).paramFrameLoop_closed
      H₂ H₂_closed
  have hhat : Vafter.orbitFrameClass Ohat =
      loopClassZ2 (targetSimpleClosedOrbitParam m hm Vtarget).paramFrameLoop
        (targetSimpleClosedOrbitParam m hm Vtarget).paramFrameLoop_closed :=
    loopClassZ2_congr (Vafter.orbitFrameLoop_closed Ohat)
      (targetSimpleClosedOrbitParam m hm Vtarget).paramFrameLoop_closed
      Hhat Hhat_closed
  calc
    Vafter.orbitFrameClass Ohat =
        loopClassZ2 (targetSimpleClosedOrbitParam m hm Vtarget).paramFrameLoop
          (targetSimpleClosedOrbitParam m hm Vtarget).paramFrameLoop_closed := hhat
    _ = loopClassZ2
          (sourceRightSimpleClosedOrbitParam m hm Vsource).paramFrameLoop
          (sourceRightSimpleClosedOrbitParam m hm Vsource).paramFrameLoop_closed +
        loopClassZ2
          (sourceLeftSimpleClosedOrbitParam m hm Vsource).paramFrameLoop
          (sourceLeftSimpleClosedOrbitParam m hm Vsource).paramFrameLoop_closed + 1 :=
      cassini_zeroPair_frame_class_splice m hm Vsource Vtarget
    _ = Vbefore.orbitFrameClass O₁ + Vbefore.orbitFrameClass O₂ + 1 := by
      rw [h₁, h₂]


-- @@ L431-431 verbatim
/-! ## Exhaustion of the endpoint orbit components -/


-- @@ L433-438 verbatim
theorem source_fiber_eq_range_union (hm : 0 < m) :
    (sourceFLS m hm).fiber =
      Set.range (StandardSaddle.sourcePointRight m) ∪
        Set.range (StandardSaddle.sourcePointLeft m) := by
  rw [source_fiber_eq_standard m hm]
  exact StandardSaddle.source_fiber_eq_range_union m


-- @@ L440-443 verbatim
theorem target_fiber_eq_range (hm : 0 < m) :
    (targetFLS m hm).fiber = Set.range (StandardSaddle.targetPoint m) := by
  rw [target_fiber_eq_standard m hm]
  exact StandardSaddle.target_fiber_eq_range m


-- @@ L445-450 verbatim
theorem source_planeFirst_ne_zero_of_mem_fiber (hm : 0 < m) {x : E}
    (hx : x ∈ (sourceFLS m hm).fiber) :
    x (StandardSaddle.planeFirst m) ≠ 0 := by
  apply StandardSaddle.source_planeFirst_ne_zero_of_mem_fiber m
  rw [← source_fiber_eq_standard m hm]
  exact hx


-- @@ L452-457 verbatim
/-- The coordinate sign separates the two incoming twisted-fiber components. -/
def sourceOvalSign (hm : 0 < m) : FiberSign (sourceFLS m hm) where
  toFun := fun x => x (StandardSaddle.planeFirst m)
  continuous :=
    (EuclideanSpace.proj (StandardSaddle.planeFirst m) : E →L[ℝ] ℝ).continuous
  nonzero := fun _ hx => source_planeFirst_ne_zero_of_mem_fiber m hm hx


-- @@ L459-464 verbatim
@[simp] theorem sourceOvalSign_apply_right (hm : 0 < m) (theta : ℝ) :
    sourceOvalSign m hm (StandardSaddle.sourcePointRight m theta) =
      StandardSaddle.sourceRootFirst theta := by
  change StandardSaddle.sourcePointRight m theta
      (StandardSaddle.planeFirst m) = StandardSaddle.sourceRootFirst theta
  exact StandardSaddle.sourcePointRight_apply_planeFirst m theta


-- @@ L466-471 verbatim
@[simp] theorem sourceOvalSign_apply_left (hm : 0 < m) (theta : ℝ) :
    sourceOvalSign m hm (StandardSaddle.sourcePointLeft m theta) =
      -StandardSaddle.sourceRootFirst theta := by
  change StandardSaddle.sourcePointLeft m theta
      (StandardSaddle.planeFirst m) = -StandardSaddle.sourceRootFirst theta
  exact StandardSaddle.sourcePointLeft_apply_planeFirst m theta


-- @@ L473-491 verbatim
theorem source_right_orbit_subset_range (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    V.orbit (StandardSaddle.sourcePointRight m 0) ⊆
      Set.range (StandardSaddle.sourcePointRight m) := by
  intro x hx
  have hp := sourcePointRight_mem_source_fiber m hm 0
  have hxfiber := V.orbit_subset_fiber hp hx
  have hbase :
      0 < sourceOvalSign m hm (StandardSaddle.sourcePointRight m 0) := by
    simpa using StandardSaddle.sourceRootFirst_pos 0
  have hxpos : 0 < sourceOvalSign m hm x :=
    ((sourceOvalSign m hm).pos_iff_of_mem_orbit V hp hx).mp hbase
  rw [source_fiber_eq_range_union m hm] at hxfiber
  rcases hxfiber with hright | hleft
  · exact hright
  · rcases hleft with ⟨theta, rfl⟩
    have hr := StandardSaddle.sourceRootFirst_pos theta
    simp only [sourceOvalSign_apply_left] at hxpos
    nlinarith


-- @@ L493-514 verbatim
theorem source_left_orbit_subset_range (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    V.orbit (StandardSaddle.sourcePointLeft m 0) ⊆
      Set.range (StandardSaddle.sourcePointLeft m) := by
  intro x hx
  have hp := sourcePointLeft_mem_source_fiber m hm 0
  have hsign := (sourceOvalSign m hm).pos_iff_of_mem_orbit V hp hx
  have hbaseNot :
      ¬0 < sourceOvalSign m hm (StandardSaddle.sourcePointLeft m 0) := by
    have hr := StandardSaddle.sourceRootFirst_pos 0
    simp only [sourceOvalSign_apply_left]
    nlinarith
  have hxfiber := V.orbit_subset_fiber hp hx
  rw [source_fiber_eq_range_union m hm] at hxfiber
  rcases hxfiber with hright | hleft
  · rcases hright with ⟨theta, rfl⟩
    have hrightPos :
        0 < sourceOvalSign m hm
          (StandardSaddle.sourcePointRight m theta) := by
      simpa using StandardSaddle.sourceRootFirst_pos theta
    exact False.elim (hbaseNot (hsign.mpr hrightPos))
  · exact hleft


-- @@ L516-523 verbatim
theorem source_right_orbit_eq_range (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    V.orbit (StandardSaddle.sourcePointRight m 0) =
      Set.range (StandardSaddle.sourcePointRight m) := by
  apply Set.Subset.antisymm
  · exact source_right_orbit_subset_range m hm V
  · rintro x ⟨theta, rfl⟩
    exact sourcePointRight_mem_orbit m hm V theta


-- @@ L525-532 verbatim
theorem source_left_orbit_eq_range (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    V.orbit (StandardSaddle.sourcePointLeft m 0) =
      Set.range (StandardSaddle.sourcePointLeft m) := by
  apply Set.Subset.antisymm
  · exact source_left_orbit_subset_range m hm V
  · rintro x ⟨theta, rfl⟩
    exact sourcePointLeft_mem_orbit m hm V theta


-- @@ L534-538 verbatim
def sourceRightOrbitIndex (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) : V.OrbitIndex :=
  ⟨V.orbit (StandardSaddle.sourcePointRight m 0), V.mem_orbitFinset.mpr
    ⟨StandardSaddle.sourcePointRight m 0,
      sourcePointRight_mem_source_fiber m hm 0, rfl⟩⟩


-- @@ L540-544 verbatim
def sourceLeftOrbitIndex (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) : V.OrbitIndex :=
  ⟨V.orbit (StandardSaddle.sourcePointLeft m 0), V.mem_orbitFinset.mpr
    ⟨StandardSaddle.sourcePointLeft m 0,
      sourcePointLeft_mem_source_fiber m hm 0, rfl⟩⟩


-- @@ L546-549 verbatim
@[simp] theorem sourceRightOrbitIndex_coe (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    ((sourceRightOrbitIndex m hm V : V.OrbitIndex) : Set E) =
      V.orbit (StandardSaddle.sourcePointRight m 0) := rfl


-- @@ L551-554 verbatim
@[simp] theorem sourceLeftOrbitIndex_coe (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    ((sourceLeftOrbitIndex m hm V : V.OrbitIndex) : Set E) =
      V.orbit (StandardSaddle.sourcePointLeft m 0) := rfl


-- @@ L556-572 verbatim
theorem sourceRightOrbitIndex_ne_sourceLeftOrbitIndex (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    sourceRightOrbitIndex m hm V ≠ sourceLeftOrbitIndex m hm V := by
  intro hindex
  have hsets := congrArg (fun O : V.OrbitIndex => (O : Set E)) hindex
  change V.orbit (StandardSaddle.sourcePointRight m 0) =
    V.orbit (StandardSaddle.sourcePointLeft m 0) at hsets
  rw [source_right_orbit_eq_range m hm V,
    source_left_orbit_eq_range m hm V] at hsets
  have hright : StandardSaddle.sourcePointRight m 0 ∈
      Set.range (StandardSaddle.sourcePointRight m) := ⟨0, rfl⟩
  have hleft : StandardSaddle.sourcePointRight m 0 ∈
      Set.range (StandardSaddle.sourcePointLeft m) := by
    rw [← hsets]
    exact hright
  exact Set.disjoint_left.mp (StandardSaddle.source_ranges_disjoint m)
    hright hleft


-- @@ L574-590 verbatim
theorem orbitIndex_eq_sourceRight_or_sourceLeft (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) (O : V.OrbitIndex) :
    O = sourceRightOrbitIndex m hm V ∨
      O = sourceLeftOrbitIndex m hm V := by
  have hp := V.orbitPoint_mem_fiber O
  rw [source_fiber_eq_range_union m hm] at hp
  rcases hp with ⟨theta, htheta⟩ | ⟨theta, htheta⟩
  · left
    apply Subtype.ext
    change (O : Set E) = V.orbit (StandardSaddle.sourcePointRight m 0)
    rw [V.orbitPoint_orbit O, ← htheta]
    exact V.orbit_eq_of_mem (sourcePointRight_mem_orbit m hm V theta)
  · right
    apply Subtype.ext
    change (O : Set E) = V.orbit (StandardSaddle.sourcePointLeft m 0)
    rw [V.orbitPoint_orbit O, ← htheta]
    exact V.orbit_eq_of_mem (sourcePointLeft_mem_orbit m hm V theta)


-- @@ L592-603 verbatim
theorem source_orbitIndex_card (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) : Fintype.card V.OrbitIndex = 2 := by
  classical
  rw [← Finset.card_univ]
  have huniv : (Finset.univ : Finset V.OrbitIndex) =
      {sourceRightOrbitIndex m hm V, sourceLeftOrbitIndex m hm V} := by
    ext O
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact orbitIndex_eq_sourceRight_or_sourceLeft m hm V O
  rw [huniv]
  simp [sourceRightOrbitIndex_ne_sourceLeftOrbitIndex m hm V]


-- @@ L605-612 verbatim
theorem target_orbit_eq_fiber (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) :
    V.orbit (StandardSaddle.targetPoint m 0) = (targetFLS m hm).fiber := by
  apply Set.Subset.antisymm
  · exact V.orbit_subset_fiber (targetPoint_mem_target_fiber m hm 0)
  · rw [target_fiber_eq_range m hm]
    rintro x ⟨theta, rfl⟩
    exact targetPoint_mem_orbit m hm V theta


-- @@ L614-618 verbatim
def targetOrbitIndex (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) : V.OrbitIndex :=
  ⟨V.orbit (StandardSaddle.targetPoint m 0), V.mem_orbitFinset.mpr
    ⟨StandardSaddle.targetPoint m 0,
      targetPoint_mem_target_fiber m hm 0, rfl⟩⟩


-- @@ L620-623 verbatim
@[simp] theorem targetOrbitIndex_coe (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) :
    ((targetOrbitIndex m hm V : V.OrbitIndex) : Set E) =
      V.orbit (StandardSaddle.targetPoint m 0) := rfl


-- @@ L625-632 verbatim
theorem orbitIndex_eq_targetOrbitIndex (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) (O : V.OrbitIndex) :
    O = targetOrbitIndex m hm V := by
  apply Subtype.ext
  change (O : Set E) = V.orbit (StandardSaddle.targetPoint m 0)
  rw [V.orbitPoint_orbit, V.orbit_eq_of_mem]
  rw [target_orbit_eq_fiber m hm V]
  exact V.orbitPoint_mem_fiber O


-- @@ L634-637 verbatim
theorem target_orbitIndex_card (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) : Fintype.card V.OrbitIndex = 1 := by
  exact Fintype.card_eq_one_iff.mpr
    ⟨targetOrbitIndex m hm V, fun O => orbitIndex_eq_targetOrbitIndex m hm V O⟩


-- @@ L639-639 verbatim
/-! ## Orbit frame classes -/


-- @@ L641-646 verbatim
theorem sourceRight_paramFrameClass_eq_fundamental (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    loopClassZ2 (sourceRightSimpleClosedOrbitParam m hm V).paramFrameLoop
        (sourceRightSimpleClosedOrbitParam m hm V).paramFrameLoop_closed =
      V.fundamentalFrameClass (sourcePointRight_mem_source_fiber m hm 0) :=
  (sourceRightSimpleClosedOrbitParam m hm V).paramFrameClass_eq_fundamental


-- @@ L648-653 verbatim
theorem sourceLeft_paramFrameClass_eq_fundamental (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    loopClassZ2 (sourceLeftSimpleClosedOrbitParam m hm V).paramFrameLoop
        (sourceLeftSimpleClosedOrbitParam m hm V).paramFrameLoop_closed =
      V.fundamentalFrameClass (sourcePointLeft_mem_source_fiber m hm 0) :=
  (sourceLeftSimpleClosedOrbitParam m hm V).paramFrameClass_eq_fundamental


-- @@ L655-660 verbatim
theorem target_paramFrameClass_eq_fundamental (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) :
    loopClassZ2 (targetSimpleClosedOrbitParam m hm V).paramFrameLoop
        (targetSimpleClosedOrbitParam m hm V).paramFrameLoop_closed =
      V.fundamentalFrameClass (targetPoint_mem_target_fiber m hm 0) :=
  (targetSimpleClosedOrbitParam m hm V).paramFrameClass_eq_fundamental


-- @@ L662-673 verbatim
theorem sourceRight_orbitFrameClass_eq_zero (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    V.orbitFrameClass (sourceRightOrbitIndex m hm V) = 0 := by
  rw [V.orbitFrameClass_eq_fundamental]
  have hpoint : V.orbitPoint (sourceRightOrbitIndex m hm V) ∈
      V.orbit (StandardSaddle.sourcePointRight m 0) := by
    rw [← sourceRightOrbitIndex_coe m hm V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase := V.fundamentalFrameClass_eq_of_mem_orbit
    (sourcePointRight_mem_source_fiber m hm 0) hpoint
  rw [hbase, ← sourceRight_paramFrameClass_eq_fundamental m hm V,
    sourceRight_paramFrameClass_eq_zero m hm V]


-- @@ L675-686 verbatim
theorem sourceLeft_orbitFrameClass_eq_zero (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    V.orbitFrameClass (sourceLeftOrbitIndex m hm V) = 0 := by
  rw [V.orbitFrameClass_eq_fundamental]
  have hpoint : V.orbitPoint (sourceLeftOrbitIndex m hm V) ∈
      V.orbit (StandardSaddle.sourcePointLeft m 0) := by
    rw [← sourceLeftOrbitIndex_coe m hm V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase := V.fundamentalFrameClass_eq_of_mem_orbit
    (sourcePointLeft_mem_source_fiber m hm 0) hpoint
  rw [hbase, ← sourceLeft_paramFrameClass_eq_fundamental m hm V,
    sourceLeft_paramFrameClass_eq_zero m hm V]


-- @@ L688-693 verbatim
theorem source_orbitFrameClass_eq_zero (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) (O : V.OrbitIndex) :
    V.orbitFrameClass O = 0 := by
  rcases orbitIndex_eq_sourceRight_or_sourceLeft m hm V O with h | h
  · rw [h, sourceRight_orbitFrameClass_eq_zero m hm V]
  · rw [h, sourceLeft_orbitFrameClass_eq_zero m hm V]


-- @@ L695-707 verbatim
theorem target_orbitFrameClass_eq_one (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) (O : V.OrbitIndex) :
    V.orbitFrameClass O = 1 := by
  rw [orbitIndex_eq_targetOrbitIndex m hm V O,
    V.orbitFrameClass_eq_fundamental]
  have hpoint : V.orbitPoint (targetOrbitIndex m hm V) ∈
      V.orbit (StandardSaddle.targetPoint m 0) := by
    rw [← targetOrbitIndex_coe m hm V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase := V.fundamentalFrameClass_eq_of_mem_orbit
    (targetPoint_mem_target_fiber m hm 0) hpoint
  rw [hbase, ← target_paramFrameClass_eq_fundamental m hm V,
    target_paramFrameClass_eq_one m hm V]


-- @@ L709-709 verbatim
/-! ## Literal all-positive ledgers -/


-- @@ L711-715 verbatim
theorem allPositive_selects_orbit {X : FramedLevelSet (m + 2)}
    (V : TamedField X) (O : V.OrbitIndex) :
    (O : Set E) ∈ (FiberSign.allPositive X).positiveOrbitCollection V := by
  rw [(FiberSign.allPositive X).mem_positiveOrbitCollection_iff V O]
  simp


-- @@ L717-724 verbatim
def allPositiveSelectedOrbitEquiv {X : FramedLevelSet (m + 2)}
    (V : TamedField X) :
    V.SelectedOrbitIndex
        ((FiberSign.allPositive X).positiveOrbitCollection V) ≃ V.OrbitIndex where
  toFun O := O.1
  invFun O := ⟨O, allPositive_selects_orbit m V O⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L726-745 verbatim
theorem source_positiveFrameLedger_eq_pair_zero (hm : 0 < m)
    (V : TamedField (sourceFLS m hm)) :
    (FiberSign.allPositive (sourceFLS m hm)).positiveFrameLedger V =
      [(0 : ZMod 2), 0] := by
  classical
  let L := (FiberSign.allPositive (sourceFLS m hm)).positiveFrameLedger V
  have hlen : L.length = 2 := by
    simp only [L, FiberSign.positiveFrameLedger,
      TamedField.selectedFrameLedger, List.length_ofFn]
    rw [Fintype.card_congr (allPositiveSelectedOrbitEquiv m V),
      source_orbitIndex_card m hm V]
  have hall : ∀ z ∈ L, z = (0 : ZMod 2) := by
    intro z hz
    simp only [L, FiberSign.positiveFrameLedger,
      TamedField.selectedFrameLedger, List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact source_orbitFrameClass_eq_zero m hm V _
  calc
    L = List.replicate L.length 0 := List.eq_replicate_length.mpr hall
    _ = [(0 : ZMod 2), 0] := by rw [hlen]; rfl


-- @@ L747-766 verbatim
theorem target_positiveFrameLedger_eq_single_one (hm : 0 < m)
    (V : TamedField (targetFLS m hm)) :
    (FiberSign.allPositive (targetFLS m hm)).positiveFrameLedger V =
      [(1 : ZMod 2)] := by
  classical
  let L := (FiberSign.allPositive (targetFLS m hm)).positiveFrameLedger V
  have hlen : L.length = 1 := by
    simp only [L, FiberSign.positiveFrameLedger,
      TamedField.selectedFrameLedger, List.length_ofFn]
    rw [Fintype.card_congr (allPositiveSelectedOrbitEquiv m V),
      target_orbitIndex_card m hm V]
  have hall : ∀ z ∈ L, z = (1 : ZMod 2) := by
    intro z hz
    simp only [L, FiberSign.positiveFrameLedger,
      TamedField.selectedFrameLedger, List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact target_orbitFrameClass_eq_one m hm V _
  calc
    L = List.replicate L.length 1 := List.eq_replicate_length.mpr hall
    _ = [(1 : ZMod 2)] := by rw [hlen]; rfl


-- @@ L768-768 verbatim
/-! ## Packaged endpoint data and the existing PT stability interface -/


-- @@ L770-771 verbatim
def sourceField (hm : 0 < m) : TamedField (sourceFLS m hm) :=
  (sourceFLS m hm).exists_tamedField.some


-- @@ L773-774 verbatim
def targetField (hm : 0 < m) : TamedField (targetFLS m hm) :=
  (targetFLS m hm).exists_tamedField.some


-- @@ L776-779 verbatim
@[simp] theorem sourceField_ledger (hm : 0 < m) :
    (FiberSign.allPositive (sourceFLS m hm)).positiveFrameLedger
        (sourceField m hm) = [(0 : ZMod 2), 0] :=
  source_positiveFrameLedger_eq_pair_zero m hm (sourceField m hm)


-- @@ L781-784 verbatim
@[simp] theorem targetField_ledger (hm : 0 < m) :
    (FiberSign.allPositive (targetFLS m hm)).positiveFrameLedger
        (targetField m hm) = [(1 : ZMod 2)] :=
  target_positiveFrameLedger_eq_single_one m hm (targetField m hm)


-- @@ L786-791 verbatim
def explicitStableEndpoints (hm : 0 < m) :
    PTStableZeroPairEndpoints m (sourceFLS m hm) (targetFLS m hm) where
  sourceField := sourceField m hm
  targetField := targetField m hm
  sourceLedger := sourceField_ledger m hm
  targetLedger := targetField_ledger m hm


-- @@ L793-793 verbatim
variable {Y₀ Y₁ : FramedLevelSet (m + 2)}

-- @@ L794-794 verbatim
variable {T₀ : FiberSign Y₀} {T₁ : FiberSign Y₁}

-- @@ L795-795 verbatim
variable {D : PTTransverseHomotopyData T₀ T₁}


-- @@ L797-803 verbatim
/-- Discharge the explicit-ledger arguments of the PT endpoint-stability
adapter.  Only the genuinely geometric connector/positivity contract remains. -/
def stableEndpointsOfPT (hm : 0 < m)
    (K : CassiniPTEndpointStability m hm T₀ T₁ D) :
    PTStableZeroPairEndpoints m Y₀ Y₁ :=
  K.toStableZeroPairEndpoints (sourceField m hm) (targetField m hm)
    (sourceField_ledger m hm) (targetField_ledger m hm)


-- @@ L805-805 verbatim
/-! ## Background harmonization and the residual model constructor -/


-- @@ L807-826 verbatim
theorem allPositive_backgroundTransport_ledger_perm
    {X : FramedLevelSet (m + 2)} (V : TamedField X)
    (c₁ c₂ : EuclideanSpace ℝ (Fin (m + 2)))
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    ((FiberSign.allPositive X).positiveFrameLedger V).Perm
      ((FiberSign.allPositive
          (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
        (V.backgroundTransport c₁ c₂ h₁ h₂)) := by
  let W := V.backgroundTransport c₁ c₂ h₁ h₂
  let T := V.backgroundDeltaTransport c₁ c₂ h₁ h₂
  let Tselected : V.SelectedDeltaTransport W
      ((FiberSign.allPositive X).positiveOrbitCollection V)
      ((FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveOrbitCollection W) :=
    TamedField.SelectedDeltaTransport.ofDeltaTransport T (by
      intro O
      constructor <;> intro _
      · exact allPositive_selects_orbit m W (T.orbitEquiv O)
      · exact allPositive_selects_orbit m V O)
  exact TamedField.SelectedDeltaTransport.selectedFrameLedger_perm V W Tselected


-- @@ L828-856 verbatim
theorem backgroundTransport_ledger_eq_pair_zero
    {X : FramedLevelSet (m + 2)} (V : TamedField X)
    (c₁ c₂ : EuclideanSpace ℝ (Fin (m + 2)))
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hledger : (FiberSign.allPositive X).positiveFrameLedger V =
      [(0 : ZMod 2), 0]) :
    (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
      (V.backgroundTransport c₁ c₂ h₁ h₂) = [(0 : ZMod 2), 0] := by
  have hp := allPositive_backgroundTransport_ledger_perm m V c₁ c₂ h₁ h₂
  rw [hledger] at hp
  have hcount := hp.length_eq
  have hall : ∀ z ∈
      (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
          (V.backgroundTransport c₁ c₂ h₁ h₂), z = (0 : ZMod 2) := by
    intro z hz
    have hzsrc : z ∈ [(0 : ZMod 2), 0] := hp.mem_iff.mpr hz
    simpa using hzsrc
  calc
    (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
          (V.backgroundTransport c₁ c₂ h₁ h₂) =
        List.replicate
          ((FiberSign.allPositive
            (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
              (V.backgroundTransport c₁ c₂ h₁ h₂)).length 0 :=
      List.eq_replicate_length.mpr hall
    _ = [(0 : ZMod 2), 0] := by rw [← hcount]; rfl


-- @@ L858-886 verbatim
theorem backgroundTransport_ledger_eq_single_one
    {X : FramedLevelSet (m + 2)} (V : TamedField X)
    (c₁ c₂ : EuclideanSpace ℝ (Fin (m + 2)))
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hledger : (FiberSign.allPositive X).positiveFrameLedger V =
      [(1 : ZMod 2)]) :
    (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
      (V.backgroundTransport c₁ c₂ h₁ h₂) = [(1 : ZMod 2)] := by
  have hp := allPositive_backgroundTransport_ledger_perm m V c₁ c₂ h₁ h₂
  rw [hledger] at hp
  have hcount := hp.length_eq
  have hall : ∀ z ∈
      (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
          (V.backgroundTransport c₁ c₂ h₁ h₂), z = (1 : ZMod 2) := by
    intro z hz
    have hzsrc : z ∈ [(1 : ZMod 2)] := hp.mem_iff.mpr hz
    simpa using hzsrc
  calc
    (FiberSign.allPositive
        (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
          (V.backgroundTransport c₁ c₂ h₁ h₂) =
        List.replicate
          ((FiberSign.allPositive
            (X.codomainEquiv (backgroundEquiv c₁ c₂ h₁ h₂))).positiveFrameLedger
              (V.backgroundTransport c₁ c₂ h₁ h₂)).length 1 :=
      List.eq_replicate_length.mpr hall
    _ = [(1 : ZMod 2)] := by rw [← hcount]; rfl


-- @@ L888-927 verbatim
/-- Once a transverse PT realization satisfies the endpoint-stability
contract, the Cassini ledger calculation and background harmonization fill the
entire residual unsigned zero-pair model. -/
def unsignedZeroPairSaddleCoreOfPT (hm : 0 < m)
    (K : CassiniPTEndpointStability m hm T₀ T₁ D) :
    ConcreteConfigurationMorseReduction.UnsignedZeroPairSaddleCore m := by
  let P := stableEndpointsOfPT m hm K
  let c₁ : EuclideanSpace ℝ (Fin (m + 2)) := -D.target
  let c₂ : EuclideanSpace ℝ (Fin (m + 2)) :=
    ConcreteConfigurationMorseReduction.compactBackground m
  have hc₁ : c₁ ≠ 0 := D.neg_target_ne_zero
  have hc₂ : c₂ ≠ 0 := CompactBirth.background_ne_zero (m + 1)
  let e := backgroundEquiv c₁ c₂ hc₁ hc₂
  let R : ℝ := Classical.choose D.exists_nonneg_spatialFlatOutside
  have hR : 0 ≤ R :=
    (Classical.choose_spec D.exists_nonneg_spatialFlatOutside).1
  have hflat : D.toFramedLevelCobordism.SpatialFlatOutside
      (-D.target) 0 R :=
    (Classical.choose_spec D.exists_nonneg_spatialFlatOutside).2
  refine {
    cobordism := D.toFramedLevelCobordism.codomainEquiv e
    sourceField := P.sourceField.backgroundTransport c₁ c₂ hc₁ hc₂
    targetField := P.targetField.backgroundTransport c₁ c₂ hc₁ hc₂
    sourceLedger := ?_
    targetLedger := ?_
    center := 0
    radius := R
    radius_nonneg := hR
    flatOutside := ?_ }
  · exact backgroundTransport_ledger_eq_pair_zero m P.sourceField
      c₁ c₂ hc₁ hc₂ P.sourceLedger
  · exact backgroundTransport_ledger_eq_single_one m P.targetField
      c₁ c₂ hc₁ hc₂ P.targetLedger
  · have hflat' :=
      FramedLevelCobordism.SpatialFlatOutside.codomainEquiv hflat e
    have hec : e (-D.target) = c₂ := by
      change e c₁ = c₂
      exact backgroundEquiv_apply c₁ c₂ hc₁ hc₂
    rw [hec] at hflat'
    exact hflat'


-- @@ L929-934 verbatim
/-- Direct consumer-level packaging, conditional only on the geometric PT
endpoint-stability witness. -/
def zeroPairSaddleModelOfPT (hm : 0 < m)
    (K : CassiniPTEndpointStability m hm T₀ T₁ D) :
    ConcreteConfigurationMorseReduction.ZeroPairSaddleModel m :=
  (unsignedZeroPairSaddleCoreOfPT m hm K).toZeroPairSaddleModel


-- @@ L936-936 verbatim
end ConcreteZeroPairCassiniFrameLedger

-- @@ L937-937 verbatim
end Submission
