import Submission.ProductionMorseDefiniteLocalExcision
import Submission.ProductionMorseDefiniteLedgerConnection
import Submission.FramedMorseEventExcision


-- @@ L5-18 verbatim
/-!
# Exterior transport for production definite Morse events

Local excision identifies every nonlocal component with an exterior component,
but it does not by itself assert that the compact critical-slice time flow
captures every such component.  This file isolates that remaining assertion as
`CriticalExteriorFlowCapture`: corresponding once-around parameters are the two
boundary loops of one short cylinder based in `criticalSliceExteriorCore`.

The cylinder API then proves frame-class preservation automatically.  The last
section composes the resulting chronological transport with the regular window
transports and supplies the literal event-bracket `SelectedDeltaTransport` used
by the production ledger callbacks.
-/


-- @@ L20-20 verbatim
set_option autoImplicit false

-- @@ L21-21 verbatim
set_option maxHeartbeats 1200000


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function Metric

-- @@ L26-26 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-30 verbatim
variable {n : ℕ}


-- @@ L32-32 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L33-33 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L35-35 verbatim
/-! ## Ambient loops attached to arbitrary once-around parameters -/


-- @@ L37-37 verbatim
namespace SimpleClosedOrbitParam


-- @@ L39-39 verbatim
variable {C : LevelCobordismData n} {t : ℝ}

-- @@ L40-40 verbatim
variable {hreg : sliceRegular C.G t}

-- @@ L41-41 verbatim
variable {V : TamedField (SlabTamedField.sliceFLSAt C t hreg)}


-- @@ L43-53 verbatim
/-- Put a spatial once-around orbit parameter back into its space-time slice. -/
def exteriorAmbientLoop
    (P : SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt C t hreg) V) : C(I, E') where
  toFun u := cobSpaceTime (P.curve u) t
  continuous_toFun := by
    have hcob : Continuous (fun x : E₁ => cobSpaceTime x t) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (hasFDerivAt_cobSpaceTime t x).continuousAt
    exact hcob.comp P.curve.continuous


-- @@ L55-62 verbatim
theorem exteriorAmbientLoop_fiber
    (P : SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt C t hreg) V) (u : I) :
    C.G (P.exteriorAmbientLoop u) = 0 := by
  have hu : P.curve u ∈
      (SlabTamedField.sliceFLSAt C t hreg).fiber :=
    V.orbit_subset_fiber P.hp (P.curve_mem_orbit u)
  rwa [SlabTamedField.sliceFLSAt_fiber] at hu


-- @@ L64-70 verbatim
theorem exteriorAmbientLoop_regular
    (P : SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt C t hreg) V) (u : I) :
    Surjective (spatialDeriv C.G (P.exteriorAmbientLoop u)) := by
  apply hreg (P.exteriorAmbientLoop u)
  · exact P.exteriorAmbientLoop_fiber u
  · simp [exteriorAmbientLoop]


-- @@ L72-77 verbatim
theorem exteriorAmbientLoop_closed
    (P : SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt C t hreg) V) :
    P.exteriorAmbientLoop 0 = P.exteriorAmbientLoop 1 := by
  change cobSpaceTime (P.curve 0) t = cobSpaceTime (P.curve 1) t
  rw [P.curve_closed]


-- @@ L79-94 verbatim
/-- The canonical frame along the ambientized parameter is its ordinary
`paramFrameLoop`. -/
theorem regularZeroFrame_exteriorAmbientLoop
    (P : SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt C t hreg) V) :
    regularZeroFrame C.smooth P.exteriorAmbientLoop
        P.exteriorAmbientLoop_regular = P.paramFrameLoop := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change regularZeroFrameMatrix C.G P.exteriorAmbientLoop u =
    frameLoop (SlabTamedField.sliceFLSAt C t hreg) P.realCurve (u : ℝ)
  unfold regularZeroFrameMatrix exteriorAmbientLoop frameLoop
    SlabTamedField.sliceFrameAt
  rw [P.realCurve_coe]
  simp [SlabTamedField.sliceFLSAt, sliceFLS, frameAt]


-- @@ L96-96 verbatim
end SimpleClosedOrbitParam


-- @@ L98-98 verbatim
/-! ## The exact missing exterior-capture condition -/


-- @@ L100-141 verbatim
/--
The remaining geometric input at an isolated event.  For every selected
negative-time component, `coreLoop` is a once-around lift to the compact
critical exterior.  Its two safe flow boundaries are once-around parameters
of the corresponding selected components.

No frame-class equation is stored here: it is a theorem of the regular
exterior cylinder below.
-/
structure CriticalExteriorFlowCapture
    (C : LevelCobordismData n) (criticalCenter : E') (t r ε : ℝ)
    (R : CompactTimeTamedField C
      (criticalSliceExteriorCore C criticalCenter t r))
    (hneg : sliceRegular C.G (t - ε))
    (hpos : sliceRegular C.G (t + ε))
    (Vneg : TamedField (SlabTamedField.sliceFLSAt C (t - ε) hneg))
    (Vpos : TamedField (SlabTamedField.sliceFLSAt C (t + ε) hpos))
    (A B : Set (Set E₁)) where
  safe : |ε| ≤ R.safeTime
  orbitEquiv :
    {O // O ∈ Vneg.selectedOrbitFinset A} ≃
      {O // O ∈ Vpos.selectedOrbitFinset B}
  coreLoop : {O // O ∈ Vneg.selectedOrbitFinset A} → C(I, E')
  core_mem : ∀ (O : {O // O ∈ Vneg.selectedOrbitFinset A}) q,
    coreLoop O q ∈
    criticalSliceExteriorCore C criticalCenter t r
  negativeParam : ∀ O : {O // O ∈ Vneg.selectedOrbitFinset A},
    SimpleClosedOrbitParam
    (SlabTamedField.sliceFLSAt C (t - ε) hneg) Vneg
  positiveParam : ∀ O : {O // O ∈ Vneg.selectedOrbitFinset A},
    SimpleClosedOrbitParam
    (SlabTamedField.sliceFLSAt C (t + ε) hpos) Vpos
  negative_orbit : ∀ O : {O // O ∈ Vneg.selectedOrbitFinset A},
    (negativeParam O).orbitIndex = O.1
  positive_orbit : ∀ O : {O // O ∈ Vneg.selectedOrbitFinset A},
    (positiveParam O).orbitIndex = (orbitEquiv O).1
  negative_boundary : ∀ (O : {O // O ∈ Vneg.selectedOrbitFinset A}) q,
    R.base.flow (coreLoop O q) (-ε) =
      (negativeParam O).exteriorAmbientLoop q
  positive_boundary : ∀ (O : {O // O ∈ Vneg.selectedOrbitFinset A}) q,
    R.base.flow (coreLoop O q) ε =
      (positiveParam O).exteriorAmbientLoop q


-- @@ L143-143 verbatim
namespace CriticalExteriorFlowCapture


-- @@ L145-145 verbatim
variable {C : LevelCobordismData n}

-- @@ L146-146 verbatim
variable {criticalCenter : EuclideanSpace ℝ (Fin (n + 2))} {t r ε : ℝ}

-- @@ L147-148 verbatim
variable {R : CompactTimeTamedField C
  (criticalSliceExteriorCore C criticalCenter t r)}

-- @@ L149-149 verbatim
variable {hneg : sliceRegular C.G (t - ε)}

-- @@ L150-150 verbatim
variable {hpos : sliceRegular C.G (t + ε)}

-- @@ L151-152 verbatim
variable {Vneg : TamedField
  (SlabTamedField.sliceFLSAt C (t - ε) hneg)}

-- @@ L153-154 verbatim
variable {Vpos : TamedField
  (SlabTamedField.sliceFLSAt C (t + ε) hpos)}

-- @@ L155-155 verbatim
variable {A B : Set (Set (EuclideanSpace ℝ (Fin (n + 1))))}


-- @@ L157-157 verbatim
include criticalCenter A B


-- @@ L159-164 verbatim
theorem core_fiber
    (H : CriticalExteriorFlowCapture C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O) (q : I) : C.G (H.coreLoop O q) = 0 := by
  exact (mem_criticalSliceExteriorCore C criticalCenter (H.coreLoop O q) t r).mp
    (H.core_mem O q) |>.1


-- @@ L166-174 verbatim
theorem core_closed
    (H : CriticalExteriorFlowCapture C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O) : H.coreLoop O 0 = H.coreLoop O 1 := by
  apply R.flow_apply_injective (-ε)
  change R.base.flow (H.coreLoop O 0) (-ε) =
    R.base.flow (H.coreLoop O 1) (-ε)
  rw [H.negative_boundary O 0, H.negative_boundary O 1]
  exact (H.negativeParam O).exteriorAmbientLoop_closed


-- @@ L176-183 verbatim
theorem negativeFlowSlice_eq
    (H : CriticalExteriorFlowCapture C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O) : R.flowSlice (H.coreLoop O) (-ε) =
      (H.negativeParam O).exteriorAmbientLoop := by
  apply ContinuousMap.ext
  intro q
  exact H.negative_boundary O q


-- @@ L185-192 verbatim
theorem positiveFlowSlice_eq
    (H : CriticalExteriorFlowCapture C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O) : R.flowSlice (H.coreLoop O) ε =
      (H.positiveParam O).exteriorAmbientLoop := by
  apply ContinuousMap.ext
  intro q
  exact H.positive_boundary O q


-- @@ L194-271 verbatim
/-- The short critical-exterior cylinder preserves the intrinsic frame class
of every captured pair of orbit components. -/
theorem orbitFrameClass_eq
    (H : CriticalExteriorFlowCapture C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) :
    Vneg.orbitFrameClass O.1 =
      Vpos.orbitFrameClass (H.orbitEquiv O).1 := by
  let Pneg := H.negativeParam O
  let Ppos := H.positiveParam O
  have hcyl := R.loopClassZ2_flowSlice_congr
    (H.coreLoop O) (H.core_mem O) (H.core_fiber O)
    (H.core_closed O) H.safe
  dsimp only at hcyl
  have hnegFrame :
      regularZeroFrame C.smooth (R.flowSlice (H.coreLoop O) (-ε))
          (fun q => by
            rw [H.negativeFlowSlice_eq O]
            exact Pneg.exteriorAmbientLoop_regular q) =
        Pneg.paramFrameLoop := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    change regularZeroFrameMatrix C.G
        (R.flowSlice (H.coreLoop O) (-ε)) q = _
    have hpoint : R.flowSlice (H.coreLoop O) (-ε) q =
        Pneg.exteriorAmbientLoop q := by
      change R.base.flow (H.coreLoop O q) (-ε) =
        Pneg.exteriorAmbientLoop q
      exact H.negative_boundary O q
    unfold regularZeroFrameMatrix
    rw [hpoint]
    exact congrArg Subtype.val <|
      congrArg (fun z => z q) Pneg.regularZeroFrame_exteriorAmbientLoop
  have hposFrame :
      regularZeroFrame C.smooth (R.flowSlice (H.coreLoop O) ε)
          (fun q => by
            rw [H.positiveFlowSlice_eq O]
            exact Ppos.exteriorAmbientLoop_regular q) =
        Ppos.paramFrameLoop := by
    apply ContinuousMap.ext
    intro q
    apply Subtype.ext
    change regularZeroFrameMatrix C.G
        (R.flowSlice (H.coreLoop O) ε) q = _
    have hpoint : R.flowSlice (H.coreLoop O) ε q =
        Ppos.exteriorAmbientLoop q := by
      change R.base.flow (H.coreLoop O q) ε =
        Ppos.exteriorAmbientLoop q
      exact H.positive_boundary O q
    unfold regularZeroFrameMatrix
    rw [hpoint]
    exact congrArg Subtype.val <|
      congrArg (fun z => z q) Ppos.regularZeroFrame_exteriorAmbientLoop
  rw [← H.negative_orbit O, ← H.positive_orbit O,
    Pneg.orbitFrameClass_eq_paramFrameClass,
    Ppos.orbitFrameClass_eq_paramFrameClass]
  have hnegClosed : R.flowSlice (H.coreLoop O) (-ε) 0 =
      R.flowSlice (H.coreLoop O) (-ε) 1 := by
    change R.base.flow (H.coreLoop O 0) (-ε) =
      R.base.flow (H.coreLoop O 1) (-ε)
    rw [H.negative_boundary O 0, H.negative_boundary O 1]
    exact Pneg.exteriorAmbientLoop_closed
  have hposClosed : R.flowSlice (H.coreLoop O) ε 0 =
      R.flowSlice (H.coreLoop O) ε 1 := by
    change R.base.flow (H.coreLoop O 0) ε =
      R.base.flow (H.coreLoop O 1) ε
    rw [H.positive_boundary O 0, H.positive_boundary O 1]
    exact Ppos.exteriorAmbientLoop_closed
  exact (loopClassZ2_congr_fun Pneg.paramFrameLoop_closed
      (regularZeroFrame_closed C.smooth
        (R.flowSlice (H.coreLoop O) (-ε)) _ hnegClosed)
      hnegFrame.symm).trans <|
    hcyl.trans <|
      loopClassZ2_congr_fun
        (regularZeroFrame_closed C.smooth
          (R.flowSlice (H.coreLoop O) ε) _ hposClosed)
        Ppos.paramFrameLoop_closed hposFrame


-- @@ L273-282 verbatim
/-- A captured exterior cylinder is exactly a selected delta transport. -/
def toSelectedDeltaTransport
    (H : CriticalExteriorFlowCapture C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B) :
    Vneg.SelectedDeltaTransport Vpos A B where
  orbitEquiv := H.orbitEquiv
  contribution_eq := by
    intro O
    unfold TamedField.orbitContribution
    rw [H.orbitFrameClass_eq O]


-- @@ L284-284 verbatim
end CriticalExteriorFlowCapture


-- @@ L286-286 verbatim
/-! ## Removing a transported distinguished component -/


-- @@ L288-288 verbatim
namespace TamedField.SelectedDeltaTransport


-- @@ L290-290 verbatim
variable {X Y : FramedLevelSet n}

-- @@ L291-291 verbatim
variable {V : TamedField X} {W : TamedField Y}


-- @@ L293-302 verbatim
private def equivSubtypeNe {α β : Type*} (e : α ≃ β) (a : α) :
    {x : α // x ≠ a} ≃ {y : β // y ≠ e a} where
  toFun x := ⟨e x.1, fun h => x.2 (e.injective h)⟩
  invFun y := ⟨e.symm y.1, fun h => y.2 (by simpa using congrArg e h)⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.1


-- @@ L304-342 verbatim
/-- Restrict a selected transport after deleting one selected source orbit and
its transported target orbit. -/
def sdiffSingleton {P Q : Set (Set E₁)}
    (T : V.SelectedDeltaTransport W P Q)
    (distinguished : V.SelectedOrbitIndex P) :
    V.SelectedDeltaTransport W
      (P \ {((distinguished.1 : V.OrbitIndex) : Set E₁)})
      (Q \ {((((selectedOrbitIndexEquiv V W T) distinguished).1 :
        W.OrbitIndex) : Set E₁)}) := by
  let e := selectedOrbitIndexEquiv V W T
  let sourceDelete := V.selectedOrbitIndexSdiffSingletonEquiv P distinguished
  let targetDelete := W.selectedOrbitIndexSdiffSingletonEquiv Q (e distinguished)
  let eDelete : V.SelectedOrbitIndex
        (P \ {((distinguished.1 : V.OrbitIndex) : Set E₁)}) ≃
      W.SelectedOrbitIndex
        (Q \ {(((e distinguished).1 : W.OrbitIndex) : Set E₁)}) :=
    sourceDelete.trans
      ((equivSubtypeNe e distinguished).trans targetDelete.symm)
  let eFin := (V.selectedOrbitIndexEquivFinset
      (P \ {((distinguished.1 : V.OrbitIndex) : Set E₁)})).symm.trans
    (eDelete.trans (W.selectedOrbitIndexEquivFinset
      (Q \ {(((e distinguished).1 : W.OrbitIndex) : Set E₁)})))
  refine {
    orbitEquiv := eFin
    contribution_eq := ?_ }
  intro O
  let O' : V.SelectedOrbitIndex
      (P \ {((distinguished.1 : V.OrbitIndex) : Set E₁)}) :=
    (V.selectedOrbitIndexEquivFinset _).symm O
  let Owhole : V.SelectedOrbitIndex P := ⟨O'.1, O'.2.1⟩
  have hclass := orbitFrameClass_eq V W T Owhole
  unfold TamedField.orbitContribution
  change V.orbitFrameClass O'.1 + 1 =
    W.orbitFrameClass (eDelete O').1 + 1
  apply congrArg (fun z => z + 1)
  have hsource : O'.1 = Owhole.1 := rfl
  have htarget : (eDelete O').1 = (e Owhole).1 := rfl
  rw [hsource, htarget]
  exact hclass


-- @@ L344-344 verbatim
end TamedField.SelectedDeltaTransport


-- @@ L346-346 verbatim
/-! ## Production critical exterior and local exclusion -/


-- @@ L348-348 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L349-349 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L350-350 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L352-352 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L354-362 verbatim
/-- Orbit collections whose every point lies outside the open local-cover
ball at time `s`. -/
def chronologicalExteriorOrbitCollection
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) (s : ℝ) :
    Set (Set E₁) :=
  {O | ∀ x ∈ O,
    (D.position.eventModel t ht).fiberCoverRadius ≤
      dist (cobSpaceTime x s) (D.position.eventCenter t ht)}


-- @@ L364-390 verbatim
/-- At a minimum, every incoming component is outside the complete-cover ball. -/
theorem chronologicalMinimumBeforeOrbit_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (O : (D.chronologicalBeforeField t ht).OrbitIndex) :
    (O : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalBeforeTime t ht) := by
  intro x hxO
  by_contra houtside
  have hxFiber : x ∈ (D.chronologicalBeforeSlice t ht).fiber := by
    apply (D.chronologicalBeforeField t ht).orbit_subset_fiber
      ((D.chronologicalBeforeField t ht).orbitPoint_mem_fiber O)
    rwa [← (D.chronologicalBeforeField t ht).orbitPoint_orbit O]
  have hxzero : D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalBeforeTime t ht)) = 0 := by
    rw [chronologicalBeforeSlice,
      SlabTamedField.sliceFLSAt_fiber] at hxFiber
    change D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalBeforeTime t ht)) = 0 at hxFiber
    exact hxFiber
  have hxCovered : x ∈ (D.position.eventModel t ht).coveredSliceFiber
      (D.chronologicalBeforeTime t ht) :=
    ⟨lt_of_not_ge houtside, hxzero⟩
  rw [D.chronologicalMinimumBeforeCoveredSliceFiber_eq_empty
    t ht hindex] at hxCovered
  exact hxCovered


-- @@ L392-451 verbatim
/-- At a minimum, every outgoing component other than the born circle is
outside the complete-cover ball. -/
theorem chronologicalMinimumAfterOrbit_mem_exterior_of_ne_local
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (O : (D.chronologicalMinimumLocalField t ht).OrbitIndex)
    (hne : (O : Set E₁) ≠
      (((D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set E₁)) :
    (O : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalAfterTime t ht) := by
  intro x hxO
  by_contra houtside
  have hxFiber : x ∈ (D.chronologicalAfterSlice t ht).fiber := by
    apply (D.chronologicalMinimumLocalField t ht).orbit_subset_fiber
      ((D.chronologicalMinimumLocalField t ht).orbitPoint_mem_fiber O)
    rwa [← (D.chronologicalMinimumLocalField t ht).orbitPoint_orbit O]
  have hxzero : D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalAfterTime t ht)) = 0 := by
    rw [chronologicalAfterSlice,
      SlabTamedField.sliceFLSAt_fiber] at hxFiber
    change D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalAfterTime t ht)) = 0 at hxFiber
    exact hxFiber
  have hxCovered : x ∈ (D.position.eventModel t ht).coveredSliceFiber
      (D.chronologicalAfterTime t ht) :=
    ⟨lt_of_not_ge houtside, hxzero⟩
  have hxLocal := D.chronologicalMinimumAfterCoveredSliceFiber_subset_orbit
    t ht hindex (D.chronologicalMinimumLocalField t ht) hxCovered
  have hxO' : x ∈ (D.chronologicalMinimumLocalField t ht).orbit
      ((D.chronologicalMinimumLocalField t ht).orbitPoint O) := by
    rwa [← (D.chronologicalMinimumLocalField t ht).orbitPoint_orbit O]
  apply hne
  calc
    (O : Set E₁) = (D.chronologicalMinimumLocalField t ht).orbit
        ((D.chronologicalMinimumLocalField t ht).orbitPoint O) :=
      (D.chronologicalMinimumLocalField t ht).orbitPoint_orbit O
    _ = (D.chronologicalMinimumLocalField t ht).orbit x :=
      ((D.chronologicalMinimumLocalField t ht).orbit_eq_of_mem hxO').symm
    _ = (D.chronologicalMinimumLocalField t ht).orbit
        (spacePart ((D.position.eventModel t ht).definiteCircle
          (D.chronologicalWindowRadius t ht) 0)) :=
      (D.chronologicalMinimumLocalField t ht).orbit_eq_of_mem hxLocal
    _ = (((D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 :
          (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set E₁) := by
      change (D.chronologicalMinimumLocalField t ht).orbit
          (spacePart ((D.position.eventModel t ht).definiteCircle
            (D.chronologicalWindowRadius t ht) 0)) =
        (D.chronologicalMinimumLocalField t ht).orbit
          (D.chronologicalMinimumLocalParam t ht hindex).p
      apply congrArg ((D.chronologicalMinimumLocalField t ht).orbit)
      change spacePart ((D.position.eventModel t ht).definiteCircle
          (D.chronologicalWindowRadius t ht) 0) =
        spacePart ((D.position.eventModel t ht).definiteCircle
          (D.chronologicalWindowRadius t ht)
          (2 * Real.pi * (((0 : I) : ℝ))))
      norm_num


-- @@ L453-512 verbatim
/-- At a maximum, every incoming component other than the dying circle is
outside the complete-cover ball. -/
theorem chronologicalMaximumBeforeOrbit_mem_exterior_of_ne_local
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (O : (D.chronologicalMaximumLocalField t ht).OrbitIndex)
    (hne : (O : Set E₁) ≠
      (((D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set E₁)) :
    (O : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalBeforeTime t ht) := by
  intro x hxO
  by_contra houtside
  have hxFiber : x ∈ (D.chronologicalBeforeSlice t ht).fiber := by
    apply (D.chronologicalMaximumLocalField t ht).orbit_subset_fiber
      ((D.chronologicalMaximumLocalField t ht).orbitPoint_mem_fiber O)
    rwa [← (D.chronologicalMaximumLocalField t ht).orbitPoint_orbit O]
  have hxzero : D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalBeforeTime t ht)) = 0 := by
    rw [chronologicalBeforeSlice,
      SlabTamedField.sliceFLSAt_fiber] at hxFiber
    change D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalBeforeTime t ht)) = 0 at hxFiber
    exact hxFiber
  have hxCovered : x ∈ (D.position.eventModel t ht).coveredSliceFiber
      (D.chronologicalBeforeTime t ht) :=
    ⟨lt_of_not_ge houtside, hxzero⟩
  have hxLocal := D.chronologicalMaximumBeforeCoveredSliceFiber_subset_orbit
    t ht hindex (D.chronologicalMaximumLocalField t ht) hxCovered
  have hxO' : x ∈ (D.chronologicalMaximumLocalField t ht).orbit
      ((D.chronologicalMaximumLocalField t ht).orbitPoint O) := by
    rwa [← (D.chronologicalMaximumLocalField t ht).orbitPoint_orbit O]
  apply hne
  calc
    (O : Set E₁) = (D.chronologicalMaximumLocalField t ht).orbit
        ((D.chronologicalMaximumLocalField t ht).orbitPoint O) :=
      (D.chronologicalMaximumLocalField t ht).orbitPoint_orbit O
    _ = (D.chronologicalMaximumLocalField t ht).orbit x :=
      ((D.chronologicalMaximumLocalField t ht).orbit_eq_of_mem hxO').symm
    _ = (D.chronologicalMaximumLocalField t ht).orbit
        (spacePart ((D.position.eventModel t ht).definiteCircle
          (D.chronologicalWindowRadius t ht) 0)) :=
      (D.chronologicalMaximumLocalField t ht).orbit_eq_of_mem hxLocal
    _ = (((D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 :
          (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set E₁) := by
      change (D.chronologicalMaximumLocalField t ht).orbit
          (spacePart ((D.position.eventModel t ht).definiteCircle
            (D.chronologicalWindowRadius t ht) 0)) =
        (D.chronologicalMaximumLocalField t ht).orbit
          (D.chronologicalMaximumLocalParam t ht hindex).p
      apply congrArg ((D.chronologicalMaximumLocalField t ht).orbit)
      change spacePart ((D.position.eventModel t ht).definiteCircle
          (D.chronologicalWindowRadius t ht) 0) =
        spacePart ((D.position.eventModel t ht).definiteCircle
          (D.chronologicalWindowRadius t ht)
          (2 * Real.pi * (((0 : I) : ℝ))))
      norm_num


-- @@ L514-540 verbatim
/-- At a maximum, every outgoing component is outside the complete-cover ball. -/
theorem chronologicalMaximumAfterOrbit_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (O : (D.chronologicalAfterField t ht).OrbitIndex) :
    (O : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalAfterTime t ht) := by
  intro x hxO
  by_contra houtside
  have hxFiber : x ∈ (D.chronologicalAfterSlice t ht).fiber := by
    apply (D.chronologicalAfterField t ht).orbit_subset_fiber
      ((D.chronologicalAfterField t ht).orbitPoint_mem_fiber O)
    rwa [← (D.chronologicalAfterField t ht).orbitPoint_orbit O]
  have hxzero : D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalAfterTime t ht)) = 0 := by
    rw [chronologicalAfterSlice,
      SlabTamedField.sliceFLSAt_fiber] at hxFiber
    change D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalAfterTime t ht)) = 0 at hxFiber
    exact hxFiber
  have hxCovered : x ∈ (D.position.eventModel t ht).coveredSliceFiber
      (D.chronologicalAfterTime t ht) :=
    ⟨lt_of_not_ge houtside, hxzero⟩
  rw [D.chronologicalMaximumAfterCoveredSliceFiber_eq_empty
    t ht hindex] at hxCovered
  exact hxCovered


-- @@ L542-542 verbatim
/-! ## Chronological capture contracts -/


-- @@ L544-572 verbatim
/-- The exact remaining capture condition for a production minimum.  The
incoming selected family is complete; the outgoing family has the born local
circle removed.  In particular, `safe` records the only quantitative fact not
supplied by existence of the compact critical-exterior field. -/
abbrev ChronologicalMinimumExteriorFlowCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :=
  CriticalExteriorFlowCapture
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    (D.position.eventModel t ht).fiberCoverRadius
    (D.chronologicalWindowRadius t ht ^ 2)
    (D.chronologicalCriticalExteriorTimeField t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalBeforeField t ht)
    (D.chronologicalMinimumLocalField t ht)
    ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
      (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
        (D.chronologicalBeforeField t ht))
    (((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
      (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
        (D.chronologicalMinimumLocalField t ht)) \
      {(((D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set E₁)})


-- @@ L574-601 verbatim
/-- The exact remaining capture condition for a production maximum.  The
dying local circle is removed on the incoming side; the outgoing selected
family is complete. -/
abbrev ChronologicalMaximumExteriorFlowCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :=
  CriticalExteriorFlowCapture
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    (D.position.eventModel t ht).fiberCoverRadius
    (D.chronologicalWindowRadius t ht ^ 2)
    (D.chronologicalCriticalExteriorTimeField t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalMaximumLocalField t ht)
    (D.chronologicalAfterField t ht)
    (((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
      (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
        (D.chronologicalMaximumLocalField t ht)) \
      {(((D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set E₁)})
    ((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
      (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
        (D.chronologicalAfterField t ht))


-- @@ L603-619 verbatim
/-- Local excision certifies that every source component requested by the
minimum capture contract really is outside the cover ball. -/
theorem minimumCapture_negative_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (H : D.ChronologicalMinimumExteriorFlowCapture
      t ht hpositive hindex)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
        (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalBeforeField t ht))}) :
    (O.1 : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalBeforeTime t ht) :=
  D.chronologicalMinimumBeforeOrbit_mem_exterior t ht hindex O.1


-- @@ L621-641 verbatim
/-- Local excision certifies the same fact for every target component captured
at a minimum; membership in the target family supplies nonlocality. -/
theorem minimumCapture_positive_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (H : D.ChronologicalMinimumExteriorFlowCapture
      t ht hpositive hindex)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
        (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalBeforeField t ht))}) :
    ((H.orbitEquiv O).1 : Set E₁) ∈
      D.chronologicalExteriorOrbitCollection t ht
        (D.chronologicalAfterTime t ht) := by
  apply D.chronologicalMinimumAfterOrbit_mem_exterior_of_ne_local
    t ht hpositive hindex (H.orbitEquiv O).1
  exact ((D.chronologicalMinimumLocalField t ht).mem_selectedOrbitFinset
    (H.orbitEquiv O).1).mp (H.orbitEquiv O).2 |>.2


-- @@ L643-664 verbatim
/-- Local excision certifies that every source component requested by the
maximum capture contract is outside the cover ball. -/
theorem maximumCapture_negative_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (H : D.ChronologicalMaximumExteriorFlowCapture
      t ht hpositive hindex)
    (O : {O // O ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
        (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalMaximumLocalField t ht)) \
        {(((D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 :
          (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set E₁)})}) :
    (O.1 : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalBeforeTime t ht) := by
  apply D.chronologicalMaximumBeforeOrbit_mem_exterior_of_ne_local
    t ht hpositive hindex O.1
  exact ((D.chronologicalMaximumLocalField t ht).mem_selectedOrbitFinset
    O.1).mp O.2 |>.2


-- @@ L666-686 verbatim
/-- Local excision certifies the outgoing side of the maximum capture
contract as exterior as well. -/
theorem maximumCapture_positive_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (H : D.ChronologicalMaximumExteriorFlowCapture
      t ht hpositive hindex)
    (O : {O // O ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
        (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalMaximumLocalField t ht)) \
        {(((D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 :
          (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set E₁)})}) :
    ((H.orbitEquiv O).1 : Set E₁) ∈
      D.chronologicalExteriorOrbitCollection t ht
        (D.chronologicalAfterTime t ht) :=
  D.chronologicalMaximumAfterOrbit_mem_exterior t ht hindex
    (H.orbitEquiv O).1


-- @@ L688-688 verbatim
/-! ## Automatically constructed event-bracket transports -/


-- @@ L690-717 verbatim
/-- The minimum capture cylinder, composed with both regular window flows,
is the literal across-critical `hcross` required by the production callback. -/
def minimumExteriorTransport_of_capture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (H : D.ChronologicalMinimumExteriorFlowCapture
      t ht hpositive hindex) :
    (D.position.eventBeforeField t ht).SelectedDeltaTransport
      (D.position.eventAfterField t ht)
      ((D.signedOutput.sliceSign (D.position.eventBracket t ht).before
        (D.position.eventBracket t ht).before_regular).positiveOrbitCollection
          (D.position.eventBeforeField t ht))
      (((D.signedOutput.sliceSign (D.position.eventBracket t ht).after
        (D.position.eventBracket t ht).after_regular).positiveOrbitCollection
          (D.position.eventAfterField t ht)) \
        {(((D.chronologicalMinimumBracketOrbit t ht hpositive hindex).1 :
          (D.position.eventAfterField t ht).OrbitIndex) : Set E₁)}) := by
  let Tin := D.beforeWindowPositiveTransport t ht
    (D.position.eventBeforeField t ht)
    (D.chronologicalBeforeField t ht)
  let Tcross := H.toSelectedDeltaTransport
  let Tout := TamedField.SelectedDeltaTransport.sdiffSingleton
    (D.chronologicalMinimumWindowTransport t ht)
    (D.chronologicalMinimumLocalOrbit t ht hpositive hindex)
  exact Tin.trans (Tcross.trans Tout)


-- @@ L719-748 verbatim
/-- The reverse maximum capture cylinder, composed with both regular window
flows, is the literal maximum `hcross`. -/
def maximumExteriorTransport_of_capture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (H : D.ChronologicalMaximumExteriorFlowCapture
      t ht hpositive hindex) :
    (D.position.eventAfterField t ht).SelectedDeltaTransport
      (D.position.eventBeforeField t ht)
      ((D.signedOutput.sliceSign (D.position.eventBracket t ht).after
        (D.position.eventBracket t ht).after_regular).positiveOrbitCollection
          (D.position.eventAfterField t ht))
      (((D.signedOutput.sliceSign (D.position.eventBracket t ht).before
        (D.position.eventBracket t ht).before_regular).positiveOrbitCollection
          (D.position.eventBeforeField t ht)) \
        {(((D.chronologicalMaximumBracketOrbit t ht hpositive hindex).1 :
          (D.position.eventBeforeField t ht).OrbitIndex) : Set E₁)}) := by
  let Tout := TamedField.SelectedDeltaTransport.symm
    (D.afterWindowPositiveTransport t ht
      (D.chronologicalAfterField t ht)
      (D.position.eventAfterField t ht))
  let Tcross := TamedField.SelectedDeltaTransport.symm
    H.toSelectedDeltaTransport
  let Tin := TamedField.SelectedDeltaTransport.sdiffSingleton
    (D.chronologicalMaximumWindowTransport t ht)
    (D.chronologicalMaximumLocalOrbit t ht hpositive hindex)
  exact Tout.trans (Tcross.trans Tin)


-- @@ L750-750 verbatim
/-! ## Ledger callbacks with no explicit `hcross` argument -/


-- @@ L752-767 verbatim
/-- A captured production minimum directly supplies its positive ledger move. -/
def minimumPositiveLedgerMove_of_capture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hclass : loopClassZ2
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop_closed = 1)
    (H : D.ChronologicalMinimumExteriorFlowCapture
      t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  D.minimumPositiveLedgerMove_of_exteriorTransport
    t ht hpositive hindex hclass
    (D.minimumExteriorTransport_of_capture t ht hpositive hindex H)


-- @@ L769-784 verbatim
/-- A captured production maximum directly supplies its positive ledger move. -/
def maximumPositiveLedgerMove_of_capture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hclass : loopClassZ2
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop_closed = 1)
    (H : D.ChronologicalMaximumExteriorFlowCapture
      t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  D.maximumPositiveLedgerMove_of_exteriorTransport
    t ht hpositive hindex hclass
    (D.maximumExteriorTransport_of_capture t ht hpositive hindex H)


-- @@ L786-786 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L788-788 verbatim
end Submission
