import Submission.ProductionMorseDefiniteReverseTransport
import Submission.ProductionMorseSaddleBalancedSupply


-- @@ L4-15 verbatim
/-!
# Reverse transport and cardinality balance at production saddles

The saddle exterior core uses the quantitative half-cover radius.  The same
compact field therefore runs backwards from the chronological after-slice to
the critical half-core.  We transport the endpoint fields across the
propositionally equal negative-step slices, construct injective reverse maps,
and combine them with the forward flow injections to force equality of the
two finite exterior component counts.

Only genuine branch noncollision and merge/split topology remain as inputs.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false

-- @@ L18-18 verbatim
set_option maxHeartbeats 2400000


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function

-- @@ L23-23 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
variable {a : ℕ}

-- @@ L28-28 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L29-29 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L30-30 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L32-32 verbatim
local notation "Eₐ" => EuclideanSpace ℝ (Fin (a + 3))


-- @@ L34-34 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L36-36 verbatim
/-! ## Common transported reverse core -/


-- @@ L38-49 verbatim
/-- The chronological after-field transported to the source endpoint of a
negative canonical half-step. -/
def chronologicalSaddleReverseSourceField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    TamedField (SlabTamedField.sliceFLSAt
      D.signedOutput.cobordism.toLevelCobordismData
      (tcoord (D.position.eventCenter t ht) -
        -(D.chronologicalWindowRadius t ht ^ 2))
      (D.chronologicalReverseAfter_regular t ht)) :=
  (D.chronologicalAfterField t ht).transport
    (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)


-- @@ L51-62 verbatim
/-- The chronological before-field transported to the target endpoint of a
negative canonical half-step. -/
def chronologicalSaddleReverseTargetField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    TamedField (SlabTamedField.sliceFLSAt
      D.signedOutput.cobordism.toLevelCobordismData
      (tcoord (D.position.eventCenter t ht) +
        -(D.chronologicalWindowRadius t ht ^ 2))
      (D.chronologicalReverseBefore_regular t ht)) :=
  (D.chronologicalBeforeField t ht).transport
    (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)


-- @@ L64-73 verbatim
/-- Transport of a selected after-orbit family to the negative-step source
field. -/
def chronologicalSaddleReverseSourceEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set Eₐ)) :
    {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset A} ≃
      {O // O ∈ (D.chronologicalSaddleReverseSourceField t ht).selectedOrbitFinset A} :=
  (D.chronologicalAfterField t ht).selectedOrbitTransportEquiv
    (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht) A


-- @@ L75-83 verbatim
/-- Transport of reverse target orbit indices back to the literal
chronological before-field. -/
def chronologicalSaddleReverseTargetOrbitEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    (D.chronologicalBeforeField t ht).OrbitIndex ≃
      (D.chronologicalSaddleReverseTargetField t ht).OrbitIndex :=
  (D.chronologicalBeforeField t ht).orbitIndexTransportEquiv
    (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)


-- @@ L85-106 verbatim
/-- Midpoint contract stated on the literal chronological after-field.

This is a named proposition rather than a reducible function abbreviation:
keeping the large dependent selected-orbit type behind a projection prevents
downstream noncollision wrappers from repeatedly normalizing the entire
production package. -/
structure ChronologicalSaddleReverseMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set Eₐ)) : Prop where
  midpoint_mem : ∀
      (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset A})
      (q : I),
    (D.chronologicalSaddleCriticalExteriorTimeField t ht).base.flow
        ((D.chronologicalAfterField t ht).intrinsicSimpleClosedOrbitParam O.1
          |>.exteriorAmbientLoop q)
        (-(D.chronologicalWindowRadius t ht ^ 2)) ∈
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        ((D.position.eventModel t ht).fiberCoverRadius / 2)


-- @@ L108-154 verbatim
/-- The generic negative-step half-core, with endpoint transports hidden in
its construction. -/
def chronologicalSaddleReverseExteriorFlowCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set Eₐ))
    (hmidpoint : D.ChronologicalSaddleReverseMidpointCapture t ht A) :
    CanonicalCriticalExteriorFlowCore (a + 2) where
  C := D.signedOutput.cobordism.toLevelCobordismData
  criticalCenter := D.position.eventCenter t ht
  t := tcoord (D.position.eventCenter t ht)
  r := (D.position.eventModel t ht).fiberCoverRadius / 2
  ε := -(D.chronologicalWindowRadius t ht ^ 2)
  R := D.chronologicalSaddleCriticalExteriorTimeField t ht
  hneg := D.chronologicalReverseAfter_regular t ht
  hpos := D.chronologicalReverseBefore_regular t ht
  Vneg := D.chronologicalSaddleReverseSourceField t ht
  Vpos := D.chronologicalSaddleReverseTargetField t ht
  A := A
  safe := by
    simpa [chronologicalSaddleCriticalExteriorTimeField,
      chronologicalExteriorSlabTimeField] using
      D.chronologicalWindowRadius_sq_reverse_safe t ht
  midpoint_mem := by
    intro O q
    let e := D.chronologicalSaddleReverseSourceEquiv t ht A
    let O₀ := e.symm O
    have hloop :
        (D.chronologicalSaddleReverseSourceField t ht
            |>.intrinsicSimpleClosedOrbitParam O.1).exteriorAmbientLoop q =
          (D.chronologicalAfterField t ht
            |>.intrinsicSimpleClosedOrbitParam O₀.1).exteriorAmbientLoop q := by
      change cobSpaceTime
          ((D.chronologicalSaddleReverseSourceField t ht
            |>.intrinsicSimpleClosedOrbitParam O.1).curve q)
          (tcoord (D.position.eventCenter t ht) -
            -(D.chronologicalWindowRadius t ht ^ 2)) =
        cobSpaceTime
          ((D.chronologicalAfterField t ht
            |>.intrinsicSimpleClosedOrbitParam O₀.1).curve q)
          (D.chronologicalAfterTime t ht)
      apply congrArg₂ cobSpaceTime
      · exact (D.chronologicalAfterField t ht).transportedIntrinsicCurve_symm
          (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht) A O q
      · exact D.chronologicalReverseAfterTime_eq t ht
    rw [hloop]
    exact hmidpoint.midpoint_mem O₀ q


-- @@ L156-156 verbatim
/-! ## Automatic reverse midpoint capture -/


-- @@ L158-187 verbatim
/-- A merge target orbit avoids both local positive branches once the merge
topology identifies those two branch indices. -/
theorem chronologicalSaddleMergeTargetOrbit_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (O : (D.chronologicalAfterField t ht).OrbitIndex)
    (hO : (O : Set Eₐ) ∈
      D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex) :
    (O : Set Eₐ) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalAfterTime t ht) := by
  have hneNegative : (O : Set Eₐ) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) := by
    simpa only [Set.mem_singleton_iff] using hO.2
  have hbranches :
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) =
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) :=
    congrArg (fun Q : (D.chronologicalAfterField t ht).OrbitIndex =>
      (Q : Set Eₐ)) Htop.positive_eq
  have hnePositive : (O : Set Eₐ) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) := by
    intro h
    exact hneNegative (h.trans hbranches.symm)
  exact D.chronologicalSaddleAfterOrbit_mem_exterior_of_ne_branches
    t ht hindex O hnePositive hneNegative


-- @@ L189-209 verbatim
/-- Every split target orbit explicitly avoids both positive-side local
branches. -/
theorem chronologicalSaddleSplitTargetOrbit_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (O : (D.chronologicalAfterField t ht).OrbitIndex)
    (hO : (O : Set Eₐ) ∈
      D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex) :
    (O : Set Eₐ) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalAfterTime t ht) := by
  have hneNegative : (O : Set Eₐ) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) := by
    simpa only [Set.mem_singleton_iff] using hO.1.2
  have hnePositive : (O : Set Eₐ) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) := by
    simpa only [Set.mem_singleton_iff] using hO.2
  exact D.chronologicalSaddleAfterOrbit_mem_exterior_of_ne_branches
    t ht hindex O hnePositive hneNegative


-- @@ L211-234 verbatim
theorem chronologicalSaddleMergeReverseMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex) :
    D.ChronologicalSaddleReverseMidpointCapture t ht
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex) := by
  constructor
  intro O q
  apply D.chronologicalExteriorSlabReverseMidpoint_mem_halfCriticalCore t ht
  · let P := D.chronologicalAfterField t ht
        |>.intrinsicSimpleClosedOrbitParam O.1
    apply D.chronologicalOrbitPoint_mem_exteriorSlabCore
      t ht (D.chronologicalAfterTime t ht)
      ⟨(D.chronologicalAfterTime_mem_bracket t ht).1.le,
        (D.chronologicalAfterTime_mem_bracket t ht).2.le⟩
      (D.chronologicalAfterTime_regular t ht)
      (D.chronologicalAfterField t ht) O.1
    · rw [(D.chronologicalAfterField t ht).orbitPoint_orbit O.1]
      exact P.curve_mem_orbit q
    · apply D.chronologicalSaddleMergeTargetOrbit_mem_exterior
        t ht hindex Htop O.1
      exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset O.1).mp O.2
  · simp [SimpleClosedOrbitParam.exteriorAmbientLoop]


-- @@ L236-258 verbatim
theorem chronologicalSaddleSplitReverseMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    D.ChronologicalSaddleReverseMidpointCapture t ht
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex) := by
  constructor
  intro O q
  apply D.chronologicalExteriorSlabReverseMidpoint_mem_halfCriticalCore t ht
  · let P := D.chronologicalAfterField t ht
        |>.intrinsicSimpleClosedOrbitParam O.1
    apply D.chronologicalOrbitPoint_mem_exteriorSlabCore
      t ht (D.chronologicalAfterTime t ht)
      ⟨(D.chronologicalAfterTime_mem_bracket t ht).1.le,
        (D.chronologicalAfterTime_mem_bracket t ht).2.le⟩
      (D.chronologicalAfterTime_regular t ht)
      (D.chronologicalAfterField t ht) O.1
    · rw [(D.chronologicalAfterField t ht).orbitPoint_orbit O.1]
      exact P.curve_mem_orbit q
    · apply D.chronologicalSaddleSplitTargetOrbit_mem_exterior
        t ht hindex O.1
      exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset O.1).mp O.2
  · simp [SimpleClosedOrbitParam.exteriorAmbientLoop]


-- @@ L260-260 verbatim
/-! ## Reverse target orbits and automatic sign transport -/


-- @@ L262-274 verbatim
/-- Run an after-side selected orbit through the transported negative-step
core and return its target index in the literal chronological before-field. -/
abbrev chronologicalSaddleReverseTargetOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set Eₐ))
    (hmidpoint : D.ChronologicalSaddleReverseMidpointCapture t ht A)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset A}) :
    (D.chronologicalBeforeField t ht).OrbitIndex :=
  let H := D.chronologicalSaddleReverseExteriorFlowCore t ht A hmidpoint
  let eSource := D.chronologicalSaddleReverseSourceEquiv t ht A
  let eTarget := D.chronologicalSaddleReverseTargetOrbitEquiv t ht
  eTarget.symm (H.targetOrbit (eSource O))


-- @@ L276-403 verbatim
/-- Positivity is preserved by the complete reverse two-half flow.  The only
input about the family is that its selected after-orbits are positive. -/
theorem chronologicalSaddleReverseTargetOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set Eₐ))
    (hmidpoint : D.ChronologicalSaddleReverseMidpointCapture t ht A)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset A})
    (hsourcePositive : (O.1 : Set Eₐ) ∈
      D.chronologicalSaddlePositiveCollection t ht) :
    D.chronologicalSaddleReverseTargetOrbit t ht A hmidpoint O ∈
      (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleNegativeCollection t ht) := by
  let H := D.chronologicalSaddleReverseExteriorFlowCore t ht A hmidpoint
  let eSource := D.chronologicalSaddleReverseSourceEquiv t ht A
  let eTarget := D.chronologicalSaddleReverseTargetOrbitEquiv t ht
  let OH := eSource O
  let Q := eTarget.symm (H.targetOrbit OH)
  let Vneg := D.chronologicalAfterField t ht
  let Vpos := D.chronologicalBeforeField t ht
  let Sneg := D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)
  let Spos := D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)
  change Q ∈ Vpos.selectedOrbitFinset (Spos.positiveOrbitCollection Vpos)
  have hsourceSign : 0 < Sneg (Vneg.orbitPoint O.1) :=
    (Sneg.mem_positiveOrbitCollection_iff Vneg O.1).mp hsourcePositive
  let P := Vneg.intrinsicSimpleClosedOrbitParam O.1
  let p := P.exteriorAmbientLoop 0
  have hpEq : p = cobSpaceTime (Vneg.orbitPoint O.1)
      (D.chronologicalAfterTime t ht) := by
    change cobSpaceTime (P.curve 0) (D.chronologicalAfterTime t ht) = _
    rw [P.curve_zero]
    rfl
  have hstartSign : 0 < D.signedOutput p := by
    rw [hpEq]
    exact hsourceSign
  have hpFiber : H.C.G p = 0 := P.exteriorAmbientLoop_fiber 0
  have hsourceLoop : (H.negativeParam OH).exteriorAmbientLoop 0 = p := by
    change cobSpaceTime
        ((D.chronologicalSaddleReverseSourceField t ht
          |>.intrinsicSimpleClosedOrbitParam OH.1).curve 0)
        (tcoord (D.position.eventCenter t ht) -
          -(D.chronologicalWindowRadius t ht ^ 2)) =
      cobSpaceTime (P.curve 0) (D.chronologicalAfterTime t ht)
    apply congrArg₂ cobSpaceTime
    · change
        ((Vneg.transport
          (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
            |>.intrinsicSimpleClosedOrbitParam OH.1).curve 0) = P.curve 0
      calc
        _ = (Vneg.intrinsicSimpleClosedOrbitParam
              (((Vneg.selectedOrbitTransportEquiv
                (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
                A).symm OH).1)).curve 0 :=
          Vneg.transportedIntrinsicCurve_symm
            (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht) A OH 0
        _ = P.curve 0 := by
          have hO : (Vneg.selectedOrbitTransportEquiv
              (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht) A).symm OH = O := by
            change eSource.symm OH = O
            exact eSource.symm_apply_apply O
          rw [hO]
    · exact D.chronologicalReverseAfterTime_eq t ht
  have hthrough : 0 < D.signedOutput (H.R.base.flow p (2 * H.ε)) :=
    D.compactTimeTamedField_flow_positive H.R hpFiber hstartSign _
  have hdouble : H.R.base.flow p (2 * H.ε) =
      H.R.base.flow (H.R.base.flow p H.ε) H.ε := by
    simpa [two_mul] using
      (congrFun (H.R.base.flow_shift p H.ε) H.ε).symm
  have hcore : H.coreLoop OH 0 = H.R.base.flow p H.ε := by
    change H.R.base.flow ((H.negativeParam OH).exteriorAmbientLoop 0) H.ε = _
    rw [hsourceLoop]
  have hendSign : 0 < D.signedOutput
      (H.R.base.flow (H.coreLoop OH 0) H.ε) := by
    rw [hcore, ← hdouble]
    exact hthrough
  have hendEq : cobSpaceTime (H.positiveCurve OH 0)
      (D.chronologicalBeforeTime t ht) =
      H.R.base.flow (H.coreLoop OH 0) H.ε := by
    calc
      cobSpaceTime (H.positiveCurve OH 0)
          (D.chronologicalBeforeTime t ht) =
          cobSpaceTime (H.positiveCurve OH 0) (H.t + H.ε) :=
        congrArg₂ cobSpaceTime rfl
          (D.chronologicalReverseBeforeTime_eq t ht).symm
      _ = H.R.base.flow (H.coreLoop OH 0) H.ε := by
        rw [← H.positiveEndpoint_time OH 0]
        exact spaceTime_spacePart _
  have hbaseSign : 0 < Spos (H.positiveCurve OH 0) := by
    change 0 < D.signedOutput (cobSpaceTime (H.positiveCurve OH 0)
      (D.chronologicalBeforeTime t ht))
    rw [hendEq]
    exact hendSign
  have hpositiveFiber : H.positiveCurve OH 0 ∈
      (D.chronologicalBeforeSlice t ht).fiber := by
    rw [chronologicalBeforeSlice, SlabTamedField.sliceFLSAt_fiber]
    change D.signedOutput.cobordism.G
      (cobSpaceTime (H.positiveCurve OH 0)
        (D.chronologicalBeforeTime t ht)) = 0
    rw [hendEq]
    exact H.R.flow_mem_fiber (H.coreLoop_fiber OH 0) H.ε
  have htargetSet : (Q : Set Eₐ) =
      Vpos.orbit (H.positiveCurve OH 0) := by
    calc
      (Q : Set Eₐ) = (H.targetOrbit OH : Set Eₐ) := by
        change ((((Vpos.orbitIndexTransportEquiv
          (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)).symm
            (H.targetOrbit OH)) : Vpos.OrbitIndex) : Set Eₐ) = _
        exact Vpos.orbitIndexTransportEquiv_symm_val
          (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)
          (H.targetOrbit OH)
      _ = H.Vpos.orbit (H.positiveCurve OH 0) := H.targetOrbit_coe OH
      _ = Vpos.orbit (H.positiveCurve OH 0) := by
        change (Vpos.transport
          (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)).orbit
            (H.positiveCurve OH 0) = Vpos.orbit (H.positiveCurve OH 0)
        exact Vpos.transport_orbit
          (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)
          (H.positiveCurve OH 0)
  have htargetPoint : Vpos.orbitPoint Q ∈
      Vpos.orbit (H.positiveCurve OH 0) := by
    rw [← htargetSet, Vpos.orbitPoint_orbit]
    exact Vpos.mem_orbit_self _
  have htargetSign : 0 < Spos (Vpos.orbitPoint Q) :=
    (Spos.pos_iff_of_mem_orbit Vpos hpositiveFiber htargetPoint).mp hbaseSign
  apply (Vpos.mem_selectedOrbitFinset Q).mpr
  exact (Spos.mem_positiveOrbitCollection_iff Vpos Q).mpr htargetSign


-- @@ L405-405 verbatim
/-! ## Merge and split reverse maps -/


-- @@ L407-417 verbatim
abbrev chronologicalSaddleMergeReverseTargetOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)}) :
    (D.chronologicalBeforeField t ht).OrbitIndex :=
  D.chronologicalSaddleReverseTargetOrbit t ht
    (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)
    (D.chronologicalSaddleMergeReverseMidpointCapture t ht hindex Htop) O


-- @@ L419-428 verbatim
abbrev chronologicalSaddleSplitReverseTargetOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)}) :
    (D.chronologicalBeforeField t ht).OrbitIndex :=
  D.chronologicalSaddleReverseTargetOrbit t ht
    (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)
    (D.chronologicalSaddleSplitReverseMidpointCapture t ht hindex) O


-- @@ L430-441 verbatim
theorem chronologicalSaddleMergeReverseTargetOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)}) :
    D.chronologicalSaddleMergeReverseTargetOrbit t ht hindex Htop O ∈
      (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleNegativeCollection t ht) := by
  apply D.chronologicalSaddleReverseTargetOrbit_mem_positive
  exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset O.1).mp O.2 |>.1


-- @@ L443-453 verbatim
theorem chronologicalSaddleSplitReverseTargetOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)}) :
    D.chronologicalSaddleSplitReverseTargetOrbit t ht hindex O ∈
      (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleNegativeCollection t ht) := by
  apply D.chronologicalSaddleReverseTargetOrbit_mem_positive
  exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset O.1).mp O.2 |>.1.1


-- @@ L455-476 verbatim
/-- The reverse merge flow must avoid both distinguished incoming branch
components.  Positivity and exterior capture are automatic.  A proposition
record keeps the dependent orbit family opaque to downstream elaboration. -/
structure ChronologicalSaddleMergeReverseNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex) : Prop where
  target_ne_negative : ∀
      O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)},
    ((D.chronologicalSaddleMergeReverseTargetOrbit t ht hindex Htop O :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set Eₐ) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set Eₐ)
  target_ne_positive : ∀
      O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)},
    ((D.chronologicalSaddleMergeReverseTargetOrbit t ht hindex Htop O :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set Eₐ) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .positive :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set Eₐ)


-- @@ L478-490 verbatim
/-- Split reverse flow has one distinguished incoming component to avoid;
the split topology already identifies its two local representatives. -/
structure ChronologicalSaddleSplitReverseNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) : Prop where
  target_ne_negative : ∀
      O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)},
    ((D.chronologicalSaddleSplitReverseTargetOrbit t ht hindex O :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set Eₐ) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set Eₐ)


-- @@ L492-515 verbatim
def chronologicalSaddleMergeReverseTargetMap
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (hnoncollision : D.ChronologicalSaddleMergeReverseNoncollision
      t ht hindex Htop) :
    {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)} →
    {Q // Q ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)} := by
  intro O
  refine ⟨D.chronologicalSaddleMergeReverseTargetOrbit
      t ht hindex Htop O, ?_⟩
  apply ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · constructor
    · exact ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset _).mp
        (D.chronologicalSaddleMergeReverseTargetOrbit_mem_positive
          t ht hindex Htop O)
    · simpa only [Set.mem_singleton_iff] using
        hnoncollision.target_ne_negative O
  · simpa only [Set.mem_singleton_iff] using
      hnoncollision.target_ne_positive O


-- @@ L517-537 verbatim
theorem chronologicalSaddleMergeReverseTargetMap_injective
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (hnoncollision : D.ChronologicalSaddleMergeReverseNoncollision
      t ht hindex Htop) :
    Function.Injective (D.chronologicalSaddleMergeReverseTargetMap
      t ht hindex Htop hnoncollision) := by
  intro O P hOP
  let A := D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex
  let hm := D.chronologicalSaddleMergeReverseMidpointCapture t ht hindex Htop
  let H := D.chronologicalSaddleReverseExteriorFlowCore t ht A hm
  let eSource := D.chronologicalSaddleReverseSourceEquiv t ht A
  let eTarget := D.chronologicalSaddleReverseTargetOrbitEquiv t ht
  have hval := congrArg Subtype.val hOP
  change eTarget.symm (H.targetOrbit (eSource O)) =
    eTarget.symm (H.targetOrbit (eSource P)) at hval
  apply eSource.injective
  apply H.targetOrbit_injective
  exact eTarget.symm.injective hval


-- @@ L539-557 verbatim
def chronologicalSaddleSplitReverseTargetMap
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hnoncollision : D.ChronologicalSaddleSplitReverseNoncollision
      t ht hindex) :
    {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)} →
    {Q // Q ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)} := by
  intro O
  refine ⟨D.chronologicalSaddleSplitReverseTargetOrbit t ht hindex O, ?_⟩
  apply ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · exact ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset _).mp
      (D.chronologicalSaddleSplitReverseTargetOrbit_mem_positive
        t ht hindex O)
  · simpa only [Set.mem_singleton_iff] using
      hnoncollision.target_ne_negative O


-- @@ L559-578 verbatim
theorem chronologicalSaddleSplitReverseTargetMap_injective
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hnoncollision : D.ChronologicalSaddleSplitReverseNoncollision
      t ht hindex) :
    Function.Injective (D.chronologicalSaddleSplitReverseTargetMap
      t ht hindex hnoncollision) := by
  intro O P hOP
  let A := D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex
  let hm := D.chronologicalSaddleSplitReverseMidpointCapture t ht hindex
  let H := D.chronologicalSaddleReverseExteriorFlowCore t ht A hm
  let eSource := D.chronologicalSaddleReverseSourceEquiv t ht A
  let eTarget := D.chronologicalSaddleReverseTargetOrbitEquiv t ht
  have hval := congrArg Subtype.val hOP
  change eTarget.symm (H.targetOrbit (eSource O)) =
    eTarget.symm (H.targetOrbit (eSource P)) at hval
  apply eSource.injective
  apply H.targetOrbit_injective
  exact eTarget.symm.injective hval


-- @@ L580-580 verbatim
/-! ## Forward injections and finite component balance -/


-- @@ L582-597 verbatim
/-- The single merge-side forward noncollision: the forced exterior target
must avoid the globally merged outgoing branch. -/
structure ChronologicalSaddleMergeForwardNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) : Prop where
  target_ne_outgoing : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleMergeExteriorFlowCore t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht)
      (D.chronologicalSaddleMergeExteriorMidpointCapture
        t ht hindex)).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ)


-- @@ L599-624 verbatim
/-- Split forward flow must avoid both distinguished outgoing branches. -/
structure ChronologicalSaddleSplitForwardNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex) : Prop where
  target_ne_negative : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht)
      (D.chronologicalSaddleSplitExteriorMidpointCapture
        t ht hindex Htop)).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ)
  target_ne_positive : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht)
      (D.chronologicalSaddleSplitExteriorMidpointCapture
        t ht hindex Htop)).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set Eₐ)


-- @@ L626-650 verbatim
def chronologicalSaddleMergeForwardTargetMap
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hnoncollision : D.ChronologicalSaddleMergeForwardNoncollision
      t ht hindex) :
    {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)} →
    {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)} := by
  let hm := D.chronologicalSaddleMergeExteriorMidpointCapture t ht hindex
  let H := D.chronologicalSaddleMergeExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht) hm
  intro O
  refine ⟨H.targetOrbit O, ?_⟩
  apply ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · have hsource : (O.1 : Set Eₐ) ∈
        D.chronologicalSaddleNegativeCollection t ht :=
      ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset O.1).mp
        O.2 |>.1.1
    exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mp
      (D.chronologicalSaddleTargetOrbit_mem_positive t ht _
        (D.chronologicalWindowRadius_sq_le_safeTime t ht) hm O hsource)
  · simpa [H, hm] using hnoncollision.target_ne_outgoing O


-- @@ L652-665 verbatim
theorem chronologicalSaddleMergeForwardTargetMap_injective
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hnoncollision : D.ChronologicalSaddleMergeForwardNoncollision
      t ht hindex) :
    Function.Injective (D.chronologicalSaddleMergeForwardTargetMap
      t ht hindex hnoncollision) := by
  intro O P hOP
  apply (D.chronologicalSaddleMergeExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht)
    (D.chronologicalSaddleMergeExteriorMidpointCapture
      t ht hindex)).targetOrbit_injective
  exact congrArg Subtype.val hOP


-- @@ L667-694 verbatim
def chronologicalSaddleSplitForwardTargetMap
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex)
    (hnoncollision : D.ChronologicalSaddleSplitForwardNoncollision
      t ht hindex Htop) :
    {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)} →
    {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)} := by
  let hm := D.chronologicalSaddleSplitExteriorMidpointCapture t ht hindex Htop
  let H := D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht) hm
  intro O
  refine ⟨H.targetOrbit O, ?_⟩
  apply ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · constructor
    · have hsource : (O.1 : Set Eₐ) ∈
          D.chronologicalSaddleNegativeCollection t ht :=
        ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset O.1).mp
          O.2 |>.1
      exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mp
        (D.chronologicalSaddleTargetOrbit_mem_positive t ht _
          (D.chronologicalWindowRadius_sq_le_safeTime t ht) hm O hsource)
    · simpa [H, hm] using hnoncollision.target_ne_negative O
  · simpa [H, hm] using hnoncollision.target_ne_positive O


-- @@ L696-710 verbatim
theorem chronologicalSaddleSplitForwardTargetMap_injective
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex)
    (hnoncollision : D.ChronologicalSaddleSplitForwardNoncollision
      t ht hindex Htop) :
    Function.Injective (D.chronologicalSaddleSplitForwardTargetMap
      t ht hindex Htop hnoncollision) := by
  intro O P hOP
  apply (D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht)
    (D.chronologicalSaddleSplitExteriorMidpointCapture
      t ht hindex Htop)).targetOrbit_injective
  exact congrArg Subtype.val hOP


-- @@ L712-733 verbatim
theorem chronologicalSaddleMergeExterior_card_eq_of_transports
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (hforward : D.ChronologicalSaddleMergeForwardNoncollision t ht hindex)
    (hreverse : D.ChronologicalSaddleMergeReverseNoncollision
      t ht hindex Htop) :
    ((D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)).card =
    ((D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)).card := by
  have hf := Fintype.card_le_of_injective
    (D.chronologicalSaddleMergeForwardTargetMap t ht hindex hforward)
    (D.chronologicalSaddleMergeForwardTargetMap_injective
      t ht hindex hforward)
  have hr := Fintype.card_le_of_injective
    (D.chronologicalSaddleMergeReverseTargetMap
      t ht hindex Htop hreverse)
    (D.chronologicalSaddleMergeReverseTargetMap_injective
      t ht hindex Htop hreverse)
  simpa only [Fintype.card_coe] using Nat.le_antisymm hf hr


-- @@ L735-756 verbatim
theorem chronologicalSaddleSplitExterior_card_eq_of_transports
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex)
    (hforward : D.ChronologicalSaddleSplitForwardNoncollision
      t ht hindex Htop)
    (hreverse : D.ChronologicalSaddleSplitReverseNoncollision t ht hindex) :
    ((D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)).card =
    ((D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)).card := by
  have hf := Fintype.card_le_of_injective
    (D.chronologicalSaddleSplitForwardTargetMap
      t ht hindex Htop hforward)
    (D.chronologicalSaddleSplitForwardTargetMap_injective
      t ht hindex Htop hforward)
  have hr := Fintype.card_le_of_injective
    (D.chronologicalSaddleSplitReverseTargetMap t ht hindex hreverse)
    (D.chronologicalSaddleSplitReverseTargetMap_injective
      t ht hindex hreverse)
  simpa only [Fintype.card_coe] using Nat.le_antisymm hf hr


-- @@ L758-758 verbatim
/-! ## Adapters to the completion-balance contracts -/


-- @@ L760-772 verbatim
def chronologicalSaddleMergeExteriorComponentBalance_of_transports
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (hforward : D.ChronologicalSaddleMergeForwardNoncollision t ht hindex)
    (hreverse : D.ChronologicalSaddleMergeReverseNoncollision
      t ht hindex Htop) :
    D.ChronologicalSaddleMergeExteriorComponentBalance t ht hindex
      (D.chronologicalSaddleMergeExteriorMidpointCapture t ht hindex) where
  target_ne_outgoing := hforward.target_ne_outgoing
  card_eq := D.chronologicalSaddleMergeExterior_card_eq_of_transports
    t ht hindex Htop hforward hreverse


-- @@ L774-788 verbatim
def chronologicalSaddleSplitExteriorComponentBalance_of_transports
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex)
    (hforward : D.ChronologicalSaddleSplitForwardNoncollision
      t ht hindex Htop)
    (hreverse : D.ChronologicalSaddleSplitReverseNoncollision t ht hindex) :
    D.ChronologicalSaddleSplitExteriorComponentBalance t ht hindex
      (D.chronologicalSaddleSplitExteriorMidpointCapture
        t ht hindex Htop) where
  target_ne_negative O := hforward.target_ne_negative O
  target_ne_positive O := hforward.target_ne_positive O
  card_eq := D.chronologicalSaddleSplitExterior_card_eq_of_transports
    t ht hindex Htop hforward hreverse


-- @@ L790-800 verbatim
def chronologicalSaddleMergeFlowSupply_of_transports
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (hforward : D.ChronologicalSaddleMergeForwardNoncollision t ht hindex)
    (hreverse : D.ChronologicalSaddleMergeReverseNoncollision
      t ht hindex Htop) :
    D.ChronologicalSaddleMergeFlowSupply t ht hindex :=
  (D.chronologicalSaddleMergeExteriorComponentBalance_of_transports
    t ht hindex Htop hforward hreverse).toFlowSupply


-- @@ L802-812 verbatim
def chronologicalSaddleSplitFlowSupply_of_transports
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex)
    (hforward : D.ChronologicalSaddleSplitForwardNoncollision
      t ht hindex Htop)
    (hreverse : D.ChronologicalSaddleSplitReverseNoncollision t ht hindex) :
    D.ChronologicalSaddleSplitFlowSupply t ht hindex :=
  (D.chronologicalSaddleSplitExteriorComponentBalance_of_transports
    t ht hindex Htop hforward hreverse).toFlowSupply


-- @@ L814-830 verbatim
/-- Assemble the reduced balanced merge record once the independent actual
three-orbit frame equation is supplied. -/
def chronologicalSaddleMergeBalancedSupply_of_transports
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (hforward : D.ChronologicalSaddleMergeForwardNoncollision t ht hindex)
    (hreverse : D.ChronologicalSaddleMergeReverseNoncollision
      t ht hindex Htop)
    (hframe : D.ChronologicalSaddleMergeActualFrameClassSupply
      t ht hindex) :
    D.ChronologicalSaddleMergeBalancedSupply t ht hindex where
  topology := Htop
  exterior := D.chronologicalSaddleMergeExteriorComponentBalance_of_transports
    t ht hindex Htop hforward hreverse
  frame := hframe


-- @@ L832-847 verbatim
/-- Split analogue of the top-level balanced adapter. -/
def chronologicalSaddleSplitBalancedSupply_of_transports
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex)
    (hforward : D.ChronologicalSaddleSplitForwardNoncollision
      t ht hindex Htop)
    (hreverse : D.ChronologicalSaddleSplitReverseNoncollision t ht hindex)
    (hframe : D.ChronologicalSaddleSplitActualFrameClassSupply
      t ht hindex) :
    D.ChronologicalSaddleSplitBalancedSupply t ht hindex where
  topology := Htop
  exterior := D.chronologicalSaddleSplitExteriorComponentBalance_of_transports
    t ht hindex Htop hforward hreverse
  frame := hframe


-- @@ L849-849 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L851-851 verbatim
end Submission
