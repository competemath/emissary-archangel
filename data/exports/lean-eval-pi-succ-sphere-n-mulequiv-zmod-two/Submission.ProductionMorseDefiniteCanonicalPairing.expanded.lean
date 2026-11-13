import Submission.ProductionMorseDefiniteExteriorCapture


-- @@ L3-15 verbatim
/-!
# Flow-induced canonical pairings for production definite Morse events

The canonical critical-exterior loop already determines its target orbit: flow
the intrinsic source loop to the critical slice and then through the second
half of the cylinder.  Consequently neither an arbitrary component
equivalence nor a separate target-base membership proof is geometric input.

This file proves that the resulting component map is injective.  A full
pairing therefore needs only target-family membership and surjectivity of this
specific map, in addition to the genuinely quantitative safe-time and
critical-exterior midpoint conditions.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false

-- @@ L18-18 verbatim
set_option maxHeartbeats 2400000


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function Metric

-- @@ L23-23 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
variable {n : ℕ}


-- @@ L29-29 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L30-30 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L32-32 verbatim
/-! ## A once-around parameter covers its entire orbit -/


-- @@ L34-34 verbatim
namespace SimpleClosedOrbitParam


-- @@ L36-36 verbatim
variable {X : FramedLevelSet n} {V : TamedField X}


-- @@ L38-88 verbatim
/-- A simple closed orbit parameter is onto the whole intrinsic flow orbit.

The existing API proves that its lifted phase ends at one positive or negative
fundamental period.  The intermediate value theorem and the standard closed
interval presentation of `AddCircle` then give surjectivity. -/
theorem exists_curve_eq_of_mem_orbit
    (P : SimpleClosedOrbitParam X V) {x : E₁}
    (hx : x ∈ V.orbit P.p) :
    ∃ u : I, P.curve u = x := by
  let T : ℝ := V.fundamentalPeriod P.hp
  letI : Fact (0 < T) := ⟨by
    dsimp [T]
    exact V.fundamentalPeriod_pos P.hp⟩
  let y : V.orbit P.p := ⟨x, hx⟩
  let θ : AddCircle T := (V.orbitCircleHomeomorph P.hp).symm y
  have finish : ∀ {u : I}, P.phase u = θ → P.curve u = x := by
    intro u hu
    have horbit : P.orbitPath u = y := by
      calc
        P.orbitPath u = V.orbitCircleHomeomorph P.hp (P.phase u) :=
          (P.orbitCircleHomeomorph_phase u).symm
        _ = V.orbitCircleHomeomorph P.hp θ := by rw [hu]
        _ = y := (V.orbitCircleHomeomorph P.hp).apply_symm_apply y
    exact congrArg Subtype.val horbit
  rcases P.phaseLift_one_eq_period_or_neg with hpositive | hnegative
  · have hθ : θ ∈
        ((↑) : ℝ → AddCircle T) '' Icc (0 : ℝ) (0 + T) := by
      rw [AddCircle.coe_image_Icc_eq]
      exact Set.mem_univ θ
    obtain ⟨s, hs, hsθ⟩ := hθ
    have hsrange : s ∈ Icc (P.phaseLift 0) (P.phaseLift 1) := by
      rw [P.phaseLift_zero, hpositive]
      simpa [T] using hs
    obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) (1 : I)
      P.phaseLift.continuous hsrange
    refine ⟨u, finish ?_⟩
    rw [← P.phaseLift_coe u, hu]
    exact hsθ
  · have hθ : θ ∈
        ((↑) : ℝ → AddCircle T) '' Icc (-T) (-T + T) := by
      rw [AddCircle.coe_image_Icc_eq]
      exact Set.mem_univ θ
    obtain ⟨s, hs, hsθ⟩ := hθ
    have hsrange : s ∈ Icc (P.phaseLift 1) (P.phaseLift 0) := by
      rw [P.phaseLift_zero, hnegative]
      simpa [T] using hs
    obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) (0 : I)
      P.phaseLift.continuous hsrange
    refine ⟨u, finish ?_⟩
    rw [← P.phaseLift_coe u, hu]
    exact hsθ


-- @@ L90-98 verbatim
theorem range_curve
    (P : SimpleClosedOrbitParam X V) :
    Set.range P.curve = V.orbit P.p := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact P.curve_mem_orbit u
  · intro hx
    exact P.exists_curve_eq_of_mem_orbit hx


-- @@ L100-100 verbatim
end SimpleClosedOrbitParam


-- @@ L102-102 verbatim
/-! ## The flow-determined target component -/


-- @@ L104-125 verbatim
/-- The complete geometric setup together with only the quantitative safe-time
and canonical midpoint assertions.  Packing the dependent setup makes the
flow-induced constructions below stable under elaboration while adding no
mathematical assumption. -/
structure CanonicalCriticalExteriorFlowCore (n : ℕ) : Type where
  C : LevelCobordismData n
  criticalCenter : EuclideanSpace ℝ (Fin (n + 2))
  t : ℝ
  r : ℝ
  ε : ℝ
  R : CompactTimeTamedField C
    (criticalSliceExteriorCore C criticalCenter t r)
  hneg : sliceRegular C.G (t - ε)
  hpos : sliceRegular C.G (t + ε)
  Vneg : TamedField (SlabTamedField.sliceFLSAt C (t - ε) hneg)
  Vpos : TamedField (SlabTamedField.sliceFLSAt C (t + ε) hpos)
  A : Set (Set (EuclideanSpace ℝ (Fin (n + 1))))
  safe : |ε| ≤ R.safeTime
  midpoint_mem : ∀ (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I),
    R.base.flow
        ((Vneg.intrinsicSimpleClosedOrbitParam O.1).exteriorAmbientLoop q) ε ∈
      criticalSliceExteriorCore C criticalCenter t r


-- @@ L127-127 verbatim
namespace CanonicalCriticalExteriorFlowCore


-- @@ L129-129 verbatim
variable {n : ℕ} (H : CanonicalCriticalExteriorFlowCore n)


-- @@ L131-134 verbatim
def negativeParam (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt H.C (H.t - H.ε) H.hneg) H.Vneg :=
  H.Vneg.intrinsicSimpleClosedOrbitParam O.1


-- @@ L136-141 verbatim
def coreLoop (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    C(I, EuclideanSpace ℝ (Fin (n + 2))) where
  toFun q := H.R.base.flow ((H.negativeParam O).exteriorAmbientLoop q) H.ε
  continuous_toFun := H.R.base.continuous_flow_uncurry.comp
    (((H.negativeParam O).exteriorAmbientLoop.continuous).prodMk
      continuous_const)


-- @@ L143-146 verbatim
theorem coreLoop_mem (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) (q : I) :
    H.coreLoop O q ∈
      criticalSliceExteriorCore H.C H.criticalCenter H.t H.r :=
  H.midpoint_mem O q


-- @@ L148-152 verbatim
theorem coreLoop_fiber
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) (q : I) :
    H.C.G (H.coreLoop O q) = 0 :=
  (mem_criticalSliceExteriorCore H.C H.criticalCenter
    (H.coreLoop O q) H.t H.r).mp (H.coreLoop_mem O q) |>.1


-- @@ L154-158 verbatim
theorem coreLoop_time
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) (q : I) :
    tcoord (H.coreLoop O q) = H.t :=
  (mem_criticalSliceExteriorCore H.C H.criticalCenter
    (H.coreLoop O q) H.t H.r).mp (H.coreLoop_mem O q) |>.2.1


-- @@ L160-165 verbatim
def positiveCurve (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    C(I, EuclideanSpace ℝ (Fin (n + 1))) where
  toFun q := spacePart (H.R.base.flow (H.coreLoop O q) H.ε)
  continuous_toFun := continuous_spacePart.comp <|
    H.R.base.continuous_flow_uncurry.comp
      ((H.coreLoop O).continuous.prodMk continuous_const)


-- @@ L167-170 verbatim
theorem positiveEndpoint_time
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) (q : I) :
    tcoord (H.R.base.flow (H.coreLoop O q) H.ε) = H.t + H.ε := by
  rw [H.R.tcoord_flow (H.coreLoop_mem O q) H.safe, H.coreLoop_time O q]


-- @@ L172-180 verbatim
theorem positiveCurve_mem_fiber
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) (q : I) :
    H.positiveCurve O q ∈
      (SlabTamedField.sliceFLSAt H.C (H.t + H.ε) H.hpos).fiber := by
  rw [SlabTamedField.sliceFLSAt_fiber]
  change H.C.G (cobSpaceTime
    (spacePart (H.R.base.flow (H.coreLoop O q) H.ε)) (H.t + H.ε)) = 0
  rw [← H.positiveEndpoint_time O q, spaceTime_spacePart]
  exact H.R.flow_mem_fiber (H.coreLoop_fiber O q) H.ε


-- @@ L182-191 verbatim
theorem positiveCurve_closed
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    H.positiveCurve O 0 = H.positiveCurve O 1 := by
  change spacePart
      (H.R.base.flow
        (H.R.base.flow ((H.negativeParam O).exteriorAmbientLoop 0) H.ε) H.ε) =
    spacePart
      (H.R.base.flow
        (H.R.base.flow ((H.negativeParam O).exteriorAmbientLoop 1) H.ε) H.ε)
  rw [(H.negativeParam O).exteriorAmbientLoop_closed]


-- @@ L193-197 verbatim
theorem positiveCurve_mem_orbit
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) (q : I) :
    H.positiveCurve O q ∈ H.Vpos.orbit (H.positiveCurve O 0) := by
  exact H.Vpos.continuousMap_mem_orbit (H.positiveCurve O)
    (H.positiveCurve_mem_fiber O) q


-- @@ L199-224 verbatim
theorem positiveCurve_eq_cases
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) {u v : I}
    (huv : H.positiveCurve O u = H.positiveCurve O v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  have hambient :
      H.R.base.flow (H.coreLoop O u) H.ε =
        H.R.base.flow (H.coreLoop O v) H.ε := by
    calc
      H.R.base.flow (H.coreLoop O u) H.ε =
          cobSpaceTime (H.positiveCurve O u) (H.t + H.ε) := by
        rw [← H.positiveEndpoint_time O u]
        exact (spaceTime_spacePart _).symm
      _ = cobSpaceTime (H.positiveCurve O v) (H.t + H.ε) := by rw [huv]
      _ = H.R.base.flow (H.coreLoop O v) H.ε := by
        rw [← H.positiveEndpoint_time O v]
        exact spaceTime_spacePart _
  have hcore : H.coreLoop O u = H.coreLoop O v :=
    H.R.flow_apply_injective H.ε hambient
  have hnegativeAmbient :
      (H.negativeParam O).exteriorAmbientLoop u =
        (H.negativeParam O).exteriorAmbientLoop v := by
    apply H.R.flow_apply_injective H.ε
    exact hcore
  apply (H.negativeParam O).curve_eq_cases
  simpa [SimpleClosedOrbitParam.exteriorAmbientLoop] using
    congrArg spacePart hnegativeAmbient


-- @@ L226-235 verbatim
def positiveParam (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt H.C (H.t + H.ε) H.hpos) H.Vpos where
  p := H.positiveCurve O 0
  hp := H.positiveCurve_mem_fiber O 0
  curve := H.positiveCurve O
  curve_zero := rfl
  curve_closed := H.positiveCurve_closed O
  curve_mem_orbit := H.positiveCurve_mem_orbit O
  curve_eq_cases := H.positiveCurve_eq_cases O


-- @@ L237-240 verbatim
/-- The target component is forced by the second half-flow. -/
def targetOrbit (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    H.Vpos.OrbitIndex :=
  (H.positiveParam O).orbitIndex


-- @@ L242-246 verbatim
theorem targetOrbit_coe
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    (H.targetOrbit O : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
      H.Vpos.orbit (H.positiveCurve O 0) := by
  rfl


-- @@ L248-253 verbatim
theorem positive_base_mem_targetOrbit
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    H.positiveCurve O 0 ∈
      (H.targetOrbit O : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  rw [H.targetOrbit_coe O]
  exact H.Vpos.mem_orbit_self _


-- @@ L255-306 verbatim
/-- Distinct source components cannot acquire the same target component under
one fixed ambient flow.  Surjectivity is therefore the only bijectivity input
left for the flow-induced component map. -/
theorem targetOrbit_injective : Function.Injective H.targetOrbit := by
  intro O P hOP
  have hPtarget : H.positiveCurve P 0 ∈
      H.Vpos.orbit (H.positiveCurve O 0) := by
    rw [← H.targetOrbit_coe O, hOP, H.targetOrbit_coe P]
    exact H.Vpos.mem_orbit_self _
  obtain ⟨u, hu⟩ :=
    (H.positiveParam O).exists_curve_eq_of_mem_orbit hPtarget
  change H.positiveCurve O u = H.positiveCurve P 0 at hu
  have hambient :
      H.R.base.flow (H.coreLoop O u) H.ε =
        H.R.base.flow (H.coreLoop P 0) H.ε := by
    calc
      H.R.base.flow (H.coreLoop O u) H.ε =
          cobSpaceTime (H.positiveCurve O u) (H.t + H.ε) := by
        rw [← H.positiveEndpoint_time O u]
        exact (spaceTime_spacePart _).symm
      _ = cobSpaceTime (H.positiveCurve P 0) (H.t + H.ε) := by rw [hu]
      _ = H.R.base.flow (H.coreLoop P 0) H.ε := by
        rw [← H.positiveEndpoint_time P 0]
        exact spaceTime_spacePart _
  have hcore : H.coreLoop O u = H.coreLoop P 0 :=
    H.R.flow_apply_injective H.ε hambient
  have hnegativeAmbient :
      (H.negativeParam O).exteriorAmbientLoop u =
        (H.negativeParam P).exteriorAmbientLoop 0 := by
    apply H.R.flow_apply_injective H.ε
    exact hcore
  have hnegative :
      (H.negativeParam O).curve u = (H.negativeParam P).curve 0 := by
    simpa [SimpleClosedOrbitParam.exteriorAmbientLoop] using
      congrArg spacePart hnegativeAmbient
  have hmem : H.Vneg.orbitPoint P.1 ∈
      H.Vneg.orbit (H.Vneg.orbitPoint O.1) := by
    have hPzero : (H.negativeParam P).curve 0 =
        H.Vneg.orbitPoint P.1 := by
      exact H.Vneg.intrinsicOrbitCurve_zero P.1
    rw [← hPzero, ← hnegative]
    exact (H.negativeParam O).curve_mem_orbit u
  apply Subtype.ext
  apply Subtype.ext
  calc
    (O.1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
        H.Vneg.orbit (H.Vneg.orbitPoint O.1) :=
      H.Vneg.orbitPoint_orbit O.1
    _ = H.Vneg.orbit (H.Vneg.orbitPoint P.1) :=
      (H.Vneg.orbit_eq_of_mem hmem).symm
    _ = (P.1 : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
      (H.Vneg.orbitPoint_orbit P.1).symm


-- @@ L308-308 verbatim
end CanonicalCriticalExteriorFlowCore


-- @@ L310-310 verbatim
/-! ## Surjectivity-only completion of the component pairing -/


-- @@ L312-323 verbatim
/-- Membership of the forced target orbit in the requested target family and
surjectivity onto that family.  Injectivity is a theorem of the ambient flow,
not a field of this contract. -/
structure FlowInducedCanonicalCriticalExteriorPairing
    {n : ℕ} (H : CanonicalCriticalExteriorFlowCore n)
    (B : Set (Set (EuclideanSpace ℝ (Fin (n + 1))))) : Type where
  target_mem : ∀ O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A},
    H.targetOrbit O ∈ H.Vpos.selectedOrbitFinset B
  target_surjective : ∀
      Q : {Q // Q ∈ H.Vpos.selectedOrbitFinset B},
    ∃ O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A},
      H.targetOrbit O = Q.1


-- @@ L325-325 verbatim
namespace FlowInducedCanonicalCriticalExteriorPairing


-- @@ L327-327 verbatim
variable {n : ℕ} {H : CanonicalCriticalExteriorFlowCore n}

-- @@ L328-328 verbatim
variable {B : Set (Set (EuclideanSpace ℝ (Fin (n + 1))))}


-- @@ L330-334 verbatim
def targetMap
    (P : FlowInducedCanonicalCriticalExteriorPairing H B) :
    {O // O ∈ H.Vneg.selectedOrbitFinset H.A} →
      {Q // Q ∈ H.Vpos.selectedOrbitFinset B} :=
  fun O => ⟨H.targetOrbit O, P.target_mem O⟩


-- @@ L336-341 verbatim
theorem targetMap_injective
    (P : FlowInducedCanonicalCriticalExteriorPairing H B) :
    Function.Injective P.targetMap := by
  intro O Q hOQ
  apply H.targetOrbit_injective
  exact congrArg Subtype.val hOQ


-- @@ L343-350 verbatim
theorem targetMap_surjective
    (P : FlowInducedCanonicalCriticalExteriorPairing H B) :
    Function.Surjective P.targetMap := by
  intro Q
  obtain ⟨O, hO⟩ := P.target_surjective Q
  refine ⟨O, ?_⟩
  apply Subtype.ext
  exact hO


-- @@ L352-358 verbatim
/-- The component equivalence is constructed from the forced flow map. -/
def orbitEquiv
    (P : FlowInducedCanonicalCriticalExteriorPairing H B) :
    {O // O ∈ H.Vneg.selectedOrbitFinset H.A} ≃
      {Q // Q ∈ H.Vpos.selectedOrbitFinset B} :=
  Equiv.ofBijective P.targetMap
    ⟨P.targetMap_injective, P.targetMap_surjective⟩


-- @@ L360-363 verbatim
@[simp] theorem orbitEquiv_val
    (P : FlowInducedCanonicalCriticalExteriorPairing H B)
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A}) :
    (P.orbitEquiv O).1 = H.targetOrbit O := rfl


-- @@ L365-380 verbatim
/-- The reduced data supplies the former canonical pairing.  In particular,
`positive_base_mem` is now a theorem rather than an input field. -/
def toCanonicalCriticalExteriorFlowPairing
    (P : FlowInducedCanonicalCriticalExteriorPairing H B) :
    CanonicalCriticalExteriorFlowPairing
      H.C H.criticalCenter H.t H.r H.ε H.R
      H.hneg H.hpos H.Vneg H.Vpos H.A B where
  safe := H.safe
  orbitEquiv := P.orbitEquiv
  midpoint_mem := H.midpoint_mem
  positive_base_mem := by
    intro O
    change H.positiveCurve O 0 ∈
      ((P.orbitEquiv O).1 : Set (EuclideanSpace ℝ (Fin (n + 1))))
    rw [P.orbitEquiv_val O]
    exact H.positive_base_mem_targetOrbit O


-- @@ L382-382 verbatim
end FlowInducedCanonicalCriticalExteriorPairing


-- @@ L384-384 verbatim
/-! ## Production minimum and maximum callbacks -/


-- @@ L386-386 verbatim
variable {a : ℕ}

-- @@ L387-387 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L388-388 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L389-389 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L391-391 verbatim
local notation "Eₐ" => EuclideanSpace ℝ (Fin (a + 3))


-- @@ L393-393 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L395-400 verbatim
abbrev chronologicalMinimumExteriorSourceFamily
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : Set (Set Eₐ) :=
  (D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
      (D.chronologicalBeforeField t ht)


-- @@ L402-412 verbatim
abbrev chronologicalMinimumExteriorTargetFamily
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) : Set (Set Eₐ) :=
  ((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
      (D.chronologicalMinimumLocalField t ht)) \
    {(((D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 :
      (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set Eₐ)}


-- @@ L414-424 verbatim
abbrev chronologicalMaximumExteriorSourceFamily
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) : Set (Set Eₐ) :=
  ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
      (D.chronologicalMaximumLocalField t ht)) \
    {(((D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 :
      (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set Eₐ)}


-- @@ L426-431 verbatim
abbrev chronologicalMaximumExteriorTargetFamily
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : Set (Set Eₐ) :=
  (D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
      (D.chronologicalAfterField t ht)


-- @@ L433-437 verbatim
abbrev ChronologicalExteriorSafe
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : Prop :=
  |D.chronologicalWindowRadius t ht ^ 2| ≤
    (D.chronologicalCriticalExteriorTimeField t ht).safeTime


-- @@ L439-452 verbatim
abbrev ChronologicalMinimumExteriorMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : Prop :=
  ∀ (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)}) (q : I),
    (D.chronologicalCriticalExteriorTimeField t ht).base.flow
        ((D.chronologicalBeforeField t ht).intrinsicSimpleClosedOrbitParam O.1
          |>.exteriorAmbientLoop q)
        (D.chronologicalWindowRadius t ht ^ 2) ∈
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        (D.position.eventModel t ht).fiberCoverRadius


-- @@ L454-470 verbatim
abbrev ChronologicalMaximumExteriorMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) : Prop :=
  ∀ (O : {O // O ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex)}) (q : I),
    (D.chronologicalCriticalExteriorTimeField t ht).base.flow
        ((D.chronologicalMaximumLocalField t ht).intrinsicSimpleClosedOrbitParam O.1
          |>.exteriorAmbientLoop q)
        (D.chronologicalWindowRadius t ht ^ 2) ∈
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        (D.position.eventModel t ht).fiberCoverRadius


-- @@ L472-490 verbatim
def chronologicalMinimumExteriorFlowCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hsafe : D.ChronologicalExteriorSafe t ht)
    (hmidpoint : D.ChronologicalMinimumExteriorMidpointCapture t ht) :
    CanonicalCriticalExteriorFlowCore (a + 2) where
  C := D.signedOutput.cobordism.toLevelCobordismData
  criticalCenter := D.position.eventCenter t ht
  t := tcoord (D.position.eventCenter t ht)
  r := (D.position.eventModel t ht).fiberCoverRadius
  ε := D.chronologicalWindowRadius t ht ^ 2
  R := D.chronologicalCriticalExteriorTimeField t ht
  hneg := D.chronologicalBeforeTime_regular t ht
  hpos := D.chronologicalAfterTime_regular t ht
  Vneg := D.chronologicalBeforeField t ht
  Vpos := D.chronologicalMinimumLocalField t ht
  A := D.chronologicalMinimumExteriorSourceFamily t ht
  safe := hsafe
  midpoint_mem := hmidpoint


-- @@ L492-514 verbatim
def chronologicalMaximumExteriorFlowCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hsafe : D.ChronologicalExteriorSafe t ht)
    (hmidpoint : D.ChronologicalMaximumExteriorMidpointCapture
      t ht hpositive hindex) :
    CanonicalCriticalExteriorFlowCore (a + 2) where
  C := D.signedOutput.cobordism.toLevelCobordismData
  criticalCenter := D.position.eventCenter t ht
  t := tcoord (D.position.eventCenter t ht)
  r := (D.position.eventModel t ht).fiberCoverRadius
  ε := D.chronologicalWindowRadius t ht ^ 2
  R := D.chronologicalCriticalExteriorTimeField t ht
  hneg := D.chronologicalBeforeTime_regular t ht
  hpos := D.chronologicalAfterTime_regular t ht
  Vneg := D.chronologicalMaximumLocalField t ht
  Vpos := D.chronologicalAfterField t ht
  A := D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex
  safe := hsafe
  midpoint_mem := hmidpoint


-- @@ L516-518 verbatim
/-! The compact critical-slice cylinder lies in the zero fiber of the signed
cobordism.  Hence its two boundary loops have the same sign.  This makes
membership of the forced target in the positive collection automatic. -/


-- @@ L520-603 verbatim
theorem chronologicalMinimumTargetOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hsafe : D.ChronologicalExteriorSafe t ht)
    (hmidpoint : D.ChronologicalMinimumExteriorMidpointCapture t ht)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)}) :
    let H := D.chronologicalMinimumExteriorFlowCore t ht hsafe hmidpoint
    H.targetOrbit O ∈
      (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
        ((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
          (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
            (D.chronologicalMinimumLocalField t ht)) := by
  let H := D.chronologicalMinimumExteriorFlowCore t ht hsafe hmidpoint
  let Sneg := D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)
  let Spos := D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)
  let O' : {Q // Q ∈ H.Vneg.selectedOrbitFinset H.A} :=
    ⟨O.1, by
      change O.1 ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalMinimumExteriorSourceFamily t ht)
      exact O.2⟩
  change H.targetOrbit O' ∈ H.Vpos.selectedOrbitFinset
    (Spos.positiveOrbitCollection H.Vpos)
  let p := (H.negativeParam O').exteriorAmbientLoop 0
  have hsourceCollection : (O'.1 : Set Eₐ) ∈
      Sneg.positiveOrbitCollection H.Vneg :=
    (H.Vneg.mem_selectedOrbitFinset O'.1).mp O'.2
  have hsourceSign : 0 < Sneg (H.Vneg.orbitPoint O'.1) :=
    (Sneg.mem_positiveOrbitCollection_iff H.Vneg O'.1).mp hsourceCollection
  have hpEq : p = cobSpaceTime (H.Vneg.orbitPoint O'.1)
      (D.chronologicalBeforeTime t ht) := by
    change cobSpaceTime ((H.negativeParam O').curve 0) (H.t - H.ε) = _
    apply congrArg₂ cobSpaceTime
    · exact H.Vneg.intrinsicOrbitCurve_zero O'.1
    · rfl
  have hstartSign : 0 < D.signedOutput p := by
    rw [hpEq]
    exact hsourceSign
  let γ : C(I, EuclideanSpace ℝ (Fin (a + 4))) :=
    ⟨fun u => H.R.base.flow p ((u : ℝ) * (2 * H.ε)),
      (H.R.base.continuous_flow p).comp
        (continuous_subtype_val.mul continuous_const)⟩
  have hpFiber : H.C.G p = 0 :=
    (H.negativeParam O').exteriorAmbientLoop_fiber 0
  have hγFiber : ∀ u, D.signedOutput.cobordism.G (γ u) = 0 := by
    intro u
    exact H.R.flow_mem_fiber hpFiber _
  have hthrough : 0 < D.signedOutput (γ 1) :=
    (D.signedOutput.pos_iff_of_zeroFiber_path γ hγFiber).mp
      (by simpa [γ] using hstartSign)
  have hdouble : H.R.base.flow p (2 * H.ε) =
      H.R.base.flow (H.R.base.flow p H.ε) H.ε := by
    simpa [two_mul] using
      (congrFun (H.R.base.flow_shift p H.ε) H.ε).symm
  have hendSign : 0 < D.signedOutput
      (H.R.base.flow (H.coreLoop O' 0) H.ε) := by
    change 0 < D.signedOutput
      (H.R.base.flow (H.R.base.flow p H.ε) H.ε)
    rw [← hdouble]
    simpa [γ] using hthrough
  have hendEq : cobSpaceTime (H.positiveCurve O' 0)
      (D.chronologicalAfterTime t ht) =
      H.R.base.flow (H.coreLoop O' 0) H.ε := by
    rw [show D.chronologicalAfterTime t ht = H.t + H.ε by rfl]
    rw [← H.positiveEndpoint_time O' 0]
    change cobSpaceTime
      (spacePart (H.R.base.flow (H.coreLoop O' 0) H.ε))
      (tcoord (H.R.base.flow (H.coreLoop O' 0) H.ε)) = _
    exact spaceTime_spacePart _
  have hbaseSign : 0 < Spos (H.positiveCurve O' 0) := by
    change 0 < D.signedOutput (cobSpaceTime (H.positiveCurve O' 0)
      (D.chronologicalAfterTime t ht))
    rw [hendEq]
    exact hendSign
  apply (H.Vpos.mem_selectedOrbitFinset (H.targetOrbit O')).mpr
  rw [Spos.mem_positiveOrbitCollection_iff]
  have htargetPoint : H.Vpos.orbitPoint (H.targetOrbit O') ∈
      H.Vpos.orbit (H.positiveCurve O' 0) := by
    rw [← H.targetOrbit_coe O', H.Vpos.orbitPoint_orbit]
    exact H.Vpos.mem_orbit_self _
  exact (Spos.pos_iff_of_mem_orbit H.Vpos
    (H.positiveCurve_mem_fiber O' 0) htargetPoint).mp hbaseSign


-- @@ L605-694 verbatim
theorem chronologicalMaximumTargetOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hsafe : D.ChronologicalExteriorSafe t ht)
    (hmidpoint : D.ChronologicalMaximumExteriorMidpointCapture
      t ht hpositive hindex)
    (O : {O // O ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex)}) :
    let H := D.chronologicalMaximumExteriorFlowCore
      t ht hpositive hindex hsafe hmidpoint
    H.targetOrbit O ∈
      (D.chronologicalAfterField t ht).selectedOrbitFinset
        ((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
          (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
            (D.chronologicalAfterField t ht)) := by
  let H := D.chronologicalMaximumExteriorFlowCore
    t ht hpositive hindex hsafe hmidpoint
  let Sneg := D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)
  let Spos := D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)
  let O' : {Q // Q ∈ H.Vneg.selectedOrbitFinset H.A} :=
    ⟨O.1, by
      change O.1 ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
        (D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex)
      exact O.2⟩
  change H.targetOrbit O' ∈ H.Vpos.selectedOrbitFinset
    (Spos.positiveOrbitCollection H.Vpos)
  let p := (H.negativeParam O').exteriorAmbientLoop 0
  have hsourceCollection : (O'.1 : Set Eₐ) ∈
      Sneg.positiveOrbitCollection H.Vneg :=
    ((H.Vneg.mem_selectedOrbitFinset O'.1).mp O'.2).1
  have hsourceSign : 0 < Sneg (H.Vneg.orbitPoint O'.1) :=
    (Sneg.mem_positiveOrbitCollection_iff H.Vneg O'.1).mp hsourceCollection
  have hpEq : p = cobSpaceTime (H.Vneg.orbitPoint O'.1)
      (D.chronologicalBeforeTime t ht) := by
    change cobSpaceTime ((H.negativeParam O').curve 0) (H.t - H.ε) = _
    apply congrArg₂ cobSpaceTime
    · exact H.Vneg.intrinsicOrbitCurve_zero O'.1
    · rfl
  have hstartSign : 0 < D.signedOutput p := by
    rw [hpEq]
    exact hsourceSign
  let γ : C(I, EuclideanSpace ℝ (Fin (a + 4))) :=
    ⟨fun u => H.R.base.flow p ((u : ℝ) * (2 * H.ε)),
      (H.R.base.continuous_flow p).comp
        (continuous_subtype_val.mul continuous_const)⟩
  have hpFiber : H.C.G p = 0 :=
    (H.negativeParam O').exteriorAmbientLoop_fiber 0
  have hγFiber : ∀ u, D.signedOutput.cobordism.G (γ u) = 0 := by
    intro u
    exact H.R.flow_mem_fiber hpFiber _
  have hthrough : 0 < D.signedOutput (γ 1) :=
    (D.signedOutput.pos_iff_of_zeroFiber_path γ hγFiber).mp
      (by simpa [γ] using hstartSign)
  have hdouble : H.R.base.flow p (2 * H.ε) =
      H.R.base.flow (H.R.base.flow p H.ε) H.ε := by
    simpa [two_mul] using
      (congrFun (H.R.base.flow_shift p H.ε) H.ε).symm
  have hendSign : 0 < D.signedOutput
      (H.R.base.flow (H.coreLoop O' 0) H.ε) := by
    change 0 < D.signedOutput
      (H.R.base.flow (H.R.base.flow p H.ε) H.ε)
    rw [← hdouble]
    simpa [γ] using hthrough
  have hendEq : cobSpaceTime (H.positiveCurve O' 0)
      (D.chronologicalAfterTime t ht) =
      H.R.base.flow (H.coreLoop O' 0) H.ε := by
    rw [show D.chronologicalAfterTime t ht = H.t + H.ε by rfl]
    rw [← H.positiveEndpoint_time O' 0]
    change cobSpaceTime
      (spacePart (H.R.base.flow (H.coreLoop O' 0) H.ε))
      (tcoord (H.R.base.flow (H.coreLoop O' 0) H.ε)) = _
    exact spaceTime_spacePart _
  have hbaseSign : 0 < Spos (H.positiveCurve O' 0) := by
    change 0 < D.signedOutput (cobSpaceTime (H.positiveCurve O' 0)
      (D.chronologicalAfterTime t ht))
    rw [hendEq]
    exact hendSign
  apply (H.Vpos.mem_selectedOrbitFinset (H.targetOrbit O')).mpr
  rw [Spos.mem_positiveOrbitCollection_iff]
  have htargetPoint : H.Vpos.orbitPoint (H.targetOrbit O') ∈
      H.Vpos.orbit (H.positiveCurve O' 0) := by
    rw [← H.targetOrbit_coe O', H.Vpos.orbitPoint_orbit]
    exact H.Vpos.mem_orbit_self _
  exact (Spos.pos_iff_of_mem_orbit H.Vpos
    (H.positiveCurve_mem_fiber O' 0) htargetPoint).mp hbaseSign


-- @@ L696-702 verbatim
/-! ## Exact residual production contracts

Positivity of every forced target was proved above.  At a minimum the only
remaining membership condition is that an exterior source does not flow to
the newly born local circle.  At a maximum there is no remaining target
membership condition at all.  In both cases surjectivity of the forced map is
the only cardinality/exhaustion assertion. -/


-- @@ L704-725 verbatim
structure ChronologicalMinimumTargetCompletion
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hsafe : D.ChronologicalExteriorSafe t ht)
    (hmidpoint : D.ChronologicalMinimumExteriorMidpointCapture t ht) : Type where
  target_ne_local : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalMinimumExteriorSourceFamily t ht)},
    (((D.chronologicalMinimumExteriorFlowCore t ht hsafe hmidpoint).targetOrbit O :
        (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set Eₐ) ≠
      (((D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set Eₐ)
  target_surjective : ∀
      Q : {Q // Q ∈ (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
        (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)},
    ∃ O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalMinimumExteriorSourceFamily t ht)},
      (D.chronologicalMinimumExteriorFlowCore t ht hsafe hmidpoint).targetOrbit O =
        Q.1


-- @@ L727-742 verbatim
structure ChronologicalMaximumTargetCompletion
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hsafe : D.ChronologicalExteriorSafe t ht)
    (hmidpoint : D.ChronologicalMaximumExteriorMidpointCapture
      t ht hpositive hindex) : Type where
  target_surjective : ∀
      Q : {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
        (D.chronologicalMaximumExteriorTargetFamily t ht)},
    ∃ O : {O // O ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
        (D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex)},
      (D.chronologicalMaximumExteriorFlowCore
        t ht hpositive hindex hsafe hmidpoint).targetOrbit O = Q.1


-- @@ L744-768 verbatim
def minimumFlowInducedPairing_of_targetCompletion
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hsafe : D.ChronologicalExteriorSafe t ht)
    (hmidpoint : D.ChronologicalMinimumExteriorMidpointCapture t ht)
    (P : D.ChronologicalMinimumTargetCompletion
      t ht hpositive hindex hsafe hmidpoint) :
    FlowInducedCanonicalCriticalExteriorPairing
      (D.chronologicalMinimumExteriorFlowCore t ht hsafe hmidpoint)
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex) where
  target_mem O := by
    apply ((D.chronologicalMinimumLocalField t ht).mem_selectedOrbitFinset
      ((D.chronologicalMinimumExteriorFlowCore
        t ht hsafe hmidpoint).targetOrbit O)).mpr
    constructor
    · exact ((D.chronologicalMinimumLocalField t ht).mem_selectedOrbitFinset
        ((D.chronologicalMinimumExteriorFlowCore
          t ht hsafe hmidpoint).targetOrbit O)).mp
          (D.chronologicalMinimumTargetOrbit_mem_positive
            t ht hsafe hmidpoint O)
    · simpa using P.target_ne_local O
  target_surjective := P.target_surjective


-- @@ L770-787 verbatim
def maximumFlowInducedPairing_of_targetCompletion
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hsafe : D.ChronologicalExteriorSafe t ht)
    (hmidpoint : D.ChronologicalMaximumExteriorMidpointCapture
      t ht hpositive hindex)
    (P : D.ChronologicalMaximumTargetCompletion
      t ht hpositive hindex hsafe hmidpoint) :
    FlowInducedCanonicalCriticalExteriorPairing
      (D.chronologicalMaximumExteriorFlowCore
        t ht hpositive hindex hsafe hmidpoint)
      (D.chronologicalMaximumExteriorTargetFamily t ht) where
  target_mem O := D.chronologicalMaximumTargetOrbit_mem_positive
    t ht hpositive hindex hsafe hmidpoint O
  target_surjective := P.target_surjective


-- @@ L789-801 verbatim
/-- Minimum data with no arbitrary orbit equivalence: after safe time and
midpoint capture, only noncollision with the born circle and surjectivity of
the forced target map remain. -/
abbrev ChronologicalMinimumFlowInducedPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :=
  Σ' hsafe : D.ChronologicalExteriorSafe t ht,
    Σ' hmidpoint : D.ChronologicalMinimumExteriorMidpointCapture t ht,
      D.ChronologicalMinimumTargetCompletion
        t ht hpositive hindex hsafe hmidpoint


-- @@ L803-814 verbatim
/-- Maximum analogue: the final contract contains only surjectivity. -/
abbrev ChronologicalMaximumFlowInducedPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :=
  Σ' hsafe : D.ChronologicalExteriorSafe t ht,
    Σ' hmidpoint : D.ChronologicalMaximumExteriorMidpointCapture
        t ht hpositive hindex,
      D.ChronologicalMaximumTargetCompletion
        t ht hpositive hindex hsafe hmidpoint


-- @@ L816-827 verbatim
def minimumExteriorCanonicalPairing_of_flowInduced
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (P : D.ChronologicalMinimumFlowInducedPairing
      t ht hpositive hindex) :
    D.ChronologicalMinimumExteriorCanonicalPairing
      t ht hpositive hindex :=
  (D.minimumFlowInducedPairing_of_targetCompletion
    t ht hpositive hindex P.1 P.2.1 P.2.2).toCanonicalCriticalExteriorFlowPairing


-- @@ L829-840 verbatim
def maximumExteriorCanonicalPairing_of_flowInduced
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (P : D.ChronologicalMaximumFlowInducedPairing
      t ht hpositive hindex) :
    D.ChronologicalMaximumExteriorCanonicalPairing
      t ht hpositive hindex :=
  (D.maximumFlowInducedPairing_of_targetCompletion
    t ht hpositive hindex P.1 P.2.1 P.2.2).toCanonicalCriticalExteriorFlowPairing


-- @@ L842-855 verbatim
/-- Complete production minimum ledger callback from the flow-induced
surjectivity contract. -/
def minimumPositiveLedgerMove_of_flowInducedPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (P : D.ChronologicalMinimumFlowInducedPairing
      t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  D.minimumPositiveLedgerMove_of_canonicalPairing t ht hpositive hindex
    (D.minimumExteriorCanonicalPairing_of_flowInduced
      t ht hpositive hindex P)


-- @@ L857-869 verbatim
/-- Complete production maximum ledger callback from the same reduced data. -/
def maximumPositiveLedgerMove_of_flowInducedPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (P : D.ChronologicalMaximumFlowInducedPairing
      t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  D.maximumPositiveLedgerMove_of_canonicalPairing t ht hpositive hindex
    (D.maximumExteriorCanonicalPairing_of_flowInduced
      t ht hpositive hindex P)


-- @@ L871-871 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L873-873 verbatim
end Submission
