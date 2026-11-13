import Submission.ProductionMorseDefiniteReverseBalanceAudit


-- @@ L3-10 verbatim
/-!
# Explicit transports for reverse definite flow

The canonical critical exterior core indexes its endpoint fields by `t - ε`
and `t + ε`. With a negative step these are the chronological after- and
before-slices, respectively, but only propositionally. This file makes the
resulting transports explicit before constructing any reverse orbit map.
-/


-- @@ L12-12 verbatim
set_option autoImplicit false

-- @@ L13-13 verbatim
set_option maxHeartbeats 2400000


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
namespace SlabTamedField


-- @@ L24-24 verbatim
variable {n : ℕ}


-- @@ L26-34 verbatim
/-- `sliceFLSAt` respects equality of slice times; the regularity proofs are
irrelevant proof data. -/
theorem sliceFLSAt_eq_of_time_eq
    (C : LevelCobordismData n) {s u : ℝ}
    (hs : sliceRegular C.G s) (hu : sliceRegular C.G u)
    (h : s = u) :
    sliceFLSAt C s hs = sliceFLSAt C u hu := by
  subst u
  rfl


-- @@ L36-36 verbatim
end SlabTamedField


-- @@ L38-38 verbatim
namespace TamedField


-- @@ L40-40 verbatim
variable {n : ℕ}

-- @@ L41-41 verbatim
variable {X Y : FramedLevelSet n}


-- @@ L43-43 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L45-47 verbatim
/-- Transport a tamed field along equality of its framed level set. -/
def transport (V : TamedField X) (h : X = Y) : TamedField Y :=
  h ▸ V


-- @@ L49-55 verbatim
/-- Transport of the finite selected-orbit subtype. -/
def selectedOrbitTransportEquiv
    (V : TamedField X) (h : X = Y) (A : Set (Set E)) :
    {O // O ∈ V.selectedOrbitFinset A} ≃
      {O // O ∈ (V.transport h).selectedOrbitFinset A} := by
  cases h
  exact Equiv.refl _


-- @@ L57-62 verbatim
/-- Transport of a single orbit index. -/
def orbitIndexTransportEquiv
    (V : TamedField X) (h : X = Y) :
    V.OrbitIndex ≃ (V.transport h).OrbitIndex := by
  cases h
  exact Equiv.refl _


-- @@ L64-69 verbatim
@[simp] theorem selectedOrbitTransportEquiv_val_val
    (V : TamedField X) (h : X = Y) (A : Set (Set E))
    (O : {O // O ∈ V.selectedOrbitFinset A}) :
    ((V.selectedOrbitTransportEquiv h A O).1.1 : Set E) = O.1.1 := by
  cases h
  rfl


-- @@ L71-76 verbatim
@[simp] theorem orbitIndexTransportEquiv_val
    (V : TamedField X) (h : X = Y) (O : V.OrbitIndex) :
    ((V.orbitIndexTransportEquiv h O :
      (V.transport h).OrbitIndex) : Set E) = (O : Set E) := by
  cases h
  rfl


-- @@ L78-83 verbatim
@[simp] theorem selectedOrbitTransportEquiv_symm_val_val
    (V : TamedField X) (h : X = Y) (A : Set (Set E))
    (O : {O // O ∈ (V.transport h).selectedOrbitFinset A}) :
    (((V.selectedOrbitTransportEquiv h A).symm O).1.1 : Set E) = O.1.1 := by
  cases h
  rfl


-- @@ L85-91 verbatim
@[simp] theorem orbitIndexTransportEquiv_symm_val
    (V : TamedField X) (h : X = Y)
    (O : (V.transport h).OrbitIndex) :
    (((V.orbitIndexTransportEquiv h).symm O : V.OrbitIndex) : Set E) =
      (O : Set E) := by
  cases h
  rfl


-- @@ L93-97 verbatim
theorem transport_orbit
    (V : TamedField X) (h : X = Y) (x : E) :
    (V.transport h).orbit x = V.orbit x := by
  cases h
  rfl


-- @@ L99-108 verbatim
/-- The intrinsic orbit curve is unchanged after transporting the framed
level-set index. -/
theorem transportedIntrinsicCurve_symm
    (V : TamedField X) (h : X = Y) (A : Set (Set E))
    (O : {O // O ∈ (V.transport h).selectedOrbitFinset A}) (q : I) :
    ((V.transport h).intrinsicSimpleClosedOrbitParam O.1).curve q =
      (V.intrinsicSimpleClosedOrbitParam
        ((V.selectedOrbitTransportEquiv h A).symm O).1).curve q := by
  cases h
  rfl


-- @@ L110-110 verbatim
end TamedField


-- @@ L112-112 verbatim
variable {a : ℕ}

-- @@ L113-113 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L114-114 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L115-115 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L117-117 verbatim
local notation "Eₐ" => EuclideanSpace ℝ (Fin (a + 3))


-- @@ L119-119 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L121-129 verbatim
/-- Regularity at the source endpoint of a negative chronological half-flow. -/
theorem chronologicalReverseAfter_regular
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    sliceRegular D.signedOutput.cobordism.G
      (tcoord (D.position.eventCenter t ht) -
        -(D.chronologicalWindowRadius t ht ^ 2)) := by
  simpa only [sub_neg_eq_add, chronologicalAfterTime] using
    D.chronologicalAfterTime_regular t ht


-- @@ L131-139 verbatim
/-- Regularity at the target endpoint of a negative chronological half-flow. -/
theorem chronologicalReverseBefore_regular
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    sliceRegular D.signedOutput.cobordism.G
      (tcoord (D.position.eventCenter t ht) +
        -(D.chronologicalWindowRadius t ht ^ 2)) := by
  simpa only [sub_eq_add_neg, chronologicalBeforeTime] using
    D.chronologicalBeforeTime_regular t ht


-- @@ L141-154 verbatim
/-- The chronological after-slice is the source slice computed by a negative
canonical half-step. -/
theorem chronologicalAfterSlice_eq_reverseAfterSlice
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalAfterSlice t ht =
      SlabTamedField.sliceFLSAt
        D.signedOutput.cobordism.toLevelCobordismData
        (tcoord (D.position.eventCenter t ht) -
          -(D.chronologicalWindowRadius t ht ^ 2))
        (D.chronologicalReverseAfter_regular t ht) := by
  unfold chronologicalAfterSlice
  apply SlabTamedField.sliceFLSAt_eq_of_time_eq
  simp only [chronologicalAfterTime, sub_neg_eq_add]


-- @@ L156-169 verbatim
/-- The chronological before-slice is the target slice computed by a negative
canonical half-step. -/
theorem chronologicalBeforeSlice_eq_reverseBeforeSlice
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalBeforeSlice t ht =
      SlabTamedField.sliceFLSAt
        D.signedOutput.cobordism.toLevelCobordismData
        (tcoord (D.position.eventCenter t ht) +
          -(D.chronologicalWindowRadius t ht ^ 2))
        (D.chronologicalReverseBefore_regular t ht) := by
  unfold chronologicalBeforeSlice
  apply SlabTamedField.sliceFLSAt_eq_of_time_eq
  simp only [chronologicalBeforeTime, sub_eq_add_neg]


-- @@ L171-177 verbatim
theorem chronologicalReverseAfterTime_eq
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    tcoord (D.position.eventCenter t ht) -
        -(D.chronologicalWindowRadius t ht ^ 2) =
      D.chronologicalAfterTime t ht := by
  simp only [chronologicalAfterTime, sub_neg_eq_add]


-- @@ L179-185 verbatim
theorem chronologicalReverseBeforeTime_eq
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    tcoord (D.position.eventCenter t ht) +
        -(D.chronologicalWindowRadius t ht ^ 2) =
      D.chronologicalBeforeTime t ht := by
  simp only [chronologicalBeforeTime, sub_eq_add_neg]


-- @@ L187-198 verbatim
/-- Transported minimum source field on the endpoint expected by the generic
negative-step core. -/
def chronologicalMinimumReverseSourceField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    TamedField (SlabTamedField.sliceFLSAt
      D.signedOutput.cobordism.toLevelCobordismData
      (tcoord (D.position.eventCenter t ht) -
        -(D.chronologicalWindowRadius t ht ^ 2))
      (D.chronologicalReverseAfter_regular t ht)) :=
  (D.chronologicalMinimumLocalField t ht).transport
    (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)


-- @@ L200-211 verbatim
/-- Transported maximum source field on the endpoint expected by the generic
negative-step core. -/
def chronologicalMaximumReverseSourceField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    TamedField (SlabTamedField.sliceFLSAt
      D.signedOutput.cobordism.toLevelCobordismData
      (tcoord (D.position.eventCenter t ht) -
        -(D.chronologicalWindowRadius t ht ^ 2))
      (D.chronologicalReverseAfter_regular t ht)) :=
  (D.chronologicalAfterField t ht).transport
    (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)


-- @@ L213-224 verbatim
/-- Transported minimum target field on the endpoint expected by the generic
negative-step core. -/
def chronologicalMinimumReverseTargetField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    TamedField (SlabTamedField.sliceFLSAt
      D.signedOutput.cobordism.toLevelCobordismData
      (tcoord (D.position.eventCenter t ht) +
        -(D.chronologicalWindowRadius t ht ^ 2))
      (D.chronologicalReverseBefore_regular t ht)) :=
  (D.chronologicalBeforeField t ht).transport
    (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)


-- @@ L226-237 verbatim
/-- Transported maximum target field on the endpoint expected by the generic
negative-step core. -/
def chronologicalMaximumReverseTargetField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    TamedField (SlabTamedField.sliceFLSAt
      D.signedOutput.cobordism.toLevelCobordismData
      (tcoord (D.position.eventCenter t ht) +
        -(D.chronologicalWindowRadius t ht ^ 2))
      (D.chronologicalReverseBefore_regular t ht)) :=
  (D.chronologicalMaximumLocalField t ht).transport
    (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)


-- @@ L239-251 verbatim
def chronologicalMinimumReverseSourceEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    {O // O ∈ (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)} ≃
    {O // O ∈ (D.chronologicalMinimumReverseSourceField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)} :=
  (D.chronologicalMinimumLocalField t ht).selectedOrbitTransportEquiv
    (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
    (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)


-- @@ L253-262 verbatim
def chronologicalMaximumReverseSourceEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)} ≃
    {O // O ∈ (D.chronologicalMaximumReverseSourceField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)} :=
  (D.chronologicalAfterField t ht).selectedOrbitTransportEquiv
    (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
    (D.chronologicalMaximumExteriorTargetFamily t ht)


-- @@ L264-270 verbatim
def chronologicalMinimumReverseTargetOrbitEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    (D.chronologicalBeforeField t ht).OrbitIndex ≃
      (D.chronologicalMinimumReverseTargetField t ht).OrbitIndex :=
  (D.chronologicalBeforeField t ht).orbitIndexTransportEquiv
    (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)


-- @@ L272-278 verbatim
def chronologicalMaximumReverseTargetOrbitEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    (D.chronologicalMaximumLocalField t ht).OrbitIndex ≃
      (D.chronologicalMaximumReverseTargetField t ht).OrbitIndex :=
  (D.chronologicalMaximumLocalField t ht).orbitIndexTransportEquiv
    (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)


-- @@ L280-280 verbatim
/-! ## Transported reverse cores -/


-- @@ L282-349 verbatim
def chronologicalMinimumReverseExteriorFlowCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    CanonicalCriticalExteriorFlowCore (a + 2) where
  C := D.signedOutput.cobordism.toLevelCobordismData
  criticalCenter := D.position.eventCenter t ht
  t := tcoord (D.position.eventCenter t ht)
  r := (D.position.eventModel t ht).fiberCoverRadius
  ε := -(D.chronologicalWindowRadius t ht ^ 2)
  R := D.chronologicalCriticalExteriorTimeField t ht
  hneg := D.chronologicalReverseAfter_regular t ht
  hpos := D.chronologicalReverseBefore_regular t ht
  Vneg := D.chronologicalMinimumReverseSourceField t ht
  Vpos := D.chronologicalMinimumReverseTargetField t ht
  A := D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex
  safe := by
    simpa [chronologicalCriticalExteriorTimeField] using
      D.chronologicalWindowRadius_sq_reverse_safe t ht
  midpoint_mem := by
    intro O q
    let e := D.chronologicalMinimumReverseSourceEquiv
      t ht hpositive hindex
    let O₀ := e.symm O
    let P := (D.chronologicalMinimumLocalField t ht).intrinsicSimpleClosedOrbitParam O₀.1
    have hPext : (O₀.1 : Set Eₐ) ∈
        D.chronologicalExteriorOrbitCollection t ht
          (D.chronologicalAfterTime t ht) := by
      apply D.chronologicalMinimumAfterOrbit_mem_exterior_of_ne_local
        t ht hpositive hindex O₀.1
      exact ((D.chronologicalMinimumLocalField t ht).mem_selectedOrbitFinset O₀.1).mp O₀.2 |>.2
    have hcurveOrbit : P.curve q ∈ (O₀.1 : Set Eₐ) := by
      rw [(D.chronologicalMinimumLocalField t ht).orbitPoint_orbit O₀.1]
      exact P.curve_mem_orbit q
    have hp : P.exteriorAmbientLoop q ∈
        D.chronologicalExteriorSlabCore t ht := by
      exact D.chronologicalOrbitPoint_mem_exteriorSlabCore
        t ht (D.chronologicalAfterTime t ht)
        ⟨(D.chronologicalAfterTime_mem_bracket t ht).1.le,
          (D.chronologicalAfterTime_mem_bracket t ht).2.le⟩
        (D.chronologicalAfterTime_regular t ht)
        (D.chronologicalMinimumLocalField t ht) O₀.1
        hcurveOrbit hPext
    have hshift : tcoord (P.exteriorAmbientLoop q) +
        -(D.chronologicalWindowRadius t ht ^ 2) =
        tcoord (D.position.eventCenter t ht) := by
      simp [P, SimpleClosedOrbitParam.exteriorAmbientLoop,
        chronologicalAfterTime]
    have hloop :
        ((D.chronologicalMinimumReverseSourceField t ht).intrinsicSimpleClosedOrbitParam O.1).exteriorAmbientLoop q =
          P.exteriorAmbientLoop q := by
      change cobSpaceTime
          ((D.chronologicalMinimumReverseSourceField t ht).intrinsicSimpleClosedOrbitParam O.1 |>.curve q)
          (tcoord (D.position.eventCenter t ht) -
            -(D.chronologicalWindowRadius t ht ^ 2)) =
        cobSpaceTime (P.curve q) (D.chronologicalAfterTime t ht)
      apply congrArg₂ cobSpaceTime
      · exact (D.chronologicalMinimumLocalField t ht).transportedIntrinsicCurve_symm
          (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
          (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)
          O q
      · exact D.chronologicalReverseAfterTime_eq t ht
    rw [hloop]
    simpa [chronologicalCriticalExteriorTimeField] using
      D.chronologicalDefiniteExteriorShift_mem t ht (Or.inl hindex)
        hp (D.chronologicalWindowRadius_sq_reverse_safe t ht) hshift


-- @@ L351-411 verbatim
def chronologicalMaximumReverseExteriorFlowCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    CanonicalCriticalExteriorFlowCore (a + 2) where
  C := D.signedOutput.cobordism.toLevelCobordismData
  criticalCenter := D.position.eventCenter t ht
  t := tcoord (D.position.eventCenter t ht)
  r := (D.position.eventModel t ht).fiberCoverRadius
  ε := -(D.chronologicalWindowRadius t ht ^ 2)
  R := D.chronologicalCriticalExteriorTimeField t ht
  hneg := D.chronologicalReverseAfter_regular t ht
  hpos := D.chronologicalReverseBefore_regular t ht
  Vneg := D.chronologicalMaximumReverseSourceField t ht
  Vpos := D.chronologicalMaximumReverseTargetField t ht
  A := D.chronologicalMaximumExteriorTargetFamily t ht
  safe := by
    simpa [chronologicalCriticalExteriorTimeField] using
      D.chronologicalWindowRadius_sq_reverse_safe t ht
  midpoint_mem := by
    intro O q
    let e := D.chronologicalMaximumReverseSourceEquiv t ht
    let O₀ := e.symm O
    let P := (D.chronologicalAfterField t ht).intrinsicSimpleClosedOrbitParam O₀.1
    have hPext : (O₀.1 : Set Eₐ) ∈
        D.chronologicalExteriorOrbitCollection t ht
          (D.chronologicalAfterTime t ht) :=
      D.chronologicalMaximumAfterOrbit_mem_exterior t ht hindex O₀.1
    have hcurveOrbit : P.curve q ∈ (O₀.1 : Set Eₐ) := by
      rw [(D.chronologicalAfterField t ht).orbitPoint_orbit O₀.1]
      exact P.curve_mem_orbit q
    have hp : P.exteriorAmbientLoop q ∈
        D.chronologicalExteriorSlabCore t ht := by
      exact D.chronologicalOrbitPoint_mem_exteriorSlabCore
        t ht (D.chronologicalAfterTime t ht)
        ⟨(D.chronologicalAfterTime_mem_bracket t ht).1.le,
          (D.chronologicalAfterTime_mem_bracket t ht).2.le⟩
        (D.chronologicalAfterTime_regular t ht)
        (D.chronologicalAfterField t ht) O₀.1 hcurveOrbit hPext
    have hshift : tcoord (P.exteriorAmbientLoop q) +
        -(D.chronologicalWindowRadius t ht ^ 2) =
        tcoord (D.position.eventCenter t ht) := by
      simp [P, SimpleClosedOrbitParam.exteriorAmbientLoop,
        chronologicalAfterTime]
    have hloop :
        ((D.chronologicalMaximumReverseSourceField t ht).intrinsicSimpleClosedOrbitParam O.1).exteriorAmbientLoop q =
          P.exteriorAmbientLoop q := by
      change cobSpaceTime
          ((D.chronologicalMaximumReverseSourceField t ht).intrinsicSimpleClosedOrbitParam O.1 |>.curve q)
          (tcoord (D.position.eventCenter t ht) -
            -(D.chronologicalWindowRadius t ht ^ 2)) =
        cobSpaceTime (P.curve q) (D.chronologicalAfterTime t ht)
      apply congrArg₂ cobSpaceTime
      · exact (D.chronologicalAfterField t ht).transportedIntrinsicCurve_symm
          (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
          (D.chronologicalMaximumExteriorTargetFamily t ht) O q
      · exact D.chronologicalReverseAfterTime_eq t ht
    rw [hloop]
    simpa [chronologicalCriticalExteriorTimeField] using
      D.chronologicalDefiniteExteriorShift_mem t ht (Or.inr hindex)
        hp (D.chronologicalWindowRadius_sq_reverse_safe t ht) hshift


-- @@ L413-427 verbatim
def chronologicalMinimumReverseTargetOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (O : {O // O ∈ (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)}) :
    (D.chronologicalBeforeField t ht).OrbitIndex :=
  let H := D.chronologicalMinimumReverseExteriorFlowCore
    t ht hpositive hindex
  let eSource := D.chronologicalMinimumReverseSourceEquiv
    t ht hpositive hindex
  let eTarget := D.chronologicalMinimumReverseTargetOrbitEquiv t ht
  eTarget.symm (H.targetOrbit (eSource O))


-- @@ L429-439 verbatim
def chronologicalMaximumReverseTargetOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)}) :
    (D.chronologicalMaximumLocalField t ht).OrbitIndex :=
  let H := D.chronologicalMaximumReverseExteriorFlowCore t ht hindex
  let eSource := D.chronologicalMaximumReverseSourceEquiv t ht
  let eTarget := D.chronologicalMaximumReverseTargetOrbitEquiv t ht
  eTarget.symm (H.targetOrbit (eSource O))


-- @@ L441-441 verbatim
/-! ## Positivity after reverse transport -/


-- @@ L443-462 verbatim
/-- A compact time-field flow preserves the sign on the zero fiber. -/
theorem compactTimeTamedField_flow_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    {K : Set (EuclideanSpace ℝ (Fin ((a + 2) + 2)))}
    (R : CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData K)
    {p : EuclideanSpace ℝ (Fin ((a + 2) + 2))}
    (hpFiber : D.signedOutput.cobordism.G p = 0)
    (hp : 0 < D.signedOutput p) (s : ℝ) :
    0 < D.signedOutput (R.base.flow p s) := by
  let γ : C(I, EuclideanSpace ℝ (Fin ((a + 2) + 2))) :=
    ⟨fun u => R.base.flow p ((u : ℝ) * s),
      (R.base.continuous_flow p).comp
        (continuous_subtype_val.mul continuous_const)⟩
  have hγFiber : ∀ u, D.signedOutput.cobordism.G (γ u) = 0 := by
    intro u
    exact R.flow_mem_fiber hpFiber _
  have h := (D.signedOutput.pos_iff_of_zeroFiber_path γ hγFiber).mp
    (by simpa [γ] using hp)
  simpa [γ] using h


-- @@ L464-599 verbatim
theorem chronologicalMinimumReverseTargetOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (O : {O // O ∈ (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)}) :
    D.chronologicalMinimumReverseTargetOrbit t ht hpositive hindex O ∈
      (D.chronologicalBeforeField t ht).selectedOrbitFinset
        ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
          (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
            (D.chronologicalBeforeField t ht)) := by
  let H := D.chronologicalMinimumReverseExteriorFlowCore
    t ht hpositive hindex
  let eSource := D.chronologicalMinimumReverseSourceEquiv
    t ht hpositive hindex
  let eTarget := D.chronologicalMinimumReverseTargetOrbitEquiv t ht
  let OH := eSource O
  let Q := eTarget.symm (H.targetOrbit OH)
  let Vneg := D.chronologicalMinimumLocalField t ht
  let Vpos := D.chronologicalBeforeField t ht
  let Sneg := D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)
  let Spos := D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)
  change Q ∈ Vpos.selectedOrbitFinset (Spos.positiveOrbitCollection Vpos)
  have hsourceCollection : (O.1 : Set Eₐ) ∈
      Sneg.positiveOrbitCollection Vneg :=
    ((Vneg.mem_selectedOrbitFinset O.1).mp O.2).1
  have hsourceSign : 0 < Sneg (Vneg.orbitPoint O.1) :=
    (Sneg.mem_positiveOrbitCollection_iff Vneg O.1).mp hsourceCollection
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
        ((D.chronologicalMinimumReverseSourceField t ht).intrinsicSimpleClosedOrbitParam OH.1 |>.curve 0)
        (tcoord (D.position.eventCenter t ht) -
          -(D.chronologicalWindowRadius t ht ^ 2)) =
      cobSpaceTime (P.curve 0) (D.chronologicalAfterTime t ht)
    apply congrArg₂ cobSpaceTime
    · change
        (((Vneg.transport
          (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)).intrinsicSimpleClosedOrbitParam OH.1).curve 0) = P.curve 0
      calc
        _ = (Vneg.intrinsicSimpleClosedOrbitParam
              (((Vneg.selectedOrbitTransportEquiv
                (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
                (D.chronologicalMinimumExteriorTargetFamily
                  t ht hpositive hindex)).symm OH).1)).curve 0 :=
          Vneg.transportedIntrinsicCurve_symm
            (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
            (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)
            OH 0
        _ = P.curve 0 := by
          have hO : (Vneg.selectedOrbitTransportEquiv
              (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
              (D.chronologicalMinimumExteriorTargetFamily
                t ht hpositive hindex)).symm OH = O := by
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


-- @@ L601-729 verbatim
theorem chronologicalMaximumReverseTargetOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)}) :
    D.chronologicalMaximumReverseTargetOrbit t ht hindex O ∈
      (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
        ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
          (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
            (D.chronologicalMaximumLocalField t ht)) := by
  let H := D.chronologicalMaximumReverseExteriorFlowCore t ht hindex
  let eSource := D.chronologicalMaximumReverseSourceEquiv t ht
  let eTarget := D.chronologicalMaximumReverseTargetOrbitEquiv t ht
  let OH := eSource O
  let Q := eTarget.symm (H.targetOrbit OH)
  let Vneg := D.chronologicalAfterField t ht
  let Vpos := D.chronologicalMaximumLocalField t ht
  let Sneg := D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)
  let Spos := D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)
  change Q ∈ Vpos.selectedOrbitFinset (Spos.positiveOrbitCollection Vpos)
  have hsourceCollection : (O.1 : Set Eₐ) ∈
      Sneg.positiveOrbitCollection Vneg :=
    (Vneg.mem_selectedOrbitFinset O.1).mp O.2
  have hsourceSign : 0 < Sneg (Vneg.orbitPoint O.1) :=
    (Sneg.mem_positiveOrbitCollection_iff Vneg O.1).mp hsourceCollection
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
        ((D.chronologicalMaximumReverseSourceField t ht).intrinsicSimpleClosedOrbitParam OH.1 |>.curve 0)
        (tcoord (D.position.eventCenter t ht) -
          -(D.chronologicalWindowRadius t ht ^ 2)) =
      cobSpaceTime (P.curve 0) (D.chronologicalAfterTime t ht)
    apply congrArg₂ cobSpaceTime
    · change
        (((Vneg.transport
          (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)).intrinsicSimpleClosedOrbitParam OH.1).curve 0) = P.curve 0
      calc
        _ = (Vneg.intrinsicSimpleClosedOrbitParam
              (((Vneg.selectedOrbitTransportEquiv
                (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
                (D.chronologicalMaximumExteriorTargetFamily t ht)).symm OH).1)).curve 0 :=
          Vneg.transportedIntrinsicCurve_symm
            (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
            (D.chronologicalMaximumExteriorTargetFamily t ht) OH 0
        _ = P.curve 0 := by
          have hO : (Vneg.selectedOrbitTransportEquiv
              (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
              (D.chronologicalMaximumExteriorTargetFamily t ht)).symm OH = O := by
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


-- @@ L731-731 verbatim
/-! ## Reverse maps on the original selected-orbit subtypes -/


-- @@ L733-746 verbatim
def chronologicalMinimumReverseTargetMap
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    {O // O ∈ (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)} →
    {Q // Q ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)} :=
  fun O => ⟨D.chronologicalMinimumReverseTargetOrbit
      t ht hpositive hindex O,
    D.chronologicalMinimumReverseTargetOrbit_mem_positive
      t ht hpositive hindex O⟩


-- @@ L748-767 verbatim
theorem chronologicalMinimumReverseTargetMap_injective
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    Function.Injective (D.chronologicalMinimumReverseTargetMap
      t ht hpositive hindex) := by
  intro O P hOP
  let H := D.chronologicalMinimumReverseExteriorFlowCore
    t ht hpositive hindex
  let eSource := D.chronologicalMinimumReverseSourceEquiv
    t ht hpositive hindex
  let eTarget := D.chronologicalMinimumReverseTargetOrbitEquiv t ht
  have hval := congrArg Subtype.val hOP
  change eTarget.symm (H.targetOrbit (eSource O)) =
    eTarget.symm (H.targetOrbit (eSource P)) at hval
  apply eSource.injective
  apply H.targetOrbit_injective
  exact eTarget.symm.injective hval


-- @@ L769-782 verbatim
/-- The one remaining maximum-side geometric statement: reverse flow must not
hit the dying local component. -/
abbrev ChronologicalMaximumReverseNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) : Prop :=
  ∀ O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)},
    ((D.chronologicalMaximumReverseTargetOrbit t ht hindex O :
        (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set Eₐ) ≠
      (((D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set Eₐ)


-- @@ L784-803 verbatim
def chronologicalMaximumReverseTargetMap
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hnoncollision : D.ChronologicalMaximumReverseNoncollision
      t ht hpositive hindex) :
    {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)} →
    {Q // Q ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorSourceFamily
        t ht hpositive hindex)} := by
  intro O
  refine ⟨D.chronologicalMaximumReverseTargetOrbit t ht hindex O, ?_⟩
  apply ((D.chronologicalMaximumLocalField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · exact ((D.chronologicalMaximumLocalField t ht).mem_selectedOrbitFinset _).mp
      (D.chronologicalMaximumReverseTargetOrbit_mem_positive t ht hindex O)
  · exact hnoncollision O


-- @@ L805-824 verbatim
theorem chronologicalMaximumReverseTargetMap_injective
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hnoncollision : D.ChronologicalMaximumReverseNoncollision
      t ht hpositive hindex) :
    Function.Injective (D.chronologicalMaximumReverseTargetMap
      t ht hpositive hindex hnoncollision) := by
  intro O P hOP
  let H := D.chronologicalMaximumReverseExteriorFlowCore t ht hindex
  let eSource := D.chronologicalMaximumReverseSourceEquiv t ht
  let eTarget := D.chronologicalMaximumReverseTargetOrbitEquiv t ht
  have hval := congrArg Subtype.val hOP
  change eTarget.symm (H.targetOrbit (eSource O)) =
    eTarget.symm (H.targetOrbit (eSource P)) at hval
  apply eSource.injective
  apply H.targetOrbit_injective
  exact eTarget.symm.injective hval


-- @@ L826-826 verbatim
/-! ## Forward maps and finite cardinality balance -/


-- @@ L828-847 verbatim
/-- The minimum-side geometric remainder: forward exterior flow must avoid
the born local component. -/
abbrev ChronologicalMinimumForwardNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) : Prop :=
  ∀ O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)},
    (((D.chronologicalMinimumExteriorFlowCore t ht
      (ChronologicalMinimumExteriorFlowControl.canonical
        (D := D) (t := t) (ht := ht)
        (hpositive := hpositive) (hindex := hindex)).safe
      (ChronologicalMinimumExteriorFlowControl.canonical
        (D := D) (t := t) (ht := ht)
        (hpositive := hpositive) (hindex := hindex)).midpointCapture).targetOrbit O :
        (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set Eₐ) ≠
      (((D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set Eₐ)


-- @@ L849-873 verbatim
def chronologicalMinimumForwardTargetMap
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hnoncollision : D.ChronologicalMinimumForwardNoncollision
      t ht hpositive hindex) :
    {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)} →
    {Q // Q ∈ (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)} := by
  let F := ChronologicalMinimumExteriorFlowControl.canonical
    (D := D) (t := t) (ht := ht)
    (hpositive := hpositive) (hindex := hindex)
  let H := D.chronologicalMinimumExteriorFlowCore
    t ht F.safe F.midpointCapture
  intro O
  refine ⟨H.targetOrbit O, ?_⟩
  apply ((D.chronologicalMinimumLocalField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · exact ((D.chronologicalMinimumLocalField t ht).mem_selectedOrbitFinset _).mp
      (D.chronologicalMinimumTargetOrbit_mem_positive
        t ht F.safe F.midpointCapture O)
  · simpa [F, H] using hnoncollision O


-- @@ L875-891 verbatim
theorem chronologicalMinimumForwardTargetMap_injective
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hnoncollision : D.ChronologicalMinimumForwardNoncollision
      t ht hpositive hindex) :
    Function.Injective (D.chronologicalMinimumForwardTargetMap
      t ht hpositive hindex hnoncollision) := by
  intro O P hOP
  let F := ChronologicalMinimumExteriorFlowControl.canonical
    (D := D) (t := t) (ht := ht)
    (hpositive := hpositive) (hindex := hindex)
  apply (D.chronologicalMinimumExteriorFlowCore
    t ht F.safe F.midpointCapture).targetOrbit_injective
  exact congrArg Subtype.val hOP


-- @@ L893-911 verbatim
def chronologicalMaximumForwardTargetMap
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    {O // O ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex)} →
    {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)} := by
  let F := ChronologicalMaximumExteriorFlowControl.canonical
    (D := D) (t := t) (ht := ht)
    (hpositive := hpositive) (hindex := hindex)
  let H := D.chronologicalMaximumExteriorFlowCore
    t ht hpositive hindex F.safe F.midpointCapture
  intro O
  exact ⟨H.targetOrbit O,
    D.chronologicalMaximumTargetOrbit_mem_positive
      t ht hpositive hindex F.safe F.midpointCapture O⟩


-- @@ L913-927 verbatim
theorem chronologicalMaximumForwardTargetMap_injective
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    Function.Injective (D.chronologicalMaximumForwardTargetMap
      t ht hpositive hindex) := by
  intro O P hOP
  let F := ChronologicalMaximumExteriorFlowControl.canonical
    (D := D) (t := t) (ht := ht)
    (hpositive := hpositive) (hindex := hindex)
  apply (D.chronologicalMaximumExteriorFlowCore
    t ht hpositive hindex F.safe F.midpointCapture).targetOrbit_injective
  exact congrArg Subtype.val hOP


-- @@ L929-950 verbatim
theorem chronologicalMinimumExterior_card_eq_of_noncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hnoncollision : D.ChronologicalMinimumForwardNoncollision
      t ht hpositive hindex) :
    ((D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)).card =
    ((D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)).card := by
  have hforward := Fintype.card_le_of_injective
    (D.chronologicalMinimumForwardTargetMap
      t ht hpositive hindex hnoncollision)
    (D.chronologicalMinimumForwardTargetMap_injective
      t ht hpositive hindex hnoncollision)
  have hreverse := Fintype.card_le_of_injective
    (D.chronologicalMinimumReverseTargetMap t ht hpositive hindex)
    (D.chronologicalMinimumReverseTargetMap_injective
      t ht hpositive hindex)
  simpa only [Fintype.card_coe] using Nat.le_antisymm hforward hreverse


-- @@ L952-973 verbatim
theorem chronologicalMaximumExterior_card_eq_of_reverse_noncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hnoncollision : D.ChronologicalMaximumReverseNoncollision
      t ht hpositive hindex) :
    ((D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex)).card =
    ((D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)).card := by
  have hforward := Fintype.card_le_of_injective
    (D.chronologicalMaximumForwardTargetMap t ht hpositive hindex)
    (D.chronologicalMaximumForwardTargetMap_injective
      t ht hpositive hindex)
  have hreverse := Fintype.card_le_of_injective
    (D.chronologicalMaximumReverseTargetMap
      t ht hpositive hindex hnoncollision)
    (D.chronologicalMaximumReverseTargetMap_injective
      t ht hpositive hindex hnoncollision)
  simpa only [Fintype.card_coe] using Nat.le_antisymm hforward hreverse


-- @@ L975-975 verbatim
/-! ## Concrete reduced-kit inhabitants from the two local noncollisions -/


-- @@ L977-989 verbatim
def chronologicalMinimumExteriorComponentBalance_of_noncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hnoncollision : D.ChronologicalMinimumForwardNoncollision
      t ht hpositive hindex) :
    D.ChronologicalMinimumExteriorComponentBalance
      t ht hpositive hindex where
  target_ne_local := hnoncollision
  card_eq := D.chronologicalMinimumExterior_card_eq_of_noncollision
    t ht hpositive hindex hnoncollision


-- @@ L991-1002 verbatim
def chronologicalMaximumExteriorComponentBalance_of_reverse_noncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hnoncollision : D.ChronologicalMaximumReverseNoncollision
      t ht hpositive hindex) :
    D.ChronologicalMaximumExteriorComponentBalance
      t ht hpositive hindex where
  card_eq := D.chronologicalMaximumExterior_card_eq_of_reverse_noncollision
    t ht hpositive hindex hnoncollision


-- @@ L1004-1015 verbatim
def chronologicalMinimumExteriorCardinalityKit_of_noncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hnoncollision : D.ChronologicalMinimumForwardNoncollision
      t ht hpositive hindex) :
    D.ChronologicalMinimumExteriorCardinalityKit
      t ht hpositive hindex where
  components := D.chronologicalMinimumExteriorComponentBalance_of_noncollision
    t ht hpositive hindex hnoncollision


-- @@ L1017-1029 verbatim
def chronologicalMaximumExteriorCardinalityKit_of_reverse_noncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hnoncollision : D.ChronologicalMaximumReverseNoncollision
      t ht hpositive hindex) :
    D.ChronologicalMaximumExteriorCardinalityKit
      t ht hpositive hindex where
  components :=
    D.chronologicalMaximumExteriorComponentBalance_of_reverse_noncollision
      t ht hpositive hindex hnoncollision


-- @@ L1031-1031 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L1033-1043 verbatim
/-- Dimension-uniform family of the sole minimum noncollision statements. -/
abbrev ProductionMorseMinimumForwardNoncollisions (a : ℕ) :=
  ∀ {X Y : FramedLevelSet (a + 2)}
    {S : FiberSign X} {T : FiberSign Y}
    (C : SignedFramedLevelCobordism S T)
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum),
      D.ChronologicalMinimumForwardNoncollision t ht hpositive hindex


-- @@ L1045-1056 verbatim
/-- Dimension-uniform family of the sole maximum reverse-noncollision
statements. -/
abbrev ProductionMorseMaximumReverseNoncollisions (a : ℕ) :=
  ∀ {X Y : FramedLevelSet (a + 2)}
    {S : FiberSign X} {T : FiberSign Y}
    (C : SignedFramedLevelCobordism S T)
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum),
      D.ChronologicalMaximumReverseNoncollision t ht hpositive hindex


-- @@ L1058-1065 verbatim
/-- A uniform minimum noncollision family now produces an actual `Kmin`;
cardinality is derived, not supplied. -/
theorem productionMorseMinimumExteriorCardinalityKits_of_forward_noncollision
    {a : ℕ} (N : ProductionMorseMinimumForwardNoncollisions a) :
    ProductionMorseMinimumExteriorCardinalityKits a := by
  intro X Y S T C D t ht hpositive hindex
  exact ⟨D.chronologicalMinimumExteriorCardinalityKit_of_noncollision
    t ht hpositive hindex (N C D t ht hpositive hindex)⟩


-- @@ L1067-1074 verbatim
/-- A uniform maximum reverse-noncollision family now produces an actual
`Kmax`; cardinality is derived, not supplied. -/
theorem productionMorseMaximumExteriorCardinalityKits_of_reverse_noncollision
    {a : ℕ} (N : ProductionMorseMaximumReverseNoncollisions a) :
    ProductionMorseMaximumExteriorCardinalityKits a := by
  intro X Y S T C D t ht hpositive hindex
  exact ⟨D.chronologicalMaximumExteriorCardinalityKit_of_reverse_noncollision
    t ht hpositive hindex (N C D t ht hpositive hindex)⟩


-- @@ L1076-1076 verbatim
end Submission
