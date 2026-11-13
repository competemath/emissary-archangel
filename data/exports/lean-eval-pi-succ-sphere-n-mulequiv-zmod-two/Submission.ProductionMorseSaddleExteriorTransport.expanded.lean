import Submission.ProductionMorseDefiniteExteriorTransport
import Submission.ProductionMorseSaddleSignControl
import Submission.ProductionMorseRegularWindowTransport
import Submission.FramedMorseEventExcision


-- @@ L6-22 verbatim
/-!
# Exterior transport for production saddle events

This file puts the actual value-separated production saddle into the
tail-aware ledger interface.  The local distinguished components are defined
from the chronological `StandardMorseEventAt.EmbeddedShrink`, rather than from
the obsolete `ExactFiniteMorseJetInstallation` route.  A compact critical
exterior capture is then converted to the literal across-critical
`SelectedDeltaTransport` and composed with the two regular chronological
windows.

The only data retained as a geometric contract are the genuinely global
facts which are not fields of `StandardMorseEventAt`: which critical-exterior
pairing occurs, the exterior-relative frame splice, and capture of all
non-distinguished components by the compact critical-slice flow.  In
particular the caller no longer supplies the ledger's `hcross` transport.
-/


-- @@ L24-24 verbatim
set_option autoImplicit false

-- @@ L25-25 verbatim
set_option maxHeartbeats 1200000


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Set Function Metric

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L32-32 verbatim
namespace Submission


-- @@ L34-34 verbatim
variable {n : ℕ}


-- @@ L36-36 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L37-37 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L38-38 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L40-46 verbatim
/-! ## Exterior-relative frame data

The splice equation is not stored as an assumption.  Instead this record
stores the three closed homotopies which split the complete orbit loops into
their exterior and standard local factors; the existing saddle theorem then
computes the equation.
-/


-- @@ L48-68 verbatim
structure SaddleRelativeFrameSpliceData
    {Xbefore Xafter : FramedLevelSet n}
    (Vbefore : TamedField Xbefore) (Vafter : TamedField Xafter)
    (O₁ O₂ : Vbefore.OrbitIndex) (Ohat : Vafter.OrbitIndex) where
  exterior₁ : C(I, SOGroup (n + 1))
  exterior₂ : C(I, SOGroup (n + 1))
  exterior₁_closed : exterior₁ 0 = exterior₁ 1
  exterior₂_closed : exterior₂ 0 = exterior₂ 1
  model : SaddleModelContract
  incoming₁Homotopy : ContinuousMap.Homotopy (Vbefore.orbitFrameLoop O₁)
    (exterior₁ * model.incoming₁.frame (n + 1))
  incoming₂Homotopy : ContinuousMap.Homotopy (Vbefore.orbitFrameLoop O₂)
    (exterior₂ * model.incoming₂.frame (n + 1))
  outgoingHomotopy : ContinuousMap.Homotopy (Vafter.orbitFrameLoop Ohat)
    ((exterior₁ * exterior₂) * model.outgoing.frame (n + 1))
  incoming₁_closed : ∀ s : I,
    incoming₁Homotopy (s, 0) = incoming₁Homotopy (s, 1)
  incoming₂_closed : ∀ s : I,
    incoming₂Homotopy (s, 0) = incoming₂Homotopy (s, 1)
  outgoing_closed : ∀ s : I,
    outgoingHomotopy (s, 0) = outgoingHomotopy (s, 1)


-- @@ L70-70 verbatim
namespace SaddleRelativeFrameSpliceData


-- @@ L72-72 verbatim
variable {Xbefore Xafter : FramedLevelSet n}

-- @@ L73-73 verbatim
variable {Vbefore : TamedField Xbefore} {Vafter : TamedField Xafter}

-- @@ L74-74 verbatim
variable {O₁ O₂ : Vbefore.OrbitIndex} {Ohat : Vafter.OrbitIndex}


-- @@ L76-87 verbatim
/-- The genuine exterior-relative homotopies compute the actual orbit-class
splice; the equality is not a field of the data. -/
theorem orbitFrameClass_splice
    (F : SaddleRelativeFrameSpliceData Vbefore Vafter O₁ O₂ Ohat)
    (hn : 2 ≤ n) :
    Vafter.orbitFrameClass Ohat =
      Vbefore.orbitFrameClass O₁ + Vbefore.orbitFrameClass O₂ + 1 := by
  exact TamedField.orbitFrameClass_relative_saddle_splice (by omega)
    Vbefore Vafter O₁ O₂ Ohat
    F.exterior₁ F.exterior₂ F.exterior₁_closed F.exterior₂_closed
    F.model F.incoming₁Homotopy F.incoming₂Homotopy F.outgoingHomotopy
    F.incoming₁_closed F.incoming₂_closed F.outgoing_closed


-- @@ L89-89 verbatim
end SaddleRelativeFrameSpliceData


-- @@ L91-91 verbatim
/-! ## Route-independent local saddle components -/


-- @@ L93-93 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L95-95 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L96-96 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L97-97 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L99-103 verbatim
/-- The actual regular slice below an embedded saddle. -/
def saddleNegativeSlice (T : M.EmbeddedShrink) (a : ℝ)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt C.toLevelCobordismData
    (tcoord center - a ^ 2) hreg


-- @@ L105-109 verbatim
/-- The actual regular slice above an embedded saddle. -/
def saddlePositiveSlice (T : M.EmbeddedShrink) (a : ℝ)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt C.toLevelCobordismData
    (tcoord center + a ^ 2) hreg


-- @@ L111-114 verbatim
/-- A canonical local point on a negative-level saddle branch. -/
def saddleNegativeBranchBase (T : M.EmbeddedShrink)
    (b : SaddleBranch) (ρ a : ℝ) : E' :=
  M.saddleNegativeBoundaryEnd b .negative ρ a


-- @@ L116-119 verbatim
/-- A canonical local point on a positive-level saddle branch. -/
def saddlePositiveBranchBase (T : M.EmbeddedShrink)
    (b : SaddleBranch) (ρ a : ℝ) : E' :=
  M.saddlePositiveBoundaryEnd b .negative ρ a


-- @@ L121-135 verbatim
theorem saddleNegativeBranchBase_mem_fiber
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2)) :
    spacePart (T.saddleNegativeBranchBase b ρ a) ∈
      (T.saddleNegativeSlice a hreg).fiber := by
  rw [saddleNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (M.saddleNegativeBoundaryEnd b .negative ρ a))
    (tcoord center - a ^ 2)) = 0
  rw [← M.saddleNegativeBoundaryEnd_time hindex b .negative hρ ha
      (hρrad.trans_le T.radius_le), spaceTime_spacePart]
  exact M.saddleNegativeBoundaryEnd_fiber b .negative hρ ha
    (hρrad.trans_le T.radius_le)


-- @@ L137-151 verbatim
theorem saddlePositiveBranchBase_mem_fiber
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2)) :
    spacePart (T.saddlePositiveBranchBase b ρ a) ∈
      (T.saddlePositiveSlice a hreg).fiber := by
  rw [saddlePositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (M.saddlePositiveBoundaryEnd b .negative ρ a))
    (tcoord center + a ^ 2)) = 0
  rw [← M.saddlePositiveBoundaryEnd_time hindex b .negative hρ ha
      (hρrad.trans_le T.radius_le), spaceTime_spacePart]
  exact M.saddlePositiveBoundaryEnd_fiber b .negative hρ ha
    (hρrad.trans_le T.radius_le)


-- @@ L153-163 verbatim
/-- The actual negative-slice component containing a local saddle branch. -/
def saddleNegativeBranchOrbitIndex
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) : V.OrbitIndex :=
  ⟨V.orbit (spacePart (T.saddleNegativeBranchBase b ρ a)),
    V.mem_orbitFinset.mpr ⟨_,
      T.saddleNegativeBranchBase_mem_fiber hindex b hρ ha hρrad hreg,
      rfl⟩⟩


-- @@ L165-175 verbatim
/-- The actual positive-slice component containing a local saddle branch. -/
def saddlePositiveBranchOrbitIndex
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) : V.OrbitIndex :=
  ⟨V.orbit (spacePart (T.saddlePositiveBranchBase b ρ a)),
    V.mem_orbitFinset.mpr ⟨_,
      T.saddlePositiveBranchBase_mem_fiber hindex b hρ ha hρrad hreg,
      rfl⟩⟩


-- @@ L177-185 verbatim
@[simp] theorem saddleNegativeBranchOrbitIndex_coe
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    ((T.saddleNegativeBranchOrbitIndex hindex b ρ a hρ ha hρrad hreg V :
      V.OrbitIndex) : Set E₁) =
      V.orbit (spacePart (T.saddleNegativeBranchBase b ρ a)) := rfl


-- @@ L187-195 verbatim
@[simp] theorem saddlePositiveBranchOrbitIndex_coe
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2) (hρrad : ρ < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    ((T.saddlePositiveBranchOrbitIndex hindex b ρ a hρ ha hρrad hreg V :
      V.OrbitIndex) : Set E₁) =
      V.orbit (spacePart (T.saddlePositiveBranchBase b ρ a)) := rfl


-- @@ L197-197 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L199-199 verbatim
/-! ## The actual chronological production saddle -/


-- @@ L201-201 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L202-202 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L203-203 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L205-205 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L207-213 verbatim
/-- A chart-boundary radius strictly between the chronological level radius
and the embedded-chart radius. -/
def chronologicalSaddleBoundaryRadius
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : ℝ :=
  (D.chronologicalWindowRadius t ht +
    (D.chronologicalEventEmbeddedShrink t ht).radius) / 2


-- @@ L215-221 verbatim
theorem chronologicalWindowRadius_lt_saddleBoundaryRadius
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalWindowRadius t ht <
      D.chronologicalSaddleBoundaryRadius t ht := by
  unfold chronologicalSaddleBoundaryRadius
  linarith [D.chronologicalWindowRadius_lt_embedded t ht]


-- @@ L223-229 verbatim
theorem chronologicalSaddleBoundaryRadius_lt_embedded
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalSaddleBoundaryRadius t ht <
      (D.chronologicalEventEmbeddedShrink t ht).radius := by
  unfold chronologicalSaddleBoundaryRadius
  linarith [D.chronologicalWindowRadius_lt_embedded t ht]


-- @@ L231-236 verbatim
theorem chronologicalSaddleBoundaryRadius_pos
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    0 < D.chronologicalSaddleBoundaryRadius t ht :=
  (D.chronologicalWindowRadius_pos t ht).trans
    (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)


-- @@ L238-245 verbatim
theorem chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalWindowRadius t ht ^ 2 <
      D.chronologicalSaddleBoundaryRadius t ht ^ 2 := by
  exact (sq_lt_sq₀ (D.chronologicalWindowRadius_pos t ht).le
    (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2
      (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)


-- @@ L247-260 verbatim
/-- The distinguished branch component on the inner negative slice. -/
def chronologicalSaddleNegativeOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) : (D.chronologicalBeforeField t ht).OrbitIndex := by
  exact (D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchOrbitIndex
    hindex b (D.chronologicalSaddleBoundaryRadius t ht)
      (D.chronologicalWindowRadius t ht)
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
      (D.chronologicalBeforeTime_regular t ht)
      (D.chronologicalBeforeField t ht)


-- @@ L262-275 verbatim
/-- The distinguished branch component on the inner positive slice. -/
def chronologicalSaddlePositiveOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) : (D.chronologicalAfterField t ht).OrbitIndex := by
  exact (D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchOrbitIndex
    hindex b (D.chronologicalSaddleBoundaryRadius t ht)
      (D.chronologicalWindowRadius t ht)
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
      (D.chronologicalAfterTime_regular t ht)
      (D.chronologicalAfterField t ht)


-- @@ L277-327 verbatim
theorem chronologicalSaddleNegativeOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    ((D.chronologicalSaddleNegativeOrbit t ht hindex b :
      (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) ∈
      (D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
        (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalBeforeField t ht) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let ρ := D.chronologicalSaddleBoundaryRadius t ht
  let a := D.chronologicalWindowRadius t ht
  let V := D.chronologicalBeforeField t ht
  let O := D.chronologicalSaddleNegativeOrbit t ht hindex b
  let S := D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)
  apply (S.mem_positiveOrbitCollection_iff V O).2
  have hbasePositive : 0 < S
      (spacePart (T.saddleNegativeBranchBase b ρ a)) := by
    change 0 < D.signedOutput (cobSpaceTime
      (spacePart ((D.position.eventModel t ht).saddleNegativeBoundaryEnd
        b .negative ρ a)) (D.chronologicalBeforeTime t ht))
    rw [chronologicalBeforeTime]
    rw [← (D.position.eventModel t ht).saddleNegativeBoundaryEnd_time
      hindex b .negative
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
        T.radius_le), spaceTime_spacePart]
    exact T.saddleNegativeBoundaryEnd_positive_of_center
      (D.chronologicalEventCenter_positive t ht hpositive) b .negative
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
  have hbaseFiber : spacePart (T.saddleNegativeBranchBase b ρ a) ∈
      (T.saddleNegativeSlice a
        (D.chronologicalBeforeTime_regular t ht)).fiber :=
    T.saddleNegativeBranchBase_mem_fiber hindex b
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
      (D.chronologicalBeforeTime_regular t ht)
  have hmem : V.orbitPoint O ∈
      V.orbit (spacePart (T.saddleNegativeBranchBase b ρ a)) := by
    change V.orbitPoint O ∈ (O : Set E₁)
    rw [V.orbitPoint_orbit O]
    exact V.mem_orbit_self _
  exact (S.pos_iff_of_mem_orbit V hbaseFiber hmem).mp hbasePositive


-- @@ L329-379 verbatim
theorem chronologicalSaddlePositiveOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    ((D.chronologicalSaddlePositiveOrbit t ht hindex b :
      (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) ∈
      (D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
        (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalAfterField t ht) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let ρ := D.chronologicalSaddleBoundaryRadius t ht
  let a := D.chronologicalWindowRadius t ht
  let V := D.chronologicalAfterField t ht
  let O := D.chronologicalSaddlePositiveOrbit t ht hindex b
  let S := D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)
  apply (S.mem_positiveOrbitCollection_iff V O).2
  have hbasePositive : 0 < S
      (spacePart (T.saddlePositiveBranchBase b ρ a)) := by
    change 0 < D.signedOutput (cobSpaceTime
      (spacePart ((D.position.eventModel t ht).saddlePositiveBoundaryEnd
        b .negative ρ a)) (D.chronologicalAfterTime t ht))
    rw [chronologicalAfterTime]
    rw [← (D.position.eventModel t ht).saddlePositiveBoundaryEnd_time
      hindex b .negative
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
        T.radius_le), spaceTime_spacePart]
    exact T.saddlePositiveBoundaryEnd_positive_of_center
      (D.chronologicalEventCenter_positive t ht hpositive) b .negative
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
  have hbaseFiber : spacePart (T.saddlePositiveBranchBase b ρ a) ∈
      (T.saddlePositiveSlice a
        (D.chronologicalAfterTime_regular t ht)).fiber :=
    T.saddlePositiveBranchBase_mem_fiber hindex b
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
      (D.chronologicalAfterTime_regular t ht)
  have hmem : V.orbitPoint O ∈
      V.orbit (spacePart (T.saddlePositiveBranchBase b ρ a)) := by
    change V.orbitPoint O ∈ (O : Set E₁)
    rw [V.orbitPoint_orbit O]
    exact V.mem_orbit_self _
  exact (S.pos_iff_of_mem_orbit V hbaseFiber hmem).mp hbasePositive


-- @@ L381-387 verbatim
/-- The complete positive family on the inner negative saddle slice. -/
def chronologicalSaddleNegativeCollection
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : Set (Set E₁) :=
  (D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
      (D.chronologicalBeforeField t ht)


-- @@ L389-395 verbatim
/-- The complete positive family on the inner positive saddle slice. -/
def chronologicalSaddlePositiveCollection
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : Set (Set E₁) :=
  (D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
      (D.chronologicalAfterField t ht)


-- @@ L397-410 verbatim
/-- A local negative branch, now carrying its proved positive-family
membership. -/
def chronologicalSaddleNegativeSelectedOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    (D.chronologicalBeforeField t ht).SelectedOrbitIndex
      (D.chronologicalSaddleNegativeCollection t ht) :=
  ⟨D.chronologicalSaddleNegativeOrbit t ht hindex b,
    D.chronologicalSaddleNegativeOrbit_mem_positive
      t ht hpositive hindex b⟩


-- @@ L412-424 verbatim
/-- A local positive branch, carrying its proved positive-family membership. -/
def chronologicalSaddlePositiveSelectedOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    (D.chronologicalAfterField t ht).SelectedOrbitIndex
      (D.chronologicalSaddlePositiveCollection t ht) :=
  ⟨D.chronologicalSaddlePositiveOrbit t ht hindex b,
    D.chronologicalSaddlePositiveOrbit_mem_positive
      t ht hpositive hindex b⟩


-- @@ L426-432 verbatim
/-! ## Exact critical-exterior contracts

Unlike an `hcross` hypothesis, these contracts store geometric loops in the
compact critical-slice core and their two actual flow boundaries.  The
general cylinder theorem computes frame preservation and constructs the
selected transport from those loops.
-/


-- @@ L434-463 verbatim
/-- Exterior capture for a merge: remove the two negative-side local branches
and the single positive-side local component. -/
abbrev ChronologicalSaddleMergeExteriorFlowCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle) :=
  CriticalExteriorFlowCapture
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    ((D.position.eventModel t ht).fiberCoverRadius / 2)
    (D.chronologicalWindowRadius t ht ^ 2)
    (D.chronologicalSaddleCriticalExteriorTimeField t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalBeforeField t ht)
    (D.chronologicalAfterField t ht)
    ((D.chronologicalSaddleNegativeCollection t ht \
      {(((D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .negative).1 :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)}) \
      {(((D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .positive).1 :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)})
    (D.chronologicalSaddlePositiveCollection t ht \
      {(((D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .negative).1 :
          (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)})


-- @@ L465-494 verbatim
/-- Exterior capture for a split: remove one negative-side local component
and both positive-side local branches. -/
abbrev ChronologicalSaddleSplitExteriorFlowCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle) :=
  CriticalExteriorFlowCapture
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    ((D.position.eventModel t ht).fiberCoverRadius / 2)
    (D.chronologicalWindowRadius t ht ^ 2)
    (D.chronologicalSaddleCriticalExteriorTimeField t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalBeforeField t ht)
    (D.chronologicalAfterField t ht)
    (D.chronologicalSaddleNegativeCollection t ht \
      {(((D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .negative).1 :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)})
    ((D.chronologicalSaddlePositiveCollection t ht \
      {(((D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .negative).1 :
          (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)}) \
      {(((D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .positive).1 :
          (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)})


-- @@ L496-520 verbatim
/-- The actual remaining global geometry in the merge orientation.  The
exterior transport itself is deliberately not a field; it is constructed
from `exteriorCapture`. -/
structure ChronologicalSaddleMergeGeometry
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle) where
  incoming_ne :
    D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .negative ≠
      D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .positive
  outgoing_eq :
    D.chronologicalSaddlePositiveOrbit t ht hindex .negative =
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive
  exteriorCapture :
    D.ChronologicalSaddleMergeExteriorFlowCapture
      t ht hpositive hindex
  frame : SaddleRelativeFrameSpliceData
    (D.chronologicalBeforeField t ht) (D.chronologicalAfterField t ht)
    (D.chronologicalSaddleNegativeOrbit t ht hindex .negative)
    (D.chronologicalSaddleNegativeOrbit t ht hindex .positive)
    (D.chronologicalSaddlePositiveOrbit t ht hindex .negative)


-- @@ L522-544 verbatim
/-- The actual remaining global geometry in the split orientation. -/
structure ChronologicalSaddleSplitGeometry
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle) where
  incoming_ne :
    D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .negative ≠
      D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .positive
  outgoing_eq :
    D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
      D.chronologicalSaddleNegativeOrbit t ht hindex .positive
  exteriorCapture :
    D.ChronologicalSaddleSplitExteriorFlowCapture
      t ht hpositive hindex
  frame : SaddleRelativeFrameSpliceData
    (D.chronologicalAfterField t ht) (D.chronologicalBeforeField t ht)
    (D.chronologicalSaddlePositiveOrbit t ht hindex .negative)
    (D.chronologicalSaddlePositiveOrbit t ht hindex .positive)
    (D.chronologicalSaddleNegativeOrbit t ht hindex .negative)


-- @@ L546-546 verbatim
namespace ChronologicalSaddleMergeGeometry


-- @@ L548-548 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L549-549 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L550-551 verbatim
variable {hpositive : D.position.eventCenter t ht ∈
  (D.signedOutput.labelMorsePosition D.position).positiveCenters}

-- @@ L552-552 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L554-570 verbatim
/-- The capture cylinder and the constructed production branch orbits give a
literal tail-aware decomposition on the two inner chronological slices. -/
def toInnerDecomposition
    (G : ChronologicalSaddleMergeGeometry D t ht hpositive hindex) :
    SaddleOrbitLedgerDecomposition
      (D.chronologicalBeforeField t ht)
      (D.chronologicalAfterField t ht)
      (D.chronologicalSaddleNegativeCollection t ht)
      (D.chronologicalSaddlePositiveCollection t ht) where
  incoming₁ := D.chronologicalSaddleNegativeSelectedOrbit
    t ht hpositive hindex .negative
  incoming₂ := D.chronologicalSaddleNegativeSelectedOrbit
    t ht hpositive hindex .positive
  incoming_ne := G.incoming_ne
  outgoing := D.chronologicalSaddlePositiveSelectedOrbit
    t ht hpositive hindex .negative
  exteriorTransport := G.exteriorCapture.toSelectedDeltaTransport


-- @@ L572-605 verbatim
/-- Assemble the actual bracket event.  Both regular window transports are
used at ledger level, so no cast identifying an inner slice with a bracket
slice and no caller-supplied `hcross` are needed. -/
def toPositiveEventLedgerMove
    (G : ChronologicalSaddleMergeGeometry D t ht hpositive hindex)
    (hn : 2 ≤ n) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht := by
  let L := G.toInnerDecomposition
  let Tin := D.beforeWindowPositiveTransport t ht
    (D.position.eventBeforeField t ht)
    (D.chronologicalBeforeField t ht)
  let Tout := D.afterWindowPositiveTransport t ht
    (D.chronologicalAfterField t ht)
    (D.position.eventAfterField t ht)
  let tail := (D.chronologicalBeforeField t ht).selectedFrameLedger
    ((D.chronologicalSaddleNegativeCollection t ht \
      {((L.incoming₁.1 :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)}) \
      {((L.incoming₂.1 :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)})
  refine {
    beforeField := D.position.eventBeforeField t ht
    afterField := D.position.eventAfterField t ht
    move := ?_ }
  rw [hindex]
  simpa only [FiberSign.positiveFrameLedger] using
    IndexedMorseLedgerMove.saddleMerge
      ((D.chronologicalBeforeField t ht).orbitFrameClass L.incoming₁.1)
      ((D.chronologicalBeforeField t ht).orbitFrameClass L.incoming₂.1)
      ((D.chronologicalAfterField t ht).orbitFrameClass L.outgoing.1)
      tail
      (G.frame.orbitFrameClass_splice hn)
      (Tin.selectedFrameLedger_perm.trans L.before_perm)
      (Tout.selectedFrameLedger_perm.symm.trans L.after_perm)


-- @@ L607-607 verbatim
end ChronologicalSaddleMergeGeometry


-- @@ L609-609 verbatim
namespace ChronologicalSaddleSplitGeometry


-- @@ L611-611 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L612-612 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L613-614 verbatim
variable {hpositive : D.position.eventCenter t ht ∈
  (D.signedOutput.labelMorsePosition D.position).positiveCenters}

-- @@ L615-615 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L617-635 verbatim
/-- The corresponding inner decomposition, oriented from the two-component
positive slice back to the one-component negative slice. -/
def toInnerDecomposition
    (G : ChronologicalSaddleSplitGeometry D t ht hpositive hindex) :
    SaddleOrbitLedgerDecomposition
      (D.chronologicalAfterField t ht)
      (D.chronologicalBeforeField t ht)
      (D.chronologicalSaddlePositiveCollection t ht)
      (D.chronologicalSaddleNegativeCollection t ht) where
  incoming₁ := D.chronologicalSaddlePositiveSelectedOrbit
    t ht hpositive hindex .negative
  incoming₂ := D.chronologicalSaddlePositiveSelectedOrbit
    t ht hpositive hindex .positive
  incoming_ne := G.incoming_ne
  outgoing := D.chronologicalSaddleNegativeSelectedOrbit
    t ht hpositive hindex .negative
  exteriorTransport :=
    TamedField.SelectedDeltaTransport.symm
      G.exteriorCapture.toSelectedDeltaTransport


-- @@ L637-668 verbatim
/-- Assemble the actual chronological split at the bracket endpoints. -/
def toPositiveEventLedgerMove
    (G : ChronologicalSaddleSplitGeometry D t ht hpositive hindex)
    (hn : 2 ≤ n) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht := by
  let L := G.toInnerDecomposition
  let Tin := D.beforeWindowPositiveTransport t ht
    (D.position.eventBeforeField t ht)
    (D.chronologicalBeforeField t ht)
  let Tout := D.afterWindowPositiveTransport t ht
    (D.chronologicalAfterField t ht)
    (D.position.eventAfterField t ht)
  let tail := (D.chronologicalAfterField t ht).selectedFrameLedger
    ((D.chronologicalSaddlePositiveCollection t ht \
      {((L.incoming₁.1 :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)}) \
      {((L.incoming₂.1 :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)})
  refine {
    beforeField := D.position.eventBeforeField t ht
    afterField := D.position.eventAfterField t ht
    move := ?_ }
  rw [hindex]
  simpa only [FiberSign.positiveFrameLedger] using
    IndexedMorseLedgerMove.saddleSplit
      ((D.chronologicalAfterField t ht).orbitFrameClass L.incoming₁.1)
      ((D.chronologicalAfterField t ht).orbitFrameClass L.incoming₂.1)
      ((D.chronologicalBeforeField t ht).orbitFrameClass L.outgoing.1)
      tail
      (G.frame.orbitFrameClass_splice hn)
      (Tin.selectedFrameLedger_perm.trans L.after_perm)
      (Tout.selectedFrameLedger_perm.symm.trans L.before_perm)


-- @@ L670-670 verbatim
end ChronologicalSaddleSplitGeometry


-- @@ L672-686 verbatim
/-- The production saddle callback obtained after choosing its actual
merge/split exterior geometry. -/
def saddlePositiveLedgerMove_of_geometry
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hn : 2 ≤ n)
    (G : ChronologicalSaddleMergeGeometry D t ht hpositive hindex ⊕
      ChronologicalSaddleSplitGeometry D t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  G.elim
    (fun H => H.toPositiveEventLedgerMove hn)
    (fun H => H.toPositiveEventLedgerMove hn)


-- @@ L688-702 verbatim
/-- Callback-shaped existence form consumed by the production three-way event
dispatcher. -/
theorem nonempty_saddlePositiveLedgerMove_of_geometry
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hn : 2 ≤ n)
    (G : ChronologicalSaddleMergeGeometry D t ht hpositive hindex ⊕
      ChronologicalSaddleSplitGeometry D t ht hpositive hindex) :
    Nonempty (PositiveEventLedgerMoveData
      D.signedOutput D.position t ht) :=
  ⟨D.saddlePositiveLedgerMove_of_geometry
    t ht hpositive hindex hn G⟩


-- @@ L704-704 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L706-706 verbatim
end Submission
