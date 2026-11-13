import Submission.ProductionMorseSaddleOrientedExteriorPairing
import Submission.ProductionMorseSaddleLocalExcision
import Submission.ProductionMorseSaddleSupply


-- @@ L5-24 verbatim
/-!
# From oriented critical arcs to the production saddle topology

`SaddlePuncturedCriticalArcPairingData` determines which of the two oriented
four-end matchings occurs.  Turning that matching into equality of the actual
regular-slice `OrbitIndex` values needs one honest ODE input: the chosen
critical arcs must admit a common safe flow to the two chronological slices,
and the four flowed endpoints must remain in their labelled local branches.

The converse implication used for *inequality* is also recorded honestly.
If two distinct regular local branches were one complete orbit, deleting the
local saddle segment must leave a critical exterior arc between the
corresponding two ends.  This is the sole complement-arc contract below.

With those two geometric bridges explicit, the rest is forced.  Safe flow
gives equality along the actual mate; uniqueness of the mate excludes equality
for the transverse matching; the finite oriented-pairing theorem then produces
exactly `ChronologicalSaddleMergeTopology` or
`ChronologicalSaddleSplitTopology`.
-/


-- @@ L26-26 verbatim
set_option autoImplicit false

-- @@ L27-27 verbatim
set_option maxHeartbeats 2400000


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
open Set Function

-- @@ L32-32 verbatim
open scoped RealInnerProductSpace unitInterval


-- @@ L34-34 verbatim
namespace Submission


-- @@ L36-36 verbatim
variable {n : ℕ}


-- @@ L38-38 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L39-39 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L40-40 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L42-42 verbatim
namespace SaddleCriticalExteriorArcPairingData


-- @@ L44-44 verbatim
variable {P X : Type*} [TopologicalSpace X]

-- @@ L45-45 verbatim
variable {endpoint : P → X} {K : Set X} {boundaryRaw : P → ℝ}


-- @@ L47-53 verbatim
/-- A fixed representative of the exterior arc from an end to its unique
mate.  No choice is added to the geometric contract: `mate_arc` already
contains the required nonempty path. -/
noncomputable def chosenMateArc
    (A : SaddleCriticalExteriorArcPairingData endpoint K boundaryRaw)
    (p : P) : SaddleCriticalExteriorArc endpoint K p (A.mate p) :=
  (A.mate_arc p).some


-- @@ L55-55 verbatim
end SaddleCriticalExteriorArcPairingData


-- @@ L57-57 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L58-58 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L59-59 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L61-61 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L63-63 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L64-64 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L65-65 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L67-67 verbatim
local notation "rho" => D.chronologicalSaddleBoundaryRadius t ht

-- @@ L68-68 verbatim
local notation "a" => D.chronologicalWindowRadius t ht


-- @@ L70-83 verbatim
/-- The explicit chart witness saying that one safely flowed critical end
lands in its labelled positive local branch. -/
structure ChronologicalSaddlePositiveEndpointCapture
    {K : Set E'}
    (R : CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData K)
    (p : SaddleBranch × SaddleBranch) : Type where
  param : E₂
  param_mem : ‖param‖ < (D.position.eventModel t ht).radius
  endpoint_eq : (D.position.eventModel t ht).param param =
    R.base.flow
      ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho) (a ^ 2)
  branch_sign : 0 < signedBranch p.1 (param 0)
  quadratic : morseQuadratic .saddle (param 0, param 1) = a ^ 2


-- @@ L85-99 verbatim
/-- Negative-slice counterpart.  At the critical level the positive label
`(branch,end)` is the negative label `(end,branch)`, hence the branch selected
after negative flow is `p.2`. -/
structure ChronologicalSaddleNegativeEndpointCapture
    {K : Set E'}
    (R : CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData K)
    (p : SaddleBranch × SaddleBranch) : Type where
  param : E₂
  param_mem : ‖param‖ < (D.position.eventModel t ht).radius
  endpoint_eq : (D.position.eventModel t ht).param param =
    R.base.flow
      ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho) (-(a ^ 2))
  branch_sign : 0 < signedBranch p.2 (param 1)
  quadratic : morseQuadratic .saddle (param 0, param 1) = -(a ^ 2)


-- @@ L101-121 verbatim
/-- The exact safe-flow completion of the topological four-end pairing.

The field is allowed to live on an arbitrary compact core `K`; only the four
chosen mate arcs must lie in that core.  `safe` and the two endpoint-capture
families are precisely the hypotheses used by the old ExactFinite
path-to-orbit proof, now stated for the actual production event. -/
structure ChronologicalSaddleOrientedArcFlowData
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) where
  K : Set E'
  field : CompactTimeTamedField
    D.signedOutput.cobordism.toLevelCobordismData K
  chosenMateArc_mem : ∀ (p : SaddleBranch × SaddleBranch) (u : I),
    (A.chosenMateArc p).toPath u ∈ K
  safe : a ^ 2 ≤ field.safeTime
  positiveEndpoint : ∀ p,
    ChronologicalSaddlePositiveEndpointCapture
      (D := D) (t := t) (ht := ht) field p
  negativeEndpoint : ∀ p,
    ChronologicalSaddleNegativeEndpointCapture
      (D := D) (t := t) (ht := ht) field p


-- @@ L123-146 verbatim
/-- The minimal converse bridge needed to turn the matching dichotomy into
the *inequality* half of merge/split topology.  It says only that equality of
the two distinct positive (respectively negative) local branches produces the
transverse critical exterior arc obtained by deleting the local saddle
segment from that complete regular orbit. -/
structure ChronologicalSaddleRegularOrbitArcRecovery : Prop where
  positiveArc :
    D.chronologicalSaddlePositiveOrbit t ht hindex .negative =
        D.chronologicalSaddlePositiveOrbit t ht hindex .positive →
      Nonempty (SaddleCriticalExteriorArc
        (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho)
        (StandardMorseEventAt.puncturedCriticalSlice
          D.signedOutput.cobordism (D.position.eventCenter t ht))
        (SaddleBranch.negative, SaddleBranch.negative)
        (SaddleBranch.positive, SaddleBranch.negative))
  negativeArc :
    D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
        D.chronologicalSaddleNegativeOrbit t ht hindex .positive →
      Nonempty (SaddleCriticalExteriorArc
        (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho)
        (StandardMorseEventAt.puncturedCriticalSlice
          D.signedOutput.cobordism (D.position.eventCenter t ht))
        (SaddleBranch.negative, SaddleBranch.negative)
        (SaddleBranch.negative, SaddleBranch.positive))


-- @@ L148-148 verbatim
namespace ChronologicalSaddleOrientedArcFlowData


-- @@ L150-152 verbatim
variable {A :
  (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
    (D.chronologicalSaddleBoundaryRadius t ht)}


-- @@ L154-180 verbatim
/-- A captured positive endpoint belongs to the actual chronological branch
orbit selected by the first end label. -/
theorem positiveEndpoint_mem_branchOrbit
    (F : ChronologicalSaddleOrientedArcFlowData
      (D := D) (t := t) (ht := ht) A)
    (p : SaddleBranch × SaddleBranch) :
    spacePart (F.field.base.flow
        ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho)
        (a ^ 2)) ∈
      ((D.chronologicalSaddlePositiveOrbit t ht hindex p.1 :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  obtain ⟨u, hu, hend, hsign, hquad⟩ := F.positiveEndpoint p
  have hmem := T.saddlePositiveParam_mem_branch_orbit_full H hindex p.1
    rho a u hquad hsign
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
    hu
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalAfterField t ht)
  rw [hend] at hmem
  simpa [T, chronologicalSaddlePositiveOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchOrbitIndex]
    using hmem


-- @@ L182-208 verbatim
/-- Negative endpoint version; the branch label is the second critical-end
coordinate because of the saddle boundary switch. -/
theorem negativeEndpoint_mem_branchOrbit
    (F : ChronologicalSaddleOrientedArcFlowData
      (D := D) (t := t) (ht := ht) A)
    (p : SaddleBranch × SaddleBranch) :
    spacePart (F.field.base.flow
        ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho)
        (-(a ^ 2))) ∈
      ((D.chronologicalSaddleNegativeOrbit t ht hindex p.2 :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  obtain ⟨u, hu, hend, hsign, hquad⟩ := F.negativeEndpoint p
  have hmem := T.saddleNegativeParam_mem_branch_orbit_full H hindex p.2
    rho a u hquad hsign
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
    hu
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalBeforeField t ht)
  rw [hend] at hmem
  simpa [T, chronologicalSaddleNegativeOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchOrbitIndex]
    using hmem


-- @@ L210-238 verbatim
/-- Production port of
`criticalSaddlePositiveBranchOrbitIndex_eq_of_criticalExteriorPath`: one
chosen critical mate arc safely flows into a path in a single actual positive
slice orbit. -/
theorem positiveMateOrbit_eq
    (F : ChronologicalSaddleOrientedArcFlowData
      (D := D) (t := t) (ht := ht) A)
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddlePositiveOrbit t ht hindex p.1 =
      D.chronologicalSaddlePositiveOrbit t ht hindex (A.mate p).1 := by
  let gamma := A.chosenMateArc p
  let V := D.chronologicalAfterField t ht
  have hsafe : |a ^ 2| ≤ F.field.safeTime := by
    rw [abs_of_nonneg (sq_nonneg a)]
    exact F.safe
  have hflow := F.field.flowSlicePath_endpoints_mem_same_orbit
    gamma.toPath (F.chosenMateArc_mem p)
    (fun u => (gamma.mem_exterior u).2.1)
    (fun u => (gamma.mem_exterior u).1)
    hsafe (D.chronologicalAfterTime_regular t ht) V
  have hmem₁ := positiveEndpoint_mem_branchOrbit
    (D := D) (t := t) (ht := ht) (hindex := hindex) F p
  have hmem₂ := positiveEndpoint_mem_branchOrbit
    (D := D) (t := t) (ht := ht) (hindex := hindex) F (A.mate p)
  have heq₁ := V.orbit_eq_of_mem hmem₁
  have heq₂ := V.orbit_eq_of_mem hmem₂
  have heqflow := V.orbit_eq_of_mem hflow
  apply Subtype.ext
  exact heq₁.symm.trans (heqflow.symm.trans heq₂)


-- @@ L240-268 verbatim
/-- Negative-slice production port of the same path-to-orbit argument. -/
theorem negativeMateOrbit_eq
    (F : ChronologicalSaddleOrientedArcFlowData
      (D := D) (t := t) (ht := ht) A)
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleNegativeOrbit t ht hindex p.2 =
      D.chronologicalSaddleNegativeOrbit t ht hindex (A.mate p).2 := by
  let gamma := A.chosenMateArc p
  let V := D.chronologicalBeforeField t ht
  have hsafe : |-(a ^ 2)| ≤ F.field.safeTime := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg a)]
    exact F.safe
  have hflow := F.field.flowSlicePath_endpoints_mem_same_orbit
    gamma.toPath (F.chosenMateArc_mem p)
    (fun u => (gamma.mem_exterior u).2.1)
    (fun u => (gamma.mem_exterior u).1)
    hsafe (by
      simpa only [chronologicalBeforeTime, sub_eq_add_neg,
        FramedLevelCobordism.toLevelCobordismData] using
        D.chronologicalBeforeTime_regular t ht) V
  have hmem₁ := negativeEndpoint_mem_branchOrbit
    (D := D) (t := t) (ht := ht) (hindex := hindex) F p
  have hmem₂ := negativeEndpoint_mem_branchOrbit
    (D := D) (t := t) (ht := ht) (hindex := hindex) F (A.mate p)
  have heq₁ := V.orbit_eq_of_mem hmem₁
  have heq₂ := V.orbit_eq_of_mem hmem₂
  have heqflow := V.orbit_eq_of_mem hflow
  apply Subtype.ext
  exact heq₁.symm.trans (heqflow.symm.trans heq₂)


-- @@ L270-270 verbatim
end ChronologicalSaddleOrientedArcFlowData


-- @@ L272-272 verbatim
namespace ChronologicalSaddleRegularOrbitArcRecovery


-- @@ L274-276 verbatim
variable {A :
  (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
    (D.chronologicalSaddleBoundaryRadius t ht)}


-- @@ L278-297 verbatim
/-- If the actual mate is `flipSecond`, equality of the two positive branches
would recover a transverse `flipFirst` arc, contradicting uniqueness. -/
theorem positive_ne_of_mate_eq_flipSecond
    (H : ChronologicalSaddleRegularOrbitArcRecovery
      (D := D) (t := t) (ht := ht) (hindex := hindex))
    (hmate : ∀ p, A.mate p = saddleBranchEndFlipSecond p) :
    D.chronologicalSaddlePositiveOrbit t ht hindex .negative ≠
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive := by
  intro heq
  let p : SaddleBranch × SaddleBranch := (.negative, .negative)
  let q : SaddleBranch × SaddleBranch := (.positive, .negative)
  have harc : Nonempty (SaddleCriticalExteriorArc
      (fun r => (D.position.eventModel t ht).saddleCriticalBoundaryEnd r rho)
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht)) p q) := by
    simpa [p, q] using H.positiveArc heq
  have hq : q = A.mate p :=
    A.eq_mate_of_ne_arc (by simp [p, q]) harc
  rw [hmate p] at hq
  simp [p, q, saddleBranchEndFlipSecond] at hq


-- @@ L299-318 verbatim
/-- If the mate is `flipFirst`, equality of the two negative branches would
recover the forbidden transverse `flipSecond` arc. -/
theorem negative_ne_of_mate_eq_flipFirst
    (H : ChronologicalSaddleRegularOrbitArcRecovery
      (D := D) (t := t) (ht := ht) (hindex := hindex))
    (hmate : ∀ p, A.mate p = saddleBranchEndFlipFirst p) :
    D.chronologicalSaddleNegativeOrbit t ht hindex .negative ≠
      D.chronologicalSaddleNegativeOrbit t ht hindex .positive := by
  intro heq
  let p : SaddleBranch × SaddleBranch := (.negative, .negative)
  let q : SaddleBranch × SaddleBranch := (.negative, .positive)
  have harc : Nonempty (SaddleCriticalExteriorArc
      (fun r => (D.position.eventModel t ht).saddleCriticalBoundaryEnd r rho)
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht)) p q) := by
    simpa [p, q] using H.negativeArc heq
  have hq : q = A.mate p :=
    A.eq_mate_of_ne_arc (by simp [p, q]) harc
  rw [hmate p] at hq
  simp [p, q, saddleBranchEndFlipFirst] at hq


-- @@ L320-320 verbatim
end ChronologicalSaddleRegularOrbitArcRecovery


-- @@ L322-359 verbatim
/-- The honest contract-to-topology bridge.  The topological pairing `A`, its
safe ODE realization `F`, and complement-arc recovery `H` force exactly one of
the two production saddle topologies. -/
theorem chronologicalSaddleTopologyDichotomy_of_orientedExteriorArcs
    (A :
      (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData rho)
    (F : ChronologicalSaddleOrientedArcFlowData
      (D := D) (t := t) (ht := ht) A)
    (H : ChronologicalSaddleRegularOrbitArcRecovery
      (D := D) (t := t) (ht := ht) (hindex := hindex)) :
    D.ChronologicalSaddleMergeTopology t ht hindex ∨
      D.ChronologicalSaddleSplitTopology t ht hindex := by
  have hdich := StandardMorseEventAt.saddleExteriorArcPairing_eq_flipSecond_or_eq_flipFirst
    (D.position.eventModel t ht)
    (StandardMorseEventAt.puncturedCriticalSlice
      D.signedOutput.cobordism (D.position.eventCenter t ht))
    rho (D.chronologicalSaddleBoundaryRadius_pos t ht) A
  rcases hdich with hsecond | hfirst
  · right
    refine {
      positive_ne := ChronologicalSaddleRegularOrbitArcRecovery.positive_ne_of_mate_eq_flipSecond
        (D := D) (t := t) (ht := ht) (hindex := hindex) H hsecond
      negative_eq := ?_ }
    let p : SaddleBranch × SaddleBranch := (.negative, .negative)
    have h := ChronologicalSaddleOrientedArcFlowData.negativeMateOrbit_eq
      (D := D) (t := t) (ht := ht) (hindex := hindex) F p
    rw [hsecond p] at h
    simpa [p, saddleBranchEndFlipSecond] using h
  · left
    refine {
      negative_ne := ChronologicalSaddleRegularOrbitArcRecovery.negative_ne_of_mate_eq_flipFirst
        (D := D) (t := t) (ht := ht) (hindex := hindex) H hfirst
      positive_eq := ?_ }
    let p : SaddleBranch × SaddleBranch := (.negative, .negative)
    have h := ChronologicalSaddleOrientedArcFlowData.positiveMateOrbit_eq
      (D := D) (t := t) (ht := ht) (hindex := hindex) F p
    rw [hfirst p] at h
    simpa [p, saddleBranchEndFlipFirst] using h


-- @@ L361-361 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L363-363 verbatim
end Submission
