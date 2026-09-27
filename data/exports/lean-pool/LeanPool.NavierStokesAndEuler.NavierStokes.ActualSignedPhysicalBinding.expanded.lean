/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualReferenceRebase
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalSignedWave
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStateRegularity


-- @@ L14-25 verbatim
/-!
# The actual signed family at its native reference bands

Each primary label retains its own prepared slow domain.  The otherwise
irrelevant band index in a physical reference is frozen at that label's
reference band.  In particular, no global ordering of a fixed native cover
above all common covers is asserted.

The request uses the actual common-reference state and its torus average.
Only the wave geometry is put in native coordinates: inverse-cover pullback
of the entire state would in general have only subcover periodicity.
-/


-- @@ L27-27 verbatim
section


-- @@ L29-36 verbatim
/-!
# A common-torus signed request with native wave geometry

The torus-averaged signed request is independent of the free fast coordinate
and angle at which it is evaluated. The common state can therefore be kept on
its original torus while the primary wave uses native fast coordinates.
Freezing the band index preserves every actual derivative and average.
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
namespace NavierStokes.TorusMeanRequestRebase


-- @@ L44-44 verbatim
open Set Function WeightedClasses CorrectionState

-- @@ L45-45 verbatim
open scoped Topology ContDiff


-- @@ L47-48 verbatim
/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point

-- @@ L49-50 verbatim
/-- Cylinder: an abbreviation for `PhysicalSignedWave.Cylinder`. -/
abbrev Cylinder := PhysicalSignedWave.Cylinder

-- @@ L51-52 verbatim
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane


-- @@ L54-54 verbatim
section Freeze


-- @@ L56-56 verbatim
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L58-65 verbatim
/-- Freeze strip as an element of `StripData D`. -/
noncomputable def freezeStrip (s : StripData D) (m : ℕ) : StripData D :=
  { s with
    epsilon := fun _ => s.epsilon m
    epsilon_pos := fun _ => s.epsilon_pos m
    epsilon_le_one := fun _ => s.epsilon_le_one m
    slow := fun _ => s.slow m
    one_le_slow := fun _ => s.one_le_slow m }


-- @@ L67-70 verbatim
/-- Freeze triple, given by `⟨fun _ => v.radial m, fun _ => v.angular m, fun _ => v.axial m⟩`. -/
noncomputable def freezeTriple (v : MeanIncrementBounds.Triple D) (m : ℕ) :
    MeanIncrementBounds.Triple D :=
  ⟨fun _ => v.radial m, fun _ => v.angular m, fun _ => v.axial m⟩


-- @@ L72-81 verbatim
/-- Freeze context, bundling `operators`, `epsilon`, `radialFrequency`, `fastCoefficient` and
the required compatibility proofs. -/
noncomputable def freezeContext (c : Context D) (m : ℕ) : Context D where
  operators := { c.operators with
    epsilon := fun _ => c.operators.epsilon m
    radialFrequency := fun _ => c.operators.radialFrequency m
    fastCoefficient := fun _ => c.operators.fastCoefficient m }
  base := freezeTriple c.base m
  virtualTheta := fun _ => c.virtualTheta m
  virtualAxial := fun _ => c.virtualAxial m


-- @@ L83-91 verbatim
/-- Freeze state, bundling `mean`, `pressure`, `oscillation`, `oscillatoryPressure` and the
required compatibility proofs. -/
noncomputable def freezeState (u : State D) (m : ℕ) : State D where
  mean := freezeTriple u.mean m
  pressure := fun _ => u.pressure m
  oscillation := fun _ => u.oscillation m
  oscillatoryPressure := fun _ => u.oscillatoryPressure m
  errors := ⟨fun _ => u.errors.base m, fun _ => u.errors.gaussian m,
    fun _ => u.errors.aliasError m⟩


-- @@ L93-104 verbatim
/-- Freeze wave, bundling `radius`, `radialBase`, `frequencyBase`, `axialBase` and the required
compatibility proofs. -/
noncomputable def freezeWave (a : LinearWaveBounds.WaveCoefficients D) (m : ℕ) :
    LinearWaveBounds.WaveCoefficients D where
  radius := fun _ => a.radius m
  radialBase := fun _ => a.radialBase m
  frequencyBase := fun _ => a.frequencyBase m
  axialBase := fun _ => a.axialBase m
  phase := fun _ => a.phase m
  amplitude := fun _ => a.amplitude m
  pressure := fun _ => a.pressure m
  frequency := fun _ => a.frequency m


-- @@ L106-110 verbatim
/-- Freeze directions, given by `{ d with radialScale := fun _ => d.radialScale m, fastScale :=
fun _ => d.fastScale m }`. -/
noncomputable def freezeDirections (d : LinearWaveBounds.GraphDirections D) (m : ℕ) :
    LinearWaveBounds.GraphDirections D :=
  { d with radialScale := fun _ => d.radialScale m, fastScale := fun _ => d.fastScale m }


-- @@ L112-113 verbatim
@[simp] theorem freezeStrip_domain (s : StripData D) (m : ℕ) :
    (freezeStrip s m).domain = s.domain := rfl


-- @@ L115-116 verbatim
@[simp] theorem freezeStrip_epsilon (s : StripData D) (m n : ℕ) :
    (freezeStrip s m).epsilon n = s.epsilon m := rfl


-- @@ L118-120 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem freezeState_covariance (u : State D) (m n : ℕ) (i j : Fin 3) :
    (freezeState u m).covariance i j n = u.covariance i j m := rfl


-- @@ L122-123 verbatim
@[simp] theorem freezeState_theta (c : Context D) (u : State D) (m n : ℕ) :
    (freezeState u m).thetaResidual (freezeContext c m) n = u.thetaResidual c m := rfl


-- @@ L125-126 verbatim
@[simp] theorem freezeState_axial (c : Context D) (u : State D) (m n : ℕ) :
    (freezeState u m).axialResidual (freezeContext c m) n = u.axialResidual c m := rfl


-- @@ L128-129 verbatim
@[simp] theorem freezeContext_frame (c : Context D) (m n : ℕ) :
    HarmonicResidual.contextFrame (freezeContext c m) n = HarmonicResidual.contextFrame c m := rfl


-- @@ L131-135 verbatim
theorem freezeState_coherent (u : State D) (m n nr : ℕ) (U : Set D) :
    PhysicalResidualNaturality.StateOn U (ContinuousLinearEquiv.refl ℝ D) 1 1
      (freezeState u m) (freezeState u m) n nr := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [PhysicalResidualNaturality.ScalarOn, freezeState, freezeTriple]


-- @@ L137-142 verbatim
theorem freezeContext_coherent (c : Context D) (m n nr : ℕ) (U : Set D) :
    PhysicalResidualNaturality.ContextOn U (ContinuousLinearEquiv.refl ℝ D) 1 1
      (freezeContext c m) (freezeContext c m) n nr := by
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [freezeContext_frame]
  all_goals simp [PhysicalResidualNaturality.ScalarOn, freezeContext, freezeTriple]


-- @@ L144-144 verbatim
end Freeze


-- @@ L146-146 verbatim
/-! ## The evaluation point carries no torus or angle dependence -/


-- @@ L148-152 verbatim
theorem fullRequest_free_variables (s : StripData Point) (P : SignedStressPrimitive.Patch)
    (coord : ℝ) (c : Context Point) (u : State Point) (n : ℕ)
    (r : ℝ) (z Y Y' : Plane) (theta theta' : ℝ) :
    LocalSignedRequest.fullRequest s P coord c u n ((r, (z, Y)), theta) =
      LocalSignedRequest.fullRequest s P coord c u n ((r, (z, Y')), theta') := rfl


-- @@ L154-158 verbatim
theorem stateRequest_free_variables (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (n : ℕ)
    (r : ℝ) (z Y Y' : Plane) (theta theta' : ℝ) :
    PhysicalSignedWave.stateRequest s P h c u n ((r, (z, Y)), theta) =
      PhysicalSignedWave.stateRequest s P h c u n ((r, (z, Y')), theta') := rfl


-- @@ L160-167 verbatim
/-- This changes only the evaluation point, not the state or the measure
used for its torus average. The fast-coordinate map can be arbitrary. -/
theorem stateRequest_fast_map (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (n : ℕ)
    (mapFast : Plane → Plane) (x : Cylinder) :
    PhysicalSignedWave.stateRequest s P h c u n
      ((x.1.1, (x.1.2.1, mapFast x.1.2.2)), x.2) =
      PhysicalSignedWave.stateRequest s P h c u n x := rfl


-- @@ L169-173 verbatim
theorem stateRequest_inverseCover (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (n gap : ℕ) (x : Cylinder) :
    PhysicalSignedWave.stateRequest s P h c u n
      ((x.1.1, (x.1.2.1, (CommonCoverSolve.coverPower gap).symm x.1.2.2)), x.2) =
      PhysicalSignedWave.stateRequest s P h c u n x := rfl


-- @@ L175-184 verbatim
/-- Equality uses exactly the source and target epsilons. No equality of
their unrelated domains, phase frames, or native backgrounds is needed. -/
theorem stateRequest_freeze (s sr : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (m n : ℕ)
    (hepsilon : sr.epsilon n = s.epsilon m) (x : Cylinder) :
    PhysicalSignedWave.stateRequest sr P h (freezeContext c m) (freezeState u m) n x =
      PhysicalSignedWave.stateRequest s P h c u m x := by
  change (sr.epsilon n)⁻¹ • _ = (s.epsilon m)⁻¹ • _
  rw [hepsilon]
  rfl


-- @@ L186-193 verbatim
theorem stateRequest_freeze_full (s : StripData Point) (sr : StripData Cylinder)
    (P : SignedStressPrimitive.Patch) (h : ℝ) (c : Context Point) (u : State Point) (m n : ℕ)
    (hepsilon : sr.epsilon n = s.epsilon m) (x : Cylinder) :
    PhysicalSignedWave.stateRequest sr P h (freezeContext c m) (freezeState u m) n x =
      LocalSignedRequest.fullRequest s P (2 * h) c u m (PhysicalResidualTZ.swapCylinder x) := by
  change (sr.epsilon n)⁻¹ • _ = (s.epsilon m)⁻¹ • _
  rw [hepsilon]
  rfl


-- @@ L195-200 verbatim
@[simp] theorem stateRequest_freezeStrip (s : StripData Cylinder) (P : SignedStressPrimitive.Patch)
    (h : ℝ) (c : Context Point) (u : State Point) (m n : ℕ) (x : Cylinder) :
    PhysicalSignedWave.stateRequest (freezeStrip s m) P h (freezeContext c m) (freezeState u m) n x
        =
      PhysicalSignedWave.stateRequest s P h c u m x :=
  stateRequest_freeze s (freezeStrip s m) P h c u m n rfl x


-- @@ L202-202 verbatim
/-! ## Identity band views of the native primary -/


-- @@ L204-206 verbatim
theorem ratioPower_self {Q : ℝ} (hQ : 0 < Q) (a : ℝ) :
    PhysicalParticularWave.ratioPower Q Q a = 1 :=
  div_self (Real.rpow_pos_of_pos hQ a).ne'


-- @@ L208-210 verbatim
theorem slowChange_self (h : ℝ) {Q : ℝ} (hQ : 0 < Q) (z : Plane) :
    PhysicalSignedWave.slowChange h Q Q z = z := by
  simp [PhysicalSignedWave.slowChange, ratioPower_self hQ]


-- @@ L212-216 verbatim
theorem requestChart_self (h : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    PhysicalSignedWave.requestChart h hQ hQ 0 = ContinuousLinearEquiv.refl ℝ Point := by
  ext x <;>
  simp [PhysicalSignedWave.requestChart_apply, ratioPower_self hQ, slowChange_self h hQ,
    TemporalMeanUpdate.coverMap]


-- @@ L218-218 verbatim
variable {U : PhaseJetBounds.Domain ℕ PhaseCalculus.Slow}


-- @@ L220-236 verbatim
/-- The dummy band index repeats one physical scale and one native cover.
Every coordinate change is the identity; the supplied primary is retained. -/
noncomputable def identityViews (B : PhysicalSignedWave.PrimaryData U) (m : ℕ)
    (h Q : ℝ) (cover : ℕ) (hQ : 0 < Q) (hfrequency : B.base.frequency m ≠ 0) : B.Views m where
  exponent := h
  referenceScale := Q
  referenceScale_pos := hQ
  referenceCover := cover
  scale _ := Q
  scale_pos _ := hQ
  cover _ := cover
  cover_le _ := le_rfl
  frequency _ := B.base.frequency m
  frequency_ne _ := hfrequency
  strip := B.strip
  directions := B.directions
  background := B.base


-- @@ L238-243 verbatim
@[simp] theorem identityViews_map (B : PhysicalSignedWave.PrimaryData U) (m : ℕ)
    (h Q : ℝ) (cover : ℕ) (hQ : 0 < Q) (hfrequency : B.base.frequency m ≠ 0)
    (n : ℕ) (x : Cylinder) :
    (identityViews B m h Q cover hQ hfrequency).map n x = x := by
  simp [PhysicalSignedWave.PrimaryData.Views.map, identityViews,
    PhysicalParticularWave.cylinderChange, ratioPower_self hQ, CommonCoverSolve.coverPower]


-- @@ L245-248 verbatim
@[simp] theorem identityViews_velocity (B : PhysicalSignedWave.PrimaryData U) (m : ℕ)
    (h Q : ℝ) (cover : ℕ) (hQ : 0 < Q) (hfrequency : B.base.frequency m ≠ 0) (n : ℕ) :
    (identityViews B m h Q cover hQ hfrequency).velocity n = 1 :=
  ratioPower_self hQ _


-- @@ L250-250 verbatim
/-! ## The actual common state supplies the request of these native views -/


-- @@ L252-252 verbatim
section IdentityStateData


-- @@ L254-261 verbatim
variable (B : PhysicalSignedWave.PrimaryData U) (m : ℕ)
  (h Q : ℝ) (cover : ℕ) (hQ : 0 < Q) (hfrequency : B.base.frequency m ≠ 0)
  (hh : 0 < h) (hh1 : h < 1 / 2)
  (R : LocalSignedRequest.SlowRegion (2 * h)) (P : SignedStressPrimitive.Patch)
  (c : Context Point) (u : State Point)
  (H : MeanStateRegularity.PrimitiveData R P.a P.b c u)
  (hp : GaugeMomentBalances.MovingField R P.a P.b u.pressure)
  (hslow : ∀ x ∈ B.strip.domain, (x.1.2.1.2, x.1.2.1.1) ∈ R.carrier)


-- @@ L263-307 verbatim
/-- Both stored states and both contexts are the same frozen common objects.
Only their dummy band index is changed. The native primary is left intact.
Residual regularity and periodicity are derived from the primitive data. -/
noncomputable def stateData : (identityViews B m h Q cover hQ hfrequency).StateData where
  patch := P
  context := freezeContext c m
  referenceContext := freezeContext c m
  current := freezeState u m
  referenceState := freezeState u m
  exponent_pos := hh
  exponent_lt_half := hh1
  domain _ := PhysicalMeanDomain.slowDomain R.carrier
  domain_open _ := PhysicalMeanDomain.slowDomain_open R.isOpen
  state_coherent n := by
    change PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain R.carrier)
      (PhysicalSignedWave.requestChart h hQ hQ (cover - cover))
      (PhysicalParticularWave.velocityWeight h Q Q) (PhysicalParticularWave.ratioPower Q Q (1 / 2))
      (freezeState u m) (freezeState u m) n m
    simp only [Nat.sub_self, requestChart_self, PhysicalParticularWave.velocityWeight,
        ratioPower_self hQ]
    exact freezeState_coherent u m n m _
  context_coherent n := by
    change PhysicalResidualNaturality.ContextOn (PhysicalMeanDomain.slowDomain R.carrier)
      (PhysicalSignedWave.requestChart h hQ hQ (cover - cover))
      (PhysicalParticularWave.velocityWeight h Q Q) (PhysicalParticularWave.ratioPower Q Q (1 / 2))
      (freezeContext c m) (freezeContext c m) n m
    simp only [Nat.sub_self, requestChart_self, PhysicalParticularWave.velocityWeight,
        ratioPower_self hQ]
    exact freezeContext_coherent c m n m _
  time_pos x hx := R.time_pos _ (hslow x hx)
  fibers _ x hx _ _ := hslow x hx
  referenceSlow _ := R.carrier
  referenceSlow_open _ := R.isOpen
  referenceSlow_mem _ x hx := by
    change PhysicalSignedWave.slowChange h Q Q (x.1.2.1.2, x.1.2.1.1) ∈ R.carrier
    rw [slowChange_self h hQ]
    exact hslow x hx
  reference_theta_smooth _ := by
    simpa only [freezeState_theta] using (H.theta P.a_pos P.a_lt_b).smooth m
  reference_axial_smooth _ := by
    simpa only [freezeState_axial] using (H.axial P.a_pos P.a_lt_b hp).smooth m
  reference_theta_periodic _ := by
    simpa only [freezeState_theta] using (H.theta P.a_pos P.a_lt_b).periodic m
  reference_axial_periodic _ := by
    simpa only [freezeState_axial] using (H.axial P.a_pos P.a_lt_b hp).periodic m


-- @@ L309-313 verbatim
theorem stateData_request (s : StripData Cylinder) (n : ℕ)
    (hepsilon : B.strip.epsilon n = s.epsilon m) (x : Cylinder) :
    (stateData B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow).request n x =
      PhysicalSignedWave.stateRequest s P h c u m x :=
  stateRequest_freeze s B.strip P h c u m n hepsilon x


-- @@ L315-319 verbatim
theorem stateData_referenceRequest (s : StripData Cylinder)
    (hepsilon : B.strip.epsilon m = s.epsilon m) (x : Cylinder) :
    (stateData B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow).referenceRequest m x =
      PhysicalSignedWave.stateRequest s P h c u m x :=
  stateRequest_freeze s B.strip P h c u m m hepsilon x


-- @@ L321-327 verbatim
/-- Exact binding to the original common-coordinate full signed request.
The swap only puts the slow coordinates into their original `(time,axial)` order. -/
theorem stateData_referenceRequest_full (s : StripData Point)
    (hepsilon : B.strip.epsilon m = s.epsilon m) (x : Cylinder) :
    (stateData B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow).referenceRequest m x =
      LocalSignedRequest.fullRequest s P (2 * h) c u m (PhysicalResidualTZ.swapCylinder x) :=
  stateRequest_freeze_full s B.strip P h c u m m hepsilon x


-- @@ L329-336 verbatim
theorem stateData_referenceRequest_fast (s : StripData Point)
    (hepsilon : B.strip.epsilon m = s.epsilon m) (mapFast : Plane → Plane) (x : Cylinder) :
    (stateData B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow).referenceRequest m x =
      LocalSignedRequest.fullRequest s P (2 * h) c u m
        (PhysicalResidualTZ.swapCylinder ((x.1.1, (x.1.2.1, mapFast x.1.2.2)), x.2)) := by
  rw [stateData_referenceRequest_full B m h Q cover hQ hfrequency hh hh1 R P c u H hp hslow s
      hepsilon x]
  rfl


-- @@ L338-338 verbatim
end IdentityStateData


-- @@ L340-340 verbatim
end NavierStokes.TorusMeanRequestRebase


-- @@ L342-342 verbatim
end

-- @@ L343-343 verbatim
end


-- @@ L345-345 verbatim
end


-- @@ L347-347 verbatim
@[expose] public section


-- @@ L349-349 verbatim
noncomputable section


-- @@ L351-351 verbatim
namespace NavierStokes.ActualSignedPhysicalBinding


-- @@ L353-353 verbatim
open Set Function Filter WeightedClasses CorrectionState TorusMeanRequestRebase

-- @@ L354-354 verbatim
open scoped ContDiff Topology BigOperators


-- @@ L356-357 verbatim
/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point

-- @@ L358-359 verbatim
/-- Cylinder: an abbreviation for `PhysicalSignedWave.Cylinder`. -/
abbrev Cylinder := PhysicalSignedWave.Cylinder

-- @@ L360-361 verbatim
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

-- @@ L362-363 verbatim
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane

-- @@ L364-365 verbatim
/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space

-- @@ L366-368 verbatim
/-- Label: an abbreviation for `ActualSignedStageControls.SignedLabel B N0 open
CorrectionInitialization CorrectionInitialization.ActualPrimary`. -/
abbrev Label (B N0 : ℕ) := ActualSignedStageControls.SignedLabel B N0


-- @@ L370-370 verbatim
open CorrectionInitialization CorrectionInitialization.ActualPrimary


-- @@ L372-372 verbatim
variable {B N0 : ℕ}


-- @@ L374-375 verbatim
/-- Reference, given by `BaseChartJets.cellBand l.1`. -/
noncomputable def reference (l : Label B N0) : ℕ := BaseChartJets.cellBand l.1


-- @@ L377-381 verbatim
/-- Domain, given by `ActualParticularStageControls.reindexDomain
(PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N) (fun _ => l.1)`. -/
noncomputable def domain (l : Label B N0) : PhaseJetBounds.Domain ℕ Slow :=
  ActualParticularStageControls.reindexDomain
    (PrimaryGeometryAssembly.domain nominal (choice B N0).prepared.N) (fun _ => l.1)


-- @@ L383-387 verbatim
/-- Pulse, given by `ActualParticularStageControls.reindexConstruction (phases B N0 j) (fun _ =>
l.1)`. -/
noncomputable def pulse (l : Label B N0) (j : Fin 2) :
    PrimaryPulseBounds.PhaseConstruction (domain l) :=
  ActualParticularStageControls.reindexConstruction (phases B N0 j) (fun _ => l.1)


-- @@ L389-390 verbatim
@[simp] theorem pulse_frame (l : Label B N0) (j : Fin 2) (n : ℕ) :
    (pulse l j).frame n = (phases B N0 j).frame l.1 := rfl


-- @@ L392-395 verbatim
/-- Spatial label, given by `PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label
nominal l.1) l.2`. -/
noncomputable def spatialLabel (l : Label B N0) : SlotColoring.Label :=
  PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal l.1) l.2


-- @@ L397-399 verbatim
/-- Geometry, given by `ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0`. -/
noncomputable def geometry (l : Label B N0) : CommonCoverSolve.Geometry :=
  ActualSignedGeometry.slotGeometry slots vectors_det (spatialLabel l) 0


-- @@ L401-404 verbatim
/-- Native clock, given by `PeriodicPhaseAssembly.periodicClock (geometry l) (clockWindow
l.1).cutoff Y`. -/
noncomputable def nativeClock (l : Label B N0) (Y : Plane) : ℝ :=
  PeriodicPhaseAssembly.periodicClock (geometry l) (clockWindow l.1).cutoff Y


-- @@ L406-411 verbatim
/-- Native free coordinates mapped to the actual common reference lift. -/
noncomputable def toCommon (l : Label B N0) : Point ≃L[ℝ] Point :=
  (CorrectionStep.cycleAssoc.toContinuousLinearEquiv.trans
    (ActualReferenceRebase.inverseCover
      (ChartScales.nativeIndex h (reference l) - CommonWindow.index h (reference l)))).trans
        CorrectionStep.cycleAssoc.symm.toContinuousLinearEquiv


-- @@ L413-417 verbatim
/-- To common cylinder, given by `PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv.trans
((toCommon l).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))`. -/
noncomputable def toCommonCylinder (l : Label B N0) : Cylinder ≃L[ℝ] Cylinder :=
  PhysicalResidualTZ.swapCylinder.toContinuousLinearEquiv.trans
    ((toCommon l).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))


-- @@ L419-422 verbatim
@[simp] theorem toCommon_apply (l : Label B N0) (x : Point) :
    toCommon l x = (x.1, (x.2.1,
      (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
        CommonWindow.index h (reference l))).symm x.2.2)) := rfl


-- @@ L424-427 verbatim
@[simp] theorem toCommonCylinder_apply (l : Label B N0) (x : Cylinder) :
    toCommonCylinder l x = ((x.1.1, ((x.1.2.1.2, x.1.2.1.1),
      (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
        CommonWindow.index h (reference l))).symm x.1.2.2)), x.2) := rfl


-- @@ L429-435 verbatim
@[simp] theorem toCommonCylinder_symm_apply (l : Label B N0) (x : Cylinder) :
    (toCommonCylinder l).symm x = ((x.1.1, ((x.1.2.1.2, x.1.2.1.1),
      CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
        CommonWindow.index h (reference l)) x.1.2.2)), x.2) := by
  apply (toCommonCylinder l).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, toCommonCylinder_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]


-- @@ L437-441 verbatim
/-- Strip, constructed using `freezeStrip`. -/
noncomputable def strip (l : Label B N0) : StripData Cylinder :=
  freezeStrip (ParticularWaveBounds.reindexStrip PhysicalResidualTZ.swapCylinder
    (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal standardRegion)))
      (reference l)


-- @@ L443-447 verbatim
/-- Base, given by `freezeWave (ActualReferenceRebase.pullWave (toCommonCylinder l)
(chartCoefficients l.2 l.1)) (reference l)`. -/
noncomputable def base (l : Label B N0) : LinearWaveBounds.WaveCoefficients Cylinder :=
  freezeWave (ActualReferenceRebase.pullWave (toCommonCylinder l)
    (chartCoefficients l.2 l.1)) (reference l)


-- @@ L449-452 verbatim
/-- Directions, constructed using `freezeDirections`. -/
noncomputable def directions (l : Label B N0) : LinearWaveBounds.GraphDirections Cylinder :=
  freezeDirections (ActualReferenceRebase.pullDirections (toCommonCylinder l)
    (PrimaryResidualClass.directions (commonContext B))) (reference l)


-- @@ L454-468 verbatim
/-- Actual selected primary data. Only the dummy index is repeated. -/
noncomputable def primary (l : Label B N0) : PhysicalSignedWave.PrimaryData (domain l) where
  strip := strip l
  base := base l
  directions := directions l
  pulse := pulse l
  prefactor j _ := prefactor j l.1
  coordinate _ x := ((x.1.1, x.1.2.1), nativeClock l x.1.2.2 / (phases B N0 0).L l.1)
  target _ x := fun q => PrimaryTargetBounds.actualTarget modulation (x.1.1, x.1.2.1) q
  mask _ x := spatialMask l.1 (x.1.1, x.1.2.1)
  normalMotion _ x := (phases B N0 l.2).phase.velocity l.1
    ((x.1.1, x.1.2.1), nativeClock l x.1.2.2)
  action _ x := PrimaryCopyBridge.baseOperator
    ((phases B N0 l.2).phase.F l.1 (x.1.1, x.1.2.1))
    ((phases B N0 l.2).phase.shear l.1 ((x.1.1, x.1.2.1), nativeClock l x.1.2.2))


-- @@ L470-474 verbatim
/-- All dummy bands describe this one native physical reference. -/
noncomputable def nativeViews (l : Label B N0) : (primary l).Views (reference l) :=
  identityViews (primary l) (reference l) h (ChartScales.Q (reference l))
    (ChartScales.nativeIndex h (reference l)) (ChartScales.Q_pos _)
      (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'


-- @@ L476-481 verbatim
@[simp] theorem nativeViews_map (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (nativeViews l).map n x = x := by
  simp [PhysicalSignedWave.PrimaryData.Views.map, nativeViews, identityViews,
    PhysicalParticularWave.cylinderChange, ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos
        _),
    CommonCoverSolve.coverPower]


-- @@ L483-485 verbatim
@[simp] theorem nativeViews_velocity (l : Label B N0) (n : ℕ) :
    (nativeViews l).velocity n = 1 := by
  exact ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _


-- @@ L487-488 verbatim
@[simp] theorem primary_frequency (l : Label B N0) (n : ℕ) :
    (primary l).base.frequency n = (ChartScales.carrier h (reference l) : ℝ) := rfl


-- @@ L490-491 verbatim
@[simp] theorem primary_epsilon (l : Label B N0) (n : ℕ) :
    (primary l).strip.epsilon n = ChartScales.epsilon h (reference l) := rfl


-- @@ L493-496 verbatim
theorem primary_matrix (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (primary l).matrix n x = covariance B N0 l.1 (x.1.1, x.1.2.1) := by
  rw [covariance_eq_integral]
  rfl


-- @@ L498-506 verbatim
theorem native_change_cancel (l : Label B N0) (x : Cylinder) :
    PhysicalParticularWave.cylinderChange h (ChartScales.Q (reference l))
      (ChartScales.Q (reference l))
      (ChartScales.nativeIndex h (reference l) - CommonWindow.index h (reference l))
      (PhysicalResidualTZ.swapCylinder (toCommonCylinder l x)) = x := by
  simp [PhysicalParticularWave.cylinderChange_apply, PhysicalParticularWave.chartChange_apply,
    toCommonCylinder, toCommon, PhysicalResidualTZ.swapCylinder_apply,
    PhysicalResidualTZ.swapSlow_apply, ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _),
    CorrectionStep.cycleAssoc, ActualReferenceRebase.inverseCover, ParticularWaveBounds.liftAssoc]


-- @@ L508-528 verbatim
theorem primary_phase (l : Label B N0) (n : ℕ) :
    (primary l).base.phase n =
      ActualSignedGeometry.periodicPhase slots (spatialLabel l) 0
        (ChartScales.epsilon h (reference l)) ((pulse l l.2).phase.p (reference l))
        ((pulse l l.2).phase.pz (reference l)) ((pulse l l.2).phase.x0 (reference l))
        ((pulse l l.2).phase.F (reference l)) ((pulse l l.2).phase.G (reference l)) := by
  funext x
  change (chartCoefficients l.2 l.1).phase (reference l) (toCommonCylinder l x) = _
  rw [chartCoefficients_phase_view l.2 l.1 (reference l) (CommonWindow.index_le_native h _)]
  unfold ActualSignedGeometry.preparedViewPhase
  change ((ChartScales.carrier h (reference l) : ℝ) / ChartScales.carrier h (reference l)) *
    ActualSignedGeometry.preparedPhase certificate modulation slots (choice B N0).prepared l.2 l.1
      (PhysicalParticularWave.cylinderChange h (ChartScales.Q (reference l)) (ChartScales.Q
          (reference l))
        (ChartScales.nativeIndex h (reference l) - CommonWindow.index h (reference l))
        (PhysicalResidualTZ.swapCylinder (toCommonCylinder l x))) = _
  rw [native_change_cancel l x]
  have hK : (ChartScales.carrier h (reference l) : ℝ) ≠ 0 :=
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
  rw [div_self hK, one_mul]
  rfl


-- @@ L530-535 verbatim
/-- The native record retains the exact annular domain; it is not an empty
or shrinking domain chosen to make the reference data vacuous. -/
theorem primary_domain (l : Label B N0) (x : Cylinder) :
    x ∈ (primary l).strip.domain ↔
      PhysicalResidualTZ.swapSlow x.1 ∈
        (BaseContextAssembly.nativeStrip nominal standardRegion).domain := Iff.rfl


-- @@ L537-539 verbatim
theorem primary_time_pos (l : Label B N0) {x : Cylinder}
    (hx : x ∈ (primary l).strip.domain) : 0 < x.1.2.1.2 :=
  BaseContextAssembly.nativeStrip_time nominal standardRegion hx


-- @@ L541-544 verbatim
theorem primary_slow_mem (l : Label B N0) {x : Cylinder}
    (hx : x ∈ (primary l).strip.domain) : (x.1.2.1.2, x.1.2.1.1) ∈ standardRegion.carrier :=
  ((BaseContextAssembly.nativeStrip_mem nominal standardRegion
    (PhysicalResidualTZ.swapSlow x.1)).mp hx).1


-- @@ L546-589 verbatim
theorem primary_radial (l : Label B N0) (n : ℕ) :
    (primary l).directions.radialField n =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q (reference l)) h
        (ChartScales.nativeIndex h (reference l))).radial := by
  funext x
  simp only [primary, directions, freezeDirections,
    LinearWaveBounds.GraphDirections.radialField, ActualReferenceRebase.pullDirections,
    ← map_smul, ← map_add]
  change (toCommonCylinder l).symm
    ((PrimaryResidualClass.directions (commonContext B)).radialField (reference l)
      (toCommonCylinder l x)) = _
  have hr := ActualPrimaryCoherence.chart_radial_swap B (reference l) (toCommonCylinder l x)
  apply (toCommonCylinder l).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply PhysicalResidualTZ.swapCylinder.injective
  rw [hr]
  simp only [PhysicalResidualBridge.ScaledGraph.radial, PhysicalResidualBridge.commonGraph,
      one_div, toCommonCylinder, toCommon, CorrectionStep.cycleAssoc,
          ParticularWaveBounds.liftAssoc, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
              ActualReferenceRebase.inverseCover, LinearIsometryEquiv.symm_symm,
                  ContinuousLinearEquiv.trans_apply,
                      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
                          PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply,
                              ContinuousLinearEquiv.prodCongr_apply,
                                  LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
                                      LinearIsometryEquiv.coe_prodAssoc_symm,
                                          Equiv.prodAssoc_symm_apply,
                                              ContinuousLinearEquiv.refl_apply,
                                                  LinearIsometryEquiv.coe_prodAssoc,
                                                      Equiv.prodAssoc_apply, Prod.mk.eta, map_smul,
                                                          Prod.mk.injEq, true_and, and_true]
  apply (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
    CommonWindow.index h (reference l))).injective
  simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply]
  rw [show CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
      CommonWindow.index h (reference l)) PhysicalGraphBounds.radialDirection =
      ChartScales.Lambda ^ (ChartScales.nativeIndex h (reference l) - CommonWindow.index h
          (reference l)) •
        PhysicalGraphBounds.radialDirection from CommonBaseContext.coverPower_radial _,
    smul_smul]
  congr 1
  have hi := Nat.add_sub_of_le (CommonWindow.index_le_native h (reference l))
  conv_rhs => rw [← hi, pow_add]
  ring


-- @@ L591-595 verbatim
theorem primary_angular (l : Label B N0) :
    (primary l).directions.angular = ((0, 1) : Cylinder) := by
  change (toCommonCylinder l).symm (0, 1) = _
  simp only [toCommonCylinder_symm_apply, Prod.fst_zero, Prod.snd_zero, map_zero]
  rfl


-- @@ L597-606 verbatim
theorem primary_axial (l : Label B N0) (n : ℕ) :
    (primary l).directions.axialField (primary l).strip n =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q (reference l)) h
        (ChartScales.nativeIndex h (reference l))).axial := by
  funext x
  change (primary l).strip.epsilon n •
    (toCommonCylinder l).symm (((0, ((0, 1), 0)), 0) : Cylinder) = _
  rw [primary_epsilon, toCommonCylinder_symm_apply]
  simp [PhysicalResidualBridge.ScaledGraph.axial, PhysicalResidualBridge.commonGraph,
      ChartScales.epsilon]


-- @@ L608-613 verbatim
theorem primary_chart (l : Label B N0) (n : ℕ) :
    PhysicalSignedWave.ChartGeometry (primary l).base (primary l).strip (primary l).directions n
      h (ChartScales.Q (reference l)) (ChartScales.nativeIndex h (reference l)) := by
  refine ⟨rfl, primary_radial l n, ?_, primary_axial l n⟩
  funext x
  exact primary_angular l


-- @@ L615-626 verbatim
/-- The actual current common state supplies the torus-mean request. The
primitive hypotheses concern only the real local incoming fields. -/
noncomputable def nativeStateData (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    (nativeViews l).StateData :=
  TorusMeanRequestRebase.stateData (primary l) (reference l) h (ChartScales.Q (reference l))
    (ChartScales.nativeIndex h (reference l)) (ChartScales.Q_pos _)
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
    outgoing.data.h_pos outgoing.data.h_lt_half standardRegion P (commonContext B) u H hp
    (fun _ hx => primary_slow_mem l hx)


-- @@ L628-642 verbatim
theorem nativeStateData_referenceRequest (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) (x : Cylinder) :
    (nativeStateData l P u H hp).referenceRequest (reference l) x =
      LocalSignedRequest.fullRequest (BaseContextAssembly.nativeStrip nominal standardRegion)
        P (2 * h) (commonContext B) u (reference l) (toCommonCylinder l x) :=
  TorusMeanRequestRebase.stateData_referenceRequest_fast (primary l) (reference l) h
    (ChartScales.Q (reference l)) (ChartScales.nativeIndex h (reference l)) (ChartScales.Q_pos _)
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
    outgoing.data.h_pos outgoing.data.h_lt_half standardRegion P (commonContext B) u H hp
    (fun _ hx => primary_slow_mem l hx)
    (BaseContextAssembly.nativeStrip nominal standardRegion) rfl
    (CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
      CommonWindow.index h (reference l))).symm x


-- @@ L644-666 verbatim
theorem primary_phase_affine (l : Label B N0) (n : ℕ) :
    CopyAngularInvariance.AffinePhase (0, 1)
      ((PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared l.2 l.1 :
          ℤ) /
        (primary l).base.frequency n) ((primary l).base.phase n) := by
  have hK : (ChartScales.carrier h (reference l) : ℝ) ≠ 0 :=
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
  have he := PrimaryGeometryAssembly.carrier_mul_phase_p certificate modulation
    (choice B N0).prepared slots.radius_pos l.2 l.1
  have hp : (pulse l l.2).phase.p (reference l) =
      (PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared l.2 l.1 :
          ℝ) /
        (ChartScales.carrier h (reference l) : ℝ) := by
    apply (eq_div_iff hK).mpr
    simp only [mul_comm]
    exact he
  rw [primary_phase, primary_frequency]
  intro x t
  simp only [ActualSignedGeometry.periodicPhase, PhaseCalculus.phase,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_zero, add_zero, smul_eq_mul, mul_one]
  rw [hp]
  ring


-- @@ L668-682 verbatim
/-- Primary angular, bundling `mode`, `phase`, `coordinate`, `target` and the required
compatibility proofs. -/
noncomputable def primaryAngular (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    (primary l).Angular (nativeStateData l P u H hp).referenceRequest (reference l) where
  mode := PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared l.2 l.1
  phase := primary_phase_affine l (reference l)
  coordinate := by intro x t; simp [primary]
  target := by intro x t; simp [primary]
  request := PhysicalSignedWave.stateRequest_invariant _ _ _ _ _ _
  mask := by intro x t; simp [primary]
  normalMotion := by intro x t; simp [primary]
  action := by intro x t; simp [primary]


-- @@ L684-684 verbatim
/-! The same individual native copy as the frozen signed stage. -/


-- @@ L686-687 verbatim
theorem label_large (l : Label B N0) : 4 ≤ (spatialLabel l).1 :=
  ActualPrimaryBounds.label_large (l.2, l.1)


-- @@ L689-692 verbatim
/-- Layout, given by `ActualSignedPhysicalData.layout slots outgoing.data.h_pos.le (spatialLabel
l) (label_large l) 0`. -/
noncomputable def layout (l : Label B N0) : ActualPeriodizedSignedRealization.Layout :=
  ActualSignedPhysicalData.layout slots outgoing.data.h_pos.le (spatialLabel l) (label_large l) 0


-- @@ L694-695 verbatim
@[simp] theorem layout_geometry (l : Label B N0) (n : ℕ) :
    (layout l).geometry n = geometry l := rfl


-- @@ L697-698 verbatim
@[simp] theorem layout_window (l : Label B N0) (n : ℕ) :
    (layout l).window n = clockWindow l.1 := rfl


-- @@ L700-701 verbatim
@[simp] theorem pulse_length (l : Label B N0) (j : Fin 2) (n : ℕ) :
    (pulse l j).L n = ChartScales.slotLength slots.radius h (reference l) := rfl


-- @@ L703-706 verbatim
/-- Native copy point, given by `((x.1.1, x.1.2.1), (geometry l).coordinates k x.1.2.2)`. -/
noncomputable def nativeCopyPoint (l : Label B N0) (k : TorusInverse.Frequency)
    (x : Cylinder) : ActualSignedGeometry.Native :=
  ((x.1.1, x.1.2.1), (geometry l).coordinates k x.1.2.2)


-- @@ L708-722 verbatim
theorem nativePoint_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.nativePoint l (reference l) k (toCommonCylinder l x) =
      nativeCopyPoint l k x := by
  apply Prod.ext
  · exact nativeSlow_toAbsolute l.1 ((toCommonCylinder l x).1)
  · change (ActualPrimary.geometry l.2 l.1).coordinates k
      ((CommonCoverSolve.coverPower (CommonWindow.index h (reference l))).symm
        ((CommonCoverSolve.coverPower (ChartScales.nativeIndex h (reference l) -
          CommonWindow.index h (reference l))).symm x.1.2.2)) = _
    rw [chartGeometry_coordinates (reference l) l.2 l.1 (CommonWindow.index_le_native h _)]
    rw [← ActualCarrierTransportBase.reference_refine l (reference l)]
    rw [CopySolveCompatibility.coordinates_refine]
    dsimp only [ActualCarrierTransportBase.gap, reference]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl


-- @@ L724-734 verbatim
@[simp] theorem signed_coefficientScale_reference (l : Label B N0) :
    ActualSignedStageControls.coefficientScale l (reference l) = 1 := by
  unfold ActualSignedStageControls.coefficientScale
  change PhysicalSignedWave.coefficientScale (ChartScales.epsilon h (reference l))
    (ChartScales.epsilon h (reference l))
    (PhysicalParticularWave.velocityWeight h (ChartScales.Q (reference l))
      (ChartScales.Q (reference l))) = 1
  rw [show PhysicalParticularWave.velocityWeight h (ChartScales.Q (reference l))
      (ChartScales.Q (reference l)) = 1 from
        ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _]
  simp [PhysicalSignedWave.coefficientScale, (Real.sqrt_pos.mpr (ChartScales.epsilon_pos h _)).ne']


-- @@ L736-738 verbatim
@[simp] theorem signed_clockScale_reference (l : Label B N0) :
    ActualSignedStageControls.clockScale l (reference l) = 1 :=
  ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _


-- @@ L740-749 verbatim
@[simp] theorem signed_normalScale_reference (l : Label B N0) :
    ActualSignedStageControls.normalScale l (reference l) = 1 := by
  unfold ActualSignedStageControls.normalScale PhysicalParticularWave.normalWeight
  change ((ChartScales.carrier h (reference l) : ℝ) / ChartScales.carrier h (reference l)) *
    PhysicalParticularWave.ratioPower (ChartScales.Q (reference l))
      (ChartScales.Q (reference l)) (1 / 2) = 1
  rw [ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _]
  have hK : (ChartScales.carrier h (reference l) : ℝ) ≠ 0 :=
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
  simp [hK]


-- @@ L751-755 verbatim
theorem signed_matrix_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.matrix l k (reference l) (toCommonCylinder l x) =
      (primary l).matrix (reference l) x := by
  rw [ActualSignedStageControls.matrix, nativePoint_reference, primary_matrix]
  rfl


-- @@ L757-762 verbatim
theorem signed_target_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.target l k (reference l) (toCommonCylinder l x) =
      (primary l).target (reference l) x := by
  rw [ActualSignedStageControls.target, signed_coefficientScale_reference, nativePoint_reference]
  simp only [one_pow, one_smul]
  rfl


-- @@ L764-768 verbatim
theorem signed_mask_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.mask l k (reference l) (toCommonCylinder l x) =
      (primary l).mask (reference l) x := by
  rw [ActualSignedStageControls.mask, nativePoint_reference]
  rfl


-- @@ L770-776 verbatim
theorem signed_unit_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.fundamental l k (reference l) (toCommonCylinder l x) =
      ActualPeriodizedSignedRealization.nativeUnit (primary l) (layout l) (nativeViews l)
        l.2 k (reference l) x := by
  rw [ActualSignedStageControls.fundamental, nativePoint_reference]
  simp only [ActualPeriodizedSignedRealization.nativeUnit, nativeViews_map]
  rfl


-- @@ L778-783 verbatim
theorem signed_cutoff_reference (l : Label B N0) (k : TorusInverse.Frequency) (x : Cylinder) :
    ActualSignedStageControls.cutoff l k (reference l) (toCommonCylinder l x) =
      PartitionedCovariance.cutoff slots.radius ((geometry l).coordinates k x.1.2.2).1 *
        (layout l).nativeGaussian (reference l) k x.1.2.2 := by
  rw [ActualSignedStageControls.cutoff, nativePoint_reference]
  rfl


-- @@ L785-790 verbatim
theorem nativeClock_on_core (l : Label B N0) (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core) :
    nativeClock l x.1.2.2 = ((geometry l).coordinates k x.1.2.2).2 := by
  exact (PeriodicPhaseAssembly.periodicClock_germ (P := Slow) (geometry l) (clockWindow l.1)
    (ActualSignedGeometry.clockWindow_injective slots vectors_det outgoing.data.h_pos.le
      (label_large l) 0) k (z := ((x.1.1, x.1.2.1), x.1.2.2)) hx).self_of_nhds


-- @@ L792-802 verbatim
theorem signed_normalMotion_reference (l : Label B N0) (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core) :
    ActualSignedStageControls.normalMotion l k (reference l) (toCommonCylinder l x) =
      (primary l).normalMotion (reference l) x := by
  rw [ActualSignedStageControls.normalMotion, signed_normalScale_reference,
    signed_clockScale_reference, nativePoint_reference]
  simp only [one_mul, one_smul]
  change _ = (phases B N0 l.2).phase.velocity l.1
    ((x.1.1, x.1.2.1), nativeClock l x.1.2.2)
  rw [nativeClock_on_core l k hx]
  rfl


-- @@ L804-813 verbatim
theorem signed_action_reference (l : Label B N0) (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core) :
    ActualSignedStageControls.action l k (reference l) (toCommonCylinder l x) =
      (primary l).action (reference l) x := by
  rw [ActualSignedStageControls.action, signed_clockScale_reference, nativePoint_reference]
  simp only [one_smul]
  change _ = PrimaryCopyBridge.baseOperator _
    ((phases B N0 l.2).phase.shear l.1 ((x.1.1, x.1.2.1), nativeClock l x.1.2.2))
  rw [nativeClock_on_core l k hx]
  rfl


-- @@ L815-821 verbatim
/-- The lower endpoint is the integration anchor; the physical carrier
retains the individual copy midpoint. -/
theorem carrier_midpoint (l : Label B N0) (k : TorusInverse.Frequency) :
    ActualSignedPhysicalData.center (h := h) (spatialLabel l) k =
      (geometry l).center + TorusAverages.latticePoint k + slots.radius •
          ActualSignedGeometry.temporalVector :=
  ActualSignedPhysicalData.center_eq_anchor slots (spatialLabel l) 0 k


-- @@ L823-828 verbatim
theorem primary_radial_pull (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (primary l).directions.radialField n x =
      (toCommonCylinder l).symm ((PrimaryResidualClass.directions (commonContext B)).radialField
        (reference l) (toCommonCylinder l x)) := by
  simp only [primary, directions, freezeDirections, ActualReferenceRebase.pullDirections,
    LinearWaveBounds.GraphDirections.radialField, map_add, map_smul]


-- @@ L830-838 verbatim
theorem primary_axial_pull (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (primary l).directions.axialField (primary l).strip n x =
      (toCommonCylinder l).symm ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
            standardRegion))
          (reference l) (toCommonCylinder l x)) := by
  simp only [primary, directions, freezeDirections, ActualReferenceRebase.pullDirections,
    LinearWaveBounds.GraphDirections.axialField, map_smul]
  rfl


-- @@ L840-868 verbatim
/-- Actual Fréchet derivatives transform with the native frame; no smoothness
of the raw phase outside its active domain is postulated. -/
theorem primary_normal_reference (l : Label B N0) (n : ℕ) (x : Cylinder) :
    (primary l).base.normal (primary l).strip (primary l).directions n x =
      (chartCoefficients l.2 l.1).normal
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
            standardRegion))
        (PrimaryResidualClass.directions (commonContext B)) (reference l) (toCommonCylinder l x) :=
            by
  unfold LinearWaveBounds.WaveCoefficients.normal
  have he := ActualPrimaryCoherence.phaseNormal_equiv (toCommonCylinder l) one_ne_zero
    ((primary l).base.radius n) ((chartCoefficients l.2 l.1).radius (reference l))
    ((primary l).directions.radialField n) (fun _ => (primary l).directions.angular)
    ((primary l).directions.axialField (primary l).strip n)
    ((PrimaryResidualClass.directions (commonContext B)).radialField (reference l))
    (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
    ((PrimaryResidualClass.directions (commonContext B)).axialField
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
          standardRegion))
        (reference l))
    (fun _ => by simp only [one_mul]; rfl)
    (fun y => by rw [primary_radial_pull, ContinuousLinearEquiv.apply_symm_apply, one_smul])
    (fun y => by
      change (toCommonCylinder l) ((toCommonCylinder l).symm _) = _
      exact (toCommonCylinder l).apply_symm_apply _)
    (fun y => by rw [primary_axial_pull, ContinuousLinearEquiv.apply_symm_apply, one_smul])
    1 ((chartCoefficients l.2 l.1).phase (reference l)) x
  simp only [one_mul, one_smul] at he
  exact he


-- @@ L870-891 verbatim
theorem nativeView_base (l : Label B N0) :
    (ActualPeriodizedSignedRealization.periodizedPrimary (primary l) (layout l)).viewBase
      (nativeViews l).background (nativeViews l).frequency
      (fun n => (nativeViews l).map n) (reference l) = (primary l).base := by
  have hK : (primary l).base.frequency (reference l) ≠ 0 :=
    (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h _)).ne'
  have hphase : (fun n x => ((primary l).base.frequency (reference l) /
      (nativeViews l).frequency n) * (primary l).base.phase (reference l) ((nativeViews l).map n
          x)) =
      (primary l).base.phase := by
    funext n x
    rw [nativeViews_map]
    change ((primary l).base.frequency (reference l) / (primary l).base.frequency (reference l)) *
        _ = _
    rw [div_self hK, one_mul]
    rfl
  change { (primary l).base with
      frequency := (nativeViews l).frequency
      phase := fun n x => ((primary l).base.frequency (reference l) / (nativeViews l).frequency n) *
        (primary l).base.phase (reference l) ((nativeViews l).map n x) } = _
  rw [hphase]
  rfl


-- @@ L893-894 verbatim
theorem nativeViews_clock (l : Label B N0) (n : ℕ) : (nativeViews l).clock n = 1 :=
  ActualReferenceRebase.ratioPower_self (ChartScales.Q_pos _) _


-- @@ L896-898 verbatim
theorem nativeViews_normal (l : Label B N0) (n : ℕ) : (nativeViews l).normal n = 1 := by
  change ActualSignedStageControls.normalScale l (reference l) = 1
  exact signed_normalScale_reference l


-- @@ L900-915 verbatim
theorem nativeView_target (l : Label B N0) :
    (ActualPeriodizedSignedRealization.periodizedPrimary (primary l) (layout l)).viewTarget
      (nativeViews l).strip (nativeViews l).velocity (fun n => (nativeViews l).map n) (reference l)
          =
      (primary l).target := by
  funext n x
  simp only [PhysicalSignedWave.PrimaryData.viewTarget, nativeViews_velocity, nativeViews_map]
  change PhysicalSignedWave.coefficientScale (ChartScales.epsilon h (reference l))
    (ChartScales.epsilon h (reference l)) 1 ^ 2 • (primary l).target (reference l) x = _
  have he : PhysicalSignedWave.coefficientScale (ChartScales.epsilon h (reference l))
      (ChartScales.epsilon h (reference l)) 1 = 1 := by
    unfold PhysicalSignedWave.coefficientScale
    simp [(Real.sqrt_pos.mpr (ChartScales.epsilon_pos h (reference l))).ne']
  rw [he]
  simp only [one_pow, one_smul]
  rfl


-- @@ L917-924 verbatim
/-- Native coefficients, constructed using `SignedWaveUpdate.coefficients`. -/
noncomputable def nativeCoefficients (l : Label B N0)
    (R : ℕ → Cylinder → SignedWaveUpdate.Vec2) (k : TorusInverse.Frequency) :
    LinearWaveBounds.WaveCoefficients Cylinder :=
  SignedWaveUpdate.coefficients (primary l).base (primary l).strip (primary l).directions
    (primary l).matrix (primary l).target R (primary l).mask
    (ActualPeriodizedSignedRealization.nativeUnit (primary l) (layout l) (nativeViews l) l.2 k)
    (primary l).normalMotion (primary l).action l.2


-- @@ L926-931 verbatim
/-- The scalar and the reference copy family are definable before proving
their regularity. No proof or independently chosen request is stored. -/
noncomputable def nativeRequest (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point) : ℕ → Cylinder → SignedWaveUpdate.Vec2 :=
  PhysicalSignedWave.stateRequest (primary l).strip P h
    (freezeContext (commonContext B) (reference l)) (freezeState u (reference l))


-- @@ L933-937 verbatim
/-- Native copies, constructed using `ActualSignedPhysicalData.dynamicCopyData`. -/
noncomputable def nativeCopies (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point) : PeriodizedWaveBounds.CopyData Cylinder TorusInverse.Frequency :=
  ActualSignedPhysicalData.dynamicCopyData slots outgoing.data.h_pos.le (spatialLabel l)
    (label_large l) 0 (primary l) (nativeViews l) (nativeRequest l P u) l.2


-- @@ L939-943 verbatim
theorem nativeStateData_request_eq (l : Label B N0) (P : SignedStressPrimitive.Patch)
    (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    (nativeStateData l P u H hp).referenceRequest = nativeRequest l P u := rfl


-- @@ L945-967 verbatim
theorem dynamicCoefficients_eq (l : Label B N0)
    (R : ℕ → Cylinder → SignedWaveUpdate.Vec2) (k : TorusInverse.Frequency) :
    ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
      (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l) R l.2 k =
      nativeCoefficients l R k := by
  change ActualPeriodizedSignedRealization.coefficientsWith (primary l) (layout l) (nativeViews l)
    R l.2 (ActualPeriodizedSignedRealization.sharedMask (primary l) (nativeViews l))
    (ActualPeriodizedSignedRealization.nativeUnit (primary l) (layout l) (nativeViews l) l.2 k) = _
  unfold ActualPeriodizedSignedRealization.coefficientsWith nativeCoefficients
  rw [nativeView_base, nativeView_target]
  congr 1
  · funext n x
    simp only [nativeViews_map]
    rfl
  · funext n x
    simp only [ActualPeriodizedSignedRealization.sharedMask, nativeViews_map]
    rfl
  · funext n x
    simp only [nativeViews_normal, nativeViews_clock, nativeViews_map, one_mul, one_smul]
    rfl
  · funext n x
    simp only [nativeViews_clock, nativeViews_map, one_smul]
    rfl


-- @@ L969-969 verbatim
section LocalizedComparison


-- @@ L971-973 verbatim
variable (l : Label B N0) (P : SignedStressPrimitive.Patch) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)


-- @@ L975-978 verbatim
/-- Reference copies, constructed using `ActualSignedPhysicalData.dynamicCopyData`. -/
noncomputable def referenceCopies : PeriodizedWaveBounds.CopyData Cylinder TorusInverse.Frequency :=
  ActualSignedPhysicalData.dynamicCopyData slots outgoing.data.h_pos.le (spatialLabel l)
    (label_large l) 0 (primary l) (nativeViews l) (nativeStateData l P u H hp).referenceRequest l.2


-- @@ L980-986 verbatim
/-- Common copies as an element of `PeriodizedWaveBounds.CopyData Cylinder
TorusInverse.Frequency`. -/
noncomputable def commonCopies : PeriodizedWaveBounds.CopyData Cylinder TorusInverse.Frequency :=
  (ActualSignedStageControls.parameters l).copyData
    (BaseContextAssembly.nativeStrip nominal standardRegion)
    (LocalSignedRequest.fullRequest (BaseContextAssembly.nativeStrip nominal standardRegion)
      P (2 * h) (commonContext B) u)


-- @@ L988-1004 verbatim
theorem signedVector_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    SignedWaveUpdate.signedVector
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
          standardRegion))
      (ActualSignedStageControls.matrix l k) (ActualSignedStageControls.target l k)
      (LocalSignedRequest.fullRequest (BaseContextAssembly.nativeStrip nominal standardRegion)
        P (2 * h) (commonContext B) u)
      (ActualSignedStageControls.mask l k) (ActualSignedStageControls.fundamental l k)
      l.2 (reference l) (toCommonCylinder l x) =
    SignedWaveUpdate.signedVector (primary l).strip (primary l).matrix (primary l).target
      (nativeStateData l P u H hp).referenceRequest (primary l).mask
      (ActualPeriodizedSignedRealization.nativeUnit (primary l) (layout l) (nativeViews l) l.2 k)
      l.2 (reference l) x := by
  unfold SignedWaveUpdate.signedVector SignedWaveUpdate.signedScalar
  rw [signed_matrix_reference, signed_target_reference, signed_mask_reference,
    signed_unit_reference, nativeStateData_referenceRequest]
  rfl


-- @@ L1006-1014 verbatim
theorem raw_amplitude_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    (commonCopies l P u).amplitude (reference l) k (toCommonCylinder l x) =
      (referenceCopies l P u H hp).amplitude (reference l) k x := by
  change CurlClassBounds.complexify _ =
    (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
      (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l)
      (nativeStateData l P u H hp).referenceRequest l.2 k).amplitude (reference l) x
  rw [dynamicCoefficients_eq]
  exact congrArg CurlClassBounds.complexify (signedVector_reference l P u H hp k x)


-- @@ L1016-1031 verbatim
theorem raw_pressure_reference (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core) :
    (commonCopies l P u).pressure (reference l) k (toCommonCylinder l x) =
      (referenceCopies l P u H hp).pressure (reference l) k x := by
  change _ = (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
    (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l)
    (nativeStateData l P u H hp).referenceRequest l.2 k).pressure (reference l) x
  rw [dynamicCoefficients_eq]
  dsimp only [commonCopies, CorrectionStep.PeriodizedSignedParameters.copyData,
    CorrectionStep.PeriodizedSignedParameters.native, CorrectionStep.SignedParameters.coefficients,
    ActualSignedStageControls.parameters, nativeCoefficients, SignedWaveUpdate.coefficients,
    SignedWaveUpdate.homogeneousCoefficients, ParticularWaveBounds.projectedPressure,
    ActualSignedStageControls.directions]
  rw [signedVector_reference l P u H hp k x, signed_normalMotion_reference l k hx,
    signed_action_reference l k hx, ← primary_normal_reference l (reference l) x]
  rfl


-- @@ L1033-1039 verbatim
theorem cutoff_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    (commonCopies l P u).cutoff (reference l) k (toCommonCylinder l x) =
      (referenceCopies l P u H hp).cutoff (reference l) k x := by
  change ActualSignedStageControls.cutoff l k (reference l) (toCommonCylinder l x) = _
  rw [signed_cutoff_reference]
  simp only [referenceCopies, ActualSignedPhysicalData.dynamicCopyData, nativeViews_map]
  rfl


-- @@ L1041-1061 verbatim
theorem reference_cutoff_core (k : TorusInverse.Frequency) {x : Cylinder}
    (hx : (referenceCopies l P u H hp).cutoff (reference l) k x ≠ 0) :
    (geometry l).coordinates k x.1.2.2 ∈ (clockWindow l.1).core := by
  have he := PrimaryCopyBounds.profile_mul_outerCutoff
    (((geometry l).coordinates k x.1.2.2).2 / ChartScales.slotLength slots.radius h (reference l))
  have hm : ActualSignedPhysicalData.nativeMask slots (spatialLabel l)
      ((geometry l).coordinates k x.1.2.2) ≠ 0 := by
    intro hm
    apply hx
    change PartitionedCovariance.cutoff slots.radius
      ((geometry l).coordinates k ((nativeViews l).map (reference l) x).1.2.2).1 *
        (layout l).nativeGaussian (reference l) k ((nativeViews l).map (reference l) x).1.2.2 = 0
    rw [nativeViews_map]
    change PartitionedCovariance.cutoff slots.radius ((geometry l).coordinates k x.1.2.2).1 *
      GaussianTailFlat.profile (((geometry l).coordinates k x.1.2.2).2 /
        ChartScales.slotLength slots.radius h (reference l)) = 0
    rw [← he, mul_comm (GaussianTailFlat.profile _), ← mul_assoc]
    change ActualSignedPhysicalData.nativeMask slots (spatialLabel l)
      ((geometry l).coordinates k x.1.2.2) * GaussianTailFlat.profile _ = 0
    rw [hm, zero_mul]
  exact ActualSignedPhysicalData.nativeMask_support slots (spatialLabel l) hm


-- @@ L1063-1068 verbatim
theorem localized_amplitude_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    ((commonCopies l P u).localized k).amplitude (reference l) (toCommonCylinder l x) =
      ((referenceCopies l P u H hp).localized k).amplitude (reference l) x := by
  change (commonCopies l P u).cutoff _ _ _ • (commonCopies l P u).amplitude _ _ _ =
    (referenceCopies l P u H hp).cutoff _ _ _ • (referenceCopies l P u H hp).amplitude _ _ _
  rw [cutoff_reference, raw_amplitude_reference]


-- @@ L1070-1078 verbatim
theorem localized_pressure_reference (k : TorusInverse.Frequency) (x : Cylinder) :
    ((commonCopies l P u).localized k).pressure (reference l) (toCommonCylinder l x) =
      ((referenceCopies l P u H hp).localized k).pressure (reference l) x := by
  change ((commonCopies l P u).cutoff _ _ _ : ℂ) * (commonCopies l P u).pressure _ _ _ =
    ((referenceCopies l P u H hp).cutoff _ _ _ : ℂ) * (referenceCopies l P u H hp).pressure _ _ _
  rw [cutoff_reference l P u H hp]
  by_cases hc : (referenceCopies l P u H hp).cutoff (reference l) k x = 0
  · simp only [hc, Complex.ofReal_zero, zero_mul]
  · rw [raw_pressure_reference l P u H hp k (reference_cutoff_core l P u H hp k hc)]


-- @@ L1080-1081 verbatim
theorem referenceCopies_eq_nativeCopies :
    referenceCopies l P u H hp = nativeCopies l P u := rfl


-- @@ L1083-1090 verbatim
/-- Exact cutoff repartition into the existing compact periodized family. -/
theorem referenceCopies_localized (k : TorusInverse.Frequency) :
    (referenceCopies l P u H hp).localized k =
      (ActualPeriodizedSignedRealization.copyData (primary l) (layout l) (nativeViews l)
        (nativeStateData l P u H hp).referenceRequest l.2).localized k :=
  ActualSignedPhysicalData.dynamic_localized_eq slots outgoing.data.h_pos.le
    (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l)
    (nativeStateData l P u H hp).referenceRequest l.2 k


-- @@ L1092-1097 verbatim
theorem common_amplitude_reference (x : Cylinder) :
    (commonCopies l P u).common.amplitude (reference l) (toCommonCylinder l x) =
      (referenceCopies l P u H hp).common.amplitude (reference l) x := by
  change (∑' k, ((commonCopies l P u).localized k).amplitude (reference l) (toCommonCylinder l x)) =
    ∑' k, ((referenceCopies l P u H hp).localized k).amplitude (reference l) x
  exact tsum_congr (fun k => localized_amplitude_reference l P u H hp k x)


-- @@ L1099-1104 verbatim
theorem common_pressure_reference (x : Cylinder) :
    (commonCopies l P u).common.pressure (reference l) (toCommonCylinder l x) =
      (referenceCopies l P u H hp).common.pressure (reference l) x := by
  change (∑' k, ((commonCopies l P u).localized k).pressure (reference l) (toCommonCylinder l x)) =
    ∑' k, ((referenceCopies l P u H hp).localized k).pressure (reference l) x
  exact tsum_congr (fun k => localized_pressure_reference l P u H hp k x)


-- @@ L1106-1107 verbatim
theorem reference_background : (referenceCopies l P u H hp).background = (primary l).base :=
  nativeView_base l


-- @@ L1109-1114 verbatim
theorem reference_common_normal :
    (referenceCopies l P u H hp).common.normal (primary l).strip (primary l).directions (reference
        l) =
      (primary l).base.normal (primary l).strip (primary l).directions (reference l) := by
  simp only [LinearWaveBounds.WaveCoefficients.normal, PeriodizedWaveBounds.CopyData.common,
    reference_background]


-- @@ L1116-1137 verbatim
theorem curlCoefficient_reference (x : Cylinder) :
    CurlClassBounds.inverseCarrier ((referenceCopies l P u H hp).common.frequency (reference l)) •
      CurlClassBounds.coefficient ((referenceCopies l P u H hp).common.radius (reference l))
        ((primary l).directions.radialField (reference l)) (fun _ => (primary l).directions.angular)
        ((primary l).directions.axialField (primary l).strip (reference l))
        ((referenceCopies l P u H hp).common.phase (reference l))
        ((referenceCopies l P u H hp).common.amplitude (reference l)) x =
    CurlClassBounds.inverseCarrier ((commonCopies l P u).common.frequency (reference l)) •
      CurlClassBounds.coefficient ((commonCopies l P u).common.radius (reference l))
        ((PrimaryResidualClass.directions (commonContext B)).radialField (reference l))
        (fun _ => (PrimaryResidualClass.directions (commonContext B)).angular)
        ((PrimaryResidualClass.directions (commonContext B)).axialField
          (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
              standardRegion))
            (reference l)) ((commonCopies l P u).common.phase (reference l))
        ((commonCopies l P u).common.amplitude (reference l)) (toCommonCylinder l x) := by
  unfold CurlClassBounds.coefficient
  change CurlClassBounds.inverseCarrier _ • CurlClassBounds.normalCoefficient
    ((referenceCopies l P u H hp).common.normal (primary l).strip (primary l).directions
      (reference l) x) ((referenceCopies l P u H hp).common.amplitude (reference l) x) = _
  rw [reference_common_normal, primary_normal_reference, ← common_amplitude_reference]
  rfl


-- @@ L1139-1144 verbatim
theorem reference_phase (x : Cylinder) :
    (referenceCopies l P u H hp).common.phase (reference l) x =
      (commonCopies l P u).common.phase (reference l) (toCommonCylinder l x) := by
  change (referenceCopies l P u H hp).background.phase (reference l) x = _
  rw [reference_background]
  rfl


-- @@ L1146-1161 verbatim
/-- The complete oscillatory curl potential, including its carrier, is the
same native reference. -/
theorem curlPotential_reference (x : Cylinder) :
    (referenceCopies l P u H hp).common.curlPotential (primary l).strip (primary l).directions
      (reference l) x =
    (commonCopies l P u).common.curlPotential
      (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
          standardRegion))
      (PrimaryResidualClass.directions (commonContext B)) (reference l) (toCommonCylinder l x) := by
  funext i
  simp only [LinearWaveBounds.WaveCoefficients.curlPotential, CurlClassBounds.vectorPotential,
    HarmonicCalculus.vectorMode, HarmonicCalculus.mode]
  rw [curlCoefficient_reference]
  unfold HarmonicCalculus.carrier
  rw [reference_phase]
  rfl


-- @@ L1163-1170 verbatim
theorem reference_exactCoefficients :
    (referenceCopies l P u H hp).commonCorrected (primary l).strip (primary l).directions =
      (ActualPeriodizedSignedRealization.views (primary l) (layout l) (nativeViews
          l)).exactCoefficients
        (nativeStateData l P u H hp).referenceRequest l.2 :=
  ActualSignedPhysicalData.dynamic_commonCorrected_eq slots outgoing.data.h_pos.le
    (spatialLabel l) (label_large l) 0 (primary l) (nativeViews l)
    (nativeStateData l P u H hp).referenceRequest l.2


-- @@ L1172-1172 verbatim
end LocalizedComparison


-- @@ L1174-1174 verbatim
/-! Bind to the literal request after the actual particular update. -/


-- @@ L1176-1180 verbatim
/-- After particular, given by `(ActualCycleParameters.fixedParameters B N0).afterParticular
x.coefficients (commonContext B) x.state`. -/
noncomputable def afterParticular (x : CorrectionStep.CycleState (Label B N0)) : State Point :=
  (ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients (commonContext B)
      x.state


-- @@ L1182-1189 verbatim
/-- Cycle state data, given by `nativeStateData l ActualInitialization.patch (afterParticular x)
H hp`. -/
noncomputable def cycleStateData (l : Label B N0) (x : CorrectionStep.CycleState (Label B N0))
    (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (commonContext B) (afterParticular x))
    (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (afterParticular x).pressure) : (nativeViews l).StateData :=
  nativeStateData l ActualInitialization.patch (afterParticular x) H hp


-- @@ L1191-1197 verbatim
theorem afterParticular_pressure (x : CorrectionStep.CycleState (Label B N0))
    (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (commonContext B) (afterParticular x)) :
    GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (afterParticular x).pressure :=
  H.pressure (g := ActualInitialization.geometry.gauge) ActualInitialization.geometry.inner_pos
    ActualInitialization.geometry.exponent_pos ActualInitialization.geometry.length_eq rfl


-- @@ L1199-1206 verbatim
/-- Cycle state data of primitive, given by `cycleStateData l x H (afterParticular_pressure x
H)`. -/
noncomputable def cycleStateDataOfPrimitive (l : Label B N0) (x : CorrectionStep.CycleState (Label
    B N0))
    (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (commonContext B) (afterParticular x)) : (nativeViews
          l).StateData :=
  cycleStateData l x H (afterParticular_pressure x H)


-- @@ L1208-1216 verbatim
theorem cycleStateData_request (l : Label B N0) (x : CorrectionStep.CycleState (Label B N0))
    (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (commonContext B) (afterParticular x))
    (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
      ActualInitialization.patch.b (afterParticular x).pressure) (z : Cylinder) :
    (cycleStateData l x H hp).referenceRequest (reference l) z =
      (ActualCycleParameters.fixedParameters B N0).signedRequest x.coefficients
        (commonContext B) x.state (reference l) (toCommonCylinder l z) :=
  nativeStateData_referenceRequest l ActualInitialization.patch (afterParticular x) H hp z


-- @@ L1218-1218 verbatim
end NavierStokes.ActualSignedPhysicalBinding
