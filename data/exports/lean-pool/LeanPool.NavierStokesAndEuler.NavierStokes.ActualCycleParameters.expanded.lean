/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleExcluded


-- @@ L13-25 verbatim
/-!
# Literal cycle parameters on the initialized labels

The current cycle uses the same primary choice, moving strip, pressure
gauge, index and rank patch as its initialization.  The particular solver
orders the sign before the spatial label; initialization and the signed
solver order it after the spatial label.  The equivalence below transports
the actual finite coefficient family, rather than choosing new labels.

This module constructs the parameters and proves their data identities.
It does not assume or assert the analytic preservation of a correction
cycle.
-/


-- @@ L27-27 verbatim
section


-- @@ L29-35 verbatim
/-!
# The actual fixed geometry for every correction cycle

The numerical data, strip, gauge, and operators below are the ones used by
`ActualInitialization`.  In particular, compatibility with the excluded-alias
estimates is proved independently of the particular and signed wave choices.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
namespace NavierStokes.ActualCycleGeometry


-- @@ L43-43 verbatim
open CorrectionInitialization CorrectionStep WeightedClasses


-- @@ L45-46 verbatim
/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point


-- @@ L48-72 verbatim
/-- Initialization supplies all numerical hypotheses of the similarity
estimates, including the actual finite-window common index. -/
noncomputable def similarityData : ActualCycleExcluded.SimilarityData where
  h := ActualPrimary.h
  h_pos := ActualPrimary.outgoing.data.h_pos
  inner := PrimaryTargetBounds.leftRadius ActualPrimary.nominal
  outer := PrimaryTargetBounds.rightRadius ActualPrimary.nominal
  inner_pos := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  inner_lt_outer := PrimaryTargetBounds.radii_ordered ActualPrimary.nominal
  leftWeight := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4
  rightWeight := 1
  left_pos := div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)
  right_pos := zero_lt_one
  baseScale := 1
  baseScale_ne := one_ne_zero
  region := ActualPrimary.standardRegion
  index := CommonWindow.index ActualPrimary.h
  gap := CommonWindow.gap ActualPrimary.h
  index_lower := CommonWindow.native_le_index_add ActualPrimary.h
      ActualPrimary.outgoing.data.h_pos.le
  index_upper := fun n => (CommonWindow.index_le_native ActualPrimary.h n).trans (Nat.le_add_right
      _ _)
  slow := BaseContextAssembly.slowScale
  slow_one := BaseContextAssembly.one_le_slowScale
  slow_scale := fun _ => le_max_right _ _


-- @@ L74-74 verbatim
theorem strip_eq : similarityData.strip = ActualInitialization.strip := rfl


-- @@ L76-76 verbatim
theorem strip_eq_geometry : similarityData.strip = ActualInitialization.geometry.strip := rfl


-- @@ L78-81 verbatim
/-- The normalization factor is exactly one, so the similarity gauge agrees
with the common reconstruction used by initialization. -/
theorem gauge_eq : similarityData.gauge = ActualPrimary.commonGauge :=
  ActualInitialCoherence.commonGauge_eq_similarity.symm


-- @@ L83-84 verbatim
theorem gauge_eq_geometry : similarityData.gauge = ActualInitialization.geometry.gauge :=
  gauge_eq


-- @@ L86-86 verbatim
theorem region_eq : similarityData.region = ActualInitialization.geometry.region := rfl


-- @@ L88-88 verbatim
theorem inner_eq : similarityData.inner = ActualInitialization.geometry.patch.a := rfl


-- @@ L90-90 verbatim
theorem outer_eq : similarityData.outer = ActualInitialization.geometry.patch.b := rfl


-- @@ L92-92 verbatim
theorem index_eq : similarityData.index = CommonWindow.index ActualPrimary.h := rfl


-- @@ L94-96 verbatim
theorem index_bounds : CommonBaseContext.IndexBounds similarityData.h
    similarityData.index similarityData.gap :=
  CommonWindow.indexBounds ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le


-- @@ L98-98 verbatim
theorem slow_eq : similarityData.slow = BaseContextAssembly.slowScale := rfl


-- @@ L100-100 verbatim
theorem epsilon_eq : similarityData.strip.epsilon = ChartScales.epsilon ActualPrimary.h := rfl


-- @@ L102-104 verbatim
theorem fast_eq (B : ℕ) : (ActualPrimary.commonContext B).operators.fastCoefficient =
    fun n => ChartScales.Tg ^ similarityData.index n *
      ChartScales.Q n ^ (1 + similarityData.h) := rfl


-- @@ L106-107 verbatim
theorem temporal_eq (B : ℕ) : (ActualPrimary.commonContext B).operators.vT =
    (0, (0, TorusInverse.vector .temporal)) := rfl


-- @@ L109-124 verbatim
/-- Changing either wave family leaves the entire similarity certificate
unchanged.  The rank stage is the actual reserved rank construction. -/
theorem compatible {ι : Type} (B : ℕ)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency) :
    ActualCycleExcluded.Compatible similarityData
      (CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
        (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
        particular signed ActualPrimary.rankData)
      (ActualPrimary.commonContext B) where
  gauge := gauge_eq.symm
  strip := strip_eq_geometry.symm
  time := rfl
  index := rfl
  fast := fast_eq B
  temporal := temporal_eq B


-- @@ L126-130 verbatim
/-- The actual operator bounds on precisely the strip in the certificate. -/
theorem operators (B : ℕ) :
    MeanIncrementBounds.OperatorBounds similarityData.strip
      (ActualPrimary.commonContext B).operators ChartScales.kappa :=
  ActualInitialization.operators B


-- @@ L132-135 verbatim
/-- These bounds concern the actual same-profile base in the common context. -/
theorem base_bounds (B : ℕ) :
    MeanIncrementBounds.BaseBounds similarityData.strip (ActualPrimary.commonContext B).base :=
  ActualInitialization.base_bounds B


-- @@ L137-139 verbatim
theorem radius_pos (B : ℕ) (x : Point) (hx : x ∈ similarityData.strip.domain) :
    0 < (ActualPrimary.commonContext B).operators.radius x :=
  ActualInitialization.radius_pos B x hx


-- @@ L141-142 verbatim
theorem strip_time (x : Point) (hx : x ∈ similarityData.strip.domain) : 0 < x.2.1.1 :=
  ActualInitialization.strip_time x hx


-- @@ L144-144 verbatim
end NavierStokes.ActualCycleGeometry


-- @@ L146-146 verbatim
end

-- @@ L147-147 verbatim
end


-- @@ L149-149 verbatim
end


-- @@ L151-151 verbatim
@[expose] public section


-- @@ L153-153 verbatim
noncomputable section


-- @@ L155-155 verbatim
namespace NavierStokes.ActualCycleParameters


-- @@ L157-157 verbatim
open Set Function CorrectionState CorrectionStep CorrectionInitialization

-- @@ L158-158 verbatim
open scoped BigOperators


-- @@ L160-160 verbatim
/-! ## Exact transport of the stored coefficient family -/


-- @@ L162-170 verbatim
/-- Reindex coefficients, bundling `labels`, `blocks`, `gaussian`, `aliasCoefficients` and the
required compatibility proofs. -/
noncomputable def reindexCoefficients {ι κ : Type} (e : κ ≃ ι)
    (v : CycleCoefficients ι) : CycleCoefficients κ where
  labels n := (v.labels n).map e.symm.toEmbedding
  blocks l := v.blocks (e l)
  gaussian l := v.gaussian (e l)
  aliasCoefficients l := v.aliasCoefficients (e l)
  residualBand := v.residualBand


-- @@ L172-177 verbatim
/-- Reindex state, bundling `state`, `coefficients`, `axisymmetricAlias`. -/
noncomputable def reindexState {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) : CycleState κ where
  state := x.state
  coefficients := reindexCoefficients e x.coefficients
  axisymmetricAlias := x.axisymmetricAlias


-- @@ L179-192 verbatim
/-- Reindex parameters, bundling `gauge`, `strip`, `patch`, `coordinate` and the required
compatibility proofs. -/
noncomputable def reindexParameters {ι κ : Type} (e : κ ≃ ι)
    (p : CycleParameters ι) : CycleParameters κ where
  gauge := p.gauge
  strip := p.strip
  patch := p.patch
  coordinate := p.coordinate
  timeExponent := p.timeExponent
  commonIndex := p.commonIndex
  axial := p.axial
  particular l := p.particular (e l)
  signed l := p.signed (e l)
  rank := p.rank


-- @@ L194-198 verbatim
@[simp] theorem reindexCoefficients_mem {ι κ : Type} (e : κ ≃ ι)
    (v : CycleCoefficients ι) (n : ℕ) (l : κ) :
    l ∈ (reindexCoefficients e v).labels n ↔ e l ∈ v.labels n := by
  classical
  simp [reindexCoefficients]


-- @@ L200-201 verbatim
@[simp] theorem reindexState_state {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) : (reindexState e x).state = x.state := rfl


-- @@ L203-204 verbatim
@[simp] theorem reindexState_axis {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) : (reindexState e x).axisymmetricAlias = x.axisymmetricAlias := rfl


-- @@ L206-208 verbatim
@[simp] theorem reindexState_band {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) :
    (reindexState e x).coefficients.residualBand = x.coefficients.residualBand := rfl


-- @@ L210-225 verbatim
theorem reindexCoefficients_symm {ι κ : Type} (e : κ ≃ ι)
    (v : CycleCoefficients ι) :
    reindexCoefficients e.symm (reindexCoefficients e v) = v := by
  classical
  rcases v with ⟨labels, blocks, gaussian, aliasCoefficients, residualBand⟩
  simp only [reindexCoefficients]
  congr 1
  · funext n
    ext l
    simp
  · funext l
    simp
  · funext l
    simp
  · funext l
    simp


-- @@ L227-230 verbatim
theorem reindexState_symm {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) : reindexState e.symm (reindexState e x) = x := by
  rcases x with ⟨state, coefficients, axis⟩
  simp only [reindexState, reindexCoefficients_symm]


-- @@ L232-237 verbatim
theorem reindexCoefficients_sum {ι κ : Type} (e : κ ≃ ι)
    (v : CycleCoefficients ι) {E : Type*} [AddCommMonoid E]
    (n : ℕ) (f : ι → E) :
    (∑ l ∈ (reindexCoefficients e v).labels n, f (e l)) = ∑ l ∈ v.labels n, f l := by
  classical
  simp [reindexCoefficients]


-- @@ L239-252 verbatim
theorem reindexState_representation {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι)
    (H : CycleRepresentation x.coefficients x.state x.axisymmetricAlias) :
    CycleRepresentation (reindexState e x).coefficients (reindexState e x).state
      (reindexState e x).axisymmetricAlias := by
  constructor
  · intro n z i
    simpa [reindexState, reindexCoefficients] using H.velocity n z i
  · intro n z
    simpa [reindexState, reindexCoefficients] using H.pressure n z
  · intro n z i
    simpa [reindexState, reindexCoefficients] using H.gaussian n z i
  · intro n z i
    simpa [reindexState, reindexCoefficients] using H.aliasError n z i


-- @@ L254-258 verbatim
theorem reindexState_bands {ι κ : Type} (e : κ ≃ ι)
    (x : CycleState ι) (H : CoefficientBands x.coefficients) :
    CoefficientBands (reindexState e x).coefficients :=
  ⟨fun l => H.velocityPressure (e l), fun l => H.gaussian (e l),
    fun l => H.aliasError (e l)⟩


-- @@ L260-260 verbatim
/-! ## The two label orders describe the same primary choice -/


-- @@ L262-263 verbatim
/-- Index: an abbreviation for `ActualInitialization.Index B N0`. -/
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

-- @@ L264-265 verbatim
/-- Particular index: an abbreviation for `ActualParticularStageControls.Label B N0`. -/
abbrev ParticularIndex (B N0 : ℕ) := ActualParticularStageControls.Label B N0


-- @@ L267-269 verbatim
/-- Swap, given by `Equiv.prodComm _ _`. -/
noncomputable def swap (B N0 : ℕ) : Index B N0 ≃ ParticularIndex B N0 :=
  Equiv.prodComm _ _


-- @@ L271-271 verbatim
@[simp] theorem swap_apply {B N0 : ℕ} (l : Index B N0) : swap B N0 l = (l.2, l.1) := rfl


-- @@ L273-274 verbatim
@[simp] theorem swap_symm_apply {B N0 : ℕ} (l : ParticularIndex B N0) :
    (swap B N0).symm l = (l.2, l.1) := rfl


-- @@ L276-278 verbatim
/-- Particular state, given by `reindexState (swap B N0).symm x`. -/
noncomputable def particularState {B N0 : ℕ} (x : CycleState (Index B N0)) :
    CycleState (ParticularIndex B N0) := reindexState (swap B N0).symm x


-- @@ L280-281 verbatim
@[simp] theorem particularState_state {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (particularState x).state = x.state := rfl


-- @@ L283-285 verbatim
theorem particularState_blocks {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (particularState x).coefficients.blocks (swap B N0 l) = x.coefficients.blocks l := rfl


-- @@ L287-289 verbatim
theorem particularState_gaussian {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (particularState x).coefficients.gaussian (swap B N0 l) = x.coefficients.gaussian l := rfl


-- @@ L291-294 verbatim
theorem particularState_alias {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (particularState x).coefficients.aliasCoefficients (swap B N0 l) =
      x.coefficients.aliasCoefficients l := rfl


-- @@ L296-300 verbatim
theorem particularState_mem {B N0 : ℕ} (x : CycleState (Index B N0))
    (n : ℕ) (l : Index B N0) :
    swap B N0 l ∈ (particularState x).coefficients.labels n ↔ l ∈ x.coefficients.labels n := by
  simpa only [particularState, reindexState, Equiv.symm_apply_apply] using
    reindexCoefficients_mem (swap B N0).symm x.coefficients n (swap B N0 l)


-- @@ L302-304 verbatim
theorem particularState_roundtrip {B N0 : ℕ} (x : CycleState (Index B N0)) :
    reindexState (swap B N0) (particularState x) = x :=
  reindexState_symm (swap B N0).symm x


-- @@ L306-306 verbatim
/-! ## The actual four-stage parameter constructor -/


-- @@ L308-314 verbatim
/-- Parameters, constructed using `CycleParameters.ofGeometry`. -/
noncomputable def parameters {B N0 : ℕ} (x : CycleState (Index B N0)) :
    CycleParameters (Index B N0) :=
  CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
    (fun l => ActualParticularStageControls.parameters (particularState x) (swap B N0 l))
    ActualSignedStageControls.parameters ActualPrimary.rankData


-- @@ L316-323 verbatim
/-- The same literal builder expressed in the particular solver's label
order.  This has no additional geometric or analytic choices. -/
noncomputable def parametersInParticularOrder {B N0 : ℕ}
    (x : CycleState (ParticularIndex B N0)) : CycleParameters (ParticularIndex B N0) :=
  CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
    (ActualParticularStageControls.parameters x)
    (fun l => ActualSignedStageControls.parameters ((swap B N0).symm l)) ActualPrimary.rankData


-- @@ L325-327 verbatim
theorem parameters_swap {B N0 : ℕ} (x : CycleState (Index B N0)) :
    reindexParameters (swap B N0).symm (parameters x) =
      parametersInParticularOrder (particularState x) := rfl


-- @@ L329-330 verbatim
@[simp] theorem parameters_gauge {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).gauge = ActualPrimary.commonGauge := rfl


-- @@ L332-333 verbatim
@[simp] theorem parameters_strip {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).strip = ActualInitialization.strip := rfl


-- @@ L335-336 verbatim
@[simp] theorem parameters_patch {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).patch = ActualInitialization.patch := rfl


-- @@ L338-339 verbatim
@[simp] theorem parameters_coordinate {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).coordinate = 2 * ActualPrimary.h := rfl


-- @@ L341-342 verbatim
@[simp] theorem parameters_timeExponent {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).timeExponent = ActualPrimary.h := rfl


-- @@ L344-345 verbatim
@[simp] theorem parameters_commonIndex {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).commonIndex = CommonWindow.index ActualPrimary.h := rfl


-- @@ L347-348 verbatim
@[simp] theorem parameters_axial {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).axial = ActualInitialization.axial := rfl


-- @@ L350-351 verbatim
@[simp] theorem parameters_rank {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).rank = ActualPrimary.rankData := rfl


-- @@ L353-356 verbatim
@[simp] theorem parameters_particular {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (parameters x).particular l =
      ActualParticularStageControls.parameters (particularState x) (swap B N0 l) := rfl


-- @@ L358-360 verbatim
@[simp] theorem parameters_signed {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (parameters x).signed l = ActualSignedStageControls.parameters l := rfl


-- @@ L362-365 verbatim
theorem parameters_indexBounds {B N0 : ℕ} (x : CycleState (Index B N0)) :
    CommonBaseContext.IndexBounds ActualPrimary.h (parameters x).commonIndex
      (CommonWindow.gap ActualPrimary.h) :=
  CommonWindow.indexBounds ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le


-- @@ L367-368 verbatim
theorem parameters_geometry_operators {B N0 : ℕ} (_x : CycleState (Index B N0)) :
    ActualInitialization.geometry.operators = (ActualPrimary.commonContext B).operators := rfl


-- @@ L370-375 verbatim
theorem parameters_compatible {B N0 : ℕ} (x : CycleState (Index B N0)) :
    ActualCycleExcluded.Compatible ActualCycleGeometry.similarityData (parameters x)
      (ActualPrimary.commonContext B) :=
  ActualCycleGeometry.compatible B
    (fun l => ActualParticularStageControls.parameters (particularState x) (swap B N0 l))
    ActualSignedStageControls.parameters


-- @@ L377-379 verbatim
/-- The physical band floor belongs to the already selected primary
choice and does not change with the current correction state. -/
noncomputable def bandFloor (B N0 : ℕ) : ℕ := (ActualPrimary.choice B N0).prepared.N


-- @@ L381-382 verbatim
/-- Source band, given by `BaseChartJets.cellBand l.1`. -/
noncomputable def sourceBand {B N0 : ℕ} (l : Index B N0) : ℕ := BaseChartJets.cellBand l.1


-- @@ L384-384 verbatim
theorem bandFloor_ge (B N0 : ℕ) : N0 ≤ bandFloor B N0 := ActualPrimary.threshold B N0


-- @@ L386-387 verbatim
theorem sourceBand_ge_floor {B N0 : ℕ} (l : Index B N0) :
    bandFloor B N0 ≤ sourceBand l := l.1.property


-- @@ L389-390 verbatim
theorem particular_reference_band {B N0 : ℕ} (l : Index B N0) :
    (ActualParticularStageControls.reference (swap B N0 l)).band = sourceBand l := rfl


-- @@ L392-395 verbatim
theorem particular_gap {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ActualParticularStageControls.gap (swap B N0 l) n =
      ChartScales.nativeIndex ActualPrimary.h (sourceBand l) -
        CommonWindow.index ActualPrimary.h n := rfl


-- @@ L397-405 verbatim
theorem activeLabel_band {B N0 : ℕ} (n : ℕ) (l : Index B N0)
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    sourceBand l ∈ CommonWindow.levels n := by
  classical
  have hm := (ActualPrimary.mem_activeLabels ActualPrimary.standardRegion n l.1 l.2).mp hl
  obtain ⟨m, hm, hg⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hg
  have he : m = sourceBand l := congrArg Prod.fst hk
  simpa only [he] using hm


-- @@ L407-411 verbatim
theorem activeLabel_index {B N0 : ℕ} (n : ℕ) (l : Index B N0)
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (sourceBand l) :=
  CommonWindow.index_le (activeLabel_band n l hl)


-- @@ L413-416 verbatim
theorem activeLabel_particular {B N0 : ℕ} (n : ℕ) (hn : 1 ≤ n) (l : Index B N0)
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    1 ≤ n ∧ BaseChartJets.cellBand (swap B N0 l).2 ∈ CommonWindow.levels n :=
  ⟨hn, activeLabel_band n l hl⟩


-- @@ L418-418 verbatim
/-! The particular source really is the current stored residual. -/


-- @@ L420-423 verbatim
theorem particular_assembly_context {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).context =
      StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B) := rfl


-- @@ L425-428 verbatim
theorem particular_assembly_state {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).state =
      StateReindex.state cycleAssoc.symm x.state := rfl


-- @@ L430-433 verbatim
theorem particular_assembly_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).carrierBlock =
      StateReindex.block cycleAssoc.symm (x.coefficients.blocks l) := rfl


-- @@ L435-438 verbatim
theorem particular_assembly_gaussian {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).gaussianInput =
      StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l) := rfl


-- @@ L440-443 verbatim
theorem particular_assembly_alias {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) :
    (ActualParticularStageControls.assembly (particularState x) (swap B N0 l)).aliasInput =
      StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l) := rfl


-- @@ L445-459 verbatim
theorem particular_source {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (j : ℤ) :
    (((parameters x).particular l).copyData
      (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
      (StateReindex.state cycleAssoc.symm x.state)
      (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l))
          j).source =
    ParticularWaveAssembly.sourceFamily
      (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
      (StateReindex.state cycleAssoc.symm x.state)
      (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
      (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)) j := rfl


-- @@ L461-466 verbatim
theorem signed_request {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (parameters x).signedRequest x.coefficients (ActualPrimary.commonContext B) x.state =
      LocalSignedRequest.fullRequest ActualInitialization.strip ActualInitialization.patch
        (2 * ActualPrimary.h) (ActualPrimary.commonContext B)
        ((parameters x).afterParticular x.coefficients (ActualPrimary.commonContext B) x.state) :=
            rfl


-- @@ L468-468 verbatim
/-! ## The signed update uses the initialized primary carrier -/


-- @@ L470-473 verbatim
theorem signed_frequency (p : PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).frequency = p.base.frequency := rfl


-- @@ L475-478 verbatim
theorem signed_phase (p : PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).phase = fun n z => p.base.phase n (z, 0) := rfl


-- @@ L480-483 verbatim
theorem signed_angular (p : PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    (p.exactBlock s request).angularFrequency = p.angularFrequency := rfl


-- @@ L485-487 verbatim
theorem primaryPiece_frequency (p : PrimaryPiece (CyclePoint × ℝ))
    (phase : ℕ → CyclePoint → ℝ) (angular : ℕ → ℤ) :
    (p.harmonicBlock phase angular).frequency = p.coefficients.frequency := rfl


-- @@ L489-491 verbatim
theorem primaryPiece_phase (p : PrimaryPiece (CyclePoint × ℝ))
    (phase : ℕ → CyclePoint → ℝ) (angular : ℕ → ℤ) :
    (p.harmonicBlock phase angular).phase = phase := rfl


-- @@ L493-495 verbatim
theorem primaryPiece_angular (p : PrimaryPiece (CyclePoint × ℝ))
    (phase : ℕ → CyclePoint → ℝ) (angular : ℕ → ℤ) :
    (p.harmonicBlock phase angular).angularFrequency = angular := rfl


-- @@ L497-511 verbatim
theorem signed_primary_carrier {B N0 : ℕ} (l : Index B N0)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    SameCarrier (ActualInitialization.primaryBlock l)
      ((ActualSignedStageControls.parameters l).exactBlock s request) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (signed_frequency (ActualSignedStageControls.parameters l) s request).trans
      (primaryPiece_frequency (ActualInitialization.primaryPiece l)
        (ActualInitialization.phase l) (ActualInitialization.angularMode l)).symm
  · exact (signed_phase (ActualSignedStageControls.parameters l) s request).trans
      (primaryPiece_phase (ActualInitialization.primaryPiece l)
        (ActualInitialization.phase l) (ActualInitialization.angularMode l)).symm
  · exact (signed_angular (ActualSignedStageControls.parameters l) s request).trans
      (primaryPiece_angular (ActualInitialization.primaryPiece l)
        (ActualInitialization.phase l) (ActualInitialization.angularMode l)).symm


-- @@ L513-521 verbatim
theorem signed_tangent_carrier {B N0 : ℕ} (l : Index B N0)
    (s : WeightedClasses.StripData CyclePoint)
    (request : ℕ → CyclePoint × ℝ → SignedWaveUpdate.Vec2) :
    SameCarrier (ActualInitialization.tangentBlock l)
      ((ActualSignedStageControls.parameters l).exactBlock s request) := by
  have hs := signed_primary_carrier l s request
  have hp := ActualInitialization.primary_tangent_carrier l
  exact ⟨hs.frequency.trans hp.frequency.symm, hs.phase.trans hp.phase.symm,
    hs.angular.trans hp.angular.symm⟩


-- @@ L523-530 verbatim
theorem parameters_signed_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).signedBlock x.coefficients c x.state l) := by
  have hs := signed_tangent_carrier l (parameters x).strip
    ((parameters x).signedRequest x.coefficients c x.state)
  exact ⟨hs.frequency.trans H.frequency, hs.phase.trans H.phase, hs.angular.trans H.angular⟩


-- @@ L532-536 verbatim
theorem parameters_particular_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).particularBlock x.coefficients c x.state l) :=
  (parameters x).particular_carrier x.coefficients c x.state l


-- @@ L538-542 verbatim
theorem parameters_gaussian_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).particularGaussianBlock x.coefficients c x.state l) :=
  (parameters x).particularGaussian_carrier x.coefficients c x.state l


-- @@ L544-551 verbatim
theorem invariant_signed_carrier {B N0 : ℕ} {x : CycleState (Index B N0)}
    {P : Index B N0 → ℕ → CyclePoint → ℝ}
    {labelCarrier : Index B N0 → ℕ → Set CyclePoint} {sigma : ℝ}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock P labelCarrier sigma x) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).signedBlock x.coefficients (ActualPrimary.commonContext B) x.state l) :=
  parameters_signed_carrier x _ l (H.carrier l)


-- @@ L553-557 verbatim
theorem initial_signed_carrier (B N0 : ℕ) (l : Index B N0) :
    let x := ActualInitialization.initialCycleState B N0
    SameCarrier (x.coefficients.blocks l)
      ((parameters x).signedBlock x.coefficients (ActualPrimary.commonContext B) x.state l) :=
  parameters_signed_carrier _ _ l (ActualInitialization.primary_tangent_carrier l)


-- @@ L559-559 verbatim
/-! ## The same fixed primitives at every valid state -/


-- @@ L561-566 verbatim
/-- Fixed parameters, constructed using `CycleParameters.ofGeometry`. -/
noncomputable def fixedParameters (B N0 : ℕ) : CycleParameters (Index B N0) :=
  CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
    (fun l => ActualParticularStageControls.canonicalParameters (swap B N0 l))
    ActualSignedStageControls.parameters ActualPrimary.rankData


-- @@ L568-570 verbatim
@[simp] theorem fixedParameters_particular (B N0 : ℕ) (l : Index B N0) :
    (fixedParameters B N0).particular l =
      ActualParticularStageControls.canonicalParameters (l.2, l.1) := rfl


-- @@ L572-573 verbatim
@[simp] theorem fixedParameters_signed (B N0 : ℕ) (l : Index B N0) :
    (fixedParameters B N0).signed l = ActualSignedStageControls.parameters l := rfl


-- @@ L575-576 verbatim
@[simp] theorem fixedParameters_strip (B N0 : ℕ) :
    (fixedParameters B N0).strip = ActualInitialization.geometry.strip := rfl


-- @@ L578-579 verbatim
@[simp] theorem fixedParameters_gauge (B N0 : ℕ) :
    (fixedParameters B N0).gauge = ActualInitialization.geometry.gauge := rfl


-- @@ L581-582 verbatim
@[simp] theorem fixedParameters_patch (B N0 : ℕ) :
    (fixedParameters B N0).patch = ActualInitialization.geometry.patch := rfl


-- @@ L584-585 verbatim
@[simp] theorem fixedParameters_coordinate (B N0 : ℕ) :
    (fixedParameters B N0).coordinate = ActualInitialization.geometry.coord := rfl


-- @@ L587-588 verbatim
@[simp] theorem fixedParameters_timeExponent (B N0 : ℕ) :
    (fixedParameters B N0).timeExponent = ActualPrimary.h := rfl


-- @@ L590-591 verbatim
@[simp] theorem fixedParameters_commonIndex (B N0 : ℕ) :
    (fixedParameters B N0).commonIndex = CommonWindow.index ActualPrimary.h := rfl


-- @@ L593-594 verbatim
@[simp] theorem fixedParameters_axial (B N0 : ℕ) :
    (fixedParameters B N0).axial = ActualInitialization.axial := rfl


-- @@ L596-597 verbatim
@[simp] theorem fixedParameters_rank (B N0 : ℕ) :
    (fixedParameters B N0).rank = ActualPrimary.rankData := rfl


-- @@ L599-604 verbatim
theorem fixedParameters_compatible (B N0 : ℕ) :
    ActualCycleExcluded.Compatible ActualCycleGeometry.similarityData (fixedParameters B N0)
      (ActualPrimary.commonContext B) :=
  ActualCycleGeometry.compatible B
    (fun l => ActualParticularStageControls.canonicalParameters (swap B N0 l))
    ActualSignedStageControls.parameters


-- @@ L606-616 verbatim
theorem current_frequency {B N0 : ℕ} (x : CycleState (Index B N0)) (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) (n : ℕ) :
    (x.coefficients.blocks l).frequency n = ChartScales.carrier ActualPrimary.h n := by
  calc
    _ = (ActualInitialization.tangentBlock l).frequency n := congrFun H.frequency.symm n
    _ = (ActualInitialization.primaryBlock l).frequency n :=
      congrFun (ActualInitialization.primary_tangent_carrier l).frequency n
    _ = (ActualInitialization.primaryPiece l).coefficients.frequency n :=
      congrFun (primaryPiece_frequency (ActualInitialization.primaryPiece l)
        (ActualInitialization.phase l) (ActualInitialization.angularMode l)) n
    _ = _ := rfl


-- @@ L618-623 verbatim
theorem parameters_particular_eq_fixed {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    (parameters x).particular l = (fixedParameters B N0).particular l :=
  ActualParticularStageControls.parameters_eq_canonical (particularState x) (swap B N0 l)
    (current_frequency x l H)


-- @@ L625-633 verbatim
theorem parameters_eq_fixed {B N0 : ℕ} (x : CycleState (Index B N0))
    (H : ∀ l, SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    parameters x = fixedParameters B N0 := by
  have hp : (parameters x).particular = (fixedParameters B N0).particular :=
    funext (fun l => parameters_particular_eq_fixed x l (H l))
  exact congrArg (fun part : Index B N0 → ParticularParameters CycleSlow =>
    CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      part ActualSignedStageControls.parameters ActualPrimary.rankData) hp


-- @@ L635-640 verbatim
theorem invariant_parameters_eq_fixed {B N0 : ℕ} {x : CycleState (Index B N0)}
    {P : Index B N0 → ℕ → CyclePoint → ℝ}
    {labelCarrier : Index B N0 → ℕ → Set CyclePoint} {sigma : ℝ}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock P labelCarrier sigma x) :
    parameters x = fixedParameters B N0 := parameters_eq_fixed x H.carrier


-- @@ L642-644 verbatim
theorem initial_parameters_eq_fixed (B N0 : ℕ) :
    parameters (ActualInitialization.initialCycleState B N0) = fixedParameters B N0 :=
  parameters_eq_fixed _ ActualInitialization.primary_tangent_carrier


-- @@ L646-653 verbatim
theorem fixedParameters_signed_carrier {B N0 : ℕ} (x : CycleState (Index B N0))
    (c : Context CyclePoint) (l : Index B N0)
    (H : SameCarrier (x.coefficients.blocks l) (ActualInitialization.tangentBlock l)) :
    SameCarrier (x.coefficients.blocks l)
      ((fixedParameters B N0).signedBlock x.coefficients c x.state l) := by
  have hs := signed_tangent_carrier l (fixedParameters B N0).strip
    ((fixedParameters B N0).signedRequest x.coefficients c x.state)
  exact ⟨hs.frequency.trans H.frequency, hs.phase.trans H.phase, hs.angular.trans H.angular⟩


-- @@ L655-663 verbatim
theorem invariant_fixedParameters_signed_carrier {B N0 : ℕ} {x : CycleState (Index B N0)}
    {P : Index B N0 → ℕ → CyclePoint → ℝ}
    {labelCarrier : Index B N0 → ℕ → Set CyclePoint} {sigma : ℝ}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock P labelCarrier sigma x) (l : Index B N0) :
    SameCarrier (x.coefficients.blocks l)
      ((fixedParameters B N0).signedBlock x.coefficients (ActualPrimary.commonContext B) x.state l)
          :=
  fixedParameters_signed_carrier x _ l (H.carrier l)


-- @@ L665-665 verbatim
end NavierStokes.ActualCycleParameters
