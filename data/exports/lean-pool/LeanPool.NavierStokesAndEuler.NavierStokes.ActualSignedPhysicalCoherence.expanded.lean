/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedExterior
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurrentSignedCurl
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedCurrentSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedReferenceGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalWaveSum
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalCurlCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPotentialCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPolarCoverage
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedPhysicalData


-- @@ L18-24 verbatim
/-!
# The canonical signed physical family and its current-band realization

The dependent family, both signed labels, and its positive physical harmonic
are retained.  Native faces are treated by the literal zero mask before a
current-band comparison is used.
-/


-- @@ L26-26 verbatim
section


-- @@ L28-34 verbatim
/-!
# Geometry for current signed waves in physical polar charts

The actual active annulus is covered for every band whose physical scale
ratio lies in `(1/2,2)`.  An explicit change of the chart radius identifies
the scaled Cartesian lift with the full native cylindrical graph.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
namespace NavierStokes.ActualSignedPhysicalGeometry


-- @@ L42-42 verbatim
open Set Function Filter ProblemStatement PhysicalWaveSum

-- @@ L43-43 verbatim
open PhysicalGraphBounds PhysicalMeanJetBounds

-- @@ L44-44 verbatim
open CorrectionInitialization CorrectionInitialization.ActualPrimary

-- @@ L45-45 verbatim
open scoped Topology ContDiff


-- @@ L47-76 verbatim
/-- The annulus estimate uses only comparability of the two positive scales,
so it holds throughout the full open native scale window. -/
theorem annulus_of_ratio (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ ActualPolarCoverage.active)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    scaledRadial n w ∈ annulus ActualPolarCoverage.inner ActualPolarCoverage.outer := by
  have hQ := ChartScales.Q_pos n
  have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by
    have he := (div_lt_iff₀ hQ).mp hq.2
    linarith
  have hhi : ChartScales.Q n ≤ 2 * physicalQ h w := by
    have he := (lt_div_iff₀ hQ).mp hq.1
    linarith
  have hell := graph_length_pos outgoing.data.h_pos outgoing.data.h_lt_half n 0 hw
  have hlen := graph_length_bounds outgoing.data.h_pos outgoing.data.h_lt_half n 0 hw hlo hhi
  have hr := ActualPolarCoverage.graph_profileRadius_mem nominal n 0 hw hactive
  have hloR := (le_div_iff₀ hell).mp hr.1
  have hhiR := (div_le_iff₀ hell).mp hr.2
  have ha := PrimaryTargetBounds.leftRadius_pos nominal
  have hb := PrimaryTargetBounds.rightRadius_pos nominal
  have hRlo : PrimaryTargetBounds.leftRadius nominal / 2 ≤ (graph h n 0 w).1 := by
    nlinarith [hlen.1]
  have hRhi : (graph h n 0 w).1 ≤ 2 * PrimaryTargetBounds.rightRadius nominal := by
    nlinarith [hlen.2]
  rw [graph_radius] at hRlo hRhi
  refine ⟨?_, ?_⟩
  · simpa only [ActualPolarCoverage.outer, Metric.mem_closedBall, dist_zero_right] using
      (PolarCharts.norm_le_radius (scaledRadial n w)).trans hRhi
  · change PrimaryTargetBounds.leftRadius nominal / 4 ≤ ‖scaledRadial n w‖
    linarith only [hRlo, PolarCharts.radius_le_two_norm (scaledRadial n w)]


-- @@ L78-85 verbatim
theorem chart_exists_of_ratio (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hactive : w ∈ ActualPolarCoverage.active)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    ∃ j : PolarCharts.Index,
      scaledRadial n w ∈ PolarCharts.chartDomain ActualPolarCoverage.inner j := by
  obtain ⟨j, hj⟩ := PolarCharts.annulus_covered ActualPolarCoverage.inner_pos
    (annulus_of_ratio n hw hactive hq)
  exact ⟨j, PolarCharts.sector_subset_chartDomain ActualPolarCoverage.inner_pos j hj⟩


-- @@ L87-89 verbatim
/-- The exact unscaled chart radius corresponding to a native chart radius. -/
noncomputable def chartRadius (a : ℝ) (n : ℕ) : ℝ :=
  a / ChartScales.Q n ^ (-(1 / 2 : ℝ))


-- @@ L91-92 verbatim
theorem chartRadius_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < chartRadius a n :=
  div_pos ha (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)


-- @@ L94-103 verbatim
theorem chartDomain_unscale {a c : ℝ} (hc : 0 < c) (j : PolarCharts.Index)
    {p : PolarCharts.Plane} (hp : c • p ∈ PolarCharts.chartDomain a j) :
    p ∈ PolarCharts.chartDomain (a / c) j := by
  change a / 4 < (PolarCharts.rotate j (c • p)).1 at hp
  rw [PolarCharts.rotate_smul] at hp
  change a / 4 < c * (PolarCharts.rotate j p).1 at hp
  change (a / c) / 4 < (PolarCharts.rotate j p).1
  calc
    (a / c) / 4 = (a / 4) / c := by ring
    _ < _ := (div_lt_iff₀ hc).mpr (by simpa only [mul_comm] using hp)


-- @@ L105-108 verbatim
theorem physical_chart_mem (n : ℕ) {a : ℝ} (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    radialProjection w ∈ PolarCharts.chartDomain (chartRadius a n) j :=
  chartDomain_unscale (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) j hchart


-- @@ L110-120 verbatim
/-- The scaled and unscaled charts have exactly the same angle. -/
theorem physical_chart_scale (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    PolarCharts.chart a j (scaledRadial n w) =
      (ChartScales.Q n ^ (-(1 / 2 : ℝ)) *
        (PolarCharts.chart (chartRadius a n) j (radialProjection w)).1,
       (PolarCharts.chart (chartRadius a n) j (radialProjection w)).2) := by
  rw [PolarCharts.chart_eq_localChart ha j hchart,
    PolarCharts.chart_eq_localChart (chartRadius_pos ha n) j (physical_chart_mem n j hchart)]
  exact PolarCharts.localChart_smul j (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) _


-- @@ L122-141 verbatim
/-- No angle choice or auxiliary coordinate is discarded by this identity. -/
theorem cylinderAt_physical_chart (h : ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    ActualSignedPhysicalData.cylinderAt a j (physicalLift h n w) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (ChartScales.nativeIndex h n)).map
          (PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w) := by
  have hb := chartRadius_pos ha n
  have hphysical := physical_chart_mem n j hchart
  have hv := ActualSignedPhysicalData.polarCoordinates_valid hb j hphysical
  have he := ActualSignedPhysicalData.polarCoordinates_backward hb j hphysical
  have hc : scaledRadial n
      ((PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w).1,
        CylindricalResidual.chart
          (PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w).2) ∈
        PolarCharts.chartDomain a j := by
    rwa [he]
  simpa only [he] using ActualSignedPhysicalData.cylinderAt_physical_forward h n ha j
    (PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w) hv.1 hv.2.1 hc


-- @@ L143-151 verbatim
theorem exists_physical_chart (h : ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    ∃ b : ℝ, 0 < b ∧ radialProjection w ∈ PolarCharts.chartDomain b j ∧
      ActualSignedPhysicalData.cylinderAt a j (physicalLift h n w) =
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (ChartScales.nativeIndex h n)).map (PhysicalCurlCovariance.polarCoordinates b j w) :=
  ⟨chartRadius a n, chartRadius_pos ha n, physical_chart_mem n j hchart,
    cylinderAt_physical_chart h n ha j hchart⟩


-- @@ L153-161 verbatim
/-- The mean graph's slow coordinate does not depend on its auxiliary cover. -/
theorem graph_slow_mem_standard_of_ratio {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    (graph h n d w).2.1 ∈ (ActualSignedGeometry.standardSlowRegion hh hh1).carrier := by
  change 0 < (graph h n d w).2.1.1 ∧
    SimilarityCoordinates.coordinateQ (2 * h) (graph h n d w).2.1 ∈ Ioo (1 / 2 : ℝ) 2
  refine ⟨graph_time_pos h n d hw, ?_⟩
  rwa [graph_q_eq hh hh1 n d hw]


-- @@ L163-179 verbatim
/-- This identity is global and needs no radius or time positivity premise. -/
theorem commonGraph_slow (h : ℝ) (n i d : ℕ) (z : SpaceTime) :
    (PhysicalResidualTZ.swapCylinder
      ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).map z)).1.2.1 =
      (graph h n d (z.1, CylindricalResidual.chart z.2)).2.1 := by
  rw [graph_slow]
  change
    (((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).velocityScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).radialScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).epsilon) * (1 - z.1),
     ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).radialScale *
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h i).epsilon) * z.2 2) = _
  rw [PhysicalResidualBridge.commonGraph_slowTimeScale (ChartScales.Q_pos n),
    PhysicalResidualBridge.commonGraph_axialScale (ChartScales.Q_pos n), Real.rpow_neg_one]
  simp only [CylindricalResidual.chart, AxisymmetricResidual.pack_two]
  congr 1
  ring


-- @@ L181-184 verbatim
theorem nativePoint_slow (n d : ℕ) (z : SpaceTime) :
    (ActualSignedPotentialCoherence.nativePoint n z).1.2.1 =
      (graph h n d (z.1, CylindricalResidual.chart z.2)).2.1 :=
  commonGraph_slow h n (CommonWindow.index h n) d z


-- @@ L186-193 verbatim
theorem nativePoint_mem_physicalDomain (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hq : physicalQ h (z.1, CylindricalResidual.chart z.2) / ChartScales.Q n ∈
      Ioo (1 / 2 : ℝ) 2) :
    z ∈ ActualSignedPotentialCoherence.physicalDomain n := by
  refine ⟨hr, ?_⟩
  rw [nativePoint_slow n 0]
  exact graph_slow_mem_standard_of_ratio outgoing.data.h_pos outgoing.data.h_lt_half n 0 hw hq


-- @@ L195-206 verbatim
theorem polarCoordinates_mem_physicalDomain (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : radialProjection w ∈ PolarCharts.chartDomain a j)
    (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    PhysicalCurlCovariance.polarCoordinates a j w ∈
      ActualSignedPotentialCoherence.physicalDomain n := by
  have hv := ActualSignedPhysicalData.polarCoordinates_valid ha j hchart
  have he := ActualSignedPhysicalData.polarCoordinates_backward ha j hchart
  apply nativePoint_mem_physicalDomain n _ hv.1
  · rwa [he]
  · rwa [he]


-- @@ L208-216 verbatim
theorem scaledChart_mem_physicalDomain (n : ℕ) {a : ℝ} (ha : 0 < a)
    (j : PolarCharts.Index) {w : SpaceTime}
    (hchart : scaledRadial n w ∈ PolarCharts.chartDomain a j)
    (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2) :
    PhysicalCurlCovariance.polarCoordinates (chartRadius a n) j w ∈
      ActualSignedPotentialCoherence.physicalDomain n :=
  polarCoordinates_mem_physicalDomain n (chartRadius_pos ha n) j
    (physical_chart_mem n j hchart) hw hq


-- @@ L218-218 verbatim
end NavierStokes.ActualSignedPhysicalGeometry


-- @@ L220-220 verbatim
end

-- @@ L221-221 verbatim
end


-- @@ L223-223 verbatim
end


-- @@ L225-225 verbatim
section


-- @@ L227-234 verbatim
/-!
# Zeros of the actual signed physical coefficients

The native dyadic mask vanishes at both faces and outside the open native
band.  This file transfers that literal zero to the canonical physical
copy family and to every current-band representation of the same label.
The current state and the native reference requests are arbitrary.
-/


-- @@ L236-236 verbatim
@[expose] public section


-- @@ L238-238 verbatim
noncomputable section


-- @@ L240-240 verbatim
namespace NavierStokes.ActualSignedPhysicalZeros


-- @@ L242-242 verbatim
open Set Function Filter ProblemStatement PhysicalWaveSum PhysicalCopyBounds

-- @@ L243-243 verbatim
open CorrectionInitialization CorrectionInitialization.ActualPrimary

-- @@ L244-244 verbatim
open ActualSignedExterior

-- @@ L245-245 verbatim
open scoped Topology ContDiff BigOperators


-- @@ L247-248 verbatim
/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label`. -/
abbrev Label := ActualSignedPhysicalBinding.Label

-- @@ L249-250 verbatim
/-- Point: an abbreviation for `ActualSignedCoherence.Point`. -/
abbrev Point := ActualSignedCoherence.Point

-- @@ L251-252 verbatim
/-- Full point: an abbreviation for `ActualSignedCoherence.FullPoint`. -/
abbrev FullPoint := ActualSignedCoherence.FullPoint

-- @@ L253-254 verbatim
/-- Frequency: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Frequency := TorusInverse.Frequency


-- @@ L256-256 verbatim
variable {B N0 : ℕ}


-- @@ L258-268 verbatim
theorem physicalLift_coordinateQ (n : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    SimilarityCoordinates.coordinateQ (2 * h)
      ((ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h n w)).1.2.1.2,
       (ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h n w)).1.2.1.1) =
      physicalQ h w / ChartScales.Q n := by
  have he := congrArg (fun p : PhaseCalculus.Slow => (p.2.2, p.2.1))
    (physicalLift_slow n w)
  change _ = (PhysicalMeanJetBounds.graph h n 0 w).2.1 at he
  dsimp only at he
  rw [he]
  exact PhysicalMeanJetBounds.graph_q_eq outgoing.data.h_pos outgoing.data.h_lt_half n 0 hw


-- @@ L270-276 verbatim
theorem primary_mask_physicalLift_zero (l : Label B N0) (m n : ℕ)
    {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q n ∉ Ioo (1 / 2 : ℝ) 2) :
    (ActualSignedPhysicalBinding.primary l).mask m
      (ActualSignedPhysicalData.cylinderZero (PhysicalGraphBounds.physicalLift h n w)) = 0 := by
  apply ActualSignedNativeRegularity.primary_mask_zero_outside
  rwa [physicalLift_coordinateQ n hw]


-- @@ L278-278 verbatim
section CanonicalFamily


-- @@ L280-280 verbatim
variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)


-- @@ L282-300 verbatim
theorem canonical_potential_amplitude_zero_of_nativeQ (l : Label B N0) (i : Fin 3)
    (k : Frequency) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).amplitude k
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l))
      (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w) = 0 := by
  classical
  change ((family s).copyAt (fun L => ActualSignedPhysicalData.potentialFamily
    slots outgoing.data.h_pos.le ((family s).singleton L) i) (nativeLabel l)).amplitude k _ _ = 0
  erw [DependentSignedPhysicalFamily.Family.copyAt_active]
  by_contra hn
  obtain ⟨_, _, hm, _⟩ := ActualSignedPhysicalData.potential_amplitude_inputs
    slots outgoing.data.h_pos.le ((family s).singleton (nativeLabel l)) i k _ _ hn
  apply hm
  change (ActualSignedPhysicalBinding.primary (actualLabel (nativeLabel l))).mask
    (ActualSignedPhysicalBinding.reference l) _ = 0
  rw [actualLabel_nativeLabel]
  exact primary_mask_physicalLift_zero l _ _ hw hq


-- @@ L302-320 verbatim
theorem canonical_pressure_amplitude_zero_of_nativeQ (l : Label B N0)
    (k : Frequency) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).amplitude k
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l))
      (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w) = 0 := by
  classical
  change ((family s).copyAt (fun L => ActualSignedPhysicalData.pressureFamily
    slots outgoing.data.h_pos.le ((family s).singleton L)) (nativeLabel l)).amplitude k _ _ = 0
  erw [DependentSignedPhysicalFamily.Family.copyAt_active]
  by_contra hn
  obtain ⟨_, _, hm, _⟩ := ActualSignedPhysicalData.pressure_amplitude_inputs
    slots outgoing.data.h_pos.le ((family s).singleton (nativeLabel l)) k _ _ hn
  apply hm
  change (ActualSignedPhysicalBinding.primary (actualLabel (nativeLabel l))).mask
    (ActualSignedPhysicalBinding.reference l) _ = 0
  rw [actualLabel_nativeLabel]
  exact primary_mask_physicalLift_zero l _ _ hw hq


-- @@ L322-334 verbatim
theorem canonical_potential_term_zero_of_nativeQ (l : Label B N0) (i : Fin 3)
    (k : Frequency) (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).term a h r0
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l)) k w = 0 := by
  apply globalWave_eq_zero
  change ((family s).potentialCopies slots outgoing.data.h_pos.le i).amplitude k
    (ActualSignedPhysicalData.positiveIndex (nativeLabel l))
    (commonLift h (ActualSignedPhysicalBinding.reference l)
      (((family s).potentialCopies slots outgoing.data.h_pos.le i).gap (nativeLabel l)) w) = 0
  rw [potential_gap, ActualSignedPhysicalData.commonLift_zero]
  exact canonical_potential_amplitude_zero_of_nativeQ s l i k hw hq


-- @@ L336-348 verbatim
theorem canonical_pressure_term_zero_of_nativeQ (l : Label B N0)
    (k : Frequency) (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).term a h r0
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l)) k w = 0 := by
  apply globalWave_eq_zero
  change ((family s).pressureCopies slots outgoing.data.h_pos.le).amplitude k
    (ActualSignedPhysicalData.positiveIndex (nativeLabel l))
    (commonLift h (ActualSignedPhysicalBinding.reference l)
      (((family s).pressureCopies slots outgoing.data.h_pos.le).gap (nativeLabel l)) w) = 0
  rw [pressure_gap, ActualSignedPhysicalData.commonLift_zero]
  exact canonical_pressure_amplitude_zero_of_nativeQ s l k hw hq


-- @@ L350-357 verbatim
theorem canonical_potential_periodized_zero_of_nativeQ (l : Label B N0) (i : Fin 3)
    (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).potentialCopies slots outgoing.data.h_pos.le i).periodized a h r0
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l)) w = 0 := by
  simp only [CopyFamily.periodized, canonical_potential_term_zero_of_nativeQ s l i _ a r0 hw hq,
    tsum_zero]


-- @@ L359-366 verbatim
theorem canonical_pressure_periodized_zero_of_nativeQ (l : Label B N0)
    (a r0 : ℝ) {w : SpaceTime} (hw : w ∈ preterminal)
    (hq : physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉
      Ioo (1 / 2 : ℝ) 2) :
    ((family s).pressureCopies slots outgoing.data.h_pos.le).periodized a h r0
      (ActualSignedPhysicalData.positiveIndex (nativeLabel l)) w = 0 := by
  simp only [CopyFamily.periodized, canonical_pressure_term_zero_of_nativeQ s l _ a r0 hw hq,
    tsum_zero]


-- @@ L368-368 verbatim
end CanonicalFamily


-- @@ L370-370 verbatim
/-! ## The same native slow point in every current band -/


-- @@ L372-389 verbatim
theorem current_nativeSlow_reference (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : SpaceTime) (hr : 0 < z.2 0) :
    (ActualSignedStageControls.nativePoint l n k
      (ActualSignedPotentialCoherence.nativePoint n z)).1 =
      BaseContextAssembly.slowCoordinates
        (ActualSignedPotentialCoherence.nativePoint (ActualSignedPhysicalBinding.reference l) z).1
            := by
  have he := congrArg Prod.fst
    ((ActualSignedPotentialCoherence.nativePoint_absolute n z hr).trans
      (ActualSignedPotentialCoherence.nativePoint_absolute
        (ActualSignedPhysicalBinding.reference l) z hr).symm)
  change toAbsolute n (ActualSignedPotentialCoherence.nativePoint n z).1 =
    toAbsolute (ActualSignedPhysicalBinding.reference l)
      (ActualSignedPotentialCoherence.nativePoint (ActualSignedPhysicalBinding.reference l) z).1
          at he
  change nativeSlow l.1 (toAbsolute n (ActualSignedPotentialCoherence.nativePoint n z).1) = _
  rw [he]
  exact nativeSlow_toAbsolute l.1 _


-- @@ L391-408 verbatim
theorem nativePoint_slowCoordinates (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0) :
    BaseContextAssembly.slowCoordinates (ActualSignedPotentialCoherence.nativePoint n z).1 =
      ActualSignedPhysicalData.nativeSlow
        (PhysicalMeanJetBounds.graph h n 0 (z.1, CylindricalResidual.chart z.2)) := by
  apply Prod.ext
  · change (ActualSignedPotentialCoherence.nativePoint n z).1.1 =
      (PhysicalMeanJetBounds.graph h n 0 (z.1, CylindricalResidual.chart z.2)).1
    rw [PhysicalMeanJetBounds.graph_radius, ActualSignedPhysicalData.scaledRadial_forward,
      PolarCharts.radius_polar,
      abs_of_pos (mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr)]
    simp only [ActualSignedPotentialCoherence.nativePoint,
      PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos n) h _ hr,
      PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply]
  · change ((ActualSignedPotentialCoherence.nativePoint n z).1.2.1.2,
      (ActualSignedPotentialCoherence.nativePoint n z).1.2.1.1) =
      ((PhysicalMeanJetBounds.graph h n 0 (z.1, CylindricalResidual.chart z.2)).2.1.2,
       (PhysicalMeanJetBounds.graph h n 0 (z.1, CylindricalResidual.chart z.2)).2.1.1)
    rw [ActualSignedPhysicalGeometry.nativePoint_slow n 0]


-- @@ L410-421 verbatim
theorem current_nativeSlow_physicalLift (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : SpaceTime) (hr : 0 < z.2 0) :
    (ActualSignedStageControls.nativePoint l n k
      (ActualSignedPotentialCoherence.nativePoint n z)).1 =
      ((ActualSignedPhysicalData.cylinderZero
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l)
            (z.1, CylindricalResidual.chart z.2))).1.1,
       (ActualSignedPhysicalData.cylinderZero
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l)
            (z.1, CylindricalResidual.chart z.2))).1.2.1) := by
  rw [current_nativeSlow_reference l n k z hr, nativePoint_slowCoordinates _ z hr]
  exact (physicalLift_slow _ _).symm


-- @@ L423-431 verbatim
theorem current_mask_physicalLift (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : SpaceTime) (hr : 0 < z.2 0) :
    ActualSignedStageControls.mask l k n (ActualSignedPotentialCoherence.nativePoint n z) =
      (ActualSignedPhysicalBinding.primary l).mask n
        (ActualSignedPhysicalData.cylinderZero
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l)
            (z.1, CylindricalResidual.chart z.2))) := by
  change spatialMask l.1 _ = spatialMask l.1 _
  rw [current_nativeSlow_physicalLift l n k z hr]


-- @@ L433-443 verbatim
theorem current_target_physicalLift (l : Label B N0) (n : ℕ) (k : Frequency)
    (z : SpaceTime) (hr : 0 < z.2 0) :
    ActualSignedStageControls.target l k n (ActualSignedPotentialCoherence.nativePoint n z) =
      ActualSignedStageControls.coefficientScale l n ^ 2 •
        (ActualSignedPhysicalBinding.primary l).target n
          (ActualSignedPhysicalData.cylinderZero
            (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l)
              (z.1, CylindricalResidual.chart z.2))) := by
  unfold ActualSignedStageControls.target
  rw [current_nativeSlow_physicalLift l n k z hr]
  rfl


-- @@ L445-445 verbatim
/-! ## Passing literal raw zeros through the current copy sum -/


-- @@ L447-459 verbatim
theorem common_zero_of_raw (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (x : FullPoint)
    (hz : ∀ k, (ActualSignedCoherence.copies l u).amplitude n k x = 0 ∧
      (ActualSignedCoherence.copies l u).pressure n k x = 0) :
    (ActualSignedCoherence.copies l u).common.amplitude n x = 0 ∧
      (ActualSignedCoherence.copies l u).common.pressure n x = 0 := by
  constructor
  · change (∑' k, (ActualSignedCoherence.copies l u).cutoff n k x •
      (ActualSignedCoherence.copies l u).amplitude n k x) = 0
    simp only [(hz _).1, smul_zero, tsum_zero]
  · change (∑' k, ((ActualSignedCoherence.copies l u).cutoff n k x : ℂ) *
      (ActualSignedCoherence.copies l u).pressure n k x) = 0
    simp only [(hz _).2, mul_zero, tsum_zero]


-- @@ L461-484 verbatim
theorem cylindrical_zero_of_raw (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime)
    (hz : ∀ k, (ActualSignedCoherence.copies l u).amplitude n k
      (ActualSignedPotentialCoherence.nativePoint n z) = 0 ∧
      (ActualSignedCoherence.copies l u).pressure n k
        (ActualSignedPotentialCoherence.nativePoint n z) = 0) :
    ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 ∧
      ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 := by
  have hc := common_zero_of_raw l u n _ hz
  constructor
  · have hp : ActualSignedPotentialCoherence.potentialCoefficient l u n
        (ActualSignedPotentialCoherence.nativePoint n z) = 0 := by
      simp [ActualSignedPotentialCoherence.potentialCoefficient, hc.1,
        CurlClassBounds.normalCoefficient, CurlClassBounds.normalCross]
    have hv : ActualSignedPotentialCoherence.potential l u n
        (ActualSignedPotentialCoherence.nativePoint n z) = 0 := by
      rw [ActualSignedPotentialCoherence.potential_eq_mode]
      ext i
      simp only [HarmonicCalculus.vectorMode, HarmonicCalculus.mode, hp, Pi.zero_apply, zero_mul]
    rw [ActualSignedPotentialCoherence.cylindricalPotential,
      ActualSignedPotentialCoherence.rescaledPotential, hv, smul_zero]
  · simp [ActualSignedPotentialCoherence.cylindricalPressureMode,
      ActualSignedPotentialCoherence.rescaledPressureMode,
      ActualSignedPotentialCoherence.pressureMode, HarmonicCalculus.mode, hc.2]


-- @@ L486-498 verbatim
theorem current_raw_zero_of_nativeQ (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (k : Frequency) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hq : physicalQ h (z.1, CylindricalResidual.chart z.2) /
      ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2) :
    (ActualSignedCoherence.copies l u).amplitude n k
      (ActualSignedPotentialCoherence.nativePoint n z) = 0 ∧
      (ActualSignedCoherence.copies l u).pressure n k
        (ActualSignedPotentialCoherence.nativePoint n z) = 0 := by
  apply (ActualSignedStageControls.parameters l).raw_zero_of_mask
  change ActualSignedStageControls.mask l k n (ActualSignedPotentialCoherence.nativePoint n z) = 0
  rw [current_mask_physicalLift l n k z hr]
  exact primary_mask_physicalLift_zero l _ _ hw hq


-- @@ L500-506 verbatim
theorem cylindricalPotential_zero_of_nativeQ (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hq : physicalQ h (z.1, CylindricalResidual.chart z.2) /
      ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2) :
    ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 :=
  (cylindrical_zero_of_raw l u n z (fun k => current_raw_zero_of_nativeQ l u n k z hr hw hq)).1


-- @@ L508-514 verbatim
theorem cylindricalPressureMode_zero_of_nativeQ (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hq : physicalQ h (z.1, CylindricalResidual.chart z.2) /
      ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2) :
    ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 :=
  (cylindrical_zero_of_raw l u n z (fun k => current_raw_zero_of_nativeQ l u n k z hr hw hq)).2


-- @@ L516-516 verbatim
/-! ## The fixed physical exterior -/


-- @@ L518-532 verbatim
theorem current_raw_zero_of_exterior (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (k : Frequency) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hout : (z.1, CylindricalResidual.chart z.2) ∉ active) :
    (ActualSignedCoherence.copies l u).amplitude n k
      (ActualSignedPotentialCoherence.nativePoint n z) = 0 ∧
      (ActualSignedCoherence.copies l u).pressure n k
        (ActualSignedPotentialCoherence.nativePoint n z) = 0 := by
  rcases primary_mask_or_target_zero l n (ActualSignedPhysicalBinding.reference l) hw hout with hm
      | ht
  · apply (ActualSignedStageControls.parameters l).raw_zero_of_mask
    change ActualSignedStageControls.mask l k n (ActualSignedPotentialCoherence.nativePoint n z) = 0
    rw [current_mask_physicalLift l n k z hr, hm]
  · apply ActualWaveRegularityData.raw_zero_of_target
    rw [current_target_physicalLift l n k z hr, ht, smul_zero]


-- @@ L534-539 verbatim
theorem cylindricalPotential_zero_of_exterior (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hout : (z.1, CylindricalResidual.chart z.2) ∉ active) :
    ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 :=
  (cylindrical_zero_of_raw l u n z (fun k => current_raw_zero_of_exterior l u n k z hr hw hout)).1


-- @@ L541-546 verbatim
theorem cylindricalPressureMode_zero_of_exterior (l : Label B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0)
    (hw : (z.1, CylindricalResidual.chart z.2) ∈ preterminal)
    (hout : (z.1, CylindricalResidual.chart z.2) ∉ active) :
    ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 :=
  (cylindrical_zero_of_raw l u n z (fun k => current_raw_zero_of_exterior l u n k z hr hw hout)).2


-- @@ L548-548 verbatim
end NavierStokes.ActualSignedPhysicalZeros


-- @@ L550-550 verbatim
end

-- @@ L551-551 verbatim
end


-- @@ L553-553 verbatim
end


-- @@ L555-555 verbatim
section


-- @@ L557-563 verbatim
/-!
# Finite-support sums in physical coordinates

These identities only use finite support and the literal real-coordinate maps.
They let a physical wave assembly retain an unrestricted label `finsum` while
identifying its value with the finite active-label sum.
-/


-- @@ L565-565 verbatim
@[expose] public section


-- @@ L567-567 verbatim
noncomputable section


-- @@ L569-569 verbatim
namespace NavierStokes.SignedPhysicalSumCalculus


-- @@ L571-571 verbatim
open Set Function ProblemStatement HarmonicCalculus

-- @@ L572-572 verbatim
open scoped BigOperators


-- @@ L574-581 verbatim
theorem finsum_eq_sum_of_zero_off {α E : Type*} [AddCommMonoid E]
    (s : Finset α) (f : α → E) (hz : ∀ l, l ∉ s → f l = 0) :
    (∑ᶠ l, f l) = ∑ l ∈ s, f l := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro l hl
  by_contra hn
  exact hl (hz l hn)


-- @@ L583-589 verbatim
theorem sum_realCoordinate (v : ComplexVector) :
    (∑ i : Fin 3, PhysicalWaveSum.realCoordinate i (v i)) =
      PhysicalCurlCovariance.realVector v := by
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_succ, PhysicalWaveSum.realCoordinate_apply,
      coordinateVector, PhysicalCurlCovariance.realVector_apply]


-- @@ L591-599 verbatim
/-- An unrestricted scalar-label sum becomes the finite real-part sum once
the labels outside the specified finite set vanish. -/
theorem real_finsum_eq_sum {α : Type*} (s : Finset α) (p : α → ℂ) (q : α → ℝ)
    (hz : ∀ l, l ∉ s → p l = 0) (hreal : ∀ l, (p l).re = q l) :
    (∑ᶠ l, p l).re = ∑ l ∈ s, q l := by
  rw [finsum_eq_sum_of_zero_off s p hz]
  change Complex.reCLM (∑ l ∈ s, p l) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun l _ => hreal l)


-- @@ L601-620 verbatim
/-- Reconstructing the Euclidean vector after the componentwise label sums
agrees exactly with summing the real vectors of the active labels. -/
theorem realCoordinate_finsum_eq_sum {α : Type*} (s : Finset α)
    (F : α → ComplexVector) (G : α → Space)
    (hz : ∀ l, l ∉ s → F l = 0)
    (hreal : ∀ l, PhysicalCurlCovariance.realVector (F l) = G l) :
    (∑ i : Fin 3, PhysicalWaveSum.realCoordinate i (∑ᶠ l, F l i)) =
      ∑ l ∈ s, G l := by
  classical
  have hs (i : Fin 3) : (∑ᶠ l, F l i) = ∑ l ∈ s, F l i :=
    finsum_eq_sum_of_zero_off s (fun l => F l i) (fun l hl => congrFun (hz l hl) i)
  calc
    _ = ∑ i : Fin 3, ∑ l ∈ s, PhysicalWaveSum.realCoordinate i (F l i) := by
      simp only [hs, map_sum]
    _ = ∑ l ∈ s, ∑ i : Fin 3, PhysicalWaveSum.realCoordinate i (F l i) :=
      Finset.sum_comm
    _ = ∑ l ∈ s, G l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [sum_realCoordinate, hreal]


-- @@ L622-622 verbatim
end NavierStokes.SignedPhysicalSumCalculus


-- @@ L624-624 verbatim
end

-- @@ L625-625 verbatim
end


-- @@ L627-627 verbatim
end


-- @@ L629-629 verbatim
@[expose] public section


-- @@ L631-631 verbatim
noncomputable section


-- @@ L633-633 verbatim
namespace NavierStokes.ActualSignedPhysicalCoherence


-- @@ L635-635 verbatim
open Set Function Filter HarmonicCalculus PhysicalWaveSum PhysicalCopyBounds

-- @@ L636-636 verbatim
open CorrectionInitialization CorrectionInitialization.ActualPrimary

-- @@ L637-637 verbatim
open scoped Topology ContDiff BigOperators


-- @@ L639-640 verbatim
/-- Label: an abbreviation for `ActualSignedPhysicalBinding.Label B N0`. -/
abbrev Label (B N0 : ℕ) := ActualSignedPhysicalBinding.Label B N0

-- @@ L641-642 verbatim
/-- Point: an abbreviation for `ActualSignedCoherence.Point`. -/
abbrev Point := ActualSignedCoherence.Point

-- @@ L643-644 verbatim
/-- Full point: an abbreviation for `ActualSignedCoherence.FullPoint`. -/
abbrev FullPoint := ActualSignedCoherence.FullPoint

-- @@ L645-646 verbatim
/-- Space time: an abbreviation for `ProblemStatement.SpaceTime`. -/
abbrev SpaceTime := ProblemStatement.SpaceTime

-- @@ L647-648 verbatim
/-- Frequency: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Frequency := TorusInverse.Frequency


-- @@ L650-650 verbatim
variable {B N0 : ℕ}


-- @@ L652-652 verbatim
section FiniteSums


-- @@ L654-654 verbatim
variable {α β V : Type*} [AddCommMonoid V]


-- @@ L656-667 verbatim
theorem finsum_injective_support (e : α → β) (he : Injective e) (f : β → V)
    (hz : ∀ b, b ∉ range e → f b = 0) :
    (∑ᶠ b, f b) = ∑ᶠ a, f (e a) := by
  calc
    _ = ∑ᶠ b ∈ range e, f b := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro b
      by_cases hb : b ∈ range e
      · simp only [indicator_of_mem hb]
      · simp only [indicator_of_notMem hb, hz b hb]
    _ = _ := finsum_mem_range he


-- @@ L669-674 verbatim
theorem finsum_finite_support (s : Finset α) (f : α → V)
    (hz : ∀ a, a ∉ s → f a = 0) : (∑ᶠ a, f a) = ∑ a ∈ s, f a := by
  apply finsum_eq_sum_of_support_subset
  intro a ha
  by_contra hn
  exact ha (hz a hn)


-- @@ L676-676 verbatim
end FiniteSums


-- @@ L678-681 verbatim
/-- Physical index, given by `ActualSignedPhysicalData.positiveIndex
(ActualSignedExterior.nativeLabel l)`. -/
noncomputable def physicalIndex (l : Label B N0) : WaveIndex 1 :=
  ActualSignedPhysicalData.positiveIndex (ActualSignedExterior.nativeLabel l)


-- @@ L683-686 verbatim
theorem physicalIndex_injective : Injective (physicalIndex (B := B) (N0 := N0)) := by
  intro l k he
  apply ActualSignedExterior.bandLabel_injective
  exact congrArg Prod.fst he


-- @@ L688-696 verbatim
theorem mem_range_physicalIndex (I : WaveIndex 1) :
    I ∈ range (physicalIndex (B := B) (N0 := N0)) ↔
      I.1 ∈ ActualSignedExterior.labels B N0 ∧ I.2.val = 1 := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Set.mem_range_self l, rfl⟩
  · rintro ⟨⟨l, hl⟩, hj⟩
    refine ⟨l, Prod.ext hl ?_⟩
    exact Subtype.ext hj.symm


-- @@ L698-698 verbatim
section PositiveHarmonic


-- @@ L700-700 verbatim
variable (f : DependentSignedPhysicalFamily.Family)


-- @@ L702-714 verbatim
theorem potential_amplitude_zero_unless (i : Fin 3) (I : WaveIndex 1)
    (hbad : I.1 ∉ f.active ∨ I.2.val ≠ 1) (k : Frequency) (x : PhysicalGraphBounds.LiftPoint) :
    (f.potentialCopies slots outgoing.data.h_pos.le i).amplitude k I x = 0 := by
  classical
  change (f.copyAt (fun L => ActualSignedPhysicalData.potentialFamily slots
    outgoing.data.h_pos.le (f.singleton L) i) I.1).amplitude k I x = 0
  by_cases hI : I.1 ∈ f.active
  · rw [f.copyAt_active _ (⟨I.1.val, I.1.property, hI⟩ : ActualSignedPhysicalData.NativeLabel
      f.active)]
    have hj : I.2.val ≠ 1 := hbad.resolve_left (not_not.mpr hI)
    simp [ActualSignedPhysicalData.potentialFamily, hj]
  · rw [f.copyAt_inactive _ hI]
    rfl


-- @@ L716-728 verbatim
theorem pressure_amplitude_zero_unless (I : WaveIndex 1)
    (hbad : I.1 ∉ f.active ∨ I.2.val ≠ 1) (k : Frequency) (x : PhysicalGraphBounds.LiftPoint) :
    (f.pressureCopies slots outgoing.data.h_pos.le).amplitude k I x = 0 := by
  classical
  change (f.copyAt (fun L => ActualSignedPhysicalData.pressureFamily slots
    outgoing.data.h_pos.le (f.singleton L)) I.1).amplitude k I x = 0
  by_cases hI : I.1 ∈ f.active
  · rw [f.copyAt_active _ (⟨I.1.val, I.1.property, hI⟩ : ActualSignedPhysicalData.NativeLabel
      f.active)]
    have hj : I.2.val ≠ 1 := hbad.resolve_left (not_not.mpr hI)
    simp [ActualSignedPhysicalData.pressureFamily, hj]
  · rw [f.copyAt_inactive _ hI]
    rfl


-- @@ L730-734 verbatim
theorem potential_term_zero_unless (i : Fin 3) (I : WaveIndex 1)
    (hbad : I.1 ∉ f.active ∨ I.2.val ≠ 1) (k : Frequency) (a r0 : ℝ) (w : SpaceTime) :
    (f.potentialCopies slots outgoing.data.h_pos.le i).term a h r0 I k w = 0 := by
  apply globalWave_eq_zero
  exact potential_amplitude_zero_unless f i I hbad k _


-- @@ L736-740 verbatim
theorem pressure_term_zero_unless (I : WaveIndex 1)
    (hbad : I.1 ∉ f.active ∨ I.2.val ≠ 1) (k : Frequency) (a r0 : ℝ) (w : SpaceTime) :
    (f.pressureCopies slots outgoing.data.h_pos.le).term a h r0 I k w = 0 := by
  apply globalWave_eq_zero
  exact pressure_amplitude_zero_unless f I hbad k _


-- @@ L742-742 verbatim
end PositiveHarmonic


-- @@ L744-744 verbatim
section CanonicalSums


-- @@ L746-746 verbatim
variable (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)


-- @@ L748-764 verbatim
theorem potential_sum_labels (i : Fin 3) (a r0 : ℝ) (w : SpaceTime) :
    ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).sum a h r0 w =
      ∑ᶠ l : Label B N0,
        ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).periodized
          a h r0 (physicalIndex l) w := by
  unfold CopyFamily.sum
  apply finsum_injective_support physicalIndex physicalIndex_injective
  intro I hI
  have hbad : I.1 ∉ (ActualSignedExterior.family s).active ∨ I.2.val ≠ 1 := by
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · right
      intro hj
      exact hI ((mem_range_physicalIndex I).mpr ⟨hL, hj⟩)
    · exact Or.inl hL
  change (∑' k, ((ActualSignedExterior.family s).potentialCopies slots
    outgoing.data.h_pos.le i).term a h r0 I k w) = 0
  simp only [potential_term_zero_unless _ i I hbad, tsum_zero]


-- @@ L766-782 verbatim
theorem pressure_sum_labels (a r0 : ℝ) (w : SpaceTime) :
    ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).sum a h r0 w =
      ∑ᶠ l : Label B N0,
        ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).periodized
          a h r0 (physicalIndex l) w := by
  unfold CopyFamily.sum
  apply finsum_injective_support physicalIndex physicalIndex_injective
  intro I hI
  have hbad : I.1 ∉ (ActualSignedExterior.family s).active ∨ I.2.val ≠ 1 := by
    by_cases hL : I.1 ∈ ActualSignedExterior.labels B N0
    · right
      intro hj
      exact hI ((mem_range_physicalIndex I).mpr ⟨hL, hj⟩)
    · exact Or.inl hL
  change (∑' k, ((ActualSignedExterior.family s).pressureCopies slots
    outgoing.data.h_pos.le).term a h r0 I k w) = 0
  simp only [pressure_term_zero_unless _ I hbad, tsum_zero]


-- @@ L784-784 verbatim
end CanonicalSums


-- @@ L786-786 verbatim
/-! ## The exact native-to-common physical graph -/


-- @@ L788-810 verbatim
theorem toCommon_nativeGraph (l : Label B N0) (z : SpaceTime) (hr : 0 < z.2 0) :
    ActualSignedPhysicalBinding.toCommonCylinder l
      ((PhysicalResidualBridge.commonGraph
        (ChartScales.Q (ActualSignedPhysicalBinding.reference l)) h
        (ChartScales.nativeIndex h (ActualSignedPhysicalBinding.reference l))).map z) =
      ActualSignedPotentialCoherence.nativePoint (ActualSignedPhysicalBinding.reference l) z := by
  let m := ActualSignedPhysicalBinding.reference l
  have he (Y : TorusInverse.Plane) :
      (CommonCoverSolve.coverPower (ChartScales.nativeIndex h m - CommonWindow.index h m)).symm
        ((SlotGeometry.cover ^ ChartScales.nativeIndex h m) Y) =
          (SlotGeometry.cover ^ CommonWindow.index h m) Y := by
    apply (CommonCoverSolve.coverPower
      (ChartScales.nativeIndex h m - CommonWindow.index h m)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [← CommonCoverSolve.coverPower_apply, ← CommonCoverSolve.coverPower_apply]
    rw [← CopySolveCompatibility.coverPower_add,
      Nat.sub_add_cancel (CommonWindow.index_le_native h m)]
  simp only [ActualSignedPotentialCoherence.nativePoint,
    PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos _) h _ hr,
    ActualSignedPhysicalBinding.toCommonCylinder_apply, PhysicalResidualTZ.swapCylinder_apply]
  exact congrArg (fun Y => ((ChartScales.Q m ^ (-(1 / 2 : ℝ)) * z.2 0,
    (((1 - z.1) / ChartScales.Q m, ChartScales.Q m ^ (-CoordinateAlgebra.D h) * z.2 2), Y)), z.2 1))
      (he _)


-- @@ L812-817 verbatim
theorem nativePoint_radius (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0) :
    (ActualSignedPotentialCoherence.nativePoint n z).1.1 =
      ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.2 0 := by
  simp only [ActualSignedPotentialCoherence.nativePoint,
    PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos _) h _ hr,
    PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply]


-- @@ L819-823 verbatim
theorem nativePoint_time (n : ℕ) (z : SpaceTime) (hr : 0 < z.2 0) :
    (ActualSignedPotentialCoherence.nativePoint n z).1.2.1.1 = (1 - z.1) / ChartScales.Q n := by
  simp only [ActualSignedPotentialCoherence.nativePoint,
    PhysicalResidualBridge.commonGraph_map (ChartScales.Q_pos _) h _ hr,
    PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply]


-- @@ L825-825 verbatim
section ReferenceAlgebra


-- @@ L827-829 verbatim
variable (l : Label B N0) (P : SignedStressPrimitive.Patch) (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure)


-- @@ L831-840 verbatim
theorem reference_cutoff_formula (k : Frequency) (x : FullPoint) :
    (ActualSignedPhysicalBinding.referenceCopies l P u H hp).cutoff
        (ActualSignedPhysicalBinding.reference l) k x =
      ActualSignedPhysicalData.waveMask slots (ActualSignedPhysicalBinding.spatialLabel l)
        ((ActualSignedPhysicalData.geometry slots (ActualSignedPhysicalBinding.spatialLabel l)
            0).coordinates
          k x.1.2.2) := by
  simp only [ActualSignedPhysicalBinding.referenceCopies, ActualSignedPhysicalData.dynamicCopyData,
    ActualSignedPhysicalBinding.nativeViews_map]
  rfl


-- @@ L842-866 verbatim
theorem reference_raw_amplitude (x : FullPoint) :
    (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.amplitude
        (ActualSignedPhysicalBinding.reference l) x =
      (ActualPeriodizedSignedRealization.periodizedPrimary
        (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l)).raw
          (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
          (ActualSignedPhysicalBinding.reference l) x := by
  rw [ActualPeriodizedSignedRealization.reference_raw_eq_sum]
  change (∑' k : Frequency, _ •
    (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
      (ActualSignedPhysicalBinding.spatialLabel l) (ActualSignedPhysicalBinding.label_large l) 0
      (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.nativeViews l)
      (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2 k).amplitude
        (ActualSignedPhysicalBinding.reference l) x) = _
  apply tsum_congr
  intro k
  rw [ActualSignedPhysicalBinding.dynamicCoefficients_eq]
  rw [ActualSignedPhysicalBinding.nativeCoefficients,
    ActualPeriodizedSignedRealization.coefficients_amplitude_at]
  simp only [ActualSignedPhysicalBinding.nativeViews_map,
    ActualPeriodizedSignedRealization.nativeUnit]
  rw [reference_cutoff_formula]
  erw [ActualSignedPhysicalData.waveMask_eq_compact]
  rw [mul_smul]
  rfl


-- @@ L868-923 verbatim
theorem reference_raw_pressure (x : FullPoint) :
    (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.pressure
        (ActualSignedPhysicalBinding.reference l) x =
      (ActualPeriodizedSignedRealization.periodizedPrimary
        (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l)).rawPressure
          (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
          (ActualSignedPhysicalBinding.reference l) x := by
  let A := ActualSignedPhysicalBinding.primary l
  let L := ActualSignedPhysicalBinding.layout l
  let R := (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest
  let m := ActualSignedPhysicalBinding.reference l
  have hs : SignedWaveUpdate.signedScalar
      (ActualPeriodizedSignedRealization.periodizedPrimary A L).strip
      (ActualPeriodizedSignedRealization.periodizedPrimary A L).matrix
      (ActualPeriodizedSignedRealization.periodizedPrimary A L).target R
      (ActualPeriodizedSignedRealization.periodizedPrimary A L).mask l.2 m x =
        L.mask m x.1.2.2 * ActualPeriodizedSignedRealization.referenceScalar A R l.2 m x :=
    ActualPeriodizedSignedRealization.signedScalar_mul_mask _ _ _ _ _ _ _ _ _
  symm
  change L.gaussian m x.1.2.2 •
    ((ActualPeriodizedSignedRealization.periodizedPrimary A L).coefficients R l.2).pressure m x = _
  rw [PhysicalSignedWave.PrimaryData.coefficients,
    ActualPeriodizedSignedRealization.coefficients_pressure_at, hs, mul_smul,
    ← L.gaussian_mask_sum]
  change (∑' k : Frequency, _) = ∑' k : Frequency,
    (_ : ℝ) • (ActualSignedPhysicalData.dynamicCoefficients slots outgoing.data.h_pos.le
      (ActualSignedPhysicalBinding.spatialLabel l) (ActualSignedPhysicalBinding.label_large l) 0
      A (ActualSignedPhysicalBinding.nativeViews l) R l.2 k).pressure m x
  apply tsum_congr
  intro k
  rw [ActualSignedPhysicalBinding.dynamicCoefficients_eq,
    ActualSignedPhysicalBinding.nativeCoefficients,
    ActualPeriodizedSignedRealization.coefficients_pressure_at]
  simp only [ActualPeriodizedSignedRealization.nativeUnit,
    ActualSignedPhysicalBinding.nativeViews_map, Complex.ofReal_re]
  rw [reference_cutoff_formula]
  change L.nativeGaussian m k x.1.2.2 • (L.nativeMask m k x.1.2.2 •
    (ActualPeriodizedSignedRealization.referenceScalar A R l.2 m x • _)) =
      ActualSignedPhysicalData.waveMask slots (ActualSignedPhysicalBinding.spatialLabel l)
        ((ActualSignedPhysicalData.geometry slots (ActualSignedPhysicalBinding.spatialLabel l)
            0).coordinates
          k x.1.2.2) • (_ : ℂ)
  by_cases hk : L.nativeMask m k x.1.2.2 = 0
  · have hk' : ActualSignedPhysicalData.nativeMask slots (ActualSignedPhysicalBinding.spatialLabel
      l)
        ((ActualSignedPhysicalData.geometry slots (ActualSignedPhysicalBinding.spatialLabel l)
            0).coordinates
          k x.1.2.2) = 0 := hk
    erw [ActualSignedPhysicalData.waveMask_eq_compact]
    simp only [hk, zero_smul, smul_zero, hk', zero_mul]
  · rw [ActualPeriodizedSignedRealization.referenceUnit_eq_native A L _ _ _ _ hk]
    erw [ActualSignedPhysicalData.waveMask_eq_compact]
    change L.nativeGaussian m k x.1.2.2 • (L.nativeMask m k x.1.2.2 • (_ : ℂ)) =
      (L.nativeMask m k x.1.2.2 * L.nativeGaussian m k x.1.2.2) • _
    exact (smul_comm (L.nativeGaussian m k x.1.2.2) (L.nativeMask m k x.1.2.2) _).trans
      (mul_smul (L.nativeMask m k x.1.2.2) (L.nativeGaussian m k x.1.2.2) _).symm


-- @@ L925-958 verbatim
theorem reference_vectorMode (x : FullPoint) :
    vectorMode ((ActualSignedPhysicalBinding.primary l).base.frequency
        (ActualSignedPhysicalBinding.reference l))
      ((ActualSignedPhysicalBinding.primary l).base.phase (ActualSignedPhysicalBinding.reference l))
      (fun y => CurlClassBounds.inverseCarrier
          ((ActualSignedPhysicalBinding.primary l).base.frequency
              (ActualSignedPhysicalBinding.reference l)) •
        CurlClassBounds.normalCoefficient
          ((ActualSignedPhysicalBinding.primary l).base.normal
            (ActualSignedPhysicalBinding.primary l).strip (ActualSignedPhysicalBinding.primary
                l).directions
            (ActualSignedPhysicalBinding.reference l) y)
          ((ActualPeriodizedSignedRealization.periodizedPrimary
            (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l)).raw
              (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
              (ActualSignedPhysicalBinding.reference l) y)) x =
      (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.curlPotential
        (ActualSignedPhysicalBinding.primary l).strip (ActualSignedPhysicalBinding.primary
            l).directions
        (ActualSignedPhysicalBinding.reference l) x := by
  let C := ActualSignedPhysicalBinding.referenceCopies l P u H hp
  let m := ActualSignedPhysicalBinding.reference l
  have hK : C.common.frequency m = (ActualSignedPhysicalBinding.primary l).base.frequency m :=
    congrArg (fun c => c.frequency m) (ActualSignedPhysicalBinding.reference_background l P u H hp)
  have hPhi : C.common.phase m = (ActualSignedPhysicalBinding.primary l).base.phase m :=
    congrArg (fun c => c.phase m) (ActualSignedPhysicalBinding.reference_background l P u H hp)
  change _ = vectorMode (C.common.frequency m) (C.common.phase m)
    (fun y => CurlClassBounds.inverseCarrier (C.common.frequency m) •
      CurlClassBounds.normalCoefficient (C.common.normal (ActualSignedPhysicalBinding.primary
          l).strip
        (ActualSignedPhysicalBinding.primary l).directions m y) (C.common.amplitude m y)) x
  rw [hK, hPhi, ActualSignedPhysicalBinding.reference_common_normal]
  dsimp only [C, m]
  simp_rw [reference_raw_amplitude l P u H hp]


-- @@ L960-987 verbatim
theorem reference_pressureMode (x : FullPoint) :
    mode ((ActualSignedPhysicalBinding.primary l).base.frequency
        (ActualSignedPhysicalBinding.reference l))
      ((ActualSignedPhysicalBinding.primary l).base.phase (ActualSignedPhysicalBinding.reference l))
      ((ActualPeriodizedSignedRealization.periodizedPrimary
        (ActualSignedPhysicalBinding.primary l) (ActualSignedPhysicalBinding.layout l)).rawPressure
          (ActualSignedPhysicalBinding.nativeStateData l P u H hp).referenceRequest l.2
          (ActualSignedPhysicalBinding.reference l)) x =
      mode ((ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.frequency
          (ActualSignedPhysicalBinding.reference l))
        ((ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.phase
          (ActualSignedPhysicalBinding.reference l))
        ((ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.pressure
          (ActualSignedPhysicalBinding.reference l)) x := by
  have hK : (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.frequency
      (ActualSignedPhysicalBinding.reference l) =
      (ActualSignedPhysicalBinding.primary l).base.frequency (ActualSignedPhysicalBinding.reference
          l) :=
    congrArg (fun c => c.frequency (ActualSignedPhysicalBinding.reference l))
      (ActualSignedPhysicalBinding.reference_background l P u H hp)
  have hPhi : (ActualSignedPhysicalBinding.referenceCopies l P u H hp).common.phase
      (ActualSignedPhysicalBinding.reference l) =
      (ActualSignedPhysicalBinding.primary l).base.phase (ActualSignedPhysicalBinding.reference l)
          :=
    congrArg (fun c => c.phase (ActualSignedPhysicalBinding.reference l))
      (ActualSignedPhysicalBinding.reference_background l P u H hp)
  unfold mode carrier
  rw [reference_raw_pressure, hK, hPhi]


-- @@ L989-989 verbatim
end ReferenceAlgebra


-- @@ L991-997 verbatim
/-- Measured states, defined pointwise by `ActualSignedPhysicalBinding.nativeStateData l P u H
hp`. -/
noncomputable def measuredStates (P : SignedStressPrimitive.Patch) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData standardRegion P.a P.b (commonContext B) u)
    (hp : GaugeMomentBalances.MovingField standardRegion P.a P.b u.pressure) :
    ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData :=
  fun l => ActualSignedPhysicalBinding.nativeStateData l P u H hp


-- @@ L999-1006 verbatim
/-- Singleton vector mode as an element of `ComplexVector`. -/
noncomputable def singletonVectorMode
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (x : FullPoint) : ComplexVector :=
  let f := (ActualSignedExterior.family s).singleton (ActualSignedExterior.nativeLabel l)
  let L := (ActualSignedExterior.family s).singletonLabel (ActualSignedExterior.nativeLabel l)
  vectorMode ((f.primary L).base.frequency L.val.1) ((f.primary L).base.phase L.val.1)
    (ActualSignedPhysicalData.referencePotentialCoefficient slots outgoing.data.h_pos.le f L) x


-- @@ L1008-1017 verbatim
/-- Singleton pressure mode as an element of `ℂ`. -/
noncomputable def singletonPressureMode
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (x : FullPoint) : ℂ :=
  let f := (ActualSignedExterior.family s).singleton (ActualSignedExterior.nativeLabel l)
  let L := (ActualSignedExterior.family s).singletonLabel (ActualSignedExterior.nativeLabel l)
  mode ((f.primary L).base.frequency L.val.1) ((f.primary L).base.phase L.val.1)
    ((ActualPeriodizedSignedRealization.periodizedPrimary (f.primary L)
      (ActualSignedPhysicalData.layout slots outgoing.data.h_pos.le L.val L.property 0)).rawPressure
        (f.state L).referenceRequest (f.column L) L.val.1) x


-- @@ L1019-1019 verbatim
section MeasuredModes


-- @@ L1021-1025 verbatim
variable (l : Label B N0) (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b u.pressure)


-- @@ L1027-1043 verbatim
theorem singletonVectorMode_eq (x : FullPoint) :
    singletonVectorMode (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l x =
      ActualSignedPotentialCoherence.potential l u (ActualSignedPhysicalBinding.reference l)
        (ActualSignedPhysicalBinding.toCommonCylinder l x) := by
  have he := (reference_vectorMode l ActualInitialization.patch u H hp x).trans
    (ActualSignedPhysicalBinding.curlPotential_reference l ActualInitialization.patch u H hp x)
  apply Eq.trans ?_ he
  funext i
  dsimp only [singletonVectorMode, vectorMode, mode,
      ActualSignedPhysicalData.referencePotentialCoefficient]
  erw [DependentSignedPhysicalFamily.Family.singleton_referenceRequest,
    ActualSignedExterior.family_referenceRequest_nativeLabel]
  dsimp only [DependentSignedPhysicalFamily.Family.singleton]
  dsimp only [ActualSignedExterior.family, DependentSignedPhysicalFamily.Family.singletonLabel]
  generalize_proofs
  erw [ActualSignedExterior.actualLabel_nativeLabel]
  rfl


-- @@ L1045-1071 verbatim
theorem singletonPressureMode_eq (x : FullPoint) :
    singletonPressureMode (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l x =
      ActualSignedPotentialCoherence.pressureMode l u (ActualSignedPhysicalBinding.reference l)
        (ActualSignedPhysicalBinding.toCommonCylinder l x) := by
  have he : mode ((ActualSignedPhysicalBinding.primary l).base.frequency
      (ActualSignedPhysicalBinding.reference l))
      ((ActualSignedPhysicalBinding.primary l).base.phase (ActualSignedPhysicalBinding.reference l))
      ((ActualPeriodizedSignedRealization.periodizedPrimary (ActualSignedPhysicalBinding.primary l)
        (ActualSignedPhysicalBinding.layout l)).rawPressure
        (ActualSignedPhysicalBinding.nativeStateData l ActualInitialization.patch u H
            hp).referenceRequest l.2
        (ActualSignedPhysicalBinding.reference l)) x =
      ActualSignedPotentialCoherence.pressureMode l u (ActualSignedPhysicalBinding.reference l)
        (ActualSignedPhysicalBinding.toCommonCylinder l x) := by
    rw [reference_pressureMode l ActualInitialization.patch u H hp x]
    unfold mode carrier
    rw [← ActualSignedPhysicalBinding.common_pressure_reference,
      ActualSignedPhysicalBinding.reference_phase]
    rfl
  apply Eq.trans ?_ he
  dsimp only [singletonPressureMode, mode]
  erw [DependentSignedPhysicalFamily.Family.singleton_referenceRequest,
    ActualSignedExterior.family_referenceRequest_nativeLabel]
  dsimp only [DependentSignedPhysicalFamily.Family.singleton]
  dsimp only [ActualSignedExterior.family, DependentSignedPhysicalFamily.Family.singletonLabel]
  erw [ActualSignedExterior.actualLabel_nativeLabel]
  rfl


-- @@ L1073-1073 verbatim
end MeasuredModes


-- @@ L1075-1080 verbatim
/-- Canonical potential as an element of `ComplexVector`. -/
noncomputable def canonicalPotential
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (w : SpaceTime) : ComplexVector := fun i =>
  ((ActualSignedExterior.family s).potentialCopies slots outgoing.data.h_pos.le i).periodized
    ActualPolarCoverage.inner h slots.radius (physicalIndex l) w


-- @@ L1082-1087 verbatim
/-- Canonical pressure as an element of `ℂ`. -/
noncomputable def canonicalPressure
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (w : SpaceTime) : ℂ :=
  ((ActualSignedExterior.family s).pressureCopies slots outgoing.data.h_pos.le).periodized
    ActualPolarCoverage.inner h slots.radius (physicalIndex l) w


-- @@ L1089-1089 verbatim
section NativeRepresentation


-- @@ L1091-1095 verbatim
variable (l : Label B N0) (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b u.pressure)


-- @@ L1097-1142 verbatim
theorem canonicalPotential_native (w : SpaceTime) (j : PolarCharts.Index)
    (hw : PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w ∈
      PhysicalGraphBounds.annulus ActualPolarCoverage.inner ActualPolarCoverage.outer)
    (hj : PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w ∈
      PolarCharts.chartDomain ActualPolarCoverage.inner j) :
    canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w =
      ActualSignedPhysicalData.rotateCoefficient
        (PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w)
        (ActualSignedPotentialCoherence.cylindricalPotential l u
            (ActualSignedPhysicalBinding.reference l)
          (PhysicalCurlCovariance.polarCoordinates
            (ActualSignedPhysicalGeometry.chartRadius ActualPolarCoverage.inner
              (ActualSignedPhysicalBinding.reference l)) j w)) := by
  let s := measuredStates (N0 := N0) ActualInitialization.patch u H hp
  let f := ActualSignedExterior.family s
  let L := f.singletonLabel (ActualSignedExterior.nativeLabel l)
  let G := ActualSignedReferenceGeometry.nativeSingletonGeometry ActualInitialization.patch u H hp l
  have hr := (ActualSignedPhysicalData.polarCoordinates_valid
    (ActualSignedPhysicalGeometry.chartRadius_pos ActualPolarCoverage.inner_pos
      (ActualSignedPhysicalBinding.reference l)) j
        (ActualSignedPhysicalGeometry.physical_chart_mem _ j hj)).1
  ext i
  change (f.potentialCopies slots outgoing.data.h_pos.le i).periodized _ _ _
    (ActualSignedPhysicalData.positiveIndex (ActualSignedExterior.nativeLabel l)) w = _
  erw [DependentSignedPhysicalFamily.Family.potential_periodized_active]
  change (ActualSignedPhysicalData.potentialFamily slots outgoing.data.h_pos.le
    (f.singleton (ActualSignedExterior.nativeLabel l)) i).periodized
      ActualPolarCoverage.inner h slots.radius (ActualSignedPhysicalData.positiveIndex L) w = _
  rw [ActualSignedPhysicalData.potential_periodized_of_chart slots outgoing.data.h_pos.le
    (f.singleton (ActualSignedExterior.nativeLabel l)) G L i ActualPolarCoverage.inner_pos w hw j
        hj]
  rw [← ActualSignedPhysicalData.rotateCoefficient_vectorMode,
    PhysicalGraphBounds.liftXY_physicalLift]
  change (ChartScales.Q (ActualSignedPhysicalBinding.reference l) ^ (-h) : ℝ) •
    ActualSignedPhysicalData.rotateCoefficient
      (PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w)
      (singletonVectorMode (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l
        (ActualSignedPhysicalData.cylinderAt ActualPolarCoverage.inner j
          (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w))) i = _
  rw [singletonVectorMode_eq l u H hp,
    ActualSignedPhysicalGeometry.cylinderAt_physical_chart h _ ActualPolarCoverage.inner_pos j hj,
    toCommon_nativeGraph l _ hr]
  change _ = ActualSignedPhysicalData.rotateCoefficient _
    ((ChartScales.Q (ActualSignedPhysicalBinding.reference l) ^ (-h) : ℝ) • _) i
  rw [ActualSignedPhysicalData.rotateCoefficient_real_smul]
  rfl


-- @@ L1144-1179 verbatim
theorem canonicalPressure_native (w : SpaceTime) (j : PolarCharts.Index)
    (hw : PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w ∈
      PhysicalGraphBounds.annulus ActualPolarCoverage.inner ActualPolarCoverage.outer)
    (hj : PhysicalGraphBounds.scaledRadial (ActualSignedPhysicalBinding.reference l) w ∈
      PolarCharts.chartDomain ActualPolarCoverage.inner j) :
    canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w =
      ActualSignedPotentialCoherence.cylindricalPressureMode l u
          (ActualSignedPhysicalBinding.reference l)
        (PhysicalCurlCovariance.polarCoordinates
          (ActualSignedPhysicalGeometry.chartRadius ActualPolarCoverage.inner
            (ActualSignedPhysicalBinding.reference l)) j w) := by
  let s := measuredStates (N0 := N0) ActualInitialization.patch u H hp
  let f := ActualSignedExterior.family s
  let L := f.singletonLabel (ActualSignedExterior.nativeLabel l)
  let G := ActualSignedReferenceGeometry.nativeSingletonGeometry ActualInitialization.patch u H hp l
  have hr := (ActualSignedPhysicalData.polarCoordinates_valid
    (ActualSignedPhysicalGeometry.chartRadius_pos ActualPolarCoverage.inner_pos
      (ActualSignedPhysicalBinding.reference l)) j
        (ActualSignedPhysicalGeometry.physical_chart_mem _ j hj)).1
  change (f.pressureCopies slots outgoing.data.h_pos.le).periodized _ _ _
    (ActualSignedPhysicalData.positiveIndex (ActualSignedExterior.nativeLabel l)) w = _
  erw [DependentSignedPhysicalFamily.Family.pressure_periodized_active]
  change (ActualSignedPhysicalData.pressureFamily slots outgoing.data.h_pos.le
    (f.singleton (ActualSignedExterior.nativeLabel l))).periodized
      ActualPolarCoverage.inner h slots.radius (ActualSignedPhysicalData.positiveIndex L) w = _
  rw [ActualSignedPhysicalData.pressure_periodized_of_chart slots outgoing.data.h_pos.le
    (f.singleton (ActualSignedExterior.nativeLabel l)) G L ActualPolarCoverage.inner_pos w hw j hj]
  change (ChartScales.Q (ActualSignedPhysicalBinding.reference l) ^ (-(2 * CoordinateAlgebra.A h))
      : ℝ) •
    singletonPressureMode (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l
      (ActualSignedPhysicalData.cylinderAt ActualPolarCoverage.inner j
        (PhysicalGraphBounds.physicalLift h (ActualSignedPhysicalBinding.reference l) w)) = _
  rw [singletonPressureMode_eq l u H hp,
    ActualSignedPhysicalGeometry.cylinderAt_physical_chart h _ ActualPolarCoverage.inner_pos j hj,
    toCommon_nativeGraph l _ hr]
  rfl


-- @@ L1181-1181 verbatim
end NativeRepresentation


-- @@ L1183-1183 verbatim
/-! ## The two literal zero cases, including both native dyadic faces -/


-- @@ L1185-1219 verbatim
theorem canonical_current_zero
    (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)
    (l : Label B N0) (u : CorrectionState.State Point) (n : ℕ)
    (w z : SpaceTime) (hr : 0 < z.2 0)
    (he : (z.1, CylindricalResidual.chart z.2) = w) (hw : w ∈ preterminal)
    (hbad : w ∉ ActualSignedExterior.active ∨
      physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2) :
    canonicalPotential s l w = 0 ∧ canonicalPressure s l w = 0 ∧
      ActualSignedPotentialCoherence.cylindricalPotential l u n z = 0 ∧
      ActualSignedPotentialCoherence.cylindricalPressureMode l u n z = 0 := by
  have hwz : (z.1, CylindricalResidual.chart z.2) ∈ preterminal := by rwa [he]
  rcases hbad with hout | hq
  · have houtz : (z.1, CylindricalResidual.chart z.2) ∉ ActualSignedExterior.active := by rwa [he]
    refine ⟨?_, ?_, ActualSignedPhysicalZeros.cylindricalPotential_zero_of_exterior l u n z hr hwz
        houtz,
      ActualSignedPhysicalZeros.cylindricalPressureMode_zero_of_exterior l u n z hr hwz houtz⟩
    · ext i
      change (∑' k : Frequency, ((ActualSignedExterior.family s).potentialCopies
        slots outgoing.data.h_pos.le i).term ActualPolarCoverage.inner h slots.radius
          (physicalIndex l) k w) = 0
      simp only [ActualSignedExterior.potential_term_zero s _ _ _ _ _ hw hout, tsum_zero]
    · change (∑' k : Frequency, ((ActualSignedExterior.family s).pressureCopies
        slots outgoing.data.h_pos.le).term ActualPolarCoverage.inner h slots.radius
          (physicalIndex l) k w) = 0
      simp only [ActualSignedExterior.pressure_term_zero s _ _ _ _ hw hout, tsum_zero]
  · have hqz : physicalQ h (z.1, CylindricalResidual.chart z.2) /
        ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2 := by rwa [he]
    refine ⟨?_, ?_, ActualSignedPhysicalZeros.cylindricalPotential_zero_of_nativeQ l u n z hr hwz
        hqz,
      ActualSignedPhysicalZeros.cylindricalPressureMode_zero_of_nativeQ l u n z hr hwz hqz⟩
    · ext i
      exact ActualSignedPhysicalZeros.canonical_potential_periodized_zero_of_nativeQ
        s l i ActualPolarCoverage.inner slots.radius hw hq
    · exact ActualSignedPhysicalZeros.canonical_pressure_periodized_zero_of_nativeQ
        s l ActualPolarCoverage.inner slots.radius hw hq


-- @@ L1221-1233 verbatim
theorem current_chart_ratio (n : ℕ) {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {w : SpaceTime} (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    physicalQ h w / ChartScales.Q n ∈ Ioo (1 / 2 : ℝ) 2 := by
  let z := PhysicalCurlCovariance.polarCoordinates a i w
  have he : (z.1, CylindricalResidual.chart z.2) = w :=
    ActualMeanPotentialRealization.polarCoordinates_back ha i hw.2.1
  have ht : (z.1, CylindricalResidual.chart z.2) ∈ preterminal := by rw [he]; exact hw.1.1
  have hn := ActualSignedCurrentSupport.physicalDomain_of_source n hw.2.2
  have hq : SimilarityCoordinates.coordinateQ (2 * h)
      (ActualSignedPotentialCoherence.nativePoint n z).1.2.1 ∈ Ioo (1 / 2 : ℝ) 2 := hn.2.2
  rw [ActualSignedPhysicalGeometry.nativePoint_slow n 0,
    PhysicalMeanJetBounds.graph_q_eq outgoing.data.h_pos outgoing.data.h_lt_half n 0 ht, he] at hq
  exact hq


-- @@ L1235-1235 verbatim
section CurrentRepresentation


-- @@ L1237-1248 verbatim
variable (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) u)
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b u.pressure)
  (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
    (commonContext B) u).pressure = u.pressure)
  (HS : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
    PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (GaugeStateCoherence.bandChartEquiv h n m k) (GaugeStateCoherence.bandVelocityScale h n m)
      (GaugeStateCoherence.bandScale n m) u u n m)


-- @@ L1250-1250 verbatim
include hfixed HS


-- @@ L1252-1333 verbatim
/-- The physical copy sum has the current-band value.  The last conclusion
is complex-valued: it justifies truncating the original complex sum before
taking real parts. -/
theorem canonical_current_values (l : Label B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    PhysicalCurlCovariance.realVector
        (canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w) =
      CurrentSignedCurl.currentPotential l u n a i w ∧
    (canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w).re =
      CurrentSignedCurl.currentPressure l u n a i w ∧
    (l ∉ activeLabels standardRegion B N0 n →
      canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w = 0 ∧
        canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w = 0) :=
            by
  by_cases hc : w ∈ ActualSignedExterior.active ∧
      physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∈ Ioo (1 / 2 : ℝ) 2
  · let m := ActualSignedPhysicalBinding.reference l
    obtain ⟨j, hj⟩ := ActualSignedPhysicalGeometry.chart_exists_of_ratio m hw.1.1 hc.1 hc.2
    let b := ActualSignedPhysicalGeometry.chartRadius ActualPolarCoverage.inner m
    let z := PhysicalCurlCovariance.polarCoordinates b j w
    have hb : 0 < b := ActualSignedPhysicalGeometry.chartRadius_pos ActualPolarCoverage.inner_pos m
    have hwb : w ∈ ActualMeanPotentialRealization.cartesianDomain b j :=
      ActualSignedPhysicalGeometry.physical_chart_mem m j hj
    have hm : z ∈ ActualSignedPotentialCoherence.physicalDomain m :=
      ActualSignedPhysicalGeometry.scaledChart_mem_physicalDomain m ActualPolarCoverage.inner_pos j
          hj
        hw.1.1 hc.2
    have hn : z ∈ ActualSignedPotentialCoherence.physicalDomain n :=
      ActualSignedPhysicalGeometry.polarCoordinates_mem_physicalDomain n hb j hwb hw.1.1
        (current_chart_ratio n ha i hw)
    have he := ActualSignedPotentialCoherence.cylindrical_values_eq l u H hfixed HS n m z hn hm
    have hann := ActualSignedPhysicalGeometry.annulus_of_ratio m hw.1.1 hc.1 hc.2
    have hv := canonicalPotential_native l u H hp w j hann hj
    have hpr := canonicalPressure_native l u H hp w j hann hj
    change canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w =
      ActualSignedPhysicalData.rotateCoefficient (PhysicalGraphBounds.scaledRadial m w)
        (ActualSignedPotentialCoherence.cylindricalPotential l u m z) at hv
    change canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w =
      ActualSignedPotentialCoherence.cylindricalPressureMode l u m z at hpr
    rw [← he.1] at hv
    rw [← he.2] at hpr
    have hangle : (PolarCharts.chart ActualPolarCoverage.inner j
        (PhysicalGraphBounds.scaledRadial m w)).2 = (PhysicalCurlCovariance.polarInput b j w).2 :=
            by
      have hh := congrArg Prod.snd (ActualSignedPhysicalGeometry.physical_chart_scale m
        ActualPolarCoverage.inner_pos j hj)
      exact hh
    have hvr : PhysicalCurlCovariance.realVector
        (canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l w) =
        CurrentSignedCurl.currentPotential l u n b j w := by
      ext r
      rw [PhysicalCurlCovariance.realVector_apply, hv,
        ActualSignedPhysicalData.rotateCoefficient_chart_re ActualPolarCoverage.inner_pos j hj,
        hangle]
      rfl
    have hprr : (canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l
        w).re =
        CurrentSignedCurl.currentPressure l u n b j w := congrArg Complex.re hpr
    refine ⟨hvr.trans (CurrentSignedCurl.currentPotential_overlap l u n hb ha j i hwb hw.2.1),
      hprr.trans (CurrentSignedCurl.currentPressure_overlap l u n hb ha j i hwb hw.2.1), ?_⟩
    intro hnot
    obtain ⟨hzv, hzp⟩ := ActualSignedCurrentSupport.cylindrical_zero l u n hn hnot
    rw [hzv, ActualSignedPhysicalData.rotateCoefficient_zero] at hv
    rw [hzp] at hpr
    exact ⟨hv, hpr⟩
  · have hbad : w ∉ ActualSignedExterior.active ∨
        physicalQ h w / ChartScales.Q (ActualSignedPhysicalBinding.reference l) ∉ Ioo (1 / 2 : ℝ) 2
            :=
      not_and_or.mp hc
    let z := PhysicalCurlCovariance.polarCoordinates a i w
    have hr : 0 < z.2 0 := (ActualMeanPotentialRealization.polarCoordinates_valid ha i hw.2.1).1
    have hback : (z.1, CylindricalResidual.chart z.2) = w :=
      ActualMeanPotentialRealization.polarCoordinates_back ha i hw.2.1
    obtain ⟨hv, hpr, hcv, hcp⟩ := canonical_current_zero
      (measuredStates (N0 := N0) ActualInitialization.patch u H hp) l u n w z hr hback hw.1.1 hbad
    dsimp only [z] at hcv hcp
    have hzero : PhysicalCurlCovariance.realVector (0 : ComplexVector) = 0 := by ext r; simp
    refine ⟨?_, ?_, fun _ => ⟨hv, hpr⟩⟩
    · simp only [hv, CurrentSignedCurl.currentPotential, PhysicalCurlCovariance.cartesianPotential,
        hcv, hzero, map_zero]
    · simp only [hpr, CurrentSignedCurl.currentPressure, hcp, Complex.zero_re]


-- @@ L1335-1350 verbatim
theorem measuredPotential_eq_sum (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ActualSignedExterior.potential (measuredStates (N0 := N0) ActualInitialization.patch u H hp) w =
      ∑ l ∈ v.labels n, CurrentSignedCurl.currentPotential l u n a i w := by
  unfold ActualSignedExterior.potential PhysicalCopyBounds.vectorSum
  simp_rw [potential_sum_labels]
  apply SignedPhysicalSumCalculus.realCoordinate_finsum_eq_sum
    (v.labels n) (fun l => canonicalPotential (measuredStates (N0 := N0) ActualInitialization.patch
        u H hp) l w)
  · intro l hn
    have hn' : l ∉ activeLabels standardRegion B N0 n := by simpa only [hlabels] using hn
    exact ((canonical_current_values u H hp hfixed HS l n ha i hw).2.2 hn').1
  · intro l
    exact (canonical_current_values u H hp hfixed HS l n ha i hw).1


-- @@ L1352-1367 verbatim
theorem measuredPressure_eq_sum (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ActualSignedExterior.pressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp) w =
      ∑ l ∈ v.labels n, CurrentSignedCurl.currentPressure l u n a i w := by
  unfold ActualSignedExterior.pressure
  rw [pressure_sum_labels]
  apply SignedPhysicalSumCalculus.real_finsum_eq_sum
    (v.labels n) (fun l => canonicalPressure (measuredStates (N0 := N0) ActualInitialization.patch
        u H hp) l w)
  · intro l hn
    have hn' : l ∉ activeLabels standardRegion B N0 n := by simpa only [hlabels] using hn
    exact ((canonical_current_values u H hp hfixed HS l n ha i hw).2.2 hn').2
  · intro l
    exact (canonical_current_values u H hp hfixed HS l n ha i hw).2.1


-- @@ L1369-1378 verbatim
theorem measuredPotential_germ (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ActualSignedExterior.potential (measuredStates (N0 := N0) ActualInitialization.patch u H hp)
        =ᶠ[𝓝 w]
      fun z => ∑ l ∈ v.labels n, CurrentSignedCurl.currentPotential l u n a i z := by
  filter_upwards [(ActualPhysicalPrefixFields.cartesianChartDomain_open qbig n ha i).mem_nhds hw]
    with z hz
  exact measuredPotential_eq_sum u H hp hfixed HS v hlabels n ha i hz


-- @@ L1380-1389 verbatim
theorem measuredPressure_germ (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {qbig a : ℝ}
    (ha : 0 < a) (i : PolarCharts.Index) {w : SpaceTime}
    (hw : w ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    ActualSignedExterior.pressure (measuredStates (N0 := N0) ActualInitialization.patch u H hp)
        =ᶠ[𝓝 w]
      fun z => ∑ l ∈ v.labels n, CurrentSignedCurl.currentPressure l u n a i z := by
  filter_upwards [(ActualPhysicalPrefixFields.cartesianChartDomain_open qbig n ha i).mem_nhds hw]
    with z hz
  exact measuredPressure_eq_sum u H hp hfixed HS v hlabels n ha i hz


-- @@ L1391-1406 verbatim
theorem measuredPotential_curl (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ) {α : ℝ}
    (hamp : ∀ l ∈ v.labels n, CurrentSignedCurl.AmplitudeBound l u α)
    {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (ActualSignedExterior.potential
        (measuredStates (N0 := N0) ActualInitialization.patch u H hp)))
      (CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          (∑ l ∈ v.labels n, ((ActualSignedStageControls.parameters l).exactBlock
            ActualInitialization.geometry.strip (ActualSignedCoherence.request B u)).oscillation
                n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  intro w hw
  exact (PhysicalCurlCovariance.spatialCurl_congr
    (measuredPotential_germ u H hp hfixed HS v hlabels n ha i hw)).trans
      (CurrentSignedCurl.currentPotential_sum_curl_map (v.labels n) u hamp n ha i hw)


-- @@ L1408-1421 verbatim
theorem measuredPressure_eq (v : CorrectionStep.CycleCoefficients (Label B N0))
    (hlabels : v.labels = activeLabels standardRegion B N0) (n : ℕ)
    {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (ActualSignedExterior.pressure (measuredStates (N0 := N0) ActualInitialization.patch u H
        hp))
      (CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          (∑ l ∈ v.labels n, ((ActualSignedStageControls.parameters l).exactBlock
            ActualInitialization.geometry.strip (ActualSignedCoherence.request B
                u)).oscillatoryPressure n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  intro w hw
  rw [measuredPressure_eq_sum u H hp hfixed HS v hlabels n ha i hw]
  simp only [CurrentSignedCurl.currentPressure_eq, map_sum, Finset.sum_apply]


-- @@ L1423-1423 verbatim
end CurrentRepresentation


-- @@ L1425-1425 verbatim
/-! ## The literal correction cycle's physical fields -/


-- @@ L1427-1432 verbatim
/-- Cycle input, given by `(ActualCycleParameters.fixedParameters B N0).afterParticular
x.coefficients (commonContext B) x.state`. -/
noncomputable def cycleInput (x : CorrectionStep.CycleState (Label B N0)) :
    CorrectionState.State Point :=
  (ActualCycleParameters.fixedParameters B N0).afterParticular
    x.coefficients (commonContext B) x.state


-- @@ L1434-1434 verbatim
section Cycle


-- @@ L1436-1448 verbatim
variable (x : CorrectionStep.CycleState (Label B N0))
  (Hu : MeanStateRegularity.PrimitiveData standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (commonContext B) (cycleInput x))
  (hp : GaugeMomentBalances.MovingField standardRegion ActualInitialization.patch.a
    ActualInitialization.patch.b (cycleInput x).pressure)
  (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
    (commonContext B) (cycleInput x)).pressure = (cycleInput x).pressure)
  (HS : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
    PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (GaugeStateCoherence.bandChartEquiv h n m k) (GaugeStateCoherence.bandVelocityScale h n m)
      (GaugeStateCoherence.bandScale n m) (cycleInput x) (cycleInput x) n m)
  (hlabels : x.coefficients.labels = activeLabels standardRegion B N0)


-- @@ L1450-1450 verbatim
include hfixed HS hlabels


-- @@ L1452-1476 verbatim
/-- Curl is taken only after equality of the canonical physical potential
on an open neighborhood has been proved.  The sole analytic bound concerns
the actual current common amplitude. -/
theorem cyclePotential_curl (n : ℕ) {α : ℝ}
    (hamp : ∀ l ∈ x.coefficients.labels n, CurrentSignedCurl.AmplitudeBound l (cycleInput x) α)
    {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (SpatialCurl.spatialCurl (ActualSignedExterior.cyclePotential x Hu hp))
      (CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).signedVelocity
            x.coefficients (commonContext B) x.state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  have hv : (∑ l ∈ x.coefficients.labels n,
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B (cycleInput x))).oscillation n) =
      (ActualCycleParameters.fixedParameters B N0).signedVelocity
        x.coefficients (commonContext B) x.state n := by
    funext z j
    simp only [Finset.sum_apply, CorrectionStep.CycleParameters.signedVelocity,
      LabelSumBounds.fieldSum]
    rfl
  have hh := measuredPotential_curl (cycleInput x) Hu hp hfixed HS x.coefficients hlabels n hamp
    (qbig := qbig) ha i
  rw [hv] at hh
  exact hh


-- @@ L1478-1498 verbatim
/-- The canonical physical pressure is the same finite signed pressure
sum used by the current correction state. -/
theorem cyclePressure_eq (n : ℕ) {qbig a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    EqOn (ActualSignedExterior.cyclePressure x Hu hp)
      (CyclePhysicalPrefixes.polarPressureMap a i
        (CyclePhysicalPrefixes.pressureMap (ActualCycleResidualBounds.actualBandGraph n)
          ((ActualCycleParameters.fixedParameters B N0).signedPressure
            x.coefficients (commonContext B) x.state n)))
      (ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) := by
  have hv : (∑ l ∈ x.coefficients.labels n,
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B (cycleInput x))).oscillatoryPressure n) =
      (ActualCycleParameters.fixedParameters B N0).signedPressure
        x.coefficients (commonContext B) x.state n := by
    funext z
    simp only [Finset.sum_apply, CorrectionStep.CycleParameters.signedPressure]
    rfl
  have hh := measuredPressure_eq (cycleInput x) Hu hp hfixed HS x.coefficients hlabels n
    (qbig := qbig) ha i
  rw [hv] at hh
  exact hh


-- @@ L1500-1500 verbatim
end Cycle


-- @@ L1502-1502 verbatim
end NavierStokes.ActualSignedPhysicalCoherence
