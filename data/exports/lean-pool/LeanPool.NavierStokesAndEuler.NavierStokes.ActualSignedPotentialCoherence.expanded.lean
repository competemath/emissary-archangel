/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedCoherence


-- @@ L11-17 verbatim
/-!
# Current-band signed vector potentials and pressure modes

The potential is formed from the literal current common signed coefficient,
after its native cutoffs and copy sum.  Its scale follows from the actual
normal, amplitude and carrier identities, before any physical curl is taken.
-/


-- @@ L19-19 verbatim
@[expose] public section



-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace NavierStokes.ActualSignedPotentialCoherence


-- @@ L26-26 verbatim
open Set Function Filter HarmonicCalculus

-- @@ L27-27 verbatim
open CorrectionInitialization CorrectionInitialization.ActualPrimary GaugeStateCoherence

-- @@ L28-28 verbatim
open ActualSignedCoherence

-- @@ L29-29 verbatim
open scoped Topology ContDiff


-- @@ L31-32 verbatim
/-- Point: an abbreviation for `ActualSignedCoherence.Point`. -/
abbrev Point := ActualSignedCoherence.Point

-- @@ L33-34 verbatim
/-- Full point: an abbreviation for `ActualSignedCoherence.FullPoint`. -/
abbrev FullPoint := ActualSignedCoherence.FullPoint


-- @@ L36-36 verbatim
variable {B N0 : ℕ}


-- @@ L38-44 verbatim
/-- The coefficient of the literal current-band vector potential. -/
noncomputable def potentialCoefficient (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (x : FullPoint) : ComplexVector :=
  CurlClassBounds.inverseCarrier ((copies l u).common.frequency n) •
    CurlClassBounds.normalCoefficient
      ((copies l u).common.normal fullStrip (ActualSignedStageControls.directions B) n x)
      ((copies l u).common.amplitude n x)


-- @@ L46-49 verbatim
/-- The actual current common coefficient's curl potential. -/
noncomputable def potential (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) : FullPoint → ComplexVector :=
  (copies l u).common.curlPotential fullStrip (ActualSignedStageControls.directions B) n


-- @@ L51-55 verbatim
/-- The actual current common pressure, with its carrier retained. -/
noncomputable def pressureMode (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) : FullPoint → ℂ :=
  mode ((copies l u).common.frequency n) ((copies l u).common.phase n)
    ((copies l u).common.pressure n)


-- @@ L57-59 verbatim
theorem potential_eq_mode (l : SignedLabel B N0) (u : CorrectionState.State Point) (n : ℕ) :
    potential l u n = vectorMode ((copies l u).common.frequency n) ((copies l u).common.phase n)
      (potentialCoefficient l u n) := rfl


-- @@ L61-64 verbatim
theorem potential_eq_curlPotential (l : SignedLabel B N0) (u : CorrectionState.State Point) (n : ℕ)
    :
    potential l u n = (copies l u).common.curlPotential fullStrip
      (ActualSignedStageControls.directions B) n := rfl


-- @@ L66-73 verbatim
theorem potential_weight (n m : ℕ) :
    bandVelocityScale h n m / bandScale n m =
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) h := by
  rw [← velocityWeight_eq, ← radiusWeight_eq, PhysicalParticularWave.velocityWeight,
    PhysicalParticularWave.ratioPower_div (ChartScales.Q_pos n) (ChartScales.Q_pos m)]
  congr 1
  unfold CoordinateAlgebra.A
  ring


-- @@ L75-82 verbatim
theorem pressure_weight (n m : ℕ) :
    bandVelocityScale h n m * bandVelocityScale h n m =
      PhysicalParticularWave.pressureWeight h (ChartScales.Q n) (ChartScales.Q m) := by
  rw [← velocityWeight_eq, PhysicalParticularWave.velocityWeight,
    PhysicalParticularWave.ratioPower_mul (ChartScales.Q_pos n) (ChartScales.Q_pos m)]
  unfold PhysicalParticularWave.pressureWeight
  congr 1
  ring


-- @@ L84-92 verbatim
private theorem inverseCarrier_scale (K L b s c : ℝ)
    (hK : K ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hKL : K * b = L) :
    CurlClassBounds.inverseCarrier K * ((c / (b*s) : ℝ) : ℂ) =
      ((c/s : ℝ) : ℂ) * CurlClassBounds.inverseCarrier L := by
  rw [← hKL]
  unfold CurlClassBounds.inverseCarrier
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hK, Complex.ofReal_ne_zero.mpr hb,
    Complex.ofReal_ne_zero.mpr hs]


-- @@ L94-120 verbatim
/-- The inverse carrier cancels the phase scale, leaving velocity divided
by radial scale. No smoothness or nonzero-normal assumption is introduced. -/
theorem potentialCoefficient_of_request (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (x : FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    potentialCoefficient l u n x = (bandVelocityScale h n m / bandScale n m) •
      potentialCoefficient l u m (chart n m k x) := by
  change CurlClassBounds.inverseCarrier (ChartScales.carrier h n) •
      CurlClassBounds.normalCoefficient
        ((chartCoefficients l.2 l.1).normal fullStrip (ActualSignedStageControls.directions B) n x)
        ((copies l u).common.amplitude n x) =
    (bandVelocityScale h n m / bandScale n m) •
      (CurlClassBounds.inverseCarrier (ChartScales.carrier h m) •
        CurlClassBounds.normalCoefficient
          ((chartCoefficients l.2 l.1).normal fullStrip (ActualSignedStageControls.directions B) m
            (chart n m k x)) ((copies l u).common.amplitude m (chart n m k x)))
  rw [normal_transport l n m k hi, common_amplitude_of_request l u n m k hi x hR,
    PhysicalCurlCovariance.normalCoefficient_scale _ _
      (mul_ne_zero (phaseWeight_ne n m) (bandScale_pos n m).ne')]
  have hs := inverseCarrier_scale (ChartScales.carrier h n) (ChartScales.carrier h m)
    (phaseWeight n m) (bandScale n m) (bandVelocityScale h n m)
    (carrier_pos n).ne' (phaseWeight_ne n m) (bandScale_pos n m).ne' (carrier_phaseWeight n m)
  ext i
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc (CurlClassBounds.inverseCarrier (ChartScales.carrier h n)), hs]
  ring


-- @@ L122-134 verbatim
theorem potential_of_request (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (x : FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    potential l u n x = (bandVelocityScale h n m / bandScale n m) •
      potential l u m (chart n m k x) := by
  have ha := potentialCoefficient_of_request l u n m k hi x hR
  have hc : carrier ((copies l u).common.frequency n) ((copies l u).common.phase n) x =
      carrier ((copies l u).common.frequency m) ((copies l u).common.phase m) (chart n m k x) :=
    PhysicalCurlCovariance.carrier_eq_of_products (carrier_transport l n m k hi x)
  ext i
  simp only [potential_eq_mode, vectorMode, mode, ha, hc, Pi.smul_apply, Complex.real_smul]
  ring


-- @@ L136-146 verbatim
theorem pressureMode_of_request (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (x : FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    pressureMode l u n x = (bandVelocityScale h n m * bandVelocityScale h n m) •
      pressureMode l u m (chart n m k x) := by
  have ha := common_pressure_of_request l u n m k hi x hR
  have hc : carrier ((copies l u).common.frequency n) ((copies l u).common.phase n) x =
      carrier ((copies l u).common.frequency m) ((copies l u).common.phase m) (chart n m k x) :=
    PhysicalCurlCovariance.carrier_eq_of_products (carrier_transport l n m k hi x)
  simp only [pressureMode, mode, ha, hc, Complex.real_smul, mul_assoc]


-- @@ L148-151 verbatim
/-- The physical power of the potential, before choosing any physical graph. -/
noncomputable def rescaledPotential (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (x : FullPoint) : ComplexVector :=
  ChartScales.Q n ^ (-h) • potential l u n x


-- @@ L153-157 verbatim
/-- Rescaled pressure mode, given by `ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) •
pressureMode l u n x`. -/
noncomputable def rescaledPressureMode (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (x : FullPoint) : ℂ :=
  ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) • pressureMode l u n x


-- @@ L159-159 verbatim
section IncomingState


-- @@ L161-169 verbatim
variable (l : SignedLabel B N0) (u : CorrectionState.State Point)
  (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
    ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B) u)
  (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
    (commonContext B) u).pressure = u.pressure)
  (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
  (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
      (ActualInitialCoherence.overlap n m))
    (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)


-- @@ L171-171 verbatim
include H hfixed hi HS


-- @@ L173-176 verbatim
theorem potential_transport (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap n m) :
    potential l u n x = (bandVelocityScale h n m / bandScale n m) •
      potential l u m (chart n m k x) :=
  potential_of_request l u n m k hi x (fullRequest_transport u H hfixed n m k hi HS x hx)


-- @@ L178-181 verbatim
theorem pressureMode_transport (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap n m) :
    pressureMode l u n x = (bandVelocityScale h n m * bandVelocityScale h n m) •
      pressureMode l u m (chart n m k x) :=
  pressureMode_of_request l u n m k hi x (fullRequest_transport u H hfixed n m k hi HS x hx)


-- @@ L183-188 verbatim
theorem potential_transport_weight (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap n
    m) :
    potential l u n x = PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) h •
      potential l u m (chart n m k x) := by
  rw [← potential_weight]
  exact potential_transport l u H hfixed n m k hi HS x hx


-- @@ L190-196 verbatim
theorem pressureMode_transport_weight (x : FullPoint) (hx : x.1.2.1 ∈
    ActualInitialCoherence.overlap n m) :
    pressureMode l u n x = PhysicalParticularWave.pressureWeight h (ChartScales.Q n) (ChartScales.Q
        m) •
      pressureMode l u m (chart n m k x) := by
  rw [← pressure_weight]
  exact pressureMode_transport l u H hfixed n m k hi HS x hx


-- @@ L198-203 verbatim
theorem rescaledPotential_transport (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap
    n m) :
    rescaledPotential l u n x = rescaledPotential l u m (chart n m k x) := by
  unfold rescaledPotential
  rw [potential_transport_weight l u H hfixed n m k hi HS x hx, smul_smul,
    mul_comm, PhysicalParticularWave.ratioPower_cancel (ChartScales.Q_pos n) (ChartScales.Q_pos m)]


-- @@ L205-211 verbatim
theorem rescaledPressureMode_transport (x : FullPoint) (hx : x.1.2.1 ∈
    ActualInitialCoherence.overlap n m) :
    rescaledPressureMode l u n x = rescaledPressureMode l u m (chart n m k x) := by
  unfold rescaledPressureMode
  rw [pressureMode_transport_weight l u H hfixed n m k hi HS x hx, smul_smul,
    PhysicalParticularWave.pressureWeight, mul_comm,
    PhysicalParticularWave.ratioPower_cancel (ChartScales.Q_pos n) (ChartScales.Q_pos m)]


-- @@ L213-220 verbatim
theorem potential_transport_germ (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap n
    m) :
    potential l u n =ᶠ[𝓝 x] fun y => (bandVelocityScale h n m / bandScale n m) •
      potential l u m (chart n m k y) := by
  have hU : {y : FullPoint | y.1.2.1 ∈ ActualInitialCoherence.overlap n m} ∈ 𝓝 x :=
    ((ActualInitialCoherence.overlap_open n m).preimage continuous_fst.snd.fst).mem_nhds hx
  filter_upwards [hU] with y hy
  exact potential_transport l u H hfixed n m k hi HS y hy


-- @@ L222-229 verbatim
theorem pressureMode_transport_germ (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap
    n m) :
    pressureMode l u n =ᶠ[𝓝 x] fun y => (bandVelocityScale h n m * bandVelocityScale h n m) •
      pressureMode l u m (chart n m k y) := by
  have hU : {y : FullPoint | y.1.2.1 ∈ ActualInitialCoherence.overlap n m} ∈ 𝓝 x :=
    ((ActualInitialCoherence.overlap_open n m).preimage continuous_fst.snd.fst).mem_nhds hx
  filter_upwards [hU] with y hy
  exact pressureMode_transport l u H hfixed n m k hi HS y hy


-- @@ L231-237 verbatim
theorem rescaledPotential_transport_germ (x : FullPoint) (hx : x.1.2.1 ∈
    ActualInitialCoherence.overlap n m) :
    rescaledPotential l u n =ᶠ[𝓝 x] fun y => rescaledPotential l u m (chart n m k y) := by
  have hU : {y : FullPoint | y.1.2.1 ∈ ActualInitialCoherence.overlap n m} ∈ 𝓝 x :=
    ((ActualInitialCoherence.overlap_open n m).preimage continuous_fst.snd.fst).mem_nhds hx
  filter_upwards [hU] with y hy
  exact rescaledPotential_transport l u H hfixed n m k hi HS y hy


-- @@ L239-245 verbatim
theorem rescaledPressureMode_transport_germ (x : FullPoint) (hx : x.1.2.1 ∈
    ActualInitialCoherence.overlap n m) :
    rescaledPressureMode l u n =ᶠ[𝓝 x] fun y => rescaledPressureMode l u m (chart n m k y) := by
  have hU : {y : FullPoint | y.1.2.1 ∈ ActualInitialCoherence.overlap n m} ∈ 𝓝 x :=
    ((ActualInitialCoherence.overlap_open n m).preimage continuous_fst.snd.fst).mem_nhds hx
  filter_upwards [hU] with y hy
  exact rescaledPressureMode_transport l u H hfixed n m k hi HS y hy


-- @@ L247-247 verbatim
end IncomingState


-- @@ L249-249 verbatim
/-! ## Comparing any two valid current-band representatives -/


-- @@ L251-256 verbatim
theorem chart_eq_of_absolute (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x y : FullPoint)
    (hxy : ActualPrimaryCoherence.absoluteChart n x = ActualPrimaryCoherence.absoluteChart m y) :
    chart n m k x = y := by
  apply (ActualPrimaryCoherence.absoluteChart m).injective
  exact (chart_absolute n m k hi x).trans hxy


-- @@ L258-283 verbatim
theorem rescaled_eq_of_absolute_of_index (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x y : FullPoint) (hx : x.1.2.1 ∈ standardRegion.carrier) (hy : y.1.2.1 ∈
        standardRegion.carrier)
    (hxy : ActualPrimaryCoherence.absoluteChart n x = ActualPrimaryCoherence.absoluteChart m y) :
    rescaledPotential l u n x = rescaledPotential l u m y ∧
      rescaledPressureMode l u n x = rescaledPressureMode l u m y := by
  have he := chart_eq_of_absolute n m k hi x y hxy
  have hslow : bandSlowEquiv h n m x.1.2.1 = y.1.2.1 :=
    congrArg (fun z : FullPoint => z.1.2.1) he
  have ho : x.1.2.1 ∈ ActualInitialCoherence.overlap n m := by
    refine ⟨hx, ?_⟩
    change bandSlowEquiv h n m x.1.2.1 ∈ standardRegion.carrier
    rw [hslow]
    exact hy
  constructor
  · simpa only [he] using rescaledPotential_transport l u H hfixed n m k hi HS x ho
  · simpa only [he] using rescaledPressureMode_transport l u H hfixed n m k hi HS x ho


-- @@ L285-310 verbatim
/-- Either order of the two common indices is allowed. The only coherence
input concerns the incoming state, on its actual full-fiber overlaps. -/
theorem rescaled_eq_of_absolute (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (HS : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
      PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
          (ActualInitialCoherence.overlap n m))
        (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (n m : ℕ) (x y : FullPoint)
    (hx : x.1.2.1 ∈ standardRegion.carrier) (hy : y.1.2.1 ∈ standardRegion.carrier)
    (hxy : ActualPrimaryCoherence.absoluteChart n x = ActualPrimaryCoherence.absoluteChart m y) :
    rescaledPotential l u n x = rescaledPotential l u m y ∧
      rescaledPressureMode l u n x = rescaledPressureMode l u m y := by
  rcases le_total (CommonWindow.index h n) (CommonWindow.index h m) with hn | hm
  · have hi : CommonWindow.index h n + (CommonWindow.index h m - CommonWindow.index h n) =
        CommonWindow.index h m := Nat.add_sub_of_le hn
    exact rescaled_eq_of_absolute_of_index l u H hfixed n m _ hi (HS n m _ hi) x y hx hy hxy
  · have hi : CommonWindow.index h m + (CommonWindow.index h n - CommonWindow.index h m) =
        CommonWindow.index h n := Nat.add_sub_of_le hm
    have he := rescaled_eq_of_absolute_of_index l u H hfixed m n _ hi (HS m n _ hi) y x hy hx
        hxy.symm
    exact ⟨he.1.symm, he.2.symm⟩


-- @@ L312-312 verbatim
/-! ## The actual cylindrical graph, with the slow-coordinate swap explicit -/


-- @@ L314-317 verbatim
/-- `commonGraph` uses `(Z,T)`; the correction state uses `(T,Z)`. -/
noncomputable def nativePoint (n : ℕ) (z : ProblemStatement.SpaceTime) : FullPoint :=
  PhysicalResidualTZ.swapCylinder
    ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).map z)


-- @@ L319-322 verbatim
theorem nativePoint_absolute (n : ℕ) (z : ProblemStatement.SpaceTime) (hr : 0 < z.2 0) :
    ActualPrimaryCoherence.absoluteChart n (nativePoint n z) = ActualPrimaryCoherence.physicalLift
        z :=
  ActualPrimaryCoherence.absoluteChart_physical n hr


-- @@ L324-329 verbatim
theorem chart_nativePoint (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (z : ProblemStatement.SpaceTime) (hr : 0 < z.2 0) :
    chart n m k (nativePoint n z) = nativePoint m z :=
  chart_eq_of_absolute n m k hi _ _ ((nativePoint_absolute n z hr).trans (nativePoint_absolute m z
      hr).symm)


-- @@ L331-335 verbatim
theorem nativePoint_smoothAt (n : ℕ) (z : ProblemStatement.SpaceTime) (hr : 0 < z.2 0) :
    ContDiffAt ℝ ∞ (nativePoint n) z :=
  PhysicalResidualTZ.swapCylinder.contDiff.contDiffAt.comp z
    ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (CommonWindow.index h n)).map_smoothAt
      (mul_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) hr).ne')


-- @@ L337-340 verbatim
/-- Cylindrical potential, given by `rescaledPotential l u n (nativePoint n z)`. -/
noncomputable def cylindricalPotential (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : ProblemStatement.SpaceTime) : ComplexVector :=
  rescaledPotential l u n (nativePoint n z)


-- @@ L342-345 verbatim
/-- Cylindrical pressure mode, given by `rescaledPressureMode l u n (nativePoint n z)`. -/
noncomputable def cylindricalPressureMode (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n : ℕ) (z : ProblemStatement.SpaceTime) : ℂ :=
  rescaledPressureMode l u n (nativePoint n z)


-- @@ L347-349 verbatim
/-- A band is used only where its own current slow chart is valid. -/
noncomputable def physicalDomain (n : ℕ) : Set ProblemStatement.SpaceTime :=
  {z | 0 < z.2 0 ∧ (nativePoint n z).1.2.1 ∈ standardRegion.carrier}


-- @@ L351-361 verbatim
theorem physicalDomain_open (n : ℕ) : IsOpen (physicalDomain n) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hr : {w : ProblemStatement.SpaceTime | 0 < w.2 0} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous).mem_nhds
        hz.1
  have hs : {w : ProblemStatement.SpaceTime | (nativePoint n w).1.2.1 ∈ standardRegion.carrier} ∈ 𝓝
      z :=
    (nativePoint_smoothAt n z hz.1).continuousAt.fst.snd.fst.preimage_mem_nhds
      (standardRegion.isOpen.mem_nhds hz.2)
  exact inter_mem hr hs


-- @@ L363-377 verbatim
theorem cylindrical_values_eq_of_index (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (z : ProblemStatement.SpaceTime) (hn : z ∈ physicalDomain n) (hm : z ∈ physicalDomain m) :
    cylindricalPotential l u n z = cylindricalPotential l u m z ∧
      cylindricalPressureMode l u n z = cylindricalPressureMode l u m z :=
  rescaled_eq_of_absolute_of_index l u H hfixed n m k hi HS _ _ hn.2 hm.2
    ((nativePoint_absolute n z hn.1).trans (nativePoint_absolute m z hn.1).symm)


-- @@ L379-394 verbatim
theorem cylindrical_values_eq (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (HS : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
      PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
          (ActualInitialCoherence.overlap n m))
        (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (n m : ℕ) (z : ProblemStatement.SpaceTime) (hn : z ∈ physicalDomain n) (hm : z ∈ physicalDomain
        m) :
    cylindricalPotential l u n z = cylindricalPotential l u m z ∧
      cylindricalPressureMode l u n z = cylindricalPressureMode l u m z :=
  rescaled_eq_of_absolute l u H hfixed HS n m _ _ hn.2 hm.2
    ((nativePoint_absolute n z hn.1).trans (nativePoint_absolute m z hn.1).symm)


-- @@ L396-416 verbatim
theorem cylindrical_values_germ (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (HS : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
      PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
          (ActualInitialCoherence.overlap n m))
        (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (n m : ℕ) (z : ProblemStatement.SpaceTime) (hn : z ∈ physicalDomain n) (hm : z ∈ physicalDomain
        m) :
    cylindricalPotential l u n =ᶠ[𝓝 z] cylindricalPotential l u m ∧
      cylindricalPressureMode l u n =ᶠ[𝓝 z] cylindricalPressureMode l u m := by
  have hN := (physicalDomain_open n).mem_nhds hn
  have hM := (physicalDomain_open m).mem_nhds hm
  constructor
  · filter_upwards [hN, hM] with w hwn hwm
    exact (cylindrical_values_eq l u H hfixed HS n m w hwn hwm).1
  · filter_upwards [hN, hM] with w hwn hwm
    exact (cylindrical_values_eq l u H hfixed HS n m w hwn hwm).2


-- @@ L418-418 verbatim
end NavierStokes.ActualSignedPotentialCoherence
