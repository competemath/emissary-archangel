/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleResidualBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanPotentialRealization
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPolarCoverage


-- @@ L13-20 verbatim
/-!
# Physical residual fields from the literal mixed prefixes

Local per-stage polar identities are converted to cylindrical germs.
The angle-branch conversion uses the actual harmonic periodicity of the
stored correction state.  Exterior statements use pointwise identities
on an open past sublevel, not global topological support.
-/


-- @@ L22-22 verbatim
section


-- @@ L24-31 verbatim
/-!
# Exterior identities for the actual finite physical prefixes

The assumptions concern the primitive potential, direct velocity, and
pressure stages on the genuine past exterior sublevel. Openness turns their
pointwise identities into the germs needed by the spatial curl. No global
support condition or final velocity identity is assumed.
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
namespace NavierStokes.ActualExteriorPrefix


-- @@ L39-39 verbatim
open Set Filter ProblemStatement PhysicalWaveSum CorrectionInitialization

-- @@ L40-40 verbatim
open scoped Topology BigOperators


-- @@ L42-45 verbatim
/-- The open physical exterior on which the raw stages are constructed. -/
noncomputable def exteriorDomain (Nr : ℕ) : Set SpaceTime :=
  {w | w ∈ preterminal ∧ w ∉ ActualPolarCoverage.active} ∩
    CutStageEstimates.physicalSublevel ActualPrimary.h (ChartScales.Q Nr)


-- @@ L47-54 verbatim
theorem mem_exteriorDomain {Nr : ℕ} {w : SpaceTime} :
    w ∈ exteriorDomain Nr ↔ w ∈ preterminal ∧
      physicalQ ActualPrimary.h w < ChartScales.Q Nr ∧ w ∉ ActualPolarCoverage.active := by
  constructor
  · intro hw
    exact ⟨hw.1.1, hw.2.2, hw.1.2⟩
  · rintro ⟨ht, hq, hout⟩
    exact ⟨⟨ht, hout⟩, ht, hq⟩


-- @@ L56-64 verbatim
theorem exteriorDomain_open (Nr : ℕ) : IsOpen (exteriorDomain Nr) := by
  have ho : IsOpen {w : SpaceTime | w ∈ preterminal ∧ w ∉ ActualPolarCoverage.active} := by
    exact BaseResidual.chartedDomain_isOpen ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half
      (show IsOpen {p : ℝ × ℝ | p.1 ∉ Icc (NominalConeAssembly.activeLeft ActualPrimary.nominal)
        (NominalConeAssembly.activeRight ActualPrimary.nominal)} from
        (isClosed_Icc.preimage continuous_fst).isOpen_compl)
  exact ho.inter (CutStageEstimates.physicalSublevel_open
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half _)


-- @@ L66-71 verbatim
/-- Local primitive equality gives an ambient germ at every exterior point. -/
theorem eqOn_exterior_germ {V : Type*} {Nr : ℕ} {f g : SpaceTime → V}
    (h : EqOn f g (exteriorDomain Nr)) {w : SpaceTime} (hw : w ∈ exteriorDomain Nr) :
    f =ᶠ[𝓝 w] g := by
  filter_upwards [(exteriorDomain_open Nr).mem_nhds hw] with y hy
  exact h hy


-- @@ L73-87 verbatim
/-- Primitive stage data on the valid exterior. The direct angular field
vanishes also at stage zero; the potential and pressure retain their actual
slow-base stage zero. -/
structure ExteriorStages (B Nr : ℕ) (A D : ℕ → VelocityField) (P : ℕ → PressureField) : Prop where
  potential_zero : EqOn (A 0)
    (TailGaugePotential.finalPotential ActualPrimary.certificate ActualPrimary.modulation
        ActualPrimary.upper B)
    (exteriorDomain Nr)
  potential_succ : ∀ k, EqOn (A (k + 1)) 0 (exteriorDomain Nr)
  direct_zero : ∀ k, EqOn (D k) 0 (exteriorDomain Nr)
  pressure_zero : EqOn (P 0)
    (FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation ActualPrimary.upper
        B)
    (exteriorDomain Nr)
  pressure_succ : ∀ k, EqOn (P (k + 1)) 0 (exteriorDomain Nr)


-- @@ L89-89 verbatim
section PrefixAlgebra


-- @@ L91-91 verbatim
variable {V : Type*} [NormedAddCommGroup V]


-- @@ L93-107 verbatim
theorem uncutPrefix_eqOn_first {A : ℕ → SpaceTime → V} {f : SpaceTime → V} {U : Set SpaceTime}
    (h0 : EqOn (A 0) f U) (h : ∀ k, EqOn (A (k + 1)) 0 U) (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix A (J + 1)) f U := by
  classical
  intro w hw
  calc
    DiagonalJetBounds.uncutPrefix A (J + 1) w = A 0 w := by
      unfold DiagonalJetBounds.uncutPrefix
      apply Finset.sum_eq_single 0
      · intro k hk hk0
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        exact h l hw
      · intro hmem
        exact False.elim (hmem (Finset.mem_range.mpr (Nat.zero_lt_succ J)))
    _ = f w := h0 hw


-- @@ L109-114 verbatim
theorem uncutPrefix_eqOn_zero {A : ℕ → SpaceTime → V} {U : Set SpaceTime}
    (h : ∀ k, EqOn (A k) 0 U) (N : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix A N) 0 U := by
  intro w hw
  unfold DiagonalJetBounds.uncutPrefix
  exact Finset.sum_eq_zero (fun k _ => h k hw)


-- @@ L116-116 verbatim
end PrefixAlgebra


-- @@ L118-118 verbatim
namespace ExteriorStages


-- @@ L120-121 verbatim
variable {B Nr : ℕ} {A D : ℕ → VelocityField} {P : ℕ → PressureField}
    (H : ExteriorStages B Nr A D P)


-- @@ L123-123 verbatim
include H


-- @@ L125-130 verbatim
theorem potential_prefix_eqOn (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix A (J + 1))
      (TailGaugePotential.finalPotential ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B)
      (exteriorDomain Nr) :=
  uncutPrefix_eqOn_first H.potential_zero H.potential_succ J


-- @@ L132-134 verbatim
theorem direct_prefix_eqOn (N : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix D N) 0 (exteriorDomain Nr) :=
  uncutPrefix_eqOn_zero H.direct_zero N


-- @@ L136-141 verbatim
theorem pressure_prefix_eqOn (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix P (J + 1))
      (FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B)
      (exteriorDomain Nr) :=
  uncutPrefix_eqOn_first H.pressure_zero H.pressure_succ J


-- @@ L143-147 verbatim
theorem potential_prefix_germ (J : ℕ) {w : SpaceTime} (hw : w ∈ exteriorDomain Nr) :
    DiagonalJetBounds.uncutPrefix A (J + 1) =ᶠ[𝓝 w]
      TailGaugePotential.finalPotential ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B :=
  eqOn_exterior_germ (H.potential_prefix_eqOn J) hw


-- @@ L149-164 verbatim
/-- The spatial curl sees the actual potential germ, so the finite velocity
prefix agrees with the slow base without any differentiability premise on
the totalized raw stages. -/
theorem velocity_prefix_eqOn (J : ℕ) :
    EqOn (MixedDiagonalResidual.uncutVelocity A D J)
      (FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B)
      (exteriorDomain Nr) := by
  intro w hw
  change SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1)) w +
    DiagonalJetBounds.uncutPrefix D (J + 1) w = _
  rw [PhysicalCurlCovariance.spatialCurl_congr (H.potential_prefix_germ J hw),
    H.direct_prefix_eqOn (J + 1) hw]
  simpa only [Pi.zero_apply, add_zero] using
    TailGaugePotential.finalPotential_sameCurl ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B hw.1.1


-- @@ L166-177 verbatim
/-- The exterior part of the physical realization required for each finite
cycle follows solely from the primitive stage identities. -/
theorem prefix_exterior (J : ℕ) {w : SpaceTime} (ht : w ∈ preterminal)
    (hq : physicalQ ActualPrimary.h w < ChartScales.Q Nr) (hout : w ∉ ActualPolarCoverage.active) :
    MixedDiagonalResidual.uncutVelocity A D J w =
        FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
            ActualPrimary.upper B w ∧
      DiagonalJetBounds.uncutPrefix P (J + 1) w =
        FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
            ActualPrimary.upper B w := by
  have hw := mem_exteriorDomain.mpr ⟨ht, hq, hout⟩
  exact ⟨H.velocity_prefix_eqOn J hw, H.pressure_prefix_eqOn J hw⟩


-- @@ L179-187 verbatim
theorem prefix_germs (J : ℕ) {w : SpaceTime} (hw : w ∈ exteriorDomain Nr) :
    MixedDiagonalResidual.uncutVelocity A D J =ᶠ[𝓝 w]
        FinalSlowBase.velocity ActualPrimary.certificate ActualPrimary.modulation
            ActualPrimary.upper B ∧
      DiagonalJetBounds.uncutPrefix P (J + 1) =ᶠ[𝓝 w]
        FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
            ActualPrimary.upper B :=
  ⟨eqOn_exterior_germ (H.velocity_prefix_eqOn J) hw,
    eqOn_exterior_germ (H.pressure_prefix_eqOn J) hw⟩


-- @@ L189-189 verbatim
end ExteriorStages


-- @@ L191-191 verbatim
end NavierStokes.ActualExteriorPrefix


-- @@ L193-193 verbatim
end

-- @@ L194-194 verbatim
end


-- @@ L196-196 verbatim
end


-- @@ L198-198 verbatim
@[expose] public section


-- @@ L200-200 verbatim
noncomputable section


-- @@ L202-202 verbatim
namespace NavierStokes.ActualPhysicalPrefixFields


-- @@ L204-204 verbatim
open Set Function Filter ProblemStatement CorrectionState CorrectionStep

-- @@ L205-205 verbatim
open scoped Topology ContDiff BigOperators


-- @@ L207-208 verbatim
/-- Point: an abbreviation for `PhysicalMeanJetBounds.Point`. -/
abbrev Point := PhysicalMeanJetBounds.Point

-- @@ L209-210 verbatim
/-- Cylinder: an abbreviation for `PhysicalResidualBridge.Cylinder`. -/
abbrev Cylinder := PhysicalResidualBridge.Cylinder

-- @@ L211-212 verbatim
/-- Scaled graph: an abbreviation for `PhysicalResidualBridge.ScaledGraph`. -/
abbrev ScaledGraph := PhysicalResidualBridge.ScaledGraph


-- @@ L214-216 verbatim
/-- Forward, given by `(z.1, CylindricalResidual.chart z.2)`. -/
noncomputable def forward (z : SpaceTime) : SpaceTime :=
  (z.1, CylindricalResidual.chart z.2)


-- @@ L218-219 verbatim
theorem forward_smooth : ContDiff ℝ ∞ forward :=
  contDiff_fst.prodMk (CylindricalResidual.contDiff_chart.comp contDiff_snd)


-- @@ L221-223 verbatim
/-- Replace angle, given by `(z.1, AxisymmetricResidual.pack (z.2 0) theta (z.2 2))`. -/
noncomputable def replaceAngle (z : SpaceTime) (theta : ℝ) : SpaceTime :=
  (z.1, AxisymmetricResidual.pack (z.2 0) theta (z.2 2))


-- @@ L225-230 verbatim
@[simp] theorem replaceAngle_self (z : SpaceTime) : replaceAngle z (z.2 1) = z := by
  unfold replaceAngle
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> simp


-- @@ L232-235 verbatim
/-- Angular periodic, given by `∀ z, Function.Periodic (fun theta => f (replaceAngle z theta))
(2 * Real.pi)`. -/
def AngularPeriodic {E : Type*} (f : SpaceTime → E) : Prop :=
  ∀ z, Function.Periodic (fun theta => f (replaceAngle z theta)) (2 * Real.pi)


-- @@ L237-244 verbatim
theorem periodic_eq_of_cos_sin {E : Type*} {f : ℝ → E}
    (hf : Function.Periodic f (2 * Real.pi)) {alpha beta : ℝ}
    (hc : Real.cos alpha = Real.cos beta) (hs : Real.sin alpha = Real.sin beta) :
    f alpha = f beta := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
  have he : alpha = beta + (k : ℝ) * (2 * Real.pi) := by nlinarith [hk]
  rw [he]
  exact hf.int_mul k beta


-- @@ L246-262 verbatim
theorem polarCoordinates_shape {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {z : SpaceTime} (hr : 0 < z.2 0)
    (hc : forward z ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    PhysicalCurlCovariance.polarCoordinates a i (forward z) =
      replaceAngle z (PhysicalCurlCovariance.polarInput a i (forward z)).2 := by
  have hrad := PhysicalCurlCovariance.polarCoordinates_radius ha i hc
  simp only [forward] at hrad
  rw [ActualMeanPotentialRealization.projection_forward, PolarCharts.radius_polar,
    abs_of_pos hr] at hrad
  unfold PhysicalCurlCovariance.polarCoordinates replaceAngle
  apply Prod.ext
  · rfl
  · ext j
    fin_cases j
    · simpa [PhysicalCurlCovariance.polarCoordinates, forward] using hrad
    · simp
    · simp [forward, CylindricalResidual.chart]


-- @@ L264-275 verbatim
theorem polarInput_cos_sin {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {z : SpaceTime} (hr : 0 < z.2 0)
    (hc : forward z ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    Real.cos (PhysicalCurlCovariance.polarInput a i (forward z)).2 = Real.cos (z.2 1) ∧
      Real.sin (PhysicalCurlCovariance.polarInput a i (forward z)).2 = Real.sin (z.2 1) := by
  have hb := ActualMeanPotentialRealization.polarCoordinates_back ha i hc
  rw [polarCoordinates_shape ha i hr hc] at hb
  have h0 := congrArg (fun w : SpaceTime => w.2 0) hb
  have h1 := congrArg (fun w : SpaceTime => w.2 1) hb
  simp only [replaceAngle, forward, CylindricalResidual.chart,
    AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one] at h0 h1
  exact ⟨mul_left_cancel₀ hr.ne' h0, mul_left_cancel₀ hr.ne' h1⟩


-- @@ L277-285 verbatim
theorem polarPressure_forward {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {f : PressureField} (hf : AngularPeriodic f) {z : SpaceTime} (hr : 0 < z.2 0)
    (hc : forward z ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    CyclePhysicalPrefixes.polarPressureMap a i f (forward z) = f z := by
  change f (PhysicalCurlCovariance.polarCoordinates a i (forward z)) = f z
  rw [polarCoordinates_shape ha i hr hc]
  have he := periodic_eq_of_cos_sin (hf z) (polarInput_cos_sin ha i hr hc).1
    (polarInput_cos_sin ha i hr hc).2
  simpa only [replaceAngle_self] using he


-- @@ L287-299 verbatim
theorem polarVelocity_forward {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {f : VelocityField} (hf : AngularPeriodic f) {z : SpaceTime} (hr : 0 < z.2 0)
    (hc : forward z ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    CyclePhysicalPrefixes.polarVelocityMap a i f (forward z) =
      CylindricalResidual.frame (z.2 1) (f z) := by
  change CylindricalResidual.frame (PhysicalCurlCovariance.polarInput a i (forward z)).2
    (f (PhysicalCurlCovariance.polarCoordinates a i (forward z))) = _
  rw [polarCoordinates_shape ha i hr hc]
  have he := periodic_eq_of_cos_sin (hf z) (polarInput_cos_sin ha i hr hc).1
    (polarInput_cos_sin ha i hr hc).2
  rw [he, replaceAngle_self]
  simp only [CylindricalResidual.frame_apply, (polarInput_cos_sin ha i hr hc).1,
    (polarInput_cos_sin ha i hr hc).2]


-- @@ L301-313 verbatim
theorem velocity_pullback_germ {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {u f : VelocityField} (hf : AngularPeriodic f) {V : Set SpaceTime} (hV : IsOpen V)
    (hu : EqOn u (CyclePhysicalPrefixes.polarVelocityMap a i f) V)
    {z : SpaceTime} (hr : 0 < z.2 0) (hz : forward z ∈ V)
    (hc : forward z ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    (u ∘ forward) =ᶠ[𝓝 z] (fun y => CylindricalResidual.frame (y.2 1) (f y)) := by
  filter_upwards [forward_smooth.continuous.continuousAt (hV.mem_nhds hz),
    forward_smooth.continuous.continuousAt
      ((ActualMeanPotentialRealization.cartesianDomain_open a i).mem_nhds hc),
    (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous).mem_nhds
        hr]
    with y hy hyc hyr
  exact (hu hy).trans (polarVelocity_forward ha i hf hyr hyc)


-- @@ L315-327 verbatim
theorem pressure_pullback_germ {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index)
    {P f : PressureField} (hf : AngularPeriodic f) {V : Set SpaceTime} (hV : IsOpen V)
    (hP : EqOn P (CyclePhysicalPrefixes.polarPressureMap a i f) V)
    {z : SpaceTime} (hr : 0 < z.2 0) (hz : forward z ∈ V)
    (hc : forward z ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    CylindricalResidual.pressurePullback P =ᶠ[𝓝 z] f := by
  filter_upwards [forward_smooth.continuous.continuousAt (hV.mem_nhds hz),
    forward_smooth.continuous.continuousAt
      ((ActualMeanPotentialRealization.cartesianDomain_open a i).mem_nhds hc),
    (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous).mem_nhds
        hr]
    with y hy hyc hyr
  exact (hP hy).trans (polarPressure_forward ha i hf hyr hyc)


-- @@ L329-329 verbatim
/-! ## Periodicity comes from the stored harmonic representation -/


-- @@ L331-339 verbatim
theorem represented_oscillation_periodic {ι : Type} {v : CycleCoefficients ι}
    {s : State Point} {axis : AxisymmetricAlias} (H : CycleRepresentation v s axis)
    (n : ℕ) (x : Point) (j : Fin 3) :
    Function.Periodic (fun theta => s.oscillation n (x, theta) j) (2 * Real.pi) := by
  intro theta
  dsimp only
  rw [H.velocity, H.velocity]
  exact Finset.sum_congr rfl (fun l _ => congrArg Complex.re
    (HarmonicFields.field_angular_periodic _ _ _ _ _ theta))


-- @@ L341-349 verbatim
theorem represented_pressure_periodic {ι : Type} {v : CycleCoefficients ι}
    {s : State Point} {axis : AxisymmetricAlias} (H : CycleRepresentation v s axis)
    (n : ℕ) (x : Point) :
    Function.Periodic (fun theta => s.oscillatoryPressure n (x, theta)) (2 * Real.pi) := by
  intro theta
  dsimp only
  rw [H.pressure, H.pressure]
  exact Finset.sum_congr rfl (fun l _ => congrArg Complex.re
    (HarmonicFields.field_angular_periodic _ _ _ _ _ theta))


-- @@ L351-361 verbatim
theorem represented_components_periodic {ι : Type} {v : CycleCoefficients ι}
    {s : State Point} {axis : AxisymmetricAlias} (H : CycleRepresentation v s axis)
    (c : Context Point) (n : ℕ) (x : Point) :
    Function.Periodic (fun theta => (PhysicalResidualBridge.baseComponents c n +
      PhysicalResidualBridge.incrementComponents s n) (x, theta)) (2 * Real.pi) := by
  intro theta
  funext j
  have hp (k : Fin 3) : s.oscillation n (x, theta + 2 * Real.pi) k =
      s.oscillation n (x, theta) k := represented_oscillation_periodic H n x k theta
  fin_cases j <;> simp [PhysicalResidualBridge.baseComponents,
    PhysicalResidualBridge.incrementComponents, hp]


-- @@ L363-368 verbatim
theorem represented_totalPressure_periodic {ι : Type} {v : CycleCoefficients ι}
    {s : State Point} {axis : AxisymmetricAlias} (H : CycleRepresentation v s axis)
    (n : ℕ) (x : Point) :
    Function.Periodic (fun theta => s.totalPressureIncrement n (x, theta)) (2 * Real.pi) := by
  intro theta
  exact congrArg (s.pressure n x + ·) (represented_pressure_periodic H n x theta)


-- @@ L370-374 verbatim
theorem graphMapTZ_replaceAngle (G : ScaledGraph) (z : SpaceTime) (theta : ℝ) :
    PhysicalResidualTZ.graphMapTZ G (replaceAngle z theta) =
      ((PhysicalResidualTZ.graphMapTZ G z).1, theta) := by
  simp [PhysicalResidualTZ.graphMapTZ, replaceAngle, PhysicalResidualBridge.ScaledGraph.map,
    PhysicalResidualTZ.swapCylinder_apply, PhysicalResidualTZ.swapSlow_apply]


-- @@ L376-386 verbatim
theorem velocityTZ_periodic (G : ScaledGraph) (a : Cylinder → Fin 3 → ℝ)
    (ha : ∀ x : Point, Function.Periodic (fun theta => a (x, theta)) (2 * Real.pi)) :
    AngularPeriodic (PhysicalResidualTZ.velocityTZ G a) := by
  intro z theta
  ext j
  simp only [PhysicalResidualTZ.velocityTZ, PhysicalResidualBridge.ScaledGraph.velocity_apply]
  change G.velocityScale * a (PhysicalResidualTZ.graphMapTZ G (replaceAngle z (theta + 2 *
      Real.pi))) j =
    G.velocityScale * a (PhysicalResidualTZ.graphMapTZ G (replaceAngle z theta)) j
  rw [graphMapTZ_replaceAngle, graphMapTZ_replaceAngle]
  exact congrArg (fun v : Fin 3 → ℝ => G.velocityScale * v j) (ha _ theta)


-- @@ L388-396 verbatim
theorem pressureTZ_periodic (G : ScaledGraph) (a : Cylinder → ℝ)
    (ha : ∀ x : Point, Function.Periodic (fun theta => a (x, theta)) (2 * Real.pi)) :
    AngularPeriodic (PhysicalResidualTZ.pressureTZ G a) := by
  intro z theta
  change G.velocityScale ^ 2 * a (PhysicalResidualTZ.graphMapTZ G (replaceAngle z (theta + 2 *
      Real.pi))) =
    G.velocityScale ^ 2 * a (PhysicalResidualTZ.graphMapTZ G (replaceAngle z theta))
  rw [graphMapTZ_replaceAngle, graphMapTZ_replaceAngle]
  exact congrArg (G.velocityScale ^ 2 * ·) (ha _ theta)


-- @@ L398-398 verbatim
/-! ## Actual finite prefixes retain local stage agreement -/


-- @@ L400-405 verbatim
theorem uncutPrefix_eqOn {E : Type*} [NormedAddCommGroup E]
    {V : Set SpaceTime} {f g : ℕ → SpaceTime → E}
    (hf : ∀ k, EqOn (f k) (g k) V) (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix f J) (DiagonalJetBounds.uncutPrefix g J) V := by
  intro z hz
  exact Finset.sum_congr rfl (fun k _ => hf k hz)


-- @@ L407-421 verbatim
theorem mixedVelocity_eqOn {ι : Type} (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (a : ℝ) (i : PolarCharts.Index)
    (G : ScaledGraph) (n : ℕ) {V : Set SpaceTime} (hV : IsOpen V)
    (A D : ℕ → VelocityField) (hA : ∀ k, DifferentiableOn ℝ (A k) V)
    (hc : ∀ k, EqOn (SpatialCurl.spatialCurl (A k))
      (CyclePhysicalPrefixes.potentialParts p c seed a i G n k) V)
    (hD : ∀ k, EqOn (D k) (CyclePhysicalPrefixes.directStages p c seed a i G n k) V)
    (J : ℕ) :
    EqOn (MixedDiagonalResidual.uncutVelocity A D J)
      (CyclePhysicalPrefixes.velocity a i G n c (CycleState.iterate p c seed J).state) V := by
  intro z hz
  change SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J+1)) z +
    DiagonalJetBounds.uncutPrefix D (J+1) z = _
  rw [uncutPrefix_eqOn hD (J+1) hz]
  exact CyclePhysicalPrefixes.mixedVelocity_prefix p c seed a i G n hV A hA hc J hz


-- @@ L423-432 verbatim
theorem pressurePrefix_eqOn {ι : Type} (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (a : ℝ) (i : PolarCharts.Index)
    (G : ScaledGraph) (n : ℕ) (p0 : Cylinder → ℝ) {V : Set SpaceTime}
    (P : ℕ → PressureField)
    (hP : ∀ k, EqOn (P k) (CyclePhysicalPrefixes.pressureStages p c seed a i G n p0 k) V)
    (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix P (J+1))
      (CyclePhysicalPrefixes.pressure a i G n p0 (CycleState.iterate p c seed J).state) V := by
  rw [← CyclePhysicalPrefixes.pressure_prefix p c seed a i G n p0 J]
  exact uncutPrefix_eqOn hP (J+1)


-- @@ L434-434 verbatim
/-! ## Open valid charts and the honest residual floor -/


-- @@ L436-446 verbatim
theorem graphSource_open (G : ScaledGraph) (hl : 0 < G.radialScale)
    {U : Set Cylinder} (hU : IsOpen U) : IsOpen (PhysicalResidualTZ.graphSourceTZ G U) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hg : ContinuousAt (PhysicalResidualTZ.graphMapTZ G) z :=
    PhysicalResidualTZ.swapCylinder.continuous.continuousAt.comp
      (G.map_smoothAt (mul_pos hl hz.1).ne').continuousAt
  exact Filter.inter_mem
    ((isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous).mem_nhds
        hz.1)
    (hg (hU.mem_nhds hz.2))


-- @@ L448-460 verbatim
theorem exists_cartesianChart {z : SpaceTime} (hr : 0 < z.2 0) :
    ∃ a : ℝ, 0 < a ∧ ∃ i : PolarCharts.Index,
      forward z ∈ ActualMeanPotentialRealization.cartesianDomain a i := by
  have he : PolarCharts.radius (PhysicalGraphBounds.radialProjection (forward z)) = z.2 0 :=
    ActualMeanPotentialRealization.radius_forward hr
  have hnorm : z.2 0 / 2 ≤ ‖PhysicalGraphBounds.radialProjection (forward z)‖ := by
    have hb := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.radialProjection (forward z))
    rw [he] at hb
    linarith
  obtain ⟨i, hi⟩ := PolarCharts.exists_rotate_fst_ge hnorm
  refine ⟨z.2 0, hr, i, ?_⟩
  change z.2 0 / 4 < (PolarCharts.rotate i (PhysicalGraphBounds.radialProjection (forward z))).1
  linarith


-- @@ L462-462 verbatim
open CorrectionInitialization.ActualPrimary


-- @@ L464-468 verbatim
/-- Source, given by `PhysicalResidualTZ.graphSourceTZ
(ActualCycleResidualBounds.actualBandGraph n) ActualPolarCoverage.nativeDomain`. -/
noncomputable def source (n : ℕ) : Set SpaceTime :=
  PhysicalResidualTZ.graphSourceTZ (ActualCycleResidualBounds.actualBandGraph n)
    ActualPolarCoverage.nativeDomain


-- @@ L470-475 verbatim
/-- Cartesian chart domain, constructed using `CutStageEstimates.physicalSublevel`. -/
noncomputable def cartesianChartDomain (qbig : ℝ) (n : ℕ) (a : ℝ) (i : PolarCharts.Index) : Set
    SpaceTime :=
  CutStageEstimates.physicalSublevel h qbig ∩
    (ActualMeanPotentialRealization.cartesianDomain a i ∩
      (PhysicalCurlCovariance.polarCoordinates a i) ⁻¹' source n)


-- @@ L477-479 verbatim
theorem source_open (n : ℕ) : IsOpen (source n) :=
  graphSource_open _ (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)
      ActualPolarCoverage.nativeDomain_open


-- @@ L481-485 verbatim
theorem cartesianChartDomain_open (qbig : ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) :
    IsOpen (cartesianChartDomain qbig n a i) :=
  (CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half qbig).inter
    ((ActualMeanPotentialRealization.cartesianDomain_open a i).inter
      ((source_open n).preimage (PhysicalCurlCovariance.polarCoordinates_smooth ha i).continuous))


-- @@ L487-504 verbatim
theorem source_q_lt (n : ℕ) {z : SpaceTime} (ht : z ∈ PhysicalWaveSum.preterminal)
    (hz : z ∈ source n) :
    PhysicalWaveSum.physicalQ h (forward z) < 2 * ChartScales.Q n := by
  have he := ActualMeanPotentialRealization.chartPoint_eq_graph_forward h n
    (ActualCycleResidualBounds.actualGap n) (Nat.sub_le _ _) hz.1
  rw [ActualCycleResidualBounds.actualGap_index] at he
  change (PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n) z).1 =
    PhysicalMeanJetBounds.graph h n (ActualCycleResidualBounds.actualGap n) (forward z) at he
  have hs : (PhysicalMeanJetBounds.graph h n (ActualCycleResidualBounds.actualGap n) (forward
      z)).2.1 ∈
      standardRegion.carrier := by
    rw [← he]
    exact hz.2.1.1
  have hu := hs.2.2
  rw [PhysicalMeanJetBounds.graph_q_eq outgoing.data.h_pos outgoing.data.h_lt_half n
    (ActualCycleResidualBounds.actualGap n) (show forward z ∈ PhysicalWaveSum.preterminal from ht)]
        at hu
  exact (div_lt_iff₀ (ChartScales.Q_pos n)).mp hu


-- @@ L506-511 verbatim
theorem source_sublevel {Nr : ℕ} {qbig : ℝ} (hfloor : 2 * ChartScales.Q Nr ≤ qbig)
    {n : ℕ} (hn : Nr ≤ n) {z : SpaceTime} (ht : z ∈ PhysicalWaveSum.preterminal)
    (hz : z ∈ source n) : forward z ∈ CutStageEstimates.physicalSublevel h qbig :=
  ⟨ht, (source_q_lt n ht hz).trans_le
    ((mul_le_mul_of_nonneg_left (ActualPrimaryCovariance.Q_antitone hn) (by
        norm_num)).trans hfloor)⟩


-- @@ L513-523 verbatim
theorem source_polarCoordinates {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (n : ℕ)
    {z : SpaceTime} (hz : z ∈ source n)
    (hc : forward z ∈ ActualMeanPotentialRealization.cartesianDomain a i) :
    PhysicalCurlCovariance.polarCoordinates a i (forward z) ∈ source n := by
  rw [polarCoordinates_shape ha i hz.1 hc]
  constructor
  · simpa only [replaceAngle, AxisymmetricResidual.pack_zero] using hz.1
  · change PhysicalResidualTZ.graphMapTZ (ActualCycleResidualBounds.actualBandGraph n)
      (replaceAngle z _) ∈ ActualPolarCoverage.nativeDomain
    rw [graphMapTZ_replaceAngle]
    exact ⟨hz.2.1, Set.mem_univ _⟩


-- @@ L525-530 verbatim
theorem exists_validChart {Nr : ℕ} {qbig : ℝ} (hfloor : 2 * ChartScales.Q Nr ≤ qbig)
    {n : ℕ} (hn : Nr ≤ n) {z : SpaceTime} (ht : z ∈ PhysicalWaveSum.preterminal)
    (hz : z ∈ source n) :
    ∃ a : ℝ, 0 < a ∧ ∃ i : PolarCharts.Index, forward z ∈ cartesianChartDomain qbig n a i := by
  obtain ⟨a, ha, i, hi⟩ := exists_cartesianChart hz.1
  exact ⟨a, ha, i, source_sublevel hfloor hn ht hz, hi, source_polarCoordinates ha i n hz hi⟩


-- @@ L532-544 verbatim
theorem actual_pressure_periodic {ι : Type} {v : CycleCoefficients ι} {s : State Point}
    {axis : AxisymmetricAlias} (H : CycleRepresentation v s axis) (B n : ℕ) (x : Point) :
    Function.Periodic (fun theta => (ActualCycleResidualBounds.actualBasePressure B n +
      s.totalPressureIncrement n) (x, theta)) (2 * Real.pi) := by
  intro theta
  change ActualBaseResidual.basePressure certificate modulation upper B n (x, theta + 2 * Real.pi) +
      s.totalPressureIncrement n (x, theta + 2 * Real.pi) =
    ActualBaseResidual.basePressure certificate modulation upper B n (x, theta) +
      s.totalPressureIncrement n (x, theta)
  rw [ActualBaseResidual.basePressure_angle_eq certificate modulation upper B n x (theta + 2 *
      Real.pi),
    ActualBaseResidual.basePressure_angle_eq certificate modulation upper B n x theta]
  exact congrArg (_ + ·) (represented_totalPressure_periodic H n x theta)


-- @@ L546-566 verbatim
/-- Every input is an individual stage agreement on its concrete valid
polar chart. No finite-prefix or germ equality is a field of this record. -/
structure StageRealizations (B N0 Nr : ℕ) (p : ℕ → CycleParameters (ActualInitialization.Index B
    N0))
    (qbig : ℝ) (A D : ℕ → VelocityField) (P : ℕ → PressureField) : Prop where
  potential : ∀ n, Nr ≤ n → ∀ a, 0 < a → ∀ i k,
    EqOn (SpatialCurl.spatialCurl (A k))
      (CyclePhysicalPrefixes.potentialParts p (commonContext B)
          (ActualInitialization.initialCycleState B N0)
        a i (ActualCycleResidualBounds.actualBandGraph n) n k) (cartesianChartDomain qbig n a i)
  direct : ∀ n, Nr ≤ n → ∀ a, 0 < a → ∀ i k,
    EqOn (D k)
      (CyclePhysicalPrefixes.directStages p (commonContext B)
          (ActualInitialization.initialCycleState B N0)
        a i (ActualCycleResidualBounds.actualBandGraph n) n k) (cartesianChartDomain qbig n a i)
  pressure : ∀ n, Nr ≤ n → ∀ a, 0 < a → ∀ i k,
    EqOn (P k)
      (CyclePhysicalPrefixes.pressureStages p (commonContext B)
          (ActualInitialization.initialCycleState B N0)
        a i (ActualCycleResidualBounds.actualBandGraph n) n
        (ActualCycleResidualBounds.actualBasePressure B n) k) (cartesianChartDomain qbig n a i)


-- @@ L568-583 verbatim
theorem StageRealizations.velocity_prefix {B N0 Nr : ℕ}
    {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    {qbig : ℝ} {A D : ℕ → VelocityField} {P : ℕ → PressureField}
    (H : StageRealizations B N0 Nr p qbig A D P)
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) (CutStageEstimates.physicalSublevel h qbig))
    (n : ℕ) (hn : Nr ≤ n) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (J : ℕ) :
    EqOn (MixedDiagonalResidual.uncutVelocity A D J)
      (CyclePhysicalPrefixes.velocity a i (ActualCycleResidualBounds.actualBandGraph n) n
          (commonContext B)
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            J).state)
      (cartesianChartDomain qbig n a i) :=
  mixedVelocity_eqOn p (commonContext B) (ActualInitialization.initialCycleState B N0)
    a i _ n (cartesianChartDomain_open qbig n ha i) A D
    (fun k => ((hA k).mono (fun _ hx => hx.1)).differentiableOn (by simp))
    (H.potential n hn a ha i) (H.direct n hn a ha i) J


-- @@ L585-597 verbatim
theorem StageRealizations.pressure_prefix {B N0 Nr : ℕ}
    {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    {qbig : ℝ} {A D : ℕ → VelocityField} {P : ℕ → PressureField}
    (H : StageRealizations B N0 Nr p qbig A D P)
    (n : ℕ) (hn : Nr ≤ n) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) (J : ℕ) :
    EqOn (DiagonalJetBounds.uncutPrefix P (J+1))
      (CyclePhysicalPrefixes.pressure a i (ActualCycleResidualBounds.actualBandGraph n) n
        (ActualCycleResidualBounds.actualBasePressure B n)
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            J).state)
      (cartesianChartDomain qbig n a i) :=
  pressurePrefix_eqOn p (commonContext B) (ActualInitialization.initialCycleState B N0) a i _ n _ P
    (H.pressure n hn a ha i) J


-- @@ L599-629 verbatim
theorem StageRealizations.velocity_germ {B N0 Nr : ℕ}
    {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    {qbig : ℝ} {A D : ℕ → VelocityField} {P : ℕ → PressureField}
    (H : StageRealizations B N0 Nr p qbig A D P)
    (hfloor : 2 * ChartScales.Q Nr ≤ qbig)
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) (CutStageEstimates.physicalSublevel h qbig))
    (J : ℕ)
    (Hrep : CycleRepresentation
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).coefficients
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0) J).state
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).axisymmetricAlias)
    (n : ℕ) (hn : Nr ≤ n) {z : SpaceTime} (ht : z ∈ PhysicalWaveSum.preterminal)
    (hz : z ∈ source n) :
    (fun y : SpaceTime => MixedDiagonalResidual.uncutVelocity A D J (y.1, CylindricalResidual.chart
        y.2)) =ᶠ[𝓝 z]
      (fun y => CylindricalResidual.frame (y.2 1)
        (PhysicalResidualTZ.velocityTZ (ActualCycleResidualBounds.actualBandGraph n)
          (fun v i => PhysicalResidualBridge.baseComponents (commonContext B) n v i +
            PhysicalResidualBridge.incrementComponents
              (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
                  J).state n v i) y)) := by
  obtain ⟨a, ha, i, hi⟩ := exists_validChart hfloor hn ht hz
  have hp : AngularPeriodic (CyclePhysicalPrefixes.cylindricalVelocity
      (ActualCycleResidualBounds.actualBandGraph n) n (commonContext B)
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).state) :=
    velocityTZ_periodic _ _ (represented_components_periodic Hrep (commonContext B) n)
  exact velocity_pullback_germ ha i hp (cartesianChartDomain_open qbig n ha i)
    (H.velocity_prefix hA n hn ha i J) hz.1 hi hi.2.1


-- @@ L631-657 verbatim
theorem StageRealizations.pressure_germ {B N0 Nr : ℕ}
    {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    {qbig : ℝ} {A D : ℕ → VelocityField} {P : ℕ → PressureField}
    (H : StageRealizations B N0 Nr p qbig A D P)
    (hfloor : 2 * ChartScales.Q Nr ≤ qbig) (J : ℕ)
    (Hrep : CycleRepresentation
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).coefficients
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0) J).state
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).axisymmetricAlias)
    (n : ℕ) (hn : Nr ≤ n) {z : SpaceTime} (ht : z ∈ PhysicalWaveSum.preterminal)
    (hz : z ∈ source n) :
    CylindricalResidual.pressurePullback (DiagonalJetBounds.uncutPrefix P (J+1)) =ᶠ[𝓝 z]
      PhysicalResidualTZ.pressureTZ (ActualCycleResidualBounds.actualBandGraph n)
        (fun v => ActualCycleResidualBounds.actualBasePressure B n v +
          (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
              J).state.totalPressureIncrement n v) := by
  obtain ⟨a, ha, i, hi⟩ := exists_validChart hfloor hn ht hz
  have hp : AngularPeriodic (CyclePhysicalPrefixes.cylindricalPressure
      (ActualCycleResidualBounds.actualBandGraph n) n (ActualCycleResidualBounds.actualBasePressure
          B n)
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).state) :=
    pressureTZ_periodic _ _ (actual_pressure_periodic Hrep B n)
  exact pressure_pullback_germ ha i hp (cartesianChartDomain_open qbig n ha i)
    (H.pressure_prefix n hn ha i J) hz.1 hi hi.2.1


-- @@ L659-659 verbatim
/-! ## All five physical-field obligations for the same literal prefix -/


-- @@ L661-697 verbatim
theorem physicalFields_of_stages {B N0 Nr : ℕ}
    {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    {qbig : ℝ} {A D : ℕ → VelocityField} {P : ℕ → PressureField}
    (H : StageRealizations B N0 Nr p qbig A D P)
    (HE : ActualExteriorPrefix.ExteriorStages B Nr A D P)
    (hfloor : 2 * ChartScales.Q Nr ≤ qbig)
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) (CutStageEstimates.physicalSublevel h qbig))
    (hD : ∀ k, ContDiffOn ℝ ∞ (D k) (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ k, ContDiffOn ℝ ∞ (P k) (CutStageEstimates.physicalSublevel h qbig))
    (J : ℕ)
    (Hrep : CycleRepresentation
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).coefficients
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0) J).state
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).axisymmetricAlias) :
    ActualCycleResidualBounds.PhysicalData B Nr
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0) J).state
      (MixedDiagonalResidual.uncutVelocity A D J) (DiagonalJetBounds.uncutPrefix P (J+1)) := by
  have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half
      qbig
  constructor
  · intro n hn z ht hz
    have hu := source_sublevel hfloor hn ht hz
    exact ((MixedDiagonalResidual.uncutVelocity_smooth hU hA hD J).contDiffAt
      (hU.mem_nhds hu)).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro n hn z ht hz
    have hu := source_sublevel hfloor hn ht hz
    have hp : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix P (J+1))
        (CutStageEstimates.physicalSublevel h qbig) := ContDiffOn.sum (fun k _ => hP k)
    exact (hp.contDiffAt (hU.mem_nhds hu)).differentiableAt (by simp)
  · intro n hn z ht hz
    exact H.velocity_germ hfloor hA J Hrep n hn ht hz
  · intro n hn z ht hz
    exact H.pressure_germ hfloor J Hrep n hn ht hz
  · intro w ht hq hout
    exact HE.prefix_exterior J ht hq hout


-- @@ L699-719 verbatim
/-- The actual residual-rate consumer can use this family without
reprovisioning any cylindrical germs or exterior prefix identities. -/
theorem physicalFields_all {B N0 Nr : ℕ}
    {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    {qbig : ℝ} {A D : ℕ → VelocityField} {P : ℕ → PressureField}
    (H : StageRealizations B N0 Nr p qbig A D P)
    (HE : ActualExteriorPrefix.ExteriorStages B Nr A D P)
    (hfloor : 2 * ChartScales.Q Nr ≤ qbig)
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) (CutStageEstimates.physicalSublevel h qbig))
    (hD : ∀ k, ContDiffOn ℝ ∞ (D k) (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ k, ContDiffOn ℝ ∞ (P k) (CutStageEstimates.physicalSublevel h qbig))
    (Hrep : ∀ J, CycleRepresentation
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).coefficients
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0) J).state
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          J).axisymmetricAlias) :
    ∀ J, ActualCycleResidualBounds.PhysicalData B Nr
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0) J).state
      (MixedDiagonalResidual.uncutVelocity A D J) (DiagonalJetBounds.uncutPrefix P (J+1)) :=
  fun J => physicalFields_of_stages H HE hfloor hA hD hP J (Hrep J)


-- @@ L721-721 verbatim
end NavierStokes.ActualPhysicalPrefixFields
