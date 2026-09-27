/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonBaseContext
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalSignedWave
public import LeanPool.NavierStokesAndEuler.NavierStokes.WaveEnvelopeTransport
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCopyBounds


-- @@ L14-20 verbatim
/-!
# Geometry of the actual prepared primary charts

The native variables are `(p,(u,v))`, with `p=(R,(Z,T))`.
The pulse coordinate is exactly `v/L`, and the common-cover chart uses
the chosen slot basis and the actual difference of covering indices.
-/


-- @@ L22-22 verbatim
section


-- @@ L24-30 verbatim
/-!
# Controls from the actual shared primary construction

The reference matrix, target, unit pulse, normal motion and action below
are computed from the same prepared primary family. Their native-copy
estimates have constants before all labels, bands and copies.
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace NavierStokes.ActualSignedControl


-- @@ L38-38 verbatim
open Set Function Filter PhaseJetBounds PrimaryPulseBounds PrimaryCopyBounds

-- @@ L39-39 verbatim
open WeightedClasses PeriodizedWaveBounds

-- @@ L40-40 verbatim
open scoped ContDiff Topology InnerProductSpace BigOperators


-- @@ L42-43 verbatim
/-- Mat2: an abbreviation for `SmoothCovariance.Mat2`. -/
abbrev Mat2 := SmoothCovariance.Mat2

-- @@ L44-45 verbatim
/-- Vec2: an abbreviation for `SmoothCovariance.Vec2`. -/
abbrev Vec2 := SmoothCovariance.Vec2

-- @@ L46-47 verbatim
/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space


-- @@ L49-52 verbatim
variable {ι Λ I D X E : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L54-58 verbatim
/-- Phase normal, defined pointwise by `F.phase.normal i (PrimaryCopyBounds.phasePoint F χ i
x)`. -/
noncomputable def phaseNormal {U : Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction U) (χ : ι → D → PhaseCalculus.Slow × ℝ) : ι → D → Space :=
  fun i x => F.phase.normal i (PrimaryCopyBounds.phasePoint F χ i x)


-- @@ L60-64 verbatim
/-- Phase motion, defined pointwise by `F.phase.velocity i (PrimaryCopyBounds.phasePoint F χ i
x)`. -/
noncomputable def phaseMotion {U : Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction U) (χ : ι → D → PhaseCalculus.Slow × ℝ) : ι → D → Space :=
  fun i x => F.phase.velocity i (PrimaryCopyBounds.phasePoint F χ i x)


-- @@ L66-72 verbatim
/-- Phase action, defined pointwise by `PrimaryCopyBridge.baseOperator (F.phase.F i (χ i x).1)
(F.phase.shear i (PrimaryCopyBounds.phasePoint F χ i x))`. -/
noncomputable def phaseAction {U : Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction U) (χ : ι → D → PhaseCalculus.Slow × ℝ) :
    ι → D → Space →L[ℝ] Space :=
  fun i x => PrimaryCopyBridge.baseOperator (F.phase.F i (χ i x).1)
    (F.phase.shear i (PrimaryCopyBounds.phasePoint F χ i x))


-- @@ L74-78 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem pulseMatrix_eq_phaseMatrix {U : Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PhaseConstruction U) (pref : Fin 2 → ℕ → ℝ)
    (χ : ℕ → D → PhaseCalculus.Slow × ℝ) :
    pulseMatrix F pref χ = SignedWaveUpdate.phaseMatrix F pref χ := rfl


-- @@ L80-83 verbatim
omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem pulseVector_eq_phaseFundamental {U : Domain ℕ PhaseCalculus.Slow}
    (F : Fin 2 → PhaseConstruction U) (χ : ℕ → D → PhaseCalculus.Slow × ℝ) (j : Fin 2) :
    pulseVector F χ j = SignedWaveUpdate.phaseFundamental F χ j := rfl


-- @@ L85-111 verbatim
/-- The three geometric jet estimates are obtained from the actual phase
construction, rather than being supplied for the pressure output. -/
theorem phase_geometry_jets {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}
    (F : PhaseConstruction U) (χ : ι → D → PhaseCalculus.Slow × ℝ)
    (hscale : ∀ i, U.scale i = V.scale i) (hχ : PolynomialJets V.toDomain χ)
    (hmap : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1) :
    PolynomialJets V.toDomain (phaseNormal F χ) ∧
    PolynomialJets V.toDomain (phaseMotion F χ) ∧
    PolynomialJets V.toDomain (phaseAction F χ) ∧
    (∀ i x, x ∈ V.carrier i → F.b ≤ ‖phaseNormal F χ i x‖) ∧
    (∀ i x, x ∈ V.carrier i → ‖phaseNormal F χ i x‖ ≤ F.M ^ 2 + 3 * F.M) := by
  have hp := PrimaryCopyBounds.phasePoint_jets F χ hscale hχ
  have hm := PrimaryCopyBounds.phasePoint_maps F χ hmap
  have hb := F.phase.polynomial_jets U F.V F.openV F.baseF F.baseG
    F.r_pos F.one_le_M F.constants F.epsilon_ne F.radius F.slot
  have hN := ((EnvelopeJets.of_polynomial hb.1).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hNd := ((EnvelopeJets.of_polynomial hb.2.1).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hshear := ((EnvelopeJets.of_polynomial hb.2.2).comp hp hscale hm).to_polynomial
    (fun _ _ _ => le_rfl)
  have hF := ((EnvelopeJets.of_polynomial F.baseF).comp
    (hχ.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) hscale
    (fun i x hx => (hmap i x hx).1)).to_polynomial (fun _ _ _ => le_rfl)
  exact ⟨hN, hNd, (hF.pair hshear).clm PrimaryCopyBridge.baseOperatorFamily,
    fun i x hx => F.normal_range.1 i _ (hm i x hx),
    fun i x hx => F.normal_range.2 i _ (hm i x hx)⟩


-- @@ L113-138 verbatim
/-- A proved reference certificate. The prepared-family constructor below
derives its target and mask estimates and all three scalar margins. -/
structure ReferenceBounds (V : JetDomain ι D) (U : Domain ι PhaseCalculus.Slow)
    (F : Fin 2 → PhaseConstruction U) (pref : Fin 2 → ι → ℝ)
    (χ : ι → D → PhaseCalculus.Slow × ℝ) (T : ι → D → Vec2)
    (mask ζ : ι → D → ℝ) where
  scale : ∀ i, U.scale i = V.scale i
  coordinate_jets : PolynomialJets V.toDomain χ
  coordinate_mem : ∀ i x, x ∈ V.carrier i → χ i x ∈ U.carrier i ×ˢ Ioo (0 : ℝ) 1
  prefactor_jets : ∀ j, PolynomialJets U (fun i _ => pref j i)
  target_jets : ∀ q, NativeJets V ζ (fun i x => T i x q)
  mask_jets : PolynomialJets V.toDomain mask
  weight_pos : ∀ i x, x ∈ V.carrier i → 0 < ζ i x
  /-- Determinant gap of `ReferenceBounds`, of type `ℝ`. -/
  determinantGap : ℝ
  /-- Entry bound of `ReferenceBounds`, of type `ℝ`. -/
  entryBound : ℝ
  /-- Primary lower of `ReferenceBounds`, of type `ℝ`. -/
  primaryLower : ℝ
  gap_pos : 0 < determinantGap
  entry_one : 1 ≤ entryBound
  lower_pos : 0 < primaryLower
  zero_order : ∀ i x, x ∈ V.carrier i →
    PrimaryCovarianceBounds.ZeroOrderBounds (Real.sqrt (V.scale i))
      determinantGap entryBound primaryLower (ζ i x)
      (pulseMatrix F pref χ i x) (T i x)


-- @@ L140-140 verbatim
namespace ReferenceBounds


-- @@ L142-145 verbatim
variable {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}
  {F : Fin 2 → PhaseConstruction U} {pref : Fin 2 → ι → ℝ}
  {χ : ι → D → PhaseCalculus.Slow × ℝ} {T : ι → D → Vec2} {mask ζ : ι → D → ℝ}
  (h : ReferenceBounds V U F pref χ T mask ζ)


-- @@ L147-147 verbatim
include h


-- @@ L149-152 verbatim
theorem matrix_jets (j k : Fin 2) :
    PolynomialJets V.toDomain (fun i x => pulseMatrix F pref χ i x j k) :=
  pulseMatrix_jets F pref χ h.scale h.coordinate_jets
    (fun i x hx => (h.coordinate_mem i x hx).1) h.prefactor_jets j k


-- @@ L154-155 verbatim
theorem unit_jets (j : Fin 2) : NativeJets V (pulseEnvelope F χ j) (pulseVector F χ j) :=
  pulseVector_jets F χ h.scale h.coordinate_jets h.coordinate_mem j


-- @@ L157-163 verbatim
theorem geometry_jets (j : Fin 2) :
    PolynomialJets V.toDomain (phaseNormal (F j) χ) ∧
    PolynomialJets V.toDomain (phaseMotion (F j) χ) ∧
    PolynomialJets V.toDomain (phaseAction (F j) χ) ∧
    (∀ i x, x ∈ V.carrier i → (F j).b ≤ ‖phaseNormal (F j) χ i x‖) ∧
    (∀ i x, x ∈ V.carrier i → ‖phaseNormal (F j) χ i x‖ ≤ (F j).M ^ 2 + 3 * (F j).M) :=
  phase_geometry_jets (F j) χ h.scale h.coordinate_jets h.coordinate_mem


-- @@ L165-170 verbatim
theorem cutoff_jets : PolynomialJets V.toDomain
    (fun i x => GaussianTailFlat.profile (χ i x).2) := by
  apply (h.coordinate_jets.clm (ContinuousLinearMap.snd ℝ PhaseCalculus.Slow ℝ)).compact_comp
    isOpen_univ GaussianTailFlat.profile_contDiff.contDiffOn isCompact_Icc (subset_univ _)
  · intro i x hx
    exact ⟨(h.coordinate_mem i x hx).2.1.le, (h.coordinate_mem i x hx).2.2.le⟩


-- @@ L172-172 verbatim
end ReferenceBounds


-- @@ L174-209 verbatim
/-- Only affine coordinate geometry and weight/scale comparisons are
stored here. No copied field or copied derivative bound is an input. -/
structure CopyChart (s : StripData X) (V : JetDomain ι D) (ζ : ι → D → ℝ)
    (K : Λ → ℕ → I → Set X) where
  /-- Index of `CopyChart`, of type `Λ → ℕ → ι`. -/
  index : Λ → ℕ → ι
  /-- Linear of `CopyChart`, of type `Λ → ℕ → I → X →L[ℝ] D`. -/
  linear : Λ → ℕ → I → X →L[ℝ] D
  /-- Shift of `CopyChart`, of type `Λ → ℕ → I → D`. -/
  shift : Λ → ℕ → I → D
  maps : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
    linear l n i x + shift l n i ∈ V.carrier (index l n)
  /-- Growth constant of `CopyChart`, of type `ℝ`. -/
  growthConstant : ℝ
  /-- Linear constant of `CopyChart`, of type `ℝ`. -/
  linearConstant : ℝ
  growth_one : 1 ≤ growthConstant
  linear_one : 1 ≤ linearConstant
  /-- Growth degree of `CopyChart`, of type `ℕ`. -/
  growthDegree : ℕ
  /-- Linear degree of `CopyChart`, of type `ℕ`. -/
  linearDegree : ℕ
  growth_bound : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
    V.growth (index l n) (linear l n i x + shift l n i) ≤
      growthConstant * s.growth n x ^ growthDegree
  linear_bound : ∀ l n i, ‖linear l n i‖ ≤ linearConstant * s.slow n ^ linearDegree
  weight_eq : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
    ζ (index l n) (linear l n i x + shift l n i) = s.zeta x
  /-- Ratio lower of `CopyChart`, of type `ℝ`. -/
  ratioLower : ℝ
  /-- Ratio upper of `CopyChart`, of type `ℝ`. -/
  ratioUpper : ℝ
  ratio_pos : 0 < ratioLower
  ratio_one : 1 ≤ ratioUpper
  scale_ratio : ∀ l n, ratioLower ≤ Real.sqrt (s.slow n) / Real.sqrt (V.scale (index l n)) ∧
    Real.sqrt (s.slow n) / Real.sqrt (V.scale (index l n)) ≤ ratioUpper


-- @@ L211-211 verbatim
namespace CopyChart


-- @@ L213-214 verbatim
variable {s : StripData X} {V : JetDomain ι D} {ζ : ι → D → ℝ}
  {K : Λ → ℕ → I → Set X} (c : CopyChart s V ζ K)


-- @@ L216-218 verbatim
/-- Pull, given by `affineCopy f c.index c.linear c.shift`. -/
noncomputable def pull (f : ι → D → E) : Λ → ℕ → I → X → E :=
  affineCopy f c.index c.linear c.shift


-- @@ L220-226 verbatim
theorem unweighted {f : ι → D → E} (hf : PolynomialJets V.toDomain f) :
    UniformLocalJets s (fun _ _ _ => 1) 0 K (c.pull f) := by
  apply (NativeJets.of_polynomial hf).copy_localJets s (fun _ _ _ => 1) 0
    c.index c.linear c.shift K (fun _ _ _ _ => zero_le_one) c.maps c.growth_one c.linear_one
    c.growthDegree c.linearDegree c.growth_bound c.linear_bound
  intro l n i x hx hi
  simp


-- @@ L228-234 verbatim
theorem weighted {f : ι → D → E} (hf : NativeJets V ζ f) :
    UniformLocalJets s (fun _ _ x => s.zeta x) 0 K (c.pull f) := by
  apply hf.copy_localJets s (fun _ _ x => s.zeta x) 0 c.index c.linear c.shift K
    (fun _ _ x hx => s.zeta_nonneg x hx) c.maps c.growth_one c.linear_one
    c.growthDegree c.linearDegree c.growth_bound c.linear_bound
  intro l n i x hx hi
  simp only [Real.rpow_zero, one_mul, c.weight_eq l n i x hx hi, le_refl]


-- @@ L236-243 verbatim
theorem envelope {w : ι → D → ℝ} {f : ι → D → E} (hf : NativeJets V w f)
    {W : Λ → ℕ → X → ℝ} (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hw : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      w (c.index l n) (c.linear l n i x + c.shift l n i) ≤ W l n x) :
    UniformLocalJets s W 0 K (c.pull f) := by
  apply hf.copy_localJets s W 0 c.index c.linear c.shift K hW c.maps c.growth_one c.linear_one
    c.growthDegree c.linearDegree c.growth_bound c.linear_bound
  simpa only [Real.rpow_zero, one_mul] using hw


-- @@ L245-245 verbatim
end CopyChart


-- @@ L247-247 verbatim
/-! ## The reference certificate is produced from the same actual profile -/


-- @@ L249-249 verbatim
section Prepared


-- @@ L251-254 verbatim
variable {F₀ : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F₀}
  (H₀ : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v₀ : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}


-- @@ L256-291 verbatim
/-- Primitive local chart geometry for a selected prepared family.
The target, matrix, mask and pulse jets are not fields of this record. -/
structure PreparedChart (a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0)
    (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D] where
  /-- Native of `PreparedChart`, of type `JetDomain (PrimaryGeometryAssembly.Index W₀ a.N) D`. -/
  native : JetDomain (PrimaryGeometryAssembly.Index W₀ a.N) D
  /-- Slow of `PreparedChart`, of type `JetDomain (PrimaryGeometryAssembly.Index W₀ a.N)
  PhaseCalculus.Slow`. -/
  slow : JetDomain (PrimaryGeometryAssembly.Index W₀ a.N) PhaseCalculus.Slow
  /-- Coordinate of `PreparedChart`, of type `PrimaryGeometryAssembly.Index W₀ a.N → D →
  PhaseCalculus.Slow × ℝ`. -/
  coordinate : PrimaryGeometryAssembly.Index W₀ a.N → D → PhaseCalculus.Slow × ℝ
  scale : ∀ L, (PrimaryGeometryAssembly.domain W₀ a.N).scale L = native.scale L
  coordinate_jets : PolynomialJets native.toDomain coordinate
  maps : ∀ L x, x ∈ native.carrier L →
    coordinate L x ∈ (PrimaryGeometryAssembly.domain W₀ a.N).carrier L ×ˢ Ioo (0 : ℝ) 1
  positive : ∀ L x, x ∈ native.carrier L → (coordinate L x).1 ∈
    PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W₀)
  slow_maps : ∀ L x, x ∈ native.carrier L → (coordinate L x).1 ∈ slow.carrier L
  slow_growth : ∀ L x, x ∈ native.carrier L → slow.growth L (coordinate L x).1 ≤ native.growth L x
  /-- Radius lower of `PreparedChart`, of type `ℝ`. -/
  radiusLower : ℝ
  /-- Norm upper of `PreparedChart`, of type `ℝ`. -/
  normUpper : ℝ
  /-- Q lower of `PreparedChart`, of type `ℝ`. -/
  qLower : ℝ
  /-- Q upper of `PreparedChart`, of type `ℝ`. -/
  qUpper : ℝ
  radius_pos : 0 < radiusLower
  q_pos : 0 < qLower
  geometry : BaseChartJets.GeometryBounds slow.toDomain F₀.data.h radiusLower normUpper qLower
      qUpper
    (NominalConeAssembly.activeLeft W₀) (NominalConeAssembly.activeRight W₀)
  inverse_edge : ∀ L p, p ∈ slow.carrier L →
    (FinalSlowBase.edgeDistance W₀ (BaseChartJets.normalizedCoordinates F₀.data.h p).2)⁻¹ ≤
        slow.growth L p


-- @@ L293-293 verbatim
namespace PreparedChart


-- @@ L295-297 verbatim
variable {H₀ v₀}
  {a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0}
  (c : PreparedChart H₀ v₀ a D)


-- @@ L299-301 verbatim
/-- Target, defined pointwise by `PrimaryTargetBounds.actualTarget v₀ (c.coordinate L x).1 k`. -/
noncomputable def target : PrimaryGeometryAssembly.Index W₀ a.N → D → Vec2 :=
  fun L x k => PrimaryTargetBounds.actualTarget v₀ (c.coordinate L x).1 k


-- @@ L303-305 verbatim
/-- Weight, defined pointwise by `PrimaryTargetBounds.movingWeight W₀ (c.coordinate L x).1`. -/
noncomputable def weight : PrimaryGeometryAssembly.Index W₀ a.N → D → ℝ :=
  fun L x => PrimaryTargetBounds.movingWeight W₀ (c.coordinate L x).1


-- @@ L307-310 verbatim
/-- Mask as an element of `PrimaryGeometryAssembly.Index W₀ a.N → D → ℝ`. -/
noncomputable def mask : PrimaryGeometryAssembly.Index W₀ a.N → D → ℝ :=
  fun L x => PrimaryRepresentatives.nativeMask (PrimaryGeometryAssembly.label W₀ L).1
    (PrimaryGeometryAssembly.label W₀ L).2 (c.coordinate L x).1


-- @@ L312-318 verbatim
theorem target_jets (hcone : LeadingStressWeights.FullTrueCone v₀) (k : Fin 2) :
    NativeJets c.native c.weight (fun L x => c.target L x k) := by
  have ht := (PrimaryCopyBounds.actualTarget_jets v₀ hcone c.slow
    c.radius_pos c.q_pos c.geometry c.inverse_edge).comp
    (c.coordinate_jets.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ)) c.slow_maps
        c.slow_growth
  exact ht.map (PiLp.proj 2 (fun _ : Fin 2 => ℝ) k)


-- @@ L320-329 verbatim
theorem mask_jets : PolynomialJets c.native.toDomain c.mask := by
  apply nativeMask_comp_jets c.native.toDomain
    (fun L x => (c.coordinate L x).1)
    (c.coordinate_jets.clm (ContinuousLinearMap.fst ℝ PhaseCalculus.Slow ℝ))
    (fun L => (PrimaryGeometryAssembly.label W₀ L).1)
    (fun L => (PrimaryGeometryAssembly.label W₀ L).2)
    (fun L => L.val.property.1)
  intro L
  rw [← c.scale L]
  rfl


-- @@ L331-340 verbatim
theorem weight_pos (L : PrimaryGeometryAssembly.Index W₀ a.N) {x : D}
    (hx : x ∈ c.native.carrier L) : 0 < c.weight L x := by
  have hs := c.slow_maps L x hx
  rw [weight, PrimaryTargetBounds.movingWeight_eq W₀ (c.geometry.time L _ hs)
    (c.radius_pos.trans_le (c.geometry.radius L _ hs))]
  apply ActiveAnnulusWeight.radialWeight_pos
  simp only [FinalSlowBase.logLeft, FinalSlowBase.logRight,
    Real.exp_log (NominalConeAssembly.activeLeft_pos W₀),
    Real.exp_log (FinalSlowBase.terminal_pos W₀)]
  exact c.geometry.x_range L _ hs


-- @@ L342-375 verbatim
/-- Every jet field in this reference certificate is derived from the
actual prepared phase, actual leading target and actual grid mask. -/
noncomputable def referenceBounds (hcone : LeadingStressWeights.FullTrueCone v₀)
    (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)
    (dg eb il : ℝ) (hdg : 0 < dg) (heb : 1 ≤ eb) (hil : 0 < il)
    (hz : ∀ (L : PrimaryGeometryAssembly.Index W₀ a.N) (p : PhaseCalculus.Slow),
      p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W₀) →
      p ∈ (PrimaryGeometryAssembly.domain W₀ a.N).carrier L →
      PrimaryCovarianceBounds.ZeroOrderBounds (Real.sqrt (ChartScales.S (BaseChartJets.cellBand L)))
        dg eb il (PrimaryTargetBounds.movingWeight W₀ p)
        (PrimaryTargetBounds.preparedCovariance H₀ v₀ a vr vt L p)
        (fun k => PrimaryTargetBounds.actualTarget v₀ p k)) :
    ReferenceBounds c.native (PrimaryGeometryAssembly.domain W₀ a.N)
      (PrimaryGeometryAssembly.construction H₀ v₀ a hr0)
      (preparedPrefactor r0 vr vt) c.coordinate c.target c.mask c.weight where
  scale := c.scale
  coordinate_jets := c.coordinate_jets
  coordinate_mem := c.maps
  prefactor_jets := fun j => preparedPrefactor_jets r0 vr vt a.N j
  target_jets := c.target_jets hcone
  mask_jets := c.mask_jets
  weight_pos := fun L _ hx => c.weight_pos L hx
  determinantGap := dg
  entryBound := eb
  primaryLower := il
  gap_pos := hdg
  entry_one := heb
  lower_pos := hil
  zero_order := by
    intro L x hx
    have h := hz L (c.coordinate L x).1 (c.positive L x hx) (c.maps L x hx).1
    have hscale : c.native.scale L = ChartScales.S (BaseChartJets.cellBand L) := (c.scale L).symm
    simp only [hscale, pulseMatrix, weight] at h ⊢
    exact h


-- @@ L377-377 verbatim
end PreparedChart


-- @@ L379-392 verbatim
/-- A supplied prepared family is only restricted to a later tail.
Every surviving phase and representative is the same one used by the
primary construction. No determinant or final control record is assumed. -/
theorem exists_referenceBounds (a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0)
    (hcone : LeadingStressWeights.FullTrueCone v₀) (hr0 : 0 < r0)
    (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    ∃ N : ℕ, ∃ hN : a.N ≤ N,
      ∀ c : PreparedChart H₀ v₀ (a.restrict N hN) D,
        Nonempty (ReferenceBounds c.native (PrimaryGeometryAssembly.domain W₀ N)
          (PrimaryGeometryAssembly.construction H₀ v₀ (a.restrict N hN) hr0)
          (preparedPrefactor r0 vr vt) c.coordinate c.target c.mask c.weight) := by
  obtain ⟨N, hN, dg, eb, il, hdg, heb, hil, hz⟩ :=
    PrimaryTargetBounds.exists_restricted_actual_bounds H₀ v₀ a hcone vr vt hdet hr0
  exact ⟨N, hN, fun c => ⟨c.referenceBounds hcone hr0 vr vt dg eb il hdg heb hil hz⟩⟩


-- @@ L394-394 verbatim
end Prepared


-- @@ L396-396 verbatim
/-! ## Transport through the actual affine views -/


-- @@ L398-408 verbatim
/-- Positive band scalars with uniform primitive zeroth-order margins. -/
structure PositiveScale (Λ : Type) where
  /-- Value of `PositiveScale`, of type `Λ → ℕ → ℝ`. -/
  value : Λ → ℕ → ℝ
  /-- Lower of `PositiveScale`, of type `ℝ`. -/
  lower : ℝ
  /-- Upper of `PositiveScale`, of type `ℝ`. -/
  upper : ℝ
  lower_pos : 0 < lower
  upper_one : 1 ≤ upper
  bounds : ∀ l n, lower ≤ value l n ∧ value l n ≤ upper


-- @@ L410-410 verbatim
namespace PositiveScale


-- @@ L412-412 verbatim
variable (a b : PositiveScale Λ)


-- @@ L414-414 verbatim
theorem value_pos (l : Λ) (n : ℕ) : 0 < a.value l n := a.lower_pos.trans_le (a.bounds l n).1


-- @@ L416-420 verbatim
theorem bandBound (s : StripData X) : UniformPrimaryWeights.UniformBandBound s 0 a.value := by
  refine ⟨a.upper, zero_le_one.trans a.upper_one, 0, ?_⟩
  intro l n
  simpa only [Real.norm_eq_abs, abs_of_pos (a.value_pos l n), Real.rpow_zero,
    pow_zero, mul_one] using (a.bounds l n).2


-- @@ L422-427 verbatim
theorem square_bandBound (s : StripData X) :
    UniformPrimaryWeights.UniformBandBound s 0 (fun l n => a.value l n ^ 2) := by
  refine ⟨a.upper ^ 2, sq_nonneg _, 0, ?_⟩
  intro l n
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a.value l n)), Real.rpow_zero,
    pow_zero, mul_one] using pow_le_pow_left₀ (a.value_pos l n).le (a.bounds l n).2 2


-- @@ L429-438 verbatim
/-- Mul, bundling `value`, `lower`, `upper`, `lower_pos` and the required compatibility proofs. -/
noncomputable def mul : PositiveScale Λ where
  value l n := a.value l n * b.value l n
  lower := a.lower * b.lower
  upper := a.upper * b.upper
  lower_pos := mul_pos a.lower_pos b.lower_pos
  upper_one := one_le_mul_of_one_le_of_one_le a.upper_one b.upper_one
  bounds l n := ⟨mul_le_mul (a.bounds l n).1 (b.bounds l n).1 b.lower_pos.le (a.value_pos l n).le,
    mul_le_mul (a.bounds l n).2 (b.bounds l n).2 (b.value_pos l n).le (zero_le_one.trans
        a.upper_one)⟩


-- @@ L440-440 verbatim
end PositiveScale


-- @@ L442-455 verbatim
theorem uniform_band_smul [Countable Λ] [Nonempty Λ]
    {s : StripData X} {K : Λ → ℕ → I → Set X} {w : Λ → ℕ → X → ℝ} {α β : ℝ}
    {f : Λ → ℕ → I → X → E} {r : Λ → ℕ → ℝ}
    (hf : UniformLocalJets s w α K f) (hr : UniformPrimaryWeights.UniformBandBound s β r)
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x) :
    UniformLocalJets s w (α + β) K (fun l n i x => r l n • f l n i x) := by
  let e := UniformPrimaryWeights.enumeration Λ
  apply SignedCopyBounds.uniform_local_of_pull (UniformPrimaryWeights.enumeration_surjective Λ)
  have hr' : UniformPrimaryWeights.UniformBandBound (UniformPrimaryWeights.reindexedStrip s e) β
      (fun (_ : I) k => r (e k).2 (e k).1) := by
    obtain ⟨C, hC, p, hb⟩ := hr
    exact ⟨C, hC, p, fun _ k => hb (e k).2 (e k).1⟩
  exact SignedCopyBounds.local_indexed_band_smul (SignedCopyBounds.local_pull hf e) hr'
    (fun k => hw (e k).2 (e k).1)


-- @@ L457-469 verbatim
theorem uniform_local_congr {s : StripData X} {K : Λ → ℕ → I → Set X}
    {w : Λ → ℕ → X → ℝ} {α : ℝ} {f g : Λ → ℕ → I → X → E}
    (hf : UniformLocalJets s w α K f)
    (he : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → f l n i =ᶠ[𝓝 x] g l n i) :
    UniformLocalJets s w α K g := by
  refine ⟨fun l n i x hx hi => (hf.smooth l n i x hx hi).congr_of_eventuallyEq
    (he l n i x hx hi).symm, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro l n i x hx hi j hj
  rw [← PeriodizedWaveBounds.jets_eq_of_germ (he l n i x hx hi) j]
  exact hb l n i x hx hi j hj


-- @@ L471-503 verbatim
/-- Changing the band's normalization and scaling the actual target
preserves quantitative Cramer margins with explicit constants. -/
theorem rescale_margins {r R dg eb il ζ c clo rlo rhi : ℝ} {H : Mat2} {T : Vec2}
    (h : PrimaryCovarianceBounds.ZeroOrderBounds r dg eb il ζ H T)
    (hr : 1 ≤ r) (hdg : 0 ≤ dg) (hil : 0 ≤ il) (hζ : 0 ≤ ζ) (hclo : 0 < clo) (hc : clo ≤ c)
    (hrlo : 0 < rlo) (hlo : rlo ≤ R / r) (hhi : R / r ≤ rhi) :
    rlo ^ 2 * dg ≤ |(normalizedMatrix R H).det| ∧
    (∀ i j, |R * H i j| ≤ rhi * eb) ∧
    (∀ j, (clo ^ 2 * il) * ζ ≤ SmoothCovariance.weights H (c ^ 2 • T) j) := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hratio : 0 < R / r := hrlo.trans_le hlo
  have he : normalizedMatrix R H = normalizedMatrix (R / r) (normalizedMatrix r H) := by
    ext i j
    simp only [normalizedMatrix]
    field_simp
  have hdet : |(normalizedMatrix R H).det| = (R / r) ^ 2 * |(normalizedMatrix r H).det| := by
    rw [he, normalizedMatrix_det, abs_mul, abs_of_nonneg (sq_nonneg _)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdet]
    exact mul_le_mul (pow_le_pow_left₀ hrlo.le hlo 2) h.determinant
      hdg (sq_nonneg _)
  · intro i j
    have hentry : R * H i j = (R / r) * (r * H i j) := by field_simp
    rw [hentry, abs_mul, abs_of_pos hratio]
    exact mul_le_mul hhi (h.entries i j) (abs_nonneg _) (by linarith [hratio, hhi])
  · intro j
    rw [PhysicalSignedWave.weights_smul_target, Pi.smul_apply, smul_eq_mul]
    have hbase : il * ζ ≤ SmoothCovariance.weights H T j := by
      apply le_trans _ (h.weights j)
      nlinarith [mul_nonneg hil hζ]
    have hh := mul_le_mul (pow_le_pow_left₀ hclo.le hc 2) hbase
      (mul_nonneg hil hζ) (sq_nonneg c)
    simpa only [mul_assoc] using hh


-- @@ L505-505 verbatim
namespace ReferenceBounds


-- @@ L507-513 verbatim
variable [Countable Λ] [Nonempty Λ]
  {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}
  {F : Fin 2 → PhaseConstruction U} {pref : Fin 2 → ι → ℝ}
  {χ : ι → D → PhaseCalculus.Slow × ℝ} {T : ι → D → Vec2} {mask ζ : ι → D → ℝ}
  (h : ReferenceBounds V U F pref χ T mask ζ)
  {s : StripData X} {K : Λ → ℕ → I → Set X}
  (c : CopyChart s V ζ K) (scale : PositiveScale Λ)


-- @@ L515-554 verbatim
/-- Construct the actual uniform native covariance record from the
derived reference jets and the primitive view geometry. -/
noncomputable def nativeCovariance (hzeta : ∀ x ∈ s.domain, 0 < s.zeta x) :
    SignedCopyBounds.UniformNativeCovariance s K
      (fun l i n => c.pull (pulseMatrix F pref χ) l n i)
      (fun l i n x => scale.value l n ^ 2 • c.pull T l n i x) where
  matrix_jets j k := c.unweighted (h.matrix_jets j k)
  target_jets q := by
    have ht := uniform_band_smul (c.weighted (h.target_jets q)) (scale.square_bandBound s)
      (fun _ _ x hx => s.zeta_nonneg x hx)
    simp only [zero_add] at ht
    exact ht
  zeta_pos := hzeta
  determinantGap := c.ratioLower ^ 2 * h.determinantGap
  entryBound := c.ratioUpper * h.entryBound
  primaryLower := scale.lower ^ 2 * h.primaryLower
  gap_pos := mul_pos (sq_pos_of_pos c.ratio_pos) h.gap_pos
  entry_one := one_le_mul_of_one_le_of_one_le c.ratio_one h.entry_one
  lower_pos := mul_pos (sq_pos_of_pos scale.lower_pos) h.lower_pos
  determinant := by
    intro l n i x hx hi
    have hz := h.zero_order (c.index l n) _ (c.maps l n i x hx hi)
    rw [c.weight_eq l n i x hx hi] at hz
    exact (rescale_margins hz (Real.one_le_sqrt.mpr (V.one_le_scale _)) h.gap_pos.le h.lower_pos.le
      (s.zeta_nonneg x hx) scale.lower_pos (scale.bounds l n).1 c.ratio_pos
      (c.scale_ratio l n).1 (c.scale_ratio l n).2).1
  entries := by
    intro l n i x hx hi
    have hz := h.zero_order (c.index l n) _ (c.maps l n i x hx hi)
    rw [c.weight_eq l n i x hx hi] at hz
    exact (rescale_margins hz (Real.one_le_sqrt.mpr (V.one_le_scale _)) h.gap_pos.le h.lower_pos.le
      (s.zeta_nonneg x hx) scale.lower_pos (scale.bounds l n).1 c.ratio_pos
      (c.scale_ratio l n).1 (c.scale_ratio l n).2).2.1
  lower := by
    intro l n i x hx hi
    have hz := h.zero_order (c.index l n) _ (c.maps l n i x hx hi)
    rw [c.weight_eq l n i x hx hi] at hz
    exact (rescale_margins hz (Real.one_le_sqrt.mpr (V.one_le_scale _)) h.gap_pos.le h.lower_pos.le
      (s.zeta_nonneg x hx) scale.lower_pos (scale.bounds l n).1 c.ratio_pos
      (c.scale_ratio l n).1 (c.scale_ratio l n).2).2.2


-- @@ L556-575 verbatim
/-- The requested copy-level `NativeCovariance` is a projection of the
jointly proved record, retaining the same numerical margins. -/
noncomputable def nativeCovarianceAt (hzeta : ∀ x ∈ s.domain, 0 < s.zeta x) (l : Λ) :
    SignedCopyBounds.NativeCovariance s (K l)
      (fun i n => c.pull (pulseMatrix F pref χ) l n i)
      (fun i n x => scale.value l n ^ 2 • c.pull T l n i x) := by
  let hc := h.nativeCovariance c scale hzeta
  exact {
    matrix_jets := fun j k => (hc.matrix_jets j k).each l
    target_jets := fun j => (hc.target_jets j).each l
    zeta_pos := hc.zeta_pos
    determinantGap := hc.determinantGap
    entryBound := hc.entryBound
    primaryLower := hc.primaryLower
    gap_pos := hc.gap_pos
    entry_one := hc.entry_one
    lower_pos := hc.lower_pos
    determinant := hc.determinant l
    entries := hc.entries l
    lower := hc.lower l }


-- @@ L577-577 verbatim
include h


-- @@ L579-585 verbatim
omit [Countable Λ] [Nonempty Λ] in
theorem copied_unit_jets (j : Fin 2) {W : Λ → ℕ → X → ℝ}
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (henv : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      c.pull (pulseEnvelope F χ j) l n i x ≤ W l n x) :
    UniformLocalJets s W 0 K (c.pull (pulseVector F χ j)) :=
  c.envelope (h.unit_jets j) hW henv


-- @@ L587-604 verbatim
/-- The modeled normal, normal motion and action are the transported
ones from the selected primary phase, with its actual clock factors. -/
theorem copied_geometry_jets (normal clock : PositiveScale Λ) (j : Fin 2) :
    UniformLocalJets s (fun _ _ _ => 1) 0 K
      (fun l n i x => normal.value l n • c.pull (phaseNormal (F j) χ) l n i x) ∧
    UniformLocalJets s (fun _ _ _ => 1) 0 K
      (fun l n i x => (normal.value l n * clock.value l n) • c.pull (phaseMotion (F j) χ) l n i x) ∧
    UniformLocalJets s (fun _ _ _ => 1) 0 K
      (fun l n i x => clock.value l n • c.pull (phaseAction (F j) χ) l n i x) := by
  have hg := h.geometry_jets j
  refine ⟨?_, ?_, ?_⟩
  · simpa only [zero_add] using uniform_band_smul (c.unweighted hg.1) (normal.bandBound s)
      (fun _ _ _ _ => zero_le_one)
  · simpa only [zero_add, PositiveScale.mul] using
      uniform_band_smul (c.unweighted hg.2.1) ((normal.mul clock).bandBound s)
        (fun _ _ _ _ => zero_le_one)
  · simpa only [zero_add] using uniform_band_smul (c.unweighted hg.2.2.1) (clock.bandBound s)
      (fun _ _ _ _ => zero_le_one)


-- @@ L606-617 verbatim
omit [Countable Λ] [Nonempty Λ] in
theorem copied_normal_bounds (normal : PositiveScale Λ) (j : Fin 2)
    (l : Λ) (n : ℕ) (i : I) {x : X} (hx : x ∈ s.domain) (hi : x ∈ K l n i) :
    normal.lower * (F j).b ≤ ‖normal.value l n • c.pull (phaseNormal (F j) χ) l n i x‖ ∧
    ‖normal.value l n • c.pull (phaseNormal (F j) χ) l n i x‖ ≤
      normal.upper * ((F j).M ^ 2 + 3 * (F j).M) := by
  have hg := h.geometry_jets j
  have hlo := hg.2.2.2.1 (c.index l n) _ (c.maps l n i x hx hi)
  have hhi := hg.2.2.2.2 (c.index l n) _ (c.maps l n i x hx hi)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (normal.value_pos l n)]
  exact ⟨mul_le_mul (normal.bounds l n).1 hlo (F j).b_pos.le (normal.value_pos l n).le,
    mul_le_mul (normal.bounds l n).2 hhi (norm_nonneg _) (zero_le_one.trans normal.upper_one)⟩


-- @@ L619-619 verbatim
end ReferenceBounds


-- @@ L621-631 verbatim
/-- The carrier bound is derived for any nonzero integral harmonic, with
one constant before both the label and the copy. -/
theorem harmonic_frequency_bound (s : StripData X)
    (base : Λ → I → LinearWaveBounds.WaveCoefficients X)
    (harmonic : Λ → ℕ → ℤ) (hn : ∀ l n, harmonic l n ≠ 0)
    (hf : ∀ l i n, (base l i).frequency n = CurlClassBounds.carrierFrequency s n * (harmonic l n :
        ℝ)) :
    UniformPrimaryWeights.UniformBandBound s (1 / 2)
      (fun li : Λ × I => fun n => 1 / (base li.1 li.2).frequency n) := by
  obtain ⟨C, hC, p, hb⟩ := UniformPrimaryWeights.harmonic_inverse_bandBound s harmonic hn
  exact ⟨C, hC, p, fun li n => by dsimp only; rw [hf]; exact hb li.1 n⟩


-- @@ L633-633 verbatim
namespace ReferenceBounds


-- @@ L635-641 verbatim
variable [Countable Λ] [Nonempty Λ]
  {V : JetDomain ι D} {U : Domain ι PhaseCalculus.Slow}
  {F : Fin 2 → PhaseConstruction U} {pref : Fin 2 → ι → ℝ}
  {χ : ι → D → PhaseCalculus.Slow × ℝ} {T : ι → D → Vec2} {mask ζ : ι → D → ℝ}
  (h : ReferenceBounds V U F pref χ T mask ζ)
  {s : StripData X} {K : Λ → ℕ → I → Set X}
  (c : CopyChart s V ζ K) (scale normal clock : PositiveScale Λ)


-- @@ L643-655 verbatim
/-- Exact functional form of the transported shared-reference signed
constructor, including the target square and the pressure clock factors. -/
noncomputable def copiedCoefficients
    (base : Λ → I → LinearWaveBounds.WaveCoefficients X)
    (dirs : Λ → I → LinearWaveBounds.GraphDirections X)
    (request : ℕ → X → Vec2) (j : Fin 2) (l : Λ) (i : I) :
    LinearWaveBounds.WaveCoefficients X :=
  SignedWaveUpdate.coefficients (base l i) s (dirs l i)
    (fun n => c.pull (pulseMatrix F pref χ) l n i)
    (fun n x => scale.value l n ^ 2 • c.pull T l n i x) request
    (fun n => c.pull mask l n i) (fun n => c.pull (pulseVector F χ j) l n i)
    (fun n x => (normal.value l n * clock.value l n) • c.pull (phaseMotion (F j) χ) l n i x)
    (fun n x => clock.value l n • c.pull (phaseAction (F j) χ) l n i x) j


-- @@ L657-657 verbatim
include h


-- @@ L659-693 verbatim
/-- The native signed estimates are obtained from the constructed
reference, without accepting a completed native covariance record. -/
theorem copied_coefficients_jets
    (base : Λ → I → LinearWaveBounds.WaveCoefficients X)
    (dirs : Λ → I → LinearWaveBounds.GraphDirections X)
    (request : ℕ → X → Vec2) {β : ℝ} {W : Λ → ℕ → X → ℝ}
    (hzeta : ∀ x ∈ s.domain, 0 < s.zeta x)
    (hR : ∀ q, UniformLocalJets s (fun _ _ x => s.zeta x) β K (fun _ n _ x => request n x q))
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (j : Fin 2)
    (henv : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      c.pull (pulseEnvelope F χ j) l n i x ≤ W l n x)
    (hnormal : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
      (fun y => normal.value l n • c.pull (phaseNormal (F j) χ) l n i y) =ᶠ[𝓝 x]
        (base l i).normal s (dirs l i) n)
    (hfrequency : UniformPrimaryWeights.UniformBandBound s (1 / 2)
      (fun li : Λ × I => fun n => 1 / (base li.1 li.2).frequency n)) :
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (β + 1 / 2) K
      (fun l n i => (copiedCoefficients (F := F) (pref := pref) (χ := χ) (T := T) (mask := mask)
        c scale normal clock base dirs request j l i).amplitude n) ∧
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (β + 1) K
      (fun l n i => (copiedCoefficients (F := F) (pref := pref) (χ := χ) (T := T) (mask := mask)
        c scale normal clock base dirs request j l i).pressure n) := by
  have hg := h.copied_geometry_jets c normal clock j
  have hN := uniform_local_congr hg.1 hnormal
  apply SignedCopyBounds.uniform_coefficients_jets (M := normal.upper * ((F j).M ^ 2 + 3 * (F j).M))
    (h.nativeCovariance c scale hzeta) hR
    (c.unweighted h.mask_jets) (h.copied_unit_jets c j hW henv) hW hN hg.2.1 hg.2.2
    (mul_pos normal.lower_pos (F j).b_pos) _ _ hfrequency j
  · intro l n i x hx hi
    rw [← Filter.EventuallyEq.eq_of_nhds (hnormal l n i x hx hi)]
    exact (h.copied_normal_bounds c normal j l n i hx hi).1
  · intro l n i x hx hi
    rw [← Filter.EventuallyEq.eq_of_nhds (hnormal l n i x hx hi)]
    exact (h.copied_normal_bounds c normal j l n i hx hi).2


-- @@ L695-695 verbatim
end ReferenceBounds


-- @@ L697-697 verbatim
/-! ## The signed request is the measured current-state request -/


-- @@ L699-705 verbatim
theorem uniformLocalJets_of_memClass {s : StripData X} {w : ℕ → X → ℝ} {α : ℝ}
    {f : ℕ → X → E} (hf : MemClass s w α f) (K : Λ → ℕ → I → Set X) :
    UniformLocalJets s (fun _ => w) α K (fun _ n _ => f n) := by
  refine ⟨fun _ n _ x hx _ => (hf.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun _ n _ x hx _ j hj => hb n x hx j hj⟩


-- @@ L707-716 verbatim
theorem fullRequest_localJets (s : StripData LocalSignedRequest.Point)
    (P : SignedStressPrimitive.Patch) (coord : ℝ)
    (ctx : CorrectionState.Context LocalSignedRequest.Point)
    (u : CorrectionState.State LocalSignedRequest.Point) {β : ℝ}
    (h : ∀ q, MeanClass s β (fun n x => LocalSignedRequest.normalizedRequest s P coord ctx u n x q))
    (K : Λ → ℕ → I → Set (LocalSignedRequest.Point × ℝ)) :
    ∀ q, UniformLocalJets (HarmonicWaveInteraction.productStrip s)
      (fun _ _ x => s.zeta x.1) β K
      (fun _ n _ x => LocalSignedRequest.fullRequest s P coord ctx u n x q) :=
  fun q => uniformLocalJets_of_memClass (LocalSignedRequest.fullRequest_class s P coord ctx u h q) K


-- @@ L718-741 verbatim
/-- The actual residuals, their support, and their incoming mean classes
give the complete copy-uniform request estimate. No request jet is assumed. -/
theorem physical_fullRequest_localJets {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (ctx : CorrectionState.Context LocalSignedRequest.Point)
    (u : CorrectionState.State LocalSignedRequest.Point) (α : ℝ)
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual ctx n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual ctx n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hsθ : ∀ n, LocalSignedRequest.MovingSupport P.a P.b coord U.carrier (u.thetaResidual ctx n))
    (hsz : ∀ n, LocalSignedRequest.MovingSupport P.a P.b coord U.carrier (u.axialResidual ctx n))
    (hcθ : MeanClass (LocalSignedRequest.movingStripData U P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL) α (u.thetaResidual ctx))
    (hcz : MeanClass (LocalSignedRequest.movingStripData U P.a P.b cL cR P.a_pos hcL hcR
      ε L hε hεone hL) α (u.axialResidual ctx))
    (K : Λ → ℕ → I → Set (LocalSignedRequest.Point × ℝ)) :
    let s := LocalSignedRequest.movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL
    ∀ q, UniformLocalJets (HarmonicWaveInteraction.productStrip s)
      (fun _ _ x => s.zeta x.1) (α - 1) K
      (fun _ n _ x => LocalSignedRequest.fullRequest s P coord ctx u n x q) := by
  dsimp only
  exact fullRequest_localJets _ P coord ctx u
    (LocalSignedRequest.normalizedRequest_class U P hcL hcR ε L hε hεone hL ctx u α
      hθ hz hsθ hsz hcθ hcz) K


-- @@ L743-743 verbatim
/-! ## One selected reference family supplies the complete signed input -/


-- @@ L745-745 verbatim
section Combined


-- @@ L747-751 verbatim
variable [Countable Λ] [Nonempty Λ]
  {F₀ : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F₀}
  {H₀ : NominalConeAssembly.Certificate W₀} {ld : ModulatedProfileAssembly.LoopData W₀}
  {v₀ : ModulatedProfileAssembly.Witness ld}
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}


-- @@ L753-753 verbatim
namespace PreparedChart


-- @@ L755-758 verbatim
variable {a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0}
  (C : PreparedChart H₀ v₀ a D) (hr0 : 0 < r0) (vr vt : TorusInverse.Plane)
  {s : StripData X} {K : Λ → ℕ → I → Set X}
  (copy : CopyChart s C.native C.weight K)


-- @@ L760-765 verbatim
/-- Copied matrix, defined pointwise by `copy.pull (pulseMatrix
(PrimaryGeometryAssembly.construction H₀ v₀ a hr0) (preparedPrefactor r0 vr vt)
C.coordinate) l n i`. -/
noncomputable def copiedMatrix : Λ → I → ℕ → X → Mat2 :=
  fun l i n => copy.pull (pulseMatrix (PrimaryGeometryAssembly.construction H₀ v₀ a hr0)
    (preparedPrefactor r0 vr vt) C.coordinate) l n i


-- @@ L767-769 verbatim
/-- Copied target, defined pointwise by `scale.value l n ^ 2 • copy.pull C.target l n i x`. -/
noncomputable def copiedTarget (scale : PositiveScale Λ) : Λ → I → ℕ → X → Vec2 :=
  fun l i n x => scale.value l n ^ 2 • copy.pull C.target l n i x


-- @@ L771-779 verbatim
/-- Copied coefficients, constructed using `ReferenceBounds.copiedCoefficients`. -/
noncomputable def copiedCoefficients (scale normal clock : PositiveScale Λ)
    (base : Λ → I → LinearWaveBounds.WaveCoefficients X)
    (dirs : Λ → I → LinearWaveBounds.GraphDirections X) (request : ℕ → X → Vec2) (j : Fin 2) :
    Λ → I → LinearWaveBounds.WaveCoefficients X :=
  ReferenceBounds.copiedCoefficients
    (F := PrimaryGeometryAssembly.construction H₀ v₀ a hr0)
    (pref := preparedPrefactor r0 vr vt) (χ := C.coordinate) (T := C.target) (mask := C.mask)
    copy scale normal clock base dirs request j


-- @@ L781-781 verbatim
end PreparedChart


-- @@ L783-840 verbatim
/-- Starting with an already selected prepared primary, a common tail
restriction gives actual uniform native covariance, request-driven signed
amplitude/pressure bounds, and the actual cutoff jets. No finished control
record, target jet, fundamental jet, or copied request jet is an input. -/
theorem exists_actual_signed_control
    (a : PrimaryGeometryAssembly.Prepared H₀ v₀ upper B r0 N0)
    (hcone : LeadingStressWeights.FullTrueCone v₀) (hr0 : 0 < r0)
    (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    ∃ N : ℕ, ∃ hN : a.N ≤ N,
      ∀ (C : PreparedChart H₀ v₀ (a.restrict N hN) D)
        (s : StripData LocalSignedRequest.Point)
        (K : Λ → ℕ → I → Set (LocalSignedRequest.Point × ℝ))
        (copy : CopyChart (HarmonicWaveInteraction.productStrip s) C.native C.weight K)
        (scale normal clock : PositiveScale Λ)
        (base : Λ → I → LinearWaveBounds.WaveCoefficients (LocalSignedRequest.Point × ℝ))
        (dirs : Λ → I → LinearWaveBounds.GraphDirections (LocalSignedRequest.Point × ℝ))
        (P : SignedStressPrimitive.Patch) (coord : ℝ)
        (ctx : CorrectionState.Context LocalSignedRequest.Point)
        (u : CorrectionState.State LocalSignedRequest.Point) (β : ℝ)
        (W : Λ → ℕ → LocalSignedRequest.Point × ℝ → ℝ)
        (j : Fin 2),
      (∀ x ∈ s.domain, 0 < s.zeta x) →
      (∀ q, MeanClass s β (fun n x => LocalSignedRequest.normalizedRequest s P coord ctx u n x q)) →
      (∀ l n x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → 0 ≤ W l n x) →
      (∀ l n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ K l n i →
        copy.pull (pulseEnvelope (PrimaryGeometryAssembly.construction H₀ v₀ (a.restrict N hN) hr0)
          C.coordinate j) l n i x ≤ W l n x) →
      (∀ l n i x, x ∈ (HarmonicWaveInteraction.productStrip s).domain → x ∈ K l n i →
        (fun y => normal.value l n • copy.pull
          (phaseNormal (PrimaryGeometryAssembly.construction H₀ v₀ (a.restrict N hN) hr0 j)
              C.coordinate)
          l n i y) =ᶠ[𝓝 x] (base l i).normal (HarmonicWaveInteraction.productStrip s) (dirs l i) n)
              →
      UniformPrimaryWeights.UniformBandBound (HarmonicWaveInteraction.productStrip s) (1 / 2)
        (fun li : Λ × I => fun n => 1 / (base li.1 li.2).frequency n) →
      Nonempty (SignedCopyBounds.UniformNativeCovariance (HarmonicWaveInteraction.productStrip s) K
        (C.copiedMatrix hr0 vr vt copy) (C.copiedTarget copy scale)) ∧
      UniformLocalJets (HarmonicWaveInteraction.productStrip s)
        (fun l n x => Real.sqrt (s.zeta x.1) * W l n x) (β + 1 / 2) K
        (fun l n i => (C.copiedCoefficients hr0 vr vt copy scale normal clock base dirs
          (LocalSignedRequest.fullRequest s P coord ctx u) j l i).amplitude n) ∧
      UniformLocalJets (HarmonicWaveInteraction.productStrip s)
        (fun l n x => Real.sqrt (s.zeta x.1) * W l n x) (β + 1) K
        (fun l n i => (C.copiedCoefficients hr0 vr vt copy scale normal clock base dirs
          (LocalSignedRequest.fullRequest s P coord ctx u) j l i).pressure n) ∧
      UniformLocalJets (HarmonicWaveInteraction.productStrip s) (fun _ _ _ => 1) 0 K
        (copy.pull (fun L x => GaussianTailFlat.profile (C.coordinate L x).2)) := by
  obtain ⟨N, hN, hc⟩ := exists_referenceBounds (D := D) H₀ v₀ a hcone hr0 vr vt hdet
  refine ⟨N, hN, ?_⟩
  intro C s K copy scale normal clock base dirs P coord ctx u β W j hzeta hrequest hW henv hnormal
      hfrequency
  obtain ⟨hr⟩ := hc C
  have hζ : ∀ x ∈ (HarmonicWaveInteraction.productStrip s).domain,
      0 < (HarmonicWaveInteraction.productStrip s).zeta x := fun x hx => hzeta x.1 hx
  have hb := hr.copied_coefficients_jets copy scale normal clock base dirs
    (LocalSignedRequest.fullRequest s P coord ctx u) hζ
    (fullRequest_localJets s P coord ctx u hrequest K) hW j henv hnormal hfrequency
  exact ⟨⟨hr.nativeCovariance copy scale hζ⟩, hb.1, hb.2, copy.unweighted hr.cutoff_jets⟩


-- @@ L842-842 verbatim
end Combined


-- @@ L844-844 verbatim
end NavierStokes.ActualSignedControl


-- @@ L846-846 verbatim
end

-- @@ L847-847 verbatim
end


-- @@ L849-849 verbatim
end


-- @@ L851-851 verbatim
@[expose] public section


-- @@ L853-853 verbatim
noncomputable section


-- @@ L855-855 verbatim
namespace NavierStokes.ActualSignedGeometry


-- @@ L857-857 verbatim
open Set Function Filter WeightedClasses PhaseJetBounds PrimaryCopyBounds

-- @@ L858-858 verbatim
open scoped ContDiff Topology BigOperators


-- @@ L860-861 verbatim
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

-- @@ L862-863 verbatim
/-- Plane: an abbreviation for `TorusInverse.Plane`. -/
abbrev Plane := TorusInverse.Plane

-- @@ L864-865 verbatim
/-- Native: an abbreviation for `Slow × Plane`. -/
abbrev Native := Slow × Plane


-- @@ L867-868 verbatim
private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n


-- @@ L870-870 verbatim
/-! ## The positive native annulus and the actual pulse coordinate -/


-- @@ L872-890 verbatim
/-- Standard slow region, bundling `carrier`, `isOpen`, `have`, `coord_pos` and the required
compatibility proofs. -/
noncomputable def standardSlowRegion {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    LocalSignedRequest.SlowRegion (2 * h) where
  carrier := {z | 0 < z.1 ∧ SimilarityCoordinates.coordinateQ (2 * h) z ∈ Ioo (1 / 2 : ℝ) 2}
  isOpen := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hq := (SimilarityCoordinates.coordinateQ_smooth
      (by linarith : 0 < 2 * h) (by linarith : 2 * h < 1) hz.1).continuousAt
    exact inter_mem (isOpen_lt continuous_const continuous_fst |>.mem_nhds hz.1)
      (hq.preimage_mem_nhds (isOpen_Ioo.mem_nhds hz.2))
  coord_pos := by linarith
  coord_lt_one := by linarith
  qlo := 1 / 2
  qhi := 2
  qlo_pos := by norm_num
  time_pos := fun _ hz => hz.1
  q_mem := fun _ hz => ⟨hz.2.1.le, hz.2.2.le⟩


-- @@ L892-892 verbatim
section Prepared


-- @@ L894-898 verbatim
variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)


-- @@ L900-901 verbatim
/-- Label: an abbreviation for `PrimaryGeometryAssembly.Index W a.N`. -/
abbrev Label := PrimaryGeometryAssembly.Index W a.N


-- @@ L903-917 verbatim
/-- Native slow, bundling `scale`, `carrier`, `isOpen`, `one_le_scale` and the required
compatibility proofs. -/
noncomputable def nativeSlow : PrimaryCopyBounds.JetDomain (Label H v a) Slow where
  scale L := ChartScales.S (BaseChartJets.cellBand L)
  carrier L := (PrimaryGeometryAssembly.domain W a.N).carrier L ∩
    BaseContextAssembly.slowCarrier W (standardSlowRegion F.data.h_pos F.data.h_lt_half)
  isOpen L := ((PrimaryGeometryAssembly.domain W a.N).isOpen L).inter
    (BaseContextAssembly.slowCarrier_open W _)
  one_le_scale L := (PrimaryGeometryAssembly.domain W a.N).one_le_scale L
  growth L p := (BaseContextAssembly.nativeStrip W
    (standardSlowRegion F.data.h_pos F.data.h_lt_half)).growth (BaseChartJets.cellBand L)
      (BaseContextAssembly.insertSlow p)
  scale_le_growth L p _ := by
    exact (le_max_right 1 (ChartScales.S (BaseChartJets.cellBand L))).trans
      ((BaseContextAssembly.nativeStrip W _).slow_le_growth _ _)


-- @@ L919-928 verbatim
/-- Native domain, bundling `scale`, `carrier`, `isOpen`, `one_le_scale` and the required
compatibility proofs. -/
noncomputable def nativeDomain : PrimaryCopyBounds.JetDomain (Label H v a) Native where
  scale L := ChartScales.S (BaseChartJets.cellBand L)
  carrier L := (nativeSlow H v a).carrier L ×ˢ
    (Ioo (-r0) r0 ×ˢ Ioo 0 (ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L)))
  isOpen L := ((nativeSlow H v a).isOpen L).prod (isOpen_Ioo.prod isOpen_Ioo)
  one_le_scale L := (nativeSlow H v a).one_le_scale L
  growth L x := (nativeSlow H v a).growth L x.1
  scale_le_growth L x hx := (nativeSlow H v a).scale_le_growth L x.1 hx.1


-- @@ L930-933 verbatim
/-- Pulse coordinates, given by `(x.1, x.2.2 / ChartScales.slotLength r0 F.data.h
(BaseChartJets.cellBand L))`. -/
noncomputable def pulseCoordinates (L : Label H v a) (x : Native) : Slow × ℝ :=
  (x.1, x.2.2 / ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L))


-- @@ L935-953 verbatim
theorem nativeSlow_positive (L : Label H v a) {p : Slow}
    (hp : p ∈ (nativeSlow H v a).carrier L) :
    p ∈ PositiveRepresentatives.positivePart (PrimaryGeometryAssembly.referenceSet W) := by
  have hs := (BaseContextAssembly.nativeStrip_mem W _ _).mp hp.2
  have ht : 0 < p.2.2 := hs.1.1
  have hq : SimilarityHomogeneity.chartQ F.data.h p ∈ Icc (1 / 2 : ℝ) 2 :=
    ⟨hs.1.2.1.le, hs.1.2.2.le⟩
  have hspec := SimilarityCoordinates.coordinateQ_spec
    (by linarith [F.data.h_pos] : 0 < 2 * F.data.h)
    (by linarith [F.data.h_lt_half] : 2 * F.data.h < 1) (p := (p.2.2, p.2.1)) ht
  have hactive := (BaseContextAssembly.nativeStrip_active W _ hp.2).1
  refine ⟨subset_closure ?_, ht⟩
  refine ⟨(BaseContextAssembly.nativeStrip_radius W _ hp.2).le, ht.le,
    SimilarityHomogeneity.chartQ F.data.h p, hq, hspec.2, ?_⟩
  have he := And.intro hactive.1.le hactive.2.le
  simp only [BaseChartJets.normalizedCoordinates_eq, SimilarityHomogeneity.chartX,
    SimilarityCoordinates.coordinateX, BaseContextAssembly.slowCoordinates_insert,
    div_div] at he
  exact he


-- @@ L955-998 verbatim
theorem pulseCoordinates_jets (hr0 : 0 < r0) :
    PolynomialJets (nativeDomain H v a).toDomain (pulseCoordinates H v a) := by
  have hslow : PolynomialJets (nativeDomain H v a).toDomain (fun _ (x : Native) => x.1) := by
    have hp := PolynomialJets.affine (D := (nativeDomain H v a).toDomain)
      (ContinuousLinearMap.fst ℝ Slow Plane) (fun _ => 0)
      (BaseContextAssembly.one_le_geometryBound W
        (standardSlowRegion F.data.h_pos F.data.h_lt_half)) (m := 0) ?_
    · simp only [add_zero]
        at hp
      exact hp
    intro L x hx
    simpa only [pow_zero, mul_one, add_zero, ContinuousLinearMap.coe_fst'] using
      (BaseContextAssembly.native_geometry W
        (standardSlowRegion F.data.h_pos F.data.h_lt_half) (Label H v a)).bounded L x.1 hx.1.2
  have hv : PolynomialJets (nativeDomain H v a).toDomain (fun _ (x : Native) => x.2.2) := by
    have hp := PolynomialJets.affine (D := (nativeDomain H v a).toDomain)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Slow Plane))
      (fun _ => 0) (C := max 1 (2 * r0 * ChartScales.Tg)) (m := 1) (le_max_left _ _) ?_
    · simpa only [add_zero, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'] using hp
    intro L x hx
    have hn := (a.large (BaseChartJets.cellBand L) L.property).four_le
    have hL := (ChartScales.slotLength_bounds r0 F.data.h hr0.le F.data.h_pos.le hn).2
    have hxv : |x.2.2| ≤ ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L) := by
      rw [abs_of_pos hx.2.2.1]
      exact hx.2.2.2.le
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      add_zero, Real.norm_eq_abs, pow_one]
    exact hxv.trans
      (hL.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (zero_le_one.trans ((nativeDomain H v a).one_le_scale L))))
  have hi : PolynomialJets (nativeDomain H v a).toDomain
      (fun L _ => (ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L))⁻¹) := by
    apply PolynomialJets.const_uniform _ a.one_le_M
    intro L
    have hn := (a.large (BaseChartJets.cellBand L) L.property).four_le
    have hL := (ChartScales.slotLength_bounds r0 F.data.h hr0.le F.data.h_pos.le hn).1
    have hS := (nativeDomain H v a).one_le_scale L
    have hlow : 2 * r0 ≤ ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L) := by
      exact (le_mul_of_one_le_right (by positivity) hS).trans hL
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (lt_of_lt_of_le (by positivity) hlow))]
    simpa only [one_div] using (one_div_le_one_div_of_le (by positivity) hlow).trans a.length_bound
  unfold pulseCoordinates
  simp only [div_eq_mul_inv]
  exact hslow.pair (hv.mul hi)


-- @@ L1000-1039 verbatim
theorem radialDelta_le_edge {r : ℝ}
    (hr : r ∈ Ioo (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W))
    (eta : ℝ) :
    WeightedRadialPrimitive.delta
      (WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius W)
          (PrimaryTargetBounds.rightRadius W))
      (WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) r) ≤
      FinalSlowBase.edgeDistance W (r ^ 2 / 2, eta) := by
  have ha := PrimaryTargetBounds.leftRadius_pos W
  have hb := PrimaryTargetBounds.rightRadius_pos W
  have hr0 := ha.trans hr.1
  have hasq : (PrimaryTargetBounds.leftRadius W) ^ 2 / 2 = NominalConeAssembly.activeLeft W := by
    rw [PrimaryTargetBounds.leftRadius, Real.sq_sqrt
      (mul_nonneg (by norm_num) (NominalConeAssembly.activeLeft_pos W).le)]
    ring
  have hbsq : (PrimaryTargetBounds.rightRadius W) ^ 2 / 2 = NominalConeAssembly.activeRight W := by
    rw [PrimaryTargetBounds.rightRadius, Real.sq_sqrt
      (mul_nonneg (by norm_num) (LeadingStressWeights.activeRight_pos W).le)]
    ring
  have halog := PrimaryTargetBounds.log_square_half ha
  have hblog := PrimaryTargetBounds.log_square_half hb
  rw [hasq] at halog
  rw [hbsq] at hblog
  have hl : Real.log (r ^ 2 / 2) - FinalSlowBase.logLeft W =
      2 * WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) r := by
    rw [FinalSlowBase.logLeft, WeightedRadialPrimitive.logPosition,
      Real.log_div hr0.ne' ha.ne', PrimaryTargetBounds.log_square_half hr0, halog]
    ring
  have hu : FinalSlowBase.logRight W - Real.log (r ^ 2 / 2) =
      2 * (WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius W)
          (PrimaryTargetBounds.rightRadius W) -
        WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W) r) := by
    rw [FinalSlowBase.logRight, WeightedRadialPrimitive.logLength,
      WeightedRadialPrimitive.logPosition, Real.log_div hb.ne' ha.ne',
      Real.log_div hr0.ne' ha.ne', PrimaryTargetBounds.log_square_half hr0, hblog]
    ring
  have hp := WeightedRadialPrimitive.logPosition_mem ha hr
  change min 1 (min _ _) ≤ min 1 (min _ _)
  rw [hl, hu]
  exact min_le_min le_rfl (min_le_min (by linarith [hp.1]) (by linarith [hp.2]))


-- @@ L1041-1063 verbatim
theorem nativeSlow_inverse_edge (L : Label H v a) {p : Slow}
    (hp : p ∈ (nativeSlow H v a).carrier L) :
    (FinalSlowBase.edgeDistance W (BaseChartJets.normalizedCoordinates F.data.h p).2)⁻¹ ≤
      (nativeSlow H v a).growth L p := by
  let st := BaseContextAssembly.nativeStrip W (standardSlowRegion F.data.h_pos F.data.h_lt_half)
  have hm := (BaseContextAssembly.nativeStrip_mem W _ _).mp hp.2
  have ht : 0 < p.2.2 := hm.1.1
  have hδ := st.delta_pos _ hp.2
  have hle := radialDelta_le_edge (W := W) hm.2
    (BaseChartJets.normalizedCoordinates F.data.h p).2.2
  simp only [BaseContextAssembly.slowCoordinates_insert] at hle
  rw [PrimaryTargetBounds.profileRadius_sq (F := F) ht] at hle
  have heq : PrimaryTargetBounds.profileRadius F.data.h p =
      (LocalSignedRequest.profileMap (2 * F.data.h) (BaseContextAssembly.insertSlow p)).1 := by
    unfold PrimaryTargetBounds.profileRadius
    rw [BaseChartJets.normalizedCoordinates_eq]
    rfl
  rw [heq] at hle
  have hi : (FinalSlowBase.edgeDistance W (BaseChartJets.normalizedCoordinates F.data.h p).2)⁻¹ ≤
      (st.delta (BaseContextAssembly.insertSlow p))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hδ hle
  exact hi.trans ((le_max_right 1 _).trans
    (le_mul_of_one_le_left (le_trans zero_le_one (le_max_left 1 _)) (st.one_le_slow _)))


-- @@ L1065-1096 verbatim
/-- This is the native chart of the supplied prepared family. All its
coordinate, growth, annular and positive-reference fields are proved. -/
noncomputable def preparedChart (hr0 : 0 < r0) :
    ActualSignedControl.PreparedChart H v a Native where
  native := nativeDomain H v a
  slow := nativeSlow H v a
  coordinate := pulseCoordinates H v a
  scale _ := rfl
  coordinate_jets := pulseCoordinates_jets H v a hr0
  maps L x hx := by
    have hL : 0 < ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L) :=
      div_pos (mul_pos (by norm_num) hr0) (ChartScales.timeCoefficient_pos _ _)
    exact ⟨hx.1.1, div_pos hx.2.2.1 hL, (div_lt_one hL).mpr hx.2.2.2⟩
  positive L x hx := nativeSlow_positive H v a L hx.1
  slow_maps _ _ hx := hx.1
  slow_growth _ _ _ := le_rfl
  radiusLower := BaseContextAssembly.geometryRadius W (standardSlowRegion F.data.h_pos
      F.data.h_lt_half)
  normUpper := BaseContextAssembly.geometryBound W (standardSlowRegion F.data.h_pos
      F.data.h_lt_half)
  qLower := (1 / 2) / 2
  qUpper := BaseContextAssembly.geometryUpper (standardSlowRegion F.data.h_pos F.data.h_lt_half)
  radius_pos := BaseContextAssembly.geometryRadius_pos W _
  q_pos := by norm_num
  geometry := by
    have g := BaseContextAssembly.native_geometry W (standardSlowRegion F.data.h_pos
        F.data.h_lt_half)
      (Label H v a)
    exact ⟨fun L p hp => g.time L p hp.2, fun L p hp => g.radius L p hp.2,
      fun L p hp => g.bounded L p hp.2, fun L p hp => g.q_range L p hp.2,
      fun L p hp => g.x_range L p hp.2⟩
  inverse_edge L p hp := nativeSlow_inverse_edge H v a L hp


-- @@ L1098-1100 verbatim
@[simp] theorem preparedChart_coordinate (hr0 : 0 < r0) (L : Label H v a) (x : Native) :
    (preparedChart H v a hr0).coordinate L x =
      (x.1, x.2.2 / (PrimaryGeometryAssembly.construction H v a hr0 0).L L) := rfl


-- @@ L1102-1102 verbatim
end Prepared


-- @@ L1104-1104 verbatim
/-! ## Uniform comparisons on the actual four-level window -/


-- @@ L1106-1107 verbatim
/-- Power bound, given by `(2 : ℝ) ^ (4 * |exponent|)`. -/
noncomputable def powerBound (exponent : ℝ) : ℝ := (2 : ℝ) ^ (4 * |exponent|)


-- @@ L1109-1110 verbatim
theorem powerBound_one (exponent : ℝ) : 1 ≤ powerBound exponent :=
  Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num) (abs_nonneg _))


-- @@ L1112-1119 verbatim
theorem dyadic_ratioPower (n m : ℕ) (exponent : ℝ) :
    PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) exponent =
      (2 : ℝ) ^ (((m : ℝ) - (n : ℝ)) * exponent) := by
  unfold PhysicalParticularWave.ratioPower ChartScales.Q SlotColoring.dyadicQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring


-- @@ L1121-1135 verbatim
theorem dyadic_ratioPower_le {n m : ℕ} (hnm : n ≤ m + 4) (hmn : m ≤ n + 4)
    (exponent : ℝ) :
    PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) exponent ≤
      powerBound exponent := by
  rw [dyadic_ratioPower]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hd : |(m : ℝ) - (n : ℝ)| ≤ 4 := by
    have h1 : (n : ℝ) ≤ (m : ℝ) + 4 := by exact_mod_cast hnm
    have h2 : (m : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hmn
    rw [abs_le]
    constructor <;> linarith
  calc
    _ ≤ |((m : ℝ) - (n : ℝ)) * exponent| := le_abs_self _
    _ = |(m : ℝ) - (n : ℝ)| * |exponent| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (abs_nonneg _)


-- @@ L1137-1156 verbatim
theorem dyadic_ratioPower_lower {n m : ℕ} (hnm : n ≤ m + 4) (hmn : m ≤ n + 4)
    (exponent : ℝ) :
    1 / powerBound exponent ≤
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) exponent := by
  have h := dyadic_ratioPower_le hmn hnm exponent
  have hp := PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos m) (ChartScales.Q_pos n)
      exponent
  have hb : 0 < powerBound exponent := zero_lt_one.trans_le (powerBound_one _)
  have he : PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) exponent *
      PhysicalParticularWave.ratioPower (ChartScales.Q m) (ChartScales.Q n) exponent = 1 := by
    unfold PhysicalParticularWave.ratioPower
    field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos n) exponent).ne',
      (Real.rpow_pos_of_pos (ChartScales.Q_pos m) exponent).ne']
  apply (div_le_iff₀ hb).mpr
  calc
    1 = PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) exponent *
        PhysicalParticularWave.ratioPower (ChartScales.Q m) (ChartScales.Q n) exponent := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h
      (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)
          exponent).le


-- @@ L1158-1164 verbatim
theorem S_window_le {n m : ℕ} (hn : 1 ≤ n) (hmn : m ≤ n + 4) :
    ChartScales.S m ≤ 25 * ChartScales.S n := by
  have hm : (m : ℝ) ≤ 5 * (n : ℝ) := by exact_mod_cast (show m ≤ 5 * n by omega)
  have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold ChartScales.S
  nlinarith [sq_nonneg (5 * (n : ℝ) - m)]


-- @@ L1166-1175 verbatim
theorem sqrt_S_window {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    1 / 5 ≤ Real.sqrt (ChartScales.S n) / Real.sqrt (ChartScales.S m) ∧
      Real.sqrt (ChartScales.S n) / Real.sqrt (ChartScales.S m) ≤ 5 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn5 : (n : ℝ) ≤ 5 * (m : ℝ) := by exact_mod_cast (show n ≤ 5 * m by omega)
  have hm5 : (m : ℝ) ≤ 5 * (n : ℝ) := by exact_mod_cast (show m ≤ 5 * n by omega)
  simp only [ChartScales.S, Real.sqrt_sq (le_of_lt hn0), Real.sqrt_sq (le_of_lt hm0)]
  exact ⟨(le_div_iff₀ hm0).mpr (by linarith), (div_le_iff₀ hm0).mpr hn5⟩


-- @@ L1177-1185 verbatim
theorem common_native_gap {h : ℝ} (hh : 0 ≤ h) {index : ℕ → ℕ} {budget : ℕ}
    (hi : CommonBaseContext.IndexBounds h index budget) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    ChartScales.nativeIndex h m - index n ≤ budget + SlotColoring.nativeGap h := by
  have hg := (SlotColoring.nativeIndex_gap h hh hn hm hnm hmn).2
  have hb := hi.gap_le n
  have he := hi.le_native n
  dsimp only [ChartScales.nativeIndex] at *
  omega


-- @@ L1187-1187 verbatim
section Scales


-- @@ L1189-1190 verbatim
variable {Λ : Type} (chart : ℕ → ℕ) (reference : Λ → ℕ → ℕ)
  (hnear : ∀ l n, chart n ≤ reference l n + 4 ∧ reference l n ≤ chart n + 4)


-- @@ L1192-1202 verbatim
/-- Band power scale, bundling `value`, `lower`, `upper`, `lower_pos` and the required
compatibility proofs. -/
noncomputable def bandPowerScale (exponent : ℝ) : ActualSignedControl.PositiveScale Λ where
  value l n := PhysicalParticularWave.ratioPower (ChartScales.Q (chart n))
    (ChartScales.Q (reference l n)) exponent
  lower := 1 / powerBound exponent
  upper := powerBound exponent
  lower_pos := div_pos zero_lt_one (zero_lt_one.trans_le (powerBound_one _))
  upper_one := powerBound_one _
  bounds l n := ⟨dyadic_ratioPower_lower (hnear l n).1 (hnear l n).2 _,
    dyadic_ratioPower_le (hnear l n).1 (hnear l n).2 _⟩


-- @@ L1204-1206 verbatim
/-- Velocity scale, given by `bandPowerScale chart reference hnear (CoordinateAlgebra.A h)`. -/
noncomputable def velocityScale (h : ℝ) : ActualSignedControl.PositiveScale Λ :=
  bandPowerScale chart reference hnear (CoordinateAlgebra.A h)


-- @@ L1208-1211 verbatim
/-- Clock scale, given by `bandPowerScale chart reference hnear (CoordinateAlgebra.A h + 1 /
2)`. -/
noncomputable def clockScale (h : ℝ) : ActualSignedControl.PositiveScale Λ :=
  bandPowerScale chart reference hnear (CoordinateAlgebra.A h + 1 / 2)


-- @@ L1213-1216 verbatim
@[simp] theorem velocityScale_value (h : ℝ) (l : Λ) (n : ℕ) :
    (velocityScale chart reference hnear h).value l n =
      PhysicalParticularWave.velocityWeight h (ChartScales.Q (chart n))
        (ChartScales.Q (reference l n)) := rfl


-- @@ L1218-1221 verbatim
@[simp] theorem clockScale_value (h : ℝ) (l : Λ) (n : ℕ) :
    (clockScale chart reference hnear h).value l n =
      PhysicalParticularWave.clockWeight h (ChartScales.Q (chart n))
        (ChartScales.Q (reference l n)) := rfl


-- @@ L1223-1223 verbatim
end Scales


-- @@ L1225-1225 verbatim
/-! ## The selected slot, including the periodic clock's padding -/


-- @@ L1227-1227 verbatim
section Slots


-- @@ L1229-1231 verbatim
variable {D h : ℝ} {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem D h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)


-- @@ L1233-1236 verbatim
/-- Slot geometry, constructed using `CommonCoverClass.bandGeometry`. -/
noncomputable def slotGeometry (l : SlotColoring.Label) (gap : ℕ) : CommonCoverSolve.Geometry :=
  CommonCoverClass.bandGeometry (TorusAverages.slotChart vr vt hdet) h l.1 gap
    (PartitionedCovariance.slotCenter h l - sys.radius • vt)


-- @@ L1238-1245 verbatim
/-- Clock window, bundling `lower`, `upper`, `padding`, `padding_pos`. -/
noncomputable def clockWindow (m : ℕ) : PeriodicPhaseAssembly.ClockWindow where
  lower := (-sys.radius, 0)
  upper := (sys.radius, ChartScales.slotLength sys.radius h m)
  padding := min sys.radius (ChartScales.slotLength sys.radius h m) / 16
  padding_pos := div_pos (lt_min sys.radius_pos
    (div_pos (mul_pos (by
        norm_num) sys.radius_pos) (ChartScales.timeCoefficient_pos h m))) (by norm_num)


-- @@ L1247-1251 verbatim
theorem slotGeometry_basis (l : SlotColoring.Label) (gap : ℕ) (z : Plane) :
    (slotGeometry sys hdet l gap).basis z =
      z.1 • vr + (ChartScales.timeCoefficient h l.1 * z.2) • vt := by
  rw [slotGeometry, CommonCoverClass.bandGeometry, CommonCoverClass.scaledBasis_apply,
    TorusAverages.slotChart_apply]


-- @@ L1253-1291 verbatim
theorem clock_outer_in_slot (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1) (gap : ℕ) :
    (fun z => (slotGeometry sys hdet l gap).center + (slotGeometry sys hdet l gap).basis z) ''
      (clockWindow sys l.1).outer ⊆ PartitionedCovariance.slotSet h sys.radius vr vt l := by
  rintro _ ⟨z, hz, rfl⟩
  have hr := sys.radius_pos
  have hci := ChartScales.timeCoefficient_pos h l.1
  have hci1 : ChartScales.timeCoefficient h l.1 ≤ 1 :=
    ((ChartScales.timeCoefficient_bounds h hh hl).2).trans
      ((div_le_one (ChartScales.S_pos (by omega))).mpr (PhysicalGraphBounds.S_ge_one (by omega)))
  have hpad0 := (clockWindow sys l.1).padding_pos
  have hpad : (clockWindow sys l.1).padding ≤ sys.radius / 16 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hz1 : |z.1| ≤ 2 * sys.radius := by
    have he : -sys.radius - 2 * (clockWindow sys l.1).padding ≤ z.1 ∧
        z.1 ≤ sys.radius + 2 * (clockWindow sys l.1).padding := hz.1
    exact abs_le.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
  have hprodpad : ChartScales.timeCoefficient h l.1 * (clockWindow sys l.1).padding ≤ sys.radius /
      16 :=
    (mul_le_of_le_one_left hpad0.le hci1).trans hpad
  have htime : ChartScales.timeCoefficient h l.1 * ChartScales.slotLength sys.radius h l.1 =
      2 * sys.radius := by
    unfold ChartScales.slotLength
    field_simp
  have hz2 : |ChartScales.timeCoefficient h l.1 * z.2 - sys.radius| ≤ 2 * sys.radius := by
    have he : -(2 * (clockWindow sys l.1).padding) ≤ z.2 ∧
        z.2 ≤ ChartScales.slotLength sys.radius h l.1 + 2 * (clockWindow sys l.1).padding := by
      have he := hz.2
      simp only [clockWindow, zero_sub] at he
      exact he
    have hlo := mul_le_mul_of_nonneg_left he.1 hci.le
    have hhi := mul_le_mul_of_nonneg_left he.2 hci.le
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  refine ⟨z.1, ChartScales.timeCoefficient h l.1 * z.2 - sys.radius, hz1, hz2, ?_⟩
  dsimp only
  rw [slotGeometry_basis]
  change PartitionedCovariance.slotCenter h l - sys.radius • vt +
      (z.1 • vr + (ChartScales.timeCoefficient h l.1 * z.2) • vt) = _
  rw [sub_smul]
  abel


-- @@ L1293-1297 verbatim
theorem clockWindow_injective (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1) (gap : ℕ) :
    InjOn TorusAverages.quotientPoint
      ((fun z => (slotGeometry sys hdet l gap).center + (slotGeometry sys hdet l gap).basis z) ''
        (clockWindow sys l.1).outer) :=
  (sys.injective l).mono (clock_outer_in_slot sys hdet hh hl gap)


-- @@ L1299-1304 verbatim
theorem slotGeometry_separated (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1) (gap : ℕ) :
    WaveEnvelopeTransport.Separated (slotGeometry sys hdet l gap)
      sys.radius (ChartScales.slotLength sys.radius h l.1) := by
  apply (clockWindow_injective sys hdet hh hl gap).mono
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, (clockWindow sys l.1).core_subset_outer hz, rfl⟩


-- @@ L1306-1311 verbatim
theorem slotGeometry_argumentCost (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1)
    {gap budget : ℕ} (hg : gap ≤ budget) :
    CommonCoverClass.argumentCost (slotGeometry sys hdet l gap) ≤
      CommonCoverClass.bandArgumentCost (TorusAverages.slotChart vr vt hdet) budget * ChartScales.S
          l.1 :=
  CommonCoverClass.bandGeometry_argumentCost_le _ hh hl hg _


-- @@ L1313-1325 verbatim
theorem slotGeometry_common_cost (hh : 0 ≤ h) {index : ℕ → ℕ} {budget : ℕ}
    (hi : CommonBaseContext.IndexBounds h index budget) {n : ℕ} {l : SlotColoring.Label}
    (hn : 1 ≤ n) (hl : 4 ≤ l.1) (hnl : n ≤ l.1 + 4) (hln : l.1 ≤ n + 4) :
    CommonCoverClass.argumentCost
      (slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - index n)) ≤
      (25 * CommonCoverClass.bandArgumentCost (TorusAverages.slotChart vr vt hdet)
        (budget + SlotColoring.nativeGap h)) * ChartScales.S n := by
  refine (slotGeometry_argumentCost sys hdet hh hl
    (common_native_gap hh hi hn (by omega) hnl hln)).trans ?_
  have hc := CommonCoverClass.bandArgumentCost_one_le (TorusAverages.slotChart vr vt hdet)
    (budget + SlotColoring.nativeGap h)
  have he := mul_le_mul_of_nonneg_left (S_window_le hn hln) (zero_le_one.trans hc)
  nlinarith


-- @@ L1327-1327 verbatim
end Slots


-- @@ L1329-1329 verbatim
/-! ## The exact physical change of slow variables and the copy affine map -/


-- @@ L1331-1337 verbatim
/-- Slow change as an element of `Slow →L[ℝ] Slow`. -/
noncomputable def slowChange (h Q Qr : ℝ) : Slow →L[ℝ] Slow :=
  (PhysicalParticularWave.ratioPower Q Qr (1 / 2) • ContinuousLinearMap.fst ℝ ℝ Plane).prod
    (((PhysicalParticularWave.ratioPower Q Qr (CoordinateAlgebra.D h) •
        ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (PhysicalParticularWave.ratioPower Q Qr 1 • ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
        (ContinuousLinearMap.snd ℝ ℝ Plane))


-- @@ L1339-1343 verbatim
@[simp] theorem slowChange_apply (h Q Qr : ℝ) (p : Slow) :
    slowChange h Q Qr p =
      (PhysicalParticularWave.ratioPower Q Qr (1 / 2) * p.1,
        (PhysicalParticularWave.ratioPower Q Qr (CoordinateAlgebra.D h) * p.2.1,
          PhysicalParticularWave.ratioPower Q Qr 1 * p.2.2)) := rfl


-- @@ L1345-1349 verbatim
theorem slowChange_eq_transition {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    ⇑(slowChange h Q Qr) = SimilarityHomogeneity.chartTransition h Q Qr := by
  funext p
  simp only [slowChange_apply, SimilarityHomogeneity.chartTransition,
    PhysicalParticularWave.ratioPower, Real.div_rpow hQ.le hQr.le, Real.rpow_one]


-- @@ L1351-1353 verbatim
theorem slowChange_time {h Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) {p : Slow}
    (ht : 0 < p.2.2) : 0 < (slowChange h Q Qr p).2.2 :=
  mul_pos (PhysicalParticularWave.ratioPower_pos hQ hQr _) ht


-- @@ L1355-1357 verbatim
theorem slowChange_radius {h Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) {p : Slow}
    (hr : 0 < p.1) : 0 < (slowChange h Q Qr p).1 :=
  mul_pos (PhysicalParticularWave.ratioPower_pos hQ hQr _) hr


-- @@ L1359-1365 verbatim
theorem normalized_inner_slowChange {F : OutgoingProfile.Profile}
    {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) {p : Slow} (ht : 0 < p.2.2) :
    (BaseChartJets.normalizedCoordinates F.data.h (slowChange F.data.h Q Qr p)).2 =
      (BaseChartJets.normalizedCoordinates F.data.h p).2 := by
  rw [slowChange_eq_transition hQ hQr, BaseChartJets.normalizedCoordinates_eq,
    BaseChartJets.normalizedCoordinates_eq]
  exact SimilarityHomogeneity.chartInner_transition F.data.h_pos F.data.h_lt_half hQ hQr ht


-- @@ L1367-1378 verbatim
theorem profileRadius_slowChange {F : OutgoingProfile.Profile}
    {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) {p : Slow} (ht : 0 < p.2.2) (hr : 0 < p.1) :
    PrimaryTargetBounds.profileRadius F.data.h (slowChange F.data.h Q Qr p) =
      PrimaryTargetBounds.profileRadius F.data.h p := by
  have htp := slowChange_time (h := F.data.h) hQ hQr ht
  have hrp := slowChange_radius (h := F.data.h) hQ hQr hr
  have hp := PrimaryTargetBounds.profileRadius_pos (F := F) ht hr
  have hp' := PrimaryTargetBounds.profileRadius_pos (F := F) htp hrp
  have he := congrArg Prod.fst (normalized_inner_slowChange (F := F) hQ hQr ht)
  rw [← PrimaryTargetBounds.profileRadius_sq (F := F) htp,
    ← PrimaryTargetBounds.profileRadius_sq (F := F) ht] at he
  nlinarith


-- @@ L1380-1385 verbatim
theorem movingWeight_slowChange {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) {p : Slow} (ht : 0 < p.2.2) (hr : 0 < p.1) :
    PrimaryTargetBounds.movingWeight W (slowChange F.data.h Q Qr p) =
      PrimaryTargetBounds.movingWeight W p := by
  unfold PrimaryTargetBounds.movingWeight
  rw [profileRadius_slowChange hQ hQr ht hr]


-- @@ L1387-1390 verbatim
/-- Slow change cost, given by `1 + powerBound (1 / 2) + powerBound (CoordinateAlgebra.D h) +
powerBound 1`. -/
noncomputable def slowChangeCost (h : ℝ) : ℝ :=
  1 + powerBound (1 / 2) + powerBound (CoordinateAlgebra.D h) + powerBound 1


-- @@ L1392-1394 verbatim
theorem slowChangeCost_one (h : ℝ) : 1 ≤ slowChangeCost h := by
  unfold slowChangeCost
  linarith [powerBound_one (1 / 2), powerBound_one (CoordinateAlgebra.D h), powerBound_one 1]


-- @@ L1396-1421 verbatim
theorem norm_slowChange_le (h : ℝ) {n m : ℕ} (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    ‖slowChange h (ChartScales.Q n) (ChartScales.Q m)‖ ≤ slowChangeCost h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (slowChangeCost_one _))
  intro p
  have hc (exponent : ℝ) :
      |PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) exponent| ≤
        powerBound exponent := by
    rw [abs_of_pos (PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos _) (ChartScales.Q_pos
        _) _)]
    exact dyadic_ratioPower_le hnm hmn _
  have hb (exponent : ℝ) (hcost : powerBound exponent ≤ slowChangeCost h)
      (y : ℝ) (hy : ‖y‖ ≤ ‖p‖) :
      ‖PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) exponent * y‖ ≤
        slowChangeCost h * ‖p‖ := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul ((hc exponent).trans hcost) hy (norm_nonneg _) (zero_le_one.trans
        (slowChangeCost_one _))
  change max ‖_‖ (max ‖_‖ ‖_‖) ≤ _
  have h1 := powerBound_one (1 / 2)
  have h2 := powerBound_one (CoordinateAlgebra.D h)
  have h3 := powerBound_one 1
  refine max_le (hb (1 / 2) (by unfold slowChangeCost; linarith) p.1 (norm_fst_le p)) ?_
  exact max_le
    (hb (CoordinateAlgebra.D h) (by
        unfold slowChangeCost; linarith) p.2.1 ((norm_fst_le p.2).trans (norm_snd_le p)))
    (hb 1 (by unfold slowChangeCost; linarith) p.2.2 ((norm_snd_le p.2).trans (norm_snd_le p)))


-- @@ L1423-1426 verbatim
/-- Mean equiv, given by `(ParticularWaveBounds.liftAssoc Plane).symm.trans
PhysicalResidualTZ.swapSlow`. -/
noncomputable def meanEquiv : Native ≃ₗᵢ[ℝ] LocalSignedRequest.Point :=
  (ParticularWaveBounds.liftAssoc Plane).symm.trans PhysicalResidualTZ.swapSlow


-- @@ L1428-1429 verbatim
@[simp] theorem meanEquiv_apply (x : Native) : meanEquiv x = (x.1.1, ((x.1.2.2, x.1.2.1), x.2)) :=
    rfl


-- @@ L1431-1436 verbatim
/-- View strip, constructed using `ParticularWaveBounds.reindexStrip`. -/
noncomputable def viewStrip {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (chart : ℕ → ℕ) : StripData Native :=
  ParticularWaveBounds.reindexStrip meanEquiv
    (UniformPrimaryWeights.reindexedStrip (BaseContextAssembly.nativeStrip W U)
      (fun n => (chart n, ())))


-- @@ L1438-1440 verbatim
theorem viewStrip_slow {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (chart : ℕ → ℕ) (n : ℕ) :
    (viewStrip W U chart).slow n = max 1 (ChartScales.S (chart n)) := rfl


-- @@ L1442-1444 verbatim
theorem viewStrip_mem {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (chart : ℕ → ℕ) (x : Native) :
    x ∈ (viewStrip W U chart).domain ↔ x.1 ∈ BaseContextAssembly.slowCarrier W U := Iff.rfl


-- @@ L1446-1450 verbatim
theorem viewStrip_zeta {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (chart : ℕ → ℕ) (x : Native) :
    (viewStrip W U chart).zeta x = PrimaryTargetBounds.movingWeight W x.1 := by
  change (BaseContextAssembly.nativeStrip W U).zeta (meanEquiv x) = _
  exact PrimaryTargetBounds.movingStripData_zeta W U _ _ _ _ _ _


-- @@ L1452-1461 verbatim
theorem viewStrip_delta {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h)) (chart : ℕ → ℕ) (x : Native) :
    (viewStrip W U chart).delta x = WeightedRadialPrimitive.delta
      (WeightedRadialPrimitive.logLength (PrimaryTargetBounds.leftRadius W)
          (PrimaryTargetBounds.rightRadius W))
      (WeightedRadialPrimitive.logPosition (PrimaryTargetBounds.leftRadius W)
        (PrimaryTargetBounds.profileRadius F.data.h x.1)) := by
  unfold PrimaryTargetBounds.profileRadius
  rw [BaseChartJets.normalizedCoordinates_eq]
  rfl


-- @@ L1463-1463 verbatim
section CopyMap


-- @@ L1465-1467 verbatim
variable {D h : ℝ} {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem D h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)


-- @@ L1469-1473 verbatim
/-- Copy point as an element of `Native`. -/
noncomputable def copyPoint (l : SlotColoring.Label) (chart common : ℕ)
    (k : TorusInverse.Frequency) (x : Native) : Native :=
  (slowChange h (ChartScales.Q chart) (ChartScales.Q l.1) x.1,
    (slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - common)).coordinates k x.2)


-- @@ L1475-1478 verbatim
/-- Copy linear as an element of `Native →L[ℝ] Native`. -/
noncomputable def copyLinear (l : SlotColoring.Label) (chart common : ℕ) : Native →L[ℝ] Native :=
  (slowChange h (ChartScales.Q chart) (ChartScales.Q l.1)).prodMap
    (slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - common)).coordinateLinear


-- @@ L1480-1489 verbatim
theorem copyPoint_affine (l : SlotColoring.Label) (chart common : ℕ)
    (k : TorusInverse.Frequency) (x : Native) :
    copyPoint sys hdet l chart common k x =
      copyLinear sys hdet l chart common x + copyPoint sys hdet l chart common k 0 := by
  apply Prod.ext
  · simp [copyPoint, copyLinear]
  · change (slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - common)).coordinates k x.2 =
      (slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - common)).coordinateLinear x.2 +
        (slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - common)).coordinates k 0
    rw [CommonCoverSolve.Geometry.coordinates_eq_affine, add_comm]


-- @@ L1491-1531 verbatim
theorem norm_copyLinear_le (hh : 0 ≤ h) {index : ℕ → ℕ} {budget : ℕ}
    (hi : CommonBaseContext.IndexBounds h index budget) {n : ℕ} {l : SlotColoring.Label}
    (hn : 1 ≤ n) (hl : 4 ≤ l.1) (hnl : n ≤ l.1 + 4) (hln : l.1 ≤ n + 4) :
    ‖copyLinear sys hdet l n (index n)‖ ≤
      (slowChangeCost h + 25 * CommonCoverClass.bandArgumentCost (TorusAverages.slotChart vr vt
          hdet)
        (budget + SlotColoring.nativeGap h)) * BaseContextAssembly.slowScale n := by
  have hc := norm_slowChange_le h hnl hln
  have hg := slotGeometry_common_cost sys hdet hh hi hn hl hnl hln
  have hd : ‖(slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - index n)).coordinateLinear‖ ≤
      CommonCoverClass.argumentCost (slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - index
          n)) := by
    unfold CommonCoverClass.argumentCost
    have hp : 0 ≤ ‖(slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - index n)).pointLinear‖
        *
        (1 + ‖(slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - index
            n)).coordinateLinear‖) := by
            positivity
    linarith
  have hS : 1 ≤ BaseContextAssembly.slowScale n := BaseContextAssembly.one_le_slowScale _
  have hSs : ChartScales.S n ≤ BaseContextAssembly.slowScale n := le_max_right _ _
  have hC := CommonCoverClass.bandArgumentCost_one_le (TorusAverages.slotChart vr vt hdet)
    (budget + SlotColoring.nativeGap h)
  have hA := slowChangeCost_one h
  have hSn : 0 ≤ ChartScales.S n := sq_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change max ‖slowChange h (ChartScales.Q n) (ChartScales.Q l.1) x.1‖
    ‖(slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - index n)).coordinateLinear x.2‖ ≤ _
  apply max_le
  · calc
      _ ≤ slowChangeCost h * ‖x‖ :=
        ((slowChange h _ _).le_opNorm _).trans (mul_le_mul hc (norm_fst_le x) (norm_nonneg _) (by
            linarith))
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
  · calc
      _ ≤ (25 * CommonCoverClass.bandArgumentCost (TorusAverages.slotChart vr vt hdet)
          (budget + SlotColoring.nativeGap h) * ChartScales.S n) * ‖x‖ :=
        ((slotGeometry sys hdet l _).coordinateLinear.le_opNorm _).trans
          (mul_le_mul (hd.trans hg) (norm_snd_le x) (norm_nonneg _) (by positivity))
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)


-- @@ L1533-1533 verbatim
end CopyMap


-- @@ L1535-1535 verbatim
/-! ## The exact coefficient and phase-normal scale factors -/


-- @@ L1537-1541 verbatim
theorem sqrt_epsilon (h : ℝ) (n : ℕ) :
    Real.sqrt (ChartScales.epsilon h n) = ChartScales.Q n ^ (h / 2) := by
  rw [Real.sqrt_eq_rpow, ChartScales.epsilon, ← Real.rpow_mul (ChartScales.Q_pos n).le]
  congr 1
  ring


-- @@ L1543-1548 verbatim
theorem sqrt_epsilon_ratio (h : ℝ) (n m : ℕ) :
    Real.sqrt (ChartScales.epsilon h m) / Real.sqrt (ChartScales.epsilon h n) =
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) (-(h / 2)) := by
  rw [sqrt_epsilon, sqrt_epsilon]
  simpa only [neg_neg] using PhysicalParticularWave.ratioPower_neg_div
    (ChartScales.Q_pos n) (ChartScales.Q_pos m) (-(h / 2))


-- @@ L1550-1553 verbatim
/-- Rounded carrier, given by `(ChartScales.carrier h n : ℝ) * Real.sqrt (ChartScales.epsilon h
n)`. -/
noncomputable def roundedCarrier (h : ℝ) (n : ℕ) : ℝ :=
  (ChartScales.carrier h n : ℝ) * Real.sqrt (ChartScales.epsilon h n)


-- @@ L1555-1560 verbatim
theorem roundedCarrier_bounds {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    1 ≤ roundedCarrier h n ∧ roundedCarrier h n ≤ 2 := by
  obtain ⟨hl, hu⟩ := Scaling.carrier_frequency_sqrt_bounds (ChartScales.epsilon_pos h n)
  have hs : Real.sqrt (ChartScales.epsilon h n) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (ChartScales.epsilon_le_one h hh n)
  exact ⟨hl, hu.trans (by linarith)⟩


-- @@ L1562-1562 verbatim
section PhysicalScales


-- @@ L1564-1565 verbatim
variable {Λ : Type} (chart : ℕ → ℕ) (reference : Λ → ℕ → ℕ)
  (hnear : ∀ l n, chart n ≤ reference l n + 4 ∧ reference l n ≤ chart n + 4)


-- @@ L1567-1570 verbatim
/-- Coefficient scale, given by `(velocityScale chart reference hnear h).mul (bandPowerScale
chart reference hnear (-(h / 2)))`. -/
noncomputable def coefficientScale (h : ℝ) : ActualSignedControl.PositiveScale Λ :=
  (velocityScale chart reference hnear h).mul (bandPowerScale chart reference hnear (-(h / 2)))


-- @@ L1572-1582 verbatim
theorem coefficientScale_value (h : ℝ) (l : Λ) (n : ℕ) :
    (coefficientScale chart reference hnear h).value l n =
      PhysicalSignedWave.coefficientScale (ChartScales.epsilon h (chart n))
        (ChartScales.epsilon h (reference l n))
        (PhysicalParticularWave.velocityWeight h (ChartScales.Q (chart n))
          (ChartScales.Q (reference l n))) := by
  change PhysicalParticularWave.velocityWeight h _ _ *
      PhysicalParticularWave.ratioPower _ _ (-(h / 2)) = _
  rw [← sqrt_epsilon_ratio]
  unfold PhysicalSignedWave.coefficientScale
  ring


-- @@ L1584-1596 verbatim
/-- Carrier ratio scale, bundling `value`, `lower`, `upper`, `lower_pos` and the required
compatibility proofs. -/
noncomputable def carrierRatioScale {h : ℝ} (hh : 0 ≤ h) : ActualSignedControl.PositiveScale Λ where
  value l n := roundedCarrier h (reference l n) / roundedCarrier h (chart n)
  lower := 1 / 2
  upper := 2
  lower_pos := by norm_num
  upper_one := by norm_num
  bounds l n := by
    have h1 := roundedCarrier_bounds hh (reference l n)
    have h2 := roundedCarrier_bounds hh (chart n)
    have hpos : 0 < roundedCarrier h (chart n) := zero_lt_one.trans_le h2.1
    exact ⟨(le_div_iff₀ hpos).mpr (by linarith), (div_le_iff₀ hpos).mpr (by linarith)⟩


-- @@ L1598-1601 verbatim
/-- Normal scale, given by `(carrierRatioScale chart reference hh).mul (bandPowerScale chart
reference hnear (h / 2 + 1 / 2))`. -/
noncomputable def normalScale {h : ℝ} (hh : 0 ≤ h) : ActualSignedControl.PositiveScale Λ :=
  (carrierRatioScale chart reference hh).mul (bandPowerScale chart reference hnear (h / 2 + 1 / 2))


-- @@ L1603-1617 verbatim
theorem normalScale_value {h : ℝ} (hh : 0 ≤ h) (l : Λ) (n : ℕ) :
    (normalScale chart reference hnear hh).value l n =
      PhysicalParticularWave.normalWeight (ChartScales.Q (chart n)) (ChartScales.Q (reference l n))
        (ChartScales.carrier h (chart n)) (ChartScales.carrier h (reference l n)) := by
  change (roundedCarrier h (reference l n) / roundedCarrier h (chart n)) *
      PhysicalParticularWave.ratioPower _ _ (h / 2 + 1 / 2) = _
  rw [← PhysicalParticularWave.ratioPower_mul (ChartScales.Q_pos _) (ChartScales.Q_pos _)]
  unfold roundedCarrier PhysicalParticularWave.normalWeight PhysicalParticularWave.ratioPower
  rw [sqrt_epsilon, sqrt_epsilon]
  have hn := Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h (chart n))
  have hm := Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h (reference l n))
  field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos (chart n)) (h / 2)).ne',
    (Real.rpow_pos_of_pos (ChartScales.Q_pos (reference l n)) (h / 2)).ne',
    (Real.rpow_pos_of_pos (ChartScales.Q_pos (reference l n)) (1 / 2)).ne',
    (show (ChartScales.carrier h (chart n) : ℝ) ≠ 0 from hn.ne')]


-- @@ L1619-1619 verbatim
end PhysicalScales


-- @@ L1621-1621 verbatim
/-! ## The concrete prepared-copy chart -/


-- @@ L1623-1623 verbatim
section PreparedCopies


-- @@ L1625-1635 verbatim
variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)
  {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem (CoordinateAlgebra.D F.data.h) F.data.h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
  (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
  {Λ : Type} (reference : Λ → ℕ → Label H v a)
  (chart index : ℕ → ℕ) (sign : Λ → ℕ → Fin 2)


-- @@ L1637-1640 verbatim
/-- Copy label, given by `PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label W
(reference l n)) (sign l n)`. -/
noncomputable def copyLabel (l : Λ) (n : ℕ) : SlotColoring.Label :=
  PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label W (reference l n)) (sign l n)


-- @@ L1642-1645 verbatim
/-- Phase cell, constructed using `copyPoint`. -/
noncomputable def phaseCell (l : Λ) (n : ℕ) (k : TorusInverse.Frequency) : Set Native :=
  copyPoint sys hdet (copyLabel H v a reference sign l n) (chart n) (index (chart n)) k ⁻¹'
    (nativeDomain H v a).carrier (reference l n)


-- @@ L1647-1651 verbatim
theorem phaseCell_open (l : Λ) (n : ℕ) (k : TorusInverse.Frequency) :
    IsOpen (phaseCell H v a sys hdet reference chart index sign l n k) := by
  apply ((nativeDomain H v a).isOpen (reference l n)).preimage
  exact ((slowChange F.data.h _ _).continuous.comp continuous_fst).prodMk
    (((slotGeometry sys hdet _ _).coordinates_contDiff k).continuous.comp continuous_snd)


-- @@ L1653-1663 verbatim
theorem copy_weight_eq (hr0 : 0 < r0) (l : Λ) (n : ℕ) (k : TorusInverse.Frequency)
    {x : Native} (hx : x ∈ (viewStrip W U chart).domain) :
    (preparedChart H v a hr0).weight (reference l n)
        (copyPoint sys hdet (copyLabel H v a reference sign l n) (chart n) (index (chart n)) k x) =
      (viewStrip W U chart).zeta x := by
  have hp := (viewStrip_mem W U chart x).mp hx
  have ht := BaseContextAssembly.nativeStrip_time W U hp
  have hr := BaseContextAssembly.nativeStrip_radius W U hp
  change PrimaryTargetBounds.movingWeight W (slowChange F.data.h _ _ x.1) = _
  rw [movingWeight_slowChange W (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht hr,
    viewStrip_zeta]


-- @@ L1665-1703 verbatim
theorem copy_growth_le
    (hchart : ∀ n, 1 ≤ chart n)
    (hnear : ∀ l n, chart n ≤ BaseChartJets.cellBand (reference l n) + 4 ∧
      BaseChartJets.cellBand (reference l n) ≤ chart n + 4)
    (l : Λ) (n : ℕ) (k : TorusInverse.Frequency)
    {x : Native} (hx : x ∈ (viewStrip W U chart).domain) :
    (nativeDomain H v a).growth (reference l n)
        (copyPoint sys hdet (copyLabel H v a reference sign l n) (chart n) (index (chart n)) k x) ≤
      25 * (viewStrip W U chart).growth n x := by
  have hp := (viewStrip_mem W U chart x).mp hx
  have ht := BaseContextAssembly.nativeStrip_time W U hp
  have hr := BaseContextAssembly.nativeStrip_radius W U hp
  have he : (BaseContextAssembly.nativeStrip W (standardSlowRegion F.data.h_pos
      F.data.h_lt_half)).delta
      (BaseContextAssembly.insertSlow (slowChange F.data.h (ChartScales.Q (chart n))
        (ChartScales.Q (BaseChartJets.cellBand (reference l n))) x.1)) =
      (viewStrip W U chart).delta x := by
    change (viewStrip W (standardSlowRegion F.data.h_pos F.data.h_lt_half) id).delta
      (slowChange F.data.h (ChartScales.Q (chart n))
        (ChartScales.Q (BaseChartJets.cellBand (reference l n))) x.1, 0) = _
    rw [viewStrip_delta, viewStrip_delta,
      profileRadius_slowChange (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht hr]
  have hSn := PhysicalGraphBounds.S_ge_one (hchart n)
  have hSm := S_window_le (hchart n) (hnear l n).2
  have hmax : BaseContextAssembly.slowScale (BaseChartJets.cellBand (reference l n)) ≤
      25 * BaseContextAssembly.slowScale (chart n) := by
    unfold BaseContextAssembly.slowScale
    rw [max_eq_right hSn]
    exact max_le (by linarith) hSm
  change BaseContextAssembly.slowScale (BaseChartJets.cellBand (reference l n)) *
    max 1 ((BaseContextAssembly.nativeStrip W _).delta
      (BaseContextAssembly.insertSlow (slowChange F.data.h (ChartScales.Q (chart n))
        (ChartScales.Q (BaseChartJets.cellBand (reference l n))) x.1)))⁻¹ ≤ _
  rw [he]
  exact (mul_le_mul_of_nonneg_right hmax (zero_le_one.trans (le_max_left 1 _))).trans_eq (by
    change (25 * BaseContextAssembly.slowScale (chart n)) * max 1 ((viewStrip W U chart).delta x)⁻¹
        =
      25 * (BaseContextAssembly.slowScale (chart n) * max 1 ((viewStrip W U chart).delta x)⁻¹)
    ring)


-- @@ L1705-1756 verbatim
/-- The copy chart is assembled from the actual dyadic and slot maps.
The only indexing restrictions are the active four-level window and
the chosen common-cover budget; all analytic comparisons are derived. -/
noncomputable def copyChart (hr0 : 0 < r0)
    (hchart : ∀ n, 1 ≤ chart n)
    (hnear : ∀ l n, chart n ≤ BaseChartJets.cellBand (reference l n) + 4 ∧
      BaseChartJets.cellBand (reference l n) ≤ chart n + 4)
    {budget : ℕ} (hi : CommonBaseContext.IndexBounds F.data.h index budget) :
    ActualSignedControl.CopyChart (viewStrip W U chart) (nativeDomain H v a)
      (preparedChart H v a hr0).weight
      (phaseCell H v a sys hdet reference chart index sign) where
  index := reference
  linear l n _ := copyLinear sys hdet (copyLabel H v a reference sign l n) (chart n) (index (chart
      n))
  shift l n k := copyPoint sys hdet (copyLabel H v a reference sign l n) (chart n) (index (chart
      n)) k 0
  maps l n k x hx hi := by
    rw [← copyPoint_affine]
    exact hi
  growthConstant := 25
  linearConstant := slowChangeCost F.data.h +
    25 * CommonCoverClass.bandArgumentCost (TorusAverages.slotChart vr vt hdet)
      (budget + SlotColoring.nativeGap F.data.h)
  growth_one := by norm_num
  linear_one := by
    have h1 := slowChangeCost_one F.data.h
    have h2 := CommonCoverClass.bandArgumentCost_one_le (TorusAverages.slotChart vr vt hdet)
      (budget + SlotColoring.nativeGap F.data.h)
    linarith
  growthDegree := 1
  linearDegree := 1
  growth_bound l n k x hx _ := by
    rw [← copyPoint_affine, pow_one]
    exact copy_growth_le H v a sys hdet U reference chart index sign hchart hnear l n k hx
  linear_bound l n _ := by
    rw [pow_one]
    exact norm_copyLinear_le sys hdet F.data.h_pos.le hi (hchart n)
      (a.large _ (reference l n).property).four_le (hnear l n).1 (hnear l n).2
  weight_eq l n k x hx _ := by
    rw [← copyPoint_affine]
    exact copy_weight_eq H v a sys hdet U reference chart index sign hr0 l n k hx
  ratioLower := 1 / 5
  ratioUpper := 5
  ratio_pos := by norm_num
  ratio_one := by norm_num
  scale_ratio l n := by
    change 1 / 5 ≤ Real.sqrt (max 1 (ChartScales.S (chart n))) /
        Real.sqrt (ChartScales.S (BaseChartJets.cellBand (reference l n))) ∧
      Real.sqrt (max 1 (ChartScales.S (chart n))) /
        Real.sqrt (ChartScales.S (BaseChartJets.cellBand (reference l n))) ≤ 5
    rw [max_eq_right (PhysicalGraphBounds.S_ge_one (hchart n))]
    exact sqrt_S_window (hchart n) (reference l n).val.property.1 (hnear l n).1 (hnear l n).2


-- @@ L1758-1770 verbatim
theorem copyChart_pull (hr0 : 0 < r0) (hchart : ∀ n, 1 ≤ chart n)
    (hnear : ∀ l n, chart n ≤ BaseChartJets.cellBand (reference l n) + 4 ∧
      BaseChartJets.cellBand (reference l n) ≤ chart n + 4)
    {budget : ℕ} (hi : CommonBaseContext.IndexBounds F.data.h index budget)
    {E : Type}
    (f : Label H v a → Native → E) (l : Λ) (n : ℕ) (k : TorusInverse.Frequency) (x : Native) :
    (copyChart H v a sys hdet U reference chart index sign hr0 hchart hnear hi).pull f l n k x =
      f (reference l n) (copyPoint sys hdet (copyLabel H v a reference sign l n)
        (chart n) (index (chart n)) k x) := by
  change f (reference l n)
    (copyLinear sys hdet (copyLabel H v a reference sign l n) (chart n) (index (chart n)) x +
      copyPoint sys hdet (copyLabel H v a reference sign l n) (chart n) (index (chart n)) k 0) = _
  rw [← copyPoint_affine]


-- @@ L1772-1772 verbatim
end PreparedCopies


-- @@ L1774-1774 verbatim
/-! ## Actual periodic phase normals on the native cores -/


-- @@ L1776-1777 verbatim
/-- Cylinder: an abbreviation for `PhysicalResidualBridge.Cylinder`. -/
abbrev Cylinder := PhysicalResidualBridge.Cylinder


-- @@ L1779-1780 verbatim
/-- Radial vector, given by `TorusInverse.vector .radial`. -/
noncomputable def radialVector : Plane := TorusInverse.vector .radial

-- @@ L1781-1782 verbatim
/-- Temporal vector, given by `TorusInverse.vector .temporal`. -/
noncomputable def temporalVector : Plane := TorusInverse.vector .temporal


-- @@ L1784-1787 verbatim
theorem vectors_det : radialVector.1 * temporalVector.2 - radialVector.2 * temporalVector.1 ≠ 0 :=
    by
  dsimp [radialVector, temporalVector, TorusInverse.vector]
  nlinarith [sq_nonneg (Real.sqrt 2 - 1)]


-- @@ L1789-1796 verbatim
/-- Slot linear, bundling `toFun`, `map_add`, `map_smul`, `cont`. -/
noncomputable def slotLinear (g : CommonCoverSolve.Geometry) : Cylinder →L[ℝ] PhaseCalculus.Slot
    where
  toFun x := ((x.1.1, x.1.2.1), (x.2, (g.coordinateLinear x.1.2.2).2))
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  cont := (continuous_fst.fst.prodMk continuous_fst.snd.fst).prodMk
    (continuous_snd.prodMk ((g.coordinateLinear.continuous.comp continuous_fst.snd.snd).snd))


-- @@ L1798-1801 verbatim
/-- Slot coordinates, given by `((x.1.1, x.1.2.1), (x.2, (g.coordinates k x.1.2.2).2))`. -/
noncomputable def slotCoordinates (g : CommonCoverSolve.Geometry) (k : TorusInverse.Frequency)
    (x : Cylinder) : PhaseCalculus.Slot :=
  ((x.1.1, x.1.2.1), (x.2, (g.coordinates k x.1.2.2).2))


-- @@ L1803-1813 verbatim
theorem slotCoordinates_affine (g : CommonCoverSolve.Geometry) (k : TorusInverse.Frequency) :
    slotCoordinates g k = fun x => slotLinear g x + ((0, 0), (0, (g.coordinates k 0).2)) := by
  funext x
  apply Prod.ext
  · simp [slotCoordinates, slotLinear]
  · apply Prod.ext
    · simp [slotCoordinates, slotLinear]
    · change (g.coordinates k x.1.2.2).2 =
        (g.coordinateLinear x.1.2.2).2 + (g.coordinates k 0).2
      rw [g.coordinates_eq_affine]
      exact add_comm _ _


-- @@ L1815-1819 verbatim
theorem slotCoordinates_hasFDerivAt (g : CommonCoverSolve.Geometry) (k : TorusInverse.Frequency) (x
    : Cylinder) :
    HasFDerivAt (slotCoordinates g k) (slotLinear g) x := by
  rw [slotCoordinates_affine]
  exact (slotLinear g).hasFDerivAt.add_const _


-- @@ L1821-1821 verbatim
section ActualPhase


-- @@ L1823-1824 verbatim
variable {D h : ℝ}
  (sys : PartitionedCovariance.SlotSystem D h radialVector temporalVector)


-- @@ L1826-1838 verbatim
theorem slot_coordinate_radial (l : SlotColoring.Label) (gap : ℕ) :
    (slotGeometry sys vectors_det l gap).coordinateLinear radialVector =
      (ChartScales.Lambda ^ gap, 0) := by
  let g := slotGeometry sys vectors_det l gap
  have hb : g.basis (1, 0) = radialVector := by
    rw [slotGeometry_basis]
    simp
  have he : g.basis.symm radialVector = (1, 0) := (g.basis.symm_apply_eq).mpr hb.symm
  change g.basis.symm (CommonCoverSolve.coverPower gap radialVector) = _
  rw [show CommonCoverSolve.coverPower gap radialVector = ChartScales.Lambda ^ gap • radialVector
      from
    CommonBaseContext.coverPower_radial gap, map_smul, he]
  simp


-- @@ L1840-1846 verbatim
theorem slot_coordinates_radial (l : SlotColoring.Label) (gap i : ℕ) (Q : ℝ) (x : Cylinder) :
    slotLinear (slotGeometry sys vectors_det l gap)
      ((PhysicalResidualBridge.commonGraph Q h i).radial x) = PhaseCalculus.eR := by
  change ((1, (0, 0)), (0, ((slotGeometry sys vectors_det l gap).coordinateLinear
    ((_ * _) • radialVector)).2)) = _
  rw [map_smul, slot_coordinate_radial]
  simp [PhaseCalculus.eR]


-- @@ L1848-1851 verbatim
theorem slot_coordinates_angular (g : CommonCoverSolve.Geometry) (x : Cylinder) :
    slotLinear g (PhysicalResidualBridge.ScaledGraph.angular x) = PhaseCalculus.eTheta := by
  change ((0, (0, 0)), (1, (g.coordinateLinear 0).2)) = _
  simp [PhaseCalculus.eTheta]


-- @@ L1853-1857 verbatim
theorem slot_coordinates_axial (g : CommonCoverSolve.Geometry) (Q h : ℝ) (i : ℕ) (x : Cylinder) :
    slotLinear g ((PhysicalResidualBridge.commonGraph Q h i).axial x) =
      Q ^ h • PhaseCalculus.eZ := by
  change ((0, (Q ^ h, 0)), (0, (g.coordinateLinear 0).2)) = _
  simp [PhaseCalculus.eZ]


-- @@ L1859-1865 verbatim
/-- Periodic phase, constructed using `PhaseCalculus.phase`. -/
noncomputable def periodicPhase (l : SlotColoring.Label) (gap : ℕ)
    (epsilon p pz x0 : ℝ) (F G : Slow → ℝ) (x : Cylinder) : ℝ :=
  PhaseCalculus.phase epsilon p pz x0 F G
    ((x.1.1, x.1.2.1), (x.2,
      PeriodicPhaseAssembly.periodicClock (slotGeometry sys vectors_det l gap)
        (clockWindow sys l.1).cutoff x.1.2.2))


-- @@ L1867-1882 verbatim
theorem periodicPhase_germ (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1) (gap : ℕ)
    (epsilon p pz x0 : ℝ) (F G : Slow → ℝ) (k : TorusInverse.Frequency)
    {x : Cylinder}
    (hx : (slotGeometry sys vectors_det l gap).coordinates k x.1.2.2 ∈ (clockWindow sys l.1).core) :
    periodicPhase sys l gap epsilon p pz x0 F G =ᶠ[𝓝 x]
      PhaseCalculus.phase epsilon p pz x0 F G ∘ slotCoordinates (slotGeometry sys vectors_det l
          gap) k := by
  have he := PeriodicPhaseAssembly.periodicClock_germ
    (slotGeometry sys vectors_det l gap) (clockWindow sys l.1)
    (clockWindow_injective sys vectors_det hh hl gap) k
    (z := ((x.1.1, x.1.2.1), x.1.2.2)) hx
  have ht : Tendsto (fun y : Cylinder => ((y.1.1, y.1.2.1), y.1.2.2)) (𝓝 x)
      (𝓝 ((x.1.1, x.1.2.1), x.1.2.2)) :=
    ((continuous_fst.fst.prodMk continuous_fst.snd.fst).prodMk continuous_fst.snd.snd).continuousAt
  filter_upwards [ht.eventually he] with y hy
  simp only [periodicPhase, Function.comp_apply, slotCoordinates, hy]


-- @@ L1884-1898 verbatim
private theorem normal_pullback {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (chi : X → PhaseCalculus.Slot) (epsilon p pz x0 : ℝ) (F G : Slow → ℝ)
    (Vr Vtheta Vz : X → X) {x : X} (hchi : DifferentiableAt ℝ chi x)
    (hF : DifferentiableAt ℝ F (chi x).1) (hG : DifferentiableAt ℝ G (chi x).1)
    (hr : fderiv ℝ chi x (Vr x) = PhaseCalculus.eR)
    (ht : fderiv ℝ chi x (Vtheta x) = PhaseCalculus.eTheta)
    (hz : fderiv ℝ chi x (Vz x) = epsilon • PhaseCalculus.eZ) :
    HarmonicCalculus.phaseNormal (fun y => (chi y).1.1) Vr Vtheta Vz
      (PhaseCalculus.phase epsilon p pz x0 F G ∘ chi) x =
        PhaseCalculus.phaseNormal epsilon p pz x0 F G (chi x) := by
  have hd := fderiv_comp x
    (PrimaryMaterialDefect.differentiableAt_phase epsilon p pz x0 F G (chi x) hF hG) hchi
  ext i
  fin_cases i <;> simp [HarmonicCalculus.phaseNormal, PhaseCalculus.phaseNormal,
    HarmonicCalculus.along, hd, hr, ht, hz]


-- @@ L1900-1926 verbatim
theorem nativePhase_normal (l : SlotColoring.Label) (gap i : ℕ) {Q : ℝ} (hQ : 0 < Q)
    (p pz x0 : ℝ) (F G : Slow → ℝ) (k : TorusInverse.Frequency) (theta : ℝ)
    {x : Cylinder} (hF : DifferentiableAt ℝ F (x.1.1, x.1.2.1))
    (hG : DifferentiableAt ℝ G (x.1.1, x.1.2.1)) :
    HarmonicCalculus.phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial
      (PhaseCalculus.phase (Q ^ h) p pz x0 F G ∘ slotCoordinates (slotGeometry sys vectors_det l
          gap) k) x =
      PhaseCalculus.phaseNormal (Q ^ h) p pz x0 F G
        ((x.1.1, x.1.2.1), (theta, ((slotGeometry sys vectors_det l gap).coordinates k x.1.2.2).2))
            := by
  have hc := slotCoordinates_hasFDerivAt (slotGeometry sys vectors_det l gap) k x
  have he := normal_pullback (slotCoordinates (slotGeometry sys vectors_det l gap) k)
    (Q ^ h) p pz x0 F G (PhysicalResidualBridge.commonGraph Q h i).radial
    PhysicalResidualBridge.ScaledGraph.angular (PhysicalResidualBridge.commonGraph Q h i).axial
    hc.differentiableAt hF hG
    (by rw [hc.fderiv]; exact slot_coordinates_radial sys l gap i Q x)
    (by rw [hc.fderiv]; exact slot_coordinates_angular _ _)
    (by rw [hc.fderiv]; exact slot_coordinates_axial _ _ _ _ _)
  change HarmonicCalculus.phaseNormal (fun y => (slotCoordinates (slotGeometry sys vectors_det l
      gap) k y).1.1)
    _ _ _ _ _ = _
  rw [he]
  rw [PhaseCalculus.phaseNormal_formula _ _ _ _ _ _ _ (Real.rpow_pos_of_pos hQ _).ne' hF hG,
    PhaseCalculus.phaseNormal_formula _ _ _ _ _ _ _ (Real.rpow_pos_of_pos hQ _).ne' hF hG]
  rfl


-- @@ L1928-1940 verbatim
theorem periodicPhase_differentiableAt (l : SlotColoring.Label) (gap : ℕ)
    (epsilon p pz x0 : ℝ) (F G : Slow → ℝ) {x : Cylinder}
    (hF : DifferentiableAt ℝ F (x.1.1, x.1.2.1))
    (hG : DifferentiableAt ℝ G (x.1.1, x.1.2.1)) :
    DifferentiableAt ℝ (periodicPhase sys l gap epsilon p pz x0 F G) x := by
  have hc := (PeriodicPhaseAssembly.periodicClock_contDiff
    (slotGeometry sys vectors_det l gap) (clockWindow sys l.1)).differentiable (by simp)
  have hchi : DifferentiableAt ℝ (fun y : Cylinder =>
      ((y.1.1, y.1.2.1), (y.2, PeriodicPhaseAssembly.periodicClock
        (slotGeometry sys vectors_det l gap) (clockWindow sys l.1).cutoff y.1.2.2))) x :=
    (differentiableAt_fst.fst.prodMk differentiableAt_fst.snd.fst).prodMk
      (differentiableAt_snd.prodMk (hc.differentiableAt.comp x differentiableAt_fst.snd.snd))
  exact (PrimaryMaterialDefect.differentiableAt_phase epsilon p pz x0 F G _ hF hG).comp x hchi


-- @@ L1942-1974 verbatim
theorem periodicPhase_normal_germ (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1)
    (gap i : ℕ) {Q : ℝ} (hQ : 0 < Q) (p pz x0 : ℝ) (F G : Slow → ℝ)
    {S : Set Slow} (hS : IsOpen S) (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S)
    (k : TorusInverse.Frequency) (theta : ℝ) {x : Cylinder}
    (hx : (x.1.1, x.1.2.1) ∈ S)
    (hc : (slotGeometry sys vectors_det l gap).coordinates k x.1.2.2 ∈ (clockWindow sys l.1).core) :
    (fun y => HarmonicCalculus.phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial
      (periodicPhase sys l gap (Q ^ h) p pz x0 F G) y) =ᶠ[𝓝 x]
    fun y => PhaseCalculus.phaseNormal (Q ^ h) p pz x0 F G
      ((y.1.1, y.1.2.1), (theta, ((slotGeometry sys vectors_det l gap).coordinates k y.1.2.2).2))
          := by
  have hp := periodicPhase_germ sys hh hl gap (Q ^ h) p pz x0 F G k hc
  have hr := ParticularWaveAssembly.along_germ hp (PhysicalResidualBridge.commonGraph Q h i).radial
  have ht := ParticularWaveAssembly.along_germ hp PhysicalResidualBridge.ScaledGraph.angular
  have hz := ParticularWaveAssembly.along_germ hp (PhysicalResidualBridge.commonGraph Q h i).axial
  have hm : ∀ᶠ y : Cylinder in 𝓝 x, (y.1.1, y.1.2.1) ∈ S :=
    (hS.preimage (continuous_fst.fst.prodMk continuous_fst.snd.fst)).mem_nhds hx
  filter_upwards [hr, ht, hz, hm] with y hyr hyt hyz hy
  have he : HarmonicCalculus.phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial
      (periodicPhase sys l gap (Q ^ h) p pz x0 F G) y =
      HarmonicCalculus.phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial
      (PhaseCalculus.phase (Q ^ h) p pz x0 F G ∘ slotCoordinates (slotGeometry sys vectors_det l
          gap) k) y := by
    simp only [HarmonicCalculus.phaseNormal, hyr, hyt, hyz]
  exact he.trans (nativePhase_normal sys l gap i hQ p pz x0 F G k theta
    ((hF.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp))
    ((hG.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp)))


-- @@ L1976-2009 verbatim
theorem phase_normal_view_germ (hh : 0 ≤ h) {l : SlotColoring.Label} (hl : 4 ≤ l.1)
    (i gap : ℕ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (K Kr p pz x0 : ℝ) (F G : Slow → ℝ)
    {S : Set Slow} (hS : IsOpen S) (hF : ContDiffOn ℝ ∞ F S) (hG : ContDiffOn ℝ ∞ G S)
    (k : TorusInverse.Frequency) (theta : ℝ) {x : Cylinder} (hxR : 0 < x.1.1)
    (hxS : (slowChange h Q Qr (x.1.1, x.1.2.1)) ∈ S)
    (hc : (slotGeometry sys vectors_det l 0).coordinates k
      (CommonCoverSolve.coverPower gap x.1.2.2) ∈ (clockWindow sys l.1).core) :
    (fun y => HarmonicCalculus.phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h i).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h i).axial
      (fun z => (Kr / K) * periodicPhase sys l 0 (Qr ^ h) p pz x0 F G
        (PhysicalParticularWave.cylinderChange h Q Qr gap z)) y) =ᶠ[𝓝 x]
    fun y => PhysicalParticularWave.normalWeight Q Qr K Kr •
      PhaseCalculus.phaseNormal (Qr ^ h) p pz x0 F G
        (slowChange h Q Qr (y.1.1, y.1.2.1),
          (theta, ((slotGeometry sys vectors_det l 0).coordinates k
            (CommonCoverSolve.coverPower gap y.1.2.2)).2)) := by
  let changeMap := PhysicalParticularWave.cylinderChange h Q Qr gap
  have hn := periodicPhase_normal_germ sys hh hl 0 (i + gap) hQr p pz x0 F G hS hF hG k theta
    (x := changeMap x) hxS hc
  have hp : Tendsto changeMap (𝓝 x) (𝓝 (changeMap x)) := changeMap.continuous.continuousAt
  have hR : ∀ᶠ y : Cylinder in 𝓝 x, 0 < y.1.1 :=
    (isOpen_lt continuous_const continuous_fst.fst).mem_nhds hxR
  have hslow : ∀ᶠ y : Cylinder in 𝓝 x, slowChange h Q Qr (y.1.1, y.1.2.1) ∈ S :=
    (hS.preimage ((slowChange h Q Qr).continuous.comp
      (continuous_fst.fst.prodMk continuous_fst.snd.fst))).mem_nhds hxS
  filter_upwards [hp.eventually hn, hR, hslow] with y hyN hyR hyS
  have hFd := (hF.contDiffAt (hS.mem_nhds hyS)).differentiableAt (by simp)
  have hGd := (hG.contDiffAt (hS.mem_nhds hyS)).differentiableAt (by simp)
  have hd := periodicPhase_differentiableAt sys l 0 (Qr ^ h) p pz x0 F G
    (x := changeMap y) hFd hGd
  exact (PhysicalParticularWave.phaseNormal_chartChange hQ hQr h i gap K Kr hyR hd).trans
    (congrArg (fun N => PhysicalParticularWave.normalWeight Q Qr K Kr • N) hyN)


-- @@ L2011-2011 verbatim
end ActualPhase


-- @@ L2013-2013 verbatim
section ReferenceViews


-- @@ L2015-2017 verbatim
variable {D h : ℝ} {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem D h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)


-- @@ L2019-2022 verbatim
theorem slotGeometry_refine (l : SlotColoring.Label) (gap : ℕ) :
    CopySolveCompatibility.refineGeometry (slotGeometry sys hdet l 0) gap =
      slotGeometry sys hdet l gap := by
  simp [CopySolveCompatibility.refineGeometry, slotGeometry, CommonCoverClass.bandGeometry]


-- @@ L2024-2029 verbatim
theorem slot_coordinates_from_zero (l : SlotColoring.Label) (gap : ℕ)
    (k : TorusInverse.Frequency) (Y : Plane) :
    (slotGeometry sys hdet l 0).coordinates k (CommonCoverSolve.coverPower gap Y) =
      (slotGeometry sys hdet l gap).coordinates k Y := by
  rw [← slotGeometry_refine sys hdet l gap]
  exact (CopySolveCompatibility.coordinates_refine _ _ _ _).symm


-- @@ L2031-2032 verbatim
/-- Cylinder native, given by `((x.1.1, x.1.2.1), x.1.2.2)`. -/
noncomputable def cylinderNative (x : Cylinder) : Native := ((x.1.1, x.1.2.1), x.1.2.2)


-- @@ L2034-2041 verbatim
theorem copyPoint_eq_reference_view (l : SlotColoring.Label) (n common : ℕ)
    (k : TorusInverse.Frequency) (x : Cylinder) :
    copyPoint sys hdet l n common k (cylinderNative x) =
      ParticularWaveBounds.nativePoint (slotGeometry sys hdet l 0) k
        (cylinderNative (PhysicalParticularWave.cylinderChange h (ChartScales.Q n)
          (ChartScales.Q l.1) (ChartScales.nativeIndex h l.1 - common) x)) := by
  apply Prod.ext rfl
  exact (slot_coordinates_from_zero sys hdet l _ k _).symm


-- @@ L2043-2053 verbatim
theorem reference_view_graph (l : SlotColoring.Label) (n common : ℕ)
    (hi : common ≤ ChartScales.nativeIndex h l.1)
    {z : ProblemStatement.SpaceTime} (hz : 0 < z.2 0) :
    PhysicalParticularWave.cylinderChange h (ChartScales.Q n) (ChartScales.Q l.1)
      (ChartScales.nativeIndex h l.1 - common)
        ((PhysicalResidualBridge.commonGraph (ChartScales.Q n) h common).map z) =
      (PhysicalResidualBridge.commonGraph (ChartScales.Q l.1) h (ChartScales.nativeIndex h
          l.1)).map z := by
  rw [PhysicalParticularWave.cylinderChange_graph (ChartScales.Q_pos _) (ChartScales.Q_pos _) h
      common _ hz,
    Nat.add_sub_of_le hi]


-- @@ L2055-2055 verbatim
end ReferenceViews


-- @@ L2057-2057 verbatim
section PreparedNormals


-- @@ L2059-2065 verbatim
variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B N0 : ℕ}
  (sys : PartitionedCovariance.SlotSystem (CoordinateAlgebra.D F.data.h) F.data.h radialVector
      temporalVector)
  (a : PrimaryGeometryAssembly.Prepared H v upper B sys.radius N0)


-- @@ L2067-2072 verbatim
/-- Prepared phase as an element of `Cylinder → ℝ`. -/
noncomputable def preparedPhase (j : Fin 2) (L : Label H v a) : Cylinder → ℝ :=
  let P := PrimaryGeometryAssembly.construction H v a sys.radius_pos j
  periodicPhase sys (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label W L) j) 0
    (ChartScales.epsilon F.data.h (BaseChartJets.cellBand L))
    (P.phase.p L) (P.phase.pz L) (P.phase.x0 L) (P.phase.F L) (P.phase.G L)


-- @@ L2074-2080 verbatim
/-- Prepared view phase as an element of `Cylinder → ℝ`. -/
noncomputable def preparedViewPhase (j : Fin 2) (L : Label H v a) (n common : ℕ) : Cylinder → ℝ :=
  fun x => ((ChartScales.carrier F.data.h (BaseChartJets.cellBand L) : ℝ) /
    (ChartScales.carrier F.data.h n : ℝ)) * preparedPhase H v sys a j L
      (PhysicalParticularWave.cylinderChange F.data.h (ChartScales.Q n)
        (ChartScales.Q (BaseChartJets.cellBand L)) (ChartScales.nativeIndex F.data.h
            (BaseChartJets.cellBand L) - common) x)


-- @@ L2082-2092 verbatim
theorem phaseNormal_pulseCoordinates (j : Fin 2) (L : Label H v a) (x : Native) :
    ActualSignedControl.phaseNormal (PrimaryGeometryAssembly.construction H v a sys.radius_pos j)
        (pulseCoordinates H v a) L x =
      (PrimaryGeometryAssembly.construction H v a sys.radius_pos j).phase.normal L (x.1, x.2.2) :=
          by
  unfold ActualSignedControl.phaseNormal PrimaryCopyBounds.phasePoint pulseCoordinates
  have hL := (PrimaryGeometryAssembly.construction H v a sys.radius_pos j).L_pos L
  change (PrimaryGeometryAssembly.construction H v a sys.radius_pos j).phase.normal L
    (x.1, (PrimaryGeometryAssembly.construction H v a sys.radius_pos j).L L *
      (x.2.2 / (PrimaryGeometryAssembly.construction H v a sys.radius_pos j).L L)) = _
  rw [mul_div_cancel₀ _ hL.ne']


-- @@ L2094-2142 verbatim
/-- The normal germ required by the signed-copy control theorem is an
output for the actual shared prepared phase and physical chart. -/
theorem preparedView_normal_germ (j : Fin 2) (L : Label H v a) (n common : ℕ)
    (k : TorusInverse.Frequency) {x : Cylinder}
    (hcell : copyPoint sys vectors_det
      (PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label W L) j) n common k
      (cylinderNative x) ∈ (nativeDomain H v a).carrier L) :
    (fun y => HarmonicCalculus.phaseNormal PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) F.data.h common).radial
      PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) F.data.h common).axial
      (preparedViewPhase H v sys a j L n common) y) =ᶠ[𝓝 x]
    fun y => PhysicalParticularWave.normalWeight (ChartScales.Q n)
      (ChartScales.Q (BaseChartJets.cellBand L)) (ChartScales.carrier F.data.h n)
      (ChartScales.carrier F.data.h (BaseChartJets.cellBand L)) •
        ActualSignedControl.phaseNormal (PrimaryGeometryAssembly.construction H v a sys.radius_pos
            j)
          (pulseCoordinates H v a) L
          (copyPoint sys vectors_det (PartitionedCovariance.signedLabel
              (PrimaryGeometryAssembly.label W L) j)
            n common k (cylinderNative y)) := by
  let P := PrimaryGeometryAssembly.construction H v a sys.radius_pos j
  let l := PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label W L) j
  let gap := ChartScales.nativeIndex F.data.h (BaseChartJets.cellBand L) - common
  have hl : 4 ≤ l.1 := (a.large _ L.property).four_le
  have hm : slowChange F.data.h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand L))
      (x.1.1, x.1.2.1) ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L := hcell.1.1
  have hr : 0 < x.1.1 := by
    have hp := a.radius_pos L _ hm
    change 0 < PhysicalParticularWave.ratioPower _ _ (1 / 2) * x.1.1 at hp
    exact (mul_pos_iff_of_pos_left (PhysicalParticularWave.ratioPower_pos
      (ChartScales.Q_pos _) (ChartScales.Q_pos _) _)).mp hp
  have hc : (slotGeometry sys vectors_det l 0).coordinates k
      (CommonCoverSolve.coverPower gap x.1.2.2) ∈ (clockWindow sys l.1).core := by
    rw [slot_coordinates_from_zero]
    exact ⟨⟨hcell.2.1.1.le, hcell.2.1.2.le⟩, ⟨hcell.2.2.1.le, hcell.2.2.2.le⟩⟩
  have he := phase_normal_view_germ sys F.data.h_pos.le hl common gap
    (ChartScales.Q_pos n) (ChartScales.Q_pos (BaseChartJets.cellBand L))
    (ChartScales.carrier F.data.h n) (ChartScales.carrier F.data.h (BaseChartJets.cellBand L))
    (P.phase.p L) (P.phase.pz L) (P.phase.x0 L) (P.phase.F L) (P.phase.G L)
    ((PrimaryGeometryAssembly.domain W a.N).isOpen L) (P.baseF.smooth L) (P.baseG.smooth L)
    k (P.phase.theta L) hr hm hc
  filter_upwards [he] with y hy
  apply hy.trans
  congr 1
  rw [phaseNormal_pulseCoordinates]
  change PhaseCalculus.phaseNormal _ _ _ _ _ _ _ = PhaseCalculus.phaseNormal _ _ _ _ _ _ _
  rw [slot_coordinates_from_zero]
  rfl


-- @@ L2144-2144 verbatim
end PreparedNormals


-- @@ L2146-2146 verbatim
/-! ## Active-pair indexing retains the true fields on inactive labels -/


-- @@ L2148-2148 verbatim
section SelectedPairs


-- @@ L2150-2151 verbatim
variable {Λ I E X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L2153-2177 verbatim
/-- Restricting the index set does not change a field or any of its jets.
This transfers a single uniform estimate back to the original labels on
their actual active cells. No values or scales are substituted there. -/
theorem uniformLocalJets_of_selected_pairs (s : StripData X) (P : Λ → ℕ → Prop)
    (e : ℕ → {q : Λ × ℕ // P q.1 q.2}) (he : Surjective e)
    {w : Λ → ℕ → X → ℝ} {f : Λ → ℕ → I → X → E} {K : Λ → ℕ → I → Set X} {alpha : ℝ}
    (hactive : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → P l n)
    (hj : PeriodizedWaveBounds.UniformLocalJets
      (UniformPrimaryWeights.reindexedStrip s (fun q => ((e q).val.2, ())))
      (fun (_ : Unit) q x => w (e q).val.1 (e q).val.2 x) alpha
      (fun (_ : Unit) q i => K (e q).val.1 (e q).val.2 i)
      (fun (_ : Unit) q i => f (e q).val.1 (e q).val.2 i)) :
    PeriodizedWaveBounds.UniformLocalJets s w alpha K f := by
  constructor
  · intro l n i x hx hk
    obtain ⟨q, hq⟩ := he ⟨(l, n), hactive l n i x hx hk⟩
    have h := hj.smooth () q i x hx
    simpa only [hq] using h (by simpa only [hq] using hk)
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hj.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro l n i x hx hk j hjm
    obtain ⟨q, hq⟩ := he ⟨(l, n), hactive l n i x hx hk⟩
    simpa only [majorant, StripData.growth, UniformPrimaryWeights.reindexedStrip, hq] using
      hb () q i x hx (by simpa only [hq] using hk) j hjm


-- @@ L2179-2179 verbatim
end SelectedPairs


-- @@ L2181-2181 verbatim
section ActiveCopies


-- @@ L2183-2193 verbatim
variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)
  {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem (CoordinateAlgebra.D F.data.h) F.data.h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
  (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
  {Λ : Type} (reference : Λ → ℕ → Label H v a) (chart index : ℕ → ℕ)
  (sign : Λ → ℕ → Fin 2)


-- @@ L2195-2199 verbatim
/-- Active pair condition, given by `1 ≤ chart n ∧ chart n ≤ BaseChartJets.cellBand (reference l
n) + 4 ∧ BaseChartJets.cellBand (reference l n) ≤ chart n + 4`. -/
noncomputable def ActivePairCondition (l : Λ) (n : ℕ) : Prop :=
  1 ≤ chart n ∧ chart n ≤ BaseChartJets.cellBand (reference l n) + 4 ∧
    BaseChartJets.cellBand (reference l n) ≤ chart n + 4


-- @@ L2201-2203 verbatim
/-- Active pair: an abbreviation for `{q : Λ × ℕ // ActivePairCondition H v a reference chart
q.1 q.2}`. -/
abbrev ActivePair := {q : Λ × ℕ // ActivePairCondition H v a reference chart q.1 q.2}


-- @@ L2205-2209 verbatim
/-- Active phase cell, given by `{x | ActivePairCondition H v a reference chart l n ∧ x ∈
phaseCell H v a sys hdet reference chart index sign l n k}`. -/
noncomputable def activePhaseCell (l : Λ) (n : ℕ) (k : TorusInverse.Frequency) : Set Native :=
  {x | ActivePairCondition H v a reference chart l n ∧
    x ∈ phaseCell H v a sys hdet reference chart index sign l n k}


-- @@ L2211-2211 verbatim
variable [Countable Λ] [Nonempty (ActivePair H v a reference chart)]


-- @@ L2213-2216 verbatim
/-- Active enumeration, given by `Classical.choose (exists_surjective_nat (ActivePair H v a
reference chart))`. -/
noncomputable def activeEnumeration : ℕ → ActivePair H v a reference chart :=
  Classical.choose (exists_surjective_nat (ActivePair H v a reference chart))


-- @@ L2218-2219 verbatim
theorem activeEnumeration_surjective : Surjective (activeEnumeration H v a reference chart) :=
  Classical.choose_spec (exists_surjective_nat (ActivePair H v a reference chart))


-- @@ L2221-2225 verbatim
/-- Active reference, given by `reference (activeEnumeration H v a reference chart q).val.1
(activeEnumeration H v a reference chart q).val.2`. -/
noncomputable def activeReference (_ : Unit) (q : ℕ) : Label H v a :=
  reference (activeEnumeration H v a reference chart q).val.1
    (activeEnumeration H v a reference chart q).val.2


-- @@ L2227-2229 verbatim
/-- Active chart, given by `chart (activeEnumeration H v a reference chart q).val.2`. -/
noncomputable def activeChart (q : ℕ) : ℕ :=
  chart (activeEnumeration H v a reference chart q).val.2


-- @@ L2231-2235 verbatim
/-- Active sign, given by `sign (activeEnumeration H v a reference chart q).val.1
(activeEnumeration H v a reference chart q).val.2`. -/
noncomputable def activeSign (_ : Unit) (q : ℕ) : Fin 2 :=
  sign (activeEnumeration H v a reference chart q).val.1
    (activeEnumeration H v a reference chart q).val.2


-- @@ L2237-2242 verbatim
theorem active_near (q : ℕ) :
    activeChart H v a reference chart q ≤ BaseChartJets.cellBand (activeReference H v a reference
        chart () q) + 4 ∧
      BaseChartJets.cellBand (activeReference H v a reference chart () q) ≤ activeChart H v a
          reference chart q + 4 :=
  (activeEnumeration H v a reference chart q).property.2


-- @@ L2244-2251 verbatim
/-- Every input of this chart is the original active pair. Its uniform
bounds are valid without any comparison for inactive label-band pairs. -/
noncomputable def activeCopyChart (hr0 : 0 < r0) {budget : ℕ}
    (hi : CommonBaseContext.IndexBounds F.data.h index budget) :=
  copyChart H v a sys hdet U (activeReference H v a reference chart)
    (activeChart H v a reference chart) index (activeSign H v a reference chart sign) hr0
    (fun q => (activeEnumeration H v a reference chart q).property.1)
    (fun _ q => active_near H v a reference chart q) hi


-- @@ L2253-2256 verbatim
theorem active_reindexed_strip :
    viewStrip W U (activeChart H v a reference chart) =
      UniformPrimaryWeights.reindexedStrip (viewStrip W U chart)
        (fun q => ((activeEnumeration H v a reference chart q).val.2, ())) := rfl


-- @@ L2258-2258 verbatim
end ActiveCopies


-- @@ L2260-2260 verbatim
/-! ## The angle coordinate is retained when making harmonic blocks -/


-- @@ L2262-2265 verbatim
/-- Cylinder native linear as an element of `Cylinder →L[ℝ] Native`. -/
noncomputable def cylinderNativeLinear : Cylinder →L[ℝ] Native :=
  (ParticularWaveBounds.liftAssoc Plane).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ PhysicalResidualBridge.Lift ℝ)


-- @@ L2267-2268 verbatim
@[simp] theorem cylinderNativeLinear_apply (x : Cylinder) :
    cylinderNativeLinear x = cylinderNative x := rfl


-- @@ L2270-2275 verbatim
theorem norm_cylinderNativeLinear : ‖cylinderNativeLinear‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(ParticularWaveBounds.liftAssoc Plane) x.1‖ ≤ 1 * ‖x‖
  rw [LinearIsometryEquiv.norm_map, one_mul]
  exact norm_fst_le x


-- @@ L2277-2280 verbatim
/-- Cylinder strip, constructed using `ParticularWaveBounds.reindexStrip`. -/
noncomputable def cylinderStrip (s : StripData Native) : StripData Cylinder :=
  ParticularWaveBounds.reindexStrip (StateReindex.cylinder (ParticularWaveBounds.liftAssoc Plane))
    (HarmonicWaveInteraction.productStrip s)


-- @@ L2282-2309 verbatim
/-- Cylinder copy chart, bundling `index`, `linear`, `shift`, `maps` and the required
compatibility proofs. -/
noncomputable def cylinderCopyChart {Λ I i : Type} {s : StripData Native}
    {V : JetDomain i Native} {weight : i → Native → ℝ} {K : Λ → ℕ → I → Set Native}
    (c : ActualSignedControl.CopyChart s V weight K) :
    ActualSignedControl.CopyChart (cylinderStrip s) V weight
      (fun l n k => cylinderNative ⁻¹' K l n k) where
  index := c.index
  linear l n k := (c.linear l n k).comp cylinderNativeLinear
  shift := c.shift
  maps l n k x hx hk := c.maps l n k (cylinderNative x) hx hk
  growthConstant := c.growthConstant
  linearConstant := c.linearConstant
  growth_one := c.growth_one
  linear_one := c.linear_one
  growthDegree := c.growthDegree
  linearDegree := c.linearDegree
  growth_bound l n k x hx hk := c.growth_bound l n k (cylinderNative x) hx hk
  linear_bound l n k := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) norm_cylinderNativeLinear).trans (c.linear_bound l n
          k))
  weight_eq l n k x hx hk := c.weight_eq l n k (cylinderNative x) hx hk
  ratioLower := c.ratioLower
  ratioUpper := c.ratioUpper
  ratio_pos := c.ratio_pos
  ratio_one := c.ratio_one
  scale_ratio := c.scale_ratio


-- @@ L2311-2315 verbatim
theorem cylinderCopyChart_pull {Λ I i E : Type}
    {s : StripData Native} {V : JetDomain i Native} {weight : i → Native → ℝ}
    {K : Λ → ℕ → I → Set Native} (c : ActualSignedControl.CopyChart s V weight K)
    (f : i → Native → E) (l : Λ) (n : ℕ) (k : I) (x : Cylinder) :
    (cylinderCopyChart c).pull f l n k x = c.pull f l n k (cylinderNative x) := rfl


-- @@ L2317-2317 verbatim
/-! ## The actual cutoffs locate every nonzero native contribution -/


-- @@ L2319-2319 verbatim
section CutoffSupport


-- @@ L2321-2325 verbatim
variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)


-- @@ L2327-2333 verbatim
/-- Native cutoff, constructed using `SquaredPartition.dyadicProfile`. -/
noncomputable def nativeCutoff (L : Label H v a) (x : Native) : ℝ :=
  SquaredPartition.dyadicProfile (SimilarityHomogeneity.chartQ F.data.h x.1) *
    PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L) (PrimaryGeometryAssembly.label W
        L).2 x.1 *
      PartitionedCovariance.cutoff r0 x.2.1 *
        GaussianTailFlat.profile (pulseCoordinates H v a L x).2


-- @@ L2335-2363 verbatim
theorem nativeCutoff_nonzero_mem (hr0 : 0 < r0) (L : Label H v a) {x : Native}
    (ht : 0 < x.1.2.2)
    (hactive : PrimaryTargetBounds.profileRadius F.data.h x.1 ∈
      Ioo (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W))
    (hx : nativeCutoff H v a L x ≠ 0) : x ∈ (nativeDomain H v a).carrier L := by
  simp only [nativeCutoff, mul_ne_zero_iff] at hx
  have hq : SimilarityHomogeneity.chartQ F.data.h x.1 ∈ Ioo (1 / 2 : ℝ) 2 := by
    rw [← SquaredPartition.dyadicProfile_support]
    exact hx.1.1.1
  have hs : x.1 ∈ (PrimaryGeometryAssembly.domain W a.N).carrier L :=
    PrimaryGeometryAssembly.native_support_in_carrier W L ⟨subset_closure hx.1.1.2, ht⟩
  have hu : x.2.1 ∈ Ioo (-r0) r0 := by
    rw [← PartitionedCovariance.cutoff_support hr0]
    exact hx.1.2
  have hgauss : |(pulseCoordinates H v a L x).2 - 1 / 2| < 1 / 3 := by
    by_contra hn
    exact hx.2 (GaussianTailFlat.profile_zero (le_of_not_gt hn))
  have hdiv : 0 < x.2.2 / ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L) ∧
      x.2.2 / ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L) < 1 := by
    dsimp only [pulseCoordinates] at hgauss
    constructor <;> linarith [(abs_lt.mp hgauss).1, (abs_lt.mp hgauss).2]
  have hL : 0 < ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L) :=
    div_pos (mul_pos (by norm_num) hr0) (ChartScales.timeCoefficient_pos _ _)
  have hv : x.2.2 ∈ Ioo 0 (ChartScales.slotLength r0 F.data.h (BaseChartJets.cellBand L)) := by
    exact ⟨by simpa only [zero_mul] using (lt_div_iff₀ hL).mp hdiv.1,
      (div_lt_one hL).mp hdiv.2⟩
  refine ⟨⟨hs, ?_⟩, hu, hv⟩
  apply (BaseContextAssembly.nativeStrip_mem W _ _).mpr
  exact ⟨⟨ht, hq⟩, hactive⟩


-- @@ L2365-2378 verbatim
theorem nativeCutoff_zero_germ_outside_q (L : Label H v a) {x : Native}
    (ht : 0 < x.1.2.2)
    (hq : SimilarityHomogeneity.chartQ F.data.h x.1 ∉ Icc (1 / 2 : ℝ) 2) :
    nativeCutoff H v a L =ᶠ[𝓝 x] fun _ => 0 := by
  have he : SquaredPartition.dyadicProfile =ᶠ[𝓝 (SimilarityHomogeneity.chartQ F.data.h x.1)] fun _
      => 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (by
        simpa only [SquaredPartition.dyadicProfile_tsupport] using hq)
  have hc : ContinuousAt (fun y : Native => SimilarityHomogeneity.chartQ F.data.h y.1) x := by
    exact ((SimilarityCoordinates.coordinateQ_smooth
      (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half]) ht).continuousAt).comp
        (continuousAt_fst.snd.snd.prodMk continuousAt_fst.snd.fst)
  filter_upwards [hc.eventually he] with y hy
  simp only [nativeCutoff, hy, zero_mul]


-- @@ L2380-2389 verbatim
theorem nativeCutoff_zero_germ_outside_cell (L : Label H v a) {x : Native}
    (ht : 0 < x.1.2.2) (hx : x.1 ∉ (PrimaryGeometryAssembly.domain W a.N).carrier L) :
    nativeCutoff H v a L =ᶠ[𝓝 x] fun _ => 0 := by
  have hs : x.1 ∉ tsupport (PrimaryRepresentatives.nativeMask
      (BaseChartJets.cellBand L) (PrimaryGeometryAssembly.label W L).2) := by
    intro hs
    exact hx (PrimaryGeometryAssembly.native_support_in_carrier W L ⟨hs, ht⟩)
  have he := notMem_tsupport_iff_eventuallyEq.mp hs
  filter_upwards [continuousAt_fst.eventually he] with y hy
  simp only [nativeCutoff, hy, Pi.zero_apply, mul_zero, zero_mul]


-- @@ L2391-2411 verbatim
theorem copy_cutoff_mem_phaseCell (hr0 : 0 < r0)
    {vr vt : Plane}
    (sys : PartitionedCovariance.SlotSystem (CoordinateAlgebra.D F.data.h) F.data.h vr vt)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
    {Λ : Type} (reference : Λ → ℕ → Label H v a) (chart index : ℕ → ℕ)
    (sign : Λ → ℕ → Fin 2) (l : Λ) (n : ℕ) (k : TorusInverse.Frequency)
    {x : Native} (hx : x ∈ (viewStrip W U chart).domain)
    (hn : nativeCutoff H v a (reference l n)
      (copyPoint sys hdet (copyLabel H v a reference sign l n) (chart n) (index (chart n)) k x) ≠
          0) :
    x ∈ phaseCell H v a sys hdet reference chart index sign l n k := by
  have hp := (viewStrip_mem W U chart x).mp hx
  have ht := BaseContextAssembly.nativeStrip_time W U hp
  have hr := BaseContextAssembly.nativeStrip_radius W U hp
  have ha := ((BaseContextAssembly.nativeStrip_mem W U _).mp hp).2
  apply nativeCutoff_nonzero_mem H v a hr0 (reference l n) _ _ hn
  · exact slowChange_time (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht
  · change PrimaryTargetBounds.profileRadius F.data.h (slowChange F.data.h _ _ x.1) ∈ _
    rw [profileRadius_slowChange (ChartScales.Q_pos _) (ChartScales.Q_pos _) ht hr]
    exact ha


-- @@ L2413-2413 verbatim
end CutoffSupport


-- @@ L2415-2415 verbatim
/-! ## The solver's `(R,(T,Z))` parameter ordering -/


-- @@ L2417-2428 verbatim
/-- Swap parameter, bundling `toFun`, `invFun`, `left_inv`, `right_inv` and the required
compatibility proofs. -/
noncomputable def swapParameter : Slow ≃ₗᵢ[ℝ] Slow where
  toFun x := (x.1, (x.2.2, x.2.1))
  invFun x := (x.1, (x.2.2, x.2.1))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change ‖(x.1, (x.2.2, x.2.1))‖ = ‖x‖
    simp only [Prod.norm_def, max_comm ‖x.2.1‖ ‖x.2.2‖]


-- @@ L2430-2434 verbatim
/-- Parameter linear, constructed using
`swapParameter.toContinuousLinearEquiv.toContinuousLinearMap.comp`. -/
noncomputable def parameterLinear (h Q Qr : ℝ) : Slow →L[ℝ] Slow :=
  swapParameter.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((slowChange h Q Qr).comp swapParameter.toContinuousLinearEquiv.toContinuousLinearMap)


-- @@ L2436-2437 verbatim
@[simp] theorem parameterLinear_apply (h Q Qr : ℝ) (x : Slow) :
    parameterLinear h Q Qr x = PhysicalParticularWave.parameterChange h Q Qr x := rfl


-- @@ L2439-2451 verbatim
theorem norm_parameterLinear_le (h : ℝ) {n m : ℕ}
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    ‖parameterLinear h (ChartScales.Q n) (ChartScales.Q m)‖ ≤ slowChangeCost h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (slowChangeCost_one h))
  intro x
  change ‖swapParameter (slowChange h (ChartScales.Q n) (ChartScales.Q m) (swapParameter x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖slowChange h (ChartScales.Q n) (ChartScales.Q m)‖ * ‖swapParameter x‖ :=
      (slowChange h _ _).le_opNorm _
    _ ≤ slowChangeCost h * ‖x‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (norm_slowChange_le h hnm hmn) (norm_nonneg _)


-- @@ L2453-2453 verbatim
end NavierStokes.ActualSignedGeometry
