import Mathlib
import Submission.MorsePerturb


-- @@ L4-9 verbatim
/-!
# Two-dimensional finite-chart Morse genericity

This module is the genericity layer between the localized ambient tilts in
`MorsePerturb` and the exact quadratic event charts in `MorsePosition`.
-/


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-13 verbatim
open Set Function Metric

-- @@ L14-14 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L16-16 verbatim
namespace Submission


-- @@ L18-18 verbatim
variable {n : ℕ}


-- @@ L20-20 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L21-21 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L23-23 verbatim
/-! ## One chart: a regular gradient value is a nondegenerate tilted critical set -/


-- @@ L25-27 verbatim
/-- Subtract the linear height with gradient `q`. -/
def chartLinearTilt (f : E₂ → ℝ) (q : E₂) (u : E₂) : ℝ :=
  f u - (innerSL ℝ q) u


-- @@ L29-31 verbatim
theorem contDiff_chartLinearTilt {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f) (q : E₂) :
    ContDiff ℝ ∞ (chartLinearTilt f q) :=
  hf.sub (innerSL ℝ q).contDiff


-- @@ L33-36 verbatim
theorem fderiv_chartLinearTilt {f : E₂ → ℝ} (hf : Differentiable ℝ f)
    (q u : E₂) :
    fderiv ℝ (chartLinearTilt f q) u = fderiv ℝ f u - innerSL ℝ q := by
  exact ((hf u).hasFDerivAt.sub (innerSL ℝ q).hasFDerivAt).fderiv


-- @@ L38-42 verbatim
theorem chartGradient_chartLinearTilt {f : E₂ → ℝ} (hf : Differentiable ℝ f)
    (q u : E₂) :
    chartGradient (chartLinearTilt f q) u = chartGradient f u - q := by
  rw [chartGradient, chartGradient, fderiv_chartLinearTilt hf]
  simp [scalarAdjointCLM, ContinuousLinearMap.adjoint_innerSL_apply]


-- @@ L44-53 verbatim
theorem fderiv_chartGradient_chartLinearTilt {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (q u : E₂) :
    fderiv ℝ (chartGradient (chartLinearTilt f q)) u =
      fderiv ℝ (chartGradient f) u := by
  have hfun : chartGradient (chartLinearTilt f q) =
      fun z => chartGradient f z - q := by
    funext z
    exact chartGradient_chartLinearTilt (hf.differentiable (by simp)) q z
  rw [hfun]
  exact (((contDiff_chartGradient hf).differentiable (by simp) u).hasFDerivAt.sub_const q).fderiv


-- @@ L55-56 verbatim
/-- Critical points are zeros of the Euclidean gradient. -/
def ChartCritical (f : E₂ → ℝ) : Set E₂ := {u | chartGradient f u = 0}


-- @@ L58-64 verbatim
theorem chartCritical_linearTilt {f : E₂ → ℝ} (hf : Differentiable ℝ f)
    (q : E₂) :
    ChartCritical (chartLinearTilt f q) = chartGradient f ⁻¹' ({q} : Set E₂) := by
  ext u
  rw [mem_preimage, mem_singleton_iff]
  simp only [ChartCritical, mem_setOf_eq, chartGradient_chartLinearTilt hf]
  exact sub_eq_zero


-- @@ L66-70 verbatim
/-- Nondegeneracy expressed without choosing a Hessian matrix: the derivative of
the gradient is an isomorphism.  In dimension two, surjectivity and bijectivity
are equivalent. -/
def NondegenerateCriticalAt (f : E₂ → ℝ) (u : E₂) : Prop :=
  chartGradient f u = 0 ∧ Bijective (fderiv ℝ (chartGradient f) u)


-- @@ L72-80 verbatim
/-- Output of the Sard tilt on a compact chart core. -/
structure GenericChartTilt (f : E₂ → ℝ) (K : Set E₂) where
  q : E₂
  tilted : E₂ → ℝ := chartLinearTilt f q
  tilted_eq : tilted = chartLinearTilt f q
  q_regular : IsRegularValue (chartGradient f) q
  critical_finite : (ChartCritical tilted ∩ K).Finite
  critical_nondegenerate : ∀ u ∈ ChartCritical tilted ∩ K,
    NondegenerateCriticalAt tilted u


-- @@ L82-109 verbatim
/-- Sard's theorem gives an arbitrarily small linear tilt which has finitely many
critical points on a compact chart core, all nondegenerate. -/
theorem exists_genericChartTilt {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set E₂} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : GenericChartTilt f K, T.q ∈ ball (0 : E₂) ε := by
  obtain ⟨q, hqsmall, hqreg⟩ := exists_small_regular_chartGradient hf hε
  refine ⟨{
    q := q
    tilted := chartLinearTilt f q
    tilted_eq := rfl
    q_regular := hqreg
    critical_finite := ?_
    critical_nondegenerate := ?_ }, hqsmall⟩
  · rw [chartCritical_linearTilt (hf.differentiable (by simp))]
    exact finite_regularValue_preimage_inter_compact
      (contDiff_chartGradient hf) hqreg hK
  · intro u hu
    have hgrad : chartGradient f u = q := by
      have hmem : u ∈ chartGradient f ⁻¹' ({q} : Set E₂) := by
        rw [← chartCritical_linearTilt (hf.differentiable (by simp))]
        exact hu.1
      simpa using hmem
    have hsurj : Surjective (fderiv ℝ (chartGradient f) u) := hqreg u hgrad
    have hinj : Injective (fderiv ℝ (chartGradient f) u) :=
      LinearMap.injective_iff_surjective.mpr hsurj
    refine ⟨hu.1, ?_⟩
    rw [fderiv_chartGradient_chartLinearTilt hf]
    exact ⟨hinj, hsurj⟩


-- @@ L111-111 verbatim
/-! ## Finite simultaneous charts and critical-value separation -/


-- @@ L113-165 verbatim
/-- Finitely many real numbers can be moved by arbitrarily small independent
amounts so that they become pairwise distinct.  The proof chooses the new values
recursively inside open intervals while avoiding the finite set already used. -/
theorem exists_close_injective_on_finset {α : Type*} (s : Finset α)
    (v : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : α → ℝ, (∀ a ∈ s, |w a - v a| < ε) ∧ Set.InjOn w (s : Set α) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨v, ?_, ?_⟩
      · simp
      · intro a ha
        simp at ha
  | @insert a s ha ih =>
      obtain ⟨w, hwclose, hwinj⟩ := ih
      let used : Finset ℝ := s.image w
      have hinterval : (Ioo (v a - ε) (v a + ε)).Infinite :=
        Set.Ioo_infinite (by linarith)
      obtain ⟨y, hy, hyused⟩ := hinterval.exists_notMem_finset used
      let w' : α → ℝ := Function.update w a y
      refine ⟨w', ?_, ?_⟩
      · intro b hb
        rcases Finset.mem_insert.mp hb with hba | hb
        · subst b
          simp only [w', Function.update_self]
          exact (abs_lt).2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
        · have hba : b ≠ a := fun h => ha (h ▸ hb)
          simpa [w', hba] using hwclose b hb
      · intro b hb c hc hbc
        have hb' := Finset.mem_insert.mp hb
        have hc' := Finset.mem_insert.mp hc
        rcases hb' with hbaEq | hbS
        · subst b
          rcases hc' with hcaEq | hcS
          · exact hcaEq.symm
          · exfalso
            have hca : c ≠ a := fun h => ha (h ▸ hcS)
            have hbc' : y = w c := by simpa [w', hca] using hbc
            apply hyused
            change y ∈ s.image w
            exact Finset.mem_image.mpr ⟨c, hcS, hbc'.symm⟩
        · rcases hc' with hcaEq | hcS
          · exfalso
            subst c
            have hba : b ≠ a := fun h => ha (h ▸ hbS)
            have hbc' : w b = y := by simpa [w', hba] using hbc
            apply hyused
            change y ∈ s.image w
            exact Finset.mem_image.mpr ⟨b, hbS, hbc'⟩
          · have hba : b ≠ a := fun h => ha (h ▸ hbS)
            have hca : c ≠ a := fun h => ha (h ▸ hcS)
            have hbc' : w b = w c := by simpa [w', hba, hca] using hbc
            exact hwinj hbS hcS hbc'


-- @@ L167-167 verbatim
/-! ## Installation in an ambient IFT coordinate chart -/


-- @@ L169-192 verbatim
/-- A local IFT chart of the two-dimensional zero surface whose two free
coordinates are ambient linear coordinates.

The parametrization is represented by a globally smooth map only to avoid
partial functions in downstream formulas.  The fiber and coordinate
identities are intentionally asserted only on `domain`, a neighborhood of the
origin.  Requiring them for every `u : E₂` is incompatible with the spatial
boundedness of a cobordism: two globally recoverable free coordinates would
force its zero surface to be spatially unbounded.

`liftCovector` extends a chart covector to the ambient space; `lift_param` is
the local exact coordinate identity that makes an ambient affine tilt equal
the chart-linear tilt. -/
structure IFTSurfaceChart (C : FramedLevelCobordism n) where
  center : E'
  domain : Set E₂
  domain_mem_nhds : domain ∈ 𝓝 (0 : E₂)
  param : E₂ → E'
  param_smooth : ContDiff ℝ ∞ param
  param_zero : param 0 = center
  param_fiber : ∀ u, u ∈ domain → C.G (param u) = 0
  liftCovector : E₂ →ₗ[ℝ] (E' →L[ℝ] ℝ)
  lift_param : ∀ q u, u ∈ domain →
    liftCovector q (param u - center) = (innerSL ℝ q) u


-- @@ L194-194 verbatim
namespace IFTSurfaceChart


-- @@ L196-198 verbatim
/-- Time restricted to the surface chart. -/
def time {C : FramedLevelCobordism n} (P : IFTSurfaceChart C) (u : E₂) : ℝ :=
  tcoord (P.param u)


-- @@ L200-202 verbatim
theorem contDiff_time {C : FramedLevelCobordism n} (P : IFTSurfaceChart C) :
    ContDiff ℝ ∞ P.time :=
  (EuclideanSpace.proj (Fin.last (n + 1)) (𝕜 := ℝ)).contDiff.comp P.param_smooth


-- @@ L204-208 verbatim
/-- The ambient amplitude which installs the chart tilt.  The minus sign matches
`chartLinearTilt f q = f - ⟪q,u⟫`. -/
def ambientTiltRaw {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    {K U : Set E'} (χ : SmoothCutoff K U) (q : E₂) : E' → ℝ :=
  χ.localize (SmoothCutoff.affineJet (-P.liftCovector q) P.center 0)


-- @@ L210-213 verbatim
theorem contDiff_ambientTiltRaw {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) {K U : Set E'} (χ : SmoothCutoff K U) (q : E₂) :
    ContDiff ℝ ∞ (P.ambientTiltRaw χ q) :=
  χ.contDiff_localize (SmoothCutoff.contDiff_affineJet _ _ _)


-- @@ L215-229 verbatim
/-- On the cutoff core, the localized ambient affine tilt is literally the
chart-linear tilt selected by Sard. -/
theorem verticalShift_time_eq_chartLinearTilt
    {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    {K U : Set E'} (χ : SmoothCutoff K U) (q : E₂) {u : E₂}
    (hud : u ∈ P.domain) (hu : P.param u ∈ K) :
    tcoord (verticalShift (P.ambientTiltRaw χ q) (P.param u)) =
      chartLinearTilt P.time q u := by
  rw [tcoord_verticalShift]
  have hamp : P.ambientTiltRaw χ q (P.param u) = -(innerSL ℝ q) u := by
    rw [ambientTiltRaw, χ.localize_affineJet_eq _ _ _ hu]
    change -(P.liftCovector q (P.param u - P.center)) + 0 = -((innerSL ℝ q) u)
    rw [P.lift_param q u hud, add_zero]
  rw [hamp]
  rw [chartLinearTilt, time, sub_eq_add_neg]


-- @@ L231-236 verbatim
/-- A single localized ambient affine jet installs both ingredients used by the
finite genericity construction: the Sard linear tilt and an independent
constant displacement of the critical time. -/
def ambientEventRaw {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    {K U : Set E'} (χ : SmoothCutoff K U) (q : E₂) (c : ℝ) : E' → ℝ :=
  χ.localize (SmoothCutoff.affineJet (-P.liftCovector q) P.center c)


-- @@ L238-242 verbatim
theorem contDiff_ambientEventRaw {C : FramedLevelCobordism n}
    (P : IFTSurfaceChart C) {K U : Set E'} (χ : SmoothCutoff K U)
    (q : E₂) (c : ℝ) :
    ContDiff ℝ ∞ (P.ambientEventRaw χ q c) :=
  χ.contDiff_localize (SmoothCutoff.contDiff_affineJet _ _ _)


-- @@ L244-261 verbatim
/-- On the cutoff core, the ambient event jet realizes exactly the separated
local time function used below. -/
theorem verticalShift_time_eq_chartLinearTilt_add_const
    {C : FramedLevelCobordism n} (P : IFTSurfaceChart C)
    {K U : Set E'} (χ : SmoothCutoff K U) (q : E₂) (c : ℝ) {u : E₂}
    (hud : u ∈ P.domain) (hu : P.param u ∈ K) :
    tcoord (verticalShift (P.ambientEventRaw χ q c) (P.param u)) =
      chartLinearTilt P.time q u + c := by
  rw [tcoord_verticalShift]
  have hamp : P.ambientEventRaw χ q c (P.param u) =
      -(innerSL ℝ q) u + c := by
    rw [ambientEventRaw, χ.localize_affineJet_eq _ _ _ hu]
    change -(P.liftCovector q (P.param u - P.center)) + c =
      -((innerSL ℝ q) u) + c
    rw [P.lift_param q u hud]
  rw [hamp]
  rw [chartLinearTilt, time, sub_eq_add_neg]
  ring


-- @@ L263-263 verbatim
end IFTSurfaceChart


-- @@ L265-272 verbatim
/-- A finite family of two-dimensional IFT chart functions and compact cores.
The ambient IFT construction is responsible for supplying these data; all
genericity work below is internal to the charts. -/
structure FiniteIFTChartFamily (ι : Type*) [Fintype ι] where
  time : ι → E₂ → ℝ
  core : ι → Set E₂
  smooth : ∀ i, ContDiff ℝ ∞ (time i)
  compact_core : ∀ i, IsCompact (core i)


-- @@ L274-282 verbatim
/-- A finite family of actual IFT charts on one cobordism.  This is the ambient
input form of `FiniteIFTChartFamily`; forgetting the parametrizations leaves the
scalar time functions to which the Sard argument applies. -/
structure FiniteIFTSurfaceChartFamily (C : FramedLevelCobordism n)
    (ι : Type*) [Fintype ι] where
  chart : ι → IFTSurfaceChart C
  core : ι → Set E₂
  compact_core : ∀ i, IsCompact (core i)
  core_subset_domain : ∀ i, core i ⊆ (chart i).domain


-- @@ L284-290 verbatim
def FiniteIFTSurfaceChartFamily.toFiniteIFTChartFamily
    {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
    (B : FiniteIFTSurfaceChartFamily C ι) : FiniteIFTChartFamily ι where
  time i := (B.chart i).time
  core := B.core
  smooth i := (B.chart i).contDiff_time
  compact_core := B.compact_core


-- @@ L292-309 verbatim
/-- Result of simultaneous Sard tilts on all charts, followed by independent
small shifts of the now finite critical values. -/
structure GenericFiniteIFTAtlas {ι : Type*} [Fintype ι]
    (A : FiniteIFTChartFamily ι) where
  tilt : ∀ i, GenericChartTilt (A.time i) (A.core i)
  gradient_bound : ℝ
  q_small : ∀ i, (tilt i).q ∈ ball (0 : E₂) gradient_bound
  criticalPoints : Finset (Σ _ : ι, E₂)
  criticalPoints_spec : ∀ p : Σ _ : ι, E₂,
    p ∈ criticalPoints ↔ p.2 ∈ ChartCritical (tilt p.1).tilted ∩ A.core p.1
  valueShift : (Σ _ : ι, E₂) → ℝ
  valueShift_bound : ℝ
  valueShift_small : ∀ p ∈ criticalPoints, |valueShift p| < valueShift_bound
  shiftedValue_injective : Set.InjOn
    (fun p : Σ _ : ι, E₂ => (tilt p.1).tilted p.2 + valueShift p)
    (criticalPoints : Set (Σ _ : ι, E₂))
  nondegenerate : ∀ p ∈ criticalPoints,
    NondegenerateCriticalAt (tilt p.1).tilted p.2


-- @@ L311-349 verbatim
/-- The finite-chart genericity theorem.  Every chart tilt is chosen by the
two-dimensional Sard theorem, compactness makes the total critical locus finite,
and a second arbitrarily small finite choice separates all critical times. -/
theorem exists_genericFiniteIFTAtlas {ι : Type*} [Fintype ι]
    (A : FiniteIFTChartFamily ι) {εgrad εtime : ℝ}
    (hεgrad : 0 < εgrad) (hεtime : 0 < εtime) :
    Nonempty (GenericFiniteIFTAtlas A) := by
  classical
  have hex : ∀ i, ∃ T : GenericChartTilt (A.time i) (A.core i),
      T.q ∈ ball (0 : E₂) εgrad := fun i =>
    exists_genericChartTilt (A.smooth i) (A.compact_core i) hεgrad
  choose T hT using hex
  let crit : Finset (Σ i, E₂) :=
    Finset.univ.sigma fun i => (T i).critical_finite.toFinset
  have hcrit (p : Σ i, E₂) :
      p ∈ crit ↔ p.2 ∈ ChartCritical (T p.1).tilted ∩ A.core p.1 := by
    simp [crit]
  let baseValue : (Σ i, E₂) → ℝ := fun p => (T p.1).tilted p.2
  obtain ⟨separated, hclose, hinj⟩ :=
    exists_close_injective_on_finset crit baseValue hεtime
  let shift : (Σ i, E₂) → ℝ := fun p => separated p - baseValue p
  refine ⟨{
    tilt := T
    gradient_bound := εgrad
    q_small := hT
    criticalPoints := crit
    criticalPoints_spec := hcrit
    valueShift := shift
    valueShift_bound := εtime
    valueShift_small := ?_
    shiftedValue_injective := ?_
    nondegenerate := ?_ }⟩
  · intro p hp
    exact hclose p hp
  · intro p hp q hq hpq
    apply hinj hp hq
    simpa [shift, baseValue] using hpq
  · intro p hp
    exact (T p.1).critical_nondegenerate p.2 ((hcrit p).mp hp)


-- @@ L351-355 verbatim
/-- The same pre-Morse package, specialized to genuine surface charts on a
fixed cobordism. -/
abbrev GenericFiniteIFTSurfaceAtlas {C : FramedLevelCobordism n}
    {ι : Type*} [Fintype ι] (B : FiniteIFTSurfaceChartFamily C ι) :=
  GenericFiniteIFTAtlas B.toFiniteIFTChartFamily


-- @@ L357-361 verbatim
theorem exists_genericFiniteIFTSurfaceAtlas {C : FramedLevelCobordism n}
    {ι : Type*} [Fintype ι] (B : FiniteIFTSurfaceChartFamily C ι)
    {εgrad εtime : ℝ} (hεgrad : 0 < εgrad) (hεtime : 0 < εtime) :
    Nonempty (GenericFiniteIFTSurfaceAtlas B) :=
  exists_genericFiniteIFTAtlas B.toFiniteIFTChartFamily hεgrad hεtime


-- @@ L363-363 verbatim
/-! ## Local separated event times -/


-- @@ L365-370 verbatim
theorem chartGradient_add_const {f : E₂ → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (u : E₂) :
    chartGradient (fun z => f z + c) u = chartGradient f u := by
  have hfd : fderiv ℝ (fun z => f z + c) u = fderiv ℝ f u :=
    ((hf u).hasFDerivAt.add_const c).fderiv
  rw [chartGradient, chartGradient, hfd]


-- @@ L372-379 verbatim
theorem fderiv_chartGradient_add_const {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : ℝ) (u : E₂) :
    fderiv ℝ (chartGradient (fun z => f z + c)) u =
      fderiv ℝ (chartGradient f) u := by
  have hfun : chartGradient (fun z => f z + c) = chartGradient f := by
    funext z
    exact chartGradient_add_const (hf.differentiable (by simp)) c z
  rw [hfun]


-- @@ L381-381 verbatim
namespace GenericFiniteIFTAtlas


-- @@ L383-390 verbatim
/-- The local time function around a critical point after its independent
constant shift.  When the ambient construction chooses its cutoff core inside
the corresponding IFT neighborhood, this is precisely the function installed
there by `IFTSurfaceChart.ambientEventRaw`. -/
def localSeparatedTime {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A)
    (p : Σ _ : ι, E₂) (u : E₂) : ℝ :=
  (G.tilt p.1).tilted u + G.valueShift p


-- @@ L392-411 verbatim
theorem localSeparatedTime_nondegenerate {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    NondegenerateCriticalAt (G.localSeparatedTime p) p.2 := by
  have hnon := G.nondegenerate p hp
  rw [(G.tilt p.1).tilted_eq] at hnon
  refine ⟨?_, ?_⟩
  · change chartGradient
      (fun u => (G.tilt p.1).tilted u + G.valueShift p) p.2 = 0
    rw [(G.tilt p.1).tilted_eq]
    rw [chartGradient_add_const
      ((contDiff_chartLinearTilt (A.smooth p.1) (G.tilt p.1).q).differentiable
        (by simp))]
    exact hnon.1
  · change Bijective (fderiv ℝ
      (chartGradient (fun u => (G.tilt p.1).tilted u + G.valueShift p)) p.2)
    rw [(G.tilt p.1).tilted_eq]
    rw [fderiv_chartGradient_add_const
      (contDiff_chartLinearTilt (A.smooth p.1) (G.tilt p.1).q)]
    exact hnon.2


-- @@ L413-417 verbatim
theorem localSeparatedTime_value {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A)
    (p : Σ _ : ι, E₂) :
    G.localSeparatedTime p p.2 =
      (G.tilt p.1).tilted p.2 + G.valueShift p := rfl


-- @@ L419-435 verbatim
/-- The finite set recorded by the atlas is exactly the critical locus of the
separated local functions on their compact chart cores. -/
theorem mem_criticalPoints_iff_localSeparatedTime_critical
    {ι : Type*} [Fintype ι] {A : FiniteIFTChartFamily ι}
    (G : GenericFiniteIFTAtlas A) (p : Σ _ : ι, E₂) :
    p ∈ G.criticalPoints ↔
      p.2 ∈ ChartCritical (G.localSeparatedTime p) ∩ A.core p.1 := by
  rw [G.criticalPoints_spec]
  have hsmooth : ContDiff ℝ ∞ (G.tilt p.1).tilted := by
    rw [(G.tilt p.1).tilted_eq]
    exact contDiff_chartLinearTilt (A.smooth p.1) (G.tilt p.1).q
  change
    (chartGradient (G.tilt p.1).tilted p.2 = 0 ∧ p.2 ∈ A.core p.1) ↔
      (chartGradient
        (fun u => (G.tilt p.1).tilted u + G.valueShift p) p.2 = 0 ∧
        p.2 ∈ A.core p.1)
  rw [chartGradient_add_const (hsmooth.differentiable (by simp))]


-- @@ L437-443 verbatim
/-- The actual local critical values are pairwise distinct. -/
theorem localCriticalValues_injective {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A) :
    Set.InjOn (fun p : Σ _ : ι, E₂ => G.localSeparatedTime p p.2)
      (G.criticalPoints : Set (Σ _ : ι, E₂)) := by
  intro p hp q hq hpq
  exact G.shiftedValue_injective hp hq hpq


-- @@ L445-445 verbatim
end GenericFiniteIFTAtlas


-- @@ L447-447 verbatim
namespace GenericFiniteIFTSurfaceAtlas


-- @@ L449-468 verbatim
/-- Every separated local event function in the finite surface atlas is
literally realized by one localized ambient affine vertical shift. -/
theorem localSeparatedTime_realized
    {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
    {B : FiniteIFTSurfaceChartFamily C ι}
    (G : GenericFiniteIFTSurfaceAtlas B)
    {K U : ι → Set E'} (χ : ∀ i, SmoothCutoff (K i) (U i))
    (hcore : ∀ i u, u ∈ B.core i → (B.chart i).param u ∈ K i)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    tcoord (verticalShift
      ((B.chart p.1).ambientEventRaw (χ p.1) (G.tilt p.1).q (G.valueShift p))
      ((B.chart p.1).param p.2)) = G.localSeparatedTime p p.2 := by
  have hpCore : p.2 ∈ B.core p.1 := by
    have h := (G.criticalPoints_spec p).mp hp
    exact h.2
  rw [(B.chart p.1).verticalShift_time_eq_chartLinearTilt_add_const
    (χ p.1) (G.tilt p.1).q (G.valueShift p)
      (B.core_subset_domain p.1 hpCore) (hcore p.1 p.2 hpCore)]
  rw [GenericFiniteIFTAtlas.localSeparatedTime, (G.tilt p.1).tilted_eq]
  rfl


-- @@ L470-470 verbatim
end GenericFiniteIFTSurfaceAtlas


-- @@ L472-472 verbatim
end Submission
