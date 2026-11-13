import Submission.MorseGlobalCutoffAmplitude
import Submission.ExactMorsePositionAssembly


-- @@ L4-14 verbatim
/-!
# Local Morse atlas for the one-cutoff shared-covector construction

The global cutoff theorem supplies one actual smooth height on every chart,
Morse-goodness on all compact cores, and exact finite ownership of the full
compact critical locus.  This file turns those critical chart parameters into
genuine ambient `StandardMorseEventAt` models for the inverse pullback.

Critical-value separation is deliberately not built into this record.  After
the local-model theorem below, it is the only missing field of `MorseAtlas`.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open Set Function Metric Filter

-- @@ L19-19 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L21-21 verbatim
namespace Submission


-- @@ L23-23 verbatim
variable {n : ℕ}


-- @@ L25-25 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L26-26 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L27-27 verbatim
local notation "Cov" => E' →L[ℝ] ℝ


-- @@ L29-29 verbatim
namespace FiniteIFTSurfaceCover


-- @@ L31-31 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]


-- @@ L33-44 verbatim
/-- Constructed data retained from the one-cutoff global Morse choice.  Every
field is produced by `exists_sharedMorse_globalCutoffCriticalCover`; no
geometric coverage or local-model hypothesis is stored here. -/
structure SharedCutoffMorseData (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) where
  covector : Cov
  forward : SmallVerticalAmplitude (n := n)
  twice_K_lt_one : 2 * forward.K < 1
  forward_toFun : forward.toFun = χ.localizeCovector (n := n) covector
  morseOn : ∀ i,
    (B.chart i).CutoffAffineMorseOn χ covector (B.core i)


-- @@ L46-46 verbatim
namespace SharedCutoffMorseData


-- @@ L48-48 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L49-50 verbatim
variable {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
  {χ : SmoothCutoff K U}


-- @@ L52-55 verbatim
/-- The inverse amplitude whose pullback realizes the forward cutoff height. -/
def amplitude (R : B.SharedCutoffMorseData χ) :
    SmallVerticalAmplitude (n := n) :=
  R.forward.inverse R.twice_K_lt_one


-- @@ L57-59 verbatim
/-- The globally perturbed cobordism. -/
def output (R : B.SharedCutoffMorseData χ) : FramedLevelCobordism n :=
  (amplitude R).toVerticalAmplitude.pullback C


-- @@ L61-63 verbatim
theorem amplitude_diffeomorph (R : B.SharedCutoffMorseData χ) :
    (amplitude R).diffeomorph = R.forward.diffeomorph.symm :=
  R.forward.inverse_diffeomorph R.twice_K_lt_one


-- @@ L65-68 verbatim
theorem amplitude_diffeomorph_symm (R : B.SharedCutoffMorseData χ) :
    (amplitude R).diffeomorph.symm = R.forward.diffeomorph := by
  rw [amplitude_diffeomorph R]
  rfl


-- @@ L70-73 verbatim
/-- Finite chart-indexed owners of the compact global critical locus. -/
def criticalParameters (R : B.SharedCutoffMorseData χ) :
    Set (Σ _ : ι, E₂) :=
  B.cutoffCoreCriticalParameters χ R.covector R.forward


-- @@ L75-78 verbatim
/-- Ambient center represented by a chart-indexed owner. -/
def center (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) : E' :=
  B.cutoffCriticalCenter R.forward p


-- @@ L80-82 verbatim
theorem finite_criticalParameters (R : B.SharedCutoffMorseData χ) :
    (criticalParameters R).Finite :=
  B.finite_cutoffCoreCriticalParameters χ R.covector R.forward R.morseOn


-- @@ L84-88 verbatim
/-- Exact global ownership inherited from the one-cutoff theorem. -/
theorem centers_exact (R : B.SharedCutoffMorseData χ) :
    center R '' criticalParameters R = coreCriticalPoints (output R) := by
  exact B.image_cutoffCoreCriticalParameters_eq_coreCriticalPoints
    χ R.covector R.forward R.forward_toFun R.twice_K_lt_one


-- @@ L90-93 verbatim
theorem critical_gradient_eq_zero (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    (B.chart p.1).cutoffAffineGradient χ (R.covector, p.2) = 0 :=
  hp.1.1


-- @@ L95-98 verbatim
theorem critical_mem_core (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    p.2 ∈ B.core p.1 :=
  hp.1.2


-- @@ L100-120 verbatim
/-- Every owned critical parameter is a nondegenerate critical point of the
actual cutoff chart height. -/
theorem critical_nondegenerate (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    NondegenerateCriticalAt
      ((B.chart p.1).cutoffAffineHeight χ R.covector) p.2 := by
  let P := B.chart p.1
  have hzero : P.cutoffAffineGradient χ (R.covector, p.2) = 0 :=
    critical_gradient_eq_zero R p hp
  have hgood := R.morseOn p.1 p.2 (critical_mem_core R p hp)
  change P.cutoffAffineGradient χ (R.covector, p.2) ≠ 0 ∨
    Bijective (P.cutoffAffineHessian χ (R.covector, p.2)) at hgood
  have hbij : Bijective (P.cutoffAffineHessian χ (R.covector, p.2)) := by
    rcases hgood with hne | hbij
    · exact (hne hzero).elim
    · exact hbij
  constructor
  · rw [← P.cutoffAffineGradient_eq_chartGradient]
    exact hzero
  · rw [← P.cutoffAffineHessian_eq_fderiv_chartGradient]
    exact hbij


-- @@ L122-130 verbatim
/-- Constructive scalar Morse coordinates at every actual cutoff critical
parameter. -/
def localMorseNormalForm (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    LocalMorseNormalForm
      (recenter ((B.chart p.1).cutoffAffineHeight χ R.covector) p.2) :=
  (nonempty_localMorseNormalForm_recenter
    ((B.chart p.1).contDiff_cutoffAffineHeight χ R.covector)
    (critical_nondegenerate R p hp)).some


-- @@ L132-137 verbatim
/-- A common radius controlling the IFT domain, a harmless ambient ball, and
`C¹` regularity of the constructive Morse parameter. -/
abbrev CriticalModelShrink (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :=
  (localMorseNormalForm R p hp).IFTChartShrink
    (B.chart p.1) p.2 (ball ((B.chart p.1).param p.2) (1 / 2 : ℝ))


-- @@ L139-146 verbatim
theorem exists_criticalModelShrink (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    ∃ S : CriticalModelShrink R p hp,
      ContDiffOn ℝ (1 : ℕ∞ω) (localMorseNormalForm R p hp).param
        (ball (0 : E₂) S.radius) := by
  exact (localMorseNormalForm R p hp).exists_iftChartCutoffShrink_contDiffOn_of_isOpen
      1 (B.chart p.1) p.2 (B.domain_open p.1)
      (B.core_subset_domain p.1 (critical_mem_core R p hp)) 1 (by norm_num)


-- @@ L148-151 verbatim
def criticalModelShrink (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    CriticalModelShrink R p hp :=
  Classical.choose (exists_criticalModelShrink R p hp)


-- @@ L153-157 verbatim
theorem criticalModelShrink_contDiffOn (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    ContDiffOn ℝ (1 : ℕ∞ω) (localMorseNormalForm R p hp).param
      (ball (0 : E₂) (criticalModelShrink R p hp).radius) :=
  Classical.choose_spec (exists_criticalModelShrink R p hp)


-- @@ L159-164 verbatim
/-- The scalar normal form restricted to the production IFT radius. -/
def criticalNormalForm (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    LocalMorseNormalForm
      (recenter ((B.chart p.1).cutoffAffineHeight χ R.covector) p.2) :=
  (criticalModelShrink R p hp).normalForm


-- @@ L166-176 verbatim
/-- The forward ambient deformation realizes the actual cutoff scalar height
on every chart, with no plateau restriction. -/
theorem installedChartTime (R : B.SharedCutoffMorseData χ)
    (i : ι) (z : E₂) :
    tcoord (R.forward.diffeomorph ((B.chart i).param z)) =
      (B.chart i).cutoffAffineHeight χ R.covector z := by
  rw [SmallVerticalAmplitude.diffeomorph_apply, tcoord_verticalShift]
  change (B.chart i).time z + R.forward.toFun ((B.chart i).param z) =
    (B.chart i).cutoffAffineHeight χ R.covector z
  rw [R.forward_toFun]
  rfl


-- @@ L178-186 verbatim
/-- The ambient surface parameter obtained by composing the constructive
Morse coordinate, the original IFT chart, and the single forward
diffeomorphism. -/
def criticalAmbientParam (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R)
    (u : E₂) : E' :=
  R.forward.diffeomorph
    ((B.chart p.1).param
      (p.2 + (criticalNormalForm R p hp).param u))


-- @@ L188-194 verbatim
@[simp] theorem criticalAmbientParam_zero
    (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    criticalAmbientParam R p hp 0 = center R p := by
  rw [criticalAmbientParam, center,
    (criticalNormalForm R p hp).param_zero, add_zero]
  rfl


-- @@ L196-233 verbatim
/-- The exact quadratic scalar identity and the global chart-criticality
equivalence identify the ambient critical point in the installed event with
the normal-form origin. -/
theorem critical_model (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R)
    (u : E₂) (hu : ‖u‖ < (criticalNormalForm R p hp).radius) :
    (criticalAmbientParam R p hp u ∈ timeCritical (output R).G ↔
      u = 0) := by
  let P := B.chart p.1
  let f := P.cutoffAffineHeight χ R.covector
  let M := localMorseNormalForm R p hp
  let S := criticalModelShrink R p hp
  let z : E₂ := p.2 + M.param u
  have huS : ‖u‖ < S.radius := by simpa [S, criticalNormalForm] using hu
  have hdom : P.domain ∈ nhds z := by
    exact LocalMorseNormalForm.SimultaneousShrink.ift_domain_mem_nhds
      (M := M) S (B.domain_open p.1) u huS
  have hgradient : chartGradient f z = 0 ↔ u = 0 := by
    exact LocalMorseNormalForm.SimultaneousShrink.chartGradient_shifted_param_eq_zero_iff_of_contDiffOn_one
        M S
        ((P.contDiff_cutoffAffineHeight χ R.covector).differentiable
          infty_ne_zero)
        (critical_nondegenerate R p hp).1
        (criticalModelShrink_contDiffOn R p hp) u huS
  change R.forward.diffeomorph (P.param z) ∈
      timeCritical
        ((R.forward.inverse R.twice_K_lt_one).toVerticalAmplitude.pullback C).G ↔
    u = 0
  calc
    R.forward.diffeomorph (P.param z) ∈
          timeCritical
            ((R.forward.inverse R.twice_K_lt_one).toVerticalAmplitude.pullback C).G
        ↔ P.cutoffAffineGradient χ (R.covector, z) = 0 :=
          P.forwardParam_mem_inversePullback_timeCritical_iff_cutoffGradient_eq_zero
            χ R.covector R.forward R.forward_toFun R.twice_K_lt_one hdom
    _ ↔ chartGradient f z = 0 := by
      rw [P.cutoffAffineGradient_eq_chartGradient]
    _ ↔ u = 0 := hgradient


-- @@ L235-303 verbatim
/-- The original production IFT chart and the constructive Morse coordinate
cover the pulled-back fiber near every installed global critical center. -/
theorem covers_fiber (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    ∃ ε > 0, ∀ v : E',
      dist v (center R p) < ε →
      (output R).G v = 0 →
      ∃ u : E₂, ‖u‖ < (criticalNormalForm R p hp).radius ∧
        criticalAmbientParam R p hp u = v := by
  let P := B.chart p.1
  let f := P.cutoffAffineHeight χ R.covector
  let M := localMorseNormalForm R p hp
  let S := criticalModelShrink R p hp
  let a := amplitude R
  let x : E' := P.param p.2
  let c : E' := center R p
  have hsmooth : ContDiff ℝ ∞ f :=
    P.contDiff_cutoffAffineHeight χ R.covector
  have hf : ContDiffAt ℝ 2 (recenter f p.2) 0 :=
    contDiffAt_infty.mp (contDiff_recenter hsmooth p.2).contDiffAt 2
  have hcrit : fderiv ℝ (recenter f p.2) 0 = 0 :=
    fderiv_eq_zero_of_chartGradient_eq_zero
      (nondegenerateCriticalAt_recenter hsmooth
        (critical_nondegenerate R p hp)).1
  obtain ⟨δ, hδ, hM⟩ := M.exists_preimage_norm_lt hf hcrit S.radius_pos
  have hpdom : p.2 ∈ P.domain :=
    B.core_subset_domain p.1 (critical_mem_core R p hp)
  obtain ⟨ε₀, hε₀, hP⟩ :=
    P.exists_param_of_fiber_near (B.domain_open p.1) hpdom
      (ball_mem_nhds p.2 hδ)
  have hac : a.diffeomorph c = x := by
    have haeq : a.diffeomorph = R.forward.diffeomorph.symm := by
      simpa [a] using amplitude_diffeomorph R
    rw [haeq]
    dsimp [c, x, center]
    exact R.forward.diffeomorph.symm_apply_apply _
  have htendsto : Tendsto (fun v : E' => a.diffeomorph v)
      (nhds c) (nhds x) := by
    rw [← hac]
    exact a.diffeomorph.continuous.continuousAt
  have hnear : (fun v : E' => a.diffeomorph v) ⁻¹' ball x ε₀ ∈ nhds c :=
    htendsto (ball_mem_nhds x hε₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_⟩
  intro v hv hzero
  have hvball : v ∈ ball c ε := by
    simpa [mem_ball, c] using hv
  have haBall : a.diffeomorph v ∈ ball x ε₀ := hball hvball
  have haDist : dist (a.diffeomorph v) (P.param p.2) < ε₀ := by
    simpa [mem_ball, x] using haBall
  have haZero : C.G (a.diffeomorph v) = 0 := by
    simpa [output, VerticalAmplitude.pullback_G,
      SmallVerticalAmplitude.diffeomorph_apply, a] using hzero
  obtain ⟨z, hzball, _hzdom, hzparam⟩ :=
    hP (a.diffeomorph v) haDist haZero
  have hy : ‖z - p.2‖ < δ := by
    simpa [mem_ball, dist_eq_norm] using hzball
  obtain ⟨u, hu, hMu⟩ := hM (z - p.2) hy
  refine ⟨u, ?_, ?_⟩
  · simpa [criticalNormalForm, S] using hu
  · change R.forward.diffeomorph (P.param (p.2 + M.param u)) = v
    rw [← amplitude_diffeomorph_symm R]
    calc
      a.diffeomorph.symm (P.param (p.2 + M.param u)) =
          a.diffeomorph.symm (P.param z) := by
            congr 2
            rw [hMu, add_sub_cancel]
      _ = a.diffeomorph.symm (a.diffeomorph v) := by rw [hzparam]
      _ = v := a.diffeomorph.symm_apply_apply v


-- @@ L305-343 verbatim
/-- All ambient fields required for one standard Morse event are now
constructed from the single global cutoff deformation. -/
def installedCriticalGeometry (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    InstalledMorseEventGeometry (n := n) (output R)
      ((B.chart p.1).cutoffAffineHeight χ R.covector) p.2
      (center R p) (criticalNormalForm R p hp) where
  ambientParam := criticalAmbientParam R p hp
  ambientParam_smooth := by
    exact (contDiff_verticalShift R.forward.smooth).contDiffAt.comp 0
      ((B.chart p.1).param_smooth.contDiffAt.comp 0
        (contDiffAt_const.add
          (criticalNormalForm R p hp).param_contDiffAt))
  ambientParam_zero := criticalAmbientParam_zero R p hp
  ambientParam_fiber := by
    intro u hu
    rw [output, VerticalAmplitude.pullback_G]
    change C.G (verticalShift (amplitude R)
      (R.forward.diffeomorph
        ((B.chart p.1).param
          (p.2 + (criticalNormalForm R p hp).param u)))) = 0
    rw [← SmallVerticalAmplitude.diffeomorph_apply]
    rw [amplitude_diffeomorph R,
      R.forward.diffeomorph.symm_apply_apply]
    apply (B.chart p.1).param_fiber
    exact LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
      (M := localMorseNormalForm R p hp)
      (criticalModelShrink R p hp) u
      (by simpa [criticalNormalForm] using hu)
  time_lift := by
    intro u _hu
    change tcoord (R.forward.diffeomorph
      ((B.chart p.1).param
        (p.2 + (criticalNormalForm R p hp).param u))) = _
    rw [installedChartTime]
    rfl
  critical_model := critical_model R p hp
  covers_fiber := by
    simpa using covers_fiber R p hp


-- @@ L345-350 verbatim
/-- A genuine standard ambient Morse event at every finite shared-cutoff
critical owner. -/
def installedStandardMorseEvent (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ criticalParameters R) :
    StandardMorseEventAt (output R) (center R p) :=
  (installedCriticalGeometry R p hp).toStandardMorseEventAt


-- @@ L352-360 verbatim
/-- Every point of the full compact global critical locus carries a standard
Morse event chart.  Exact ownership removes all global coverage assumptions. -/
theorem localModel (R : B.SharedCutoffMorseData χ) :
    ∀ v, v ∈ coreCriticalPoints (output R) →
      Nonempty (StandardMorseEventAt (output R) v) := by
  intro v hv
  rw [← centers_exact R] at hv
  rcases hv with ⟨p, hp, rfl⟩
  exact ⟨installedStandardMorseEvent R p hp⟩


-- @@ L362-369 verbatim
/-- Once event times have been separated, the remaining `MorseAtlas`
assembly is immediate; all local and global coverage fields are already
theorems of the shared-cutoff construction. -/
theorem toMorseAtlas (R : B.SharedCutoffMorseData χ)
    (hdistinct : Set.InjOn tcoord (coreCriticalPoints (output R))) :
    MorseAtlas (output R) where
  localModel := localModel R
  distinct_times := hdistinct


-- @@ L371-388 verbatim
/-- Package the output of the proved shared-covector/no-transition theorem as
`SharedCutoffMorseData`. -/
theorem nonempty_of_globalCutoffChoice
    (B : FiniteIFTSurfaceCover C ι)
    {a b : ℝ} (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff (compactInteriorFiber C a b) U)
    (hU : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ))
    (hcrit : timeCritical C.G ⊆ tcoord ⁻¹' Ioo a b) :
    Nonempty (B.SharedCutoffMorseData χ) := by
  obtain ⟨A, forward, hsmall, hforward, hMorse, _hfinite, _hexact⟩ :=
    B.exists_sharedMorse_globalCutoffCriticalCover ha hb χ hU hcrit
  exact ⟨{
    covector := A
    forward := forward
    twice_K_lt_one := hsmall
    forward_toFun := hforward
    morseOn := hMorse }⟩


-- @@ L390-409 verbatim
/-- End-to-end choice from a finite production IFT cover: strict global
plateau bounds, one fiber-wide cutoff, one shared ambient covector, exact
finite global ownership, and standard local Morse models all exist without an
additional compatibility assumption. -/
theorem exists_globalCutoffMorseData
    (B : FiniteIFTSurfaceCover C ι) :
    ∃ a b : ℝ, ∃ U : Set E',
      ∃ χ : SmoothCutoff (compactInteriorFiber C a b) U,
        1 / 4 < a ∧ a < b ∧ b < 3 / 4 ∧
        U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ) ∧
        Nonempty (B.SharedCutoffMorseData χ) := by
  obtain ⟨a, b, ha, hab, hb, hcore⟩ :=
    exists_strictInterior_bounds_coreCriticalPoints C
  have hcrit : timeCritical C.G ⊆ tcoord ⁻¹' Ioo a b :=
    timeCritical_subset_strictInterior_of_coreCritical_subset C hcore
  obtain ⟨U, hU, hχ⟩ :=
    exists_globalCompactInteriorFiberCutoff C ha hb
  obtain ⟨χ⟩ := hχ
  refine ⟨a, b, U, χ, ha, hab, hb, hU, ?_⟩
  exact nonempty_of_globalCutoffChoice B ha hb χ hU hcrit


-- @@ L411-411 verbatim
end SharedCutoffMorseData


-- @@ L413-413 verbatim
end FiniteIFTSurfaceCover


-- @@ L415-415 verbatim
end Submission
