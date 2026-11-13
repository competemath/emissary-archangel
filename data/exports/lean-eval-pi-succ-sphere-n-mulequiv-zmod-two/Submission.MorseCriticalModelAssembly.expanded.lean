import Submission.FiniteMorseJetInstallation
import Submission.FiniteIFTSurfaceCover
import Submission.IFTSurfaceCriticality
import Submission.MorseNormalFormShrink


-- @@ L6-16 verbatim
/-!
# Assembly of the actual local Morse critical model

The finite jet installation already gives one global amplitude and its exact
chartwise time formula on each owned cutoff core.  This file shrinks every
scalar Morse normal form into the open IFT domain and the interior of that
core, retains `C¹` control of the Morse parameter on the resulting ball, and
then differentiates the installed time identity.  The IFT criticality theorem
turns the resulting chart-gradient statement into the required ambient
`timeCritical` model.
-/


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Set Function Metric Filter

-- @@ L21-21 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L23-23 verbatim
namespace Submission


-- @@ L25-25 verbatim
variable {n : ℕ}


-- @@ L27-27 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L28-28 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L30-30 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L32-34 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L36-44 verbatim
/-- The control package selected at one recorded event.  Its parameter-space
condition is the genuine IFT domain and its ambient condition is the open
half-radius cutoff ball. -/
abbrev CriticalModelShrink (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :=
  (G.localMorseNormalForm p hp).IFTChartShrink
    (B.chart p.1) p.2
    (ball ((B.chart p.1).param p.2)
      (R.cutoffs.radius ⟨p, hp⟩ / 2))


-- @@ L46-61 verbatim
/-- Every production event admits one common radius controlling the open chart
domain, the open cutoff core, and first derivatives of the Morse parameter. -/
theorem exists_criticalModelShrink
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ∃ S : R.CriticalModelShrink p hp,
      ContDiffOn ℝ (1 : ℕ∞ω) (G.localMorseNormalForm p hp).param
        (ball (0 : E₂) S.radius) := by
  have hcore : p.2 ∈ B.core p.1 :=
    ((G.criticalPoints_spec p).mp hp).2
  have hdomain : p.2 ∈ (B.chart p.1).domain :=
    B.core_subset_domain p.1 hcore
  exact LocalMorseNormalForm.exists_iftChartCutoffShrink_contDiffOn_of_isOpen
      (G.localMorseNormalForm p hp) 1 (B.chart p.1) p.2
      (B.domain_open p.1) hdomain (R.cutoffs.radius ⟨p, hp⟩)
      (R.cutoffs.radius_pos ⟨p, hp⟩)


-- @@ L63-67 verbatim
/-- A fixed, choice-independent-at-the-interface shrink for each event. -/
def criticalModelShrink (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.CriticalModelShrink p hp :=
  Classical.choose (R.exists_criticalModelShrink p hp)


-- @@ L69-74 verbatim
theorem criticalModelShrink_contDiffOn
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ContDiffOn ℝ (1 : ℕ∞ω) (G.localMorseNormalForm p hp).param
      (ball (0 : E₂) (R.criticalModelShrink p hp).radius) :=
  Classical.choose_spec (R.exists_criticalModelShrink p hp)


-- @@ L76-82 verbatim
/-- The actual scalar normal form used by the installed event.  It has the
same index and parameter as the original Morse form, with only its radius
restricted. -/
def criticalNormalForm (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    LocalMorseNormalForm (recenter (G.localSeparatedTime p) p.2) :=
  (R.criticalModelShrink p hp).normalForm


-- @@ L84-88 verbatim
@[simp] theorem criticalNormalForm_index
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    (R.criticalNormalForm p hp).index =
      (G.localMorseNormalForm p hp).index := rfl


-- @@ L90-94 verbatim
@[simp] theorem criticalNormalForm_radius
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    (R.criticalNormalForm p hp).radius =
      (R.criticalModelShrink p hp).radius := rfl


-- @@ L96-100 verbatim
@[simp] theorem criticalNormalForm_param
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    (R.criticalNormalForm p hp).param =
      (G.localMorseNormalForm p hp).param := rfl


-- @@ L102-118 verbatim
/-- The finite installation's exact time equation, restricted to any valid
critical-model shrink. -/
theorem time_install_of_criticalModelShrink
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (S : R.CriticalModelShrink p hp) (u : E₂)
    (hu : ‖u‖ < S.radius) :
    tcoord (R.amplitude.diffeomorph.symm
      ((B.chart p.1).param
        (p.2 + (G.localMorseNormalForm p hp).param u))) =
      G.localSeparatedTime p
        (p.2 + (G.localMorseNormalForm p hp).param u) := by
  apply R.time_install ⟨p, hp⟩
  · exact LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
      (M := G.localMorseNormalForm p hp) S u hu
  · exact LocalMorseNormalForm.SimultaneousShrink.ift_lifted_mem_closedBall
      (M := G.localMorseNormalForm p hp) S u hu


-- @@ L120-134 verbatim
/-- On the shrink ball, the installed ambient time is literally the selected
Morse quadratic model. -/
theorem time_model_of_criticalModelShrink
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (S : R.CriticalModelShrink p hp) (u : E₂)
    (hu : ‖u‖ < S.radius) :
    tcoord (R.amplitude.diffeomorph.symm
      ((B.chart p.1).param
        (p.2 + (G.localMorseNormalForm p hp).param u))) =
      G.localSeparatedTime p p.2 +
        morseQuadratic (G.localMorseNormalForm p hp).index (u 0, u 1) := by
  rw [R.time_install_of_criticalModelShrink p hp S u hu]
  simpa [recenter] using (G.localMorseNormalForm p hp).exact u
    (hu.trans_le S.radius_le)


-- @@ L136-156 verbatim
/-- The installed chart time and the separated local time agree on a full
neighborhood whenever the point lies in the open IFT domain and open cutoff
core.  This is the differentiable strengthening of `time_install`. -/
theorem eventuallyEq_installedChartTime
    (R : ExactFiniteMorseJetInstallation G)
    (p : GenericMorseEvent G) {z : E₂}
    (hdom : (B.chart p.1.1).domain ∈ nhds z)
    (hcore : (B.chart p.1.1).param z ∈
      ball ((B.chart p.1.1).param p.1.2)
        (R.cutoffs.radius p / 2)) :
    (fun w : E₂ => tcoord (R.amplitude.diffeomorph.symm
      ((B.chart p.1.1).param w))) =ᶠ[nhds z]
        G.localSeparatedTime p.1 := by
  have hcoreEventually : ∀ᶠ w in nhds z,
      (B.chart p.1.1).param w ∈
        ball ((B.chart p.1.1).param p.1.2)
          (R.cutoffs.radius p / 2) :=
    (B.chart p.1.1).param_smooth.continuous.continuousAt
      (isOpen_ball.mem_nhds hcore)
  filter_upwards [hdom, hcoreEventually] with w hwd hwc
  exact R.time_install p w hwd (ball_subset_closedBall hwc)


-- @@ L158-165 verbatim
/-- Smoothness of the separated local scalar function. -/
private theorem localSeparatedTime_contDiff
    (p : Σ _ : ι, E₂) : ContDiff ℝ ∞ (G.localSeparatedTime p) := by
  change ContDiff ℝ ∞
    (fun u => (G.tilt p.1).tilted u + G.valueShift p)
  rw [(G.tilt p.1).tilted_eq]
  exact (contDiff_chartLinearTilt
    (B.chart p.1).contDiff_time (G.tilt p.1).q).add contDiff_const


-- @@ L167-214 verbatim
/-- The actual local ambient critical model.  No injectivity of the Morse
parameter is assumed: IFT criticality detects the chart gradient, and the
exact quadratic identity plus `C¹` control proves that its only zero is the
normal-form origin. -/
theorem critical_model_of_criticalModelShrink
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (S : R.CriticalModelShrink p hp)
    (hparam : ContDiffOn ℝ (1 : ℕ∞ω)
      (G.localMorseNormalForm p hp).param (ball (0 : E₂) S.radius))
    (u : E₂) (hu : ‖u‖ < S.radius) :
    (R.amplitude.diffeomorph.symm
        ((B.chart p.1).param
          (p.2 + (G.localMorseNormalForm p hp).param u)) ∈
      timeCritical (R.amplitude.toVerticalAmplitude.pullback C).G ↔ u = 0) := by
  let M := G.localMorseNormalForm p hp
  let P := B.chart p.1
  let z : E₂ := p.2 + M.param u
  have hdom : P.domain ∈ nhds z := by
    exact LocalMorseNormalForm.SimultaneousShrink.ift_domain_mem_nhds
      (M := M) S (B.domain_open p.1) u hu
  have hcore : P.param z ∈
      ball (P.param p.2) (R.cutoffs.radius ⟨p, hp⟩ / 2) := by
    exact LocalMorseNormalForm.SimultaneousShrink.ift_lifted_mem
      (M := M) S u hu
  have htime := R.eventuallyEq_installedChartTime ⟨p, hp⟩ hdom hcore
  have hgradient :
      chartGradient
          (fun w : E₂ => tcoord
            (R.amplitude.diffeomorph.symm (P.param w))) z =
        chartGradient (G.localSeparatedTime p) z := by
    rw [chartGradient, chartGradient, htime.fderiv_eq]
  have hquadratic :
      chartGradient (G.localSeparatedTime p) (p.2 + M.param u) = 0 ↔
        u = 0 := by
    exact LocalMorseNormalForm.SimultaneousShrink.chartGradient_shifted_param_eq_zero_iff_of_contDiffOn_one
        M S ((localSeparatedTime_contDiff (G := G) p).differentiable (by simp))
        (G.localSeparatedTime_nondegenerate p hp).1 hparam u hu
  calc
    R.amplitude.diffeomorph.symm (P.param z) ∈
          timeCritical (R.amplitude.toVerticalAmplitude.pullback C).G
        ↔ chartGradient
            (fun w : E₂ => tcoord
              (R.amplitude.diffeomorph.symm (P.param w))) z = 0 :=
          P.pullbackParam_mem_timeCritical_iff_chartGradient_eq_zero
            R.amplitude hdom
    _ ↔ chartGradient (G.localSeparatedTime p) z = 0 := by rw [hgradient]
    _ ↔ u = 0 := by simpa [z, M] using hquadratic


-- @@ L216-227 verbatim
/-- The chosen production shrink therefore carries a proved ambient critical
model at every recorded event. -/
theorem critical_model
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    (R.amplitude.diffeomorph.symm
        ((B.chart p.1).param
          (p.2 + (G.localMorseNormalForm p hp).param u)) ∈
      timeCritical (R.amplitude.toVerticalAmplitude.pullback C).G ↔ u = 0) :=
  R.critical_model_of_criticalModelShrink p hp
    (R.criticalModelShrink p hp) (R.criticalModelShrink_contDiffOn p hp) u hu


-- @@ L229-239 verbatim
/-- Form consumed by the existing installed-parameter API. -/
theorem installed_critical_model
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalNormalForm p hp).radius) :
    (R.amplitude.diffeomorph.symm
        ((B.chart p.1).param
          (p.2 + G.installedMorseParam p u)) ∈
      timeCritical (R.amplitude.toVerticalAmplitude.pullback C).G ↔ u = 0) := by
  rw [G.installedMorseParam_eq p hp]
  exact R.critical_model p hp u (by simpa using hu)


-- @@ L241-241 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L243-243 verbatim
end Submission
