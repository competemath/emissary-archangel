import Mathlib
import Submission.MorseAtlasAssembly
import Submission.FiniteGlobalVerticalAmplitude
import Submission.FiniteDisjointSmoothCutoff
import Submission.SmallVerticalAmplitudeInverse


-- @@ L7-20 verbatim
/-!
# Exact finite installation of local Morse event jets

The chartwise genericity package supplies one localized affine time jet around
each recorded critical point.  Pairwise disjoint cutoffs let us add those jets
without changing any owned core.  If their quantitative Lipschitz bounds sum
to less than one half, the resulting forward deformation is small and its
inverse is again a `SmallVerticalAmplitude`.

The pullback amplitude is chosen to be that inverse.  Consequently its inverse
diffeomorphism is the original forward deformation, and the chartwise formula
from `IFTSurfaceChart.ambientEventRaw` becomes exactly the inverse-time formula
required by `SignedMorseGeometry`.
-/


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function Metric

-- @@ L25-25 verbatim
open scoped RealInnerProductSpace ContDiff Topology BigOperators


-- @@ L27-27 verbatim
namespace Submission


-- @@ L29-29 verbatim
variable {n : ℕ}


-- @@ L31-31 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L32-32 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L34-39 verbatim
/-- The finite type of critical points recorded by a generic surface atlas. -/
abbrev GenericMorseEvent
    {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
    {B : FiniteIFTSurfaceChartFamily C ι}
    (G : GenericFiniteIFTSurfaceAtlas B) :=
  {p : Σ _ : ι, E₂ // p ∈ G.criticalPoints}


-- @@ L41-41 verbatim
namespace GenericFiniteIFTSurfaceAtlas


-- @@ L43-45 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceChartFamily C ι}
  (G : GenericFiniteIFTSurfaceAtlas B)


-- @@ L47-49 verbatim
/-- The ambient point represented by a recorded chart critical point. -/
def eventAmbientPoint (p : GenericMorseEvent G) : E' :=
  (B.chart p.1.1).param p.1.2


-- @@ L51-51 verbatim
end GenericFiniteIFTSurfaceAtlas


-- @@ L53-64 verbatim
/-- Pairwise disjoint cutoff data together with quantitative bounds for every
localized event jet. -/
structure ExactFiniteMorseJetInstallation
    {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
    {B : FiniteIFTSurfaceChartFamily C ι}
    (G : GenericFiniteIFTSurfaceAtlas B) where
  cutoffs : FiniteDisjointMiddleCutoffs G.eventAmbientPoint
  K : GenericMorseEvent G → NNReal
  twice_sum_K_lt_one : 2 * (∑ p, K p) < 1
  lipschitz : ∀ p, LipschitzWith (K p)
    ((B.chart p.1.1).ambientEventRaw (cutoffs.cutoff p)
      (G.tilt p.1.1).q (G.valueShift p.1))


-- @@ L66-66 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L68-70 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceChartFamily C ι}
  {G : GenericFiniteIFTSurfaceAtlas B}


-- @@ L72-76 verbatim
/-- The localized affine jet owned by one recorded event. -/
def eventRaw (R : ExactFiniteMorseJetInstallation G)
    (p : GenericMorseEvent G) : E' → ℝ :=
  (B.chart p.1.1).ambientEventRaw (R.cutoffs.cutoff p)
    (G.tilt p.1.1).q (G.valueShift p.1)


-- @@ L78-81 verbatim
theorem eventRaw_smooth (R : ExactFiniteMorseJetInstallation G)
    (p : GenericMorseEvent G) : ContDiff ℝ ∞ (R.eventRaw p) :=
  (B.chart p.1.1).contDiff_ambientEventRaw (R.cutoffs.cutoff p)
    (G.tilt p.1.1).q (G.valueShift p.1)


-- @@ L83-85 verbatim
theorem eventRaw_compactSupport (R : ExactFiniteMorseJetInstallation G)
    (p : GenericMorseEvent G) : HasCompactSupport (R.eventRaw p) :=
  (R.cutoffs.cutoff p).hasCompactSupport_localize _


-- @@ L87-92 verbatim
theorem eventRaw_collar_zero (R : ExactFiniteMorseJetInstallation G)
    (p : GenericMorseEvent G) (v : E')
    (hv : tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v) :
    R.eventRaw p v = 0 :=
  (R.cutoffs.cutoff p).localize_collar_zero
    (R.cutoffs.support_subset_middle p) _ v hv


-- @@ L94-105 verbatim
/-- Disjoint support balls make every other event jet vanish on the current
event's owned core. -/
theorem eventRaw_noninterference (R : ExactFiniteMorseJetInstallation G)
    (p : GenericMorseEvent G) (v : E')
    (hv : v ∈ closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p / 2))
    (q : GenericMorseEvent G) (hqp : q ≠ p) :
    R.eventRaw q v = 0 := by
  let jet : GenericMorseEvent G → E' → ℝ := fun e =>
    SmoothCutoff.affineJet (-((B.chart e.1.1).liftCovector (G.tilt e.1.1).q))
      (B.chart e.1.1).center (G.valueShift e.1)
  simpa [eventRaw, IFTSurfaceChart.ambientEventRaw, jet] using
    R.cutoffs.localized_eq_zero_of_mem_core jet p hv q hqp


-- @@ L107-113 verbatim
theorem sum_K_lt_one (R : ExactFiniteMorseJetInstallation G) :
    (∑ p, R.K p) < 1 := by
  have htwice : 2 * ((∑ p, R.K p : NNReal) : ℝ) < 1 := by
    exact_mod_cast R.twice_sum_K_lt_one
  have hnonneg : 0 ≤ ((∑ p, R.K p : NNReal) : ℝ) := NNReal.coe_nonneg _
  have hreal : ((∑ p, R.K p : NNReal) : ℝ) < 1 := by linarith
  exact_mod_cast hreal


-- @@ L115-122 verbatim
/-- The one forward deformation obtained by summing all local event jets. -/
def forwardAmplitude (R : ExactFiniteMorseJetInstallation G) :
    SmallVerticalAmplitude (n := n) :=
  FiniteGlobalVerticalAmplitude.ofFiniteLipschitz
    R.eventRaw
    (fun p => R.eventRaw_smooth p)
    (fun p v hv => R.eventRaw_collar_zero p v hv)
    R.K R.sum_K_lt_one R.lipschitz


-- @@ L124-126 verbatim
@[simp] theorem forwardAmplitude_K
    (R : ExactFiniteMorseJetInstallation G) :
    R.forwardAmplitude.K = ∑ p, R.K p := rfl


-- @@ L128-132 verbatim
theorem forwardAmplitude_twice_K_lt_one
    (R : ExactFiniteMorseJetInstallation G) :
    2 * R.forwardAmplitude.K < 1 := by
  rw [R.forwardAmplitude_K]
  exact R.twice_sum_K_lt_one


-- @@ L134-137 verbatim
/-- The pullback amplitude is the inverse of the forward event deformation. -/
def amplitude (R : ExactFiniteMorseJetInstallation G) :
    SmallVerticalAmplitude (n := n) :=
  R.forwardAmplitude.inverse R.forwardAmplitude_twice_K_lt_one


-- @@ L139-150 verbatim
/-- Its inverse diffeomorphism is exactly the forward event deformation. -/
theorem amplitude_diffeomorph_symm
    (R : ExactFiniteMorseJetInstallation G) :
    R.amplitude.diffeomorph.symm = R.forwardAmplitude.diffeomorph := by
  apply Diffeomorph.ext
  intro v
  have hinv := R.forwardAmplitude.inverse_diffeomorph
    R.forwardAmplitude_twice_K_lt_one
  change (R.forwardAmplitude.inverse
    R.forwardAmplitude_twice_K_lt_one).diffeomorph.symm v = _
  rw [hinv]
  exact R.forwardAmplitude.diffeomorph.symm_symm_apply v


-- @@ L152-165 verbatim
/-- On an owned core, the global forward amplitude is exactly the corresponding
localized event jet. -/
theorem forwardAmplitude_eq_eventRaw_on_core
    (R : ExactFiniteMorseJetInstallation G)
    (p : GenericMorseEvent G) {v : E'}
    (hv : v ∈ closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p / 2)) :
    R.forwardAmplitude v = R.eventRaw p v := by
  exact FiniteGlobalVerticalAmplitude.ofFiniteLipschitz_eq_on_core
    R.eventRaw
    (fun p => closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p / 2))
    (fun p => R.eventRaw_smooth p)
    (fun p v hv => R.eventRaw_collar_zero p v hv)
    (fun p v hv q hqp => R.eventRaw_noninterference p v hv q hqp)
    R.K R.sum_K_lt_one R.lipschitz p hv


-- @@ L167-191 verbatim
/-- Exact local inverse-time installation.  This has the same orientation as
the `time_install` field of `SignedMorseGeometry`. -/
theorem time_install
    (R : ExactFiniteMorseJetInstallation G)
    (p : GenericMorseEvent G) (u : E₂)
    (hud : u ∈ (B.chart p.1.1).domain)
    (hu : (B.chart p.1.1).param u ∈
      closedBall (G.eventAmbientPoint p) (R.cutoffs.radius p / 2)) :
    tcoord (R.amplitude.diffeomorph.symm ((B.chart p.1.1).param u)) =
      G.localSeparatedTime p.1 u := by
  rw [R.amplitude_diffeomorph_symm]
  rw [SmallVerticalAmplitude.diffeomorph_apply]
  have ha : R.forwardAmplitude ((B.chart p.1.1).param u) =
      R.eventRaw p ((B.chart p.1.1).param u) :=
    R.forwardAmplitude_eq_eventRaw_on_core p hu
  have hshift : verticalShift R.forwardAmplitude ((B.chart p.1.1).param u) =
      verticalShift (R.eventRaw p) ((B.chart p.1.1).param u) := by
    simp only [verticalShift]
    rw [ha]
  rw [hshift]
  have hlocal := (B.chart p.1.1).verticalShift_time_eq_chartLinearTilt_add_const
    (R.cutoffs.cutoff p) (G.tilt p.1.1).q (G.valueShift p.1) hud hu
  simpa [eventRaw, GenericFiniteIFTAtlas.localSeparatedTime,
    (G.tilt p.1.1).tilted_eq,
    FiniteIFTSurfaceChartFamily.toFiniteIFTChartFamily] using hlocal


-- @@ L193-212 verbatim
/-- The installed normal-form parametrizations inherit the exact time formula
once they are contained in their owned cutoff cores. -/
theorem installed_time_install
    (R : ExactFiniteMorseJetInstallation G)
    (hdom : ∀ p (hp : p ∈ G.criticalPoints) u,
      ‖u‖ < (G.localMorseNormalForm p hp).radius →
        p.2 + G.installedMorseParam p u ∈ (B.chart p.1).domain)
    (hcore : ∀ p (hp : p ∈ G.criticalPoints) u,
      ‖u‖ < (G.localMorseNormalForm p hp).radius →
        (B.chart p.1).param (p.2 + G.installedMorseParam p u) ∈
          closedBall (G.eventAmbientPoint ⟨p, hp⟩)
            (R.cutoffs.radius ⟨p, hp⟩ / 2)) :
    ∀ p (hp : p ∈ G.criticalPoints) u,
      ‖u‖ < (G.localMorseNormalForm p hp).radius →
      tcoord (R.amplitude.diffeomorph.symm
        ((B.chart p.1).param (p.2 + G.installedMorseParam p u))) =
          G.localSeparatedTime p (p.2 + G.installedMorseParam p u) := by
  intro p hp u hu
  exact R.time_install ⟨p, hp⟩ (p.2 + G.installedMorseParam p u)
    (hdom p hp u hu) (hcore p hp u hu)


-- @@ L214-214 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L216-216 verbatim
namespace GenericFiniteIFTSurfaceAtlas


-- @@ L218-219 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceChartFamily C ι}


-- @@ L221-237 verbatim
/-- The necessary injectivity and interior conditions produce all disjoint
event cutoffs automatically. -/
theorem nonempty_disjointEventCutoffs
    (G : GenericFiniteIFTSurfaceAtlas B)
    (hinj : Set.InjOn
      (fun p : Σ _ : ι, E₂ => (B.chart p.1).param p.2)
      (G.criticalPoints : Set (Σ _ : ι, E₂)))
    (hinterior : ∀ p (_hp : p ∈ G.criticalPoints),
      1 / 4 < tcoord ((B.chart p.1).param p.2) ∧
        tcoord ((B.chart p.1).param p.2) < 3 / 4) :
    Nonempty (FiniteDisjointMiddleCutoffs G.eventAmbientPoint) := by
  apply FiniteDisjointMiddleCutoffs.exists_of_injective_interior
  · intro p q hpq
    apply Subtype.ext
    exact hinj p.2 q.2 hpq
  · intro p
    exact hinterior p.1 p.2


-- @@ L239-239 verbatim
end GenericFiniteIFTSurfaceAtlas


-- @@ L241-241 verbatim
end Submission
