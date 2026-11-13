import Mathlib
import Submission.LocalIFTSurfaceCoverExistence
import Submission.PerturbedIFTSurfaceCover
import Submission.MorseInvariantAssembly


-- @@ L6-25 verbatim
/-!
# Global compatibility for a finite Morse installation

The chartwise Sard theorem chooses independent linear tilts.  On overlaps those
choices do not automatically define one ambient vertical perturbation.  This
file isolates the exact compatibility condition with a *single* global
amplitude.

`FiniteCoverSignedMorseCompatibility` replaces the raw global-cover field of
`SignedMorseGeometry` by an ownership condition on the compact cores of an
actual `FiniteIFTSurfaceCover`.  The topological part of global coverage is then
a theorem: `PerturbedIFTSurfaceCover` supplies a compact-core representation of
every critical point, and the ownership condition moves it into one installed
Morse neighborhood.

The final section records two necessary overlap conditions already forced by
`SignedMorseGeometry`.  In particular, independently chosen chart data cannot
silently assign two distinct critical indices to the same point of the
original zero surface.
-/


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Set Function Metric

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L32-32 verbatim
namespace Submission


-- @@ L34-34 verbatim
variable {n : ℕ}


-- @@ L36-36 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L37-37 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L39-39 verbatim
/-! ## A finite-cover form of the remaining global compatibility kernel -/


-- @@ L41-86 verbatim
/-- Compatibility of the independently produced local Morse data with one
global vertical amplitude.

The first four fields are the local installation fields of
`SignedMorseGeometry`.  The last field is deliberately phrased on the compact
cores of a genuine finite cover: every core parameter which represents a
global critical point must be owned by one of the installed critical
neighborhoods.  It allows overlapping cover charts, because the owner need not
be the chart in which the point was first represented. -/
structure FiniteCoverSignedMorseCompatibility
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁)
    {ι : Type*} [Fintype ι]
    (B : FiniteIFTSurfaceCover C.cobordism ι)
    (G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily) where
  amplitude : SmallVerticalAmplitude (n := n)
  param_domain : ∀ p (hp : p ∈ G.criticalPoints) u,
    ‖u‖ < (G.localMorseNormalForm p hp).radius →
      p.2 + G.installedMorseParam p u ∈ (B.chart p.1).domain
  time_install : ∀ p (hp : p ∈ G.criticalPoints) u,
    ‖u‖ < (G.localMorseNormalForm p hp).radius →
      tcoord (amplitude.diffeomorph.symm
        ((B.chart p.1).param (p.2 + G.installedMorseParam p u))) =
          G.localSeparatedTime p (p.2 + G.installedMorseParam p u)
  critical_model : ∀ p (hp : p ∈ G.criticalPoints) u,
    ‖u‖ < (G.localMorseNormalForm p hp).radius →
      (amplitude.diffeomorph.symm
          ((B.chart p.1).param (p.2 + G.installedMorseParam p u)) ∈
        timeCritical
          (amplitude.toVerticalAmplitude.pullback C.cobordism).G ↔ u = 0)
  covers_fiber : ∀ p (hp : p ∈ G.criticalPoints),
    ∃ ε > 0, ∀ v,
      dist v (amplitude.diffeomorph.symm
        ((B.chart p.1).param (p.2 + G.installedMorseParam p 0))) < ε →
      (amplitude.toVerticalAmplitude.pullback C.cobordism).G v = 0 →
      ∃ u, ‖u‖ < (G.localMorseNormalForm p hp).radius ∧
        amplitude.diffeomorph.symm
          ((B.chart p.1).param (p.2 + G.installedMorseParam p u)) = v
  critical_owner : ∀ i z, z ∈ B.core i →
    amplitude.diffeomorph.symm ((B.chart i).param z) ∈
      coreCriticalPoints
        (amplitude.toVerticalAmplitude.pullback C.cobordism) →
    ∃ p, ∃ hp : p ∈ G.criticalPoints, ∃ u,
      ‖u‖ < (G.localMorseNormalForm p hp).radius ∧
      (B.chart p.1).param (p.2 + G.installedMorseParam p u) =
        (B.chart i).param z


-- @@ L88-88 verbatim
namespace FiniteCoverSignedMorseCompatibility


-- @@ L90-94 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  {C : SignedFramedLevelCobordism S₀ S₁}
  {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C.cobordism ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L96-121 verbatim
/-- The finite ambient cover supplies the global critical-cover field.  Thus
the ownership clause is exactly the remaining overlap/gluing obligation, not
another compactness assumption. -/
def toSignedMorseGeometry
    (R : FiniteCoverSignedMorseCompatibility C B G) :
    SignedMorseGeometry C B.toSurfaceChartFamily G where
  amplitude := R.amplitude
  param_domain := R.param_domain
  time_install := R.time_install
  critical_model := R.critical_model
  covers_fiber := R.covers_fiber
  coreCritical_cover := by
    intro v hv
    obtain ⟨i, z, hz, hzv⟩ :=
      B.exists_pullback_chart_parameter_of_coreCritical R.amplitude hv
    have hzcrit :
        R.amplitude.diffeomorph.symm ((B.chart i).param z) ∈
          coreCriticalPoints
            (R.amplitude.toVerticalAmplitude.pullback C.cobordism) := by
      rw [hzv]
      exact hv
    obtain ⟨p, hp, u, hu, hup⟩ := R.critical_owner i z hz hzcrit
    refine ⟨p, hp, u, hu, ?_⟩
    change R.amplitude.diffeomorph.symm
      ((B.chart p.1).param (p.2 + G.installedMorseParam p u)) = v
    rw [hup, hzv]


-- @@ L123-145 verbatim
/-- Conversely, any already installed `SignedMorseGeometry` satisfies the
finite-cover ownership contract.  Hence the new contract is an exact
factorization of the old global-cover field through the proved finite-cover
theorem, rather than an additional geometric hypothesis. -/
def ofSignedMorseGeometry
    (R : SignedMorseGeometry C B.toSurfaceChartFamily G) :
    FiniteCoverSignedMorseCompatibility C B G where
  amplitude := R.amplitude
  param_domain := R.param_domain
  time_install := R.time_install
  critical_model := R.critical_model
  covers_fiber := R.covers_fiber
  critical_owner := by
    intro i z _hz hzcrit
    obtain ⟨p, hp, u, hu, huv⟩ := R.coreCritical_cover
      (v := R.amplitude.diffeomorph.symm ((B.chart i).param z)) hzcrit
    refine ⟨p, hp, u, hu, ?_⟩
    apply R.amplitude.diffeomorph.symm.injective
    change R.amplitude.diffeomorph.symm
      ((B.toSurfaceChartFamily.chart p.1).param
        (p.2 + G.installedMorseParam p u)) =
      R.amplitude.diffeomorph.symm ((B.chart i).param z) at huv
    exact huv


-- @@ L147-150 verbatim
/-- The signed perturbation determined by the compatible global amplitude. -/
def perturbation (R : FiniteCoverSignedMorseCompatibility C B G) :
    SignedMorsePerturbation C :=
  R.toSignedMorseGeometry.perturbation


-- @@ L152-155 verbatim
/-- Its finite chronological Morse position. -/
def position (R : FiniteCoverSignedMorseCompatibility C B G) :
    MorsePosition R.perturbation.signedCobordism.cobordism :=
  R.toSignedMorseGeometry.position


-- @@ L157-163 verbatim
/-- Once the already separated local events have framed excisions, the
compatible finite cover gives the actual delta resolution consumed by the
global invariant theorem. -/
def toDeltaResolution (R : FiniteCoverSignedMorseCompatibility C B G)
    (hn : 2 ≤ n) (K : R.position.FramedEventExcisions hn) :
    SignedMorseDeltaResolution C hn :=
  R.toSignedMorseGeometry.toDeltaResolution hn K


-- @@ L165-165 verbatim
end FiniteCoverSignedMorseCompatibility


-- @@ L167-167 verbatim
/-! ## Necessary overlap conditions for any installed geometry -/


-- @@ L169-169 verbatim
namespace SignedMorseGeometry


-- @@ L171-175 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  {C : SignedFramedLevelCobordism S₀ S₁}
  {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceChartFamily C.cobordism ι}
  {G : GenericFiniteIFTSurfaceAtlas B}


-- @@ L177-184 verbatim
/-- At an installed critical index, the ambient center is the pullback of the
unrecentered chart point. -/
theorem center_eq_pullback_chart_point (R : SignedMorseGeometry C B G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.center p =
      R.amplitude.diffeomorph.symm ((B.chart p.1).param p.2) := by
  rw [center, ambientParam, G.installedMorseParam_eq p hp,
    (G.localMorseNormalForm p hp).param_zero, add_zero]


-- @@ L186-202 verbatim
/-- A single ambient amplitude forces the installed scalar times to agree
whenever two local installed parametrizations describe the same point of the
original zero surface.  This is the precise cocycle condition absent from a
mere list of independent chartwise Sard tilts. -/
theorem installed_time_eq_of_chart_overlap
    (R : SignedMorseGeometry C B G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (u : E₂)
    (hu : ‖u‖ < (G.localMorseNormalForm p hp).radius)
    (q : Σ _ : ι, E₂) (hq : q ∈ G.criticalPoints) (w : E₂)
    (hw : ‖w‖ < (G.localMorseNormalForm q hq).radius)
    (hoverlap :
      (B.chart p.1).param (p.2 + G.installedMorseParam p u) =
        (B.chart q.1).param (q.2 + G.installedMorseParam q w)) :
    G.localSeparatedTime p (p.2 + G.installedMorseParam p u) =
      G.localSeparatedTime q (q.2 + G.installedMorseParam q w) := by
  rw [← R.time_install p hp u hu, ← R.time_install q hq w hw,
    hoverlap]


-- @@ L204-216 verbatim
/-- Distinct generic critical indices cannot represent the same point of the
original zero surface in any genuine global installation.  This gives a
formal obstruction to treating an overlapping finite cover as a disjoint list
of independently perturbable charts. -/
theorem critical_chart_point_injective (R : SignedMorseGeometry C B G) :
    Set.InjOn (fun p : Σ _ : ι, E₂ => (B.chart p.1).param p.2)
      (G.criticalPoints : Set (Σ _ : ι, E₂)) := by
  intro p hp q hq hpq
  change (B.chart p.1).param p.2 = (B.chart q.1).param q.2 at hpq
  apply R.assemblyContract.center_time_injective hp hq
  change tcoord (R.center p) = tcoord (R.center q)
  rw [R.center_eq_pullback_chart_point p hp,
    R.center_eq_pullback_chart_point q hq, hpq]


-- @@ L218-218 verbatim
end SignedMorseGeometry


-- @@ L220-220 verbatim
end Submission
