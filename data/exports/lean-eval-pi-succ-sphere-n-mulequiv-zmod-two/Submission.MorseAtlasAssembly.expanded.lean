import Submission.MorseGenericity2D
import Submission.MorseLemma2D
import Submission.MorseNondegenerateBridge


-- @@ L5-21 verbatim
/-!
# Assembly of the generic finite IFT atlas

`MorseGenericity2D` supplies a finite chart-indexed critical locus, proves every
point nondegenerate, and separates its local critical values.  `MorseLemma2D`
turns suitable local coordinate input into an exact scalar quadratic normal
form.  This file isolates the remaining ambient geometry in one contract and
then constructs `StandardMorseEventAt`, `MorseAtlas`, and `MorsePosition`.

The contract deliberately contains only facts not supplied by those two files:

* construction and globalization of the scalar Morse coordinate input;
* lifting the scalar normal form to a smooth parametrization of the perturbed
  zero surface, including the critical-point rank equivalence and local cover;
* completeness of the finite list (there are no unlisted global critical
  points after splicing the localized perturbations).
-/


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function Metric

-- @@ L26-26 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-30 verbatim
variable {n : ℕ}


-- @@ L32-32 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L33-33 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L35-35 verbatim
namespace GenericFiniteIFTAtlas


-- @@ L37-52 verbatim
/-- The separated scalar function at every listed critical point already has
an exact local Morse normal form.  This is a definition, not an additional
assembly hypothesis: smoothness and nondegeneracy come from the generic atlas,
and `MorseNondegenerateBridge` supplies the constructive normal form. -/
def localMorseNormalForm {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    LocalMorseNormalForm (recenter (G.localSeparatedTime p) p.2) := by
  have hsmooth : ContDiff ℝ ∞ (G.localSeparatedTime p) := by
    change ContDiff ℝ ∞
      (fun u => (G.tilt p.1).tilted u + G.valueShift p)
    rw [(G.tilt p.1).tilted_eq]
    exact (contDiff_chartLinearTilt (A.smooth p.1) (G.tilt p.1).q).add
      contDiff_const
  exact (nonempty_localMorseNormalForm_recenter hsmooth
    (G.localSeparatedTime_nondegenerate p hp)).some


-- @@ L54-62 verbatim
/-- A total parameter family.  At a listed critical point it is the local
Morse inverse parameter; elsewhere the identity is used only to keep the
ambient center function total. -/
def installedMorseParam {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A)
    (p : Σ _ : ι, E₂) : E₂ → E₂ := by
  classical
  exact if hp : p ∈ G.criticalPoints then
    (G.localMorseNormalForm p hp).param else id


-- @@ L64-69 verbatim
theorem installedMorseParam_eq {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    G.installedMorseParam p = (G.localMorseNormalForm p hp).param := by
  classical
  simp only [installedMorseParam, dif_pos hp]


-- @@ L71-76 verbatim
theorem installedMorseParam_contDiffAt {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ContDiffAt ℝ ∞ (G.installedMorseParam p) 0 := by
  rw [G.installedMorseParam_eq p hp]
  exact (G.localMorseNormalForm p hp).param_contDiffAt


-- @@ L78-78 verbatim
end GenericFiniteIFTAtlas


-- @@ L80-80 verbatim
/-! ## One exact scalar normal form installed in the ambient zero surface -/


-- @@ L82-102 verbatim
/-- The ambient geometric data still required after the scalar local Morse
lemma.  The field `time_lift` is the only compatibility equation: it says the
ambient time is exactly the scalar normal form produced in `MorseLemma2D`.

Global smoothness of `ambientParam`, the rank characterization in
`critical_model`, and `covers_fiber` are the precise IFT/globalization facts
which are not consequences of the scalar lemma alone. -/
structure InstalledMorseEventGeometry
    (C : FramedLevelCobordism n) (f : E₂ → ℝ) (base : E₂)
    (center : EuclideanSpace ℝ (Fin (n + 2)))
    (N : LocalMorseNormalForm (recenter f base)) where
  ambientParam : E₂ → E'
  ambientParam_smooth : ContDiffAt ℝ ∞ ambientParam 0
  ambientParam_zero : ambientParam 0 = center
  ambientParam_fiber : ∀ u, ‖u‖ < N.radius → C.G (ambientParam u) = 0
  time_lift : ∀ u, ‖u‖ < N.radius →
    tcoord (ambientParam u) = recenter f base (N.param u)
  critical_model : ∀ u, ‖u‖ < N.radius →
    (ambientParam u ∈ timeCritical C.G ↔ u = 0)
  covers_fiber : ∃ ε > 0, ∀ v, dist v center < ε → C.G v = 0 →
    ∃ u, ‖u‖ < N.radius ∧ ambientParam u = v


-- @@ L104-104 verbatim
namespace InstalledMorseEventGeometry


-- @@ L106-108 verbatim
variable {C : FramedLevelCobordism n} {f : E₂ → ℝ} {base : E₂}
  {center : EuclideanSpace ℝ (Fin (n + 2))}
  {N : LocalMorseNormalForm (recenter f base)}


-- @@ L110-117 verbatim
/-- The center time is the separated critical value of the scalar chart. -/
theorem center_time
    (I : InstalledMorseEventGeometry (n := n) C f base center N) :
    tcoord center = f base := by
  have hzero : ‖(0 : E₂)‖ < N.radius := by simpa using N.radius_pos
  have h := I.time_lift 0 hzero
  rw [I.ambientParam_zero, N.param_zero] at h
  simpa [recenter] using h


-- @@ L119-140 verbatim
/-- The scalar exact normal form and the ambient installation contract assemble
to the exact event chart consumed by `MorseAtlas`. -/
def toStandardMorseEventAt
    (I : InstalledMorseEventGeometry (n := n) C f base center N) :
    StandardMorseEventAt C center where
  index := N.index
  radius := N.radius
  radius_pos := N.radius_pos
  param := I.ambientParam
  param_smooth := I.ambientParam_smooth
  param_zero := I.ambientParam_zero
  param_fiber := I.ambientParam_fiber
  time_model := by
    intro u hu
    calc
      tcoord (I.ambientParam u) = recenter f base (N.param u) := I.time_lift u hu
      _ = recenter f base 0 + morseQuadratic N.index (u 0, u 1) := N.exact u hu
      _ = f base + morseQuadratic N.index (u 0, u 1) := by simp [recenter]
      _ = tcoord center + morseQuadratic N.index (u 0, u 1) := by
        rw [I.center_time]
  critical_model := I.critical_model
  covers_fiber := I.covers_fiber


-- @@ L142-142 verbatim
end InstalledMorseEventGeometry


-- @@ L144-144 verbatim
/-! ## Global finite assembly contract -/


-- @@ L146-159 verbatim
/-- Minimal interface between the proved chart-level genericity theorem and a
global perturbed cobordism.  Each finite critical index receives the scalar
Morse-lemma input and an ambient installation of the resulting normal form.
`centers_exact` is the global no-new-critical-points/splicing obligation. -/
structure MorseAtlasAssemblyContract {ι : Type*} [Fintype ι]
    {A : FiniteIFTChartFamily ι} (G : GenericFiniteIFTAtlas A) where
  output : FramedLevelCobordism n
  center : (Σ _ : ι, E₂) → EuclideanSpace ℝ (Fin (n + 2))
  geometry : ∀ p (hp : p ∈ G.criticalPoints),
    InstalledMorseEventGeometry (n := n) output
      (G.localSeparatedTime p) p.2 (center p)
      (G.localMorseNormalForm p hp)
  centers_exact : center '' (G.criticalPoints : Set (Σ _ : ι, E₂)) =
    coreCriticalPoints output


-- @@ L161-161 verbatim
namespace MorseAtlasAssemblyContract


-- @@ L163-164 verbatim
variable {ι : Type*} [Fintype ι] {A : FiniteIFTChartFamily ι}
  {G : GenericFiniteIFTAtlas A}


-- @@ L166-169 verbatim
/-- The exact standard event attached to a finite generic critical index. -/
def event (D : MorseAtlasAssemblyContract (n := n) G) (p : Σ _ : ι, E₂)
    (hp : p ∈ G.criticalPoints) : StandardMorseEventAt D.output (D.center p) :=
  (D.geometry p hp).toStandardMorseEventAt


-- @@ L171-176 verbatim
/-- Ambient time at an installed center is the separated local critical value. -/
theorem center_time (D : MorseAtlasAssemblyContract (n := n) G)
    (p : Σ _ : ι, E₂)
    (hp : p ∈ G.criticalPoints) :
    tcoord (D.center p) = G.localSeparatedTime p p.2 :=
  (D.geometry p hp).center_time


-- @@ L178-187 verbatim
/-- The ambient event times are pairwise distinct.  This is the exact point at
which the finite scalar separation theorem is consumed. -/
theorem center_time_injective (D : MorseAtlasAssemblyContract (n := n) G) :
    Set.InjOn (fun p : Σ _ : ι, E₂ => tcoord (D.center p))
      (G.criticalPoints : Set (Σ _ : ι, E₂)) := by
  intro p hp q hq hpq
  apply G.localCriticalValues_injective hp hq
  change G.localSeparatedTime p p.2 = G.localSeparatedTime q q.2
  rw [← D.center_time p hp, ← D.center_time q hq]
  exact hpq


-- @@ L189-204 verbatim
/-- The installed standard events and the completeness contract produce the
global Morse atlas. -/
theorem toMorseAtlas (D : MorseAtlasAssemblyContract (n := n) G) :
    MorseAtlas D.output where
  localModel := by
    intro v hv
    rw [← D.centers_exact] at hv
    rcases hv with ⟨p, hp, rfl⟩
    exact ⟨D.event p hp⟩
  distinct_times := by
    intro v hv w hw hvw
    rw [← D.centers_exact] at hv hw
    rcases hv with ⟨p, hp, rfl⟩
    rcases hw with ⟨q, hq, rfl⟩
    have hpq : p = q := D.center_time_injective hp hq hvw
    rw [hpq]


-- @@ L206-210 verbatim
/-- Final finite Morse-position package.  Finiteness is now a theorem of
`MorseAtlas`: exact event charts isolate the compact global critical locus. -/
def toMorsePosition (D : MorseAtlasAssemblyContract (n := n) G) :
    MorsePosition D.output :=
  D.toMorseAtlas.toMorsePosition


-- @@ L212-215 verbatim
theorem toMorsePosition_centers_exact
    (D : MorseAtlasAssemblyContract (n := n) G) :
    (D.toMorsePosition.centers : Set E') = coreCriticalPoints D.output :=
  D.toMorsePosition.centers_exact


-- @@ L217-220 verbatim
theorem toMorsePosition_distinct_times
    (D : MorseAtlasAssemblyContract (n := n) G) :
    Set.InjOn tcoord (coreCriticalPoints D.output) :=
  D.toMorsePosition.distinct_times


-- @@ L222-222 verbatim
end MorseAtlasAssemblyContract


-- @@ L224-224 verbatim
end Submission
