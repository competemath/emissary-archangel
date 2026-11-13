import Submission.MorseAtlasAssembly
import Submission.LocalIFTSurfaceCoverExistence
import Submission.MorseGlobalValueSeparation


-- @@ L5-29 verbatim
/-!
# Existence interface for signed Morse position

This file specializes `MorseAtlasAssemblyContract` to a genuine signed framed
level cobordism, one concrete vertical amplitude, and an actual finite family of
IFT surface charts.  All bookkeeping is constructed here: the signed pullback,
the installed event records, the assembly contract, the Morse atlas, and the
finite (labeled) Morse position.

`SignedMorseGeometry` remains the compatibility interface for the original
generic-atlas route.  Scalar Morse normal forms are generated directly from
the proved generic-atlas nondegeneracy theorem.  Its fields isolate the
ambient analytic/geometric statements required by that route:

* splice the local scalar changes into one ambient parametrization and prove
  its local rank characterization and IFT covering property;
* prove that the listed centers are exactly the global critical locus after the
  finite perturbation (the no-new-critical-points theorem).

The shared-cutoff/value-separation route imported below now proves those
global obligations directly.  The final section composes its two vertical
pullbacks into the single `SignedMorsePerturbation` expected downstream and
therefore constructs position data for every signed cobordism without an
extra geometry hypothesis.
-/


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
open Set Function Metric

-- @@ L34-34 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L36-36 verbatim
namespace Submission


-- @@ L38-38 verbatim
variable {n : ℕ}


-- @@ L40-40 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L42-42 verbatim
namespace VerticalAmplitude


-- @@ L44-53 verbatim
/-- Structural form of the existing pointwise composition law: one composite
vertical amplitude gives exactly the cobordism obtained by the two successive
pullbacks.  Proof fields disappear by proof irrelevance. -/
theorem pullback_after_eq (C : FramedLevelCobordism n)
    (a b : VerticalAmplitude (n := n)) :
    (a.after b).pullback C = b.pullback (a.pullback C) := by
  rw [FramedLevelCobordism.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext v
  exact a.pullback_after_G C b v


-- @@ L55-55 verbatim
end VerticalAmplitude


-- @@ L57-57 verbatim
/-! ## The one remaining signed geometric kernel -/


-- @@ L59-99 verbatim
/-- The irreducible geometric obligations for installing a generic finite IFT
atlas in one signed vertical perturbation.

`ambientParam p` is defined for every chart-indexed point so that its value at
zero can serve as a total center function.  Only indices in
`G.criticalPoints` carry proof obligations. -/
structure SignedMorseGeometry
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁)
    {ι : Type*} [Fintype ι]
    (B : FiniteIFTSurfaceChartFamily C.cobordism ι)
    (G : GenericFiniteIFTSurfaceAtlas B) where
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
        timeCritical (amplitude.toVerticalAmplitude.pullback C.cobordism).G ↔ u = 0)
  covers_fiber : ∀ p (hp : p ∈ G.criticalPoints),
    ∃ ε > 0, ∀ v,
      dist v (amplitude.diffeomorph.symm
        ((B.chart p.1).param (p.2 + G.installedMorseParam p 0))) < ε →
      (amplitude.toVerticalAmplitude.pullback C.cobordism).G v = 0 →
      ∃ u, ‖u‖ < (G.localMorseNormalForm p hp).radius ∧
        amplitude.diffeomorph.symm
          ((B.chart p.1).param (p.2 + G.installedMorseParam p u)) = v
  coreCritical_cover : ∀ v,
    v ∈ coreCriticalPoints
      (amplitude.toVerticalAmplitude.pullback C.cobordism) →
    ∃ p, ∃ hp : p ∈ G.criticalPoints, ∃ u,
      ‖u‖ < (G.localMorseNormalForm p hp).radius ∧
      amplitude.diffeomorph.symm
        ((B.chart p.1).param (p.2 + G.installedMorseParam p u)) = v


-- @@ L101-101 verbatim
namespace SignedMorseGeometry


-- @@ L103-107 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  {C : SignedFramedLevelCobordism S₀ S₁}
  {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceChartFamily C.cobordism ι}
  {G : GenericFiniteIFTSurfaceAtlas B}


-- @@ L109-113 verbatim
/-- The concrete signed output; endpoint identifications and the nonvanishing
sign are inherited automatically from `VerticalAmplitude.pullbackSigned`. -/
def signedOutput (R : SignedMorseGeometry C B G) :
    SignedFramedLevelCobordism S₀ S₁ :=
  R.amplitude.toVerticalAmplitude.pullbackSigned C


-- @@ L115-117 verbatim
/-- The perturbed unsigned cobordism underlying `signedOutput`. -/
def output (R : SignedMorseGeometry C B G) : FramedLevelCobordism n :=
  R.amplitude.toVerticalAmplitude.pullback C.cobordism


-- @@ L119-120 verbatim
@[simp] theorem signedOutput_cobordism (R : SignedMorseGeometry C B G) :
    R.signedOutput.cobordism = R.output := rfl


-- @@ L122-124 verbatim
@[simp] theorem signedOutput_source_eq (R : SignedMorseGeometry C B G) :
    R.signedOutput.cobordism.X₀ = X₀ :=
  R.signedOutput.source_eq


-- @@ L126-128 verbatim
@[simp] theorem signedOutput_target_eq (R : SignedMorseGeometry C B G) :
    R.signedOutput.cobordism.X₁ = X₁ :=
  R.signedOutput.target_eq


-- @@ L130-135 verbatim
/-- The actual ambient parametrization: reparametrize the old IFT surface chart
and pull it back through the global vertical diffeomorphism. -/
def ambientParam (R : SignedMorseGeometry C B G) (p : Σ _ : ι, E₂)
    (u : E₂) : EuclideanSpace ℝ (Fin (n + 2)) :=
  R.amplitude.diffeomorph.symm
    ((B.chart p.1).param (p.2 + G.installedMorseParam p u))


-- @@ L137-140 verbatim
/-- Ambient center assigned to a chart-indexed critical point. -/
def center (R : SignedMorseGeometry C B G) (p : Σ _ : ι, E₂) :
    EuclideanSpace ℝ (Fin (n + 2)) :=
  R.ambientParam p 0


-- @@ L142-147 verbatim
theorem ambientParam_smooth (R : SignedMorseGeometry C B G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ContDiffAt ℝ ∞ (R.ambientParam p) 0 := by
  exact R.amplitude.contDiff_equiv_symm.contDiffAt.comp 0
    ((B.chart p.1).param_smooth.contDiffAt.comp 0
      (contDiffAt_const.add (G.installedMorseParam_contDiffAt p hp)))


-- @@ L149-162 verbatim
theorem ambientParam_fiber (R : SignedMorseGeometry C B G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (u : E₂)
    (hu : ‖u‖ < (G.localMorseNormalForm p hp).radius) :
    R.output.G (R.ambientParam p u) = 0 := by
  change C.cobordism.G
    (verticalShift R.amplitude (R.ambientParam p u)) = 0
  have hinv : verticalShift R.amplitude (R.ambientParam p u) =
      (B.chart p.1).param (p.2 + G.installedMorseParam p u) := by
    change R.amplitude.diffeomorph
      (R.amplitude.diffeomorph.symm
        ((B.chart p.1).param (p.2 + G.installedMorseParam p u))) = _
    exact R.amplitude.diffeomorph.apply_symm_apply _
  rw [hinv]
  exact (B.chart p.1).param_fiber _ (R.param_domain p hp u hu)


-- @@ L164-172 verbatim
theorem time_lift (R : SignedMorseGeometry C B G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (u : E₂)
    (hu : ‖u‖ < (G.localMorseNormalForm p hp).radius) :
    tcoord (R.ambientParam p u) =
      recenter (G.localSeparatedTime p) p.2
        ((G.localMorseNormalForm p hp).param u) := by
  rw [ambientParam]
  rw [R.time_install p hp u hu, G.installedMorseParam_eq p hp]
  rfl


-- @@ L174-197 verbatim
/-- Every listed center is a genuine middle-slab critical point.  Membership in
the time-critical locus comes from the local critical model.  The collar
regularity theorems force its time strictly between `1/4` and `3/4`; the fiber
equation used there is supplied by the explicit ambient lift. -/
theorem center_mem_coreCriticalPoints (R : SignedMorseGeometry C B G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.center p ∈ coreCriticalPoints R.output := by
  let N := G.localMorseNormalForm p hp
  have hzero : ‖(0 : E₂)‖ < N.radius := by simpa [N] using N.radius_pos
  have hcrit : R.center p ∈ timeCritical R.output.G := by
    exact (R.critical_model p hp 0 hzero).2 rfl
  have hfiber : R.output.G (R.center p) = 0 :=
    R.ambientParam_fiber p hp 0 hzero
  have hlower : (1 / 4 : ℝ) < tcoord (R.center p) := by
    by_contra h
    have hle : tcoord (R.center p) ≤ 1 / 4 := le_of_not_gt h
    exact hcrit.2
      ((R.output.sliceRegular_of_le_quarter hle) (R.center p) hfiber rfl)
  have hupper : tcoord (R.center p) < (3 / 4 : ℝ) := by
    by_contra h
    have hle : 3 / 4 ≤ tcoord (R.center p) := le_of_not_gt h
    exact hcrit.2
      ((R.output.sliceRegular_of_three_quarter_le hle) (R.center p) hfiber rfl)
  exact ⟨hcrit, ⟨hlower.le, hupper.le⟩⟩


-- @@ L199-214 verbatim
/-- The global cover and the uniqueness clause of each local critical model
show that no covered critical point occurs away from the chart center. -/
theorem coreCriticalPoints_subset_center_image
    (R : SignedMorseGeometry C B G) :
    coreCriticalPoints R.output ⊆
      R.center '' (G.criticalPoints : Set (Σ _ : ι, E₂)) := by
  intro v hv
  obtain ⟨p, hp, u, hu, huv⟩ := R.coreCritical_cover v hv
  have hu0 : u = 0 := by
    apply (R.critical_model p hp u hu).1
    rw [huv]
    exact hv.1
  refine ⟨p, hp, ?_⟩
  rw [center, ambientParam]
  rw [hu0] at huv
  exact huv


-- @@ L216-224 verbatim
/-- Consequently the listed centers are exactly the full compact global
critical locus.  This is derived, not assumed. -/
theorem centers_exact (R : SignedMorseGeometry C B G) :
    R.center '' (G.criticalPoints : Set (Σ _ : ι, E₂)) =
      coreCriticalPoints R.output := by
  apply Set.Subset.antisymm
  · rintro v ⟨p, hp, rfl⟩
    exact R.center_mem_coreCriticalPoints p hp
  · exact R.coreCriticalPoints_subset_center_image


-- @@ L226-239 verbatim
/-- Package one remaining-geometry record as the installation interface used by
`MorseAtlasAssembly`.  The center equation is now definitional. -/
def installedGeometry (R : SignedMorseGeometry C B G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    InstalledMorseEventGeometry (n := n) R.output
      (G.localSeparatedTime p) p.2 (R.center p)
      (G.localMorseNormalForm p hp) where
  ambientParam := R.ambientParam p
  ambientParam_smooth := R.ambientParam_smooth p hp
  ambientParam_zero := rfl
  ambientParam_fiber := fun u hu => R.ambientParam_fiber p hp u hu
  time_lift := R.time_lift p hp
  critical_model := R.critical_model p hp
  covers_fiber := R.covers_fiber p hp


-- @@ L241-248 verbatim
/-- All fields of the general assembly contract are filled from the single
signed geometric kernel. -/
def assemblyContract (R : SignedMorseGeometry C B G) :
    MorseAtlasAssemblyContract (n := n) G where
  output := R.output
  center := R.center
  geometry := R.installedGeometry
  centers_exact := R.centers_exact


-- @@ L250-253 verbatim
/-- The actual signed Morse perturbation promised by the perturbation stage. -/
def perturbation (R : SignedMorseGeometry C B G) : SignedMorsePerturbation C where
  amplitude := R.amplitude.toVerticalAmplitude
  atlas := R.assemblyContract.toMorseAtlas


-- @@ L255-257 verbatim
@[simp] theorem perturbation_signedCobordism
    (R : SignedMorseGeometry C B G) :
    R.perturbation.signedCobordism = R.signedOutput := rfl


-- @@ L259-262 verbatim
/-- Public finite event schedule on the perturbed signed bridge. -/
def position (R : SignedMorseGeometry C B G) :
    MorsePosition R.signedOutput.cobordism :=
  R.assemblyContract.toMorsePosition


-- @@ L264-267 verbatim
/-- The north/south labeled schedule is free once the signed pullback exists. -/
def labeledPosition (R : SignedMorseGeometry C B G) :
    LabeledMorsePosition R.signedOutput.cobordism :=
  R.perturbation.labeledPosition


-- @@ L269-271 verbatim
theorem nonempty_position (R : SignedMorseGeometry C B G) :
    Nonempty (MorsePosition R.signedOutput.cobordism) :=
  ⟨R.position⟩


-- @@ L273-275 verbatim
theorem nonempty_labeledPosition (R : SignedMorseGeometry C B G) :
    Nonempty (LabeledMorsePosition R.signedOutput.cobordism) :=
  ⟨R.labeledPosition⟩


-- @@ L277-277 verbatim
end SignedMorseGeometry


-- @@ L279-279 verbatim
/-! ## Public existence theorems -/


-- @@ L281-288 verbatim
/-- A pre-existing `SignedMorsePerturbation` already contains the verified
atlas, hence always exposes a finite Morse position. -/
theorem SignedMorsePerturbation.nonempty_position
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    {C : SignedFramedLevelCobordism S₀ S₁}
    (P : SignedMorsePerturbation C) :
    Nonempty (MorsePosition P.signedCobordism.cobordism) :=
  ⟨P.atlas.toMorsePosition⟩


-- @@ L290-304 verbatim
/-- Finite IFT charts plus the proved Sard genericity theorem reduce existence
of a signed Morse perturbation to `SignedMorseGeometry` and nothing else. -/
theorem exists_signedMorsePerturbation_of_finiteIFT
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁)
    {ι : Type*} [Fintype ι]
    (B : FiniteIFTSurfaceChartFamily C.cobordism ι)
    {εgrad εtime : ℝ} (hεgrad : 0 < εgrad) (hεtime : 0 < εtime)
    (hgeometry : ∀ G : GenericFiniteIFTSurfaceAtlas B,
      Nonempty (SignedMorseGeometry C B G)) :
    ∃ P : SignedMorsePerturbation C,
      Nonempty (MorsePosition P.signedCobordism.cobordism) := by
  obtain ⟨G⟩ := exists_genericFiniteIFTSurfaceAtlas B hεgrad hεtime
  obtain ⟨R⟩ := hgeometry G
  exact ⟨R.perturbation, R.nonempty_position⟩


-- @@ L306-319 verbatim
/-- Labeled version used directly by the signed bridge event argument. -/
theorem exists_labeledMorsePosition_of_finiteIFT
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁)
    {ι : Type*} [Fintype ι]
    (B : FiniteIFTSurfaceChartFamily C.cobordism ι)
    {εgrad εtime : ℝ} (hεgrad : 0 < εgrad) (hεtime : 0 < εtime)
    (hgeometry : ∀ G : GenericFiniteIFTSurfaceAtlas B,
      Nonempty (SignedMorseGeometry C B G)) :
    ∃ P : SignedMorsePerturbation C,
      Nonempty (LabeledMorsePosition P.signedCobordism.cobordism) := by
  obtain ⟨G⟩ := exists_genericFiniteIFTSurfaceAtlas B hεgrad hεtime
  obtain ⟨R⟩ := hgeometry G
  exact ⟨R.perturbation, R.nonempty_labeledPosition⟩


-- @@ L321-321 verbatim
/-! ## Assumption-free shared-cutoff route -/


-- @@ L323-351 verbatim
/-- Every signed framed cobordism admits one collar-preserving vertical
perturbation whose output carries a finite Morse position.  Internally the
proved construction uses two small diffeomorphisms; `VerticalAmplitude.after`
packages them as the single amplitude required by `SignedMorsePerturbation`. -/
theorem exists_signedMorsePerturbation
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁) :
    ∃ P : SignedMorsePerturbation C,
      Nonempty (MorsePosition P.signedCobordism.cobordism) := by
  obtain ⟨s, ⟨B⟩⟩ := exists_finiteIFTSurfaceCover C.cobordism
  obtain ⟨a, b, U, χ, _ha, _hab, _hb, _hU, ⟨R⟩⟩ :=
    FiniteIFTSurfaceCover.SharedCutoffMorseData.exists_globalCutoffMorseData B
  obtain ⟨S⟩ := R.nonempty_stableCriticalValueShiftData
  let T := S.toCriticalValueShiftData
  let A : VerticalAmplitude (n := n) :=
    R.amplitude.toVerticalAmplitude.after T.amplitude.toVerticalAmplitude
  have houtput : A.pullback C.cobordism = T.output := by
    dsimp [A, T]
    rw [FiniteIFTSurfaceCover.SharedCutoffMorseData.CriticalValueShiftData.output,
      FiniteIFTSurfaceCover.SharedCutoffMorseData.output]
    exact VerticalAmplitude.pullback_after_eq C.cobordism
      R.amplitude.toVerticalAmplitude
      S.toCriticalValueShiftData.amplitude.toVerticalAmplitude
  let P : SignedMorsePerturbation C := {
    amplitude := A
    atlas := by
      rw [houtput]
      exact S.toMorseAtlas }
  exact ⟨P, ⟨P.atlas.toMorsePosition⟩⟩


-- @@ L353-361 verbatim
/-- The same assumption-free perturbation automatically carries the signed
north/south labeling used by the Morse-event pipeline. -/
theorem exists_labeledMorsePosition
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁) :
    ∃ P : SignedMorsePerturbation C,
      Nonempty (LabeledMorsePosition P.signedCobordism.cobordism) := by
  obtain ⟨P, _hposition⟩ := exists_signedMorsePerturbation C
  exact ⟨P, ⟨P.labeledPosition⟩⟩


-- @@ L363-363 verbatim
end Submission
