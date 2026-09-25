import Mathlib.Topology.MetricSpace.PartitionOfUnity
import SphereEversion.Global.SmoothEmbedding


-- @@ L4-4 verbatim
noncomputable section


-- @@ L6-6 verbatim
open scoped Manifold ContDiff


-- @@ L8-8 verbatim
open Set Metric


-- @@ L10-10 verbatim
section


-- @@ L12-18 verbatim
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']


-- @@ L20-32 verbatim
/-- Definition `def:localisation_data`. -/
structure LocalisationData (f : M → M') where
  cont : Continuous f
  ι' : Type*
  N : ℕ
  φ : IndexType N → OpenSmoothEmbedding 𝓘(𝕜, E) E I M
  ψ : ι' → OpenSmoothEmbedding 𝓘(𝕜, E') E' I' M'
  j : IndexType N → ι'
  h₁ : (⋃ i, φ i '' ball (0 : E) 1) = univ
  h₂ : (⋃ i', ψ i' '' ball (0 : E') 1) = univ
  h₃ : ∀ i, range (f ∘ φ i) ⊆ ψ (j i) '' ball (0 : E') 1
  h₄ : LocallyFinite fun i' ↦ range (ψ i')
  lf_φ : LocallyFinite fun i ↦ range (φ i)


-- @@ L34-34 verbatim
namespace LocalisationData


-- @@ L36-36 verbatim
variable {f : M → M'} {I I'} (ld : LocalisationData I I' f)


-- @@ L38-39 verbatim
abbrev ψj : IndexType ld.N → OpenSmoothEmbedding 𝓘(𝕜, E') E' I' M' :=
  ld.ψ ∘ ld.j


-- @@ L41-43 verbatim
/-- The type indexing the source charts of the given localisation data. -/
def ι (L : LocalisationData I I' f) :=
  IndexType L.N


-- @@ L45-50 verbatim
omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem iUnion_succ' {β : Type*} (s : ld.ι → Set β) (i : IndexType ld.N) :
    (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i := by
  simp only [(fun _ ↦ le_iff_lt_or_eq : ∀ j, j ≤ i ↔ j < i ∨ j = i)]
  erw [biUnion_union, biUnion_singleton]
  rfl


-- @@ L52-52 verbatim
open Filter


-- @@ L54-54 verbatim
end LocalisationData


-- @@ L56-56 verbatim
end


-- @@ L58-58 verbatim
section


-- @@ L60-60 verbatim
open ModelWithCorners


-- @@ L62-69 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [SigmaCompactSpace M] [LocallyCompactSpace M] [T2Space M]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [Boundaryless I] [Nonempty M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [Boundaryless I']
  {M' : Type*} [MetricSpace M'] [SigmaCompactSpace M'] [LocallyCompactSpace M']
  [Nonempty M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']


-- @@ L71-71 verbatim
variable (M')


-- @@ L73-78 verbatim
theorem nice_atlas_target :
    ∃ n,
      ∃ ψ : IndexType n → OpenSmoothEmbedding 𝓘(ℝ, E') E' I' M',
        (LocallyFinite fun i' ↦ range (ψ i')) ∧ (⋃ i', ψ i' '' ball 0 1) = univ :=
  let h := nice_atlas E' I' (fun _ : Unit ↦ @isOpen_univ M' _) (by simp [eq_univ_iff_forall])
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2⟩


-- @@ L80-84 verbatim
/-- A collection of charts on a manifold `M'` which are smooth open embeddings with domain the whole
model space, and which cover the manifold when restricted in each case to the unit ball. -/
def targetCharts (i' : IndexType (nice_atlas_target E' I' M').choose) :
    OpenSmoothEmbedding 𝓘(ℝ, E') E' I' M' :=
  (nice_atlas_target E' I' M').choose_spec.choose i'


-- @@ L86-87 verbatim
theorem targetCharts_cover : (⋃ i', targetCharts E' I' M' i' '' ball (0 : E') 1) = univ :=
  (nice_atlas_target E' I' M').choose_spec.choose_spec.2


-- @@ L89-89 verbatim
variable (E) {M'}

-- @@ L90-90 verbatim
variable {f : M → M'} (hf : Continuous f)


-- @@ L92-100 verbatim
include hf in
theorem nice_atlas_domain :
    ∃ n,
      ∃ φ : IndexType n → OpenSmoothEmbedding 𝓘(ℝ, E) E I M,
        (∀ i, ∃ i', range (φ i) ⊆ f ⁻¹' (targetCharts E' I' M' i' '' ball (0 : E') 1)) ∧
          (LocallyFinite fun i ↦ range (φ i)) ∧ (⋃ i, φ i '' ball 0 1) = univ :=
  nice_atlas E I
    (fun i' ↦ ((targetCharts E' I' M' i').isOpenMap (ball 0 1) isOpen_ball).preimage hf)
    (by rw [← preimage_iUnion, targetCharts_cover, preimage_univ])


-- @@ L102-118 verbatim
/-- Lemma `lem:ex_localisation`
  Any continuous map between manifolds has some localisation data. -/
def stdLocalisationData : LocalisationData I I' f where
  cont := hf
  N := (nice_atlas_domain E I E' I' hf).choose
  ι' := IndexType (nice_atlas_target E' I' M').choose
  φ := (nice_atlas_domain E I E' I' hf).choose_spec.choose
  ψ := targetCharts E' I' M'
  j i := ((nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.1 i).choose
  h₁ := (nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.2.2
  h₂ := targetCharts_cover E' I' M'
  h₃ i := by
    rw [range_comp]
    rintro - ⟨y, hy, rfl⟩
    exact ((nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.1 i).choose_spec hy
  h₄ := (nice_atlas_target E' I' M').choose_spec.choose_spec.1
  lf_φ := (nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.2.1


-- @@ L120-120 verbatim
variable {E E' I I'}


-- @@ L122-122 verbatim
section


-- @@ L124-126 verbatim
omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [LocallyCompactSpace M] [T2Space M]
  [I.Boundaryless] [Nonempty M] [IsManifold I ∞ M] [I'.Boundaryless]
  [SigmaCompactSpace M'] [LocallyCompactSpace M'] [Nonempty M'] [IsManifold I' ∞ M']


-- @@ L128-146 verbatim
/-- Lemma `lem:localisation_stability`. -/
theorem localisation_stability {f : M → M'} (ld : LocalisationData I I' f) :
    ∃ (ε : M → ℝ) (_hε : ∀ m, 0 < ε m) (_hε' : Continuous ε),
      ∀ (g : M → M') (_hg : ∀ m, dist (g m) (f m) < ε m) (i),
        range (g ∘ ld.φ i) ⊆ range (ld.ψj i) := by
  let K : ld.ι' → Set M' := fun i ↦ ld.ψ i '' closedBall 0 1
  let U : ld.ι' → Set M' := fun i ↦ range <| ld.ψ i
  have hK : ∀ i, IsClosed (K i) := fun i ↦
    IsCompact.isClosed (IsCompact.image (isCompact_closedBall 0 1) (ld.ψ i).continuous)
  have hK' : LocallyFinite K := ld.h₄.subset fun i ↦ image_subset_range (ld.ψ i) (closedBall 0 1)
  have hU : ∀ i, IsOpen (U i) := fun i ↦ (ld.ψ i).isOpen_range
  have hKU : ∀ i, K i ⊆ U i := fun i ↦ image_subset_range _ _
  obtain ⟨δ, hδ₀, hδ₁⟩ := exists_continuous_real_forall_closedBall_subset hK hU hKU hK'
  have := ld.cont
  refine ⟨δ ∘ f, fun m ↦ hδ₀ (f m), by fun_prop, fun g hg i ↦ ?_⟩
  rintro - ⟨e, rfl⟩
  have hi : f (ld.φ i e) ∈ K (ld.j i) :=
    image_mono ball_subset_closedBall (ld.h₃ i (mem_range_self e))
  exact hδ₁ (ld.j i) (f <| ld.φ i e) hi (le_of_lt (hg _))


-- @@ L148-148 verbatim
namespace LocalisationData


-- @@ L150-151 verbatim
protected def ε (ld : LocalisationData I I' f) : M → ℝ :=
  (localisation_stability ld).choose


-- @@ L153-154 verbatim
theorem ε_pos (ld : LocalisationData I I' f) : ∀ m, 0 < ld.ε m :=
  (localisation_stability ld).choose_spec.choose


-- @@ L156-157 verbatim
theorem ε_cont (ld : LocalisationData I I' f) : Continuous ld.ε :=
  (localisation_stability ld).choose_spec.choose_spec.choose


-- @@ L159-162 verbatim
theorem ε_spec (ld : LocalisationData I I' f) :
    ∀ (g : M → M') (_hg : ∀ m, dist (g m) (f m) < ld.ε m) (i : ld.ι),
      range (g ∘ ld.φ i) ⊆ range (ld.ψj i) :=
  (localisation_stability ld).choose_spec.choose_spec.choose_spec


-- @@ L164-164 verbatim
end LocalisationData

-- @@ L165-165 verbatim
end


-- @@ L167-167 verbatim
variable (I I')


-- @@ L169-183 verbatim
open LocalisationData in
theorem _root_.exists_stability_dist {f : M → M'} (hf : Continuous f) :
    ∃ ε : M → ℝ, (∀ m, 0 < ε m) ∧ Continuous ε ∧
      ∀ x : M,
        ∃ φ : OpenSmoothEmbedding 𝓘(ℝ, E) E I M,
        ∃ ψ : OpenSmoothEmbedding 𝓘(ℝ, E') E' I' M',
          x ∈ range φ ∧
          ∀ (g : M → M'), (∀ m, dist (g m) (f m) < ε m) → range (g ∘ φ) ⊆ range ψ := by
  let L := stdLocalisationData E I E' I' hf
  use L.ε, L.ε_pos, L.ε_cont
  intro x
  rcases mem_iUnion.mp <| eq_univ_iff_forall.mp L.h₁ x with ⟨i, hi⟩
  use L.φ i, L.ψj i, mem_range_of_mem_image (φ L i) _ hi, ?_
  have := L.ε_spec
  tauto


-- @@ L185-185 verbatim
end
