/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Compact


-- @@ L11-13 verbatim
/-!
# LeanPool.RiemannMappingTheorem.Uniform
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Set Filter UniformSpace Function Uniformity Topology SetRel


-- @@ L19-19 verbatim
variable {ι α β : Type*} {a : α} {s t : Set α} {x u v : Set (α × α)}


-- @@ L21-22 verbatim
lemma symmetricRel_of (h : ∀ {a b : α}, (a, b) ∈ x → (b, a) ∈ x) : SetRel.IsSymm x where
  symm _ _ := h


-- @@ L24-24 verbatim
namespace UniformSpace -- uniform thickening


-- @@ L26-28 verbatim
/-- The `U`-thickening of `S`: the union of `U`-balls around each point of
`S`. Equals `{a | ∃ x ∈ S, (x, a) ∈ U}`. -/
def thickening (U : Set (α × α)) (S : Set α) : Set α := ⋃ x ∈ S, ball x U


-- @@ L30-31 verbatim
lemma mem_thickening : a ∈ thickening u s ↔ ∃ x ∈ s, (x, a) ∈ u := by
  simp only [thickening, ball, mem_iUnion, Set.mem_preimage, exists_prop]


-- @@ L33-34 verbatim
@[simp] lemma thickening_singleton : thickening u {a} = ball a u := by
  simp only [thickening, mem_singleton_iff, iUnion_iUnion_eq_left]


-- @@ L36-40 verbatim
@[simp] lemma monotone_thickening : Monotone (thickening · s) := by
  intro u v huv
  apply iUnion₂_mono
  simp only [ball] at huv ⊢
  exact fun _ _ => preimage_mono huv


-- @@ L42-43 verbatim
lemma thickening_mono : Monotone (thickening u) :=
  fun _ _ h => iUnion₂_mono' (fun a ha => ⟨a, h ha, subset_rfl⟩)


-- @@ L45-46 verbatim
@[simp] lemma thickening_comp : thickening v (thickening u s) = thickening (u ○ v) s := by
  ext; simp [thickening, ball]


-- @@ L48-50 verbatim
lemma disjoint_ball_iff : Disjoint (ball a u) t ↔ ∀ b ∈ t, (a, b) ∉ u := by
  rw [← compl_compl (ball a u), disjoint_compl_left_iff_subset]
  rfl


-- @@ L52-53 verbatim
lemma thickening_inter_eq_empty : thickening u s ∩ t = ∅ ↔ ∀ a ∈ s, ∀ b ∈ t, (a, b) ∉ u := by
  simp [thickening, ← disjoint_iff_inter_eq_empty, disjoint_ball_iff]


-- @@ L55-58 verbatim
lemma thickening_inter_eq_empty_comm (hu : SetRel.IsSymm u) :
    thickening u s ∩ t = ∅ ↔ s ∩ thickening u t = ∅ := by
  rw [inter_comm s, thickening_inter_eq_empty, thickening_inter_eq_empty]
  constructor <;> exact fun h a ha b hb hab => h b hb a ha (SetRel.symm u hab)


-- @@ L60-64 verbatim
lemma thickening_inter_thickening_eq_empty_of_comp (hv : SetRel.IsSymm v) (hvu : v ○ v ⊆ u)
    (hST : thickening u s ∩ t = ∅) :
    thickening v s ∩ thickening v t = ∅ := by
  simp only [←thickening_inter_eq_empty_comm hv, thickening_comp]
  exact subset_eq_empty (inter_subset_inter_left _ (monotone_thickening hvu)) hST


-- @@ L66-68 verbatim
end UniformSpace

-----------------------------------------------------------------------------


-- @@ L70-74 verbatim
/-- The uniform neighbourhood filter of a set `s`: filter of supersets
of `U`-thickenings of `s` for entourages `U`. Strengthens `𝓝ˢ s` for
locally uniform statements. -/
def uniformNhdsSet [UniformSpace α] (s : Set α) : Filter α :=
  Filter.lift' (𝓤 α) (UniformSpace.thickening · s)


-- @@ L76-77 verbatim
/-- Notation for `uniformNhdsSet`, the uniform neighbourhood filter. -/
scoped[Uniformity] notation "𝓝ᵘ" => uniformNhdsSet


-- @@ L79-79 verbatim
namespace UniformSpace -- uniformNhdsSet


-- @@ L81-81 verbatim
variable [UniformSpace α]


-- @@ L83-84 expanded
lemma thickening_mem_uniform_nhds_set (hu : u ∈ 𝓤 α) : thickening u s ∈ uniformNhdsSet s :=
  (mem_lift'_sets monotone_thickening).mpr ⟨u, hu, subset_rfl⟩


-- @@ L86-87 expanded
lemma uniform_nhds_set_mono {s t : Set α} (h : s ⊆ t) : uniformNhdsSet s ≤ uniformNhdsSet t :=
  lift'_mono le_rfl (fun _ => thickening_mono h)


-- @@ L89-90 expanded
lemma uniform_nhds_set_singleton {a : α} : uniformNhdsSet { a } = 𝓝 a := by
  simp only [uniformNhdsSet, thickening_singleton, nhds_eq_uniformity]


-- @@ L92-93 expanded
lemma mem_uniform_nhds_set_iff : s ∈ uniformNhdsSet t ↔ ∃ u ∈ 𝓤 α, thickening u t ⊆ s := by
  simp [uniformNhdsSet, mem_lift'_sets]


-- @@ L95-96 expanded
lemma nhds_le_uniform_nhds_set {s : Set α} (ha : a ∈ s) : 𝓝 a ≤ uniformNhdsSet s := by
  simpa [← uniform_nhds_set_singleton] using uniform_nhds_set_mono (singleton_subset_iff.mpr ha)


-- @@ L98-99 expanded
lemma nhds_set_le_uniform_nhds_set {s : Set α} : 𝓝ˢ s ≤ uniformNhdsSet s := by
  simpa [nhdsSet] using fun _ => nhds_le_uniform_nhds_set


-- @@ L101-108 expanded
lemma uniform_nhds_inf_uniform_nhds_eq_bot {s t : Set α} (h : uniformNhdsSet s ⊓ 𝓟 t = ⊥) :
    uniformNhdsSet s ⊓ uniformNhdsSet t = ⊥ :=
  by
  simp_rw [inf_principal_eq_bot, inf_eq_bot_iff, mem_uniform_nhds_set_iff] at h ⊢
  obtain ⟨u, hu, hsu⟩ := h
  obtain ⟨v, hv, hvs, hvu⟩ := comp_symm_of_uniformity hu
  refine ⟨_, ⟨v, hv, subset_rfl⟩, _, ⟨v, hv, subset_rfl⟩, ?h⟩
  apply thickening_inter_thickening_eq_empty_of_comp (symmetricRel_of hvs) hvu
  exact (subset_compl_iff_disjoint_right.mp hsu).inter_eq


-- @@ L110-112 expanded
lemma nhds_inf_uniform_nhds_eq_bot {s : Set α} (hf : 𝓝 a ⊓ 𝓟 s = ⊥) : 𝓝 a ⊓ uniformNhdsSet s = ⊥ :=
  by
  rw [← uniform_nhds_set_singleton] at hf ⊢
  exact uniform_nhds_inf_uniform_nhds_eq_bot hf


-- @@ L114-116 expanded
lemma nhds_set_eq_uniform_nhds_set_of_isCompact {s : Set α} (hs : IsCompact s) :
    𝓝ˢ s = uniformNhdsSet s :=
  (hs.nhdsSet_basis_uniformity (basis_sets _)).eq_of_same_basis ⟨fun _ => mem_uniform_nhds_set_iff⟩


-- @@ L118-120 verbatim
end UniformSpace

-----------------------------------------------------------------------------


-- @@ L122-122 verbatim
open UniformSpace


-- @@ L124-124 verbatim
variable {p : Filter ι}


-- @@ L126-128 expanded
lemma lemma0 [UniformSpace α] : Tendsto Prod.snd (𝓤 α ⊓ comap Prod.fst (𝓟 s)) (uniformNhdsSet s) :=
  by
  simp_rw [comap_principal, uniformNhdsSet, tendsto_lift', eventually_inf_principal]
  exact fun U hU => mem_of_superset hU (fun ⟨x, y⟩ hxy hx => mem_biUnion hx hxy)


-- @@ L130-132 verbatim
lemma lemma2 {p : Filter ι} {f : α → β} {s : Set α} :
    Tendsto (f ∘ Prod.snd) (p ×ˢ (𝓟 s)) (𝓟 (f '' s)) :=
  (tendsto_principal_principal.mpr <| fun _ => mem_image_of_mem f).comp tendsto_snd


-- @@ L134-138 expanded
lemma lemma1 {F : ι → α → β} {f : α → β} [UniformSpace β] (hF : TendstoUniformlyOn F f p s) :
    Tendsto (fun (q : ι × α) => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s)
      ((𝓟 (f '' s)) ×ˢ (uniformNhdsSet (f '' s))) :=
  by
  rw [tendstoUniformlyOn_iff_tendsto] at hF
  refine tendsto_prod_iff'.mpr ⟨lemma2, ?h⟩
  exact lemma0.comp (tendsto_inf.mpr ⟨hF, tendsto_comap_iff.mpr lemma2⟩)


-- @@ L140-142 expanded
lemma lemma13 {f : α → β} {F : ι → α → β} [UniformSpace β] (hF : TendstoUniformlyOn F f p s) :
    Tendsto (uncurry F) (p ×ˢ 𝓟 s) (uniformNhdsSet (f '' s)) :=
  (tendsto_prod_iff'.mp (lemma1 hF)).2

