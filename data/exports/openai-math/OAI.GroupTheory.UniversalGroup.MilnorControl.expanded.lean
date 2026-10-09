import OAI.GroupTheory.UniversalGroup.CellularLifting


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set Metric Topology BigOperators

-- @@ L8-8 verbatim
open Set Metric Topology


-- @@ L10-10 verbatim
namespace UniversalFInfinity.Milnor


-- @@ L12-12 verbatim
section

-- @@ L13-13 verbatim
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial

-- @@ L14-14 verbatim
open scoped Classical unitInterval

-- @@ L15-15 verbatim
universe u v

-- @@ L16-16 verbatim
variable {G : Type u}

-- @@ L17-17 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L19-21 verbatim
def boundedInclusion (N : ℕ) : C(Simplicial.Space (bounded G N),Space G) :=
  ⟨Simplicial.inclusion (bounded G N) (complex G) (fun _ h => bounded_le G N h),
    Simplicial.continuous_inclusion _ _ _⟩


-- @@ L23-28 verbatim
def boundedContraction (N : ℕ) (g : G) :
    (boundedInclusion (G := G) N).Homotopy (ContinuousMap.const _ (vertex (N,g))) := by
  let H := Simplicial.straightHomotopy (bounded G N) (complex G) id (fun _ => (N,g))
    (bounded_id_face N) (bounded_const_face N g) (bounded_contiguous N g)
  exact H.cast (ContinuousMap.ext (fun x => bounded_map_id N x))
    (ContinuousMap.ext (fun x => map_const_vertex (bounded G N) (N,g) (bounded_const_face N g) x))


-- @@ L30-41 verbatim
lemma compactMap_bounded {A : Type v} [TopologicalSpace A] [CompactSpace A] (f : C(A,Space G)) :
    ∃ N : ℕ, ∃ F : C(A,Simplicial.Space (bounded G N)), (boundedInclusion N).comp F = f := by
  obtain ⟨S,hS⟩ := Simplicial.compact_bounded_vertices (complex G) (isCompact_range f.continuous)
  let N := S.sup Prod.fst + 1
  have hN (a : A) (v : ℕ × G) (hv : v ∈ (f a).1.support) : v.1 < N := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := Prod.fst) (hS (f a) (mem_range_self a) hv))
  let F : A → Simplicial.Space (bounded G N) := fun a =>
    ⟨(f a).1,(f a).2.1,(f a).2.2.1,(f a).2.2.2,hN a⟩
  have hc : Continuous F :=
    (Simplicial.inclusion_closedEmbedding (bounded G N) (complex G)
      (fun _ h => bounded_le G N h)).isEmbedding.continuous_iff.mpr f.continuous
  exact ⟨N,⟨F,hc⟩,rfl⟩


-- @@ L43-46 verbatim
lemma compactMap_nullhomotopic {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (g : G) (f : C(A,Space G)) : ∃ y, Nonempty (f.Homotopy (ContinuousMap.const _ y)) := by
  obtain ⟨N,F,hF⟩ := compactMap_bounded f
  exact ⟨vertex (N,g),⟨((boundedContraction N g).compContinuousMap F).cast hF rfl⟩⟩


-- @@ L48-63 verbatim
lemma sphereFillable (g : G) : Cellular.SphereFillable (Space G) := by
  intro n f
  cases n with
  | zero =>
    refine ⟨ContinuousMap.const _ (vertex (0,g)),?_⟩
    intro x
    have hx : False := by
      have he := x.2
      simp only [Metric.mem_sphere,Subsingleton.elim x.1 0,dist_self] at he
      exact zero_ne_one he
    exact hx.elim
  | succ n =>
    let := SphereTopology.sphere_nonempty n
    obtain ⟨y,⟨H⟩⟩ := compactMap_nullhomotopic g f
    obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic H.symm
    exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩


-- @@ L65-68 verbatim
lemma contractible [Nonempty G] : ContractibleSpace (Space G) := by
  let g : G := Classical.choice ‹Nonempty G›
  let : Nonempty (Space G) := ⟨vertex (0,g)⟩
  exact Cellular.contractible_of_sphereFillable (sphereFillable g)


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
section

-- @@ L73-73 verbatim
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial

-- @@ L74-74 verbatim
open scoped Classical

-- @@ L75-75 verbatim
universe u v

-- @@ L76-76 verbatim
variable {G : Type u} [Group G]

-- @@ L77-77 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L79-79 verbatim
def translate (g : G) (s : Finset (ℕ × G)) : Finset (ℕ × G) := s.image (fun v => (v.1,g*v.2))


-- @@ L81-82 verbatim
lemma translate_one (s : Finset (ℕ × G)) : translate 1 s = s := by
  simp only [translate,one_mul,Prod.mk.eta,Finset.image_id']

-- @@ L83-84 verbatim
lemma translate_mul (g h : G) (s : Finset (ℕ × G)) : translate g (translate h s) = translate (g*h) s := by
  simp only [translate,Finset.image_image,Function.comp_def,mul_assoc]

-- @@ L85-86 verbatim
lemma translate_mono (g : G) {s t : Finset (ℕ × G)} (h : s ⊆ t) : translate g s ⊆ translate g t :=
  Finset.image_subset_image h

-- @@ L87-88 verbatim
lemma translate_valid (g : G) {s : Finset (ℕ × G)} (hs : s ∈ complex G) : translate g s ∈ complex G :=
  map_face (g * ·) id Function.injective_id ⟨s,hs⟩


-- @@ L90-97 verbatim
def orbitSpan (S : Finset (Finset (ℕ × G))) : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {t | t ∈ complex G ∧ ∃ g : G, ∃ s ∈ S, t ⊆ translate g s}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨ht.1.1,?_⟩
    intro u hut hu
    obtain ⟨g,s,hs,hts⟩ := ht.2
    exact ⟨(complex G).isRelLowerSet_faces.mem_of_le ht.1 hut hu,g,s,hs,hut.trans hts⟩


-- @@ L99-99 verbatim
lemma orbitSpan_le (S : Finset (Finset (ℕ × G))) : orbitSpan S ≤ complex G := fun _ h => h.1

-- @@ L100-103 verbatim
lemma orbitSpan_mono {S T : Finset (Finset (ℕ × G))} (h : S ⊆ T) : orbitSpan S ≤ orbitSpan T := by
  intro t ht
  obtain ⟨g,s,hs,hts⟩ := ht.2
  exact ⟨ht.1,g,s,h hs,hts⟩

-- @@ L104-107 verbatim
lemma orbitSpan_contains (S : Finset (Finset (ℕ × G))) {t : Finset (ℕ × G)}
    (ht : t ∈ complex G) (h : ∃ s ∈ S, t ⊆ s) : t ∈ orbitSpan S := by
  obtain ⟨s,hs,hts⟩ := h
  exact ⟨ht,1,s,hs,by rwa [translate_one]⟩

-- @@ L108-111 verbatim
lemma orbitSpan_invariant (S : Finset (Finset (ℕ × G))) (g : G)
    {t : Finset (ℕ × G)} (ht : t ∈ orbitSpan S) : translate g t ∈ orbitSpan S := by
  obtain ⟨h,s,hs,hts⟩ := ht.2
  exact ⟨translate_valid g ht.1,g*h,s,hs,by rw [←translate_mul]; exact translate_mono g hts⟩


-- @@ L113-121 verbatim
lemma orbitSpan_bounded (S : Finset (Finset (ℕ × G))) :
    orbitSpan S ≤ bounded G ((S.biUnion id).sup Prod.fst + 1) := by
  intro t ht
  refine ⟨ht.1,?_⟩
  intro v hv
  obtain ⟨g,s,hs,hts⟩ := ht.2
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp (hts hv)
  have hh : w.1 ≤ (S.biUnion id).sup Prod.fst := Finset.le_sup (f := Prod.fst) (Finset.mem_biUnion.mpr ⟨s,hs,hw⟩)
  exact Nat.lt_succ_of_le hh


-- @@ L123-124 verbatim
def Controlled (K : PreAbstractSimplicialComplex (ℕ × G)) : Prop :=
  ∃ S : Finset (Finset (ℕ × G)), K ≤ orbitSpan S


-- @@ L126-126 verbatim
lemma controlled_orbitSpan (S : Finset (Finset (ℕ × G))) : Controlled (orbitSpan S) := ⟨S,le_rfl⟩

-- @@ L127-130 verbatim
lemma controlled_bounded {K : PreAbstractSimplicialComplex (ℕ × G)} (hK : Controlled K) :
    ∃ N, K ≤ bounded G N := by
  obtain ⟨S,hS⟩ := hK
  exact ⟨_,hS.trans (orbitSpan_bounded S)⟩


-- @@ L132-141 verbatim
lemma orbitSpan_finite_representatives (S : Finset (Finset (ℕ × G))) :
    ∃ T : Finset (Finset (ℕ × G)), ∀ t ∈ orbitSpan S, ∃ s ∈ T, ∃ g : G, t = translate g s := by
  refine ⟨S.biUnion Finset.powerset,?_⟩
  intro t ht
  obtain ⟨g,s,hs,hts⟩ := ht.2
  have hh : translate g⁻¹ t ⊆ s := by
    have hh := translate_mono g⁻¹ hts
    simpa only [translate_mul,inv_mul_cancel,translate_one] using hh
  refine ⟨translate g⁻¹ t,Finset.mem_biUnion.mpr ⟨s,hs,Finset.mem_powerset.mpr hh⟩,g,?_⟩
  rw [translate_mul,mul_inv_cancel,translate_one]


-- @@ L143-143 verbatim
end

-- @@ L144-144 verbatim
section

-- @@ L145-145 verbatim
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial

-- @@ L146-146 verbatim
open scoped Classical

-- @@ L147-147 verbatim
universe u v

-- @@ L148-148 verbatim
variable {G : Type u} {H : Type v} [Group G] [Group H]

-- @@ L149-149 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L151-151 verbatim
def vertexMap (φ : G →* H) (α : ℕ → ℕ) : ℕ × G → ℕ × H := fun v => (α v.1,φ v.2)

-- @@ L152-152 verbatim
def faceImage (φ : G →* H) (α : ℕ → ℕ) (s : Finset (ℕ × G)) : Finset (ℕ × H) := s.image (vertexMap φ α)

-- @@ L153-153 verbatim
def imageShapes (φ : G →* H) (α : ℕ → ℕ) (S : Finset (Finset (ℕ × G))) : Finset (Finset (ℕ × H)) := S.image (faceImage φ α)


-- @@ L155-157 verbatim
lemma faceImage_translate (φ : G →* H) (α : ℕ → ℕ) (a : G) (s : Finset (ℕ × G)) :
    faceImage φ α (translate a s) = translate (φ a) (faceImage φ α s) := by
  simp only [faceImage,translate,Finset.image_image,vertexMap,Function.comp_def,map_mul]


-- @@ L159-161 verbatim
lemma faceImage_valid (φ : G →* H) (α : ℕ → ℕ) (hα : Function.Injective α)
    {s : Finset (ℕ × G)} (hs : s ∈ complex G) : faceImage φ α s ∈ complex H :=
  map_face φ α hα ⟨s,hs⟩


-- @@ L163-170 verbatim
lemma faceImage_controlled (φ : G →* H) (α : ℕ → ℕ) (hα : Function.Injective α)
    (S : Finset (Finset (ℕ × G))) (s : Face (orbitSpan S)) :
    faceImage φ α s.1 ∈ orbitSpan (imageShapes φ α S) := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  refine ⟨faceImage_valid φ α hα s.2.1,φ a,faceImage φ α t,
    Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  rw [← faceImage_translate]
  exact Finset.image_subset_image hst


-- @@ L172-195 verbatim
lemma unionFace_valid (φ : G →* H) (α β : ℕ → ℕ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {s : Finset (ℕ × G)} (hs : s ∈ complex G)
    (hc : ∀ v ∈ s, ∀ w ∈ s, α v.1 = β w.1 → v.1 = w.1) :
    faceImage φ α s ∪ faceImage φ β s ∈ complex H := by
  refine ⟨(faceImage_valid φ α hα hs).1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact (faceImage_valid φ α hα hs).2 hx hy hxy
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hvw : v = w := hs.2 hv hw (hc v hv w hw hxy)
    subst w
    apply Prod.ext
    · exact hxy
    · rfl
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hvw : w = v := hs.2 hw hv (hc w hw v hv hxy.symm)
    subst w
    apply Prod.ext
    · exact hxy
    · rfl
  · exact (faceImage_valid φ β hβ hs).2 hx hy hxy


-- @@ L197-198 verbatim
def unionShapes (φ : G →* H) (α β : ℕ → ℕ) (S : Finset (Finset (ℕ × G))) :
    Finset (Finset (ℕ × H)) := S.image (fun s => faceImage φ α s ∪ faceImage φ β s)


-- @@ L200-201 verbatim
lemma translate_union (a : H) (s t : Finset (ℕ × H)) : translate a (s ∪ t) = translate a s ∪ translate a t :=
  Finset.image_union _ _


-- @@ L203-212 verbatim
lemma unionFace_controlled (φ : G →* H) (α β : ℕ → ℕ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (S : Finset (Finset (ℕ × G))) (s : Face (orbitSpan S))
    (hc : ∀ v ∈ s.1, ∀ w ∈ s.1, α v.1 = β w.1 → v.1 = w.1) :
    faceImage φ α s.1 ∪ faceImage φ β s.1 ∈ orbitSpan (unionShapes φ α β S) := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  refine ⟨unionFace_valid φ α β hα hβ s.2.1 hc,φ a,faceImage φ α t ∪ faceImage φ β t,
    Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  rw [translate_union,←faceImage_translate,←faceImage_translate]
  exact Finset.union_subset_union (Finset.image_subset_image hst) (Finset.image_subset_image hst)


-- @@ L214-214 verbatim
def fresh (N : ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else N+i

-- @@ L215-215 verbatim
lemma fresh_zero (N : ℕ) : fresh N 0 = 0 := by simp [fresh]

-- @@ L216-223 verbatim
lemma fresh_injective (N : ℕ) : Function.Injective (fresh N) := by
  intro i j h
  unfold fresh at h
  split_ifs at h with hi hj hj
  · exact hi.trans hj.symm
  · exfalso; omega
  · exfalso; omega
  · omega


-- @@ L225-232 verbatim
lemma fresh_cross (N : ℕ) (α : ℕ → ℕ) (hα : Function.Injective α) (hzero : α 0 = 0)
    {i j : ℕ} (hi : α i < N) (h : α i = fresh N j) : i = j := by
  by_cases hj : j = 0
  · subst j
    apply hα
    simpa only [fresh_zero,hzero] using h
  · have hh : N ≤ fresh N j := by simp only [fresh,ite_eq_right hj]; exact Nat.le_add_right _ _
    omega

-- @@ L233-233 verbatim
end

-- @@ L234-234 verbatim
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial

-- @@ L235-235 verbatim
open scoped Classical unitInterval

-- @@ L236-236 verbatim
universe u v

-- @@ L237-237 verbatim
variable {G : Type u} {H : Type v} [Group G] [Group H]

-- @@ L238-238 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L240-241 verbatim
def shapeBound (S : Finset (Finset (ℕ × G))) (α : ℕ → ℕ) : ℕ :=
  (S.biUnion id).sup (fun v => α v.1) + 1

-- @@ L242-248 verbatim
lemma orbit_below_bound (S : Finset (Finset (ℕ × G))) (α : ℕ → ℕ)
    (s : Face (orbitSpan S)) {v : ℕ × G} (hv : v ∈ s.1) : α v.1 < shapeBound S α := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp (hst hv)
  have hh : α w.1 ≤ (S.biUnion id).sup (fun v => α v.1) :=
    Finset.le_sup (f := fun v : ℕ × G => α v.1) (Finset.mem_biUnion.mpr ⟨t,ht,hw⟩)
  exact Nat.lt_succ_of_le hh


-- @@ L250-251 verbatim
def relayerFresh (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ) : ℕ → ℕ :=
  fresh (max (shapeBound S α) (shapeBound S β))

-- @@ L252-253 verbatim
def relayerTarget (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ) :=
  unionShapes φ α (relayerFresh S α β) S ∪ unionShapes φ β (relayerFresh S α β) S


-- @@ L255-261 verbatim
lemma relayerLeftValid (φ : G →* H) (S : Finset (Finset (ℕ × G)))
    (α β : ℕ → ℕ) (hα : Function.Injective α) (hα0 : α 0 = 0) (s : Face (orbitSpan S)) :
    faceImage φ α s.1 ∪ faceImage φ (relayerFresh S α β) s.1 ∈ orbitSpan (relayerTarget φ S α β) := by
  apply orbitSpan_mono Finset.subset_union_left
  apply unionFace_controlled φ α (relayerFresh S α β) hα (fresh_injective _) S s
  intro v hv w _ h
  exact fresh_cross _ α hα hα0 ((orbit_below_bound S α s hv).trans_le (le_max_left _ _)) h


-- @@ L263-269 verbatim
lemma relayerRightValid (φ : G →* H) (S : Finset (Finset (ℕ × G)))
    (α β : ℕ → ℕ) (hβ : Function.Injective β) (hβ0 : β 0 = 0) (s : Face (orbitSpan S)) :
    faceImage φ β s.1 ∪ faceImage φ (relayerFresh S α β) s.1 ∈ orbitSpan (relayerTarget φ S α β) := by
  apply orbitSpan_mono Finset.subset_union_right
  apply unionFace_controlled φ β (relayerFresh S α β) hβ (fresh_injective _) S s
  intro v hv w _ h
  exact fresh_cross _ β hβ hβ0 ((orbit_below_bound S β s hv).trans_le (le_max_right _ _)) h


-- @@ L271-271 verbatim
variable (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ)

-- @@ L272-272 verbatim
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)

-- @@ L273-277 verbatim
include hα hα0 in
lemma relayerLeftMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ α) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerLeftValid φ S α β hα hα0 s)
    Finset.subset_union_left (s.2.1.1.image _)

-- @@ L278-282 verbatim
include hβ hβ0 in
lemma relayerRightMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ β) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerRightValid φ S α β hβ hβ0 s)
    Finset.subset_union_left (s.2.1.1.image _)

-- @@ L283-287 verbatim
include hα hα0 in
lemma relayerFreshMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ (relayerFresh S α β)) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerLeftValid φ S α β hα hα0 s)
    Finset.subset_union_right (s.2.1.1.image _)


-- @@ L289-290 verbatim
def relayerLeftMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ α) (relayerLeftMapValid φ S α β hα hα0)

-- @@ L291-292 verbatim
def relayerRightMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ β) (relayerRightMapValid φ S α β hβ hβ0)

-- @@ L293-294 verbatim
def relayerFreshMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ (relayerFresh S α β)) (relayerFreshMapValid φ S α β hα hα0)


-- @@ L296-297 verbatim
def relayerLeftHomotopy : (relayerLeftMap φ S α β hα hα0).Homotopy (relayerFreshMap φ S α β hα hα0) :=
  straightHomotopy _ _ _ _ _ _ (relayerLeftValid φ S α β hα hα0)

-- @@ L298-299 verbatim
def relayerRightHomotopy : (relayerRightMap φ S α β hβ hβ0).Homotopy (relayerFreshMap φ S α β hα hα0) :=
  straightHomotopy _ _ _ _ _ _ (relayerRightValid φ S α β hβ hβ0)


-- @@ L301-302 verbatim
def relayerHomotopy : (relayerLeftMap φ S α β hα hα0).Homotopy (relayerRightMap φ S α β hβ hβ0) :=
  (relayerLeftHomotopy φ S α β hα hα0).trans (relayerRightHomotopy φ S α β hα hβ hα0 hβ0).symm


-- @@ L304-310 verbatim
lemma relayerLeftPure (x : Simplicial.Space (orbitSpan S)) (g : G) (hx : x.1 = Finsupp.single (0,g) 1) :
    relayerLeftMap φ S α β hα hα0 x = relayerFreshMap φ S α β hα hα0 x := by
  apply Subtype.ext
  change x.1.mapDomain (vertexMap φ α) = x.1.mapDomain (vertexMap φ (relayerFresh S α β))
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext (hα0.trans (fresh_zero (max (shapeBound S α) (shapeBound S β))).symm) rfl

-- @@ L311-317 verbatim
lemma relayerRightPure (x : Simplicial.Space (orbitSpan S)) (g : G) (hx : x.1 = Finsupp.single (0,g) 1) :
    relayerRightMap φ S α β hβ hβ0 x = relayerFreshMap φ S α β hα hα0 x := by
  apply Subtype.ext
  change x.1.mapDomain (vertexMap φ β) = x.1.mapDomain (vertexMap φ (relayerFresh S α β))
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext (hβ0.trans (fresh_zero (max (shapeBound S α) (shapeBound S β))).symm) rfl


-- @@ L319-323 verbatim
lemma relayerLeftHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerLeftHomotopy φ S α β hα hα0 (t,x) = relayerLeftMap φ S α β hα hα0 x :=
  straightHomotopy_fixed _ _ _ _ _ _ (relayerLeftValid φ S α β hα hα0) x
    (relayerLeftPure φ S α β hα hα0 x g hx) t

-- @@ L324-328 verbatim
lemma relayerRightHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerRightHomotopy φ S α β hα hβ hα0 hβ0 (t,x) = relayerRightMap φ S α β hβ hβ0 x :=
  straightHomotopy_fixed _ _ _ _ _ _ (relayerRightValid φ S α β hβ hβ0) x
    (relayerRightPure φ S α β hα hβ hα0 hβ0 x g hx) t


-- @@ L330-339 verbatim
theorem relayerHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerHomotopy φ S α β hα hβ hα0 hβ0 (t,x) = relayerLeftMap φ S α β hα hα0 x := by
  rw [relayerHomotopy,ContinuousMap.Homotopy.trans_apply]
  split
  · exact relayerLeftHomotopy_fixed φ S α β hα hα0 x g hx _
  · rw [ContinuousMap.Homotopy.symm_apply]
    exact (relayerRightHomotopy_fixed φ S α β hα hβ hα0 hβ0 x g hx _).trans
      ((relayerRightPure φ S α β hα hβ hα0 hβ0 x g hx).trans
        (relayerLeftPure φ S α β hα hα0 x g hx).symm)

-- @@ L340-340 verbatim
end UniversalFInfinity.Milnor


-- @@ L342-342 verbatim
end


-- @@ L344-344 verbatim
end OAI
