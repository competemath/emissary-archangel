import OAI.GroupTheory.UniversalGroup.AscendingTorus


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set Metric Topology BigOperators

-- @@ L8-8 verbatim
open Set Metric Topology

-- @@ L9-9 verbatim
open Set Topology

-- @@ L10-10 verbatim
open Set Metric Topology

-- @@ L11-11 verbatim
open scoped NNReal

-- @@ L12-12 verbatim
open Set Metric Topology

-- @@ L13-13 verbatim
open scoped NNReal ENNReal

-- @@ L14-14 verbatim
open Set Metric Topology

-- @@ L15-15 verbatim
open scoped TensorProduct


-- @@ L17-17 verbatim
namespace UniversalFInfinity.Milnor

-- @@ L18-18 verbatim
open Set Topology

-- @@ L19-19 verbatim
universe u v

-- @@ L20-20 verbatim
variable {G : Type u} [Group G] {H : Type v} [Group H]

-- @@ L21-27 verbatim
lemma map_smul (φ : G →* H) (g : G) (x : Space G) :
    map φ id Function.injective_id (g • x) = φ g • map φ id Function.injective_id x := by
  change map φ id Function.injective_id (map (g * ·) id Function.injective_id x) =
    map (φ g * ·) id Function.injective_id (map φ id Function.injective_id x)
  rw [map_comp,map_comp]
  have he : (φ ∘ (g * ·)) = ((φ g * ·) ∘ φ) := funext (map_mul φ g)
  rw [he]

-- @@ L28-35 verbatim
omit [Group G] [Group H] in
lemma map_leftInverse (φ : G → H) (ψ : H → G) (h : Function.LeftInverse ψ φ) :
    Function.LeftInverse (map ψ id Function.injective_id) (map φ id Function.injective_id) := by
  intro x
  rw [map_comp]
  have he : ψ ∘ φ = id := funext h
  rw [he]
  exact map_id x

-- @@ L36-41 verbatim
omit [Group H] in
lemma map_closedEmbedding (φ : G → H) (hφ : Function.Injective φ) :
    IsClosedEmbedding (map φ id Function.injective_id) := by
  obtain ⟨ψ,hψ⟩ := hφ.hasLeftInverse
  exact (map_leftInverse φ ψ hψ).isClosedEmbedding
    (map ψ id Function.injective_id).continuous (map φ id Function.injective_id).continuous


-- @@ L43-43 verbatim
def smulMap (g : G) : C(Space G,Space G) := ⟨(g • ·),continuous_const_smul g⟩

-- @@ L44-45 verbatim
lemma smulMap_closedEmbedding (g : G) : IsClosedEmbedding (smulMap g) := by
  exact (Homeomorph.smul g).isClosedEmbedding

-- @@ L46-46 verbatim
end UniversalFInfinity.Milnor


-- @@ L48-48 verbatim
namespace UniversalFInfinity.TorusGeometry

-- @@ L49-49 verbatim
open Set Topology AscendingTorus

-- @@ L50-50 verbatim
universe u

-- @@ L51-51 verbatim
variable {U : Type u} [Group U] (f : Monoid.End U)


-- @@ L53-53 verbatim
instance cosetTopology : TopologicalSpace (Coset f) := ⊥

-- @@ L54-54 verbatim
instance : DiscreteTopology (Coset f) := ⟨rfl⟩


-- @@ L56-57 verbatim
def transition (c : Coset f) : C(Milnor.Space U,Milnor.Space U) :=
  (Milnor.smulMap (cosetOffset f c)).comp (Milnor.map f id Function.injective_id)

-- @@ L58-59 verbatim
lemma transition_apply (c : Coset f) (x : Milnor.Space U) :
    transition f c x = cosetOffset f c • Milnor.map f id Function.injective_id x := rfl

-- @@ L60-62 verbatim
lemma transition_embedding (hf : Function.Injective f) (c : Coset f) :
    IsClosedEmbedding (transition f c) :=
  (Milnor.smulMap_closedEmbedding _).comp (Milnor.map_closedEmbedding f hf)


-- @@ L64-64 verbatim
abbrev Space := GraphBundle.Space (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)

-- @@ L65-65 verbatim
def vertex (c : Coset f) (x : Milnor.Space U) : Space f := GraphBundle.vertex _ _ _ c x


-- @@ L67-68 verbatim
def coordinateAction (g : Torus f) (c : Coset f) : C(Milnor.Space U,Milnor.Space U) :=
  Milnor.smulMap (actionOffset f g c)

-- @@ L69-84 verbatim
lemma coordinateAction_compatible (hf : Function.Injective f) (g : Torus f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f g (next f c) (transition f c x) =
      transition f (g • c) (coordinateAction f g c x) := by
  change actionOffset f g (next f c) • (cosetOffset f c • Milnor.map f id Function.injective_id x) =
    cosetOffset f (g • c) • Milnor.map f id Function.injective_id (actionOffset f g c • x)
  calc
    _ = (actionOffset f g (next f c) * cosetOffset f c) •
        Milnor.map f id Function.injective_id x := (mul_smul _ _ _).symm
    _ = (cosetOffset f (g • c) * f (actionOffset f g c)) •
        Milnor.map f id Function.injective_id x :=
      congrArg (fun element : U => element • Milnor.map f id Function.injective_id x)
        (actionOffset_next f hf g c)
    _ = cosetOffset f (g • c) •
        (f (actionOffset f g c) • Milnor.map f id Function.injective_id x) := mul_smul _ _ _
    _ = _ := congrArg (cosetOffset f (g • c) • ·)
      (Milnor.map_smul f (actionOffset f g c) x).symm

-- @@ L85-88 verbatim
lemma coordinateAction_one (hf : Function.Injective f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f 1 c x = x := by
  change actionOffset f 1 c • x = x
  rw [actionOffset_one f hf,one_smul]

-- @@ L89-92 verbatim
lemma coordinateAction_mul (hf : Function.Injective f) (g h : Torus f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f (g*h) c x = coordinateAction f g (h • c) (coordinateAction f h c x) := by
  change actionOffset f (g*h) c • x = actionOffset f g (h • c) • (actionOffset f h c • x)
  rw [actionOffset_mul f hf,mul_smul]


-- @@ L94-97 verbatim
@[instance_reducible]
def action (hf : Function.Injective f) : MulAction (Torus f) (Space f) :=
  GraphBundle.graphAction (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) (coordinateAction_one f hf) (coordinateAction_mul f hf)


-- @@ L99-99 verbatim
variable [Fact (Function.Injective f)]

-- @@ L100-100 verbatim
local notation "hf" => (Fact.out : Function.Injective f)

-- @@ L101-101 verbatim
local instance : MulAction (Torus f) (Space f) := action f hf

-- @@ L102-104 verbatim
instance action_continuous : ContinuousConstSMul (Torus f) (Space f) :=
  GraphBundle.graphAction_continuous (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) (coordinateAction_one f hf) (coordinateAction_mul f hf)

-- @@ L105-106 verbatim
lemma smul_vertex (g : Torus f) (c : Coset f) (x : Milnor.Space U) :
    g • vertex f c x = vertex f (g • c) (actionOffset f g c • x) := rfl

-- @@ L107-111 verbatim
lemma smul_edge (g : Torus f) (c : Coset f) (t : unitInterval) (x : Milnor.Space U) :
    g • GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) c t x =
      GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) (g • c) t (actionOffset f g c • x) :=
  GraphBundle.actionMap_edge (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) g c t x

-- @@ L112-112 verbatim
end UniversalFInfinity.TorusGeometry


-- @@ L114-114 verbatim
namespace UniversalFInfinity.GraphBundle


-- @@ L116-116 verbatim
section

-- @@ L117-117 verbatim
open Set Topology

-- @@ L118-118 verbatim
open scoped unitInterval

-- @@ L119-119 verbatim
universe u v w z r

-- @@ L120-120 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L121-121 verbatim
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]

-- @@ L122-122 verbatim
variable {A' : Type z} [TopologicalSpace A'] {B' : Type r} [TopologicalSpace B']

-- @@ L123-123 verbatim
variable (τ : C → C) (L R : C → C(B,A)) (L' R' : C → C(B',A'))

-- @@ L124-124 verbatim
variable (i : C(A,A')) (j : C(B,B'))

-- @@ L125-125 verbatim
variable (hL : ∀ c x,i (L c x) = L' c (j x)) (hR : ∀ c x,i (R c x) = R' c (j x))


-- @@ L127-128 verbatim
def inclusionFun : Space τ L R → Space τ L' R' :=
  Sum.map (Prod.map id i) (Prod.map id (Prod.map id j))

-- @@ L129-131 verbatim
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma inclusionFun_vertex (c : C) (x : A) :
    inclusionFun τ L R L' R' i j (vertex τ L R c x) = vertex τ L' R' c (i x) := rfl

-- @@ L132-134 verbatim
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma inclusionFun_interior (c : C) (t : Inner) (x : B) :
    inclusionFun τ L R L' R' i j (interior τ L R c t x) = interior τ L' R' c t (j x) := rfl

-- @@ L135-148 verbatim
include hL hR in
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma inclusionFun_edge (c : C) (t : I) (x : B) :
    inclusionFun τ L R L' R' i j (edge τ L R c t x) = edge τ L' R' c t (j x) := by
  classical
  by_cases h0 : t = 0
  · subst t; rw [edge_zero,edge_zero,inclusionFun_vertex,hL]
  by_cases h1 : t = 1
  · subst t; rw [edge_one,edge_one,inclusionFun_vertex,hR]
  let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
    lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
  change inclusionFun τ L R L' R' i j (edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ x) =
    edge τ L' R' c ⟨s.1,s.2.1.le,s.2.2.le⟩ (j x)
  rw [edge_inner,edge_inner]; rfl


-- @@ L150-156 verbatim
def inclusion : C(Space τ L R,Space τ L' R') :=
  ⟨inclusionFun τ L R L' R' i j,(continuous_iff τ L R _).mpr ⟨fun c =>
    (vertexMap τ L' R' c).continuous.comp i.continuous,fun c => by
      have he : (fun p : I × B => inclusionFun τ L R L' R' i j (edge τ L R c p.1 p.2)) =
          (fun p : I × B => edge τ L' R' c p.1 (j p.2)) := funext (fun p => inclusionFun_edge τ L R L' R' i j hL hR c p.1 p.2)
      rw [he]
      exact (edgeMap τ L' R' c).continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd))⟩⟩

-- @@ L157-158 verbatim
lemma inclusion_vertex (c : C) (x : A) :
    inclusion τ L R L' R' i j hL hR (vertex τ L R c x) = vertex τ L' R' c (i x) := rfl

-- @@ L159-160 verbatim
lemma inclusion_interior (c : C) (t : Inner) (x : B) :
    inclusion τ L R L' R' i j hL hR (interior τ L R c t x) = interior τ L' R' c t (j x) := rfl

-- @@ L161-163 verbatim
lemma inclusion_edge (c : C) (t : I) (x : B) :
    inclusion τ L R L' R' i j hL hR (edge τ L R c t x) = edge τ L' R' c t (j x) :=
  inclusionFun_edge τ L R L' R' i j hL hR c t x


-- @@ L165-167 verbatim
lemma inclusion_injective (hi : Function.Injective i) (hj : Function.Injective j) :
    Function.Injective (inclusion τ L R L' R' i j hL hR) :=
  Sum.map_injective.mpr ⟨Function.injective_id.prodMap hi,Function.injective_id.prodMap (Function.injective_id.prodMap hj)⟩


-- @@ L169-182 verbatim
lemma inclusion_vertex_preimage (S : Set (Space τ L R)) (c : C) :
    (vertex τ L' R' c) ⁻¹' (inclusion τ L R L' R' i j hL hR '' S) =
      i '' ((vertex τ L R c) ⁻¹' S) := by
  ext x
  constructor
  · rintro ⟨a,ha,he⟩
    change Core (C := C) (A := A) (B := B) at a
    cases a with
    | inl a =>
      have hh : (a.1,i a.2) = (c,x) := Sum.inl.inj he
      obtain rfl := congrArg Prod.fst hh
      exact ⟨a.2,ha,congrArg Prod.snd hh⟩
    | inr a => cases he
  · rintro ⟨y,hy,rfl⟩; exact ⟨vertex τ L R c y,hy,rfl⟩


-- @@ L184-231 verbatim
lemma inclusion_edge_preimage (S : Set (Space τ L R)) (c : C) :
    (fun p : I × B' => edge τ L' R' c p.1 p.2) ⁻¹' (inclusion τ L R L' R' i j hL hR '' S) =
      ({0} ×ˢ ((L' c) ⁻¹' (i '' ((vertex τ L R c) ⁻¹' S)))) ∪
      ({1} ×ˢ ((R' c) ⁻¹' (i '' ((vertex τ L R (τ c)) ⁻¹' S)))) ∪
      (Prod.map id j '' ((fun p : I × B => edge τ L R c p.1 p.2) ⁻¹' S)) := by
  classical
  ext ⟨t,x⟩
  constructor
  · intro h
    by_cases h0 : t = 0
    · subst t; apply Or.inl; apply Or.inl; refine ⟨rfl,?_⟩
      rw [Set.mem_preimage,edge_zero] at h
      exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S c) _).mp h
    by_cases h1 : t = 1
    · subst t; apply Or.inl; apply Or.inr; refine ⟨rfl,?_⟩
      rw [Set.mem_preimage,edge_one] at h
      exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S (τ c)) _).mp h
    let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
      lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
    change edge τ L' R' c ⟨s.1,s.2.1.le,s.2.2.le⟩ x ∈ inclusion τ L R L' R' i j hL hR '' S at h
    rw [edge_inner] at h
    obtain ⟨a,ha,he⟩ := h
    change Core (C := C) (A := A) (B := B) at a
    cases a with
    | inl a => cases he
    | inr a =>
      have hh : (a.1,(a.2.1,j a.2.2)) = (c,(s,x)) := Sum.inr.inj he
      have hc : a.1 = c := congrArg Prod.fst hh
      have ht : a.2.1 = s := congrArg (fun p : C × (Inner × B') => p.2.1) hh
      have hx : j a.2.2 = x := congrArg (fun p : C × (Inner × B') => p.2.2) hh
      apply Or.inr
      refine ⟨(t,a.2.2),?_,Prod.ext rfl hx⟩
      change edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ a.2.2 ∈ S
      rw [edge_inner,←hc,←ht]
      exact ha
  · rintro (h|h)
    · rcases h with h|h
      · have ht : t = 0 := h.1; subst t
        rw [Set.mem_preimage,edge_zero]
        exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S c) _).mpr h.2
      · have ht : t = 1 := h.1; subst t
        rw [Set.mem_preimage,edge_one]
        exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S (τ c)) _).mpr h.2
    · obtain ⟨⟨r,y⟩,hy,he⟩ := h
      have ht : r = t := congrArg Prod.fst he
      have hx : j y = x := congrArg Prod.snd he
      subst t; subst x
      exact ⟨edge τ L R c r y,hy,inclusion_edge τ L R L' R' i j hL hR c r y⟩


-- @@ L233-245 verbatim
lemma inclusion_closedEmbedding (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    IsClosedEmbedding (inclusion τ L R L' R' i j hL hR) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap (inclusion τ L R L' R' i j hL hR).continuous
    (inclusion_injective τ L R L' R' i j hL hR hi.injective hj.injective)
  intro S hS
  obtain ⟨hv,he⟩ := (isClosed_iff τ L R S).mp hS
  apply (isClosed_iff τ L' R' _).mpr
  constructor
  · intro c; rw [inclusion_vertex_preimage]; exact hi.isClosedMap _ (hv c)
  · intro c; rw [inclusion_edge_preimage]
    exact ((isClosed_singleton.prod ((hi.isClosedMap _ (hv c)).preimage (L' c).continuous)).union
      (isClosed_singleton.prod ((hi.isClosedMap _ (hv (τ c))).preimage (R' c).continuous))).union
      ((IsClosedEmbedding.prodMap IsClosedEmbedding.id hj).isClosedMap _ (he c))

-- @@ L246-246 verbatim
end


-- @@ L248-248 verbatim
open Set Topology

-- @@ L249-249 verbatim
open scoped unitInterval

-- @@ L250-250 verbatim
universe u v w

-- @@ L251-251 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L252-252 verbatim
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B] [T1Space B]

-- @@ L253-253 verbatim
variable (τ : C → C) (L R : C → C(B,A))


-- @@ L255-279 verbatim
theorem compact_coordinates (hτ : ∀ c,τ c ≠ c)
    (hL : ∀ c,IsClosedEmbedding (L c)) (hR : ∀ c,IsClosedEmbedding (R c))
    {K : Set (Space τ L R)} (hK : IsCompact K) :
    ∃ (KA : Set A) (KB : Set B), IsCompact KA ∧ IsCompact KB ∧
      (∀ c x,vertex τ L R c x ∈ K → x ∈ KA) ∧
      (∀ c s x,interior τ L R c s x ∈ K → x ∈ KB) := by
  let KA := Prod.snd '' ((fun z : C × A => vertex τ L R z.1 z.2) ⁻¹' K)
  let J := {c : C | ∃ s x,interior τ L R c s x ∈ K}
  let KB := ⋃ c ∈ J, Prod.snd '' ((fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' K)
  have hJ : J.Finite := compact_finitely_many_edges τ L R hK
  have hA : IsCompact KA :=
    ((base_closedEmbedding τ L R).isProperMap.isCompact_preimage hK).image continuous_snd
  have hB : IsCompact KB := by
    apply hJ.isCompact_biUnion
    intro c _
    exact ((edge_closedEmbedding τ L R c (hτ c) (hL c) (hR c)).isProperMap.isCompact_preimage hK).image continuous_snd
  refine ⟨KA,KB,hA,hB,?_,?_⟩
  · intro c x hx
    exact ⟨(c,x),hx,rfl⟩
  · intro c s x hx
    apply Set.mem_iUnion₂.mpr
    refine ⟨c,⟨s,x,hx⟩,?_⟩
    refine ⟨(⟨s.1,s.2.1.le,s.2.2.le⟩,x),?_,rfl⟩
    change edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ x ∈ K
    rwa [edge_inner]

-- @@ L280-280 verbatim
end UniversalFInfinity.GraphBundle


-- @@ L282-282 verbatim
namespace UniversalFInfinity.TorusGeometry


-- @@ L284-284 verbatim
section

-- @@ L285-285 verbatim
open Set Topology Milnor UniversalFInfinity.Simplicial AscendingTorus

-- @@ L286-286 verbatim
open scoped Classical unitInterval

-- @@ L287-287 verbatim
universe u v

-- @@ L288-288 verbatim
variable {U : Type u} [Group U] (f : Monoid.End U)

-- @@ L289-289 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L291-291 verbatim
def vertexShapes (S : Shapes U) : Shapes U := S ∪ imageShapes f id (basedShapes U S)

-- @@ L292-292 verbatim
lemma vertexShapes_left (S : Shapes U) : S ⊆ vertexShapes f S := Finset.subset_union_left

-- @@ L293-297 verbatim
lemma vertexShapes_map (S : Shapes U) (s : Face (stage U S)) :
    faceImage f id s.1 ∈ stage U (vertexShapes f S) := by
  apply orbitSpan_mono (show imageShapes f id (basedShapes U S) ⊆ basedShapes U (vertexShapes f S) from
    fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
  exact faceImage_controlled f id Function.injective_id (basedShapes U S) s


-- @@ L299-300 verbatim
def stageForward (S : Shapes U) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  mapC _ _ (Milnor.vertexMap f id) (vertexShapes_map f S)

-- @@ L301-303 verbatim
lemma stageForward_full (S : Shapes U) (x : Milnor.Stage U S) :
    stageFull U (vertexShapes f S) (stageForward f S x) =
      map f id Function.injective_id (stageFull U S x) := rfl


-- @@ L305-306 verbatim
def left (S : Shapes U) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  stageIncl U S (vertexShapes f S) (vertexShapes_left f S)

-- @@ L307-308 verbatim
def right (S : Shapes U) (c : Coset f) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  (stageSmul U (vertexShapes f S) (cosetOffset f c)).comp (stageForward f S)

-- @@ L309-310 verbatim
lemma left_full (S : Shapes U) (_c : Coset f) (x : Milnor.Stage U S) :
    stageFull U (vertexShapes f S) (left f S x) = (ContinuousMap.id (Milnor.Space U)) (stageFull U S x) := rfl

-- @@ L311-312 verbatim
lemma right_full (S : Shapes U) (c : Coset f) (x : Milnor.Stage U S) :
    stageFull U (vertexShapes f S) (right f S c x) = transition f c (stageFull U S x) := rfl


-- @@ L314-314 verbatim
abbrev Stage (S : Shapes U) := GraphBundle.Space (next f) (fun _ => left f S) (right f S)

-- @@ L315-318 verbatim
def stageFull (S : Shapes U) : C(Stage f S,Space f) :=
  GraphBundle.inclusion (next f) (fun _ => left f S) (right f S)
    (fun _ => ContinuousMap.id _) (transition f) (Milnor.stageFull U (vertexShapes f S)) (Milnor.stageFull U S)
    (left_full f S) (right_full f S)

-- @@ L319-321 verbatim
lemma stageFull_closedEmbedding (S : Shapes U) : IsClosedEmbedding (stageFull f S) :=
  GraphBundle.inclusion_closedEmbedding _ _ _ _ _ _ _ _ _
    (Milnor.stageFull_embedding U _) (Milnor.stageFull_embedding U _)

-- @@ L322-323 verbatim
lemma stageFull_vertex (S : Shapes U) (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    stageFull f S (GraphBundle.vertex _ _ _ c x) = vertex f c (Milnor.stageFull U _ x) := rfl

-- @@ L324-325 verbatim
lemma stageFull_interior (S : Shapes U) (c : Coset f) (t : GraphBundle.Inner) (x : Milnor.Stage U S) :
    stageFull f S (GraphBundle.interior _ _ _ c t x) = GraphBundle.interior _ _ _ c t (Milnor.stageFull U _ x) := rfl

-- @@ L326-328 verbatim
lemma stageFull_edge (S : Shapes U) (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    stageFull f S (GraphBundle.edge _ _ _ c t x) = GraphBundle.edge _ _ _ c t (Milnor.stageFull U _ x) :=
  GraphBundle.inclusion_edge _ _ _ _ _ _ _ _ _ c t x


-- @@ L330-334 verbatim
lemma next_ne (c : Coset f) : next f c ≠ c := by
  intro h
  have he := height_next f c
  rw [h] at he
  omega


-- @@ L336-356 verbatim
theorem compact_controlled (hf : Function.Injective f) {K : Set (Space f)} (hK : IsCompact K) :
    ∃ S : Shapes U, K ⊆ Set.range (stageFull f S) := by
  obtain ⟨KA,KB,hA,hB,hVA,hEB⟩ := GraphBundle.compact_coordinates (next f)
    (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f) (next_ne f)
    (fun _ => IsClosedEmbedding.id) (transition_embedding f hf) hK
  obtain ⟨S,hS⟩ := Milnor.compact_controlled U hA
  obtain ⟨T,hT⟩ := Milnor.compact_controlled U hB
  let R := S ∪ T
  refine ⟨R,?_⟩
  intro x hx
  change GraphBundle.Core (C := Coset f) (A := Milnor.Space U) (B := Milnor.Space U) at x
  cases x with
  | inl x =>
    obtain ⟨y,hy⟩ := hS (hVA x.1 x.2 hx)
    let z := stageIncl U S (vertexShapes f R) (Finset.subset_union_left.trans (vertexShapes_left f R)) y
    exact ⟨GraphBundle.vertex _ _ _ x.1 z,congrArg (vertex f x.1) hy⟩
  | inr x =>
    obtain ⟨y,hy⟩ := hT (hEB x.1 x.2.1 x.2.2 hx)
    let z := stageIncl U T R Finset.subset_union_right y
    exact ⟨GraphBundle.interior _ _ _ x.1 x.2.1 z,
      congrArg (GraphBundle.interior _ _ _ x.1 x.2.1) hy⟩

-- @@ L357-357 verbatim
end


-- @@ L359-359 verbatim
open Set Topology Milnor AscendingTorus

-- @@ L360-360 verbatim
open scoped Classical unitInterval

-- @@ L361-361 verbatim
universe u v

-- @@ L362-362 verbatim
variable {U : Type u} [Group U] (f : Monoid.End U)

-- @@ L363-363 verbatim
variable [Fact (Function.Injective f)]

-- @@ L364-364 verbatim
local notation "hf" => (Fact.out : Function.Injective f)

-- @@ L365-365 verbatim
local instance : MulAction (Torus f) (Space f) := action f hf


-- @@ L367-388 verbatim
lemma stage_range_smul (S : Shapes U) (g : Torus f) {x : Space f}
    (hx : x ∈ Set.range (stageFull f S)) : g • x ∈ Set.range (stageFull f S) := by
  obtain ⟨a,rfl⟩ := hx
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at a
  cases a with
  | inl a =>
    refine ⟨GraphBundle.vertex _ _ _ (g • a.1) (actionOffset f g a.1 • a.2),?_⟩
    change vertex f (g • a.1) (Milnor.stageFull U _ (actionOffset f g a.1 • a.2)) =
      g • vertex f a.1 (Milnor.stageFull U _ a.2)
    rw [smul_vertex,Milnor.stageFull_smul]
  | inr a =>
    refine ⟨GraphBundle.interior _ _ _ (g • a.1) a.2.1 (actionOffset f g a.1 • a.2.2),?_⟩
    change stageFull f S (GraphBundle.interior (next f) (fun _ => left f S) (right f S)
      (g • a.1) a.2.1 (actionOffset f g a.1 • a.2.2)) =
      g • stageFull f S (GraphBundle.interior (next f) (fun _ => left f S) (right f S) a.1 a.2.1 a.2.2)
    rw [stageFull_interior,stageFull_interior,Milnor.stageFull_smul]
    let t : unitInterval := ⟨a.2.1.1,a.2.1.2.1.le,a.2.1.2.2.le⟩
    have h1 : GraphBundle.interior (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)
        a.1 a.2.1 (Milnor.stageFull U _ a.2.2) =
        GraphBundle.edge (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)
        a.1 t (Milnor.stageFull U _ a.2.2) := (GraphBundle.edge_inner _ _ _ _ _ _).symm
    rw [h1,smul_edge,GraphBundle.edge_inner]


-- @@ L390-396 verbatim
lemma compact_orbit_controlled {K : Set (Space f)} (hK : IsCompact K) :
    ∃ S : Shapes U, ∀ g : Torus f, (g • ·) '' K ⊆ Set.range (stageFull f S) := by
  obtain ⟨S,hS⟩ := compact_controlled f hf hK
  refine ⟨S,?_⟩
  intro g x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact stage_range_smul f S g (hS hy)


-- @@ L398-398 verbatim
variable {X : Type v} [TopologicalSpace X] [MulAction (Torus f) X]

-- @@ L399-408 verbatim
lemma equivariant_controlled (hX : Milnor.CompactFundamentalSet (Torus f) (X := X))
    (a : C(X,Space f)) (he : ∀ (g : Torus f) x,a (g • x) = g • a x) :
    ∃ S : Shapes U, Set.range a ⊆ Set.range (stageFull f S) := by
  obtain ⟨K,hK,hcov⟩ := hX
  obtain ⟨S,hS⟩ := compact_orbit_controlled f (hK.image a.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [he]
  exact hS g ⟨a y,⟨y,hy,rfl⟩,rfl⟩


-- @@ L410-417 verbatim
omit [MulAction (Torus f) X] [Fact (Function.Injective f)] in
def factorStage (a : C(X,Space f)) (S : Shapes U)
    (ha : Set.range a ⊆ Set.range (stageFull f S)) : C(X,Stage f S) where
  toFun x := (ha (Set.mem_range_self x)).choose
  continuous_toFun := (stageFull_closedEmbedding f S).isEmbedding.continuous_iff.mpr (by
    convert a.continuous using 1
    funext x
    exact (ha (Set.mem_range_self x)).choose_spec)

-- @@ L418-421 verbatim
omit [MulAction (Torus f) X] [Fact (Function.Injective f)] in
lemma factorStage_spec (a : C(X,Space f)) (S : Shapes U)
    (ha : Set.range a ⊆ Set.range (stageFull f S)) (x : X) :
    stageFull f S (factorStage f a S ha x) = a x := (ha (Set.mem_range_self x)).choose_spec

-- @@ L422-422 verbatim
end UniversalFInfinity.TorusGeometry


-- @@ L424-424 verbatim
end


-- @@ L426-426 verbatim
end OAI
