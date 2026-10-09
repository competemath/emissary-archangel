import OAI.GroupTheory.UniversalGroup.GraphBundles


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
namespace UniversalFInfinity.GraphBundle


-- @@ L19-19 verbatim
section

-- @@ L20-20 verbatim
open Set Topology

-- @@ L21-21 verbatim
open scoped unitInterval

-- @@ L22-22 verbatim
universe u v w

-- @@ L23-23 verbatim
variable {C : Type u} {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]

-- @@ L24-24 verbatim
variable (τ : C → C) (L R : C → C(B,A))


-- @@ L26-75 verbatim
lemma edgeImage_edge_slice [DecidableEq C] (c d : C) (S : Set (I × B)) :
    (fun z : I × B => edge τ L R d z.1 z.2) ⁻¹'
      ((fun z : I × B => edge τ L R c z.1 z.2) '' S) =
      (if d = c then S else ∅) ∪
      ({0} ×ˢ ((L d) ⁻¹' ((vertex τ L R d) ⁻¹'
        ((fun z : I × B => edge τ L R c z.1 z.2) '' S)))) ∪
      ({1} ×ˢ ((R d) ⁻¹' ((vertex τ L R (τ d)) ⁻¹'
        ((fun z : I × B => edge τ L R c z.1 z.2) '' S)))) := by
  classical
  ext ⟨t,x⟩
  constructor
  · intro hz
    by_cases h0 : t = 0
    · subst t
      change edge τ L R d 0 x ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S) at hz
      exact Or.inl (Or.inr ⟨rfl,by
        change vertex τ L R d (L d x) ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S)
        rw [edge_zero] at hz; exact hz⟩)
    · by_cases h1 : t = 1
      · subst t
        change edge τ L R d 1 x ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S) at hz
        exact Or.inr ⟨rfl,by
          change vertex τ L R (τ d) (R d x) ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S)
          rw [edge_one] at hz; exact hz⟩
      · let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
          lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
        have he : edge τ L R d t x = interior τ L R d s x := edge_inner τ L R d s x
        obtain ⟨z,hz,hze⟩ := hz
        have hm : z ∈ (fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' {interior τ L R d s x} := hze.trans he
        rw [interior_preimage] at hm
        split_ifs at hm with hcd
        · change z = (t,x) at hm
          exact Or.inl (Or.inl (by rw [ite_eq_left hcd.symm]; exact hm ▸ hz))
        · exact False.elim hm
  · rintro ((hz|hz)|hz)
    · split_ifs at hz with hdc
      · subst d; exact ⟨(t,x),hz,rfl⟩
      · exact False.elim hz
    · rcases hz with ⟨h0,hx⟩
      change t = 0 at h0
      subst t
      change edge τ L R d 0 x ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S)
      rw [edge_zero]
      exact hx
    · rcases hz with ⟨h1,hx⟩
      change t = 1 at h1
      subst t
      change edge τ L R d 1 x ∈ ((fun z : I × B => edge τ L R c z.1 z.2) '' S)
      rw [edge_one]
      exact hx


-- @@ L77-98 verbatim
lemma edge_injective (c : C) (hτ : τ c ≠ c) (hL : Function.Injective (L c))
    (hR : Function.Injective (R c)) : Function.Injective (fun z : I × B => edge τ L R c z.1 z.2) := by
  classical
  rintro ⟨t,x⟩ ⟨s,y⟩ he
  by_cases h0 : t = 0
  · subst t
    have he' : edge τ L R c s y = vertex τ L R c (L c x) := he.symm.trans (edge_zero τ L R c x)
    rcases (edge_eq_vertex τ L R c c s y (L c x)).mp he' with ⟨rfl,_,hy⟩|⟨_,ht,_⟩
    · exact Prod.ext rfl (hL hy).symm
    · exact False.elim (hτ ht)
  · by_cases h1 : t = 1
    · subst t
      have he' : edge τ L R c s y = vertex τ L R (τ c) (R c x) := he.symm.trans (edge_one τ L R c x)
      rcases (edge_eq_vertex τ L R c (τ c) s y (R c x)).mp he' with ⟨_,ht,_⟩|⟨rfl,_,hy⟩
      · exact False.elim (hτ ht.symm)
      · exact Prod.ext rfl (hR hy).symm
    · let r : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
        lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
      have ht : edge τ L R c t x = interior τ L R c r x := edge_inner τ L R c r x
      have hm : (s,y) ∈ (fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' {interior τ L R c r x} := he.symm.trans ht
      rw [interior_preimage,ite_eq_left rfl] at hm
      exact (show (s,y) = (t,x) from hm).symm


-- @@ L100-100 verbatim
variable [TopologicalSpace C] [DiscreteTopology C]

-- @@ L101-112 verbatim
lemma edge_closedMap (c : C) (hL : IsClosedMap (L c)) (hR : IsClosedMap (R c)) :
    IsClosedMap (fun z : I × B => edge τ L R c z.1 z.2) := by
  classical
  intro S hS
  apply (isClosed_iff τ L R _).mpr
  refine ⟨fun d => edgeImage_vertex_closed τ L R c d S hS hL hR,fun d => ?_⟩
  rw [edgeImage_edge_slice]
  apply IsClosed.union
  · apply IsClosed.union
    · split_ifs; exact hS; exact isClosed_empty
    · exact isClosed_singleton.prod ((edgeImage_vertex_closed τ L R c d S hS hL hR).preimage (L d).continuous)
  · exact isClosed_singleton.prod ((edgeImage_vertex_closed τ L R c (τ d) S hS hL hR).preimage (R d).continuous)


-- @@ L114-118 verbatim
lemma edge_closedEmbedding (c : C) (hτ : τ c ≠ c) (hL : IsClosedEmbedding (L c))
    (hR : IsClosedEmbedding (R c)) : IsClosedEmbedding (fun z : I × B => edge τ L R c z.1 z.2) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap (edgeMap τ L R c).continuous
    (edge_injective τ L R c hτ hL.injective hR.injective)
    (edge_closedMap τ L R c hL.isClosedMap hR.isClosedMap)

-- @@ L119-119 verbatim
end


-- @@ L121-121 verbatim
open Set Topology

-- @@ L122-122 verbatim
open scoped unitInterval

-- @@ L123-123 verbatim
universe u v w z

-- @@ L124-124 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L125-125 verbatim
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]

-- @@ L126-126 verbatim
variable (τ : C → C) (L R : C → C(B,A))

-- @@ L127-127 verbatim
variable {Y : Type z} [TopologicalSpace Y]


-- @@ L129-141 verbatim
omit [DiscreteTopology C] in
lemma hom_ext {f g : C(Space τ L R,Y)}
    (hv : ∀ c x,f (vertex τ L R c x) = g (vertex τ L R c x))
    (he : ∀ c (z : I × B),f (edge τ L R c z.1 z.2) = g (edge τ L R c z.1 z.2)) : f = g := by
  apply ContinuousMap.ext
  intro z
  change Core (C := C) (A := A) (B := B) at z
  cases z with
  | inl z => exact hv z.1 z.2
  | inr z =>
    have hh := he z.1 (⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)
    rw [edge_inner] at hh
    exact hh


-- @@ L143-143 verbatim
variable (f g : C(Space τ L R,Y))

-- @@ L144-144 verbatim
variable (V : ∀ c,(f.comp (vertexMap τ L R c)).Homotopy (g.comp (vertexMap τ L R c)))

-- @@ L145-145 verbatim
variable (E : ∀ c,(f.comp (edgeMap τ L R c)).Homotopy (g.comp (edgeMap τ L R c)))

-- @@ L146-146 verbatim
variable (hE0 : ∀ c t x,E c (t,(0,x)) = V c (t,L c x))

-- @@ L147-147 verbatim
variable (hE1 : ∀ c t x,E c (t,(1,x)) = V (τ c) (t,R c x))


-- @@ L149-153 verbatim
def homotopyPaths : C(Space τ L R,C(I,Y)) :=
  lift τ L R (fun c => ContinuousMap.curry ((V c).toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩))
    (fun c => ContinuousMap.curry ((E c).toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩)) (by
      intro c x; apply ContinuousMap.ext; intro t; exact hE0 c t x) (by
      intro c x; apply ContinuousMap.ext; intro t; exact hE1 c t x)


-- @@ L155-175 verbatim
def homotopy : f.Homotopy g where
  toFun z := homotopyPaths τ L R f g V E hE0 hE1 z.2 z.1
  continuous_toFun := (homotopyPaths τ L R f g V E hE0 hE1).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    change Core (C := C) (A := A) (B := B) at z
    cases z with
    | inl z => exact (V z.1).apply_zero z.2
    | inr z =>
      have he := (E z.1).apply_zero (⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)
      change E z.1 (0,(⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)) = f (edge τ L R z.1 ⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩ z.2.2) at he
      rw [edge_inner] at he
      exact he
  map_one_left z := by
    change Core (C := C) (A := A) (B := B) at z
    cases z with
    | inl z => exact (V z.1).apply_one z.2
    | inr z =>
      have he := (E z.1).apply_one (⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)
      change E z.1 (1,(⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2)) = g (edge τ L R z.1 ⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩ z.2.2) at he
      rw [edge_inner] at he
      exact he

-- @@ L176-176 verbatim
end UniversalFInfinity.GraphBundle


-- @@ L178-178 verbatim
namespace UniversalFInfinity.PathFamilies

-- @@ L179-179 verbatim
open scoped unitInterval

-- @@ L180-180 verbatim
universe u v

-- @@ L181-181 verbatim
variable {J : Type u} [TopologicalSpace J] {Y : Type v} [TopologicalSpace Y]

-- @@ L182-186 verbatim
def intervalPath : Path (0:I) 1 where
  toFun := id
  continuous_toFun := continuous_id
  source' := rfl
  target' := rfl


-- @@ L188-188 verbatim
def unpause : C(I × I,I) := (Path.Homotopy.transRefl intervalPath).toContinuousMap


-- @@ L190-191 verbatim
lemma transRefl_natural {x y : Y} (p : Path x y) (z : I × I) :
    Path.Homotopy.transRefl p z = p (unpause z) := rfl


-- @@ L193-197 verbatim
lemma continuous_transRefl {a b : J → Y} (p : ∀ j,Path (a j) (b j))
    (hp : Continuous (fun z : J × I => p z.1 z.2)) :
    Continuous (fun z : J × (I × I) => Path.Homotopy.transRefl (p z.1) z.2) := by
  change Continuous (fun z : J × (I × I) => p z.1 (unpause z.2))
  exact hp.comp (continuous_fst.prodMk (unpause.continuous.comp continuous_snd))

-- @@ L198-198 verbatim
end UniversalFInfinity.PathFamilies


-- @@ L200-200 verbatim
namespace UniversalFInfinity.GraphBundle


-- @@ L202-202 verbatim
section

-- @@ L203-203 verbatim
open Set Topology

-- @@ L204-204 verbatim
open scoped unitInterval

-- @@ L205-205 verbatim
universe u v w

-- @@ L206-206 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L207-207 verbatim
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]

-- @@ L208-208 verbatim
variable (τ : C → C) (L R : C → C(B,A))


-- @@ L210-214 verbatim
def edgePath (c : C) (x : B) : Path (vertex τ L R c (L c x)) (vertex τ L R (τ c) (R c x)) where
  toFun t := edge τ L R c t x
  continuous_toFun := (edgeMap τ L R c).continuous.comp (continuous_id.prodMk continuous_const)
  source' := edge_zero τ L R c x
  target' := edge_one τ L R c x


-- @@ L216-218 verbatim
omit [DiscreteTopology C] in
lemma edgePath_continuous (c : C) : Continuous (fun z : B × I => edgePath τ L R c z.1 z.2) :=
  (edgeMap τ L R c).continuous.comp continuous_swap


-- @@ L220-220 verbatim
def pausedEdge (c : C) (x : B) := (edgePath τ L R c x).trans (Path.refl _)

-- @@ L221-225 verbatim
omit [DiscreteTopology C] in
lemma pausedEdge_continuous (c : C) : Continuous (fun z : B × I => pausedEdge τ L R c z.1 z.2) :=
  Path.trans_continuous_family (edgePath τ L R c) (edgePath_continuous τ L R c)
    (fun x => Path.refl (vertex τ L R (τ c) (R c x)))
    ((vertexMap τ L R (τ c)).continuous.comp ((R c).continuous.comp continuous_fst))


-- @@ L227-231 verbatim
def pause : C(Space τ L R,Space τ L R) :=
  lift τ L R (vertexMap τ L R)
    (fun c => ⟨fun z => pausedEdge τ L R c z.2 z.1,(pausedEdge_continuous τ L R c).comp continuous_swap⟩)
    (fun c x => (pausedEdge τ L R c x).source)
    (fun c x => (pausedEdge τ L R c x).target)

-- @@ L232-232 verbatim
lemma pause_vertex (c : C) (x : A) : pause τ L R (vertex τ L R c x) = vertex τ L R c x := rfl

-- @@ L233-234 verbatim
lemma pause_edge (c : C) (z : I × B) : pause τ L R (edge τ L R c z.1 z.2) = pausedEdge τ L R c z.2 z.1 :=
  lift_edge τ L R _ _ _ _ c z


-- @@ L236-238 verbatim
def pauseVertexHomotopy (c : C) :
    ((pause τ L R).comp (vertexMap τ L R c)).Homotopy ((ContinuousMap.id _).comp (vertexMap τ L R c)) :=
  ContinuousMap.Homotopy.refl (vertexMap τ L R c)


-- @@ L240-248 verbatim
omit [DiscreteTopology C] in
lemma pauseEdgeHomotopy_continuous (c : C) :
    Continuous (fun z : I × (I × B) =>
      Path.Homotopy.transRefl (edgePath τ L R c z.2.2) (z.1,z.2.1)) := by
  change Continuous (fun z : I × (I × B) =>
    edge τ L R c (PathFamilies.unpause (z.1,z.2.1)) z.2.2)
  exact (edgeMap τ L R c).continuous.comp
    ((PathFamilies.unpause.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      continuous_snd.snd)


-- @@ L250-258 verbatim
def pauseEdgeHomotopy (c : C) :
    ((pause τ L R).comp (edgeMap τ L R c)).Homotopy ((ContinuousMap.id _).comp (edgeMap τ L R c)) where
  toFun z := Path.Homotopy.transRefl (edgePath τ L R c z.2.2) (z.1,z.2.1)
  continuous_toFun := pauseEdgeHomotopy_continuous τ L R c
  map_zero_left z := by
    change Path.Homotopy.transRefl (edgePath τ L R c z.2) (0,z.1) = pause τ L R (edge τ L R c z.1 z.2)
    rw [pause_edge]
    exact (Path.Homotopy.transRefl (edgePath τ L R c z.2)).apply_zero z.1
  map_one_left z := (Path.Homotopy.transRefl (edgePath τ L R c z.2)).apply_one z.1


-- @@ L260-263 verbatim
def pauseHomotopy : (pause τ L R).Homotopy (ContinuousMap.id _) :=
  homotopy τ L R (pause τ L R) (ContinuousMap.id _) (pauseVertexHomotopy τ L R)
    (pauseEdgeHomotopy τ L R) (fun c t x => (Path.Homotopy.transRefl (edgePath τ L R c x)).source t)
    (fun c t x => (Path.Homotopy.transRefl (edgePath τ L R c x)).target t)

-- @@ L264-264 verbatim
end


-- @@ L266-266 verbatim
section

-- @@ L267-267 verbatim
open Set Topology

-- @@ L268-268 verbatim
open scoped unitInterval

-- @@ L269-269 verbatim
universe u v w z

-- @@ L270-270 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L271-271 verbatim
variable {D : Type v} [TopologicalSpace D] [DiscreteTopology D]

-- @@ L272-272 verbatim
variable {A : Type w} [TopologicalSpace A] {B : Type z} [TopologicalSpace B]

-- @@ L273-273 verbatim
variable (τ : C → C) (F : C → C(A,A)) (ν : D → D) (K : D → C(B,B))

-- @@ L274-274 verbatim
variable (sig : C → D) (hsig : ∀ c,sig (τ c) = ν (sig c)) (a : C → C(A,B))

-- @@ L275-275 verbatim
variable (ha : ∀ c x,a (τ c) (F c x) = K (sig c) (a c x))


-- @@ L277-283 verbatim
def homogeneousMap : C(Space τ (fun _ => .id A) F,Space ν (fun _ => .id B) K) :=
  lift τ (fun _ => .id A) F
    (fun c => (vertexMap ν (fun _ => .id B) K (sig c)).comp (a c))
    (fun c => (edgeMap ν (fun _ => .id B) K (sig c)).comp
      ⟨fun z => (z.1,a c z.2), continuous_fst.prodMk ((a c).continuous.comp continuous_snd)⟩)
    (fun c x => edge_zero ν _ K (sig c) (a c x))
    (fun c x => by change edge ν _ K (sig c) 1 (a c x) = vertex ν _ K (sig (τ c)) (a (τ c) (F c x)); rw [edge_one,hsig,ha])

-- @@ L284-287 verbatim
omit [DiscreteTopology D] in
lemma homogeneousMap_vertex (c : C) (x : A) :
    homogeneousMap τ F ν K sig hsig a ha (vertex τ (fun _ => .id A) F c x) =
      vertex ν (fun _ => .id B) K (sig c) (a c x) := rfl

-- @@ L288-291 verbatim
omit [DiscreteTopology D] in
lemma homogeneousMap_edge (c : C) (t : I) (x : A) :
    homogeneousMap τ F ν K sig hsig a ha (edge τ (fun _ => .id A) F c t x) =
      edge ν (fun _ => .id B) K (sig c) t (a c x) := lift_edge τ _ F _ _ _ _ c (t,x)

-- @@ L292-292 verbatim
end


-- @@ L294-294 verbatim
open Set Topology

-- @@ L295-295 verbatim
open scoped unitInterval

-- @@ L296-296 verbatim
universe u v w

-- @@ L297-297 verbatim
variable {G : Type u} [Group G]

-- @@ L298-298 verbatim
variable {C : Type v} [TopologicalSpace C] [DiscreteTopology C] [MulAction G C]

-- @@ L299-299 verbatim
variable {A : Type w} [TopologicalSpace A]

-- @@ L300-300 verbatim
variable (τ : C → C) (F : C → C(A,A)) (hτ : ∀ (g : G) c,τ (g • c) = g • τ c)

-- @@ L301-301 verbatim
variable (a : G → C → C(A,A))

-- @@ L302-302 verbatim
variable (ha : ∀ (g : G) c x,a g (τ c) (F c x) = F (g • c) (a g c x))

-- @@ L303-303 verbatim
variable (a_one : ∀ c x,a 1 c x = x)

-- @@ L304-304 verbatim
variable (a_mul : ∀ (g h : G) c x,a (g*h) c x = a g (h • c) (a h c x))


-- @@ L306-307 verbatim
def actionMap (g : G) : C(Space τ (fun _ => .id A) F,Space τ (fun _ => .id A) F) :=
  homogeneousMap τ F τ F (g • ·) (fun c => (hτ g c).symm) (a g) (ha g)

-- @@ L308-310 verbatim
lemma actionMap_vertex (g : G) (c : C) (x : A) :
    actionMap τ F hτ a ha g (vertex τ (fun _ => .id A) F c x) =
      vertex τ (fun _ => .id A) F (g • c) (a g c x) := rfl

-- @@ L311-314 verbatim
lemma actionMap_edge (g : G) (c : C) (t : I) (x : A) :
    actionMap τ F hτ a ha g (edge τ (fun _ => .id A) F c t x) =
      edge τ (fun _ => .id A) F (g • c) t (a g c x) :=
  homogeneousMap_edge τ F τ F _ _ _ _ c t x


-- @@ L316-330 verbatim
@[instance_reducible]
def graphAction : MulAction G (Space τ (fun _ => .id A) F) where
  smul g x := actionMap τ F hτ a ha g x
  one_smul x := by
    have he : actionMap τ F hτ a ha 1 = ContinuousMap.id _ := by
      apply hom_ext τ (fun _ => .id A) F
      · intro c y; rw [actionMap_vertex,one_smul,a_one]; rfl
      · intro c z; rw [actionMap_edge,one_smul,a_one]; rfl
    exact ContinuousMap.congr_fun he x
  mul_smul g h x := by
    have he : actionMap τ F hτ a ha (g*h) = (actionMap τ F hτ a ha g).comp (actionMap τ F hτ a ha h) := by
      apply hom_ext τ (fun _ => .id A) F
      · intro c y; simp only [ContinuousMap.comp_apply,actionMap_vertex,mul_smul,a_mul]
      · intro c z; simp only [ContinuousMap.comp_apply,actionMap_edge,mul_smul,a_mul]
    exact ContinuousMap.congr_fun he x


-- @@ L332-336 verbatim
lemma graphAction_continuous : @ContinuousConstSMul G (Space τ (fun _ => .id A) F) _
    (graphAction τ F hτ a ha a_one a_mul).toSMul :=
by
  let := graphAction τ F hτ a ha a_one a_mul
  exact ⟨fun g => (actionMap τ F hτ a ha g).continuous⟩

-- @@ L337-337 verbatim
end UniversalFInfinity.GraphBundle


-- @@ L339-339 verbatim
end


-- @@ L341-341 verbatim
end OAI
