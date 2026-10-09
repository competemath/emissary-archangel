import OAI.GroupTheory.UniversalGroup.Idempotents


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
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial ConcreteEnvelopes

-- @@ L19-19 verbatim
open scoped Classical Topology.Homotopy

-- @@ L20-20 verbatim
variable {G H : Type} [Group G] [Group H]

-- @@ L21-21 verbatim
variable (N : Type*) [DecidableEq N] [Nontrivial N]

-- @@ L22-22 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L24-38 verbatim
lemma diagramValue_one (k : Index → G →* H) (hk : IsDiagram k) (S : Shapes G) :
    mapValue N (k (.inl P₂.identity)) id S rfl Function.injective_id = 1 := by
  let z : Index → Additive (ControlledValues H N (StagePi G N S)) :=
    fun E => Additive.ofMul (mapValue N (k E) id S rfl Function.injective_id)
  have hc : z (.inl P₂.identity) = z (.inr P₃.identity) := by
    simp only [z,hk.common]
  have hs : ∀ t : triples, z t.val.2.2 = z t.val.1 + z t.val.2.1 := by
    intro t
    have he : k t.val.2.2 = commutingProduct (k t.val.1) (k t.val.2.1) (hk.commute t) := by
      ext g
      exact hk.sum t g
    change mapValue N (k t.val.2.2) id S rfl Function.injective_id = _
    rw [he]
    exact mapValue_product N (k t.val.1) (k t.val.2.1) (hk.commute t) S
  exact congrArg Additive.toMul (coprime_annihilation z hc hs)


-- @@ L40-45 verbatim
theorem diagram_uniform_homotopy_killing (k : Index → G →* H) (hk : IsDiagram k) (S : Shapes G) :
    ∃ T : Shapes H, ∃ h : imageShapes (k (.inl P₂.identity)) id (basedShapes G S) ⊆ T,
      (stageHom H N _ T h).comp
        (stageMapHom N (k (.inl P₂.identity)) id S _
          (image_stage_valid (k (.inl P₂.identity)) id S Function.injective_id) rfl) = 1 := by
  exact (value_eq_one_iff H N (StagePi G N S) _ _).mp (diagramValue_one N k hk S)

-- @@ L46-46 verbatim
end UniversalFInfinity.Milnor


-- @@ L48-48 verbatim
namespace UniversalFInfinity.Cellular

-- @@ L49-49 verbatim
open Set Metric Topology

-- @@ L50-50 verbatim
universe u v w

-- @@ L51-51 verbatim
variable {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]


-- @@ L53-54 verbatim
def KillsSpheres (q : C(Y,Z)) (n : ℕ) : Prop :=
  ∀ a : C(Sphere n,Y), ∃ F : C(Disk n,Z), ∀ x, F (boundary n x) = q (a x)


-- @@ L56-97 verbatim
lemma cylinder_filling_after {n : ℕ} (q : C(Y,Z)) (hq : KillsSpheres q (n+1))
    (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x)) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x t, e (boundary n x) t = q (a x t)) ∧
      ∀ x, pathEndpoint (e x) = (q (b x).1,q (b x).2) := by
  obtain ⟨F,hF⟩ := hq (cylinderBoundaryMap a b h)
  let e : C(Disk n,C(unitInterval,Z)) :=
    (F.comp ⟨fun p : Disk n × unitInterval => diskCons p.1 p.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = q (a x t)
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change q (a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t))) = q (a x t)
    rw [diskTime_cons]
    congr 2
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = q (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 0))).1 = q (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = q (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change q (b (diskTail (diskCons x 1))).2 = q (b x).2
      rw [diskTail_cons]


-- @@ L99-99 verbatim
variable {X : Type u} [TopologicalSpace X] [T2Space X]

-- @@ L100-100 verbatim
variable {C : Set X} [CWComplex C]


-- @@ L102-106 verbatim
structure PartialHomotopy (f g : C(X,Y)) (n : ℕ) where
  val : X → C(unitInterval,Y)
  continuousOn : ContinuousOn val (Skeleton C n)
  zero : ∀ x ∈ Skeleton C n, val x 0 = f x
  one : ∀ x ∈ Skeleton C n, val x 1 = g x


-- @@ L108-108 verbatim
namespace PartialHomotopy

-- @@ L109-109 verbatim
variable {f g : C(X,Y)} {n : ℕ}


-- @@ L111-115 verbatim
def onSphere (a : PartialHomotopy (C := C) f g n) (i : RelCWComplex.cell C n) :
    C(Sphere n,C(unitInterval,Y)) :=
  ⟨fun x => a.val (characteristic n i (boundary n x)),
    a.continuousOn.comp_continuous ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩


-- @@ L117-120 verbatim
def endpoints (i : RelCWComplex.cell C n) : C(Disk n,Y × Y) :=
  ⟨fun x => (f (characteristic n i x),g (characteristic n i x)),
    (f.continuous.comp (characteristic n i).continuous).prodMk
      (g.continuous.comp (characteristic n i).continuous)⟩


-- @@ L122-125 verbatim
lemma endpoints_compatible (a : PartialHomotopy (C := C) f g n)
    (i : RelCWComplex.cell C n) (x : Sphere n) :
    pathEndpoint (a.onSphere i x) = endpoints (f := f) (g := g) i (boundary n x) :=
  Prod.ext (a.zero _ (sphere_mem_skeleton n i x)) (a.one _ (sphere_mem_skeleton n i x))


-- @@ L127-136 verbatim
lemma cell_extension_after (a : PartialHomotopy (C := C) f g n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+1)) (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,C(unitInterval,Z)),
      (∀ x, e (boundary n x) = q.comp (a.val (characteristic n i (boundary n x)))) ∧
      (∀ x, e x 0 = q (f (characteristic n i x))) ∧
      (∀ x, e x 1 = q (g (characteristic n i x))) := by
  obtain ⟨e,he,hp⟩ := cylinder_filling_after q hq (a.onSphere i) (endpoints i)
    (a.endpoints_compatible i)
  exact ⟨e,fun x => ContinuousMap.ext (he x),fun x => congrArg Prod.fst (hp x),
    fun x => congrArg Prod.snd (hp x)⟩


-- @@ L138-166 verbatim
def next (a : PartialHomotopy (C := C) f g n)
    (q : C(Y,Z)) (hq : KillsSpheres q (n+1)) :
    PartialHomotopy (C := C) (q.comp f) (q.comp g) (n+1) := by
  let e := fun i => (a.cell_extension_after q hq i).choose
  have hb : ∀ i x, e i (boundary n x) =
      q.comp (a.val (characteristic n i (boundary n x))) :=
    fun i => (a.cell_extension_after q hq i).choose_spec.1
  have hz := fun i => (a.cell_extension_after q hq i).choose_spec.2.1
  have ho := fun i => (a.cell_extension_after q hq i).choose_spec.2.2
  let v : X → C(unitInterval,Z) := fun x => q.comp (a.val x)
  have hv : ContinuousOn v (Skeleton C n) :=
    (ContinuousMap.continuous_postcomp q).comp_continuousOn a.continuousOn
  refine ⟨attachValue v e,attachValue_continuous v hv e hb,?_,?_⟩
  all_goals
    intro x hx
    have heq : Skeleton C (n+1) = Skeleton C n ∪
        ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
      simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
        (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
    rw [heq] at hx
    rcases hx with hx | hx
    · rw [attachValue_old v e hx]
      first
      | exact congrArg q (a.zero x hx)
      | exact congrArg q (a.one x hx)
    · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
      rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
        attachValue_characteristic v e hb]
      first | exact hz i ⟨y,hy⟩ | exact ho i ⟨y,hy⟩


-- @@ L168-176 verbatim
def start (f g : C(X,Y)) : PartialHomotopy (C := C) f g 0 where
  val := fun x => ContinuousMap.const _ (f x)
  continuousOn := by
    rw [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty]
    exact continuousOn_empty _
  zero := by intro x _; rfl
  one := by
    intro x hx
    simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx


-- @@ L178-188 verbatim
def toHomotopy [CWComplex (Set.univ : Set X)] (a : PartialHomotopy (C := (Set.univ : Set X)) f g n)
    (hdim : Skeleton (Set.univ : Set X) n = Set.univ) : f.Homotopy g where
  toFun p := a.val p.2 p.1
  continuous_toFun := by
    have hv : Continuous a.val := by
      have hh := a.continuousOn
      rw [hdim] at hh
      exact continuousOn_univ.mp hh
    exact continuous_eval.comp ((hv.comp continuous_snd).prodMk continuous_fst)
  map_zero_left x := a.zero x (hdim.symm ▸ Set.mem_univ x)
  map_one_left x := a.one x (hdim.symm ▸ Set.mem_univ x)


-- @@ L190-190 verbatim
end PartialHomotopy

-- @@ L191-191 verbatim
end UniversalFInfinity.Cellular


-- @@ L193-193 verbatim
end


-- @@ L195-195 verbatim
end OAI
