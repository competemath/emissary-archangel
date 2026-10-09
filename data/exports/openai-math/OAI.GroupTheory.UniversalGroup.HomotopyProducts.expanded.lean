import OAI.GroupTheory.UniversalGroup.MilnorControl


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set Metric Topology BigOperators

-- @@ L8-8 verbatim
open Set Metric Topology


-- @@ L10-10 verbatim
namespace UniversalFInfinity.HomotopyFunctor


-- @@ L12-12 verbatim
section

-- @@ L13-13 verbatim
open scoped Topology Topology.Homotopy

-- @@ L14-14 verbatim
universe u v w

-- @@ L15-15 verbatim
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

-- @@ L16-16 verbatim
variable {x : X} {y : Y}


-- @@ L18-19 verbatim
def loopMap (f : C(X,Y)) (hf : f x = y) (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.1,fun t ht => by change f (p t) = y; rw [GenLoop.boundary p t ht,hf]⟩


-- @@ L21-23 verbatim
lemma loopMap_homotopic (f : C(X,Y)) (hf : f x = y) {p q : GenLoop N X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (loopMap f hf p) (loopMap f hf q) :=
  h.comp_continuousMap f


-- @@ L25-26 verbatim
def map (f : C(X,Y)) (hf : f x = y) : HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (loopMap f hf) (fun _ _ h => loopMap_homotopic f hf h)


-- @@ L28-29 verbatim
@[simp] lemma map_mk (f : C(X,Y)) (hf : f x = y) (p : GenLoop N X x) :
    map f hf (Quotient.mk' p) = Quotient.mk' (loopMap f hf p) := rfl


-- @@ L31-34 verbatim
lemma loopMap_const (f : C(X,Y)) (hf : f x = y) :
    loopMap (N := N) f hf GenLoop.const = GenLoop.const := by
  ext t
  exact hf


-- @@ L36-42 verbatim
lemma loopMap_transAt [DecidableEq N] (i : N) (f : C(X,Y)) (hf : f x = y)
    (p q : GenLoop N X x) :
    loopMap f hf (GenLoop.transAt i p q) = GenLoop.transAt i (loopMap f hf p) (loopMap f hf q) := by
  ext t
  change f (if (t i : ℝ) ≤ 1/2 then p _ else q _) =
    if (t i : ℝ) ≤ 1/2 then f (p _) else f (q _)
  split <;> rfl


-- @@ L44-55 verbatim
def mapHom [DecidableEq N] [Nonempty N] (f : C(X,Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    change Quotient.mk' (loopMap f hf GenLoop.const) = Quotient.mk' GenLoop.const
    exact congrArg Quotient.mk' (loopMap_const f hf)
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    have h₁ := HomotopyGroup.mul_spec (i := Classical.arbitrary N) (p := p) (q := q)
    have h₂ := HomotopyGroup.mul_spec (i := Classical.arbitrary N)
      (p := loopMap f hf p) (q := loopMap f hf q)
    exact (congrArg (map f hf) h₁).trans
      ((congrArg Quotient.mk' (loopMap_transAt (Classical.arbitrary N) f hf q p)).trans h₂.symm)


-- @@ L57-59 verbatim
lemma map_id (a : HomotopyGroup N X x) : map (y := x) (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with | h p =>
  exact congrArg Quotient.mk' (by ext t; rfl)


-- @@ L61-66 verbatim
lemma map_comp {Z : Type*} [TopologicalSpace Z] {z : Z}
    (f : C(X,Y)) (hf : f x = y) (g : C(Y,Z)) (hg : g y = z)
    (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = map (g.comp f) (by change g (f x) = z; rw [hf,hg]) a := by
  induction a using Quotient.inductionOn with | h p =>
  rfl


-- @@ L68-71 verbatim
lemma map_const [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    map (ContinuousMap.const X y) rfl a = 1 := by
  induction a using Quotient.inductionOn with | h p =>
  rfl


-- @@ L73-73 verbatim
variable {Z : Type*} [TopologicalSpace Z] {z : Z}


-- @@ L75-76 verbatim
def loopPair (p : GenLoop N X x) (q : GenLoop N Y y) : GenLoop N (X × Y) (x,y) :=
  ⟨p.1.prodMk q.1,fun t ht => Prod.ext (GenLoop.boundary p t ht) (GenLoop.boundary q t ht)⟩


-- @@ L78-85 verbatim
lemma pair_homotopic {p p' : GenLoop N X x} {q q' : GenLoop N Y y}
    (h : GenLoop.Homotopic p p') (k : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (loopPair p q) (loopPair p' q') := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  refine ⟨{ toHomotopy := h.toHomotopy.prodMk k.toHomotopy,prop' := ?_ }⟩
  intro t a ha
  exact Prod.ext (h.eq_fst t ha) (k.eq_fst t ha)


-- @@ L87-94 verbatim
lemma product_ext (a b : HomotopyGroup N (X × Y) (x,y))
    (h₁ : map ((ContinuousMap.fst : C(X × Y,X))) rfl a = map ((ContinuousMap.fst : C(X × Y,X))) rfl b)
    (h₂ : map ((ContinuousMap.snd : C(X × Y,Y))) rfl a = map ((ContinuousMap.snd : C(X × Y,Y))) rfl b) : a = b := by
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  apply Quotient.sound
  have hh := pair_homotopic (Quotient.exact h₁) (Quotient.exact h₂)
  exact hh


-- @@ L96-144 verbatim
lemma diagonal_split [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl a =
      (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl a) *
      (map (y := (x,x)) ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl a) := by
  apply product_ext
  · change mapHom ((ContinuousMap.fst : C(X × X,X))) rfl _ = mapHom ((ContinuousMap.fst : C(X × X,X))) rfl _
    rw [map_mul]
    change map (y := x) ContinuousMap.fst rfl
        (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl a) =
      map (y := x) ContinuousMap.fst rfl
        (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl a) *
      map (y := x) ContinuousMap.fst rfl
        (map (y := (x,x)) ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl a)
    calc
      _ = map (y := x) (ContinuousMap.id X) rfl a := map_comp _ _ _ _ a
      _ = map (y := x) (ContinuousMap.id X) rfl a *
          map (y := x) (ContinuousMap.const X x) rfl a :=
        (map_id a).trans (((congrArg₂ (fun left right : HomotopyGroup N X x => left * right)
          (map_id a) (map_const (y := x) a)).trans
          (mul_one a)).symm)
      _ = _ := congrArg₂ (fun left right : HomotopyGroup N X x => left * right)
        (map_comp (y := (x,x)) (z := x)
          ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl
          ContinuousMap.fst rfl a).symm
        (map_comp (y := (x,x)) (z := x)
          ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl
          ContinuousMap.fst rfl a).symm
  · change mapHom ((ContinuousMap.snd : C(X × X,X))) rfl _ = mapHom ((ContinuousMap.snd : C(X × X,X))) rfl _
    rw [map_mul]
    change map (y := x) ContinuousMap.snd rfl
        (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl a) =
      map (y := x) ContinuousMap.snd rfl
        (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl a) *
      map (y := x) ContinuousMap.snd rfl
        (map (y := (x,x)) ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl a)
    calc
      _ = map (y := x) (ContinuousMap.id X) rfl a := map_comp _ _ _ _ a
      _ = map (y := x) (ContinuousMap.const X x) rfl a *
          map (y := x) (ContinuousMap.id X) rfl a :=
        (map_id a).trans (((congrArg₂ (fun left right : HomotopyGroup N X x => left * right)
          (map_const (y := x) a) (map_id a)).trans
          (one_mul a)).symm)
      _ = _ := congrArg₂ (fun left right : HomotopyGroup N X x => left * right)
        (map_comp (y := (x,x)) (z := x)
          ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl
          ContinuousMap.snd rfl a).symm
        (map_comp (y := (x,x)) (z := x)
          ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl
          ContinuousMap.snd rfl a).symm


-- @@ L146-155 verbatim
theorem product_additivity [DecidableEq N] [Nonempty N] (F : C(X × X,Y))
    (hF : F (x,x) = y) (a : HomotopyGroup N X x) :
    map (F.comp ((ContinuousMap.id X).prodMk (ContinuousMap.id X))) hF a =
      map (F.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X x))) hF a *
      map (F.comp ((ContinuousMap.const X x).prodMk (ContinuousMap.id X))) hF a := by
  have h := map_comp (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl F hF a
  rw [← h,diagonal_split]
  change mapHom (N := N) F hF (_ * _) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (map_comp _ _ _ _ a) (map_comp _ _ _ _ a)

-- @@ L156-156 verbatim
end

-- @@ L157-157 verbatim
open scoped Topology Topology.Homotopy

-- @@ L158-158 verbatim
universe u v w

-- @@ L159-159 verbatim
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

-- @@ L160-160 verbatim
variable {x : X} {y : Y}

-- @@ L161-169 verbatim
lemma map_eq_of_homotopy (f g : C(X,Y)) (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t,x) = y) (a : HomotopyGroup N X x) :
    map f hf a = map g hg a := by
  induction a using Quotient.inductionOn with | h p =>
  apply Quotient.sound
  refine ⟨{ toHomotopy := H.compContinuousMap p.1,prop' := ?_ }⟩
  intro t z hz
  change H (t,p z) = f (p z)
  rw [GenLoop.boundary p z hz,hH,hf]

-- @@ L170-170 verbatim
end UniversalFInfinity.HomotopyFunctor

-- @@ L171-171 verbatim
namespace UniversalFInfinity.Milnor


-- @@ L173-173 verbatim
section

-- @@ L174-174 verbatim
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial

-- @@ L175-175 verbatim
open scoped Classical Topology.Homotopy

-- @@ L176-176 verbatim
universe u v

-- @@ L177-177 verbatim
variable (G : Type u) [Group G]

-- @@ L178-178 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L180-180 verbatim
abbrev Shapes := Finset (Finset (ℕ × G))

-- @@ L181-181 verbatim
def basedShapes (S : Shapes G) : Shapes G := insert {(0,1)} S

-- @@ L182-182 verbatim
def stage (S : Shapes G) := orbitSpan (basedShapes G S)


-- @@ L184-185 verbatim
lemma stage_mono {S T : Shapes G} (h : S ⊆ T) : stage G S ≤ stage G T :=
  orbitSpan_mono (Finset.insert_subset_insert _ h)


-- @@ L187-190 verbatim
lemma stage_point_face (S : Shapes G) : {(0,1)} ∈ stage G S := by
  apply orbitSpan_contains (basedShapes G S)
  · exact ⟨Finset.singleton_nonempty _,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (0,(1:G))⟩
  · exact ⟨{(0,1)},Finset.mem_insert_self _ _,Finset.Subset.refl _⟩


-- @@ L192-194 verbatim
def stagePoint (S : Shapes G) : Simplicial.Space (stage G S) :=
  ⟨Finsupp.single (0,1) 1,by intro w; simp only [Finsupp.single_apply]; split_ifs <;> norm_num,
    by simp,by simpa only [Finsupp.support_single _ one_ne_zero] using stage_point_face G S⟩


-- @@ L196-197 verbatim
def stageIncl (S T : Shapes G) (h : S ⊆ T) : C(Simplicial.Space (stage G S),Simplicial.Space (stage G T)) :=
  ⟨inclusion _ _ (fun _ hs => stage_mono G h hs),continuous_inclusion _ _ _⟩


-- @@ L199-199 verbatim
lemma stageIncl_point (S T : Shapes G) (h : S ⊆ T) : stageIncl G S T h (stagePoint G S) = stagePoint G T := rfl


-- @@ L201-201 verbatim
variable (N : Type v) [DecidableEq N] [Nonempty N]

-- @@ L202-205 verbatim
def stageHom (S T : Shapes G) (h : S ⊆ T) :
    HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S) →*
      HomotopyGroup N (Simplicial.Space (stage G T)) (stagePoint G T) :=
  HomotopyFunctor.mapHom (stageIncl G S T h) rfl


-- @@ L207-212 verbatim
instance : DirectedSystem (fun S : Shapes G => HomotopyGroup N (Simplicial.Space (stage G S)) (stagePoint G S))
    (fun S T h => stageHom G N S T h) where
  map_self _ a := by
    exact HomotopyFunctor.map_id a
  map_map _ _ _ h₁ h₂ a := by
    exact HomotopyFunctor.map_comp _ _ _ _ a


-- @@ L214-214 verbatim
end


-- @@ L216-216 verbatim
section

-- @@ L217-217 verbatim
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial

-- @@ L218-218 verbatim
open scoped Classical unitInterval

-- @@ L219-219 verbatim
universe u

-- @@ L220-220 verbatim
variable {G : Type u} [Group G]

-- @@ L221-221 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L223-236 verbatim
instance : MulAction G (Space G) where
  smul g x := map (g * ·) id Function.injective_id x
  one_smul x := by
    change map (1 * ·) id Function.injective_id x = x
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,1*v.2)) = x.1
    rw [show (fun v : ℕ × G => (v.1,1*v.2)) = id from funext (fun v => Prod.ext rfl (one_mul v.2))]
    exact Finsupp.mapDomain_id
  mul_smul g h x := by
    change map ((g*h) * ·) id Function.injective_id x = map (g * ·) id Function.injective_id (map (h * ·) id Function.injective_id x)
    rw [map_comp]
    have he : (fun a => (g*h)*a) = ((g * ·) ∘ (h * ·)) := funext (mul_assoc g h)
    rw [he]
    rfl


-- @@ L238-239 verbatim
instance : ContinuousConstSMul G (Space G) where
  continuous_const_smul g := (map (g * ·) id Function.injective_id).continuous


-- @@ L241-247 verbatim
lemma smul_weight (g : G) (x : Space G) (v : ℕ × G) : (g • x).1 (v.1,g*v.2) = x.1 v := by
  change (x.1.mapDomain (fun w => (w.1,g*w.2))) (v.1,g*v.2) = x.1 v
  apply Finsupp.mapDomain_apply_of_injective (f := fun w : ℕ × G => (w.1,g*w.2))
  intro a b hab
  have hfst := congrArg (fun p : ℕ × G => p.1) hab
  have hsnd := congrArg (fun p : ℕ × G => p.2) hab
  exact Prod.ext hfst (mul_left_cancel hsnd)


-- @@ L249-250 verbatim
lemma smul_weight_inv (g : G) (x : Space G) (v : ℕ × G) : (g • x).1 v = x.1 (v.1,g⁻¹*v.2) := by
  simpa only [mul_inv_cancel_left] using smul_weight g x (v.1,g⁻¹*v.2)


-- @@ L252-269 verbatim
lemma exists_disjoint_nhds (x : Space G) :
    ∃ U ∈ 𝓝 x, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  obtain ⟨v,hv⟩ := Simplicial.support_nonempty x.2.2.1
  let U : Set (Space G) := {y | 0 < y.1 v}
  have hx : x ∈ U := lt_of_le_of_ne (x.2.1 v) (Ne.symm (Finsupp.mem_support_iff.mp hv))
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_eval (complex G) v)
  refine ⟨U,hU.mem_nhds hx,?_⟩
  intro g hg
  obtain ⟨z,⟨y,hy,rfl⟩,hgy⟩ := hg
  have h1 : v ∈ y.1.support := Finsupp.mem_support_iff.mpr (ne_of_gt hy)
  have h2 : (v.1,g⁻¹*v.2) ∈ y.1.support := by
    apply Finsupp.mem_support_iff.mpr
    have hp : 0 < (g • y).1 v := hgy
    rw [smul_weight_inv] at hp
    exact ne_of_gt hp
  have he := congrArg Prod.snd (y.2.2.2.2 h1 h2 rfl)
  have hi : g⁻¹ = 1 := (mul_right_cancel (he.symm.trans (one_mul v.2).symm))
  exact inv_eq_one.mp hi


-- @@ L271-276 verbatim
lemma quotientCovering : IsQuotientCoveringMap
    (Quotient.mk (MulAction.orbitRel G (Space G))) G where
  __ := isQuotientMap_quotient_mk'
  continuous_const_smul g := continuous_const_smul g
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint := exists_disjoint_nhds


-- @@ L278-278 verbatim
end

-- @@ L279-279 verbatim
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial

-- @@ L280-280 verbatim
open scoped Classical

-- @@ L281-281 verbatim
universe u v

-- @@ L282-282 verbatim
variable (G : Type u) [Group G]

-- @@ L283-283 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L285-285 verbatim
abbrev Stage (S : Shapes G) := Simplicial.Space (stage G S)


-- @@ L287-288 verbatim
def stageFull (S : Shapes G) : C(Stage G S,Space G) :=
  ⟨inclusion _ _ (fun _ h => orbitSpan_le _ h),continuous_inclusion _ _ _⟩

-- @@ L289-290 verbatim
lemma stageFull_embedding (S : Shapes G) : IsClosedEmbedding (stageFull G S) :=
  inclusion_closedEmbedding _ _ (fun _ h => orbitSpan_le _ h)


-- @@ L292-293 verbatim
lemma stage_translate (S : Shapes G) (g : G) (s : Face (stage G S)) :
    s.1.image (fun v => (v.1,g*v.2)) ∈ stage G S := orbitSpan_invariant _ g s.2


-- @@ L295-296 verbatim
def stageSmul (S : Shapes G) (g : G) : C(Stage G S,Stage G S) :=
  Simplicial.mapC _ _ (fun v => (v.1,g*v.2)) (stage_translate G S g)


-- @@ L298-312 verbatim
instance stageAction (S : Shapes G) : MulAction G (Stage G S) where
  smul g x := stageSmul G S g x
  one_smul x := by
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,1*v.2)) = x.1
    rw [show (fun v : ℕ × G => (v.1,1*v.2)) = id from funext (fun v => Prod.ext rfl (one_mul v.2))]
    exact Finsupp.mapDomain_id
  mul_smul g h x := by
    apply Subtype.ext
    change x.1.mapDomain (fun v => (v.1,(g*h)*v.2)) =
      (x.1.mapDomain (fun v => (v.1,h*v.2))).mapDomain (fun v => (v.1,g*v.2))
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext v
    exact Prod.ext rfl (mul_assoc _ _ _)


-- @@ L314-315 verbatim
instance stageContinuousAction (S : Shapes G) : ContinuousConstSMul G (Stage G S) where
  continuous_const_smul g := (stageSmul G S g).continuous


-- @@ L317-318 verbatim
lemma stageFull_smul (S : Shapes G) (g : G) (x : Stage G S) :
    stageFull G S (g • x) = g • stageFull G S x := rfl

-- @@ L319-320 verbatim
lemma stageIncl_smul (S T : Shapes G) (h : S ⊆ T) (g : G) (x : Stage G S) :
    stageIncl G S T h (g • x) = g • stageIncl G S T h x := rfl


-- @@ L322-330 verbatim
lemma compact_controlled {K : Set (Space G)} (hK : IsCompact K) :
    ∃ S : Shapes G, K ⊆ Set.range (stageFull G S) := by
  obtain ⟨V,hV⟩ := Simplicial.compact_bounded_vertices (complex G) hK
  refine ⟨V.powerset,?_⟩
  intro x hx
  have hm : x.1.support ∈ stage G V.powerset := by
    apply orbitSpan_contains (basedShapes G V.powerset) x.2.2.2
    exact ⟨x.1.support,Finset.mem_insert_of_mem (Finset.mem_powerset.mpr (hV x hx)),Finset.Subset.refl _⟩
  exact ⟨⟨x.1,x.2.1,x.2.2.1,hm⟩,rfl⟩


-- @@ L332-339 verbatim
lemma compact_orbit_controlled {K : Set (Space G)} (hK : IsCompact K) :
    ∃ S : Shapes G, ∀ g : G, (g • ·) '' K ⊆ Set.range (stageFull G S) := by
  obtain ⟨S,hS⟩ := compact_controlled G hK
  refine ⟨S,?_⟩
  intro g y hy
  obtain ⟨x,hx,rfl⟩ := hy
  obtain ⟨z,rfl⟩ := hS hx
  exact ⟨g • z,stageFull_smul G S g z⟩


-- @@ L341-341 verbatim
variable {X : Type v} [TopologicalSpace X] [MulAction G X]


-- @@ L343-344 verbatim
def CompactFundamentalSet : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, ∃ y ∈ K, x = g • y


-- @@ L346-355 verbatim
lemma equivariant_controlled (hX : CompactFundamentalSet G (X := X))
    (f : C(X,Space G)) (hf : ∀ (g : G) x, f (g • x) = g • f x) :
    ∃ S : Shapes G, Set.range f ⊆ Set.range (stageFull G S) := by
  obtain ⟨K,hK,hcov⟩ := hX
  obtain ⟨S,hS⟩ := compact_orbit_controlled G (hK.image f.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [hf]
  exact hS g ⟨f y,⟨y,hy,rfl⟩,rfl⟩


-- @@ L357-363 verbatim
def factorStage (f : C(X,Space G)) (S : Shapes G)
    (hf : Set.range f ⊆ Set.range (stageFull G S)) : C(X,Stage G S) where
  toFun x := (hf (Set.mem_range_self x)).choose
  continuous_toFun := (stageFull_embedding G S).isEmbedding.continuous_iff.mpr (by
    convert f.continuous using 1
    funext x
    exact (hf (Set.mem_range_self x)).choose_spec)

-- @@ L364-367 verbatim
omit [MulAction G X] in
lemma factorStage_spec (f : C(X,Space G)) (S : Shapes G)
    (hf : Set.range f ⊆ Set.range (stageFull G S)) (x : X) :
    stageFull G S (factorStage G f S hf x) = f x := (hf (Set.mem_range_self x)).choose_spec

-- @@ L368-373 verbatim
lemma factorStage_smul (f : C(X,Space G)) (S : Shapes G)
    (hf : Set.range f ⊆ Set.range (stageFull G S))
    (he : ∀ (g : G) x, f (g • x) = g • f x) (g : G) (x : X) :
    factorStage G f S hf (g • x) = g • factorStage G f S hf x := by
  apply (stageFull_embedding G S).injective
  rw [factorStage_spec,stageFull_smul,factorStage_spec,he]

-- @@ L374-374 verbatim
end UniversalFInfinity.Milnor


-- @@ L376-376 verbatim
open Set Metric Topology


-- @@ L378-378 verbatim
end


-- @@ L380-380 verbatim
end OAI
