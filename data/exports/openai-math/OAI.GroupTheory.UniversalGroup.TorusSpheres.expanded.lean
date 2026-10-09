import OAI.GroupTheory.UniversalGroup.TorusHomotopies


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
open Set Topology UniversalFInfinity.Simplicial

-- @@ L19-19 verbatim
open scoped Classical unitInterval

-- @@ L20-20 verbatim
universe u v w

-- @@ L21-21 verbatim
variable {G : Type u} {H : Type v}

-- @@ L22-22 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

-- @@ L23-23 verbatim
def evenLayer (n : ℕ) := 2*n

-- @@ L24-24 verbatim
def oddLayer (n : ℕ) := 2*n+1

-- @@ L25-25 verbatim
lemma evenLayer_injective : Function.Injective evenLayer := by intro a b h; unfold evenLayer at h; omega

-- @@ L26-26 verbatim
lemma oddLayer_injective : Function.Injective oddLayer := by intro a b h; unfold oddLayer at h; omega

-- @@ L27-27 verbatim
lemma even_ne_odd (a b : ℕ) : evenLayer a ≠ oddLayer b := by unfold evenLayer oddLayer; omega


-- @@ L29-43 verbatim
lemma mixed_face (φ ψ : G → H) (s : Face (complex G)) :
    s.1.image (fun v => (evenLayer v.1,φ v.2)) ∪ s.1.image (fun v => (oddLayer v.1,ψ v.2)) ∈ complex H := by
  have h1 := map_face φ evenLayer evenLayer_injective s
  have h2 := map_face ψ oddLayer oddLayer_injective s
  refine ⟨h1.1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact h1.2 hx hy hxy
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact False.elim (even_ne_odd a.1 b.1 hxy)
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact False.elim (even_ne_odd b.1 a.1 hxy.symm)
  · exact h2.2 hx hy hxy


-- @@ L45-48 verbatim
def mixedHomotopy (φ ψ : G → H) :
    (map φ evenLayer evenLayer_injective).Homotopy (map ψ oddLayer oddLayer_injective) :=
  straightHomotopy (complex G) (complex H) _ _
    (map_face φ evenLayer evenLayer_injective) (map_face ψ oddLayer oddLayer_injective) (mixed_face φ ψ)


-- @@ L50-52 verbatim
def bridge (φ ψ : G → H) :
    (map φ evenLayer evenLayer_injective).Homotopy (map ψ evenLayer evenLayer_injective) :=
  (mixedHomotopy φ φ).trans (mixedHomotopy ψ φ).symm


-- @@ L54-59 verbatim
lemma map_natural (φ φ' : G → H) (δ : G → G) (θ : H → H)
    (h : ∀ x,φ' (δ x) = θ (φ x)) (α : ℕ → ℕ) (hα : Function.Injective α) (x : Space G) :
    map φ' α hα (map δ id Function.injective_id x) =
      map θ id Function.injective_id (map φ α hα x) := by
  rw [map_comp,map_comp]
  exact congrArg (fun φ => map φ α hα x) (funext h)


-- @@ L61-72 verbatim
lemma mixedHomotopy_natural (φ ψ φ' ψ' : G → H) (δ : G → G) (θ : H → H)
    (hφ : ∀ x,φ' (δ x) = θ (φ x)) (hψ : ∀ x,ψ' (δ x) = θ (ψ x)) (t : I) (x : Space G) :
    mixedHomotopy φ' ψ' (t,map δ id Function.injective_id x) =
      map θ id Function.injective_id (mixedHomotopy φ ψ (t,x)) := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (map φ' evenLayer evenLayer_injective (map δ id Function.injective_id x)).1 +
    (t:ℝ) • (map ψ' oddLayer oddLayer_injective (map δ id Function.injective_id x)).1 =
      ((1-(t:ℝ)) • (map φ evenLayer evenLayer_injective x).1 +
        (t:ℝ) • (map ψ oddLayer oddLayer_injective x).1).mapDomain (fun v => (v.1,θ v.2))
  rw [map_natural _ _ _ _ hφ,map_natural _ _ _ _ hψ,Finsupp.mapDomain_add,
    Finsupp.mapDomain_smul,Finsupp.mapDomain_smul]
  rfl


-- @@ L74-81 verbatim
lemma bridge_natural (φ ψ φ' ψ' : G → H) (δ : G → G) (θ : H → H)
    (hφ : ∀ x,φ' (δ x) = θ (φ x)) (hψ : ∀ x,ψ' (δ x) = θ (ψ x)) (t : I) (x : Space G) :
    bridge φ' ψ' (t,map δ id Function.injective_id x) =
      map θ id Function.injective_id (bridge φ ψ (t,x)) := by
  simp only [bridge,ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact mixedHomotopy_natural φ φ φ' φ' δ θ hφ hφ _ x
  · exact mixedHomotopy_natural ψ φ ψ' φ' δ θ hψ hφ _ x

-- @@ L82-82 verbatim
end UniversalFInfinity.Milnor


-- @@ L84-84 verbatim
namespace UniversalFInfinity.TorusGeometry

-- @@ L85-85 verbatim
open Set Topology AscendingTorus

-- @@ L86-86 verbatim
open scoped Classical unitInterval

-- @@ L87-87 verbatim
universe u

-- @@ L88-88 verbatim
variable {U : Type u} [Group U] (f : Monoid.End U)


-- @@ L90-90 verbatim
def lowerLabel (c : Coset f) (u : U) : Torus f := origin f c * of f u

-- @@ L91-91 verbatim
def upperLabel (c : Coset f) (u : U) : Torus f := lowerLabel f (next f c) (cosetOffset f c * f u)


-- @@ L93-94 verbatim
def vertexToMilnor (c : Coset f) : C(Milnor.Space U,Milnor.Space (Torus f)) :=
  Milnor.map (lowerLabel f c) Milnor.evenLayer Milnor.evenLayer_injective


-- @@ L96-97 verbatim
def edgeToMilnor (c : Coset f) : C(I × Milnor.Space U,Milnor.Space (Torus f)) :=
  (Milnor.bridge (lowerLabel f c) (upperLabel f c)).toContinuousMap


-- @@ L99-101 verbatim
lemma edgeToMilnor_zero (c : Coset f) (x : Milnor.Space U) :
    edgeToMilnor f c (0,x) = vertexToMilnor f c x :=
  (Milnor.bridge (lowerLabel f c) (upperLabel f c)).apply_zero x

-- @@ L102-110 verbatim
lemma edgeToMilnor_one (c : Coset f) (x : Milnor.Space U) :
    edgeToMilnor f c (1,x) = vertexToMilnor f (next f c) (transition f c x) := by
  change Milnor.bridge _ _ (1,x) = _
  rw [ContinuousMap.Homotopy.apply_one]
  change Milnor.map (upperLabel f c) Milnor.evenLayer Milnor.evenLayer_injective x =
    Milnor.map (lowerLabel f (next f c)) Milnor.evenLayer Milnor.evenLayer_injective
      (Milnor.map (cosetOffset f c * ·) id Function.injective_id (Milnor.map f id Function.injective_id x))
  rw [Milnor.map_comp,Milnor.map_comp]
  rfl


-- @@ L112-114 verbatim
def toMilnor : C(Space f,Milnor.Space (Torus f)) :=
  GraphBundle.lift (next f) (fun _ => .id _) (transition f) (vertexToMilnor f) (edgeToMilnor f)
    (edgeToMilnor_zero f) (edgeToMilnor_one f)

-- @@ L115-116 verbatim
lemma toMilnor_vertex (c : Coset f) (x : Milnor.Space U) :
    toMilnor f (vertex f c x) = vertexToMilnor f c x := rfl

-- @@ L117-119 verbatim
lemma toMilnor_edge (c : Coset f) (t : I) (x : Milnor.Space U) :
    toMilnor f (GraphBundle.edge _ _ _ c t x) = edgeToMilnor f c (t,x) :=
  GraphBundle.lift_edge _ _ _ _ _ _ _ c (t,x)


-- @@ L121-124 verbatim
lemma lowerLabel_action (g : Torus f) (c : Coset f) (u : U) :
    lowerLabel f (g • c) (actionOffset f g c * u) = g * lowerLabel f c u := by
  unfold lowerLabel
  rw [map_mul,←mul_assoc,origin_action,mul_assoc]

-- @@ L125-129 verbatim
lemma upperLabel_action (hf : Function.Injective f) (g : Torus f) (c : Coset f) (u : U) :
    upperLabel f (g • c) (actionOffset f g c * u) = g * upperLabel f c u := by
  unfold upperLabel
  rw [map_mul,←mul_assoc,←actionOffset_next f hf,mul_assoc,next_smul]
  exact lowerLabel_action f g (next f c) (cosetOffset f c * f u)


-- @@ L131-131 verbatim
variable [Fact (Function.Injective f)]

-- @@ L132-132 verbatim
local notation "hf" => (Fact.out : Function.Injective f)

-- @@ L133-133 verbatim
local instance : MulAction (Torus f) (Space f) := action f hf

-- @@ L134-149 verbatim
lemma toMilnor_equivariant (g : Torus f) (x : Space f) :
    toMilnor f (g • x) = g • toMilnor f x := by
  change GraphBundle.Core (C := Coset f) (A := Milnor.Space U) (B := Milnor.Space U) at x
  cases x with
  | inl x =>
    change vertexToMilnor f (g • x.1) (actionOffset f g x.1 • x.2) = g • vertexToMilnor f x.1 x.2
    exact Milnor.map_natural (lowerLabel f x.1) (lowerLabel f (g • x.1))
      (actionOffset f g x.1 * ·) (g * ·) (lowerLabel_action f g x.1) _ _ x.2
  | inr x =>
    let t : I := ⟨x.2.1.1,x.2.1.2.1.le,x.2.1.2.2.le⟩
    have hx : (Sum.inr x : Space f) = GraphBundle.edge (next f) (fun _ => ContinuousMap.id _)
        (transition f) x.1 t x.2.2 := (GraphBundle.edge_inner _ _ _ _ _ _).symm
    rw [hx,smul_edge,toMilnor_edge,toMilnor_edge]
    exact Milnor.bridge_natural (lowerLabel f x.1) (upperLabel f x.1)
      (lowerLabel f (g • x.1)) (upperLabel f (g • x.1)) (actionOffset f g x.1 * ·) (g * ·)
      (lowerLabel_action f g x.1) (upperLabel_action f hf g x.1) _ x.2.2

-- @@ L150-150 verbatim
end UniversalFInfinity.TorusGeometry


-- @@ L152-152 verbatim
namespace UniversalFInfinity.GraphBundle

-- @@ L153-153 verbatim
open Set Topology Cellular

-- @@ L154-154 verbatim
open scoped unitInterval

-- @@ L155-155 verbatim
universe u v

-- @@ L156-156 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L157-157 verbatim
variable {A : Type v} [TopologicalSpace A]

-- @@ L158-158 verbatim
variable (τ : C → C) (F : C → C(A,A)) (z : A)

-- @@ L159-159 verbatim
variable (H : (ContinuousMap.id A).Homotopy (.const _ z))


-- @@ L161-177 verbatim
def contractionSquare (c : C) : SquareBoundary A A where
  b := (ContinuousMap.curry ((F c).comp .fst)).prodMk
    (.const _ ⟨fun t => H (t,F c z),H.continuous.comp (continuous_id.prodMk continuous_const)⟩)
  c := (ContinuousMap.curry ⟨fun p : A × I => F c (H (p.2,p.1)),
      (F c).continuous.comp (H.continuous.comp continuous_swap)⟩).prodMk
    (ContinuousMap.curry ⟨fun p : A × I => H (p.2,F c p.1),
      H.continuous.comp (continuous_snd.prodMk ((F c).continuous.comp continuous_fst))⟩)
  zero x := by
    apply Prod.ext <;> change F c x = _
    · exact congrArg (F c) (H.apply_zero x).symm
    · exact (H.apply_zero (F c x)).symm
  one x := by
    apply Prod.ext
    · change H (0,F c z) = F c (H (1,x))
      rw [H.apply_zero,H.apply_one]; rfl
    · change H (1,F c z) = H (1,F c x)
      rw [H.apply_one,H.apply_one]; rfl


-- @@ L179-186 verbatim
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma contractionSquare_filling (c : C) :
    ∃ Q : C(A,C(I,C(I,A))),
      (∀ x t,Q x 0 t = F c x) ∧
      (∀ x t,Q x 1 t = H (t,F c z)) ∧
      (∀ x s,Q x s 0 = F c (H (s,x))) ∧
      (∀ x s,Q x s 1 = H (s,F c x)) :=
  (contractionSquare F z H c).fill_after_nullhomotopy (.id A) z H


-- @@ L188-231 verbatim
include z H in

theorem homogeneous_contractible
    (height : C → ℤ) (hτ : ∀ c,height (τ c) = height c+1)
    (hc : ∀ c d,∃ m n : ℕ,τ^[m] c = τ^[n] d) (root : C) :
    ContractibleSpace (Space τ (fun _ => ContinuousMap.id A) F) := by
  choose Q hQ0 hQ1 hQL hQR using contractionSquare_filling F z H
  let L : C → C(A,A) := fun _ => .id A
  let W := Space τ L F
  let y : C → W := fun c => vertex τ L F c z
  let V (c : C) : ((ContinuousMap.id W).comp (vertexMap τ L F c)).Homotopy (.const _ (y c)) :=
    (ContinuousMap.Homotopy.refl (vertexMap τ L F c)).comp H
  let b (c : C) : C(A,W) := (vertexMap τ L F (τ c)).comp (F c)
  let E (c : C) (x : A) : Path (vertex τ L F c x) (b c x) := edgePath τ L F c x
  let J (c : C) : C(A,C(I,C(I,W))) := ContinuousMap.curry (ContinuousMap.curry
    ((vertexMap τ L F (τ c)).comp ((Q c).uncurry.uncurry)))
  let P (c : C) : Path (b c z) (y (τ c)) :=
    { toFun t := vertex τ L F (τ c) (H (t,F c z))
      continuous_toFun := (vertexMap τ L F (τ c)).continuous.comp
        (H.continuous.comp (continuous_id.prodMk continuous_const))
      source' := congrArg (vertex τ L F (τ c)) (H.apply_zero (F c z))
      target' := congrArg (vertex τ L F (τ c)) (H.apply_one (F c z)) }
  let p (c : C) : Path (y c) (y (τ c)) := (E c z).trans (P c)
  have he (c : C) : Continuous (fun a : A × I => E c a.1 a.2) :=
    (edgeMap τ L F c).continuous.comp continuous_swap
  have hleft (c : C) (t : I) (x : A) : vertexMap τ L F c (H (t,x)) = V c (t,L c x) := rfl
  have hleftQ (c : C) (x : A) (t : I) : J c x t 0 = b c (H (t,x)) :=
    congrArg (vertex τ L F (τ c)) (hQL c x t)
  have hrightQ (c : C) (x : A) (t : I) : J c x t 1 = V (τ c) (t,F c x) :=
    congrArg (vertex τ L F (τ c)) (hQR c x t)
  apply (contractible_iff_id_nullhomotopic _).mpr
  apply nullhomotopic_of_coherent_contraction τ L F (.id W) y V (vertexMap τ L F) b E he
    (fun _ => H.toContinuousMap) J hleft hleftQ hrightQ
    (fun c x s => ?_) (fun c x s => ?_) p (fun c x s => ?_) height hτ hc root
  · change edge τ L F c s (H (0,x)) = edge τ L F c s x
    rw [H.apply_zero]; rfl
  · exact congrArg (vertex τ L F (τ c)) (hQ0 c x s)
  · change ((E c (H (1,x))).trans (connectorPath τ L F (.id W) y V b
        (fun _ => H.toContinuousMap) J hleftQ hrightQ c (1,x))) s = ((E c z).trans (P c)) s
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs
    · change edge τ L F c _ (H (1,x)) = edge τ L F c _ z
      rw [H.apply_one]; rfl
    · exact congrArg (vertex τ L F (τ c)) (hQ1 c x _)

-- @@ L232-232 verbatim
end UniversalFInfinity.GraphBundle


-- @@ L234-234 verbatim
namespace UniversalFInfinity.TorusGeometry

-- @@ L235-235 verbatim
open Set Topology Milnor AscendingTorus

-- @@ L236-236 verbatim
variable {U : Type*} [Group U] (f : Monoid.End U)


-- @@ L238-242 verbatim
lemma contractible : ContractibleSpace (Space f) := by
  have h := (contractible_iff_id_nullhomotopic (Milnor.Space U)).mp (Milnor.contractible (G := U))
  obtain ⟨z,⟨H⟩⟩ := h
  exact GraphBundle.homogeneous_contractible (next f) (transition f) z H
    (cosetHeight f) (height_next f) (common_descendant f) (coset f 1)

-- @@ L243-243 verbatim
end UniversalFInfinity.TorusGeometry

-- @@ L244-244 verbatim
namespace UniversalFInfinity.Milnor

-- @@ L245-245 verbatim
open Set Metric Topology Cellular

-- @@ L246-246 verbatim
universe u

-- @@ L247-247 verbatim
variable (G : Type u) [Group G]

-- @@ L248-248 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L250-256 verbatim
lemma stageCell_dimension_bound (S : Shapes G) (n : ℕ) (i : StageCell G S n) :
    n < (basedShapes G S).sup Finset.card := by
  obtain ⟨g,s,hs,his⟩ := i.1.2.2
  have hcard := Finset.card_le_card his
  rw [translate_card,i.2] at hcard
  have hd := Finset.le_sup (f := Finset.card) hs
  omega


-- @@ L258-271 verbatim
lemma stageEquivariant_bounded (S : Shapes G) :
    let : CWComplex (univ : Set (Stage G S)) := stageEquivariantCW G S
    ∃ d : ℕ, Skeleton (univ : Set (Stage G S)) d = univ := by
  let : CWComplex (univ : Set (Stage G S)) := stageEquivariantCW G S
  refine ⟨(basedShapes G S).sup Finset.card,Set.eq_univ_of_forall (fun x => ?_)⟩
  have hx : x ∈ (univ : Set (Stage G S)) := mem_univ _
  rw [←CWComplex.iUnion_openCell_eq_complex (C := (univ : Set (Stage G S)))] at hx
  simp only [mem_iUnion] at hx
  obtain ⟨n,i,hi⟩ := hx
  have hn := stageCell_dimension_bound G S n (cellCoordinates G S n i)
  exact CWComplex.skeletonLT_mono (C := (univ : Set (Stage G S)))
    (m := (n : ℕ∞)+1) (n := (((basedShapes G S).sup Finset.card : ℕ) : ℕ∞))
    (by exact_mod_cast Nat.succ_le_of_lt hn)
    (CWComplex.closedCell_subset_skeletonLT n i (CWComplex.openCell_subset_closedCell n i hi))


-- @@ L273-288 verbatim
lemma stage_compactFundamentalSet (S : Shapes G) : CompactFundamentalSet G (X := Stage G S) := by
  let : CWComplex (univ : Set (Stage G S)) := stageEquivariantCW G S
  let σ : ∀ n, (G × CellOrbits G S n) ≃ RelCWComplex.cell (univ : Set (Stage G S)) n :=
    fun _ => Equiv.refl _
  have hσ : ∀ n (g h : G) (i : CellOrbits G S n) (x : Fin n → ℝ),
    RelCWComplex.map n (σ n (g*h,i)) x = g • RelCWComplex.map n (σ n (h,i)) x := by
    intro n g h i x
    exact mul_smul g h _
  obtain ⟨d,hd⟩ := stageEquivariant_bounded G S
  obtain ⟨K,hK,hcov⟩ := skeleton_compact_representatives σ hσ d
  refine ⟨Subtype.val '' K,hK.image continuous_subtype_val,?_⟩
  intro x
  have hx : x ∈ Skeleton (univ : Set (Stage G S)) d := by rw [hd]; trivial
  obtain ⟨g,y,hy,he⟩ := hcov ⟨x,hx⟩
  refine ⟨g,y.1,⟨y,hy,rfl⟩,?_⟩
  exact congrArg Subtype.val he

-- @@ L289-289 verbatim
end UniversalFInfinity.Milnor

-- @@ L290-290 verbatim
namespace UniversalFInfinity.TorusGeometry

-- @@ L291-291 verbatim
open Set Topology AscendingTorus

-- @@ L292-292 verbatim
open scoped unitInterval

-- @@ L293-293 verbatim
universe u

-- @@ L294-294 verbatim
variable {U : Type u} [Group U] (f : Monoid.End U)

-- @@ L295-295 verbatim
variable [Fact (Function.Injective f)]

-- @@ L296-296 verbatim
local notation "hf" => (Fact.out : Function.Injective f)

-- @@ L297-297 verbatim
local instance : MulAction (Torus f) (Space f) := action f hf


-- @@ L299-313 verbatim
lemma exists_moveOffset (c d : Coset f) (u : U) :
    ∃ g : Torus f, g • c = d ∧ actionOffset f g c = u := by
  let g := origin f d * of f u * (origin f c)⁻¹
  have hg : g * origin f c = origin f d * of f u := by simp [g,mul_assoc]
  have hgc : g • c = d := by
    rw [←coset_origin f c,smul_coset,hg,←coset_origin f d]
    apply QuotientGroup.eq.mpr
    refine ⟨u⁻¹,?_⟩
    simp [map_inv,mul_assoc]
  refine ⟨g,hgc,?_⟩
  apply of_injective f hf
  apply mul_left_cancel (a := origin f d)
  have h := origin_action f g c
  rw [hgc,hg] at h
  exact h


-- @@ L315-347 verbatim
lemma stage_compact_representatives (S : Milnor.Shapes U) :
    ∃ K : Set (Space f), IsCompact K ∧
      ∀ x : Stage f S, ∃ g : Torus f, ∃ y ∈ K, stageFull f S x = g • y := by
  obtain ⟨A,hA,hAcov⟩ := Milnor.stage_compactFundamentalSet U (vertexShapes f S)
  obtain ⟨B,hB,hBcov⟩ := Milnor.stage_compactFundamentalSet U S
  let c := coset f 1
  let v : C(Milnor.Stage U (vertexShapes f S),Space f) :=
    (GraphBundle.vertexMap _ _ _ c).comp (Milnor.stageFull U (vertexShapes f S))
  let e : C(I × Milnor.Stage U S,Space f) :=
    (GraphBundle.edgeMap _ _ _ c).comp
      (ContinuousMap.prodMap (.id I) (Milnor.stageFull U S))
  let K := v '' A ∪ e '' (univ ×ˢ B)
  have hK : IsCompact K := (hA.image v.continuous).union ((isCompact_univ.prod hB).image e.continuous)
  refine ⟨K,hK,?_⟩
  intro x
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at x
  cases x with
  | inl x =>
    obtain ⟨u,y,hy,he⟩ := hAcov x.2
    obtain ⟨g,hg,ho⟩ := exists_moveOffset f c x.1 u
    refine ⟨g,v y,Or.inl ⟨y,hy,rfl⟩,?_⟩
    change vertex f x.1 (Milnor.stageFull U _ x.2) = g • vertex f c (Milnor.stageFull U _ y)
    rw [smul_vertex,hg,ho,he,Milnor.stageFull_smul]
  | inr x =>
    obtain ⟨u,y,hy,he⟩ := hBcov x.2.2
    obtain ⟨g,hg,ho⟩ := exists_moveOffset f c x.1 u
    let t : I := ⟨x.2.1.1,x.2.1.2.1.le,x.2.1.2.2.le⟩
    refine ⟨g,e (t,y),Or.inr ⟨(t,y),⟨mem_univ _,hy⟩,rfl⟩,?_⟩
    change stageFull f S (GraphBundle.interior _ _ _ x.1 x.2.1 x.2.2) = _
    rw [stageFull_interior]
    change GraphBundle.interior _ _ _ x.1 x.2.1 (Milnor.stageFull U _ x.2.2) =
      g • GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) c t (Milnor.stageFull U S y)
    rw [smul_edge,hg,ho,GraphBundle.edge_inner,he,Milnor.stageFull_smul]


-- @@ L349-359 verbatim
lemma toMilnor_controlled (S : Milnor.Shapes U) :
    ∃ T : Milnor.Shapes (Torus f), Set.range ((toMilnor f).comp (stageFull f S)) ⊆
      Set.range (Milnor.stageFull (Torus f) T) := by
  obtain ⟨K,hK,hcov⟩ := stage_compact_representatives f S
  obtain ⟨T,hT⟩ := Milnor.compact_orbit_controlled (Torus f) (hK.image (toMilnor f).continuous)
  refine ⟨T,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,he⟩ := hcov x
  change toMilnor f (stageFull f S x) ∈ _
  rw [he,toMilnor_equivariant]
  exact hT g ⟨toMilnor f y,⟨y,hy,rfl⟩,rfl⟩

-- @@ L360-360 verbatim
end UniversalFInfinity.TorusGeometry

-- @@ L361-361 verbatim
namespace UniversalFInfinity.SphereTopology

-- @@ L362-362 verbatim
open Set Topology Cellular

-- @@ L363-372 verbatim
lemma sphereFillable_of_contractible {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y] :
    SphereFillable Y := by
  obtain ⟨z,⟨H⟩⟩ := id_nullhomotopic Y
  intro n a
  cases n with
  | zero => exact fill_zero a
  | succ n =>
    let := sphere_nonempty n
    obtain ⟨e,he⟩ := extends_of_nullhomotopic (H.compContinuousMap a).symm
    exact ⟨e,fun x => ContinuousMap.congr_fun he x⟩

-- @@ L373-373 verbatim
end UniversalFInfinity.SphereTopology


-- @@ L375-375 verbatim
namespace UniversalFInfinity.TorusGeometry


-- @@ L377-377 verbatim
section

-- @@ L378-378 verbatim
open Set Topology AscendingTorus Cellular

-- @@ L379-379 verbatim
open scoped unitInterval

-- @@ L380-380 verbatim
universe u

-- @@ L381-381 verbatim
variable {U : Type u} [Group U] (f : Monoid.End U)

-- @@ L382-382 verbatim
variable [hfi : Fact (Function.Injective f)]

-- @@ L383-383 verbatim
local notation "hf" => (Fact.out : Function.Injective f)

-- @@ L384-384 verbatim
local instance : MulAction (Torus f) (Space f) := action f hf

-- @@ L385-385 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L387-461 verbatim
omit hfi in

theorem milnor_uniform_nullhomotopy [Fact (Function.Injective f)]
    (hgraph : ∀ S : Milnor.Shapes U, ∃ (R : Milnor.Shapes U) (hSR : S ⊆ R),
      (stageInclusion f S R hSR).Nullhomotopic)
    (S : Milnor.Shapes (Torus f)) :
    ∃ (R : Milnor.Shapes (Torus f)) (hSR : S ⊆ R),
      (Milnor.stageIncl (Torus f) S R hSR).Nullhomotopic := by
  let G := Torus f
  let : CWComplex (univ : Set (Milnor.Stage G S)) := Milnor.stageEquivariantCW G S
  let κ : ∀ n, (G × Milnor.CellOrbits G S n) ≃ RelCWComplex.cell (univ : Set (Milnor.Stage G S)) n :=
    fun _ => Equiv.refl _
  have hκ : ∀ n (g h : G) (i : Milnor.CellOrbits G S n) (x : Fin n → ℝ),
    RelCWComplex.map n (κ n (g*h,i)) x = g • RelCWComplex.map n (κ n (h,i)) x := by
    intro n g h i x
    exact mul_smul g h _
  obtain ⟨d,hd⟩ := Milnor.stageEquivariant_bounded G S
  let back : C(Milnor.Stage G S,Skeleton (univ : Set (Milnor.Stage G S)) d) :=
    ⟨fun x => ⟨x,by rw [hd]; trivial⟩,continuous_id.subtype_mk (fun x => by rw [hd]; trivial)⟩
  have hback (g : G) (x : Milnor.Stage G S) :
      back (g • x) = skeletonTranslate κ hκ d g (back x) := rfl
  let : ContractibleSpace (Space f) := contractible f
  have hfill := SphereTopology.sphereFillable_of_contractible (Y := Space f)
  obtain ⟨e,he⟩ := exists_equivariant_map_on_skeleton κ hκ d (fun n _ => hfill n)
  let e' := e.comp back
  have he' (g : G) x : e' (g • x) = g • e' x := by
    change e (back (g • x)) = g • e (back x)
    rw [hback,he]
  obtain ⟨A,hA⟩ := equivariant_controlled f (Milnor.stage_compactFundamentalSet G S) e' he'
  let q := factorStage f e' A hA
  obtain ⟨B,hAB,z,⟨J⟩⟩ := hgraph A
  obtain ⟨T,hT⟩ := toMilnor_controlled f B
  let tmap := Milnor.factorStage G ((toMilnor f).comp (stageFull f B)) T hT
  let a := (Milnor.stageFull G S).comp (skeletonInclusion (C := (univ : Set (Milnor.Stage G S))) d)
  let b := (toMilnor f).comp e
  have ha (g : G) x : a (skeletonTranslate κ hκ d g x) = g • a x := Milnor.stageFull_smul G S g x.1
  have hb (g : G) x : b (skeletonTranslate κ hκ d g x) = g • b x := by
    change toMilnor f (e (skeletonTranslate κ hκ d g x)) = g • toMilnor f (e x)
    rw [he,toMilnor_equivariant]
  obtain ⟨H,hH⟩ := exists_equivariant_homotopy_on_skeleton κ hκ d (Milnor.sphereFillable (1:G)) a b ha hb
  obtain ⟨Q,hQ⟩ := Milnor.controlled_skeleton_homotopy κ hκ d a b H hH
  let R := S ∪ T ∪ Q
  have hSR : S ⊆ R := Finset.subset_union_left.trans Finset.subset_union_left
  have hTR : T ⊆ R := Finset.subset_union_right.trans Finset.subset_union_left
  have hQR : Q ⊆ R := Finset.subset_union_right
  let out := (Milnor.stageIncl G T R hTR).comp tmap
  let inc := Milnor.stageIncl G S R hSR
  let target := out.comp ((stageInclusion f A B hAB).comp q)
  let H' := H.compContinuousMap back
  have hHR : Set.range H'.toContinuousMap ⊆ Set.range (Milnor.stageFull G R) := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := hQ (Set.mem_range_self (x.1,back x.2))
    exact ⟨Milnor.stageIncl G Q R hQR y,hy⟩
  let HTmap := Milnor.factorStage G H'.toContinuousMap R hHR
  have hout (y : Stage f B) : Milnor.stageFull G R (out y) = toMilnor f (stageFull f B y) := by
    change Milnor.stageFull G T (tmap y) = _
    exact Milnor.factorStage_spec G _ T hT y
  let HT : inc.Homotopy target :=
    { toContinuousMap := HTmap
      map_zero_left := fun x => by
        apply (Milnor.stageFull_embedding G R).injective
        change Milnor.stageFull G R (HTmap (0,x)) = Milnor.stageFull G R (inc x)
        rw [Milnor.factorStage_spec]
        change H' (0,x) = _
        rw [H'.apply_zero]
        rfl
      map_one_left := fun x => by
        apply (Milnor.stageFull_embedding G R).injective
        change Milnor.stageFull G R (HTmap (1,x)) = Milnor.stageFull G R (out (stageInclusion f A B hAB (q x)))
        rw [Milnor.factorStage_spec]
        change H' (1,x) = _
        rw [H'.apply_one,hout,stageInclusion_full,factorStage_spec]
        rfl }
  refine ⟨R,hSR,out z,⟨?_⟩⟩
  exact HT.trans ((ContinuousMap.Homotopy.refl out).comp (J.compContinuousMap q))

-- @@ L462-462 verbatim
end


-- @@ L464-464 verbatim
open Set Topology AscendingTorus ConcreteEnvelopes

-- @@ L465-466 verbatim
variable {U : Type} [Group U] [Group.IsFinitelyPresented U]
  [TopologicalSpace U] [DiscreteTopology U]

-- @@ L467-467 verbatim
variable (k : Index → U →* U) (hk : IsDiagram k)

-- @@ L468-468 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L470-481 verbatim
include hk in
lemma diagram_graph_uniform_nullhomotopy (S : Milnor.Shapes U) :
    let f : Monoid.End U := k (.inl P₂.identity)
    ∃ (R : Milnor.Shapes U) (hSR : S ⊆ R),
      (stageInclusion f S R hSR).Nullhomotopic := by
  apply uniform_stage_nullhomotopy
  intro A
  obtain ⟨n,T,q,z,hq,H⟩ := Milnor.diagram_uniform_stage_nullhomotopy k hk A
  refine ⟨n,T,q,z,?_,H⟩
  intro x
  apply Subtype.ext
  exact hq x


-- @@ L483-492 verbatim
include hk in

theorem diagram_milnor_uniform_nullhomotopy
    [Fact (Function.Injective (k (.inl P₂.identity)))]
    (S : Milnor.Shapes (Torus (k (.inl P₂.identity)))) :
    ∃ (R : Milnor.Shapes (Torus (k (.inl P₂.identity)))) (hSR : S ⊆ R),
      (Milnor.stageIncl (Torus (k (.inl P₂.identity))) S R hSR).Nullhomotopic :=
  @milnor_uniform_nullhomotopy U _ (k (.inl P₂.identity))
    ⟨(Fact.out : Function.Injective (k (.inl P₂.identity)))⟩
    (diagram_graph_uniform_nullhomotopy k hk) S

-- @@ L493-493 verbatim
end UniversalFInfinity.TorusGeometry


-- @@ L495-495 verbatim
end


-- @@ L497-497 verbatim
end OAI
