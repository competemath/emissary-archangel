import OAI.GroupTheory.UniversalGroup.Attachments


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set Metric Topology BigOperators

-- @@ L8-8 verbatim
open Set Metric Topology


-- @@ L10-10 verbatim
namespace UniversalFInfinity.Cellular

-- @@ L11-11 verbatim
universe u

-- @@ L12-12 verbatim
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]

-- @@ L13-13 verbatim
variable {C : Set X} [CWComplex C] {f : X → Y} (hf : IsClosedEmbedding f)


-- @@ L15-16 verbatim
def transportedMap (n : ℕ) (i : RelCWComplex.cell C n) : PartialEquiv (Fin n → ℝ) Y :=
  (RelCWComplex.map n i).trans (hf.isEmbedding.toPartialHomeomorph f).toPartialEquiv


-- @@ L18-19 verbatim
@[simp] lemma transportedMap_apply (n : ℕ) (i : RelCWComplex.cell C n) (x : Fin n → ℝ) :
    transportedMap hf n i x = f (RelCWComplex.map n i x) := rfl


-- @@ L21-25 verbatim
lemma transportedMap_source (n : ℕ) (i : RelCWComplex.cell C n) :
    (transportedMap hf n i).source = ball 0 1 := by
  simp only [transportedMap,PartialEquiv.trans_source,
    IsEmbedding.toPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ,
    RelCWComplex.source_eq]


-- @@ L27-29 verbatim
lemma transportedMap_image (n : ℕ) (i : RelCWComplex.cell C n) (S : Set (Fin n → ℝ)) :
    transportedMap hf n i '' S = f '' (RelCWComplex.map n i '' S) :=
  Set.image_comp f (RelCWComplex.map n i) S


-- @@ L31-33 verbatim
lemma transportedMap_continuousOn (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)


-- @@ L35-41 verbatim
lemma transportedMap_continuousOn_symm (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (transportedMap hf n i).symm (transportedMap hf n i).target := by
  let e := hf.isEmbedding.toPartialHomeomorph f
  change ContinuousOn (fun y => (RelCWComplex.map n i).symm (e.symm y))
    (e.target ∩ e.symm ⁻¹' (RelCWComplex.map n i).target)
  exact (RelCWComplex.continuousOn_symm n i).comp
    (e.continuousOn_symm.mono Set.inter_subset_left) (fun _ h => h.2)


-- @@ L43-43 verbatim
variable [T2Space X]


-- @@ L45-87 verbatim
@[instance_reducible]
def transportCW : CWComplex (f '' C) where
  cell := RelCWComplex.cell C
  map := transportedMap hf
  source_eq := transportedMap_source hf
  continuousOn := transportedMap_continuousOn hf
  continuousOn_symm := transportedMap_continuousOn_symm hf
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (transportedMap hf p.1 p.2 '' ball 0 1)
      (transportedMap hf q.1 q.2 '' ball 0 1)
    rw [transportedMap_image,transportedMap_image]
    exact (CWComplex.disjoint_openCell_of_ne hpq).image hf.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
  mapsTo' := by
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n i
    refine ⟨I,?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n i x ∈ CWComplex.cellFrontier n i from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hx⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩⟩⟩
    rw [transportedMap_image]
    exact ⟨_,hx,rfl⟩
  closed' := by
    intro A hA hclosed
    have hpre : IsClosed (f ⁻¹' A) := by
      apply (CWComplex.closed C (f ⁻¹' A) ?_).mpr
      · intro n i
        have h := (hclosed n i).preimage hf.continuous
        rw [transportedMap_image,Set.preimage_inter,
          Set.preimage_image_eq _ hf.injective] at h
        exact h
      · intro x hx
        obtain ⟨y,hy,hyx⟩ := hA hx
        exact hf.injective hyx ▸ hy
    have h := hf.isClosedMap _ hpre
    rwa [Set.image_preimage_eq_of_subset (hA.trans (Set.image_subset_range f C))] at h
  union' := by
    simp only [transportedMap_image,← Set.image_iUnion]
    change f '' (⋃ n, ⋃ i, CWComplex.closedCell n i) = f '' C
    rw [CWComplex.union]


-- @@ L89-89 verbatim
end UniversalFInfinity.Cellular


-- @@ L91-91 verbatim
open Set Metric Topology

-- @@ L92-92 verbatim
namespace UniversalFInfinity.Attachment


-- @@ L94-94 verbatim
section

-- @@ L95-95 verbatim
open Set Metric Topology

-- @@ L96-96 verbatim
universe z

-- @@ L97-97 verbatim
variable {X : Type z} [TopologicalSpace X] [T2Space X] [Nonempty X]

-- @@ L98-98 verbatim
variable [CWComplex (Set.univ : Set X)] {ι : Type z} {n : ℕ}

-- @@ L99-99 verbatim
variable (a : ι → C(Sphere n,X))


-- @@ L101-101 verbatim
abbrev OldCell (m : ℕ) := RelCWComplex.cell (Set.univ : Set X) m


-- @@ L103-123 verbatim
omit [Nonempty X] in
lemma attaching_finite_frontier
    (hdim : ∀ m (_ : OldCell (X := X) m), m < n) (i : ι) :
    ∃ I : ∀ m, Finset (OldCell (X := X) m),
      ∀ x, a i x ∈ ⋃ m < n, ⋃ j ∈ I m, CWComplex.closedCell m j := by
  classical
  let S := {p : Σ m, OldCell (X := X) m |
    (Set.range (a i) ∩ CWComplex.openCell p.1 p.2).Nonempty}
  have hS : S.Finite := Cellular.compact_finitely_many_cells (C := (Set.univ : Set X))
    (isCompact_range (a i).continuous)
  have hSm (m : ℕ) : ((Sigma.mk m) ⁻¹' S).Finite :=
    hS.preimage (Set.injOn_of_injective (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2))
  refine ⟨fun m => (hSm m).toFinset,?_⟩
  intro x
  have hx : a i x ∈ (Set.univ : Set X) := Set.mem_univ _
  rw [← CWComplex.iUnion_openCell_eq_complex (C := (Set.univ : Set X))] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨m,j,hx⟩ := hx
  exact Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hdim m j,Set.mem_iUnion.mpr
    ⟨j,Set.mem_iUnion.mpr ⟨(hSm m).mem_toFinset.mpr ⟨a i x,⟨x,rfl⟩,hx⟩,
      CWComplex.openCell_subset_closedCell m j hx⟩⟩⟩⟩


-- @@ L125-125 verbatim
abbrev LayerCell (m : ℕ) := OldCell (X := X) m ⊕ CellIndex.{z,z} m n ι


-- @@ L127-130 verbatim
def layerMap (m : ℕ) : LayerCell (X := X) (ι := ι) (n := n) m →
    PartialEquiv (Fin m → ℝ) (Space a)
  | Sum.inl i => Cellular.transportedMap (C := Set.univ) (base_closedEmbedding a) m i
  | Sum.inr i => cellMap a m i


-- @@ L132-134 verbatim
omit [T2Space X] in
lemma layerMap_old_apply (m : ℕ) (i : OldCell (X := X) m) (x : Fin m → ℝ) :
    layerMap a m (Sum.inl i) x = base a (RelCWComplex.map m i x) := rfl


-- @@ L136-139 verbatim
omit [T2Space X] in
lemma layerMap_old_image (m : ℕ) (i : OldCell (X := X) m) (S : Set (Fin m → ℝ)) :
    layerMap a m (Sum.inl i) '' S = base a '' (RelCWComplex.map m i '' S) :=
  Cellular.transportedMap_image (base_closedEmbedding a) m i S


-- @@ L141-143 verbatim
omit [T2Space X] in
lemma layerMap_new (i : ι) :
    layerMap a n (Sum.inr ⟨⟨⟨rfl⟩,i⟩⟩) = characteristicPE a i := rfl


-- @@ L145-262 verbatim
@[instance_reducible]
def layerCW (hdim : ∀ m (_ : OldCell (X := X) m), m < n) :
    CWComplex (Set.univ : Set (Space a)) where
  cell := LayerCell (X := X) (ι := ι) (n := n)
  map := layerMap a
  source_eq := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_source (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).source_eq m i
  continuousOn := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_continuousOn (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).continuousOn m i
  continuousOn_symm := by
    intro m i
    cases i with
    | inl i => exact Cellular.transportedMap_continuousOn_symm (base_closedEmbedding a) m i
    | inr i => exact (relCWComplex a).continuousOn_symm m i
  pairwiseDisjoint' := by
    rintro ⟨m,i⟩ _ ⟨k,j⟩ _ hne
    change Disjoint (layerMap a m i '' ball 0 1) (layerMap a k j '' ball 0 1)
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        rw [layerMap_old_image,layerMap_old_image]
        apply (CWComplex.disjoint_openCell_of_ne ?_).image (base_closedEmbedding a).injective.injOn (Set.subset_univ _) (Set.subset_univ _)
        intro h
        cases h
        exact hne rfl
      | inr j =>
        obtain ⟨⟨⟨hk⟩,j⟩⟩ := j
        subst k
        rw [layerMap_old_image,layerMap_new,characteristicPE_image_ball]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,_,rfl⟩ ⟨y,h⟩
        cases h
    | inr i =>
      obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
      subst m
      cases j with
      | inl j =>
        rw [layerMap_new,characteristicPE_image_ball,layerMap_old_image]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,rfl⟩ ⟨y,_,h⟩
        cases h
      | inr j =>
        obtain ⟨⟨⟨hk⟩,j⟩⟩ := j
        subst k
        rw [layerMap_new,layerMap_new,characteristicPE_image_ball,characteristicPE_image_ball]
        apply Set.disjoint_left.mpr
        rintro z ⟨x,rfl⟩ ⟨y,h⟩
        have hij : j = i := congrArg Sigma.fst (Sum.inr_injective h)
        subst j
        exact hne rfl
  mapsTo' := by
    classical
    intro m c
    cases c with
    | inl i =>
      obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell m i
      refine ⟨fun k => (I k).image Sum.inl,?_⟩
      intro x hx
      have hh := hI (show RelCWComplex.map m i x ∈ CWComplex.cellFrontier m i from ⟨x,hx,rfl⟩)
      simp only [Set.mem_iUnion] at hh
      obtain ⟨k,hkm,j,hj,hx⟩ := hh
      refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkm,Set.mem_iUnion.mpr
        ⟨Sum.inl j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
      rw [layerMap_old_image]
      exact ⟨_,hx,rfl⟩
    | inr i =>
      obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
      subst m
      obtain ⟨I,hI⟩ := attaching_finite_frontier a hdim i
      refine ⟨fun k => (I k).image Sum.inl,?_⟩
      intro x hx
      have hh := hI ⟨x,hx⟩
      simp only [Set.mem_iUnion] at hh
      obtain ⟨k,hkn,j,hj,hx'⟩ := hh
      refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hkn,Set.mem_iUnion.mpr
        ⟨Sum.inl j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
      rw [layerMap_old_image]
      refine ⟨a i ⟨x,hx⟩,hx',?_⟩
      change base a (a i ⟨x,hx⟩) = characteristic a i x
      exact (cell_boundary a i ⟨x,hx⟩).symm.trans
        (characteristic_disk a i (boundary n ⟨x,hx⟩)).symm
  closed' := by
    intro A _ hA
    apply (isClosed_iff a A).mpr
    constructor
    · apply (CWComplex.closed Set.univ (base a ⁻¹' A) (Set.subset_univ _)).mpr
      intro m i
      have h := (hA m (Sum.inl i)).preimage (continuous_base a)
      rw [layerMap_old_image,Set.preimage_inter,
        Set.preimage_image_eq _ (base_closedEmbedding a).injective] at h
      exact h
    · intro i
      have h := (hA n (Sum.inr ⟨⟨⟨rfl⟩,i⟩⟩)).preimage (cell a i).continuous
      rw [layerMap_new,characteristicPE_image_closedBall,Set.preimage_inter] at h
      simpa only [Set.preimage_range,Set.inter_univ] using h
  union' := by
    apply Set.eq_univ_of_forall
    intro z
    cases z with
    | inl x =>
      have hx : x ∈ (Set.univ : Set X) := Set.mem_univ _
      rw [← CWComplex.union (C := (Set.univ : Set X))] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨m,i,hx⟩ := hx
      refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨Sum.inl i,?_⟩⟩
      rw [layerMap_old_image]
      exact ⟨x,hx,rfl⟩
    | inr p =>
      refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨Sum.inr ⟨⟨⟨rfl⟩,p.1⟩⟩,?_⟩⟩
      rw [layerMap_new,characteristicPE_image_closedBall]
      exact ⟨interior n p.2,cell_interior a p.1 p.2⟩


-- @@ L264-271 verbatim
lemma layerCW_dimensions (hdim : ∀ m (_ : OldCell (X := X) m), m < n)
    (m : ℕ) (i : (layerCW a hdim).cell m) : m < n+1 := by
  cases i with
  | inl i => exact (hdim m i).trans (Nat.lt_succ_self n)
  | inr i =>
    obtain ⟨⟨⟨hm⟩,i⟩⟩ := i
    subst m
    exact Nat.lt_succ_self n


-- @@ L273-279 verbatim
lemma layerCW_finite_cells [Finite ι]
    (hfin : ∀ m, Finite (OldCell (X := X) m))
    (hdim : ∀ m (_ : OldCell (X := X) m), m < n) (m : ℕ) :
    Finite ((layerCW a hdim).cell m) := by
  let := hfin m
  change Finite (LayerCell (X := X) (ι := ι) (n := n) m)
  infer_instance


-- @@ L281-281 verbatim
end


-- @@ L283-283 verbatim
section

-- @@ L284-284 verbatim
open Set Metric Topology

-- @@ L285-285 verbatim
universe u v w z

-- @@ L286-286 verbatim
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}

-- @@ L287-287 verbatim
variable (a : ι → C(Sphere n,X))

-- @@ L288-288 verbatim
variable {G : Type w} [Group G] [MulAction G X] [MulAction G ι]


-- @@ L290-301 verbatim
instance spaceMulAction : MulAction G (Space a) where
  smul g := Sum.elim (fun x => Sum.inl (g • x)) (fun p => Sum.inr ⟨g • p.1,p.2⟩)
  one_smul := by
    intro x
    cases x with
    | inl x => change Sum.inl ((1 : G) • x) = Sum.inl x; rw [one_smul]
    | inr p => change Sum.inr ⟨(1 : G) • p.1,p.2⟩ = Sum.inr p; rw [one_smul]
  mul_smul := by
    intro g h x
    cases x with
    | inl x => change Sum.inl ((g * h) • x) = Sum.inl (g • h • x); rw [mul_smul]
    | inr p => change (Sum.inr ⟨(g * h) • p.1,p.2⟩ : Space a) = Sum.inr ⟨g • h • p.1,p.2⟩; rw [mul_smul]


-- @@ L303-303 verbatim
@[simp] lemma smul_base (g : G) (x : X) : g • base a x = base a (g • x) := rfl

-- @@ L304-305 verbatim
@[simp] lemma smul_openCell (g : G) (i : ι) (x : OpenDisk n) :
    g • openCell a i x = openCell a (g • i) x := rfl


-- @@ L307-307 verbatim
variable (ha : ∀ (g : G) i x, a (g • i) x = g • a i x)

-- @@ L308-308 verbatim
include ha

-- @@ L309-321 verbatim
lemma smul_cell (g : G) (i : ι) (d : Disk n) :
    g • cell a i d = cell a (g • i) d := by
  classical
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq,cell_interior,cell_interior]
    rfl
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    rw [heq,cell_boundary,cell_boundary,smul_base,ha]


-- @@ L323-328 verbatim
lemma continuousConstSMul [ContinuousConstSMul G X] : ContinuousConstSMul G (Space a) where
  continuous_const_smul g := (continuous_iff a _).mpr ⟨
    (continuous_base a).comp (continuous_const_smul g),fun i => by
      have heq : (g • ·) ∘ cell a i = cell a (g • i) := funext (smul_cell a ha g i)
      rw [heq]
      exact (cell a (g • i)).continuous⟩


-- @@ L330-335 verbatim
omit ha in
lemma isOpen_iff (S : Set (Space a)) :
    IsOpen S ↔ IsOpen (base a ⁻¹' S) ∧ ∀ i, IsOpen (cell a i ⁻¹' S) := by
  change @IsOpen _ (TopologicalSpace.coinduced (quotient a) inferInstance) S ↔ _
  rw [isOpen_coinduced,isOpen_sum_iff,isOpen_sigma_iff]
  rfl


-- @@ L337-337 verbatim
end


-- @@ L339-339 verbatim
section

-- @@ L340-340 verbatim
open Set Metric Topology

-- @@ L341-341 verbatim
universe u v w

-- @@ L342-342 verbatim
abbrev Collar (n : ℕ) := {d : Disk n | (1 / 2 : ℝ) < ‖d.1‖}


-- @@ L344-344 verbatim
def collarInclusion (n : ℕ) : Collar n → Disk n := Subtype.val


-- @@ L346-350 verbatim
def radial (n : ℕ) : Collar n → Sphere n := fun d =>
  ⟨‖d.1.1‖⁻¹ • d.1.1,by
    have hn : ‖d.1.1‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) d.2)
    rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
      inv_mul_cancel₀ hn]⟩


-- @@ L352-356 verbatim
lemma continuous_radial (n : ℕ) : Continuous (radial n) := by
  apply Continuous.subtype_mk
  have hn : ∀ d : Collar n, ‖d.1.1‖ ≠ 0 := fun d => ne_of_gt (lt_trans (by norm_num) d.2)
  exact ((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀ hn).smul
    (continuous_subtype_val.comp continuous_subtype_val)


-- @@ L358-359 verbatim
lemma collar_openEmbedding (n : ℕ) : IsOpenEmbedding (collarInclusion n) :=
  (isOpen_lt continuous_const continuous_subtype_val.norm).isOpenEmbedding_subtypeVal


-- @@ L361-365 verbatim
lemma radial_boundary (n : ℕ) (x : Sphere n) (h : (1/2:ℝ) < ‖(boundary n x).1‖) :
    radial n ⟨boundary n x,h⟩ = x := by
  apply Subtype.ext
  have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  simp only [radial,boundary,hx,inv_one,one_smul]


-- @@ L367-367 verbatim
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}

-- @@ L368-368 verbatim
variable (a : ι → C(Sphere n,X))


-- @@ L370-374 verbatim
def thickening (U : Set X) : Set (Space a) := fun z =>
  match z with
  | Sum.inl x => x ∈ U
  | Sum.inr p => ∃ h : (1/2:ℝ) < ‖p.2.1‖,
      a p.1 (radial n ⟨interior n p.2,h⟩) ∈ U


-- @@ L376-377 verbatim
@[simp] lemma base_mem_thickening (U : Set X) (x : X) :
    base a x ∈ thickening a U ↔ x ∈ U := Iff.rfl


-- @@ L379-409 verbatim
lemma cell_preimage_thickening (U : Set X) (i : ι) :
    cell a i ⁻¹' thickening a U =
      collarInclusion n '' ((a i ∘ radial n) ⁻¹' U) := by
  classical
  ext d
  by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d = interior n ⟨d.1,hd⟩ := rfl
    rw [heq]
    simp only [Set.mem_preimage,cell_interior,Set.mem_image]
    constructor
    · rintro ⟨h,hh⟩
      exact ⟨⟨d,h⟩,hh,rfl⟩
    · rintro ⟨y,hy,he⟩
      have heq' : y.1 = d := he
      subst d
      exact ⟨y.2,hy⟩
  · let x : Sphere n := ⟨d.1,by
      have hm := d.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have heq : d = boundary n x := rfl
    have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
    have hhalf : (1/2:ℝ) < ‖(boundary n x).1‖ := by change (1/2:ℝ) < ‖x.1‖; rw [hx]; norm_num
    rw [heq]
    simp only [Set.mem_preimage,cell_boundary,base_mem_thickening,Set.mem_image]
    constructor
    · intro h
      exact ⟨⟨boundary n x,hhalf⟩,by simpa only [Function.comp_apply,radial_boundary] using h,rfl⟩
    · rintro ⟨y,hy,he⟩
      have heq' : y = ⟨boundary n x,hhalf⟩ := Subtype.ext he
      simpa only [heq',Function.comp_apply,radial_boundary] using hy


-- @@ L411-416 verbatim
lemma thickening_isOpen {U : Set X} (hU : IsOpen U) : IsOpen (thickening a U) := by
  rw [isOpen_iff]
  refine ⟨hU,fun i => ?_⟩
  rw [cell_preimage_thickening]
  exact (collar_openEmbedding n).isOpenMap _
    (hU.preimage ((a i).continuous.comp (continuous_radial n)))


-- @@ L418-418 verbatim
variable {G : Type w} [Group G] [MulAction G X] [MulAction G ι]

-- @@ L419-419 verbatim
variable (ha : ∀ (g : G) i x, a (g • i) x = g • a i x)

-- @@ L420-420 verbatim
include ha

-- @@ L421-433 verbatim
lemma thickening_disjoint {U : Set X}
    (hU : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∀ g : G, ((g • ·) '' thickening a U ∩ thickening a U).Nonempty → g = 1 := by
  intro g h
  obtain ⟨_,⟨z,hz,rfl⟩,hgz⟩ := h
  cases z with
  | inl x => exact hU g ⟨g • x,⟨x,hz,rfl⟩,hgz⟩
  | inr p =>
    obtain ⟨hhalf,hz⟩ := hz
    obtain ⟨_,hgz⟩ := hgz
    change a (g • p.1) (radial n ⟨interior n p.2,hhalf⟩) ∈ U at hgz
    rw [ha] at hgz
    exact hU g ⟨g • a p.1 (radial n ⟨interior n p.2,hhalf⟩),⟨_,hz,rfl⟩,hgz⟩


-- @@ L435-453 verbatim
lemma exists_disjoint_nhds [IsCancelSMul G ι]
    (hX : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∀ z : Space a, ∃ U ∈ 𝓝 z, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  intro z
  cases z with
  | inl x =>
    obtain ⟨U,hUx,hU⟩ := hX x
    obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUx
    refine ⟨thickening a V,(thickening_isOpen a hV).mem_nhds hxV,
      thickening_disjoint a ha (fun g hg => hU g ?_)⟩
    exact hg.mono (Set.inter_subset_inter (Set.image_mono hVU) hVU)
  | inr p =>
    refine ⟨Set.range (openCell a p.1),(openCell_openEmbedding a p.1).isOpen_range.mem_nhds
      (Set.mem_range_self p.2),?_⟩
    intro g hg
    obtain ⟨_,⟨_,⟨x,rfl⟩,rfl⟩,⟨y,hy⟩⟩ := hg
    have hi : p.1 = g • p.1 := congrArg Sigma.fst (Sum.inr_injective hy)
    apply IsCancelSMul.right_cancel g 1 p.1
    simpa only [one_smul] using hi.symm


-- @@ L455-455 verbatim
end


-- @@ L457-457 verbatim
section

-- @@ L458-458 verbatim
open Set Metric Topology

-- @@ L459-459 verbatim
universe u v w z

-- @@ L460-460 verbatim
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

-- @@ L461-461 verbatim
variable {ι : Type w} {κ : Type z} {n : ℕ}

-- @@ L462-462 verbatim
variable (a : ι → C(Sphere n,X)) (b : κ → C(Sphere n,Y))


-- @@ L464-467 verbatim
def map (p : C(X,Y)) (σ : ι → κ) (h : ∀ i x, p (a i x) = b (σ i) x) :
    C(Space a,Space b) :=
  lift a ⟨base b ∘ p,(continuous_base b).comp p.continuous⟩
    (fun i => cell b (σ i)) (fun i x => by simp only [cell_boundary,ContinuousMap.coe_mk,Function.comp_apply,h])


-- @@ L469-471 verbatim
@[simp] lemma map_base (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (x : X) :
    map a b p σ h (base a x) = base b (p x) := rfl


-- @@ L473-475 verbatim
@[simp] lemma map_cell (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (i : ι) (d : Disk n) :
    map a b p σ h (cell a i d) = cell b (σ i) d := lift_cell a _ _ _ i d


-- @@ L477-481 verbatim
@[simp] lemma map_openCell (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x) (i : ι) (d : OpenDisk n) :
    map a b p σ h (openCell a i d) = openCell b (σ i) d := by
  change map a b p σ h (Sum.inr ⟨i,d⟩) = Sum.inr ⟨σ i,d⟩
  rw [← cell_interior a i d,map_cell,cell_interior]


-- @@ L483-494 verbatim
lemma map_surjective (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x)
    (hp : Function.Surjective p) (hσ : Function.Surjective σ) :
    Function.Surjective (map a b p σ h) := by
  intro z
  cases z with
  | inl y =>
    obtain ⟨x,rfl⟩ := hp y
    exact ⟨base a x,rfl⟩
  | inr q =>
    obtain ⟨i,hi⟩ := hσ q.1
    exact ⟨openCell a i q.2,by rw [map_openCell,hi]; rfl⟩


-- @@ L496-514 verbatim
lemma map_isQuotientMap (p : C(X,Y)) (σ : ι → κ)
    (h : ∀ i x, p (a i x) = b (σ i) x)
    (hp : IsQuotientMap p) (hσ : Function.Surjective σ) :
    IsQuotientMap (map a b p σ h) := by
  refine ⟨?_,map_surjective a b p σ h hp.surjective hσ⟩
  rw [isCoinducing_iff]
  intro U
  constructor
  · intro hU
    rw [isOpen_iff] at hU ⊢
    constructor
    · apply hp.isOpen_preimage.mp
      exact hU.1
    · intro j
      obtain ⟨i,rfl⟩ := hσ j
      convert hU.2 i using 1
      ext d
      simp only [Set.mem_preimage,map_cell]
  · exact fun hU => hU.preimage (map a b p σ h).continuous


-- @@ L516-516 verbatim
end


-- @@ L518-518 verbatim
open Set Metric Topology

-- @@ L519-519 verbatim
universe u v w z


-- @@ L521-521 verbatim
def FreeIndex (G : Type u) (ι : Type v) := G × ι


-- @@ L523-526 verbatim
instance {G : Type u} [Group G] {ι : Type v} : MulAction G (FreeIndex G ι) where
  smul g p := (g * p.1,p.2)
  one_smul p := by change ((1:G)*p.1,p.2)=p; simp only [one_mul]; rfl
  mul_smul g h p := by change ((g*h)*p.1,p.2)=(g*(h*p.1),p.2); rw [mul_assoc]


-- @@ L528-529 verbatim
instance {G : Type u} [Group G] {ι : Type v} : IsCancelSMul G (FreeIndex G ι) where
  right_cancel' _ _ _ he := mul_right_cancel (congrArg (fun p : FreeIndex G ι => p.1) he)


-- @@ L531-531 verbatim
variable {G : Type u} [Group G]

-- @@ L532-532 verbatim
variable {E : Type v} [TopologicalSpace E] [MulAction G E] [ContinuousConstSMul G E]

-- @@ L533-533 verbatim
variable {X : Type w} [TopologicalSpace X] {ι : Type z} {n : ℕ}

-- @@ L534-534 verbatim
variable (a : ι → C(Sphere n,E))


-- @@ L536-537 verbatim
def equivariantFamily : FreeIndex G ι → C(Sphere n,E) :=
  fun i => ⟨fun x => i.1 • a i.2 x,(continuous_const_smul i.1).comp (a i.2).continuous⟩


-- @@ L539-540 verbatim
lemma equivariantFamily_smul (g : G) (i : FreeIndex G ι) (x : Sphere n) :
    equivariantFamily (G := G) a (g • i) x = g • equivariantFamily a i x := mul_smul g i.1 _


-- @@ L542-544 verbatim
instance equivariantAttachmentContinuousAction :
    ContinuousConstSMul G (Space (equivariantFamily (G := G) a)) :=
  continuousConstSMul _ (equivariantFamily_smul a)


-- @@ L546-546 verbatim
variable (p : C(E,X)) (hp : IsQuotientCoveringMap p G)

-- @@ L547-547 verbatim
variable (b : ι → C(Sphere n,X)) (h : ∀ i x, p (a i x) = b i x)


-- @@ L549-552 verbatim
include hp h in
lemma equivariantFamily_over (i : FreeIndex G ι) (x : Sphere n) :
    p (equivariantFamily (G := G) a i x) = b i.2 x :=
  (hp.map_smul i.1).trans (h i.2 x)


-- @@ L554-555 verbatim
def coverMap : C(Space (equivariantFamily (G := G) a),Space b) :=
  map _ b p Prod.snd (equivariantFamily_over a p hp b h)


-- @@ L557-558 verbatim
lemma coverMap_isQuotient : IsQuotientMap (coverMap a p hp b h) :=
  map_isQuotientMap _ b p Prod.snd _ hp.toIsQuotientMap (fun i => ⟨(1,i),rfl⟩)


-- @@ L560-611 verbatim
lemma coverMap_fibers {e₁ e₂ : Space (equivariantFamily (G := G) a)} :
    coverMap a p hp b h e₁ = coverMap a p hp b h e₂ ↔ e₁ ∈ MulAction.orbit G e₂ := by
  classical
  cases e₁ with
  | inl x =>
    cases e₂ with
    | inl y =>
      change Sum.inl (p x) = Sum.inl (p y) ↔ _
      rw [Sum.inl.injEq,hp.apply_eq_iff_mem_orbit]
      constructor
      · rintro ⟨g,hg⟩; exact ⟨g,congrArg Sum.inl hg⟩
      · rintro ⟨g,hg⟩; exact ⟨g,Sum.inl_injective hg⟩
    | inr q =>
      constructor
      · intro hh
        change base b (p x) =
          map _ b p (fun index : FreeIndex G ι => index.2) _ (openCell _ q.1 q.2) at hh
        rw [map_openCell] at hh
        cases hh
      · rintro ⟨g,hg⟩; cases hg
  | inr q =>
    cases e₂ with
    | inl y =>
      constructor
      · intro hh
        change map _ b p (fun index : FreeIndex G ι => index.2) _
          (openCell _ q.1 q.2) = base b (p y) at hh
        rw [map_openCell] at hh
        cases hh
      · rintro ⟨g,hg⟩; cases hg
    | inr r =>
      change map _ b p (fun index : FreeIndex G ι => index.2) _ (openCell _ q.1 q.2) =
        map _ b p (fun index : FreeIndex G ι => index.2) _ (openCell _ r.1 r.2) ↔ _
      rw [map_openCell,map_openCell]
      constructor
      · intro hh
        have hi : q.1.2 = r.1.2 := congrArg Sigma.fst (Sum.inr_injective hh)
        have hd : q.2 = r.2 := congrArg (fun p : Σ _ : ι, OpenDisk n => p.2) (Sum.inr_injective hh)
        refine ⟨q.1.1 * r.1.1⁻¹,?_⟩
        change Sum.inr ⟨((q.1.1 * r.1.1⁻¹) * r.1.1,r.1.2),r.2⟩ = Sum.inr q
        simp only [inv_mul_cancel_right,← hi,← hd]
        rfl
      · rintro ⟨g,hg⟩
        change (Sum.inr ⟨g • r.1,r.2⟩ : Space (equivariantFamily (G := G) a)) = Sum.inr q at hg
        have hi : (g • r.1) = q.1 := congrArg Sigma.fst (Sum.inr_injective hg)
        have htuple : (⟨g • r.1,r.2⟩ : Σ _ : FreeIndex G ι, OpenDisk n) = q := Sum.inr_injective hg
        have hd' := congrArg (fun p : Σ _ : FreeIndex G ι, OpenDisk n => p.2) htuple
        have hd : r.2 = q.2 := hd'
        have his' := congrArg (fun p : FreeIndex G ι => p.2) hi
        have his : r.1.2 = q.1.2 := his'
        change (Sum.inr ⟨q.1.2,q.2⟩ : Space b) = Sum.inr ⟨r.1.2,r.2⟩
        rw [his,hd]


-- @@ L613-617 verbatim
lemma coverMap_isQuotientCovering : IsQuotientCoveringMap (coverMap a p hp b h) G where
  __ := coverMap_isQuotient a p hp b h
  __ := equivariantAttachmentContinuousAction a
  apply_eq_iff_mem_orbit := coverMap_fibers a p hp b h
  disjoint := exists_disjoint_nhds _ (equivariantFamily_smul a) hp.disjoint


-- @@ L619-620 verbatim
lemma coverMap_isCovering : IsCoveringMap (coverMap a p hp b h) :=
  (coverMap_isQuotientCovering a p hp b h).isCoveringMap


-- @@ L622-622 verbatim
end UniversalFInfinity.Attachment


-- @@ L624-624 verbatim
end


-- @@ L626-626 verbatim
end OAI
