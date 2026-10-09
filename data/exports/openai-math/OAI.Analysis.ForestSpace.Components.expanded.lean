import OAI.Analysis.ForestSpace.Reflexivity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open scoped BigOperators

-- @@ L6-6 verbatim
open Finset


-- @@ L8-8 verbatim
namespace ForestSpace


-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L13-13 verbatim
section ComponentDecomposition


-- @@ L15-18 verbatim
noncomputable def componentRaw (h : ℕ) : TestVector Vertex →ₗ[ℝ] TestVector (Component h) where
  toFun u := u.toFinsupp.subtypeDomain (fun v => v.height = h)
  map_add' u v := by ext w; rfl
  map_smul' a u := by ext w; rfl


-- @@ L20-21 verbatim
@[simp] theorem componentRaw_apply (h : ℕ) (u : TestVector Vertex) (v : Component h) :
    componentRaw h u v = u v := rfl


-- @@ L23-24 verbatim
noncomputable def liftComponent (h : ℕ) (u : TestVector (Component h)) : TestVector Vertex :=
  Finsupp.extendDomain u.toFinsupp


-- @@ L26-28 verbatim
@[simp] theorem liftComponent_apply (h : ℕ) (u : TestVector (Component h)) (v : Vertex) :
    liftComponent h u v = if hv : v.height = h then u ⟨v,hv⟩ else 0 :=
  Finsupp.extendDomain_apply _ _


-- @@ L30-33 verbatim
@[simp] theorem componentRaw_lift_same (h : ℕ) (u : TestVector (Component h)) :
    componentRaw h (liftComponent h u) = u := by
  ext v
  simp [v.property]

 
-- @@ L35-39 verbatim
theorem componentRaw_lift_other (h j : ℕ) (hj : j ≠ h) (u : TestVector (Component h)) :
    componentRaw j (liftComponent h u) = 0 := by
  ext v
  have hv : v.val.height ≠ h := by simpa only [v.property] using hj
  simp [hv]


-- @@ L41-42 verbatim
noncomputable def componentSupport (u : TestVector Vertex) : Finset ℕ :=
  u.toFinsupp.support.image Vertex.height

 
-- @@ L44-50 verbatim
theorem componentRaw_zero (u : TestVector Vertex) {h : ℕ} (hh : h ∉ componentSupport u) :
    componentRaw h u = 0 := by
  ext v
  change u v = 0
  apply Finsupp.notMem_support_iff.mp
  intro hv
  exact hh (Finset.mem_image.mpr ⟨v,hv,v.property⟩)


-- @@ L52-66 verbatim
noncomputable def rawDecompositionLinear : TestVector Vertex →ₗ[ℝ] lp (fun h => J (Component h)) 2 where
  toFun u := ⟨(fun h => (componentRaw h u : J (Component h))),memℓp_gen (by
    apply summable_of_ne_finset_zero (s := componentSupport u)
    intro h hh
    simp [componentRaw_zero u hh])⟩
  map_add' u v := by
    ext h
    change ((componentRaw h (u+v) : TestVector (Component h)) : J (Component h)) = _
    rw [map_add,UniformSpace.Completion.coe_add]
    rfl
  map_smul' a u := by
    ext h
    change ((componentRaw h (a • u) : TestVector (Component h)) : J (Component h)) = _
    rw [map_smul,UniformSpace.Completion.coe_smul]
    rfl


-- @@ L68-69 verbatim
@[simp] theorem rawDecomposition_apply (u : TestVector Vertex) (h : ℕ) :
    rawDecompositionLinear u h = (componentRaw h u : J (Component h)) := rfl

 
-- @@ L71-78 verbatim
theorem rawDecomposition_norm_sq (u : TestVector Vertex) :
    ‖rawDecompositionLinear u‖^2 = ∑ h ∈ componentSupport u, ‖componentRaw h u‖^2 := by
  have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (rawDecompositionLinear u)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,rawDecomposition_apply,UniformSpace.Completion.norm_coe] at he
  rw [he]
  apply tsum_eq_sum
  intro h hh
  simp [componentRaw_zero u hh]

 
-- @@ L80-86 verbatim
theorem segment_component_subtype (S : Finset Vertex) (hS : IsSegment S) (h : ℕ) :
    IsSegment (S.subtype (fun v => v.height = h)) := by
  constructor
  · intro a ha b hb
    exact hS.1 a (Finset.mem_subtype.mp ha) b (Finset.mem_subtype.mp hb)
  · intro a ha b hb c hac hcb
    exact Finset.mem_subtype.mpr (hS.2 a (Finset.mem_subtype.mp ha) b (Finset.mem_subtype.mp hb) c hac hcb)

 
-- @@ L88-99 verbatim
theorem segment_component_image (h : ℕ) (S : Finset (Component h)) (hS : IsSegment S) :
    IsSegment (S.image Subtype.val) := by
  constructor
  · intro a ha b hb
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    exact hS.1 a' ha' b' hb'
  · intro a ha b hb c hac hcb
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    have hc : c.height = h := hac.1.symm.trans a'.property
    exact Finset.mem_image.mpr ⟨⟨c,hc⟩,hS.2 a' ha' b' hb' ⟨c,hc⟩ hac hcb,rfl⟩

 
-- @@ L101-103 verbatim
theorem segSum_component_image (h : ℕ) (u : TestVector Vertex) (S : Finset (Component h)) :
    segSum u (S.image Subtype.val) = segSum (componentRaw h u) S := by
  exact Finset.sum_image (fun a ha b hb hab => Subtype.val_injective hab)

 
-- @@ L105-108 verbatim
theorem segment_single_height {S : Finset Vertex} (hS : IsSegment S) {v : Vertex} (hv : v ∈ S) :
    ∀ w ∈ S, w.height = v.height := by
  intro w hw
  exact (hS.1 w hw v hv).elim (fun h => h.1) (fun h => h.1.symm)

 
-- @@ L110-124 verbatim
theorem segSum_component_subtype (u : TestVector Vertex) (S : Finset Vertex)
    (k : ℕ) (hS : ∀ v ∈ S, v.height = k) (h : ℕ) :
    segSum (componentRaw h u) (S.subtype (fun v => v.height = h)) =
      if h = k then segSum u S else 0 := by
  unfold segSum
  simp only [componentRaw_apply,Finset.sum_subtype_eq_sum_filter]
  by_cases hh : h = k
  · subst h
    rw [ite_eq_left rfl,Finset.filter_eq_self.mpr hS]
  · rw [ite_eq_right hh]
    have hf : S.filter (fun v => v.height = h) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv he
      exact hh (he.symm.trans (hS v hv))
    rw [hf,Finset.sum_empty]

 
-- @@ L126-142 verbatim
theorem segSum_sq_components (u : TestVector Vertex) (S : Finset Vertex) (hS : IsSegment S) :
    segSum u S ^ 2 = ∑ h ∈ componentSupport u,
      segSum (componentRaw h u) (S.subtype (fun v => v.height = h))^2 := by
  by_cases hne : S.Nonempty
  · obtain ⟨v,hv⟩ := hne
    simp_rw [segSum_component_subtype u S v.height (segment_single_height hS hv)]
    by_cases hh : v.height ∈ componentSupport u
    · simp [hh]
    · have hz : segSum u S = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        apply Finsupp.notMem_support_iff.mp
        intro hw'
        exact hh (Finset.mem_image.mpr ⟨w,hw',segment_single_height hS hv w hw⟩)
      simp [hz]
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he,segSum]

 
-- @@ L144-161 verbatim
theorem norm_le_rawDecomposition (u : TestVector Vertex) : ‖u‖ ≤ ‖rawDecompositionLinear u‖ := by
  classical
  apply (TestVector.norm_le_iff_testBound u (norm_nonneg _)).mpr
  intro I inst S hS hd
  rw [rawDecomposition_norm_sq]
  simp_rw [segSum_sq_components u _ (hS _)]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h hh
  change (∑ i, segSum (componentRaw h u) ((S i).subtype (fun v => v.height = h)) ^ 2) ≤
    rho (componentRaw h u) ^ 2
  apply testBound_rho_sq (finsupp_has_testBound (componentRaw h u).toFinsupp)
  · intro i
    exact segment_component_subtype _ (hS i) h
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact Finset.disjoint_left.mp (hd hij) (Finset.mem_subtype.mp hvi) (Finset.mem_subtype.mp hvj)

 
-- @@ L163-174 verbatim
theorem exists_half_test {W : Type} [PartialOrder W] (u : TestVector W) :
    ∃ (I : Type) (_ : Fintype I) (S : I → Finset W), (∀ i, IsSegment (S i)) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧ ‖u‖^2 ≤ 2*∑ i, segSum u (S i)^2 := by
  by_cases hz : ‖u‖ = 0
  · exact ⟨PEmpty,inferInstance,PEmpty.elim,by simp,by simp [Pairwise],by simp [hz]⟩
  · have hp : 0 < ‖u‖^2 := sq_pos_of_ne_zero hz
    have hs : ‖u‖^2/2 < squareSup u := by
      rw [← rho_sq (finsupp_has_testBound u.toFinsupp)]
      exact half_lt_self hp
    obtain ⟨r,hr,hl⟩ := (lt_csSup_iff (testBound_l1size u.toFinsupp).bddAbove ⟨0,zero_mem_testValues u⟩).mp hs
    obtain ⟨I,inst,S,hS,hd,rfl⟩ := hr
    exact ⟨I,inst,S,hS,hd,by linarith⟩

 
-- @@ L176-212 verbatim
theorem rawDecomposition_norm_le (u : TestVector Vertex) : ‖rawDecompositionLinear u‖ ≤ 2*‖u‖ := by
  let K := componentSupport u
  choose I inst S hS hd hb using (fun h : K => exists_half_test (componentRaw h u))
  let : ∀ h : K, Fintype (I h) := inst
  let A : (Σ h : K, I h) → Finset Vertex := fun i => (S i.1 i.2).image Subtype.val
  have hA : ∀ i, IsSegment (A i) := fun i => segment_component_image i.1 _ (hS i.1 i.2)
  have hdis : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    by_cases hh : i.1 = j.1
    · rcases i with ⟨h,i⟩
      rcases j with ⟨h',j⟩
      dsimp at hh
      subst h'
      apply (Finset.disjoint_image Subtype.val_injective).mpr
      exact hd h (fun he => hij (by cases he; rfl))
    · apply Finset.disjoint_left.mpr
      intro v hvi hvj
      obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hvi
      obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hvj
      exact hh (Subtype.ext (a.property.symm.trans ((congrArg Vertex.height (hea.trans heb.symm)).trans b.property)))
  have ht := (testBound_rho_sq (finsupp_has_testBound u.toFinsupp)) (Σ h : K, I h) inferInstance A hA hdis
  have he : (∑ i : (Σ h : K, I h), segSum u (A i)^2) =
      ∑ h : K, ∑ i : I h, segSum (componentRaw h u) (S h i)^2 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro i hi
    rw [show A ⟨h,i⟩ = (S h i).image Subtype.val from rfl,segSum_component_image]
  rw [he] at ht
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun h hh => hb h)
  rw [← Finset.mul_sum] at hh
  have hsq : ‖rawDecompositionLinear u‖^2 ≤ 2*‖u‖^2 := by
    rw [rawDecomposition_norm_sq,← Finset.sum_coe_sort]
    change (∑ h : K, ‖componentRaw h u‖^2) ≤ 2*‖u‖^2
    exact hh.trans (mul_le_mul_of_nonneg_left ht (by norm_num))
  nlinarith [norm_nonneg u,norm_nonneg (rawDecompositionLinear u)]


-- @@ L214-215 verbatim
noncomputable def rawDecomposition : TestVector Vertex →L[ℝ] lp (fun h => J (Component h)) 2 :=
  rawDecompositionLinear.mkContinuous 2 rawDecomposition_norm_le

 
-- @@ L217-223 verbatim
theorem rawDecomposition_lift (h : ℕ) (u : TestVector (Component h)) :
    rawDecompositionLinear (liftComponent h u) = lp.single 2 h (u : J (Component h)) := by
  ext j
  by_cases hj : j = h
  · subst j
    simp
  · simp [componentRaw_lift_other h j hj,Pi.single_eq_of_ne hj]

 
-- @@ L225-239 verbatim
theorem rawDecomposition_dense : DenseRange rawDecomposition := by
  let : DecidableEq ℕ := Classical.decEq ℕ
  apply denseRange_lp_of_singles (fun h => J (Component h)) rawDecompositionLinear
  intro h x
  refine UniformSpace.Completion.induction_on (p := fun a => lp.single 2 h a ∈ rawDecompositionLinear.range.topologicalClosure) x ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure rawDecompositionLinear.range).preimage
      (lp.isometry_single (E := fun h => J (Component h)) (p := 2) h).continuous
  · intro u
    apply Submodule.le_topologicalClosure
    refine ⟨liftComponent h u,?_⟩
    ext j
    by_cases hj : j = h
    · subst j
      simp
    · simp [componentRaw_lift_other h j hj,Pi.single_eq_of_ne hj]


-- @@ L241-250 verbatim
/-- The specified disjoint-component segment completion is canonically
reflexive. Only bounded isomorphisms are needed here; its norm is unchanged. -/
 theorem reflexive_forest_J : Reflexive (J Vertex) := by
  obtain ⟨e⟩ := completion_equiv_of_bounds rawDecomposition 1
    (fun u => by
      change ‖u‖ ≤ 1*‖rawDecompositionLinear u‖
      rw [one_mul]
      exact norm_le_rawDecomposition u)
    rawDecomposition_dense
  exact reflexive_of_equiv e (reflexive_l2 (fun h => J (Component h)) reflexive_component)


-- @@ L252-252 verbatim
end ComponentDecomposition


-- @@ L254-254 verbatim
end


-- @@ L256-256 verbatim
end ForestSpace


-- @@ L258-258 verbatim
end OAI
