import OAI.Analysis.TreePotential.SegmentEndpoints


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set

-- @@ L7-7 verbatim
open scoped ENNReal

-- @@ L8-8 verbatim
open Set Filter Topology

-- @@ L9-9 verbatim
open scoped Classical




-- @@ L13-13 verbatim
namespace BoundedTreePotentials

-- @@ L14-14 verbatim
section FiniteHilbert

-- @@ L15-15 verbatim
variable {I : Type*}


-- @@ L17-17 verbatim
abbrev CoordinateHilbert (I : Type*) := lp (fun _ : I => ℝ) 2


-- @@ L19-22 verbatim
def finiteHilbert : (I →₀ ℝ) →ₗ[ℝ] CoordinateHilbert I where
  toFun g := ⟨(fun i => g i),(memℓp_zero g.hasFiniteSupport).of_exponent_ge (by norm_num)⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' a g := by apply Subtype.ext; rfl


-- @@ L24-24 verbatim
lemma finiteHilbert_apply (g : I →₀ ℝ) (i : I) : finiteHilbert g i=g i := rfl


-- @@ L26-32 verbatim
lemma finiteHilbert_norm_sq (g : I →₀ ℝ) : ‖finiteHilbert g‖^2=∑ i ∈ g.support, (g i)^2 := by
  have hs : HasSum (fun i => (g i)^2) (∑ i ∈ g.support, (g i)^2) :=
    hasSum_sum_of_ne_finset_zero (fun i hi => by rw [Finsupp.notMem_support_iff.mp hi]; norm_num)
  have hh : HasSum (fun i => (g i)^2) (‖finiteHilbert g‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,finiteHilbert_apply]
      using lp.hasSum_norm (p:=2) (by norm_num) (finiteHilbert g)
  exact hh.unique hs


-- @@ L34-37 verbatim
lemma finiteHilbert_single (i : I) (a : ℝ) : finiteHilbert (Finsupp.single i a)=lp.single 2 i a := by
  apply Subtype.ext
  funext j
  simp only [finiteHilbert_apply,lp.single_apply,Finsupp.single_apply,Pi.single_apply,eq_comm]


-- @@ L39-46 verbatim
lemma finiteHilbert_dense : DenseRange (finiteHilbert (I := I)) := by
  intro x
  have hlim := lp.hasSum_single (p:=2) (by norm_num) x
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [] with S
  apply subset_closure
  refine ⟨∑ i ∈ S, Finsupp.single i (x i),?_⟩
  simp only [map_sum,finiteHilbert_single]


-- @@ L48-54 verbatim
/-- A general completion comparison, using both actual inequalities on c00.
No finite dimensionality of the index set is asserted. -/
def finiteHilbertMap (K : TestFamily I) (C : ℝ)
    (hlower : ∀ g, ‖finiteHilbert g‖ ≤ C*testNorm K g) :
    TestVector K →L[ℝ] CoordinateHilbert I :=
  (finiteHilbert.comp (testVectorEquiv K).toLinearMap).mkContinuous C
    (fun g => hlower ((testVectorEquiv K) g))


-- @@ L56-59 verbatim
def completedHilbertMap (K : TestFamily I) (C : ℝ)
    (hlower : ∀ g, ‖finiteHilbert g‖ ≤ C*testNorm K g) :
    TestCompletion K →L[ℝ] CoordinateHilbert I :=
  (finiteHilbertMap K C hlower).extend UniformSpace.Completion.toComplL


-- @@ L61-65 verbatim
lemma completedHilbertMap_coe (K : TestFamily I) (C : ℝ)
    (hlower : ∀ g, ‖finiteHilbert g‖ ≤ C*testNorm K g) (g : TestVector K) :
    completedHilbertMap K C hlower g=finiteHilbert ((testVectorEquiv K) g) := by
  exact (finiteHilbertMap K C hlower).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformEmbedding_coe _).isUniformInducing g


-- @@ L67-75 verbatim
lemma completedHilbertMap_lower (K : TestFamily I) (C : ℝ)
    (hlower : ∀ g, ‖finiteHilbert g‖ ≤ C*testNorm K g)
    (hupper : ∀ g, testNorm K g ≤ C*‖finiteHilbert g‖) (x : TestCompletion K) :
    ‖x‖ ≤ C*‖completedHilbertMap K C hlower x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le continuous_norm (continuous_const.mul (completedHilbertMap K C hlower).continuous.norm)) ?_
  intro g
  rw [completedHilbertMap_coe,UniformSpace.Completion.norm_coe]
  exact hupper ((testVectorEquiv K) g)


-- @@ L77-101 verbatim
def completionHilbertEquiv (K : TestFamily I) (C : ℝ) (hC : 0 ≤ C)
    (hlower : ∀ g, ‖finiteHilbert g‖ ≤ C*testNorm K g)
    (hupper : ∀ g, testNorm K g ≤ C*‖finiteHilbert g‖) :
    TestCompletion K ≃L[ℝ] CoordinateHilbert I := by
  let L := completedHilbertMap K C hlower
  have hb : AntilipschitzWith ⟨C,hC⟩ L := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    rw [dist_eq_norm,dist_eq_norm]
    change ‖x-y‖ ≤ C*‖L x-L y‖
    rw [← map_sub]
    exact completedHilbertMap_lower K C hlower hupper (x-y)
  have hc : IsClosed (Set.range L) := hb.isClosed_range L.uniformContinuous
  have hd : Dense (Set.range L) := by
    apply finiteHilbert_dense.mono
    rintro y ⟨g,rfl⟩
    refine ⟨((testVectorEquiv K).symm g : TestVector K),?_⟩
    exact completedHilbertMap_coe K C hlower ((testVectorEquiv K).symm g)
  have hs : Function.Surjective L := by
    intro y
    have ht : Set.range L=Set.univ := hc.closure_eq.symm.trans hd.closure_eq
    rw [← Set.mem_range,ht]
    trivial
  exact ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hb.injective)
    (LinearMap.range_eq_top.mpr hs)


-- @@ L103-103 verbatim
end FiniteHilbert

-- @@ L104-104 verbatim
end BoundedTreePotentials


-- @@ L106-106 verbatim
namespace BoundedTreePotentials.Segments

-- @@ L107-107 verbatim
abbrev BlockNode (n : ℕ) := {s : List ℕ // s.length ≤ n+1}

-- @@ L108-108 verbatim
def componentEmbedding (n : ℕ) : BlockNode n ↪ Node := ⟨Sigma.mk n,fun _ _ h => by cases h; rfl⟩

-- @@ L109-109 verbatim
abbrev blockTests (n : ℕ) := restrictedTestFamily atomTests (componentEmbedding n)

-- @@ L110-110 verbatim
abbrev PredualBlock (n : ℕ) := TestCompletion (blockTests n)


-- @@ L112-114 verbatim
lemma Segment.card_nodes (S : Segment) : S.nodes.card ≤ S.finish.2.val.length+1 := by
  apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
  exact (Finset.card_image_le).trans_eq (by simp)


-- @@ L116-129 verbatim
lemma Atom.profile_sq (A : Atom) (v : Node) :
    (A.profile v)^2=∑ S ∈ A.family, if v ∈ S.nodes then (A.coeff S)^2 else 0 := by
  by_cases hh : ∃ S ∈ A.family, v ∈ S.nodes
  · obtain ⟨S,hS,hv⟩ := hh
    rw [A.profile_at hS hv,Finset.sum_eq_single_of_mem S hS,ite_eq_left hv]
    intro T hT hne
    have hn : v ∉ T.nodes := fun hvT => Finset.disjoint_left.mp
      (incomparable_disjoint A.incomparable hT hS hne) hvT hv
    exact ite_eq_right hn
  · have hn : ∀ S ∈ A.family, v ∉ S.nodes := by simpa only [not_exists,not_and] using hh
    rw [A.profile_missing hn]
    simp only [zero_pow (by norm_num : (2:ℕ)≠0)]
    symm
    exact Finset.sum_eq_zero (fun S hS => ite_eq_right (hn S hS))


-- @@ L131-154 verbatim
lemma Atom.profile_energy (A : Atom) {n : ℕ} (U : Finset Node)
    (hU : ∀ v ∈ U, v.1=n) : (∑ v ∈ U, (A.profile v)^2) ≤ n+2 := by
  simp_rw [A.profile_sq]
  rw [Finset.sum_comm]
  have hcard (S : Segment) : (U.filter (fun v => v ∈ S.nodes)).card ≤ n+2 := by
    by_cases he : (U.filter (fun v => v ∈ S.nodes)).Nonempty
    · obtain ⟨v,hv⟩ := he
      obtain ⟨hvU,hvS⟩ := Finset.mem_filter.mp hv
      have hc : S.finish.1=n := ((S.mem_nodes v).mp hvS).2.1.symm.trans (hU v hvU)
      apply (Finset.card_le_card (show U.filter (fun v => v ∈ S.nodes) ⊆ S.nodes from
        fun v hv => (Finset.mem_filter.mp hv).2)).trans
      apply S.card_nodes.trans
      have hh := S.finish.2.property
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
      omega
  have hbound : (∑ S ∈ A.family, ∑ v ∈ U, if v ∈ S.nodes then (A.coeff S)^2 else 0) ≤
      (n+2 : ℝ)*(∑ S ∈ A.family, (A.coeff S)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S hS
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard S) (sq_nonneg _)
  exact hbound.trans (mul_le_of_le_one_right (by positivity) A.budget)


-- @@ L156-175 verbatim
lemma predual_hilbert_upper {n : ℕ} (g : Node →₀ ℝ)
    (hg : ∀ v ∈ g.support, v.1=n) :
    testNorm atomTests g ≤ Real.sqrt (n+2)*‖finiteHilbert g‖ := by
  apply ciSup_le
  rintro ⟨f,A,rfl⟩
  rw [finitePairing_apply]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq g.support (fun v => g v) A.profile
  have hb := A.profile_energy g.support hg
  have hgs := finiteHilbert_norm_sq g
  have ht : (Real.sqrt (n+2)*‖finiteHilbert g‖)^2=(n+2)*‖finiteHilbert g‖^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hbp : (∑ v ∈ g.support, (A.profile v)^2)*(∑ v ∈ g.support, (g v)^2) ≤
      (n+2)*‖finiteHilbert g‖^2 := by
    rw [← hgs]
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hh : (∑ v ∈ g.support, g v*A.profile v)^2 ≤ (Real.sqrt (n+2)*‖finiteHilbert g‖)^2 := by
    rw [ht]
    nlinarith
  nlinarith [abs_nonneg (∑ v ∈ g.support,g v*A.profile v),sq_abs (∑ v ∈ g.support,g v*A.profile v),
    mul_nonneg (Real.sqrt_nonneg (n+2)) (norm_nonneg (finiteHilbert g))]


-- @@ L177-187 verbatim
lemma level_incomparable (U : Finset Node) (d : ℕ) (hd : ∀ v ∈ U, v.2.val.length=d) :
    Incomparable (U.image Segment.singleton) := by
  intro S hS T hT hne
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hT
  have hn : s≠t := fun hh => hne (congrArg Segment.singleton hh)
  have he {s t : Node} (h : Prefix s t) (hlen : s.2.val.length=t.2.val.length) : s=t := by
    apply Prefix.antisymm h
    exact ⟨h.1.symm,(h.2.eq_of_length (by omega)) ▸ List.prefix_refl _⟩
  exact ⟨fun h => hn (he h ((hd s hs).trans (hd t ht).symm)),
    fun h => hn (he h ((hd t ht).trans (hd s hs).symm)).symm⟩


-- @@ L189-202 verbatim
lemma level_energy (g : Node →₀ ℝ) (d : ℕ) :
    (∑ v ∈ g.support.filter (fun v => v.2.val.length=d), (g v)^2) ≤ (testNorm atomTests g)^2 := by
  let U := g.support.filter (fun v => v.2.val.length=d)
  have hi : Incomparable (U.image Segment.singleton) :=
    level_incomparable U d (fun v hv => (Finset.mem_filter.mp hv).2)
  have hh := predual_test_bound g (U.image Segment.singleton) hi
  have he : (∑ S ∈ U.image Segment.singleton, (S.eval g)^2) = ∑ v ∈ U, (g v)^2 := by
    rw [Finset.sum_image]
    · simp only [Segment.eval_singleton]
    · intro s hs t ht hh
      exact congrArg Segment.start hh
  rw [he] at hh
  have hs := Real.sq_sqrt (show 0 ≤ ∑ v ∈ U, (g v)^2 from Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  nlinarith [Real.sqrt_nonneg (∑ v ∈ U,(g v)^2),testNorm_nonneg atomTests g]


-- @@ L204-226 verbatim
lemma predual_hilbert_lower {n : ℕ} (g : Node →₀ ℝ)
    (hg : ∀ v ∈ g.support, v.1=n) :
    ‖finiteHilbert g‖ ≤ Real.sqrt (n+2)*testNorm atomTests g := by
  have he : (∑ d ∈ Finset.range (n+2), ∑ v ∈ g.support.filter (fun v => v.2.val.length=d), (g v)^2)=
      ∑ v ∈ g.support, (g v)^2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    have hd : v.2.val.length ∈ Finset.range (n+2) := by
      have hl := v.2.property
      have hc := hg v hv
      simp only [Finset.mem_range]
      omega
    simp [hd]
  have hb := Finset.sum_le_sum (s:=Finset.range (n+2)) (fun d _ => level_energy g d)
  rw [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,← finiteHilbert_norm_sq] at hb
  have hs : (Real.sqrt (n+2))^2=n+2 := Real.sq_sqrt (by positivity)
  have ht : (Real.sqrt (n+2)*testNorm atomTests g)^2=(n+2)*(testNorm atomTests g)^2 := by
    rw [mul_pow,hs]
  have hp : 0 ≤ Real.sqrt (n+2)*testNorm atomTests g := mul_nonneg (Real.sqrt_nonneg _) (testNorm_nonneg _ _)
  push_cast at hb
  nlinarith [norm_nonneg (finiteHilbert g)]


-- @@ L228-228 verbatim
end BoundedTreePotentials.Segments


-- @@ L230-230 verbatim
namespace BoundedTreePotentials

-- @@ L231-235 verbatim
lemma finiteHilbert_emb_norm {I J : Type*} (ι : J ↪ I) (g : J →₀ ℝ) :
    ‖finiteHilbert (Finsupp.embDomain ι g)‖=‖finiteHilbert g‖ := by
  have he : ‖finiteHilbert (Finsupp.embDomain ι g)‖^2=‖finiteHilbert g‖^2 := by
    simp only [finiteHilbert_norm_sq,Finsupp.support_embDomain,Finset.sum_map,Finsupp.embDomain_apply_self]
  nlinarith [norm_nonneg (finiteHilbert (Finsupp.embDomain ι g)),norm_nonneg (finiteHilbert g)]

-- @@ L236-236 verbatim
end BoundedTreePotentials


-- @@ L238-238 verbatim
namespace BoundedTreePotentials.Segments

-- @@ L239-244 verbatim
lemma component_support {n : ℕ} (g : BlockNode n →₀ ℝ) :
    ∀ v ∈ (Finsupp.embDomain (componentEmbedding n) g).support, v.1=n := by
  intro v hv
  rw [Finsupp.support_embDomain] at hv
  obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hv
  rfl


-- @@ L246-251 verbatim
lemma block_hilbert_comparisons (n : ℕ) (g : BlockNode n →₀ ℝ) :
    ‖finiteHilbert g‖ ≤ Real.sqrt (n+2)*testNorm (blockTests n) g ∧
    testNorm (blockTests n) g ≤ Real.sqrt (n+2)*‖finiteHilbert g‖ := by
  have h1 := predual_hilbert_lower (Finsupp.embDomain (componentEmbedding n) g) (component_support g)
  have h2 := predual_hilbert_upper (Finsupp.embDomain (componentEmbedding n) g) (component_support g)
  simpa only [finiteHilbert_emb_norm,← testNorm_restricted] using And.intro h1 h2


-- @@ L253-255 verbatim
def predualBlockHilbertEquiv (n : ℕ) : PredualBlock n ≃L[ℝ] CoordinateHilbert (BlockNode n) :=
  completionHilbertEquiv (blockTests n) (Real.sqrt (n+2)) (Real.sqrt_nonneg _)
    (fun g => (block_hilbert_comparisons n g).1) (fun g => (block_hilbert_comparisons n g).2)


-- @@ L257-258 verbatim
theorem predualBlock_reflexive (n : ℕ) : IsReflexive (PredualBlock n) :=
  reflexive_equiv (predualBlockHilbertEquiv n) hilbert_reflexive


-- @@ L260-260 verbatim
end BoundedTreePotentials.Segments



-- @@ L263-263 verbatim
end


-- @@ L265-265 verbatim
end OAI
