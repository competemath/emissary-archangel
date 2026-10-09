import OAI.Analysis.TreePotential.Dyadic


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set

-- @@ L7-7 verbatim
open scoped ENNReal

-- @@ L8-8 verbatim
namespace BoundedTreePotentials


-- @@ L10-10 verbatim
abbrev ForestNode := (n : ℕ) × Tree (n+1)


-- @@ L12-12 verbatim
namespace FiniteOuterHead

-- @@ L13-13 verbatim
open TreeCalculus


-- @@ L15-17 verbatim
def subtreeEmbedding (n : ℕ) : Tree (n+1) ↪ ForestNode where
  toFun s := ⟨n,s⟩
  inj' _ _ h := Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq


-- @@ L19-20 verbatim
def ancestors (s : ForestNode) : Finset ForestNode :=
  (pathNodes s.2).map (subtreeEmbedding s.1)


-- @@ L22-22 verbatim
def hull (S : Finset ForestNode) : Finset ForestNode := S.biUnion ancestors


-- @@ L24-33 verbatim
lemma mem_ancestors_same (n : ℕ) (s r : Tree (n+1)) :
    (⟨n,r⟩ : ForestNode) ∈ ancestors ⟨n,s⟩ ↔ r.val <+: s.val := by
  simp only [ancestors, Finset.mem_map]
  constructor
  · rintro ⟨t, ht, he⟩
    have ht' : t = r := (subtreeEmbedding n).injective he
    subst t
    exact (mem_pathNodes_iff _ _).mp ht
  · intro hr
    exact ⟨r, (mem_pathNodes_iff _ _).mpr hr, rfl⟩


-- @@ L35-37 verbatim
lemma hull_contains (S : Finset ForestNode) {s : ForestNode} (hs : s ∈ S) : s ∈ hull S := by
  apply Finset.mem_biUnion.mpr
  exact ⟨s, hs, (mem_ancestors_same s.1 s.2 s.2).mpr (List.prefix_refl _)⟩


-- @@ L39-52 verbatim
lemma hull_initial (S : Finset ForestNode) {n : ℕ} {s r : Tree (n+1)}
    (hs : (⟨n,s⟩ : ForestNode) ∈ hull S) (hr : r.val <+: s.val) :
    (⟨n,r⟩ : ForestNode) ∈ hull S := by
  obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp hs
  obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hst
  have htn : t.1 = n := congrArg Sigma.fst he
  rcases t with ⟨k,v⟩
  dsimp only at htn
  subst k
  have hus : u = s := (subtreeEmbedding n).injective he
  subst u
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨n,v⟩, ht, (mem_ancestors_same n v r).mpr ?_⟩
  exact hr.trans ((mem_pathNodes_iff _ _).mp hu)


-- @@ L54-72 verbatim
def ofFinset (S : Finset ForestNode) : FiniteOuterHead where
  nodes n := {r | ∃ h : r.length ≤ n+1, (⟨n,⟨r,h⟩⟩ : ForestNode) ∈ hull S}
  initial n := by
    intro s r hs hrs
    obtain ⟨h, hh⟩ := hs
    exact ⟨hrs.length_le.trans h, hull_initial S hh hrs⟩
  finite_nodes := by
    have he : {s : ForestNode | ∃ h : s.2.val.length ≤ s.1+1,
        (⟨s.1,⟨s.2.val,h⟩⟩ : ForestNode) ∈ hull S} = (hull S : Set ForestNode) := by
      ext s
      constructor
      · rintro ⟨h,hh⟩
        exact hh
      · intro hh
        exact ⟨s.2.property, hh⟩
    change {s : ForestNode | ∃ h : s.2.val.length ≤ s.1+1,
      (⟨s.1,⟨s.2.val,h⟩⟩ : ForestNode) ∈ hull S}.Finite
    rw [he]
    exact (hull S).finite_toSet


-- @@ L74-75 verbatim
lemma ofFinset_contains (S : Finset ForestNode) {s : ForestNode} (hs : s ∈ S) :
    s.2.val ∈ (ofFinset S).nodes s.1 := ⟨s.2.property, hull_contains S hs⟩


-- @@ L77-77 verbatim
end FiniteOuterHead


-- @@ L79-79 verbatim
namespace ForestCoordinates

-- @@ L80-80 verbatim
open scoped Classical

-- @@ L81-81 verbatim
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]

-- @@ L82-82 verbatim
variable (e : ∀ n, E n ≃L[ℝ] TreeHilbert (n+1))


-- @@ L84-84 verbatim
def coefficient (x : HilbertSum E) (s : ForestNode) : ℝ := e s.1 (x s.1) s.2


-- @@ L86-87 verbatim
def coefficientCLM (s : ForestNode) : HilbertSum E →L[ℝ] ℝ :=
  (lp.evalCLM ℝ _ 2 s.2).comp ((e s.1).toContinuousLinearMap.comp (lp.evalCLM ℝ E 2 s.1))


-- @@ L89-90 verbatim
@[simp] lemma coefficientCLM_apply (s : ForestNode) (x : HilbertSum E) :
    coefficientCLM e s x = coefficient e x s := rfl


-- @@ L92-93 verbatim
@[simp] lemma coefficient_add (x y : HilbertSum E) (s : ForestNode) :
    coefficient e (x+y) s = coefficient e x s+coefficient e y s := (coefficientCLM e s).map_add x y

-- @@ L94-95 verbatim
@[simp] lemma coefficient_smul (a : ℝ) (x : HilbertSum E) (s : ForestNode) :
    coefficient e (a • x) s = a*coefficient e x s := (coefficientCLM e s).map_smul a x

-- @@ L96-96 verbatim
@[simp] lemma coefficient_zero (s : ForestNode) : coefficient e 0 s = 0 := map_zero (coefficientCLM e s)


-- @@ L98-104 verbatim
lemma coefficient_ext {x y : HilbertSum E} (h : ∀ s, coefficient e x s = coefficient e y s) : x = y := by
  apply Subtype.ext
  funext n
  apply (e n).injective
  apply Subtype.ext
  funext s
  exact h ⟨n,s⟩


-- @@ L106-125 verbatim
/-- The actual finite node support, not only finite component support. -/
def finiteNodeSpace : Submodule ℝ (HilbertSum E) where
  carrier := {x | (Function.support (coefficient e x)).Finite}
  zero_mem' := by
    change (Function.support (coefficient e (0 : HilbertSum E))).Finite
    have he : coefficient e (0 : HilbertSum E) = 0 := funext (coefficient_zero e)
    rw [he, Function.support_zero]
    exact Set.finite_empty
  add_mem' hx hy := by
    apply (hx.union hy).subset
    intro s hs
    contrapose! hs
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hs
    simp [Function.mem_support, coefficient_add, hs.1, hs.2]
  smul_mem' a x hx := by
    apply hx.subset
    intro s hs
    contrapose! hs
    simp only [Function.mem_support, not_not] at hs ⊢
    simp only [coefficient_smul, hs, mul_zero]


-- @@ L127-141 verbatim
lemma finiteNodeSpace_single (n : ℕ) (s : Tree (n+1)) (a : ℝ) :
    lp.single 2 n ((e n).symm (lp.single 2 s a)) ∈ finiteNodeSpace e := by
  apply (Set.finite_singleton (⟨n,s⟩ : ForestNode)).subset
  intro q hq
  rw [Set.mem_singleton_iff]
  rcases q with ⟨k,t⟩
  by_contra hne
  have hz : coefficient e (lp.single 2 n ((e n).symm (lp.single 2 s a))) ⟨k,t⟩ = 0 := by
    by_cases hn : k = n
    · subst k
      have ht : t ≠ s := fun h => hne (by subst t; rfl)
      simp only [coefficient, lp.single_apply_self, ContinuousLinearEquiv.apply_symm_apply,
        lp.single_apply_ne (E := fun _ : Tree (n+1) => ℝ) 2 s a ht]
    · simp only [coefficient, lp.single_apply_ne 2 n _ hn, map_zero, lp.coeFn_zero, Pi.zero_apply]
  exact hq hz


-- @@ L143-162 verbatim
lemma dense_finiteNodeSpace : Dense (finiteNodeSpace e : Set (HilbertSum E)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro x hx
  let U := (finiteNodeSpace e).topologicalClosure
  have hU : IsClosed (U : Set (HilbertSum E)) := (finiteNodeSpace e).isClosed_topologicalClosure
  have heach : ∀ n, lp.single 2 n (x n) ∈ U := by
    intro n
    let L : TreeHilbert (n+1) →L[ℝ] HilbertSum E :=
      (lp.singleContinuousLinearMap ℝ E 2 n).comp (e n).symm.toContinuousLinearMap
    have hs := L.hasSum (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) (e n (x n)))
    have hs' : HasSum (fun s : Tree (n+1) => lp.single 2 n ((e n).symm (lp.single 2 s (e n (x n) s))))
        (lp.single 2 n (x n)) := by
      simpa only [L, ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using hs
    apply hU.mem_of_tendsto hs'
    exact Filter.Eventually.of_forall (fun S => U.sum_mem fun s hs =>
      (finiteNodeSpace e).le_topologicalClosure (finiteNodeSpace_single e n s _))
  apply hU.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun S => U.sum_mem fun n hn => heach n)


-- @@ L164-172 verbatim
lemma finiteNodeSpace_head (x : HilbertSum E) (hx : x ∈ finiteNodeSpace e) :
    ∃ A : FiniteOuterHead, ∀ s : ForestNode, s.2.val ∉ A.nodes s.1 → coefficient e x s = 0 := by
  let S := hx.toFinset
  refine ⟨FiniteOuterHead.ofFinset S, ?_⟩
  intro s hs
  by_contra hne
  apply hs
  apply FiniteOuterHead.ofFinset_contains
  exact hx.mem_toFinset.mpr hne


-- @@ L174-179 verbatim
lemma exists_finite_head_approx (x : HilbertSum E) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : HilbertSum E, ∃ A : FiniteOuterHead, ‖x-p‖ < ε ∧
      ∀ s : ForestNode, s.2.val ∉ A.nodes s.1 → coefficient e p s = 0 := by
  obtain ⟨p, hp, hd⟩ := (dense_finiteNodeSpace e).exists_dist_lt x hε
  obtain ⟨A,hA⟩ := finiteNodeSpace_head e p hp
  exact ⟨p,A,by simpa only [dist_eq_norm] using hd,hA⟩


-- @@ L181-183 verbatim
def finiteCoordinates (A : FiniteOuterHead) : HilbertSum E →L[ℝ]
    ({s : ForestNode // s.2.val ∈ A.nodes s.1} → ℝ) :=
  ContinuousLinearMap.pi (fun s => coefficientCLM e s.val)


-- @@ L185-188 verbatim
def coordinateTail (A : FiniteOuterHead) : ClosedFiniteCodim (HilbertSum E) := by
  letI : Fintype {s : ForestNode // s.2.val ∈ A.nodes s.1} := A.finite_nodes.fintype
  exact ⟨(finiteCoordinates e A).ker, (finiteCoordinates e A).isClosed_ker,
    Module.Finite.equiv (finiteCoordinates e A).toLinearMap.quotKerEquivRange.symm⟩


-- @@ L190-194 verbatim
lemma mem_coordinateTail (A : FiniteOuterHead) (x : HilbertSum E) :
    x ∈ (coordinateTail e A).space ↔ ∀ s : ForestNode, s.2.val ∈ A.nodes s.1 → coefficient e x s = 0 := by
  change finiteCoordinates e A x = 0 ↔ _
  simp only [finiteCoordinates, ContinuousLinearMap.pi_apply, coefficientCLM_apply,
    funext_iff, Pi.zero_apply, Subtype.forall]


-- @@ L196-196 verbatim
end ForestCoordinates



-- @@ L199-199 verbatim
end BoundedTreePotentials


-- @@ L201-201 verbatim
end


-- @@ L203-203 verbatim
end OAI
