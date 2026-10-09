import OAI.Analysis.C0Absorption.Operators


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Filter Topology

-- @@ L6-6 verbatim
open scoped NNReal BigOperators ZeroAtInfty

-- @@ L7-7 verbatim
open NormedSpace


-- @@ L9-9 verbatim
namespace C0Absorption

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open Set Filter Topology

-- @@ L12-12 verbatim
open scoped NNReal BigOperators


-- @@ L14-14 verbatim
section LocalOnto

-- @@ L15-16 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L18-23 verbatim
theorem range_mem_nhds_of_approx {f : E → F} {a : E} (S : E ≃L[ℝ] F)
    (s : Set E) (hs : s∈nhds a) (c : ℝ≥0)
    (hc : c<‖(S.symm : F →L[ℝ] E)‖₊⁻¹) (ha : ApproximatesLinearOn f (S : E →L[ℝ] F) s c) :
    Set.range f∈nhds (f a) := by
  have hh := ha.image_mem_nhds S.toNonlinearRightInverse hs (Or.inr hc)
  exact mem_of_superset hh (Set.image_subset_range f s)


-- @@ L25-57 verbatim
theorem surjective_of_punctured_local_onto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial E]
    (f : E → F) {c C : ℝ≥0} (hf : AntilipschitzWith c f) (hLip : LipschitzWith C f)
    (hzero : f 0=0) (hconn : IsPreconnected ({0}ᶜ : Set F))
    (hlocal : ∀ x≠0, Set.range f∈nhds (f x)) : Function.Surjective f := by
  let K : Set F := {0}ᶜ
  let A : Set K := Subtype.val ⁻¹' Set.range f
  let : PreconnectedSpace K := Subtype.preconnectedSpace hconn
  have hclosed : IsClosed A := (hf.isClosed_range hLip.uniformContinuous).preimage continuous_subtype_val
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨x,hx⟩ := hy
    have hx0 : x≠0 := by
      intro hx0
      have he : y.val=0 := by rw [← hx,hx0,hzero]
      exact y.property (by simpa only [Set.mem_singleton_iff] using he)
    have hn : Set.range f∈nhds y.val := by rw [← hx]; exact hlocal x hx0
    exact continuous_subtype_val.continuousAt hn
  have hne : A.Nonempty := by
    obtain ⟨x,hx⟩ := exists_ne (0 : E)
    have hx' : f x≠0 := by intro he; exact hx (hf.injective (he.trans hzero.symm))
    refine ⟨⟨f x,?_⟩,x,rfl⟩
    simpa only [K,Set.mem_compl_iff,Set.mem_singleton_iff] using hx'
  have heq : A=Set.univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hne
  intro y
  by_cases hy : y=0
  · exact ⟨0,hzero.trans hy.symm⟩
  · let yy : K := ⟨y,by simpa only [K,Set.mem_compl_iff,Set.mem_singleton_iff] using hy⟩
    have hh : yy∈A := by rw [heq]; trivial
    exact hh


-- @@ L59-59 verbatim
end LocalOnto

-- @@ L60-60 verbatim
end

-- @@ L61-61 verbatim
end C0Absorption


-- @@ L63-63 verbatim
end OAI
