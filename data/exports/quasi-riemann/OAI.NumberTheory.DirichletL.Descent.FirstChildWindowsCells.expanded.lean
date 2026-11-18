import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsActual
import OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.InverseMomentFirstChildWindows

-- @@ L9-9 verbatim
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels

-- @@ L10-10 verbatim
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)

-- @@ L11-11 verbatim
open ConcreteTraceCRT (eisEmbedding)

-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L14-14 verbatim
abbrev SourceIndex := Fin 6→ℕ


-- @@ L16-17 verbatim
def sourceNorms {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ) : Fin 6→ℝ :=
  ![A₁ x,A₂ x,C x,‖eisEmbedding (d x)‖^2,R x,‖eisEmbedding (h x)‖^2]


-- @@ L19-19 verbatim
def sourceIndex {κ : Type*} (q : κ→Fin 6→ℝ) (x : κ) : SourceIndex := fun i=>dyadIndex (q x i)

-- @@ L20-20 verbatim
def sourceKeys {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) := S.image (sourceIndex q)

-- @@ L21-22 verbatim
def sourceCell {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) (k : SourceIndex) :=
  S.filter (fun x=>sourceIndex q x=k)


-- @@ L24-25 verbatim
def commonKeys {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι) : Finset ℕ :=
  F.powerset.image (fun D=>dyadIndex (primeProductNorm p D))


-- @@ L27-28 verbatim
def commonSelector {ι : Type*} [DecidableEq ι] (p : ι→O) (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) : ℂ :=
  if dyadIndex (primeProductNorm p D)=l then selector D else 0


-- @@ L30-32 verbatim
def rawScales (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) : Fin 9→ℝ :=
  ![dyadScale (k 0),dyadScale (k 1),dyadScale (k 2),dyadScale (k 3),dyadScale (k 4),
    dyadScale l,dyadScale (k 5),T₁,T₂]


-- @@ L34-37 verbatim
lemma rawScales_pos (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (h₁ : 0<T₁) (h₂ : 0<T₂) :
    ∀i,0<rawScales k l T₁ T₂ i := by
  intro i
  fin_cases i <;> first | exact dyadScale_pos _ | exact h₁ | exact h₂


-- @@ L39-49 verbatim
lemma sourceNorms_ge_one {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ)
    (hA₁ : 1≤A₁ x) (hA₂ : 1≤A₂ x) (hC : 1≤C x) (hR : 1≤R x)
    (hd : d x≠0) (hh : h x≠0) : ∀i,1≤sourceNorms A₁ A₂ C R d h x i := by
  intro i
  fin_cases i
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hd
  · exact hR
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hh


-- @@ L51-59 verbatim
lemma sourceCell_ratios {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ)
    (hq : ∀x∈S,∀i,1≤q x i) (k : SourceIndex) (x : κ) (hx : x∈sourceCell q S k) (i : Fin 6) :
    q x i/dyadScale (k i)∈Set.Icc 1 2 := by
  obtain ⟨hxs,hindex⟩ := Finset.mem_filter.mp hx
  have hh := dyadIndex_bounds (q x i) (hq x hxs i)
  have he : dyadIndex (q x i)=k i := congrFun hindex i
  rw [he] at hh
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
    (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩


-- @@ L61-87 verbatim
theorem actual_original_cell_ratios {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (S : Finset κ) (selector C₁ C₂ : κ→Finset ι→ℂ)
    (A₁ A₂ C R : κ→ℝ) (d h : κ→O)
    (hq : ∀x∈S,∀i,1≤sourceNorms A₁ A₂ C R d h x i)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (x : κ)
    (hx : x∈sourceCell (sourceNorms A₁ A₂ C R d h) S k) (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0) :
    ∀i,actualOuterRatios p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  have hl : dyadIndex (primeProductNorm p j.2.1)=l := by
    by_contra he
    exact hn (by simp [commonSelector,he])
  have hh := dyadIndex_bounds _ (SecondPassArithmetic.primeProductNorm_ge_one p hp j.2.1)
  rw [hl] at hh
  have hD : primeProductNorm p j.2.1/dyadScale l∈Set.Icc 1 2 :=
    ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
      (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩
  intro i
  fin_cases i
  · exact sourceCell_ratios _ S hq k x hx 0
  · exact sourceCell_ratios _ S hq k x hx 1
  · exact sourceCell_ratios _ S hq k x hx 2
  · exact sourceCell_ratios _ S hq k x hx 3
  · exact sourceCell_ratios _ S hq k x hx 4
  · exact hD
  · exact sourceCell_ratios _ S hq k x hx 5


-- @@ L89-92 verbatim
lemma sum_source_cells {κ β : Type*} [DecidableEq κ] [AddCommMonoid β]
    (q : κ→Fin 6→ℝ) (S : Finset κ) (f : κ→β) :
    (∑x∈S,f x)=∑k∈sourceKeys q S,∑x∈sourceCell q S k,f x := by
  exact (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem (sourceIndex q) hx) f).symm


-- @@ L94-98 verbatim
lemma common_key_of_index {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices F) :
    dyadIndex (primeProductNorm p j.2.1)∈commonKeys p F := by
  apply Finset.mem_image_of_mem
  exact (Finset.mem_sigma.mp (Finset.mem_product.mp hj).2).1


-- @@ L100-108 verbatim
lemma sum_common_cells {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι)
    (selector : Finset ι→ℂ) (G : FirstCommonIndex ι→ℂ) :
    (∑j∈firstCommonIndices F,selector j.2.1*G j)=
      ∑l∈commonKeys p F,∑j∈firstCommonIndices F,commonSelector p selector l j.2.1*G j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hkey := common_key_of_index p F j hj
  simp [commonSelector,ite_mul,hkey]


-- @@ L110-125 verbatim
theorem original_signed_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑k∈sourceKeys q S,∑l∈commonKeys p F,∑x∈sourceCell q S k,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [sum_source_cells q S]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑x∈sourceCell q S k,∑l∈commonKeys p F,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_common_cells p F (selector x) (G x)
    _ = _ := Finset.sum_comm


-- @@ L127-127 verbatim
end SevenEighths.InverseMomentFirstChildWindows

-- @@ L128-128 verbatim
end


-- @@ L130-130 verbatim
end OAI
