import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsCells


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMomentFirstChildWindows

-- @@ L8-8 verbatim
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels

-- @@ L9-9 verbatim
open InverseSecondSourceBlocks (dyadIndex)

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-16 verbatim
def liveCommonKeys {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) : Finset ℕ :=
  (((S×ˢfirstCommonIndices F).filter (fun x=>selector x.1 x.2.2.1*G x.1 x.2≠0)).image
    (fun x=>dyadIndex (primeProductNorm p x.2.2.1)))


-- @@ L18-37 verbatim
lemma sum_live_common_cells {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) (x : κ) (hx : x∈S) :
    (∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑l∈liveCommonKeys p F S selector G,∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : selector x j.2.1*G x j=0
  · rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro l hl
    by_cases he : dyadIndex (primeProductNorm p j.2.1)=l
    · simpa only [commonSelector,he,ite_true] using hz
    · simp only [commonSelector,he,ite_false,zero_mul]
  · have hkey : dyadIndex (primeProductNorm p j.2.1)∈liveCommonKeys p F S selector G := by
      exact Finset.mem_image.mpr ⟨(x,j),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hj⟩,hz⟩,rfl⟩
    simp [commonSelector,ite_mul,hkey]


-- @@ L39-54 verbatim
theorem original_live_signed_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑k∈sourceKeys q S,∑l∈liveCommonKeys p F S selector G,∑x∈sourceCell q S k,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [sum_source_cells q S]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑x∈sourceCell q S k,∑l∈liveCommonKeys p F S selector G,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_live_common_cells p F S selector G x (Finset.mem_filter.mp hx).1
    _ = _ := Finset.sum_comm


-- @@ L56-71 verbatim
theorem liveCommonKeys_card {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (F : Finset ι) (S : Finset κ) (selector : κ→Finset ι→ℂ)
    (G : κ→FirstCommonIndex ι→ℂ) (R : ℝ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices F,selector x j.2.1*G x j≠0 → primeProductNorm p j.2.1≤R) :
    (liveCommonKeys p F S selector G).card≤dyadIndex R+1 := by
  have hsub : liveCommonKeys p F S selector G⊆Finset.range (dyadIndex R+1) := by
    intro l hl
    obtain ⟨⟨x,j⟩,hmem,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hxj,hn⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hxj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (primeProductNorm_pos p hp _) (hcap x hx j hj hn))
  simpa only [Finset.card_range] using Finset.card_le_card hsub


-- @@ L73-80 verbatim
theorem original_live_norm_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    ‖∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j‖≤
      ∑k∈sourceKeys q S,∑l∈liveCommonKeys p F S selector G,
        ‖∑x∈sourceCell q S k,∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j‖ := by
  rw [original_live_signed_partition p F S q selector G]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk=>norm_sum_le _ _))


-- @@ L82-82 verbatim
end SevenEighths.InverseMomentFirstChildWindows

-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end OAI
