import OAI.Combinatorics.SparsestCut.FiniteDuality


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter Matrix


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
namespace UniformSparsestCut


-- @@ L12-12 verbatim
section CutSums


-- @@ L14-14 verbatim
variable {n : ℕ}


-- @@ L16-24 verbatim
lemma pairSum_nonneg {f : Fin n → Fin n → ℝ} (hf : ∀ i j, 0 ≤ f i j) :
    0 ≤ pairSum f := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact hf _ _
  · exact le_rfl


-- @@ L26-33 verbatim
lemma pairSum_add (f g : Fin n → Fin n → ℝ) :
    pairSum (fun i j => f i j + g i j) = pairSum f + pairSum g := by
  simp only [pairSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring


-- @@ L35-42 verbatim
lemma pairSum_smul (a : ℝ) (f : Fin n → Fin n → ℝ) :
    pairSum (fun i j => a * f i j) = a * pairSum f := by
  simp only [pairSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring


-- @@ L44-57 verbatim
lemma pairSum_swap (f : Fin n → Fin n → ℝ) (hd : ∀ i, f i i = 0) :
    pairSum f + pairSum (fun i j => f j i) = ∑ i, ∑ j, f i j := by
  unfold pairSum
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.mpr h.le]
  · subst j; simp [hd]
  · simp [h, not_lt.mpr h.le]


-- @@ L59-63 verbatim
lemma orderedSum_eq_two_pairSum (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * pairSum f := by
  have he : (fun i j => f j i) = f := funext (fun i => funext (fun j => hs j i))
  simpa [he, two_mul] using (pairSum_swap f hd).symm


-- @@ L65-82 verbatim
lemma le_pairSum {f : Fin n → Fin n → ℝ} (hf : ∀ i j, 0 ≤ f i j)
    {i j : Fin n} (hij : i < j) : f i j ≤ pairSum f := by
  calc
    f i j ≤ ∑ k, if i < k then f i k else 0 := by
      have := Finset.single_le_sum (s := Finset.univ)
        (f := fun k => if i < k then f i k else 0)
        (fun k hk => by split_ifs; exact hf _ _; exact le_rfl) (Finset.mem_univ j)
      simpa [hij] using this
    _ ≤ pairSum f := by
      unfold pairSum
      apply Finset.single_le_sum (f := fun k => ∑ l, if k < l then f k l else 0) (a := i)
      · intro k hk
        apply Finset.sum_nonneg
        intro l hl
        split_ifs
        · exact hf _ _
        · exact le_rfl
      · exact Finset.mem_univ i


-- @@ L84-84 verbatim
noncomputable def cutIndicator (B : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ B then 1 else 0

-- @@ L85-86 verbatim
noncomputable def cutDist (B : Finset (Fin n)) (i j : Fin n) : ℝ :=
  |cutIndicator B i - cutIndicator B j|

-- @@ L87-87 verbatim
noncomputable def cutDemand (B : Finset (Fin n)) : ℝ := (B.card : ℝ) * (Bᶜ.card : ℝ)


-- @@ L89-89 verbatim
def Cut (n : ℕ) := {B : Finset (Fin n) // B.Nonempty ∧ B ≠ Finset.univ}


-- @@ L91-91 verbatim
noncomputable instance : Fintype (Cut n) := by unfold Cut; exact Fintype.ofFinite _


-- @@ L93-93 verbatim
lemma cutDist_nonneg (B : Finset (Fin n)) (i j : Fin n) : 0 ≤ cutDist B i j := abs_nonneg _

-- @@ L94-95 verbatim
lemma cutDist_symm (B : Finset (Fin n)) (i j : Fin n) : cutDist B i j = cutDist B j i :=
  abs_sub_comm _ _

-- @@ L96-97 verbatim
@[simp] lemma cutDist_self (B : Finset (Fin n)) (i : Fin n) : cutDist B i i = 0 := by
  simp [cutDist]


-- @@ L99-103 verbatim
lemma cutDist_binary (B : Finset (Fin n)) (i j : Fin n) :
    cutDist B i j = 0 ∨ cutDist B i j = 1 := by
  classical
  unfold cutDist cutIndicator
  split_ifs <;> norm_num


-- @@ L105-106 verbatim
lemma cutDist_triangle (B : Finset (Fin n)) (i j k : Fin n) :
    cutDist B i k ≤ cutDist B i j + cutDist B j k := abs_sub_le _ _ _


-- @@ L108-111 verbatim
lemma cutDemand_eq (B : Finset (Fin n)) :
    cutDemand B = (B.card : ℝ) * ((n : ℝ) - B.card) := by
  unfold cutDemand
  rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (show B.card ≤ n by simpa using B.card_le_univ)]


-- @@ L113-117 verbatim
lemma cutDemand_pos (B : Cut n) : 0 < cutDemand B.1 := by
  unfold cutDemand
  apply mul_pos
  · exact_mod_cast Finset.card_pos.mpr B.2.1
  · exact_mod_cast Finset.card_pos.mpr (by simpa [Finset.nonempty_iff_ne_empty] using B.2.2)


-- @@ L119-130 verbatim
lemma ordered_cut_sum (B : Finset (Fin n)) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f i j * cutDist B i j) =
      (∑ i ∈ B, ∑ j ∈ Bᶜ, f i j) + (∑ i ∈ Bᶜ, ∑ j ∈ B, f i j) := by
  classical
  have hp (i j : Fin n) : f i j * cutDist B i j =
      (if i ∈ B then if j ∈ Bᶜ then f i j else 0 else 0) +
      (if i ∈ Bᶜ then if j ∈ B then f i j else 0 else 0) := by
    unfold cutDist cutIndicator
    by_cases hi : i ∈ B <;> by_cases hj : j ∈ B <;> simp [hi, hj]
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]


-- @@ L132-142 verbatim
lemma ordered_cut_sum_symm (B : Finset (Fin n)) (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j * cutDist B i j) = 2 * (∑ i ∈ B, ∑ j ∈ Bᶜ, f i j) := by
  rw [ordered_cut_sum, two_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hs j i


-- @@ L144-149 verbatim
lemma pairSum_cut (B : Finset (Fin n)) : pairSum (cutDist B) = cutDemand B := by
  have h := ordered_cut_sum_symm B (fun _ _ => 1) (fun _ _ => rfl)
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [orderedSum_eq_two_pairSum _ (cutDist_symm B) (cutDist_self B)] at h
  unfold cutDemand
  nlinarith


-- @@ L151-157 verbatim
lemma cut_capacity_pair (C : Capacity n) (B : Finset (Fin n)) :
    pairSum (fun i j => C.cap i j * cutDist B i j) =
      ∑ i ∈ B, ∑ j ∈ Bᶜ, C.cap i j := by
  have h := ordered_cut_sum_symm B C.cap C.symm
  rw [orderedSum_eq_two_pairSum _ (fun i j => by rw [C.symm i j, cutDist_symm B i j])
    (fun i => by simp)] at h
  linarith


-- @@ L159-159 verbatim
end CutSums


-- @@ L161-161 verbatim
end UniformSparsestCut


-- @@ L163-163 verbatim
end


-- @@ L165-165 verbatim
end OAI
