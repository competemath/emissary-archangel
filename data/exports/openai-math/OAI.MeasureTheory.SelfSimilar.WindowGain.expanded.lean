import OAI.MeasureTheory.SelfSimilar.ScaleGain


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uα uβ


-- @@ L7-7 verbatim
namespace EntropyRateDimension.Typed

-- @@ L8-8 verbatim
open MeasureTheory MeasureEntropy FairPairs Windows

-- @@ L9-9 verbatim
open scoped BigOperators ENNReal

-- @@ L10-10 verbatim
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]


-- @@ L12-15 verbatim
noncomputable def retainedCapacity (S : System α) (tag : α → β)
    (A' : ℝ) (n : ℕ) (a B L : ℤ) (W : List α) (j : ℕ) : ℝ :=
  if Retained (fun j => S.listDepth (W.take j)) A' n a B L j then
    capacity (listLaw S tag ((W.drop j).take n)) (L-⌈S.listDepth (W.take j)⌉) else 0


-- @@ L17-21 verbatim
noncomputable def retainedDrop (S : System α) (tag : α → β) (μ : Measure ℝ)
    (M : ℕ) (A' : ℝ) (n : ℕ) (a B L : ℤ) (W : List α) (j : ℕ) : ℝ :=
  if Retained (fun j => S.listDepth (W.take j)) A' n a B L j then
    suffixWindow S tag μ ((2 : ℝ)^(-L)/M) (M*M) W j-
      suffixWindow S tag μ ((2 : ℝ)^(-L)/M) (M*M) W (j+n) else 0


-- @@ L23-30 verbatim
omit [Fintype α] [DecidableEq β] in
theorem three_segment {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    (((List.ofFn u++List.ofFn w)++List.ofFn z).drop j).take n=List.ofFn w := by
  have h1 : ((List.ofFn u++List.ofFn w)++List.ofFn z).drop j=List.ofFn w++List.ofFn z := by
    rw [List.append_assoc]
    simpa only [List.length_ofFn] using (List.drop_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))
  rw [h1]
  simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn w) (l₂ := List.ofFn z))


-- @@ L32-36 verbatim
omit [Fintype α] [DecidableEq β] in
theorem three_take {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    ((List.ofFn u++List.ofFn w)++List.ofFn z).take j=List.ofFn u := by
  rw [List.append_assoc]
  simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))


-- @@ L38-42 verbatim
theorem three_retained (S : System α) (A' : ℝ) (a B L : ℤ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    Retained (fun i => S.listDepth (((List.ofFn u++List.ofFn w)++List.ofFn z).take i)) A' n a B L j ↔
      S.wordDepth w ≤ A'*n ∧ a ≤ L-⌈S.wordDepth u⌉ ∧ L-⌈S.wordDepth u⌉ ≤ B := by
  simp only [Retained,S.listDepth_take_add,add_sub_cancel_left,three_segment,three_take,S.listDepth_ofFn]


-- @@ L44-46 verbatim
theorem suffixLaw_at_append (S : System α) (tag : α → β) (μ : Measure ℝ) (U V : List α) :
    suffixLaw S tag μ (U++V) U.length=listScaledTail S tag μ (S.wordAffine U).1 V := by
  simp only [suffixLaw,List.take_append_length,List.drop_append_length]


-- @@ L48-56 verbatim
theorem three_suffix_start (S : System α) (tag : α → β) (μ : Measure ℝ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    suffixLaw S tag μ ((List.ofFn u++List.ofFn w)++List.ofFn z) j=
      scaledTail S tag μ (S.completeMap u).1 (Fin.append w z) := by
  rw [List.append_assoc]
  have h := suffixLaw_at_append S tag μ (List.ofFn u) (List.ofFn w++List.ofFn z)
  simp only [List.length_ofFn] at h
  rw [h,← List.ofFn_fin_append,listScaledTail_ofFn]
  rfl


-- @@ L58-65 verbatim
theorem three_suffix_end (S : System α) (tag : α → β) (μ : Measure ℝ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    suffixLaw S tag μ ((List.ofFn u++List.ofFn w)++List.ofFn z) (j+n)=
      scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1) z := by
  have h := suffixLaw_at_append S tag μ (List.ofFn u++List.ofFn w) (List.ofFn z)
  simp only [List.length_append,List.length_ofFn] at h
  rw [h,listScaledTail_ofFn,S.wordAffine_append]
  rfl


-- @@ L67-92 verbatim
theorem expected_retained_gain (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {H j n : ℕ} (hH : j+n ≤ H) (A' : ℝ) (a B L : ℤ) :
    δ/2*S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j) ≤
      S.wordAverage H (fun W => retainedDrop S tag μ M A' n a B L W j) := by
  classical
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [← S.wordAverage_mul]
  apply S.wordAverage_future_le (j+n) t
  intro v
  obtain ⟨⟨u,w⟩,rfl⟩ := (Fin.appendEquiv j n).surjective v
  change (∑ z : Fin t → α, S.wordWeight z*(δ/2*retainedCapacity S tag A' n a B L
    (List.ofFn (Fin.append u w)++List.ofFn z) j)) ≤
    ∑ z : Fin t → α, S.wordWeight z*retainedDrop S tag μ M A' n a B L
      (List.ofFn (Fin.append u w)++List.ofFn z) j
  simp only [List.ofFn_fin_append]
  have hgain := conditional_gain S tag hr μ hμ hc hδ hM he u w t L
  simp only [retainedCapacity,retainedDrop,three_retained,three_segment,three_take,
    S.listDepth_ofFn,listLaw_ofFn,suffixWindow,three_suffix_start,three_suffix_end]
  split_ifs
  · simpa only [← Finset.sum_mul,S.wordWeight_sum,one_mul] using hgain
  · simp only [mul_zero,Finset.sum_const_zero,le_refl]


-- @@ L94-113 verbatim
theorem expected_capacity_targets (S : System α) (tag : α → β)
    {H j n : ℕ} (hH : j+n ≤ H) (A' : ℝ) (a B T : ℤ)
    (ha : 1 ≤ a)
    (hcover : ∀ W : List α, 0 ≤ ⌈S.listDepth (W.take j)⌉ ∧ B+⌈S.listDepth (W.take j)⌉ ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j))=
      pairBudget S tag A' a B n := by
  classical
  rw [← S.wordAverage_finset_sum]
  have hpoint (W : List α) : (∑ L ∈ Finset.Icc 1 T, retainedCapacity S tag A' n a B L W j)=
      if S.listDepth ((W.drop j).take n) ≤ A'*n then
        ∑ ℓ ∈ Finset.Icc a B, capacity (listLaw S tag ((W.drop j).take n)) ℓ else 0 := by
    simp only [retainedCapacity,Retained,S.listDepth_take_add,add_sub_cancel_left]
    by_cases h : S.listDepth ((W.drop j).take n) ≤ A'*n
    · simp only [h,true_and]
      exact sum_target_shift _ a B _ T ha (hcover W).1 (hcover W).2
    · simp only [h,false_and,ite_false,Finset.sum_const_zero]
  simp_rw [hpoint]
  rw [S.wordAverage_segment hH (fun V => if S.listDepth V ≤ A'*n then
    ∑ ℓ ∈ Finset.Icc a B, capacity (listLaw S tag V) ℓ else 0)]
  simp only [System.wordAverage,System.listDepth_ofFn,listLaw_ofFn,pairBudget,mul_ite,mul_zero]


-- @@ L115-115 verbatim
end EntropyRateDimension.Typed


-- @@ L117-117 verbatim
end OAI
