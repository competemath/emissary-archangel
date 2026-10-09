import OAI.Geometry.PinnedDistances.ArithmeticHierarchy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3 u4 u5


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
open NumberField

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open MeasureTheory

-- @@ L13-13 verbatim
open scoped Topology

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory

-- @@ L16-16 verbatim
open scoped Topology ENNReal

-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
open MeasureTheory NumberField

-- @@ L19-22 verbatim
open scoped BigOperators

/- Finite off-diagonal variance. All diagonal terms are identically zero,
   not O(1/n): singleton cells may persist forever. -/

-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-24 verbatim
open scoped BigOperators

-- @@ L25-25 verbatim
open MeasureTheory

-- @@ L26-26 verbatim
namespace WeakPinned.Variance


-- @@ L28-28 verbatim
variable {P : Type u1} [Fintype P] [DecidableEq P]


-- @@ L30-30 verbatim
def prob (B : Finset P) (x : P) : ℝ := if x ∈ B then 1 / B.card else 0


-- @@ L32-33 verbatim
def pairProb (B : Finset P) (x y : P) : ℝ :=
  if x ∈ B ∧ y ∈ B ∧ x ≠ y then 1 / ((B.card : ℝ) * (B.card - 1)) else 0


-- @@ L35-41 verbatim
/-- Mixed cell probability, including B=P without an undefined outside branch.
    The outside column formula is never used when B=P. -/
def mixedProb (B : Finset P) (x y : P) : ℝ :=
  if x ∈ B ∧ x ≠ y then
    if y ∈ B then 1 / ((Fintype.card P : ℝ) * (B.card - 1))
    else 1 / ((Fintype.card P : ℝ) * B.card)
  else 0


-- @@ L43-46 verbatim
lemma sum_prob (B : Finset P) (hB : B.Nonempty) : ∑ x, prob B x = 1 := by
  classical
  rw [show (∑ x, prob B x) = ∑ x ∈ B, 1 / (B.card : ℝ) by simp [prob]]
  simp [hB.card_ne_zero]


-- @@ L48-67 verbatim
lemma sum_pairProb (B : Finset P) (hB : 2 ≤ B.card) (x : P) :
    ∑ y, pairProb B x y = prob B x := by
  classical
  by_cases hx : x ∈ B
  · have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
    have hk1 : (B.card : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
      linarith
    have he : ∀ y, pairProb B x y = if y ∈ B.erase x then
        1 / ((B.card : ℝ) * (B.card - 1)) else 0 := by
      intro y
      simp only [pairProb, hx, true_and, Finset.mem_erase, ne_comm (a := y)]
      simp only [and_comm]
    simp_rw [he]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, Finset.card_erase_of_mem hx]
    rw [Nat.cast_sub (by omega)]
    simp only [Nat.cast_one, prob, hx, reduceIte]
    field_simp
  · simp [pairProb, prob, hx]


-- @@ L69-71 verbatim
omit [Fintype P] in
lemma pairProb_symm (B : Finset P) (x y : P) : pairProb B x y = pairProb B y x := by
  simp only [pairProb, and_left_comm, ne_comm]


-- @@ L73-75 verbatim
omit [Fintype P] in
lemma pairProb_diag (B : Finset P) (x : P) : pairProb B x x = 0 := by
  simp [pairProb]


-- @@ L77-79 verbatim
omit [DecidableEq P] in
lemma ambient_card_ge_two (B : Finset P) (hB : 2 ≤ B.card) :
    2 ≤ Fintype.card P := hB.trans (Finset.card_le_univ B)


-- @@ L81-92 verbatim
lemma mixedProb_decompose (B : Finset P) (hB : 2 ≤ B.card) (x y : P) :
    mixedProb B x y = (B.card : ℝ) / Fintype.card P * pairProb B x y +
      prob B x / Fintype.card P * (if y ∈ B then 0 else 1) := by
  have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  have hn : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast (by have := ambient_card_ge_two B hB; omega : Fintype.card P ≠ 0)
  have hk1 : (B.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
    linarith
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> by_cases hxy : x = y
  all_goals simp_all [mixedProb, pairProb, prob]
  all_goals field_simp


-- @@ L94-109 verbatim
lemma sum_mixedProb (B : Finset P) (hB : 2 ≤ B.card) (x : P) :
    ∑ y, mixedProb B x y = prob B x := by
  have hn : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast (by have := ambient_card_ge_two B hB; omega : Fintype.card P ≠ 0)
  have hout : (∑ y : P, (if y ∈ B then (0 : ℝ) else 1)) =
      Fintype.card P - (B.card : ℝ) := by
    have he : ∀ y : P, (if y ∈ B then (0 : ℝ) else 1) =
        if y ∈ Bᶜ then 1 else 0 := by intro y; simp
    simp_rw [he]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_compl,
      Nat.cast_sub (Finset.card_le_univ B)]
  simp_rw [mixedProb_decompose B hB, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_pairProb B hB, hout]
  field_simp
  ring


-- @@ L111-119 verbatim
lemma sum_mixedProb_left (B : Finset P) (hB : 2 ≤ B.card) (y : P) :
    ∑ x, mixedProb B x y = 1 / Fintype.card P := by
  have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  simp_rw [mixedProb_decompose B hB, Finset.sum_add_distrib,
    ← Finset.mul_sum, pairProb_symm B _ y, sum_pairProb B hB,
    ← Finset.sum_mul, ← Finset.sum_div, sum_prob B hne]
  by_cases hy : y ∈ B <;> simp [prob, hy]
  field_simp


-- @@ L121-122 verbatim
lemma mixedProb_diag (B : Finset P) (x : P) : mixedProb B x x = 0 := by
  simp [mixedProb]


-- @@ L124-125 verbatim
def signedPair (B : Finset P) (x y : P) : ℝ :=
  pairProb B x y - 2 * mixedProb B x y + pairProb Finset.univ x y


-- @@ L127-128 verbatim
lemma signedPair_diag (B : Finset P) (x : P) : signedPair B x x = 0 := by
  simp [signedPair, pairProb_diag, mixedProb_diag]


-- @@ L130-137 verbatim
lemma signedPair_row (B : Finset P) (hB : 2 ≤ B.card) (x : P) :
    (∑ y, signedPair B x y) = 1 / Fintype.card P - prob B x := by
  have hP : 2 ≤ (Finset.univ : Finset P).card := ambient_card_ge_two B hB
  simp_rw [signedPair, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_pairProb B hB, sum_mixedProb B hB,
    sum_pairProb Finset.univ hP]
  simp only [prob, Finset.mem_univ, reduceIte, Finset.card_univ]
  ring


-- @@ L139-147 verbatim
lemma signedPair_col (B : Finset P) (hB : 2 ≤ B.card) (y : P) :
    (∑ x, signedPair B x y) = prob B y - 1 / Fintype.card P := by
  have hP : 2 ≤ (Finset.univ : Finset P).card := ambient_card_ge_two B hB
  simp_rw [signedPair, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_mixedProb_left B hB, pairProb_symm B _ y,
    pairProb_symm Finset.univ _ y, sum_pairProb B hB,
    sum_pairProb Finset.univ hP]
  simp only [prob, Finset.mem_univ, reduceIte, Finset.card_univ]
  ring


-- @@ L149-173 verbatim
/-- Exact cancellation against every additive off-diagonal overlap kernel.
    Only the sum of the two marginals is constrained. -/
lemma additive_cancel (H L : P → P → ℝ) (b : ℝ) (S : P → ℝ)
    (hdiag : ∀ x, H x x = 0)
    (hmass : (∑ x, ∑ y, H x y) = 0)
    (hmarg : ∀ x, (∑ y, H x y) + ∑ y, H y x = 0)
    (hL : ∀ x y, x ≠ y → L x y = b + S x + S y) :
    (∑ x, ∑ y, H x y * L x y) = 0 := by
  have hterm (x y : P) : H x y * L x y = H x y * (b + S x + S y) := by
    by_cases h : x = y
    · subst y; simp [hdiag]
    · rw [hL x y h]
  simp_rw [hterm, mul_add, Finset.sum_add_distrib]
  have hb : (∑ x, ∑ y, H x y * b) = (∑ x, ∑ y, H x y) * b := by
    simp_rw [Finset.sum_mul]
  rw [hb, hmass, zero_mul, zero_add]
  have h₁ : (∑ x, ∑ y, H x y * S x) = ∑ x, (∑ y, H x y) * S x := by
    simp_rw [Finset.sum_mul]
  have h₂ : (∑ x, ∑ y, H x y * S y) = ∑ x, (∑ y, H y x) * S x := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  rw [h₁, h₂, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro x _
  rw [← add_mul, hmarg, zero_mul]


-- @@ L175-187 verbatim
lemma variance_cancel (B : Finset P) (hB : 2 ≤ B.card)
    (L : P → P → ℝ) (b : ℝ) (S : P → ℝ)
    (hL : ∀ x y, x ≠ y → L x y = b + S x + S y) :
    (∑ x, ∑ y, signedPair B x y * L x y) = 0 := by
  apply additive_cancel _ _ b S (signedPair_diag B) _ _ hL
  · simp_rw [signedPair_row B hB, Finset.sum_sub_distrib]
    have hn : (Fintype.card P : ℝ) ≠ 0 := by
      exact_mod_cast (by have := ambient_card_ge_two B hB; omega : Fintype.card P ≠ 0)
    rw [sum_prob B (Finset.card_pos.mp (by omega))]
    simp [hn]
  · intro x
    rw [signedPair_row B hB, signedPair_col B hB]
    ring


-- @@ L189-190 verbatim
/-- Exact cell probabilities, with the diagonal excluded. -/
def pairCell (B C : Finset P) : ℝ := ∑ x ∈ C, ∑ y ∈ C, pairProb B x y


-- @@ L192-192 verbatim
def mixedCell (B C : Finset P) : ℝ := ∑ x ∈ C, ∑ y ∈ C, mixedProb B x y


-- @@ L194-194 verbatim
def cellProb (B C : Finset P) : ℝ := ((B ∩ C).card : ℝ) / B.card


-- @@ L196-199 verbatim
omit [Fintype P] in
lemma sum_prob_cell (B C : Finset P) : ∑ x ∈ C, prob B x = cellProb B C := by
  simp only [prob, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one_div,
    cellProb, Finset.inter_comm]


-- @@ L201-219 verbatim
omit [Fintype P] in
lemma pairCell_formula (B C : Finset P) :
    pairCell B C = ((B ∩ C).card : ℝ) * ((B ∩ C).card - 1) /
      ((B.card : ℝ) * (B.card - 1)) := by
  classical
  unfold pairCell pairProb
  rw [← Finset.sum_product C C (fun xy : P × P =>
    if xy.1 ∈ B ∧ xy.2 ∈ B ∧ xy.1 ≠ xy.2 then
      1 / ((B.card : ℝ) * (B.card - 1)) else 0), ← Finset.sum_filter]
  have hf : (C ×ˢ C).filter (fun xy => xy.1 ∈ B ∧ xy.2 ∈ B ∧ xy.1 ≠ xy.2) =
      (B ∩ C).offDiag := by
    ext ⟨x,y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag, Finset.mem_inter]
    tauto
  rw [hf, Finset.sum_const, nsmul_eq_mul, Finset.offDiag_card, ← Nat.mul_sub_one]
  by_cases hb : (B ∩ C).card = 0
  · simp [hb]
  · rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
    ring


-- @@ L221-231 verbatim
omit [Fintype P] in
lemma sum_outside_cell (B C : Finset P) :
    (∑ y ∈ C, if y ∈ B then (0 : ℝ) else 1) =
      (C.card : ℝ) - (B ∩ C).card := by
  have he : ∀ y, (if y ∈ B then (0 : ℝ) else 1) =
      if y ∉ B then 1 else 0 := by intro y; split_ifs <;> rfl
  simp_rw [he]
  rw [← Finset.sum_filter]
  rw [show C.filter (fun y => y ∉ B) = C \ B by ext y; simp]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_sdiff,
    Nat.cast_sub (Finset.card_le_card Finset.inter_subset_right)]


-- @@ L233-239 verbatim
lemma mixedCell_formula (B C : Finset P) (hB : 2 ≤ B.card) :
    mixedCell B C = (B.card : ℝ) / Fintype.card P * pairCell B C +
      cellProb B C / Fintype.card P * ((C.card : ℝ) - (B ∩ C).card) := by
  unfold mixedCell
  simp_rw [mixedProb_decompose B hB, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_outside_cell B C, ← Finset.sum_mul, ← Finset.sum_div, sum_prob_cell B C]
  rfl


-- @@ L241-244 verbatim
omit [Fintype P] in
lemma cellProb_nonneg (B C : Finset P) : 0 ≤ cellProb B C := by
  unfold cellProb
  positivity


-- @@ L246-251 verbatim
omit [Fintype P] in
lemma cellProb_le_one (B C : Finset P) : cellProb B C ≤ 1 := by
  unfold cellProb
  apply div_le_one_of_le₀
  · exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₂ := C))
  · positivity


-- @@ L253-265 verbatim
omit [Fintype P] in
lemma pairCell_nonneg (B C : Finset P) : 0 ≤ pairCell B C := by
  unfold pairCell pairProb
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs with h
  · have : 2 ≤ B.card := Finset.one_lt_card.mpr ⟨x,h.1,y,h.2.1,h.2.2⟩
    have : (2 : ℝ) ≤ B.card := by exact_mod_cast this
    have : 0 ≤ (B.card : ℝ) - 1 := by linarith
    positivity
  · rfl


-- @@ L267-270 verbatim
private lemma pair_fraction (k b : ℝ) (hk : k ≠ 0) (hk1 : k - 1 ≠ 0) :
    b * (b-1) / (k*(k-1)) = (b/k)^2 - (b/k)*(1-b/k)/(k-1) := by
  field_simp
  ring


-- @@ L272-280 verbatim
omit [Fintype P] in
lemma pairCell_centered (B C : Finset P) (hB : 2 ≤ B.card) :
    pairCell B C = (cellProb B C)^2 - cellProb B C * (1-cellProb B C) /
      ((B.card : ℝ) - 1) := by
  have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  have hk1 : (B.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
    linarith
  rw [pairCell_formula, cellProb, pair_fraction _ _ hk hk1]


-- @@ L282-290 verbatim
lemma mixedCell_centered (B C : Finset P) (hB : 2 ≤ B.card) :
    mixedCell B C = cellProb Finset.univ C * cellProb B C -
      (B.card : ℝ) / Fintype.card P *
        (cellProb B C * (1-cellProb B C) / ((B.card : ℝ)-1)) := by
  have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  rw [mixedCell_formula B C hB, pairCell_centered B C hB]
  simp only [cellProb, Finset.univ_inter, Finset.card_univ]
  field_simp
  ring


-- @@ L292-302 verbatim
lemma mixedCell_le_product (B C : Finset P) (hB : 2 ≤ B.card) :
    mixedCell B C ≤ cellProb Finset.univ C * cellProb B C := by
  rw [mixedCell_centered B C hB]
  have hp := cellProb_nonneg B C
  have hp1 := cellProb_le_one B C
  have hk : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
  have hk0 : 0 ≤ (B.card : ℝ) - 1 := by linarith
  have hp10 : 0 ≤ 1-cellProb B C := sub_nonneg.mpr hp1
  have hh : 0 ≤ (B.card : ℝ) / Fintype.card P *
      (cellProb B C * (1-cellProb B C) / ((B.card : ℝ)-1)) := by positivity
  linarith


-- @@ L304-317 verbatim
lemma signedCell_formula (B C : Finset P) (hB : 2 ≤ B.card) :
    (∑ x ∈ C, ∑ y ∈ C, signedPair B x y) =
      (cellProb B C - cellProb Finset.univ C)^2 +
      (2 * (B.card : ℝ) / Fintype.card P - 1) *
        (cellProb B C * (1-cellProb B C) / ((B.card : ℝ)-1)) -
      cellProb Finset.univ C * (1-cellProb Finset.univ C) /
        ((Fintype.card P : ℝ)-1) := by
  have hP : 2 ≤ (Finset.univ : Finset P).card := ambient_card_ge_two B hB
  simp_rw [signedPair, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change pairCell B C - 2 * mixedCell B C + pairCell Finset.univ C = _
  rw [pairCell_centered B C hB, mixedCell_centered B C hB,
    pairCell_centered Finset.univ C hP]
  simp only [Finset.card_univ]
  ring


-- @@ L319-338 verbatim
private lemma pair_fraction_bounds (n m : ℝ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    (1/2) * (m/n)^2 ≤ m*(m-1)/(n*(n-1)) ∧
      m*(m-1)/(n*(n-1)) ≤ (m/n)^2 := by
  have hn : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hmn0 : 0 ≤ m/n := div_nonneg (by linarith) hn.le
  have hlow : m/(2*n) ≤ (m-1)/(n-1) := by
    apply (div_le_div_iff₀ (by positivity) hn1).mpr
    nlinarith [mul_nonneg hn.le (show 0 ≤ m-2 by linarith)]
  have hupp : (m-1)/(n-1) ≤ m/n := by
    apply (div_le_div_iff₀ hn1 hn).mpr
    nlinarith
  have he : m*(m-1)/(n*(n-1)) = (m/n)*((m-1)/(n-1)) := by
    field_simp
  rw [he]
  constructor
  · calc
      (1/2) * (m/n)^2 = (m/n)*(m/(2*n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow hmn0
  · simpa only [sq] using mul_le_mul_of_nonneg_left hupp hmn0


-- @@ L340-347 verbatim
lemma uniform_pair_comparison (C : Finset P) (hC : 2 ≤ C.card) :
    (1/2) * (cellProb Finset.univ C)^2 ≤ pairCell Finset.univ C ∧
      pairCell Finset.univ C ≤ (cellProb Finset.univ C)^2 := by
  rw [pairCell_formula]
  simp only [cellProb, Finset.univ_inter, Finset.card_univ]
  apply pair_fraction_bounds
  · exact_mod_cast hC
  · exact_mod_cast Finset.card_le_univ C


-- @@ L349-360 verbatim
omit [Fintype P] in
lemma fiber_pair_lower (B C : Finset P) (hB : 2 ≤ B.card) :
    (1/2) * (if 2 / (B.card : ℝ) ≤ cellProb B C then (cellProb B C)^2 else 0) ≤
      pairCell B C := by
  split_ifs with hp
  · have hk : 0 < (B.card : ℝ) := by exact_mod_cast (by omega : 0 < B.card)
    have hb : (2 : ℝ) ≤ (B ∩ C).card :=
      (div_le_div_iff_of_pos_right hk).mp hp
    rw [pairCell_formula, cellProb]
    exact (pair_fraction_bounds _ _ hb
      (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₂ := C)))).1
  · simpa only [mul_zero] using pairCell_nonneg B C


-- @@ L362-371 verbatim
omit [Fintype P] in
lemma singleton_pairCell (B C : Finset P) (hC : C.card ≤ 1) : pairCell B C = 0 := by
  unfold pairCell
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have : x = y := Finset.card_le_one.mp hC x hx y hy
  subst y
  exact pairProb_diag B x


-- @@ L373-381 verbatim
lemma singleton_mixedCell (B C : Finset P) (hC : C.card ≤ 1) : mixedCell B C = 0 := by
  unfold mixedCell
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have : x = y := Finset.card_le_one.mp hC x hx y hy
  subst y
  exact mixedProb_diag B x


-- @@ L383-391 verbatim
omit [Fintype P] in
lemma singleton_fiber_term (B C : Finset P) (hB : 2 ≤ B.card) (hC : C.card ≤ 1) :
    (if 2 / (B.card : ℝ) ≤ cellProb B C then (cellProb B C)^2 else 0) = 0 := by
  have hk : 0 < (B.card : ℝ) := by exact_mod_cast (by omega : 0 < B.card)
  have hi : (B ∩ C).card ≤ 1 := (Finset.card_le_card Finset.inter_subset_right).trans hC
  have hiR : ((B ∩ C).card : ℝ) < 2 := by exact_mod_cast (by omega : (B ∩ C).card < 2)
  have hp : cellProb B C < 2 / (B.card : ℝ) :=
    (div_lt_div_iff_of_pos_right hk).mpr hiR
  simp only [not_le.mpr hp, reduceIte]


-- @@ L393-394 verbatim
def signedCell (B C : Finset P) : ℝ := pairCell B C - 2 * mixedCell B C +
    pairCell Finset.univ C


-- @@ L396-399 verbatim
lemma signedCell_eq (B C : Finset P) :
    signedCell B C = ∑ x ∈ C, ∑ y ∈ C, signedPair B x y := by
  simp only [signedCell, pairCell, mixedCell, signedPair,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]


-- @@ L401-402 verbatim
lemma singleton_signedCell (B C : Finset P) (hC : C.card ≤ 1) : signedCell B C = 0 := by
  simp [signedCell, singleton_pairCell _ _ hC, singleton_mixedCell _ _ hC]


-- @@ L404-416 verbatim
private lemma correction_bound (p k ε : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hk : 0 < k-1) (he : 1/(k-1) ≤ ε) :
    0 ≤ p*(1-p)/(k-1) ∧ p*(1-p)/(k-1) ≤ ε*p := by
  have hε : 0 ≤ ε := (by positivity : 0 ≤ 1/(k-1)).trans he
  constructor
  · exact div_nonneg (mul_nonneg hp (sub_nonneg.mpr hp1)) hk.le
  · calc
      p*(1-p)/(k-1) ≤ p/(k-1) := by
        apply div_le_div_of_nonneg_right _ hk.le
        nlinarith [sq_nonneg p]
      _ = p * (1/(k-1)) := by ring
      _ ≤ p*ε := mul_le_mul_of_nonneg_left he hp
      _ = _ := mul_comm _ _


-- @@ L418-432 verbatim
/-- The finite large-cell estimate before converting a to pair mass. -/
lemma signedCell_lower (B C : Finset P) (hB : 2 ≤ B.card) (ε : ℝ)
    (hk : 1 / ((B.card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε) :
    (cellProb B C - cellProb Finset.univ C)^2 -
      ε * (cellProb B C + cellProb Finset.univ C) ≤ signedCell B C := by
  have hkr : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
  have hnr : (2 : ℝ) ≤ Fintype.card P := by exact_mod_cast ambient_card_ge_two B hB
  have hp := correction_bound (cellProb B C) (B.card : ℝ) ε
    (cellProb_nonneg B C) (cellProb_le_one B C) (by linarith) hk
  have ha := correction_bound (cellProb Finset.univ C) (Fintype.card P : ℝ) ε
    (cellProb_nonneg _ C) (cellProb_le_one _ C) (by linarith) hn
  rw [signedCell_eq, signedCell_formula B C hB]
  have hc : 0 ≤ 2 * (B.card : ℝ) / Fintype.card P := by positivity
  nlinarith [mul_nonneg hc hp.1]


-- @@ L434-434 verbatim
section Family

-- @@ L435-435 verbatim
variable {I : Type u2} [Fintype I]

-- @@ L436-436 verbatim
variable (w : I → ℝ) (B : I → Finset P)


-- @@ L438-443 verbatim
lemma mean_cell_bound (C : Finset P) (M : ℝ)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x) :
    (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C := by
  simp_rw [← sum_prob_cell, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ => hdom x


-- @@ L445-472 verbatim
lemma family_large_raw (C : Finset P) (M ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1) (hε : 0 ≤ ε)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hmean : (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C) :
    (∑ i, w i * (cellProb (B i) C - cellProb Finset.univ C)^2) -
      ε*(M+1)*cellProb Finset.univ C ≤ (∑ i, w i * signedCell (B i) C) := by
  let a := cellProb Finset.univ C
  have ha : 0 ≤ a := cellProb_nonneg _ _
  have hc : (∑ i, w i * cellProb (B i) C) + (∑ i, w i)*a ≤ (M+1)*a := by
    have := mul_le_mul_of_nonneg_right hW ha
    dsimp [a] at *
    linarith
  calc
    _ ≤ (∑ i, w i * (cellProb (B i) C - a)^2) -
        ε*((∑ i, w i * cellProb (B i) C)+(∑ i, w i)*a) := by
      have := mul_le_mul_of_nonneg_left hc hε
      dsimp [a] at *
      nlinarith
    _ = ∑ i, w i * ((cellProb (B i) C - a)^2 - ε*(cellProb (B i) C+a)) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_mul]
      rw [sub_add_eq_sub_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (signedCell_lower (B i) C (hB i) ε (hk i) hn) (hw i)


-- @@ L474-493 verbatim
lemma family_large (C : Finset P) (M ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hτ : 0 < τ) (hC : 2 ≤ C.card) (ha : τ ≤ cellProb Finset.univ C)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hmean : (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C) :
    (∑ i, w i * (cellProb (B i) C - cellProb Finset.univ C)^2) -
      (2*ε*(M+1)/τ)*pairCell Finset.univ C ≤ (∑ i, w i * signedCell (B i) C) := by
  have hcomp := (uniform_pair_comparison C hC).1
  have ha0 := cellProb_nonneg (Finset.univ : Finset P) C
  have hmass : cellProb Finset.univ C ≤ 2*pairCell Finset.univ C/τ := by
    apply (le_div_iff₀ hτ).mpr
    nlinarith [mul_le_mul_of_nonneg_right ha ha0]
  have herr := mul_le_mul_of_nonneg_left hmass (show 0 ≤ ε*(M+1) by positivity)
  have h := family_large_raw w B C M ε hw hW hε hB hk hn hmean
  have he : ε*(M+1)*(2*pairCell Finset.univ C/τ) =
      (2*ε*(M+1)/τ)*pairCell Finset.univ C := by ring
  rw [he] at herr
  linarith


-- @@ L495-527 verbatim
lemma family_small (C : Finset P) (M : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hM : 0 ≤ M) (hC : 2 ≤ C.card)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hmean : (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C) :
    (1/2) * (∑ i, w i * (if 2 / ((B i).card : ℝ) ≤ cellProb (B i) C then
      (cellProb (B i) C)^2 else 0)) - 4*M*pairCell Finset.univ C ≤
      (∑ i, w i * signedCell (B i) C) := by
  let a := cellProb Finset.univ C
  have ha0 : 0 ≤ a := cellProb_nonneg _ _
  have hp0 := pairCell_nonneg (Finset.univ : Finset P) C
  have hc := (uniform_pair_comparison C hC).1
  have hterm (i : I) :
      (1/2)*(if 2 / ((B i).card : ℝ) ≤ cellProb (B i) C then
        (cellProb (B i) C)^2 else 0) - 2*a*cellProb (B i) C ≤ signedCell (B i) C := by
    have h₁ := fiber_pair_lower (B i) C (hB i)
    have h₂ := mixedCell_le_product (B i) C (hB i)
    dsimp [signedCell, a] at *
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hterm i) (hw i))
  have he : (∑ i, w i * ((1/2)*(if 2 / ((B i).card : ℝ) ≤ cellProb (B i) C then
        (cellProb (B i) C)^2 else 0) - 2*a*cellProb (B i) C)) =
      (1/2)*(∑ i, w i * (if 2 / ((B i).card : ℝ) ≤ cellProb (B i) C then
        (cellProb (B i) C)^2 else 0)) - 2*a*(∑ i, w i * cellProb (B i) C) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hs
  have hmean' := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2*a by positivity)
  have hcomp := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*M by positivity)
  dsimp [a] at *
  nlinarith


-- @@ L529-529 verbatim
end Family


-- @@ L531-546 verbatim
/-- Zero pair overlap is precisely an empty or singleton occurrence. -/
lemma zero_uniform_pair_iff (C : Finset P) :
    pairCell Finset.univ C = 0 ↔ C.card ≤ 1 := by
  refine ⟨?_, singleton_pairCell _ _⟩
  intro h
  by_contra! hc
  have hc2 : 2 ≤ C.card := hc
  have hn : 0 < (Fintype.card P : ℝ) := by
    exact_mod_cast (show 0 < Fintype.card P by have := Finset.card_le_univ C; omega)
  have hm : 0 < (C.card : ℝ) := by exact_mod_cast (by omega : 0 < C.card)
  have ha : 0 < cellProb Finset.univ C := by
    simpa only [cellProb, Finset.univ_inter, Finset.card_univ] using div_pos hm hn
  have hh := (uniform_pair_comparison C hc2).1
  rw [h] at hh
  have : 0 < (1/2 : ℝ)*(cellProb Finset.univ C)^2 := by positivity
  linarith


-- @@ L548-548 verbatim
section CellIntegral

-- @@ L549-551 verbatim
variable {Ω : Type u3} [MeasurableSpace Ω]
-- A finite set of vertex labels is discrete. No condition is imposed on the
-- underlying cell-occurrence measure, which may have infinite singleton tails.

-- @@ L552-552 verbatim
local instance : MeasurableSpace (Finset P) := ⊤

-- @@ L553-553 verbatim
local instance : DiscreteMeasurableSpace (Finset P) := ⟨fun _ => trivial⟩


-- @@ L555-568 verbatim
private lemma finite_weighted_bound {T : Type u4} [Fintype T]
    (f q : T → ℝ) (hq : ∀ t, 0 ≤ q t) (hf : ∀ t, q t = 0 → f t = 0) :
    ∃ K : ℝ, ∀ t, |f t| ≤ K*q t := by
  classical
  refine ⟨∑ t, |f t / q t|, ?_⟩
  intro t
  by_cases ht : q t = 0
  · simp [ht, hf t ht]
  · calc
      |f t| = |f t / q t| * q t := by
        rw [abs_div, abs_of_nonneg (hq t), div_mul_cancel₀ _ ht]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (s := Finset.univ) (f := fun t => |f t / q t|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ t)) (hq t)


-- @@ L570-579 verbatim
/-- The only integrability input needed for any fixed finite cell function
    vanishing on singletons is integrability of the off-diagonal pair mass. -/
lemma integrable_cell_function (C : Ω → Finset P) (μ : Measure Ω)
    (hC : Measurable C) (hq : Integrable (fun ω => pairCell Finset.univ (C ω)) μ)
    (f : Finset P → ℝ) (hf : ∀ D, D.card ≤ 1 → f D = 0) :
    Integrable (fun ω => f (C ω)) μ := by
  obtain ⟨K,hK⟩ := finite_weighted_bound f (pairCell Finset.univ)
    (pairCell_nonneg _) (fun D hd => hf D ((zero_uniform_pair_iff D).mp hd))
  apply (hq.const_mul K).mono' ((measurable_of_finite f).comp hC).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hK (C ω)


-- @@ L581-582 verbatim
def offDiagonalCell (C : Finset P) (x y : P) : ℝ :=
  if x ≠ y ∧ x ∈ C ∧ y ∈ C then 1 else 0


-- @@ L584-590 verbatim
omit [Fintype P] in
lemma offDiagonalCell_singleton (C : Finset P) (x y : P) (hC : C.card ≤ 1) :
    offDiagonalCell C x y = 0 := by
  unfold offDiagonalCell
  split_ifs with h
  · exact False.elim (h.1 (Finset.card_le_one.mp hC x h.2.1 y h.2.2))
  · rfl


-- @@ L592-593 verbatim
def overlap (C : Ω → Finset P) (μ : Measure Ω) (x y : P) : ℝ :=
  ∫ ω, offDiagonalCell (C ω) x y ∂μ


-- @@ L595-602 verbatim
lemma cell_sum_eq (H : P → P → ℝ) (hdiag : ∀ x, H x x = 0) (C : Finset P) :
    (∑ x ∈ C, ∑ y ∈ C, H x y) = ∑ x, ∑ y, H x y * offDiagonalCell C x y := by
  have he (x y : P) : H x y * offDiagonalCell C x y =
      if x ∈ C then if y ∈ C then H x y else 0 else 0 := by
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> by_cases hxy : x = y
    all_goals simp_all [offDiagonalCell]
  simp_rw [he]
  simp


-- @@ L604-622 verbatim
lemma integral_signedCell (C : Ω → Finset P) (μ : Measure Ω)
    (hC : Measurable C) (hq : Integrable (fun ω => pairCell Finset.univ (C ω)) μ)
    (B : Finset P) :
    (∫ ω, signedCell B (C ω) ∂μ) = ∑ x, ∑ y, signedPair B x y * overlap C μ x y := by
  have hi (x y : P) : Integrable (fun ω => signedPair B x y * offDiagonalCell (C ω) x y) μ :=
    (integrable_cell_function C μ hC hq (fun D => offDiagonalCell D x y)
      (fun D hD => offDiagonalCell_singleton D x y hD)).const_mul _
  calc
    _ = ∫ ω, ∑ x, ∑ y, signedPair B x y * offDiagonalCell (C ω) x y ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change signedCell B (C ω) = _
        rw [signedCell_eq, cell_sum_eq _ (signedPair_diag B)]
    _ = ∑ x, ∑ y, ∫ ω, signedPair B x y * offDiagonalCell (C ω) x y ∂μ := by
      rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
      apply Finset.sum_congr rfl
      intro x _
      exact integral_finsetSum _ (fun y _ => hi x y)
    _ = _ := by simp only [overlap, integral_const_mul]


-- @@ L624-631 verbatim
lemma integrated_cancel (C : Ω → Finset P) (μ : Measure Ω)
    (hC : Measurable C) (hq : Integrable (fun ω => pairCell Finset.univ (C ω)) μ)
    (b : ℝ) (S : P → ℝ)
    (hL : ∀ x y, x ≠ y → overlap C μ x y = b + S x + S y)
    (B : Finset P) (hB : 2 ≤ B.card) :
    (∫ ω, signedCell B (C ω) ∂μ) = 0 := by
  rw [integral_signedCell C μ hC hq]
  exact variance_cancel B hB _ b S hL


-- @@ L633-633 verbatim
section Quantitative

-- @@ L634-634 verbatim
variable {I : Type u5} [Fintype I]


-- @@ L636-640 verbatim
def varianceCell (w : I → ℝ) (B : I → Finset P) (T : ℝ) (D : Finset P) : ℝ :=
  if T < D.card then
    ∑ i, w i * (cellProb (B i) D - cellProb Finset.univ D)^2
  else (1/2) * ∑ i, w i *
    (if 2 / ((B i).card : ℝ) ≤ cellProb (B i) D then (cellProb (B i) D)^2 else 0)


-- @@ L642-646 verbatim
lemma varianceCell_singleton (w : I → ℝ) (B : I → Finset P) (T : ℝ)
    (hT : 1 ≤ T) (hB : ∀ i, 2 ≤ (B i).card) (D : Finset P) (hD : D.card ≤ 1) :
    varianceCell w B T D = 0 := by
  have hd : (D.card : ℝ) ≤ T := (by exact_mod_cast hD : (D.card : ℝ) ≤ 1).trans hT
  simp [varianceCell, not_lt.mpr hd, singleton_fiber_term _ _ (hB _) hD]


-- @@ L648-682 verbatim
lemma varianceCell_bound (w : I → ℝ) (B : I → Finset P) (T M ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1)
    (hT : 1 ≤ T) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hscale : τ * Fintype.card P ≤ T)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x)
    (D : Finset P) :
    varianceCell w B T D ≤ (∑ i, w i * signedCell (B i) D) +
      (2*ε*(M+1)/τ)*pairCell Finset.univ D +
      4*M*(if (D.card : ℝ) ≤ T then pairCell Finset.univ D else 0) := by
  have hmean := mean_cell_bound w B D M hdom
  have herr : 0 ≤ (2*ε*(M+1)/τ)*pairCell Finset.univ D := by
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε)
      (by linarith)) hτ.le) (pairCell_nonneg _ _)
  by_cases hD : T < (D.card : ℝ)
  · have hd2 : 2 ≤ D.card := by
      have : (1 : ℝ) < D.card := hT.trans_lt hD
      exact_mod_cast (show 1 < D.card by exact_mod_cast this)
    have hnp : 0 < (Fintype.card P : ℝ) := by
      exact_mod_cast (show 0 < Fintype.card P by have := Finset.card_le_univ D; omega)
    have ha : τ ≤ cellProb Finset.univ D := by
      simp only [cellProb, Finset.univ_inter, Finset.card_univ]
      exact (le_div_iff₀ hnp).mpr (hscale.trans hD.le)
    have hh := family_large w B D M ε τ hw hW hM hε hτ hd2 ha hB hk hn hmean
    simp only [varianceCell, hD, reduceIte, not_le.mpr hD, mul_zero, add_zero]
    linarith
  · simp only [varianceCell, hD, reduceIte, not_lt.mp hD]
    by_cases hd2 : 2 ≤ D.card
    · have hh := family_small w B D M hw hM hd2 hB hmean
      linarith
    · have hd1 : D.card ≤ 1 := by omega
      simp [singleton_fiber_term _ _ (hB _) hd1, singleton_signedCell _ _ hd1,
        singleton_pairCell _ _ hd1]


-- @@ L684-726 verbatim
/-- The integrated off-diagonal variance estimate before specializing the
    threshold and denominator errors to powers of n. The pair overlap may
    have infinite singleton tails; no diagonal integral is used. -/
theorem integrated_variance (C : Ω → Finset P) (μ : Measure Ω)
    (hC : Measurable C) (hq : Integrable (fun ω => pairCell Finset.univ (C ω)) μ)
    (b : ℝ) (S : P → ℝ)
    (hL : ∀ x y, x ≠ y → overlap C μ x y = b + S x + S y)
    (w : I → ℝ) (B : I → Finset P) (T M ε τ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : (∑ i, w i) ≤ 1)
    (hT : 1 ≤ T) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hτ : 0 < τ)
    (hscale : τ * Fintype.card P ≤ T)
    (hB : ∀ i, 2 ≤ (B i).card)
    (hk : ∀ i, 1 / (((B i).card : ℝ)-1) ≤ ε)
    (hn : 1 / ((Fintype.card P : ℝ)-1) ≤ ε)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x) :
    (∫ ω, varianceCell w B T (C ω) ∂μ) ≤
      (2*ε*(M+1)/τ)*(∫ ω, pairCell Finset.univ (C ω) ∂μ) +
      4*M*(∫ ω, if ((C ω).card : ℝ) ≤ T then pairCell Finset.univ (C ω) else 0 ∂μ) := by
  have hv : Integrable (fun ω => varianceCell w B T (C ω)) μ :=
    integrable_cell_function C μ hC hq _ (varianceCell_singleton w B T hT hB)
  have hs (i : I) : Integrable (fun ω => signedCell (B i) (C ω)) μ :=
    integrable_cell_function C μ hC hq _ (singleton_signedCell _)
  have hsmall : Integrable (fun ω =>
      if ((C ω).card : ℝ) ≤ T then pairCell Finset.univ (C ω) else 0) μ := by
    apply integrable_cell_function C μ hC hq
      (fun D => if (D.card : ℝ) ≤ T then pairCell Finset.univ D else 0)
    intro D hD
    simp [singleton_pairCell _ _ hD]
  have hsum : Integrable (fun ω => ∑ i, w i * signedCell (B i) (C ω)) μ :=
    integrable_finsetSum _ fun i _ => (hs i).const_mul _
  have hzero : (∫ ω, ∑ i, w i * signedCell (B i) (C ω) ∂μ) = 0 := by
    rw [integral_finsetSum _ fun i _ => (hs i).const_mul _]
    simp only [integral_const_mul,
      integrated_cancel C μ hC hq b S hL _ (hB _), mul_zero, Finset.sum_const_zero]
  have hh := integral_mono hv
    ((hsum.add (hq.const_mul _)).add (hsmall.const_mul _))
    (fun ω => varianceCell_bound w B T M ε τ hw hW hT hM hε hτ hscale hB hk hn hdom (C ω))
  simp only [Pi.add_apply] at hh
  have h₁ := integral_add (hsum.add (hq.const_mul (2*ε*(M+1)/τ))) (hsmall.const_mul (4*M))
  have h₂ := integral_add hsum (hq.const_mul (2*ε*(M+1)/τ))
  simp only [Pi.add_apply] at h₁ h₂
  rw [h₁, h₂, hzero, zero_add, integral_const_mul, integral_const_mul] at hh
  exact hh


-- @@ L728-728 verbatim
end Quantitative


-- @@ L730-730 verbatim
end CellIntegral


-- @@ L732-732 verbatim
end WeakPinned.Variance


-- @@ L734-734 verbatim
end

-- @@ L735-735 verbatim
end

-- @@ L736-736 verbatim
end

-- @@ L737-737 verbatim
end

-- @@ L738-738 verbatim
end

-- @@ L739-739 verbatim
end


-- @@ L741-741 verbatim
end OAI
