import MagicSquares.CenterZero.Squares

-- @@ L2-2 verbatim
namespace MagicSquares


-- @@ L4-4 verbatim
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


-- @@ L6-6 verbatim
local notation "χ" => quadraticChar F


-- @@ L8-13 verbatim
/-- The seven exceptional parameter values in the center-zero family from
Section 6 of the paper. A list is used before `toFinset` so the cardinality
bound `≤ 7` does not require proving that these values remain distinct in every
odd characteristic. -/
def centerZeroBadValues : Finset F :=
  [(-2 : F), (-1 : F), (-1 : F) / 2, 0, (1 : F) / 2, 1, 2].toFinset


-- @@ L15-20 verbatim
omit [Fintype F] in
@[simp] theorem mem_centerZeroBadValues (x : F) :
    x ∈ (centerZeroBadValues : Finset F) ↔
      x = -2 ∨ x = -1 ∨ x = (-1 : F) / 2 ∨ x = 0 ∨
      x = (1 : F) / 2 ∨ x = 1 ∨ x = 2 := by
  simp [centerZeroBadValues]


-- @@ L22-29 verbatim
omit [Fintype F] in
/-- There are at most seven exceptional values. In small characteristics
some of them can coincide, which only makes this estimate stronger. -/
theorem centerZeroBadValues_card_le :
    (centerZeroBadValues : Finset F).card ≤ 7 := by
  simpa [centerZeroBadValues] using
    (List.toFinset_card_le
      [(-2 : F), (-1 : F), (-1 : F) / 2, 0, (1 : F) / 2, 1, 2])


-- @@ L31-39 verbatim
omit [Fintype F] [DecidableEq F] in
/-- In odd characteristic, two is nonzero. -/
private theorem two_ne_zero_of_ringChar_ne_two
    (hodd : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro htwo
  apply Ring.neg_one_ne_one_of_char_ne_two hodd
  calc
    (-1 : F) = 1 - 2 := by ring
    _ = 1 := by rw [htwo]; ring


-- @@ L41-41 verbatim
set_option maxHeartbeats 0


-- @@ L43-256 verbatim
omit [Fintype F] in
/-- A collision among two distinct entries of `M₀(x)` forces `x` to be one
of the seven exceptional values listed in Section 6. This version proves
the 36 unordered entry inequalities explicitly, avoiding tactic search over
the seven exceptional values. -/
theorem centerZero_pairwiseDistinct_of_not_mem_bad
    (hodd : ringChar F ≠ 2)
    {x : F}
    (hxgood : x ∉ (centerZeroBadValues : Finset F)) :
    (Square3.centerZero x).PairwiseDistinct := by
  have htwo : (2 : F) ≠ 0 := two_ne_zero_of_ringChar_ne_two (F := F) hodd
  have hnegone : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hodd
  have hgood :
      x ≠ -2 ∧ x ≠ -1 ∧ x ≠ (-1 : F) / 2 ∧ x ≠ 0 ∧
      x ≠ (1 : F) / 2 ∧ x ≠ 1 ∧ x ≠ 2 := by
    simpa [mem_centerZeroBadValues] using hxgood
  rcases hgood with ⟨hneg2, hneg1, hnegHalf, hzero, hhalf, hone, htwoVal⟩

  have eq_neg_half_of_two_mul_eq_neg_one {y : F}
      (h : (2 : F) * y = -1) : y = (-1 : F) / 2 := by
    apply (eq_div_iff htwo).2
    linear_combination h

  have eq_half_of_two_mul_eq_one {y : F}
      (h : (2 : F) * y = 1) : y = (1 : F) / 2 := by
    apply (eq_div_iff htwo).2
    linear_combination h

  have eq_zero_of_two_mul_eq_zero {y : F}
      (h : (2 : F) * y = 0) : y = 0 := by
    exact (mul_eq_zero.mp h).resolve_left htwo

  have eq_neg_one_of_two_mul_eq_neg_two {y : F}
      (h : (2 : F) * y = -2) : y = -1 := by
    apply mul_left_cancel₀ htwo
    linear_combination h

  have eq_one_of_two_mul_eq_two {y : F}
      (h : (2 : F) * y = 2) : y = 1 := by
    apply mul_left_cancel₀ htwo
    linear_combination h

  -- Entries, in order:
  -- e0=x, e1=-x-1, e2=1, e3=1-x, e4=0,
  -- e5=x-1, e6=-1, e7=x+1, e8=-x.

  have h01 : x ≠ -x - 1 := by
    intro h
    apply hnegHalf
    apply eq_neg_half_of_two_mul_eq_neg_one
    linear_combination h
  have h02 : x ≠ (1 : F) := hone
  have h03 : x ≠ 1 - x := by
    intro h
    apply hhalf
    apply eq_half_of_two_mul_eq_one
    linear_combination h
  have h04 : x ≠ 0 := hzero
  have h05 : x ≠ x - 1 := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination h
  have h06 : x ≠ -1 := hneg1
  have h07 : x ≠ x + 1 := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination (-1) * h
  have h08 : x ≠ -x := by
    intro h
    apply hzero
    apply eq_zero_of_two_mul_eq_zero
    linear_combination h

  have h12 : -x - 1 ≠ (1 : F) := by
    intro h
    apply hneg2
    linear_combination (-1) * h
  have h13 : -x - 1 ≠ 1 - x := by
    intro h
    apply htwo
    linear_combination (-1) * h
  have h14 : -x - 1 ≠ 0 := by
    intro h
    apply hneg1
    linear_combination (-1) * h
  have h15 : -x - 1 ≠ x - 1 := by
    intro h
    apply hzero
    apply eq_zero_of_two_mul_eq_zero
    linear_combination (-1) * h
  have h16 : -x - 1 ≠ -1 := by
    intro h
    apply hzero
    linear_combination (-1) * h
  have h17 : -x - 1 ≠ x + 1 := by
    intro h
    apply hneg1
    apply eq_neg_one_of_two_mul_eq_neg_two
    linear_combination (-1) * h
  have h18 : -x - 1 ≠ -x := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination (-1) * h

  have h23 : (1 : F) ≠ 1 - x := by
    intro h
    apply hzero
    linear_combination h
  have h24 : (1 : F) ≠ 0 := one_ne_zero
  have h25 : (1 : F) ≠ x - 1 := by
    intro h
    apply htwoVal
    linear_combination (-1) * h
  have h26 : (1 : F) ≠ -1 := Ne.symm hnegone
  have h27 : (1 : F) ≠ x + 1 := by
    intro h
    apply hzero
    linear_combination (-1) * h
  have h28 : (1 : F) ≠ -x := by
    intro h
    apply hneg1
    linear_combination h

  have h34 : 1 - x ≠ (0 : F) := by
    intro h
    apply hone
    linear_combination (-1) * h
  have h35 : 1 - x ≠ x - 1 := by
    intro h
    apply hone
    apply eq_one_of_two_mul_eq_two
    linear_combination (-1) * h
  have h36 : 1 - x ≠ (-1 : F) := by
    intro h
    apply htwoVal
    linear_combination (-1) * h
  have h37 : 1 - x ≠ x + 1 := by
    intro h
    apply hzero
    apply eq_zero_of_two_mul_eq_zero
    linear_combination (-1) * h
  have h38 : 1 - x ≠ -x := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination h

  have h45 : (0 : F) ≠ x - 1 := by
    intro h
    apply hone
    linear_combination (-1) * h
  have h46 : (0 : F) ≠ -1 := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination h
  have h47 : (0 : F) ≠ x + 1 := by
    intro h
    apply hneg1
    linear_combination (-1) * h
  have h48 : (0 : F) ≠ -x := by
    intro h
    apply hzero
    linear_combination h

  have h56 : x - 1 ≠ (-1 : F) := by
    intro h
    apply hzero
    linear_combination h
  have h57 : x - 1 ≠ x + 1 := by
    intro h
    apply htwo
    linear_combination (-1) * h
  have h58 : x - 1 ≠ -x := by
    intro h
    apply hhalf
    apply eq_half_of_two_mul_eq_one
    linear_combination h

  have h67 : (-1 : F) ≠ x + 1 := by
    intro h
    apply hneg2
    linear_combination (-1) * h
  have h68 : (-1 : F) ≠ -x := by
    intro h
    apply hone
    linear_combination h

  have h78 : x + 1 ≠ -x := by
    intro h
    apply hnegHalf
    apply eq_neg_half_of_two_mul_eq_neg_one
    linear_combination h

  -- Package the nine entries as a concrete list.  Proving that this list has
  -- no duplicates is much cheaper than expanding all 81 pairs of indices.
  let L : List F :=
    [x, -x - 1, 1, 1 - x, 0, x - 1, -1, x + 1, -x]

  have hLnodup : L.Nodup := by
    dsimp [L]
    simp [h01, h02, h03, h04, h05, h06, h07, h08,
      h12, h13, h14, h15, h16, h17, h18,
      h23, h24, h25, h26, h27, h28,
      h34, h35, h36, h37, h38,
      h45, h46, h47, h48,
      h56, h57, h58, h67, h68, h78]

  have hentries :
      (Square3.centerZero x).entries = L.get := by
    funext i
    fin_cases i <;> simp [Square3.entries, L]

  change Function.Injective (Square3.centerZero x).entries
  rw [hentries]
  exact hLnodup.injective_get


-- @@ L258-269 verbatim
/-- Each factor `1 + χ(y)` is one of `0,1,2`. -/
theorem one_add_quadraticChar_cases (y : F) :
    1 + χ y = 0 ∨ 1 + χ y = 1 ∨ 1 + χ y = 2 := by
  by_cases hy : y = 0
  · subst y
    simp
  · rcases quadraticChar_dichotomy hy with h | h
    · right
      right
      simp [h]
    · left
      simp [h]


-- @@ L271-280 verbatim
/-- Hence the unnormalized center-zero indicator has values between `0` and
`8`. -/
theorem centerZeroWeight_bounds (x : F) :
    0 ≤ centerZeroWeight x ∧ centerZeroWeight x ≤ 8 := by
  rcases one_add_quadraticChar_cases (F := F) (x - 1) with h1 | h1 | h1 <;>
  rcases one_add_quadraticChar_cases (F := F) x with h2 | h2 | h2 <;>
  rcases one_add_quadraticChar_cases (F := F) (x + 1) with h3 | h3 | h3 <;>
  change 0 ≤ (1 + χ (x - 1)) * (1 + χ x) * (1 + χ (x + 1)) ∧
    (1 + χ (x - 1)) * (1 + χ x) * (1 + χ (x + 1)) ≤ 8 <;>
  rw [h1, h2, h3] <;> norm_num


-- @@ L282-322 verbatim
/-- If the total weight is greater than `7·8 = 56`, then some nonzero-weight
parameter lies outside the seven exceptional values. -/
theorem exists_good_centerZero_parameter_of_sum_gt_56
    (hsum : 56 < ((∑ x : F, centerZeroWeight x : ℤ) : ℝ)) :
    ∃ x : F, x ∉ (centerZeroBadValues : Finset F) ∧ centerZeroWeight x ≠ 0 := by
  by_contra h
  push Not at h
  have hout : ∀ x : F, x ∉ (centerZeroBadValues : Finset F) → centerZeroWeight x = 0 := by
    intro x hx
    exact h x hx

  have hsum_eq :
      ∑ x : F, centerZeroWeight x =
        ∑ x ∈ (centerZeroBadValues : Finset F), centerZeroWeight x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x hxuniv hxnot
    exact hout x hxnot

  have hbad_sum :
      (∑ x ∈ (centerZeroBadValues : Finset F), centerZeroWeight x) ≤
        (centerZeroBadValues : Finset F).card • (8 : ℤ) := by
    exact Finset.sum_le_card_nsmul _ _ _
      (fun x hx => (centerZeroWeight_bounds (F := F) x).2)

  have hcard := centerZeroBadValues_card_le (F := F)
  have hcardZ : ((centerZeroBadValues : Finset F).card : ℤ) ≤ 7 := by
    exact_mod_cast hcard
  have hbad_sum' :
      (∑ x ∈ (centerZeroBadValues : Finset F), centerZeroWeight x) ≤ 56 := by
    have hbad_sum_cast :
        (∑ x ∈ (centerZeroBadValues : Finset F), centerZeroWeight x) ≤
          ((centerZeroBadValues : Finset F).card : ℤ) * 8 := by
      simpa [nsmul_eq_mul] using hbad_sum
    nlinarith
  have htotalZ : (∑ x : F, centerZeroWeight x) ≤ 56 := by
    rw [hsum_eq]
    exact hbad_sum'
  have htotalR : ((∑ x : F, centerZeroWeight x : ℤ) : ℝ) ≤ 56 := by
    exact_mod_cast htotalZ
  linarith


-- @@ L324-351 verbatim
/-- Section 6, with the single cubic Weil estimate still explicit as a
hypothesis: if `q ≥ 77` and `-1` is a square, the center-zero family contains
a distinct magic square of squares. -/
theorem exists_centerZero_magic_of_squares_of_card_ge_77
    (hodd : ringChar F ≠ 2)
    (hneg : IsSquare (-1 : F))
    (hWeil : HasCenterZeroCubicWeilBound F)
    (hq : 77 ≤ Fintype.card F) :
    ∃ M : Square3 F, IsMagicOfPowers 2 M := by
  have hsum := centerZeroWeight_sum_gt_56 (F := F) hodd hWeil hq
  obtain ⟨x, hxgood, hw⟩ :=
    exists_good_centerZero_parameter_of_sum_gt_56 (F := F) hsum

  have hdistinct : (Square3.centerZero x).PairwiseDistinct :=
    centerZero_pairwiseDistinct_of_not_mem_bad (F := F) hodd hxgood

  have hgood :
      x ≠ -2 ∧ x ≠ -1 ∧ x ≠ (-1 : F) / 2 ∧ x ≠ 0 ∧
      x ≠ (1 : F) / 2 ∧ x ≠ 1 ∧ x ≠ 2 := by
    simpa [mem_centerZeroBadValues] using hxgood
  rcases hgood with ⟨_, hxneg1, _, hx0, _, hx1, _⟩

  obtain ⟨hxm, hx, hxp⟩ :=
    centerZeroWeight_ne_zero_forces_squares (F := F) x hx1 hx0 hxneg1 hw
  have hpowers := centerZero_all_entries_are_squares (F := F) x hneg hxm hx hxp

  refine ⟨Square3.centerZero x, ?_, hdistinct, hpowers⟩
  exact Square3.centerZero_isMagic x


-- @@ L353-364 verbatim
/-- The paper's congruence formulation of the preceding theorem. -/
theorem exists_centerZero_magic_of_squares_of_card_mod_four_one
    (hodd : ringChar F ≠ 2)
    (hWeil : HasCenterZeroCubicWeilBound F)
    (hq : 77 ≤ Fintype.card F)
    (hqmod : Fintype.card F % 4 = 1) :
    ∃ M : Square3 F, IsMagicOfPowers 2 M := by
  have hneg : IsSquare (-1 : F) := by
    apply (neg_one_isSquare_iff_card_mod_four_ne_three (F := F)).2
    omega
  exact exists_centerZero_magic_of_squares_of_card_ge_77
    (F := F) hodd hneg hWeil hq


-- @@ L366-366 verbatim
end MagicSquares
