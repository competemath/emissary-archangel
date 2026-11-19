import MagicSquares.WeilInterface
import MagicSquares.Bounds


-- @@ L4-4 verbatim
namespace MagicSquares


-- @@ L6-6 verbatim
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


-- @@ L8-8 verbatim
local notation "χ" => quadraticChar F


-- @@ L10-15 verbatim
/-- The integer-valued numerator of the indicator used in Section 6.
Dividing this by `8` gives the paper's `I(x)`.  Keeping the numerator
integral avoids unnecessary rational/real coercions during the character-sum
expansion. -/
def centerZeroWeight (x : F) : ℤ :=
  (1 + χ (x - 1)) * (1 + χ x) * (1 + χ (x + 1))


-- @@ L17-26 verbatim
/-- Pointwise expansion of the Section 6 indicator numerator. -/
theorem centerZeroWeight_expand (x : F) :
    centerZeroWeight x =
      1 + χ (x - 1) + χ x + χ (x + 1) +
      χ ((x - 1) * x) +
      χ ((x - 1) * (x + 1)) +
      χ (x * (x + 1)) +
      χ ((x - 1) * x * (x + 1)) := by
  simp only [centerZeroWeight, map_mul]
  ring


-- @@ L28-76 verbatim
/-- Exact evaluation of all non-cubic terms in the Section 6 expansion:

`Σ_x W(x) = q - 3 + Σ_x χ((x-1)x(x+1))`.

This is the formal counterpart of the calculation on pp. 8--9 of the paper.
The three quadratic sums are discharged by `quadraticChar_two_root_sum`. -/
theorem centerZeroWeight_sum_identity (hodd : ringChar F ≠ 2) :
    ∑ x : F, centerZeroWeight x =
      (Fintype.card F : ℤ) - 3 +
        ∑ x : F, χ ((x - 1) * x * (x + 1)) := by
  have hlin1 : ∑ x : F, χ (x - 1) = 0 :=
    quadraticChar_linear_shift_sum hodd 1
  have hlin0 : ∑ x : F, χ x = 0 := quadraticChar_sum_zero hodd
  have hlinm1 : ∑ x : F, χ (x + 1) = 0 := by
    simpa [sub_neg_eq_add] using quadraticChar_linear_shift_sum (F := F) hodd (-1)

  have hq10 : ∑ x : F, χ ((x - 1) * x) = -1 := by
    simpa using quadraticChar_two_root_sum (F := F) hodd (a := (1 : F)) (b := 0) one_ne_zero

  have h1m1 : (1 : F) ≠ -1 := by
    exact Ne.symm (Ring.neg_one_ne_one_of_char_ne_two hodd)
  have hq1m1 : ∑ x : F, χ ((x - 1) * (x + 1)) = -1 := by
    simpa [sub_neg_eq_add] using
      quadraticChar_two_root_sum (F := F) hodd (a := (1 : F)) (b := (-1 : F)) h1m1

  have hq0m1 : ∑ x : F, χ (x * (x + 1)) = -1 := by
    have h0m1 : (0 : F) ≠ -1 := by simp
    simpa [sub_neg_eq_add] using
      quadraticChar_two_root_sum (F := F) hodd (a := (0 : F)) (b := (-1 : F)) h0m1

  calc
    ∑ x : F, centerZeroWeight x
        = ∑ x : F,
            (1 + χ (x - 1) + χ x + χ (x + 1) +
              χ ((x - 1) * x) +
              χ ((x - 1) * (x + 1)) +
              χ (x * (x + 1)) +
              χ ((x - 1) * x * (x + 1))) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact centerZeroWeight_expand x
    _ = (Fintype.card F : ℤ) - 3 +
          ∑ x : F, χ ((x - 1) * x * (x + 1)) := by
          simp only [Finset.sum_add_distrib]
          rw [hlin1, hlin0, hlinm1, hq10, hq1m1, hq0m1]
          have hconst : (∑ _x : F, (1 : ℤ)) = (Fintype.card F : ℤ) := by
            simp
          rw [hconst]
          ring


-- @@ L78-103 verbatim
/-- Applying only the cubic Weil interface gives the lower bound used in
Section 6.  Everything in this theorem except the explicit hypothesis `hWeil`
is elementary/mathlib character theory. -/
theorem centerZeroWeight_sum_lower_bound
    (hodd : ringChar F ≠ 2)
    (hWeil : HasCenterZeroCubicWeilBound F) :
    (Fintype.card F : ℝ) - 3 - 2 * Real.sqrt (Fintype.card F : ℝ)
      ≤ ((∑ x : F, centerZeroWeight x : ℤ) : ℝ) := by
  have hidR :
      ((∑ x : F, centerZeroWeight x : ℤ) : ℝ) =
        (Fintype.card F : ℝ) - 3 +
          ((∑ x : F, χ ((x - 1) * x * (x + 1)) : ℤ) : ℝ) := by
    norm_cast
    exact centerZeroWeight_sum_identity (F := F) hodd
  have hTlower :
      -(2 * Real.sqrt (Fintype.card F : ℝ)) ≤
        ((∑ x : F, χ ((x - 1) * x * (x + 1)) : ℤ) : ℝ) :=
    (abs_le.mp hWeil).1
  rw [hidR]
  calc
    (Fintype.card F : ℝ) - 3 - 2 * Real.sqrt (Fintype.card F : ℝ)
        = ((Fintype.card F : ℝ) - 3) +
            (-(2 * Real.sqrt (Fintype.card F : ℝ))) := by ring
    _ ≤ ((Fintype.card F : ℝ) - 3) +
          ((∑ x : F, χ ((x - 1) * x * (x + 1)) : ℤ) : ℝ) := by
      linarith


-- @@ L105-115 verbatim
/-- Thus the unnormalized indicator sum is already larger than `56 = 7*8`
whenever `q ≥ 77`.  The only remaining Section 6 step is the finite
seven-bad-values/distinctness argument. -/
theorem centerZeroWeight_sum_gt_56
    (hodd : ringChar F ≠ 2)
    (hWeil : HasCenterZeroCubicWeilBound F)
    (hq : 77 ≤ Fintype.card F) :
    56 < ((∑ x : F, centerZeroWeight x : ℤ) : ℝ) := by
  have hnum := centerZero_numeric_bound hq
  have hlower := centerZeroWeight_sum_lower_bound (F := F) hodd hWeil
  linarith


-- @@ L117-117 verbatim
end MagicSquares
