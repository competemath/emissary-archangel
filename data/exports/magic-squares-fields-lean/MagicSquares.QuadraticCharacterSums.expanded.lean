import MagicSquares.QuadraticCharacter
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.GroupWithZero.Units.Equiv


-- @@ L5-5 verbatim
namespace MagicSquares


-- @@ L7-7 verbatim
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


-- @@ L9-9 verbatim
local notation "χ" => quadraticChar F


-- @@ L11-18 verbatim
/-- Lemma 5.4: translating the argument of the quadratic character does not
change its complete sum. -/
theorem quadraticChar_linear_shift_sum (hodd : ringChar F ≠ 2) (a : F) :
    ∑ x : F, χ (x - a) = 0 := by
  calc
    ∑ x : F, χ (x - a) = ∑ x : F, χ x := by
      simpa using (Equiv.subRight a).sum_comp (fun x : F => χ x)
    _ = 0 := quadraticChar_sum_zero hodd


-- @@ L20-26 verbatim
/-- For the quadratic character, the Jacobi sum `J(χ,χ)` is `-χ(-1)`.
This is already contained in mathlib's Jacobi-sum API. -/
theorem quadraticChar_jacobi_self (hodd : ringChar F ≠ 2) :
    jacobiSum χ χ = -χ (-1) := by
  have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hodd)
  rw [(quadraticChar_isQuadratic F).inv] at h
  exact h


-- @@ L28-54 verbatim
/-- Standardized form of Lemma 5.5:
`Σ_y χ(y(y-1)) = -1` over a finite field of odd characteristic. -/
theorem quadraticChar_y_mul_y_sub_one_sum (hodd : ringChar F ≠ 2) :
    ∑ y : F, χ (y * (y - 1)) = -1 := by
  have hJ : jacobiSum χ χ = -χ (-1) := quadraticChar_jacobi_self hodd
  have hneg_sq : χ (-1 : F) ^ 2 = 1 := by
    exact quadraticChar_sq_one (by simp)
  calc
    ∑ y : F, χ (y * (y - 1))
        = ∑ y : F, χ y * χ (y - 1) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [map_mul]
    _ = χ (-1 : F) * ∑ y : F, χ y * χ (1 - y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          have hsub : y - 1 = (-1 : F) * (1 - y) := by ring
          rw [hsub, map_mul]
          ring
    _ = χ (-1 : F) * jacobiSum χ χ := by
          rfl
    _ = -1 := by
          rw [hJ]
          calc
            χ (-1 : F) * -χ (-1 : F) = -(χ (-1 : F) ^ 2) := by ring
            _ = -1 := by rw [hneg_sq]


-- @@ L56-83 verbatim
/-- Lemma 5.5 in the form used in the paper.  The proof reduces an arbitrary
pair of distinct roots to the standardized Jacobi sum by the affine change of
variables `x = a + (b-a)y`. -/
theorem quadraticChar_two_root_sum (hodd : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ x : F, χ ((x - a) * (x - b)) = -1 := by
  let d : F := b - a
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr (Ne.symm hab)
  let e : F ≃ F := (Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a)
  have he_apply (y : F) : e y = a + d * y := by
    simp [e]
  have hsq : χ (d ^ 2) = 1 := quadraticChar_sq_one' hd
  calc
    ∑ x : F, χ ((x - a) * (x - b))
        = ∑ y : F, χ ((e y - a) * (e y - b)) := by
            simpa using ((e.sum_comp (fun x : F => χ ((x - a) * (x - b)))).symm)
    _ = ∑ y : F, χ (y * (y - 1)) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [he_apply]
          have hprod :
              (a + d * y - a) * (a + d * y - b) = d ^ 2 * (y * (y - 1)) := by
            dsimp [d]
            ring
          rw [hprod, map_mul, hsq]
          simp
    _ = -1 := quadraticChar_y_mul_y_sub_one_sum hodd


-- @@ L85-85 verbatim
end MagicSquares
