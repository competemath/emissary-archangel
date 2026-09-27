/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Mathlib.Topology.UnitInterval


-- @@ L10-12 verbatim
/-!
# LeanPool.DirectedTopologyLean4.Fraction
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
open scoped unitInterval

-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-27 verbatim
/-- For any natural numbers `i n : ℕ` such that `n` is positive and `i ≤ n`, we have that the
fraction
`i/n : ℝ` lives in the unit interval
-/
@[reducible]
def Fraction {i n : ℕ} (hn : 0 < n) (hi : i ≤ n) : I :=
  ⟨(i : ℝ)/(n : ℝ),
    ⟨div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n),
      (div_le_one ((Nat.cast_pos (α := ℝ)).mpr hn)).mpr (Nat.cast_le.mpr hi)⟩⟩


-- @@ L29-29 verbatim
namespace Fraction


-- @@ L31-34 verbatim
/-- For any positive number `n : ℕ`, we have the fraction `1/n : ℝ` in the unit interval
-/
@[reducible]
def ofPos {n : ℕ} (hn : 0 < n) : I := Fraction hn (Nat.succ_le_iff.mpr hn)


-- @@ L36-37 verbatim
@[simp]
lemma Fraction_coe {i n : ℕ} (hn : 0 < n) (hi : i ≤ n) : (Fraction hn hi : ℝ) = (i/n : ℝ) := rfl

-- @@ L38-38 verbatim
lemma ofPos_coe {n : ℕ} (hn : 0 < n) : ((ofPos hn) : ℝ) = (1/n : ℝ) := by simp


-- @@ L40-44 verbatim
/-- For any postive `n : ℕ`, we have that `0/n = n`.
-/
lemma eq_zero {n : ℕ} (n_pos : 0 < n) : Fraction n_pos (Nat.zero_le n) = 0 := by
  ext
  simp


-- @@ L46-52 verbatim
/-- For any postive `n : ℕ`, we have that `n/n = n`.
-/
lemma eq_one {n : ℕ} (n_pos : 0 < n) : Fraction n_pos (le_refl n) = 1 := by
  ext
  rw [Fraction_coe, div_self]
  · simp
  · exact Nat.cast_ne_zero.mpr (ne_of_gt n_pos)


-- @@ L54-62 verbatim
/-- For any `i n : ℕ` with `0 < i ≤ n`, we have that `i/n * 1/i` = `1/n` as members of `I`.
-/
lemma mul_inv {i n : ℕ} (i_pos : 0 < i) (hi_n : i ≤ n) :
    (Fraction (lt_of_lt_of_le i_pos hi_n) hi_n) * (ofPos i_pos) =
      (ofPos (lt_of_lt_of_le i_pos hi_n)) := by
  apply Subtype.coe_inj.mp
  have hi : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_lt i_pos).symm
  simp only [Set.Icc.coe_mul]
  field_simp


-- @@ L64-67 verbatim
/-- For any `n i : ℕ` with `0 < i ≤ n`, we have that `0 < i/n`.
-/
lemma pos_of_pos {n i : ℕ} (hi : 0 < i) (hn : i ≤ n) : 0 < Fraction (lt_of_lt_of_le hi hn) hn :=
  Subtype.coe_lt_coe.mp (div_pos (Nat.cast_pos.mpr hi) (Nat.cast_pos.mpr (lt_of_lt_of_le hi hn)))


-- @@ L69-78 verbatim
/-- For any `n i : ℕ` with `0 ≤ i < n`, we have that `i/n < 1`.
-/
lemma lt_one_of_lt {n i : ℕ} (hi : 0 ≤ i) (hn : i < n) :
    Fraction (lt_of_le_of_lt hi hn) (le_of_lt hn) < 1 :=
  Subtype.coe_lt_coe.mp
    ((div_lt_one (Nat.cast_pos.mpr (lt_of_le_of_lt hi hn))).mpr (Nat.cast_lt.mpr hn))

/-
For any positive `n : ℕ`, we have that `0 < 1/n`.
-/

-- @@ L79-84 verbatim
lemma ofPos_pos {n : ℕ} (hn : 0 < n) : 0 < ofPos hn :=
  pos_of_pos zero_lt_one (Nat.succ_le_iff.mpr hn)

/-
For any `n : ℕ` with `n > 1`, we have that `1/n < 1`.
-/

-- @@ L85-90 verbatim
lemma ofPos_lt_one {n : ℕ} (hn : 1 < n) : ofPos (lt_trans zero_lt_one hn) < 1 :=
  lt_one_of_lt zero_le_one hn

/-
For any `n m : ℕ` with `m < n`, we have that `m/n ≤ (m+1) ≤ n`
-/

-- @@ L91-97 verbatim
lemma lt_frac_succ {n m : ℕ} (hn : m < n) :
    Fraction (lt_of_le_of_lt (Nat.zero_le m) hn) (le_of_lt hn) <
    Fraction (lt_of_le_of_lt (Nat.zero_le m) hn) (Nat.succ_le_of_lt hn) := by
  change ((m : ℝ) / n) < ((m + 1 : ℕ) : ℝ) / n
  push_cast
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le m) hn))
  linarith


-- @@ L99-99 verbatim
end Fraction
