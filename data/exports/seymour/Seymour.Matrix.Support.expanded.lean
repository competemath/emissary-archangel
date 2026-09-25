import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.Basic.Fin


-- @@ L4-8 verbatim
/-!
# Support Matrix

This file defines the support matrix and provides some API about them.
-/


-- @@ L10-10 verbatim
variable {X Y R : Type*} [Zero R] [DecidableEq R]


-- @@ L12-15 verbatim
/-- Auxiliary `Z2`-valued matrix that has `1` on the position of all nonzero elements. -/
@[simp]
def Matrix.support (A : Matrix X Y R) : Matrix X Y Z2 :=
  Matrix.of (if A · · = 0 then 0 else 1)


-- @@ L17-19 verbatim
lemma Matrix.support_transpose (A : Matrix X Y R) :
    A.support.transpose = A.transpose.support :=
  rfl


-- @@ L21-23 verbatim
lemma Matrix.support_submatrix (A : Matrix X Y R) {X' Y' : Type*} (f : X' → X) (g : Y' → Y) :
    A.support.submatrix f g = (A.submatrix f g).support :=
  rfl


-- @@ L25-25 verbatim
omit R


-- @@ L27-28 verbatim
lemma Matrix.support_Z2 (A : Matrix X Y Z2) : A.support = A := by
  aesop


-- @@ L30-35 verbatim
lemma Matrix.IsTotallyUnimodular.abs_eq_support_val {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    ∀ i : X, ∀ j : Y, |A i j| = (A.support i j).val := by
  intro i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.of_apply, ZMod.natCast_val, ←hs]
  cases s <;> rfl


-- @@ L37-42 verbatim
lemma Matrix.IsTotallyUnimodular.abs_cast_eq_support {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular) :
    ∀ i : X, ∀ j : Y, |A i j|.cast = A.support i j := by
  intro i j
  obtain ⟨s, hs⟩ := hA.apply i j
  rw [Matrix.support, Matrix.of_apply, ←hs]
  cases s <;> simp


-- @@ L44-51 verbatim
lemma Matrix.IsTotallyUnimodular.apply_abs_eq_one {A : Matrix X Y ℚ} (hA : A.IsTotallyUnimodular)
    {i : X} {j : Y} (hAij : A.support i j = 1) :
    |A i j| = 1 := by
  obtain ⟨s, hs⟩ := hA.apply i j
  cases s with
  | zero => simp [←hs] at hAij
  | pos => simp [←hs]
  | neg => simp [←hs]
