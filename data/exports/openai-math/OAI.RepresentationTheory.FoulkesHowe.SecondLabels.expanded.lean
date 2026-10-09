import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators


-- @@ L8-8 verbatim
namespace Problem346.SecondTransfer


-- @@ L10-12 verbatim
/-- Blocks: `none` is the common vector, `some 0` is the fixed first row,
and `some i.succ` is the independent vector in row `i`. -/
abbrev Block (r : ℕ) := Option (Fin (r+1))


-- @@ L14-16 verbatim
/-- In each nonzero row, its first `k i` factors use the common block. -/
def label {r b : ℕ} (k : Fin r → ℕ) (p : Fin (r+1) × Fin b) : Block r :=
  Fin.cases (some 0) (fun i => if p.2.val < k i then none else some i.succ) p.1


-- @@ L18-19 verbatim
@[simp] theorem label_zero_row {r b : ℕ} (k : Fin r → ℕ) (j : Fin b) :
    label k (0,j) = some 0 := rfl


-- @@ L21-23 verbatim
@[simp] theorem label_succ_row {r b : ℕ} (k : Fin r → ℕ)
    (i : Fin r) (j : Fin b) :
    label k (i.succ,j) = if j.val < k i then none else some i.succ := rfl


-- @@ L25-28 verbatim
@[simp] theorem label_zero {r b : ℕ} (p : Fin (r+1) × Fin b) :
    label (fun _ : Fin r => 0) p = some p.1 := by
  rcases p with ⟨i,j⟩
  refine Fin.cases ?_ (fun i => ?_) i <;> simp


-- @@ L30-30 verbatim
end Problem346.SecondTransfer


-- @@ L32-32 verbatim
end


-- @@ L34-34 verbatim
end OAI
