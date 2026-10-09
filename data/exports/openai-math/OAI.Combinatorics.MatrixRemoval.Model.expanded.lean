import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section




-- @@ L9-9 verbatim
namespace Problem348


-- @@ L11-11 verbatim
abbrev BinaryMatrix (n : ℕ) := Fin n → Fin n → Bool


-- @@ L13-13 verbatim
abbrev IncreasingMap (k n : ℕ) := {f : Fin k → Fin n // StrictMono f}


-- @@ L15-19 verbatim
def orderedCopies {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) :
    Finset (IncreasingMap k n × IncreasingMap k n) := by
  classical
  exact Finset.univ.filter (fun rc =>
    ∀ i j, A ((rc.1).val i) ((rc.2).val j) = H i j)


-- @@ L21-22 verbatim
def copyCount {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) : ℕ :=
  (orderedCopies H A).card


-- @@ L24-25 verbatim
def HFree {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) : Prop :=
  copyCount H A = 0


-- @@ L27-30 verbatim
def hammingDistance {n : ℕ} (A B : BinaryMatrix n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun rc : Fin n × Fin n =>
    A rc.1 rc.2 ≠ B rc.1 rc.2)).card


-- @@ L32-33 verbatim
def etaBit (a b : ℕ) : Bool :=
  decide (((a / (2 ^ (5 - b))) % 2) = 1)


-- @@ L35-39 verbatim
def anchor64 (u v : Fin 64) : Bool :=
  if 32 ≤ u.val ∧ 59 ≤ v.val then
    etaBit (u.val - 32) (v.val - 58)
  else
    decide (u.val ≠ v.val)


-- @@ L41-53 verbatim
def fixedH : BinaryMatrix 66 := fun u v =>
  if hu : u.val < 64 then
    if hv : v.val < 64 then
      anchor64 ⟨u.val, hu⟩ ⟨v.val, hv⟩
    else
      decide ((v.val = 64 ∧ u.val = 0) ∨
        (v.val = 65 ∧ u.val = 1))
  else
    if v.val < 64 then
      decide ((u.val = 64 ∧ v.val = 0) ∨
        (u.val = 65 ∧ v.val = 1))
    else
      decide (u.val = 65 ∨ v.val = 64)


-- @@ L55-60 verbatim
def fixedMinEdits {n : ℕ} (A : BinaryMatrix n) : ℕ := by
  classical
  exact
    (Finset.univ.image (fun B : BinaryMatrix n =>
      if HFree fixedH B then hammingDistance A B else n * n + 1)).min'
      (by simp)


-- @@ L62-63 verbatim
def fixedDistance {n : ℕ} (A : BinaryMatrix n) : ℝ :=
  (fixedMinEdits A : ℝ) / ((n : ℝ) ^ 2)


-- @@ L65-65 verbatim
end Problem348


-- @@ L67-67 verbatim
end


-- @@ L69-69 verbatim
end OAI
