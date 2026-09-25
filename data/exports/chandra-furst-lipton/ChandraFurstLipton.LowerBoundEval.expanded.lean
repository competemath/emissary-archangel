/-
Copyright (c) 2024 Yaël Dillies, Isabel Dahlgren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Isabel Dahlgren
-/
module

public import ChandraFurstLipton.NOFModel
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.ZMod.Basic


-- @@ L14-16 verbatim
/-!
# Lower bound on the communication complexity of Eval
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace NOF

-- @@ L21-22 verbatim
variable {ι G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ} [NeZero d]
  {P : Protocol G d} {t : ℕ} {B : List Bool} {a : ZMod d → ZMod d → G} [Fintype ι]


-- @@ L24-25 verbatim
def eval (x : ι → G) : Bool :=
  ∑ i, x i == 0


-- @@ L27-27 verbatim
@[simp] lemma eval_eq_true {x : ι → G} : eval x = true ↔ ∑ i, x i = 0 := by simp [eval]


-- @@ L29-29 verbatim
variable [DecidableEq ι]


-- @@ L31-52 verbatim
lemma trivial_of_isForbiddenPattern_of_isValid_eval (ha : IsForbiddenPattern a)
    (hP : P.IsValid eval t) (hE : ∀ i, eval (a i) = true) (hB : ∀ i, P.broadcast (a i) t = B) :
    ∀ i j, a i = a j := by
  obtain ⟨v, ha⟩ := ha
  have : P.broadcast v t = B := ha.broadcast_eq hB
  have h i : eval (a i) = eval v :=
    calc
      _ = P.guess i (forget i (a i)) (P.broadcast (a i) t) := by rw [hP]
      _ = P.guess i (forget i v) (P.broadcast v t) := by rw [hB, ha.broadcast_eq hB, ha.forget]
      _ = eval v := by rw [hP]
  suffices h : ∀ i, a i = v by simp [h]
  intro i
  ext j
  obtain hij | rfl := ne_or_eq i j
  · exact ha hij
  simp only [hE, Bool.true_eq, eval_eq_true, forall_const] at h
  rw [← sub_eq_zero]
  calc
    a i i - v i = ∑ j, (a i j - v j) := by
      rw [Fintype.sum_eq_single]; simpa [eq_comm, sub_eq_zero] using @ha i
    _ = ∑ j, a i j - ∑ j, v j := by rw [Finset.sum_sub_distrib]
    _ = 0 := by simpa [h] using hE i


-- @@ L54-58 verbatim
def getBits (B : List Bool) (i : ℕ) (d : ℕ) : List Bool := Id.run do
  let mut L := []
  for j in [0:B.length] do
    L := L ++ [B.getI ((i - 1) % d + j)]
  pure L


-- @@ L60-60 verbatim
variable [Fintype G]


-- @@ L62-73 verbatim
noncomputable
def Protocol.trivial (hd : 3 ≤ d) (F : (ZMod d → G) → Bool) : Protocol G d where
  nextBit i x B := by
    refine (Nat.bits (Fintype.equivFin G (x ⟨i + 1, ?_ ⟩))).getI (B.length / d)
    rw [Ne, add_eq_left, ← Nat.cast_one, ZMod.natCast_eq_zero_iff, Nat.dvd_one]
    omega
  guess i x B := F fun j ↦
    if h : j = i then
      (Fintype.equivFin G).symm <| (ZMod.finEquiv _).symm
        (BitVec.toNat (BitVec.ofBoolListLE (getBits B i.val d)))
    else
      x ⟨j, h⟩


-- @@ L75-75 verbatim
end NOF
