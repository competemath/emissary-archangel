/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag


-- @@ L12-16 verbatim
/-!
# LeanPool.BrauerGroupNew.MatrixCenterEquiv

Imported Lean Pool material for `LeanPool.BrauerGroupNew.MatrixCenterEquiv`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
local notation "M[" ι "," R "]" => Matrix ι ι R


-- @@ L22-22 verbatim
universe u v w


-- @@ L24-24 verbatim
section RingEquiv


-- @@ L26-46 expanded
lemma Matrix.mem_center_iff (R : Type*) [Ring R] (n : ℕ) (M) :
    M ∈ Subring.center (Matrix (Fin n) (Fin n) R) ↔ ∃ α : (Subring.center R), M = α • 1 :=
  by
  constructor
  ·
    if h : n = 0 then subst h; exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩
    else
      intro h
      rw [Subring.mem_center_iff] at h
      have diag : Matrix.IsDiag M := fun i j hij => by
        simpa only [single_mul_apply_same, one_mul, mul_single_apply_of_ne (hbj := hij.symm)] using
          Matrix.ext_iff.2 (h (single i i 1)) i j
      have (i j : Fin n) : M i i = M j j := by
        simpa [Eq.comm] using Matrix.ext_iff.2 (h (single i j 1)) i j
      obtain ⟨b, hb⟩ : ∃ (b : R), M = b • 1 :=
        by
        refine ⟨M ⟨0, by omega⟩ ⟨0, by omega⟩, Matrix.ext fun i j => ?_⟩
        if heq : i = j then subst heq; rw [this i ⟨0, by omega⟩]; simp
        else simp [diag heq, Matrix.one_apply_ne heq]
      suffices b ∈ Subring.center R by aesop
      refine Subring.mem_center_iff.mpr fun g ↦ ?_
      simpa [hb] using Matrix.ext_iff.2 (h (Matrix.diagonal fun _ ↦ g)) ⟨0, by omega⟩ ⟨0, by omega⟩
  · rintro ⟨α, ha⟩; rw [Subring.mem_center_iff]; aesop


-- @@ L48-76 expanded
/-- The center of a nonempty square matrix ring is ring-equivalent to the center of the
base ring. -/
def Matrix.centerEquivBase (n : ℕ) (hn : 0 < n) (R : Type*) [Ring R] :
    Subring.center (Matrix (Fin n) (Fin n) R) ≃+* (Subring.center R)
    where
  toFun
    A :=
    ⟨(A.1 ⟨0, by omega⟩ ⟨0, by omega⟩),
      by
      obtain ⟨a, ha⟩ := (Matrix.mem_center_iff R n A.1).1 A.2
      rw [ha, smul_apply, one_apply_eq]
      change (a : R) * (1 : R) ∈ Subring.center R
      exact Subring.mul_mem _ a.2 (Subring.one_mem _)⟩
  invFun a := ⟨a • 1, Subring.mem_center_iff.2 fun A ↦ Matrix.ext <| by simp⟩
  left_inv := by
    if hn : n = 0 then subst hn; exact fun _ ↦ Subsingleton.elim _ _
    else
      rintro ⟨A, hA⟩; obtain ⟨⟨α, hα⟩, rfl⟩ := Matrix.mem_center_iff _ _ _ |>.1 hA
      simp only [smul_apply, one_apply_eq, Subtype.mk.injEq]
      change (α • (1 : R)) • (1 : Matrix (Fin n) (Fin n) R) = α • (1 : _)
      simp only [smul_eq_mul, mul_one]
  right_inv := by
    intro ⟨r, hr⟩; simp only [smul_apply, one_apply_eq, Subtype.mk.injEq]
    change r • (1 : R) = _
    simp only [smul_eq_mul, mul_one]
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    rw [Matrix.mem_center_iff] at hA hB
    obtain ⟨a, rfl⟩ := hA
    simp_all
  map_add' := by simp_all


-- @@ L78-78 verbatim
end RingEquiv


-- @@ L80-80 verbatim
section AlgEquiv


-- @@ L82-82 verbatim
variable (R A : Type u) [CommSemiring R] [Ring A] [Algebra R A]


-- @@ L84-88 expanded
/-- The center of a nonempty matrix algebra is algebra-equivalent to the center of the algebra. -/
def Matrix.centerAlgEquiv (n : ℕ) (hn : 0 < n) :
    Subalgebra.center R (Matrix (Fin n) (Fin n) A) ≃ₐ[R] Subalgebra.center R A :=
  { __ := Matrix.centerEquivBase n hn A
    commutes' := fun _ ↦ rfl }


-- @@ L90-90 verbatim
end AlgEquiv
