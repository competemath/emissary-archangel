/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BMinusL

-- @@ L9-17 verbatim
/-!
# Solutions from quad solutions

We use $B-L$ to form a surjective map from quad solutions to solutions.

## References

* The main reference for this material is https://arxiv.org/abs/2006.03588. [ref: arxiv_2006_03588]
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace SMRHN

-- @@ L22-22 verbatim
namespace PlusU1


-- @@ L24-24 verbatim
namespace QuadSolToSol


-- @@ L26-26 verbatim
open SMνCharges

-- @@ L27-27 verbatim
open SMνACCs

-- @@ L28-28 verbatim
open BigOperators


-- @@ L30-30 verbatim
variable {n : ℕ}

-- @@ L31-32 verbatim
/-- A helper function for what follows. -/
def α₁ (S : (PlusU1 n).QuadSols) : ℚ := - 3 * cubeTriLin S.val S.val (BL n).val


-- @@ L34-35 verbatim
/-- A helper function for what follows. -/
def α₂ (S : (PlusU1 n).QuadSols) : ℚ := accCube S.val


-- @@ L37-40 verbatim
lemma cube_α₁_α₂_zero (S : (PlusU1 n).QuadSols) (a b : ℚ) (h1 : α₁ S = 0) (h2 : α₂ S = 0) :
    accCube (BL.addQuad S a b).val = 0 := by
  erw [BL.add_AFL_cube]
  simp_all [α₁, α₂]


-- @@ L42-42 verbatim
lemma α₂_AF (S : (PlusU1 n).Sols) : α₂ S.toQuadSols = 0 := S.2


-- @@ L44-51 verbatim
lemma BL_add_α₁_α₂_cube (S : (PlusU1 n).QuadSols) :
    accCube (BL.addQuad S (α₁ S) (α₂ S)).val = 0 := by
  erw [BL.add_AFL_cube]
  simp only [α₁, BL_val, neg_mul, even_two, Even.neg_pow, α₂, mul_eq_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, false_or]
  right
  field_simp
  ring


-- @@ L53-55 verbatim
lemma BL_add_α₁_α₂_AF (S : (PlusU1 n).Sols) :
    BL.addQuad S.1 (α₁ S.1) (α₂ S.1) = (α₁ S.1) • S.1 := by
  rw [α₂_AF, BL.addQuad_zero]


-- @@ L57-59 verbatim
/-- The construction of a `Sol` from a `QuadSol` in the generic case. -/
def generic (S : (PlusU1 n).QuadSols) : (PlusU1 n).Sols :=
  quadToAF (BL.addQuad S (α₁ S) (α₂ S)) (BL_add_α₁_α₂_cube S)


-- @@ L61-65 verbatim
lemma generic_on_AF (S : (PlusU1 n).Sols) : generic S.1 = (α₁ S.1) • S := by
  apply ACCSystem.Sols.ext
  change (BL.addQuad S.1 (α₁ S.1) (α₂ S.1)).val = _
  rw [BL_add_α₁_α₂_AF]
  rfl


-- @@ L67-69 verbatim
lemma generic_on_AF_α₁_ne_zero (S : (PlusU1 n).Sols) (h : α₁ S.1 ≠ 0) :
    (α₁ S.1)⁻¹ • generic S.1 = S := by
  rw [generic_on_AF, smul_smul, inv_mul_cancel₀ h, one_smul]


-- @@ L71-74 verbatim
/-- The construction of a `Sol` from a `QuadSol` in the case when `α₁ S = 0` and `α₂ S = 0`. -/
def special (S : (PlusU1 n).QuadSols) (a b : ℚ) (h1 : α₁ S = 0) (h2 : α₂ S = 0) :
    (PlusU1 n).Sols :=
  quadToAF (BL.addQuad S a b) (cube_α₁_α₂_zero S a b h1 h2)


-- @@ L76-81 verbatim
lemma special_on_AF (S : (PlusU1 n).Sols) (h1 : α₁ S.1 = 0) :
    special S.1 1 0 h1 (α₂_AF S) = S := by
  apply ACCSystem.Sols.ext
  change (BL.addQuad S.1 1 0).val = _
  rw [BL.addQuad_zero]
  simp


-- @@ L83-83 verbatim
end QuadSolToSol


-- @@ L85-85 verbatim
open QuadSolToSol

-- @@ L86-92 verbatim
/-- A map from `QuadSols × ℚ × ℚ` to `Sols` taking account of the special and generic cases.
We will show that this map is a surjection. -/
def quadSolToSol {n : ℕ} : (PlusU1 n).QuadSols × ℚ × ℚ → (PlusU1 n).Sols := fun S =>
  if h1 : α₁ S.1 = 0 ∧ α₂ S.1 = 0 then
    special S.1 S.2.1 S.2.2 h1.1 h1.2
  else
    S.2.1 • generic S.1


-- @@ L94-101 verbatim
/-- A map from `Sols` to `QuadSols × ℚ × ℚ` which forms a right-inverse to `quadSolToSol`, as
shown in `quadSolToSolInv_rightInverse`. -/
def quadSolToSolInv {n : ℕ} : (PlusU1 n).Sols → (PlusU1 n).QuadSols × ℚ × ℚ :=
    fun S =>
  if α₁ S.1 = 0 then
    (S.1, 1, 0)
  else
    (S.1, (α₁ S.1)⁻¹, 0)


-- @@ L103-107 verbatim
lemma quadSolToSolInv_1 (S : (PlusU1 n).Sols) :
    (quadSolToSolInv S).1 = S.1 := by
  simp only [quadSolToSolInv, α₁, BL_val,
    neg_mul, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
  split <;> rfl


-- @@ L109-112 verbatim
lemma quadSolToSolInv_α₁_α₂_zero (S : (PlusU1 n).Sols) (h : α₁ S.1 = 0) :
    α₁ (quadSolToSolInv S).1 = 0 ∧ α₂ (quadSolToSolInv S).1 = 0 := by
  rw [quadSolToSolInv_1, α₂_AF S, h]
  exact Prod.mk_eq_zero.mp rfl


-- @@ L114-118 verbatim
lemma quadSolToSolInv_α₁_α₂_ne_zero (S : (PlusU1 n).Sols) (h : α₁ S.1 ≠ 0) :
    ¬ (α₁ (quadSolToSolInv S).1 = 0 ∧ α₂ (quadSolToSolInv S).1 = 0) := by
  rw [not_and, quadSolToSolInv_1, α₂_AF S]
  intro hn
  simp_all


-- @@ L120-126 verbatim
lemma quadSolToSolInv_special (S : (PlusU1 n).Sols) (h : α₁ S.1 = 0) :
    special (quadSolToSolInv S).1 (quadSolToSolInv S).2.1 (quadSolToSolInv S).2.2
    (quadSolToSolInv_α₁_α₂_zero S h).1 (quadSolToSolInv_α₁_α₂_zero S h).2 = S := by
  simp only [quadSolToSolInv_1]
  rw [show (quadSolToSolInv S).2.1 = 1 by rw [quadSolToSolInv, if_pos h]]
  rw [show (quadSolToSolInv S).2.2 = 0 by rw [quadSolToSolInv, if_pos h]]
  rw [special_on_AF]


-- @@ L128-132 verbatim
lemma quadSolToSolInv_generic (S : (PlusU1 n).Sols) (h : α₁ S.1 ≠ 0) :
    (quadSolToSolInv S).2.1 • generic (quadSolToSolInv S).1 = S := by
  simp only [quadSolToSolInv_1]
  rw [show (quadSolToSolInv S).2.1 = (α₁ S.1)⁻¹ by rw [quadSolToSolInv, if_neg h]]
  rw [generic_on_AF_α₁_ne_zero S h]


-- @@ L134-140 verbatim
lemma quadSolToSolInv_rightInverse : Function.RightInverse (@quadSolToSolInv n) quadSolToSol := by
  intro S
  by_cases h : α₁ S.1 = 0
  · rw [quadSolToSol, dif_pos (quadSolToSolInv_α₁_α₂_zero S h)]
    exact quadSolToSolInv_special S h
  · rw [quadSolToSol, dif_neg (quadSolToSolInv_α₁_α₂_ne_zero S h)]
    exact quadSolToSolInv_generic S h


-- @@ L142-143 verbatim
theorem quadSolToSol_surjective : Function.Surjective (@quadSolToSol n) :=
  Function.RightInverse.surjective quadSolToSolInv_rightInverse


-- @@ L145-145 verbatim
end PlusU1

-- @@ L146-146 verbatim
end SMRHN
