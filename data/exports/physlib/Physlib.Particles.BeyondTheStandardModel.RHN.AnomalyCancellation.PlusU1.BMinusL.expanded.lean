/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.FamilyMaps

-- @@ L9-14 verbatim
/-!
# B Minus L in SM with RHN.

Relevant definitions for the SM `B-L`.

-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace SMRHN

-- @@ L19-19 verbatim
namespace PlusU1


-- @@ L21-21 verbatim
open SMνCharges

-- @@ L22-22 verbatim
open SMνACCs

-- @@ L23-23 verbatim
open BigOperators


-- @@ L25-25 verbatim
variable {n : ℕ}


-- @@ L27-49 verbatim
/-- $B - L$ in the 1-family case. -/
@[simps!]
def BL₁ : (PlusU1 1).Sols where
  val := fun i =>
    match i with
    | (0 : Fin 6) => 1
    | (1 : Fin 6) => -1
    | (2 : Fin 6) => -1
    | (3 : Fin 6) => -3
    | (4 : Fin 6) => 3
    | (5 : Fin 6) => 3
  linearSol := by
    intro i
    match i with
    | ⟨0, _⟩ => with_unfolding_all rfl
    | ⟨1, _⟩ => with_unfolding_all rfl
    | ⟨2, _⟩ => with_unfolding_all rfl
    | ⟨3, _⟩ => with_unfolding_all rfl
  quadSol := by
    intro i
    match i with
    | ⟨0, _⟩ => with_unfolding_all rfl
  cubicSol := by with_unfolding_all rfl


-- @@ L51-54 verbatim
/-- $B - L$ in the $n$-family case. -/
@[simps!]
def BL (n : ℕ) : (PlusU1 n).Sols :=
  familyUniversalAF n BL₁


-- @@ L56-56 verbatim
namespace BL


-- @@ L58-58 verbatim
variable {n : ℕ}


-- @@ L60-67 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma on_quadBiLin (S : (PlusU1 n).Charges) :
    quadBiLin (BL n).val S = 1/2 * accYY S + 3/2 * accSU2 S - 2 * accSU3 S := by
  erw [familyUniversal_quadBiLin]
  rw [accYY_decomp, accSU2_decomp, accSU3_decomp]
  simp only [Fin.isValue, BL₁_val, toSpecies_apply, one_mul, mul_neg,
    mul_one, neg_mul, sub_neg_eq_add]
  ring


-- @@ L69-71 verbatim
lemma on_quadBiLin_AFL (S : (PlusU1 n).LinSols) : quadBiLin (BL n).val S.val = 0 := by
  rw [on_quadBiLin, YYsol S, SU2Sol S, SU3Sol S]
  with_unfolding_all rfl


-- @@ L73-79 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma add_AFL_quad (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accQuad (a • S.val + b • (BL n).val) = a ^ 2 * accQuad S.val := by
  erw [BiLinearSymm.toHomogeneousQuad_add, quadSol (b • (BL n)).1]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₂, quadBiLin.swap, on_quadBiLin_AFL]
  erw [accQuad.map_smul]
  simp


-- @@ L81-84 verbatim
lemma add_quad (S : (PlusU1 n).QuadSols) (a b : ℚ) :
    accQuad (a • S.val + b • (BL n).val) = 0 := by
  rw [add_AFL_quad, quadSol S]
  exact Rat.mul_zero (a ^ 2)


-- @@ L86-88 verbatim
/-- The `QuadSol` obtained by adding $B-L$ to a `QuadSol`. -/
def addQuad (S : (PlusU1 n).QuadSols) (a b : ℚ) : (PlusU1 n).QuadSols :=
  linearToQuad (a • S.1 + b • (BL n).1.1) (add_quad S a b)


-- @@ L90-92 verbatim
lemma addQuad_zero (S : (PlusU1 n).QuadSols) (a : ℚ) : addQuad S a 0 = a • S := by
  simp only [addQuad, linearToQuad, zero_smul, add_zero]
  rfl


-- @@ L94-101 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma on_cubeTriLin (S : (PlusU1 n).Charges) :
    cubeTriLin (BL n).val (BL n).val S = 9 * accGrav S - 24 * accSU3 S := by
  erw [familyUniversal_cubeTriLin']
  rw [accGrav_decomp, accSU3_decomp]
  simp only [Fin.isValue, BL₁_val, mul_one, toSpecies_apply, mul_neg,
    neg_neg, neg_mul]
  ring


-- @@ L103-106 verbatim
lemma on_cubeTriLin_AFL (S : (PlusU1 n).LinSols) :
    cubeTriLin (BL n).val (BL n).val S.val = 0 := by
  rw [on_cubeTriLin, gravSol S, SU3Sol S]
  with_unfolding_all rfl


-- @@ L108-117 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma add_AFL_cube (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accCube (a • S.val + b • (BL n).val) =
    a ^ 2 * (a * accCube S.val + 3 * b * cubeTriLin S.val S.val (BL n).val) := by
  erw [TriLinearSymm.toCubic_add, cubeSol (b • (BL n)), accCube.map_smul]
  repeat rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  rw [on_cubeTriLin_AFL]
  simp only [HomogeneousCubic, accCube, TriLinearSymm.toCubic_apply,
    add_zero, BL_val, mul_zero]
  ring


-- @@ L119-119 verbatim
end BL

-- @@ L120-120 verbatim
end PlusU1

-- @@ L121-121 verbatim
end SMRHN
