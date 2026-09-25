/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.FamilyMaps

-- @@ L9-14 verbatim
/-!
# Hypercharge in SM with RHN.

Relevant definitions for the SM hypercharge.

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


-- @@ L25-47 verbatim
/-- The hypercharge for 1 family. -/
@[simps!]
def Y₁ : (PlusU1 1).Sols where
  val := fun i =>
    match i with
    | (0 : Fin 6) => 1
    | (1 : Fin 6) => -4
    | (2 : Fin 6) => 2
    | (3 : Fin 6) => -3
    | (4 : Fin 6) => 6
    | (5 : Fin 6) => 0
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


-- @@ L49-52 verbatim
/-- The hypercharge for `n` family. -/
@[simps!]
def Y (n : ℕ) : (PlusU1 n).Sols :=
  familyUniversalAF n Y₁


-- @@ L54-54 verbatim
namespace Y


-- @@ L56-56 verbatim
variable {n : ℕ}


-- @@ L58-66 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma on_quadBiLin (S : (PlusU1 n).Charges) :
    quadBiLin (Y n).val S = accYY S := by
  erw [familyUniversal_quadBiLin]
  rw [accYY_decomp]
  simp only [Fin.isValue, Y₁_val, toSpecies_apply, one_mul, mul_neg,
    neg_mul, sub_neg_eq_add, add_left_inj, add_right_inj, mul_eq_mul_right_iff]
  ring_nf
  simp


-- @@ L68-69 verbatim
lemma on_quadBiLin_AFL (S : (PlusU1 n).LinSols) : quadBiLin (Y n).val S.val = 0 := by
  rw [on_quadBiLin, YYsol S]


-- @@ L71-77 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma add_AFL_quad (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accQuad (a • S.val + b • (Y n).val) = a ^ 2 * accQuad S.val := by
  erw [BiLinearSymm.toHomogeneousQuad_add, quadSol (b • (Y n)).1]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₂, quadBiLin.swap, on_quadBiLin_AFL]
  rw [← accQuad, accQuad.map_smul]
  simp


-- @@ L79-81 verbatim
lemma add_quad (S : (PlusU1 n).QuadSols) (a b : ℚ) :
    accQuad (a • S.val + b • (Y n).val) = 0 := by
  rw [add_AFL_quad, quadSol S]; simp


-- @@ L83-85 verbatim
/-- The `QuadSol` obtained by adding hypercharge to a `QuadSol`. -/
def addQuad (S : (PlusU1 n).QuadSols) (a b : ℚ) : (PlusU1 n).QuadSols :=
  linearToQuad (a • S.1 + b • (Y n).1.1) (add_quad S a b)


-- @@ L87-88 verbatim
lemma addQuad_zero (S : (PlusU1 n).QuadSols) (a : ℚ) : addQuad S a 0 = a • S := by
  simp only [addQuad, linearToQuad, zero_smul, add_zero]; rfl


-- @@ L90-97 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma on_cubeTriLin (S : (PlusU1 n).Charges) :
    cubeTriLin (Y n).val (Y n).val S = 6 * accYY S := by
  erw [familyUniversal_cubeTriLin']
  rw [accYY_decomp]
  simp only [Fin.isValue, Y₁_val, mul_one, toSpecies_apply, mul_neg,
    neg_mul, neg_neg, mul_zero, zero_mul, add_zero]
  ring


-- @@ L99-102 verbatim
lemma on_cubeTriLin_AFL (S : (PlusU1 n).LinSols) :
    cubeTriLin (Y n).val (Y n).val S.val = 0 := by
  rw [on_cubeTriLin, YYsol S]
  with_unfolding_all rfl


-- @@ L104-111 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma on_cubeTriLin' (S : (PlusU1 n).Charges) :
    cubeTriLin (Y n).val S S = 6 * accQuad S := by
  erw [familyUniversal_cubeTriLin]
  rw [accQuad_decomp]
  simp only [Fin.isValue, Y₁_val, mul_one, toSpecies_apply, mul_neg,
    neg_mul, zero_mul, add_zero]
  ring_nf


-- @@ L113-116 verbatim
lemma on_cubeTriLin'_ALQ (S : (PlusU1 n).QuadSols) :
    cubeTriLin (Y n).val S.val S.val = 0 := by
  rw [on_cubeTriLin', quadSol S]
  with_unfolding_all rfl


-- @@ L118-127 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma add_AFL_cube (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accCube (a • S.val + b • (Y n).val) =
    a ^ 2 * (a * accCube S.val + 3 * b * cubeTriLin S.val S.val (Y n).val) := by
  erw [TriLinearSymm.toCubic_add, cubeSol (b • (Y n)), accCube.map_smul]
  repeat rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  rw [on_cubeTriLin_AFL]
  simp only [HomogeneousCubic, accCube, TriLinearSymm.toCubic_apply,
    add_zero, Y_val, mul_zero]
  ring


-- @@ L129-133 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma add_AFQ_cube (S : (PlusU1 n).QuadSols) (a b : ℚ) :
    accCube (a • S.val + b • (Y n).val) = a ^ 3 * accCube S.val := by
  rw [add_AFL_cube, cubeTriLin.swap₃, on_cubeTriLin'_ALQ]
  ring


-- @@ L135-138 verbatim
lemma add_AF_cube (S : (PlusU1 n).Sols) (a b : ℚ) :
    accCube (a • S.val + b • (Y n).val) = 0 := by
  rw [add_AFQ_cube, cubeSol S]
  simp


-- @@ L140-142 verbatim
/-- The `Sol` obtained by adding hypercharge to a `Sol`. -/
def addCube (S : (PlusU1 n).Sols) (a b : ℚ) : (PlusU1 n).Sols :=
  quadToAF (addQuad S.1 a b) (add_AF_cube S a b)


-- @@ L144-144 verbatim
end Y

-- @@ L145-145 verbatim
end PlusU1

-- @@ L146-146 verbatim
end SMRHN
