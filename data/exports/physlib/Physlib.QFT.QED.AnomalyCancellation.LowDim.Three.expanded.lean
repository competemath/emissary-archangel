/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Basic

-- @@ L9-14 verbatim
/-!
# The Pure U(1) case with 3 fermion

We show that S is a solution only if one of its charges is zero.
We define a surjective map from `LinSols` with a charge equal to zero to `Sols`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Nat

-- @@ L19-19 verbatim
open Finset


-- @@ L21-21 verbatim
namespace PureU1


-- @@ L23-23 verbatim
variable {n : ℕ}

-- @@ L24-24 verbatim
namespace Three


-- @@ L26-36 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma cube_for_linSol' (S : (PureU1 3).LinSols) :
    3 * S.val (0 : Fin 3) * S.val (1 : Fin 3) * S.val (2 : Fin 3) = 0 ↔
    (PureU1 3).cubicACC S.val = 0 := by
  have hL := pureU1_linear S
  rw [Fin.sum_univ_three] at hL
  change _ ↔ accCube _ _ = _
  rw [accCube_explicit, Fin.sum_univ_three]
  rw [show S.val (0 : Fin 3) = - (S.val (1 : Fin 3) + S.val (2 : Fin 3)) by
      linear_combination hL]
  ring_nf


-- @@ L38-42 verbatim
lemma cube_for_linSol (S : (PureU1 3).LinSols) :
    (S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0 ∨ S.val (2 : Fin 3) = 0) ↔
    (PureU1 3).cubicACC S.val = 0 := by
  simp only [← cube_for_linSol', Fin.isValue, _root_.mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or, or_assoc]


-- @@ L44-45 verbatim
lemma three_sol_zero (S : (PureU1 3).Sols) : S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0
    ∨ S.val (2 : Fin 3) = 0 := (cube_for_linSol S.1.1).mpr S.cubicSol


-- @@ L47-52 verbatim
/-- Given a `LinSol` with a charge equal to zero a `Sol`. -/
def solOfLinear (S : (PureU1 3).LinSols)
    (hS : S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0 ∨ S.val (2 : Fin 3) = 0) :
    (PureU1 3).Sols :=
  ⟨⟨S, fun i => Fin.elim0 i⟩,
    (cube_for_linSol S).mp hS⟩


-- @@ L54-57 verbatim
theorem solOfLinear_surjects (S : (PureU1 3).Sols) :
    ∃ (T : (PureU1 3).LinSols) (hT : T.val (0 : Fin 3) = 0 ∨ T.val (1 : Fin 3) = 0
    ∨ T.val (2 : Fin 3) = 0), solOfLinear T hT = S :=
  ⟨S.1.1, three_sol_zero S, rfl⟩


-- @@ L59-59 verbatim
end Three


-- @@ L61-61 verbatim
end PureU1
