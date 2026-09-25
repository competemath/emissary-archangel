/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Basic
public import Mathlib.RepresentationTheory.Basic

-- @@ L10-16 verbatim
/-!
# Permutations of MSSM charges and solutions

The three family MSSM charges has a family permutation of S₃⁶. This file defines this group
and its action on the MSSM.

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Nat

-- @@ L21-21 verbatim
open Finset


-- @@ L23-23 verbatim
namespace MSSM


-- @@ L25-25 verbatim
open MSSMCharges

-- @@ L26-26 verbatim
open MSSMACCs

-- @@ L27-27 verbatim
open BigOperators


-- @@ L29-31 verbatim
/-- The group of family permutations is `S₃⁶`-/
@[simp]
def PermGroup := Fin 6 → Equiv.Perm (Fin 3)


-- @@ L33-35 verbatim
/-- The type `PermGroup` has a group instances derived from the group instance of it's target. -/
@[simp]
instance : Group PermGroup := Pi.group


-- @@ L37-53 verbatim
/-- The image of an element of `permGroup` under the representation on charges. -/
@[simps!]
def chargeMap (f : PermGroup) : MSSMCharges.Charges →ₗ[ℚ] MSSMCharges.Charges where
  toFun S := toSpecies.symm (fun i => toSMSpecies i S ∘ f i, Prod.snd (toSpecies S))
  map_add' S T := by
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    rw [(toSMSpecies i).map_add]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
  map_smul' a S := by
    rw [charges_eq_toSpecies_eq]
    apply And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    rw [(toSMSpecies i).map_smul, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl


-- @@ L55-57 verbatim
lemma chargeMap_toSpecies (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    toSMSpecies j (chargeMap f S) = toSMSpecies j S ∘ f j :=
  toSMSpecies_toSpecies_inv _ _


-- @@ L59-82 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The representation of `permGroup` acting on the vector space of charges. -/
@[simp]
def repCharges : Representation ℚ PermGroup (MSSMCharges).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    simp only [Module.End.mul_apply]
    rw [chargeMap_toSpecies, chargeMap_toSpecies]
    simp only [Pi.inv_apply]
    rw [chargeMap_toSpecies]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    refine And.intro ?_ $ Prod.mk_inj.mp rfl
    intro i
    exact toSMSpecies_toSpecies_inv _ _


-- @@ L84-86 verbatim
lemma repCharges_toSMSpecies (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    toSMSpecies j (repCharges f S) = toSMSpecies j S ∘ f⁻¹ j :=
  toSMSpecies_toSpecies_inv _ _


-- @@ L88-92 verbatim
lemma toSpecies_sum_invariant (m : ℕ) (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    ∑ i, ((fun a => a ^ m) ∘ toSMSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSMSpecies j S) i := by
  rw [repCharges_toSMSpecies]
  exact Equiv.sum_comp (f⁻¹ j) ((fun a => a ^ m) ∘ (toSMSpecies j) S)


-- @@ L94-95 verbatim
lemma Hd_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    Hd (repCharges f S) = Hd S := rfl


-- @@ L97-98 verbatim
lemma Hu_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    Hu (repCharges f S) = Hu S := rfl


-- @@ L100-106 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accGrav_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accGrav (repCharges f S) = accGrav S :=
  accGrav_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)


-- @@ L108-114 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accSU2_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accSU2 (repCharges f S) = accSU2 S :=
  accSU2_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)


-- @@ L116-120 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accSU3_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext
    (by simpa using toSpecies_sum_invariant 1 f S)


-- @@ L122-128 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accYY_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)


-- @@ L130-135 verbatim
lemma accQuad_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accQuad (repCharges f S) = accQuad S :=
  accQuad_ext
    (toSpecies_sum_invariant 2 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)


-- @@ L137-142 verbatim
lemma accCube_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accCube (repCharges f S) = accCube S :=
  accCube_ext
    (toSpecies_sum_invariant 3 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)


-- @@ L144-144 verbatim
end MSSM
