/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Basic
public import Mathlib.RepresentationTheory.Basic

-- @@ L10-14 verbatim
/-!
# Permutations of SM charges with RHN.

We define the group of permutations for the SM charges with RHN.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Nat

-- @@ L19-19 verbatim
open Finset


-- @@ L21-21 verbatim
namespace SMRHN


-- @@ L23-23 verbatim
open SMνCharges

-- @@ L24-24 verbatim
open SMνACCs

-- @@ L25-25 verbatim
open BigOperators


-- @@ L27-29 verbatim
/-- The group of `Sₙ` permutations for each species. -/
@[simp]
def PermGroup (n : ℕ) := Fin 6 → Equiv.Perm (Fin n)


-- @@ L31-31 verbatim
variable {n : ℕ}


-- @@ L33-35 verbatim
/-- The instance of a group on `PermGroup n` through the target space `Equiv.Perm (Fin n)`. -/
@[simp]
instance : Group (PermGroup n) := Pi.group


-- @@ L37-42 verbatim
/-- The image of an element of `permGroup n` under the representation on charges. -/
@[simps!]
def chargeMap (f : PermGroup n) : (SMνCharges n).Charges →ₗ[ℚ] (SMνCharges n).Charges where
  toFun S := toSpeciesEquiv.symm (fun i => toSpecies i S ∘ f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L44-62 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The representation of `(permGroup n)` acting on the vector space of charges. -/
@[simp]
def repCharges {n : ℕ} : Representation ℚ (PermGroup n) (SMνCharges n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [chargeMap_apply, Pi.inv_apply, Module.End.mul_apply]
    repeat rw [toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    refine LinearMap.ext fun S => ?_
    rw [charges_eq_toSpecies_eq]
    intro i
    exact toSMSpecies_toSpecies_inv _ _


-- @@ L64-66 verbatim
lemma repCharges_toSpecies (f : PermGroup n) (S : (SMνCharges n).Charges) (j : Fin 6) :
    toSpecies j (repCharges f S) = toSpecies j S ∘ f⁻¹ j :=
  toSMSpecies_toSpecies_inv _ _


-- @@ L68-72 verbatim
lemma toSpecies_sum_invariant (m : ℕ) (f : PermGroup n) (S : (SMνCharges n).Charges) (j : Fin 6) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j S) i := by
  rw [repCharges_toSpecies]
  exact Equiv.sum_comp (f⁻¹ j) ((fun a => a ^ m) ∘ toSpecies j S)


-- @@ L74-77 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accGrav_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accGrav (repCharges f S) = accGrav S :=
  accGrav_ext (by simpa using toSpecies_sum_invariant 1 f S)


-- @@ L79-82 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accSU2_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accSU2 (repCharges f S) = accSU2 S :=
  accSU2_ext (by simpa using toSpecies_sum_invariant 1 f S)


-- @@ L84-87 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accSU3_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext (by simpa using toSpecies_sum_invariant 1 f S)


-- @@ L89-92 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma accYY_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext (by simpa using toSpecies_sum_invariant 1 f S)


-- @@ L94-96 verbatim
lemma accQuad_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accQuad (repCharges f S) = accQuad S :=
  accQuad_ext (toSpecies_sum_invariant 2 f S)


-- @@ L98-100 verbatim
lemma accCube_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accCube (repCharges f S) = accCube S :=
  accCube_ext (by simpa using toSpecies_sum_invariant 3 f S)


-- @@ L102-102 verbatim
end SMRHN
