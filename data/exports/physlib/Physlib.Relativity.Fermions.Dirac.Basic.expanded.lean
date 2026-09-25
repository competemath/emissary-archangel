/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded

-- @@ L12-23 verbatim
/-!

# Dirac fermions

In this file we define Dirac fermions.
This corresponds to a combination of two Weyl fermions (ψ^α, χ_{dot α})
That is a LeftHandedWeyl and a DualRightHandedWeyl.

## References

* arXiv:0812.1594 page 197. [ref: Dreiner:2008tw]
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace Fermion

-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open Matrix

-- @@ L31-31 verbatim
open MatrixGroups

-- @@ L32-32 verbatim
open Complex

-- @@ L33-33 verbatim
open TensorProduct


-- @@ L35-41 verbatim
/-- A Dirac fermion, consisting of a left handed Weyl fermion and a dual
  right handed Weyl fermion. -/
structure Dirac where
  /-- The left handed component of the Dirac fermion. -/
  left : LeftHandedWeyl
  /-- The right handed component of the Dirac fermion. -/
  dualRight : DualRightHandedWeyl


-- @@ L43-43 verbatim
namespace Dirac


-- @@ L45-52 verbatim
/-!

## The underlying module structure

We inherit the module structure on dirac fermions
from the module structure on left handed and dual right handed Weyl fermions.

-/


-- @@ L54-60 verbatim
/-- The decomposition of a Dirac fermion into its left handed and
  dual right handed components. -/
def decomposeEquiv : Dirac ≃ LeftHandedWeyl × DualRightHandedWeyl where
  toFun d := (d.left, d.dualRight)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L62-62 verbatim
instance : AddCommGroup Dirac := Equiv.addCommGroup decomposeEquiv


-- @@ L64-64 verbatim
instance : Module ℂ Dirac := Equiv.module ℂ decomposeEquiv


-- @@ L66-67 verbatim
@[simp]
lemma left_add (d₁ d₂ : Dirac) : (d₁ + d₂).left = d₁.left + d₂.left := rfl


-- @@ L69-70 verbatim
@[simp]
lemma dualRight_add (d₁ d₂ : Dirac) : (d₁ + d₂).dualRight = d₁.dualRight + d₂.dualRight := rfl


-- @@ L72-73 verbatim
@[simp]
lemma left_smul (c : ℂ) (d : Dirac) : (c • d).left = c • d.left := rfl


-- @@ L75-76 verbatim
@[simp]
lemma dualRight_smul (c : ℂ) (d : Dirac) : (c • d).dualRight = c • d.dualRight := rfl


-- @@ L78-82 verbatim
/-- The linear equivalence between `Dirac` and `LeftHandedWeyl × DualRightHandedWeyl`. -/
def decomposeLinEquiv : Dirac ≃ₗ[ℂ] LeftHandedWeyl × DualRightHandedWeyl where
  toEquiv := decomposeEquiv
  map_add' := by intros; rfl
  map_smul' := by intros; rfl


-- @@ L84-88 verbatim
/-!

## The chiral basis

-/


-- @@ L90-90 verbatim
open Module


-- @@ L92-95 verbatim
/-- The chiral basis of the Dirac fermions. -/
def chiralBasis : Basis (Fin 4) ℂ Dirac :=
  ((LeftHandedWeyl.basis.prod DualRightHandedWeyl.basis).reindex finSumFinEquiv).map
  decomposeLinEquiv.symm


-- @@ L97-103 verbatim
lemma chiralBasis_cast_add (i : Fin 2) : chiralBasis (Fin.castAdd 2 i) =
    ⟨LeftHandedWeyl.basis i, 0⟩ := by
  fin_cases i
  all_goals
    simp only [chiralBasis, Nat.reduceAdd, Basis.map_apply, Basis.coe_reindex,
    Function.comp_apply, Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr]
    rfl


-- @@ L105-111 verbatim
lemma chiralBasis_nat_add (i : Fin 2) : chiralBasis (Fin.natAdd 2 i) =
    ⟨0, DualRightHandedWeyl.basis i⟩ := by
  fin_cases i
  all_goals
    simp only [chiralBasis, Nat.reduceAdd, Basis.map_apply, Basis.coe_reindex,
    Function.comp_apply, Basis.prod_apply, LinearMap.coe_inl, LinearMap.coe_inr]
    rfl


-- @@ L113-117 verbatim
/-!

## The representation of the Lorentz group

-/


-- @@ L119-129 verbatim
/-- The representation of `SL(2, ℂ)` on Dirac fermions. -/
def rep : Representation ℂ SL(2,ℂ) Dirac where
  toFun g := decomposeLinEquiv.symm ∘ₗ
    (((LeftHandedWeyl.rep).prod (DualRightHandedWeyl.rep)) g) ∘ₗ
    decomposeLinEquiv
  map_one' := by
    ext1 i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp


-- @@ L131-132 verbatim
lemma rep_apply_mk (g : SL(2,ℂ)) (ψ : LeftHandedWeyl) (χ : DualRightHandedWeyl) :
    rep g ⟨ψ, χ⟩ = ⟨LeftHandedWeyl.rep g ψ, DualRightHandedWeyl.rep g χ⟩ := rfl


-- @@ L134-142 verbatim
/-- The equivalence between the representation on `Dirac` and the representation
  on `LeftHandedWeyl × DualRightHandedWeyl`. -/
def decomposeRepEquiv : rep.Equiv ((LeftHandedWeyl.rep).prod (DualRightHandedWeyl.rep))  where
  toLinearEquiv := decomposeLinEquiv
  isIntertwining' g := by
    ext1 x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Representation.prod_apply_apply]
    rfl


-- @@ L144-144 verbatim
end Dirac


-- @@ L146-146 verbatim
end

-- @@ L147-147 verbatim
end Fermion
