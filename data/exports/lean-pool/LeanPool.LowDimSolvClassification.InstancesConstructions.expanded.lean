/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
module

public import LeanPool.LowDimSolvClassification.Semidirect
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L13-15 verbatim
/-!
# LeanPool.LowDimSolvClassification.InstancesConstructions
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Module

-- @@ L20-23 verbatim
open Submodule

-- `LieRing.ofAssociativeRing` is a local instance in Mathlib (a `def`, not a global instance), so
-- we re-enable it locally to view associative rings (such as `K` and `End K V`) as Lie rings.

-- @@ L24-24 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L26-26 verbatim
namespace LieAlgebra


-- @@ L28-28 verbatim
section mkAbelian


-- @@ L30-34 verbatim
/-- The abelian Lie algebra constructed from a vector space by setting the bracket to zero.
The unused `Module K V` instance is consumed by `inferInstance` so the `unusedArguments` linter
accepts the definition; the result is still a synonym for `V`. -/
def mkAbelian (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] : Type _ :=
  (inferInstance : Module K V).toDistribMulAction.toMulAction.toSMul |> fun _ ↦ V


-- @@ L36-36 verbatim
variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]


-- @@ L38-40 verbatim
instance : Bracket (mkAbelian K V) (mkAbelian K V) := {
  bracket := fun _ _ ↦ (0 : V)
}


-- @@ L42-48 verbatim
instance : LieRing (mkAbelian K V) := {
  (inferInstance : AddCommGroup V) with
  add_lie := fun _ _ _ ↦ show (0 : V) = 0 + 0 by rw [add_zero]
  lie_add := fun _ _ _ ↦ show (0 : V) = 0 + 0 by rw [add_zero]
  lie_self := fun _ ↦ show (0 : V) = 0 from rfl
  leibniz_lie := fun _ _ _ ↦ show (0 : V) = 0 + 0 by rw [add_zero]
}


-- @@ L50-53 verbatim
instance : LieAlgebra K (mkAbelian K V) := {
  (inferInstance : Module K V) with
  lie_smul := fun _ _ _ ↦ show (0 : V) = (_ : K) • (0 : V) by rw [smul_zero]
}


-- @@ L55-56 verbatim
instance : IsLieAbelian (mkAbelian K V) :=
  ⟨fun _ _ ↦ rfl⟩


-- @@ L58-58 verbatim
end mkAbelian


-- @@ L60-60 verbatim
section abelianDerivation


-- @@ L62-70 verbatim
/-- TODO. -/
def _root_.LieAlgebra.Abelian.DerivationOfLinearMap' {K : Type*} [CommRing K] {L : Type*}
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : End K L) :
    LieDerivation K L L := {
  toLinearMap := f,
  leibniz' := by
    intro x y
    simp only [trivial_lie_zero, map_zero, sub_self]
}


-- @@ L72-100 verbatim
/-- If `L` is an abelian Lie algebra, any linear endomorphism of L is also a derivation of L. -/
def _root_.LieAlgebra.Abelian.DerivationOfLinearMap (K L : Type*) [CommRing K] [LieRing L]
    [LieAlgebra K L] [IsLieAbelian L] :
    End K L ≃ₗ⁅K⁆ LieDerivation K L L := {
  toFun := Abelian.DerivationOfLinearMap',
  map_add' := by
    intro f g
    ext x
    unfold Abelian.DerivationOfLinearMap'
    simp only [LieDerivation.mk_coe, LinearMap.add_apply, LieDerivation.coe_add, Pi.add_apply]
  map_smul' := by
    intro a f
    ext x
    unfold Abelian.DerivationOfLinearMap'
    simp only [LieDerivation.mk_coe, LinearMap.smul_apply, RingHom.id_apply, LieDerivation.coe_smul,
      Pi.smul_apply]
  map_lie' := by
    intro f g
    ext x
    change (f * g - g * f) x = f (g x) - g (f x)
    simp
  invFun := LieDerivation.toLinearMap
  left_inv := by
    intro f
    rfl
  right_inv := by
    intro f
    rfl
}


-- @@ L102-105 verbatim
@[simp]
theorem _root_.LieAlgebra.Abelian.DerivationCoeLinearMap {K : Type*} [CommRing K] {L : Type*}
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    (Abelian.DerivationOfLinearMap K L f).toLinearMap = f := rfl


-- @@ L107-110 verbatim
@[simp]
theorem _root_.LieAlgebra.Abelian.DerivationCoeFun {K : Type*} [CommRing K] {L : Type*}
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    ⇑(Abelian.DerivationOfLinearMap K L f) = ⇑f := rfl


-- @@ L112-115 verbatim
@[simp]
theorem _root_.LieAlgebra.Abelian.DerivationCoeFun' {K : Type*} [CommRing K] {L : Type*}
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    ⇑((Abelian.DerivationOfLinearMap K L).toLieHom f) = ⇑f := rfl


-- @@ L117-117 verbatim
end abelianDerivation


-- @@ L119-119 verbatim
section liealgofaffineequiv


-- @@ L121-121 verbatim
variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]


-- @@ L123-123 verbatim
example : LieAlgebra K (Module.End K V) := inferInstance


-- @@ L125-126 verbatim
/-- TODO. -/
def _root_.LieAlgebra.ofAffineEquivAux := (Abelian.DerivationOfLinearMap K (mkAbelian K V)).toLieHom


-- @@ L128-133 expanded
/-- The Lie algebra of the general affine group on a vector space `V`,
    constructed as semidirect product of `V →ₗ[K] V` with the abelian Lie algebra `V`. -/
abbrev _root_.LieAlgebra.OfAffineEquiv :=
  LieSemidirectProduct (Module.End K (mkAbelian K V)) (mkAbelian K V) (ofAffineEquivAux K V)


-- @@ L135-136 verbatim
@[inherit_doc]
notation "𝔞𝔣𝔣" => OfAffineEquiv


-- @@ L138-138 verbatim
end liealgofaffineequiv


-- @@ L140-140 verbatim
section liealghyperbolic


-- @@ L142-143 verbatim
variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] (L : Type*)
    [LieRing L] [LieAlgebra K L] [IsLieAbelian L]


-- @@ L145-147 verbatim
/-- TODO. -/
def _root_.LieAlgebra.RealHyperbolicAux' : K →ₗ⁅K⁆ LieDerivation K L L :=
  LieHom.comp (Abelian.DerivationOfLinearMap K L) (LieHom.smulRight (LinearMap.id : End K L))


-- @@ L149-151 verbatim
/-- TODO. -/
def _root_.LieAlgebra.RealHyperbolicAux : K →ₗ⁅K⁆ LieDerivation K (mkAbelian K V) (mkAbelian K V)
    := RealHyperbolicAux' K (mkAbelian K V)


-- @@ L153-155 expanded
/-- The almost abelian Lie algebra associated to real hyperbolic space,
  generalized to arbitrary `K`. -/
abbrev _root_.LieAlgebra.RealHyperbolic :=
  LieSemidirectProduct K (mkAbelian K V) (RealHyperbolicAux K V)


-- @@ L157-161 expanded
/-- The almost abelian Lie algebra associated to real hyperbolic `n`-space,
  generalized to arbitrary `K`. -/
abbrev _root_.LieAlgebra.RealHyperbolic' (n : ℕ) (K : Type*) [CommRing K] :=
  LieSemidirectProduct K
    (mkAbelian K (Fin (n - 1) → K))
      --requires n > 0
      
    (RealHyperbolicAux K (Fin (n - 1) → K))


-- @@ L163-164 verbatim
@[inherit_doc]
notation "𝔥𝔶𝔭" => RealHyperbolic'


-- @@ L166-166 verbatim
end liealghyperbolic


-- @@ L168-168 verbatim
end LieAlgebra
