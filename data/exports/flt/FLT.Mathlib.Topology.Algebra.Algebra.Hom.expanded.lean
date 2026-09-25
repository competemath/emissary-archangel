/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import FLT.Mathlib.Algebra.Algebra.Hom
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor


-- @@ L15-19 verbatim
/-!
# Hom

Material destined for Mathlib.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-29 verbatim
/-- A `SemialgHom` (i.e., `ψ` such that `ψ (r • a) = φ r • ψ a` for some `φ : R →+* S`) that
is also continuous. -/
structure ContinuousSemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (A B : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends SemialgHom φ A B where
  continuous_toFun : Continuous toFun


-- @@ L31-32 verbatim
@[inherit_doc ContinuousSemialgHom]
infixr:25 " →SA " => ContinuousSemialgHom _


-- @@ L34-35 verbatim
@[inherit_doc]
notation:25 A " →SA[" φ:25 "] " B:0 => ContinuousSemialgHom φ A B


-- @@ L37-42 verbatim
/-- `ContinuousSemialgHomClass F φ A B` states that `F` is the type of continuous semi-algebra
maps from `A` to `B` with respect to `φ`. -/
class ContinuousSemialgHomClass (F : Type*) {R S : outParam Type*}
    [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [TopologicalSpace A] [TopologicalSpace B]
    [FunLike F A B] extends SemialgHomClass F φ A B where continuous_toFun (f : F) : Continuous f


-- @@ L44-44 verbatim
namespace ContinuousSemialgHom


-- @@ L46-48 verbatim
variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [TopologicalSpace A] [TopologicalSpace B]


-- @@ L50-56 expanded
instance instFunLike : FunLike (ContinuousSemialgHom φ A B) A B
    where
  coe f := f.toFun
  coe_injective f g
    h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h


-- @@ L58-59 expanded
instance : CoeOut (ContinuousSemialgHom φ A B) (SemialgHom φ A B) :=
  ⟨fun f => f.toSemialgHom⟩


-- @@ L61-63 verbatim
variable (F : Type*) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [TopologicalSpace A] [TopologicalSpace B] [ContinuousSemialgHomClass F φ A B]


-- @@ L65-71 expanded
instance : ContinuousSemialgHomClass (ContinuousSemialgHom φ A B) φ A B
    where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero
  continuous_toFun ψ := ψ.continuous_toFun


-- @@ L73-77 expanded
variable {F} {φ} {A} {B} in
/-- Turn an element of `F` which satisfies `ContinuousSemialgHomClass F φ A B` to a
`ContinuousSemialgHom`. -/
def _root_.ContinuousSemialgHomClass.toContinuousSemialgHom (f : F) : ContinuousSemialgHom φ A B :=
  { (f : SemialgHom φ A B) with continuous_toFun := ContinuousSemialgHomClass.continuous_toFun f }


-- @@ L79-80 expanded
instance : CoeTC F (ContinuousSemialgHom φ A B) :=
  ⟨ContinuousSemialgHomClass.toContinuousSemialgHom⟩


-- @@ L82-84 expanded
@[simp]
theorem coe_coe (f : F) : ⇑(f : ContinuousSemialgHom φ A B) = f :=
  rfl


-- @@ L86-87 expanded
theorem toSemialgHom_eq_coe (f : ContinuousSemialgHom φ A B) : f.toSemialgHom = f :=
  rfl


-- @@ L89-91 expanded
@[simp]
theorem toLinearMap_eq_coe (f : ContinuousSemialgHom φ A B) : f.toLinearMap = f := by rfl


-- @@ L93-95 expanded
@[simp]
theorem toRingHom_eq_coe (f : ContinuousSemialgHom φ A B) : f.toRingHom = f :=
  rfl


-- @@ L97-99 expanded
theorem commutes (ψ : ContinuousSemialgHom φ A B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) :=
  ψ.toSemialgHom.commutes r


-- @@ L101-106 expanded
/-- The product of two continuous semi-algebra isomorphisms on the same domain. -/
def prod {C : Type*} [Semiring C] [Algebra S C] [TopologicalSpace C]
    (f : ContinuousSemialgHom φ A B) (g : ContinuousSemialgHom φ A C) :
    ContinuousSemialgHom φ A (B × C)
    where
  __ := f.toSemialgHom.prod g.toSemialgHom
  continuous_toFun := f.continuous_toFun.prodMk g.continuous_toFun


-- @@ L108-114 expanded
variable {φ A B} in
/-- the product of two continuous semi-algebra isomorphisms on different domains. -/
def prodMap {C D : Type*} [Semiring C] [Semiring D] [Algebra S C] [Algebra S D] [TopologicalSpace C]
    [TopologicalSpace D] [Algebra R B] (f : ContinuousSemialgHom φ A C)
    (g : ContinuousSemialgHom φ B D) : ContinuousSemialgHom φ (A × B) (C × D)
    where
  __ := SemialgHom.prodMap f g
  continuous_toFun := Continuous.prodMap f.continuous_toFun g.continuous_toFun


-- @@ L116-116 verbatim
end ContinuousSemialgHom
