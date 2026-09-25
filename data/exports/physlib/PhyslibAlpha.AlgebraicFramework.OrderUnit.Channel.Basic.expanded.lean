/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.Complex.Basic


-- @@ L11-39 verbatim
/-!

# Channels

## i. Overview

A channel from system `A` to system `B` is, in the Schrödinger picture, an affine map on states.
Dualizing gives a unital positive linear map on effects in the other direction (the Heisenberg
picture): `UnitalPositiveLinearMap` is exactly that dual, and `E₁ →ₚ₁[R] E₂` reads as "the
adjoint of a channel `A → B`" whenever `E₁`, `E₂` are the effect algebras of `A`, `B`.

## ii. Key definitions and results

- `UnitalPositiveLinearMap` is the type of positive linear maps that preserve `1`.
- `E₁ →ₚ₁[R] E₂` is notation for it.
- Endomorphisms `E →ₚ₁[R] E` form a monoid under composition.

## iii. Table of contents

- A. Unital positive linear maps
- B. Constructors
- C. Coercions and extensionality
- D. Identity and composition

## Implementation details

We follow the implementation of `PositiveLinearMap` closely.

-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
section UnitalPositiveLinearMap


-- @@ L45-45 verbatim
/-! ## A. Unital positive linear maps -/


-- @@ L47-52 verbatim
/-- A positive linear map that preserves `1`. -/
structure UnitalPositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [One E₁] [One E₂] extends E₁ →ₚ[R] E₂, OneHom E₁ E₂

-- The inherited `OneHom` projection has no separately attachable docstring.

-- @@ L53-53 verbatim
attribute [nolint docBlame] UnitalPositiveLinearMap.toOneHom


-- @@ L55-56 verbatim
/-- Notation for unital positive linear maps. -/
notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F


-- @@ L58-58 verbatim
section UnitalPositiveLinearMapClass


-- @@ L60-60 verbatim
/-! ## B. Constructors -/


-- @@ L62-65 verbatim
variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂] [One E₁] [One E₂] [OneHomClass F E₁ E₂]


-- @@ L67-69 expanded
/-- Bundle a positive, unital linear map satisfying the relevant typeclass assumptions. -/
def UnitalPositiveLinearMap.ofClass (f : F) : UnitalPositiveLinearMap R E₁ E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂), (f : OneHom E₁ E₂) with }


-- @@ L71-71 verbatim
end UnitalPositiveLinearMapClass


-- @@ L73-73 verbatim
namespace UnitalPositiveLinearMap


-- @@ L75-78 verbatim
variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂]
  [Module R E₁] [Module R E₂] [One E₁] [One E₂]


-- @@ L80-84 expanded
/-- Bundle a linear map after proving only positivity and preservation of `1`. -/
def ofLinearMap (f : E₁ →ₗ[R] E₂) (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) (hone : f 1 = 1) :
    UnitalPositiveLinearMap R E₁ E₂
    where
  toPositiveLinearMap := PositiveLinearMap.mk₀ f hpos
  map_one' := hone


-- @@ L86-86 verbatim
end UnitalPositiveLinearMap


-- @@ L88-88 verbatim
namespace UnitalPositiveLinearMap


-- @@ L90-90 verbatim
/-! ## C. Coercions and extensionality -/


-- @@ L92-98 verbatim
variable {R E₁ E₂ E₃ E₄ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [AddCommMonoid E₃] [PartialOrder E₃]
    [AddCommMonoid E₄] [PartialOrder E₄]
    [Module R E₁] [Module R E₂] [Module R E₃] [Module R E₄]
    [One E₁] [One E₂] [One E₃] [One E₄]


-- @@ L100-107 expanded
instance : FunLike (UnitalPositiveLinearMap R E₁ E₂) E₁ E₂
    where
  coe f := f.toFun
  coe_injective f g
    h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h


-- @@ L109-111 expanded
instance : LinearMapClass (UnitalPositiveLinearMap R E₁ E₂) R E₁ E₂
    where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'


-- @@ L113-114 expanded
instance : OrderHomClass (UnitalPositiveLinearMap R E₁ E₂) E₁ E₂ where
  map_rel f {_ _} hab := f.monotone' hab


-- @@ L116-117 expanded
instance : OneHomClass (UnitalPositiveLinearMap R E₁ E₂) E₁ E₂ where map_one f := f.map_one'


-- @@ L119-119 expanded
example (f : UnitalPositiveLinearMap R E₁ E₂) : f 1 = 1 := by simp


-- @@ L121-123 expanded
@[simp]
lemma coe_toPositiveLinearMap (f : UnitalPositiveLinearMap R E₁ E₂) :
    (f.toPositiveLinearMap : E₁ → E₂) = f :=
  rfl


-- @@ L125-126 expanded
example (f : UnitalPositiveLinearMap R E₁ E₂) : f.toLinearMap 1 = 1 := by simp


-- @@ L128-128 verbatim
initialize_simps_projections UnitalPositiveLinearMap (toFun → apply, as_prefix toLinearMap)


-- @@ L130-132 expanded
@[ext]
lemma ext {f g : UnitalPositiveLinearMap R E₁ E₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h


-- @@ L134-139 expanded
variable (R E₁) in
/-- The identity as a positive linear one-preserving map. -/
@[simps! apply toLinearMap]
protected def id : UnitalPositiveLinearMap R E₁ E₁
    where
  __ := LinearMap.id
  __ := OrderHom.id
  __ := OneHom.id E₁


-- @@ L141-141 verbatim
@[simp] lemma toOrderHom_id : (UnitalPositiveLinearMap.id R E₁).toOrderHom = .id := rfl

-- @@ L142-142 verbatim
@[simp] lemma toOneHom_id : (UnitalPositiveLinearMap.id R E₁).toOneHom = .id E₁ := rfl


-- @@ L144-144 verbatim
/-! ## D. Identity and composition -/


-- @@ L146-151 expanded
/-- Composition of positive linear one-preserving maps. -/
@[simps! apply]
def comp (g : UnitalPositiveLinearMap R E₂ E₃) (f : UnitalPositiveLinearMap R E₁ E₂) :
    UnitalPositiveLinearMap R E₁ E₃
    where
  toLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  monotone' := g.monotone'.comp f.monotone'
  map_one' := by simp


-- @@ L153-157 expanded
/-- Composition of unital positive linear maps is associative. -/
lemma comp_assoc (h : UnitalPositiveLinearMap R E₃ E₄) (g : UnitalPositiveLinearMap R E₂ E₃)
    (f : UnitalPositiveLinearMap R E₁ E₂) : (h.comp g).comp f = h.comp (g.comp f) :=
  by
  ext x
  simp


-- @@ L159-161 expanded
@[simp]
lemma toPositiveLinearMap_comp (g : UnitalPositiveLinearMap R E₂ E₃)
    (f : UnitalPositiveLinearMap R E₁ E₂) :
    (g.comp f).toPositiveLinearMap = g.toPositiveLinearMap.comp f.toPositiveLinearMap :=
  rfl


-- @@ L163-165 expanded
@[simp]
lemma toOrderHom_comp (g : UnitalPositiveLinearMap R E₂ E₃) (f : UnitalPositiveLinearMap R E₁ E₂) :
    (g.comp f).toOrderHom = g.toOrderHom.comp f.toOrderHom :=
  rfl


-- @@ L167-167 expanded
@[simp]
lemma comp_id (f : UnitalPositiveLinearMap R E₁ E₂) : f.comp (.id R E₁) = f :=
  rfl


-- @@ L168-168 expanded
@[simp]
lemma id_comp (f : UnitalPositiveLinearMap R E₁ E₂) :
    (UnitalPositiveLinearMap.id R E₂).comp f = f :=
  rfl


-- @@ L170-176 expanded
/-- Unital positive endomorphisms form a monoid under composition. -/
instance instMonoid : Monoid (UnitalPositiveLinearMap R E₁ E₁)
    where
  one := .id R E₁
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc


-- @@ L178-178 expanded
@[simp]
lemma one_apply (x : E₁) : (1 : UnitalPositiveLinearMap R E₁ E₁) x = x :=
  rfl


-- @@ L180-180 expanded
@[simp]
lemma mul_apply (f g : UnitalPositiveLinearMap R E₁ E₁) (x : E₁) : (f * g) x = f (g x) :=
  rfl


-- @@ L182-185 expanded
@[simp]
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂] [LinearMap.CompatibleSMul E₁ E₂ S R]
    (f : UnitalPositiveLinearMap R E₁ E₂) (c : S) (x : E₁) : f (c • x) = c • f x :=
  LinearMapClass.map_smul_of_tower f _ _


-- @@ L187-189 expanded
@[aesop safe apply (rule_sets := [CStarAlgebra])]
protected lemma map_nonneg (f : UnitalPositiveLinearMap R E₁ E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  map_nonneg f hx


-- @@ L191-193 unexpanded
lemma toPositiveLinearMap_injective :
    Function.Injective (toPositiveLinearMap : (E₁ →ₚ₁[R] E₂) → (E₁ →ₚ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)


-- @@ L195-201 expanded
/-- Unital positive linear maps are determined by their underlying linear maps. -/
lemma toLinearMap_injective :
    Function.Injective (fun f : UnitalPositiveLinearMap R E₁ E₂ => f.toLinearMap) :=
  by
  intro f g h
  ext x
  exact congrArg (fun k : E₁ →ₗ[R] E₂ => k x) h


-- @@ L203-206 expanded
@[simp]
lemma toPositiveLinearMap_inj {f g : UnitalPositiveLinearMap R E₁ E₂} :
    f.toPositiveLinearMap = g.toPositiveLinearMap ↔ f = g :=
  toPositiveLinearMap_injective.eq_iff

