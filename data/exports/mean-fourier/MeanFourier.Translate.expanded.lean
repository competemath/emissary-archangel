/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Util.Notation3
public import MeanFourier.Mathlib.Topology.Bornology.Basic


-- @@ L12-14 verbatim
/-!
# Translating functions
-/


-- @@ L16-16 verbatim
public section


-- @@ L18-18 verbatim
namespace Function

-- @@ L19-19 verbatim
variable {G α M : Type*} [Group G] {x : G} {f : G → α}


-- @@ L21-23 verbatim
/-- Left-translation of a function: `τ_[x] f y := f (x⁻¹ * y)`. -/
@[expose]
def translate (x : G) (f : G → α) : G → α := fun y ↦ f (x⁻¹ * y)


-- @@ L25-25 verbatim
@[inherit_doc translate] notation3 "τ_[" x "]" => translate x


-- @@ L27-27 expanded
@[simp]
lemma translate_apply (x : G) (f : G → α) (y : G) : (translate x) f y = f (x⁻¹ * y) :=
  rfl


-- @@ L29-29 expanded
@[simp]
lemma translate_one (f : G → α) : (translate 1) f = f := by ext; simp


-- @@ L30-34 expanded
@[simp]
lemma translate_translate (x y : G) (f : G → α) :
    (translate x) ((translate y) f) = (translate (x * y)) f := by ext;
  simp [mul_assoc]
    -- TODO: Move the `attribute [local push] Function.const_def` from `Mathlib.Order.ScottContinuity`
    -- to an earlier file.


-- @@ L35-36 expanded
@[to_fun (attr := simp) translate_fun_const]
lemma translate_const (x : G) (a : α) : (translate x) (const G a) = const G a :=
  rfl


-- @@ L38-39 expanded
@[to_additive (attr := simp) (dont_translate := G)]
lemma translate_one_fun [One M] (x : G) : (translate x) (1 : G → M) = 1 :=
  rfl


-- @@ L41-42 expanded
@[to_additive (attr := simp) (dont_translate := G)]
lemma translate_mul_fun [Mul M] (x : G) (f g : G → M) :
    (translate x) (f * g) = (translate x) f * (translate x) g :=
  rfl


-- @@ L44-45 expanded
@[simp]
lemma range_translate (x : G) (f : G → α) : Set.range ((translate x) f) = .range f := by ext a;
  exact (Equiv.mulLeft x⁻¹).exists_congr (by simp)


-- @@ L47-47 verbatim
end Function


-- @@ L49-49 verbatim
namespace Bornology

-- @@ L50-50 verbatim
variable {G X : Type*} [Group G] [Bornology X] {x : G} {f : G → X}


-- @@ L52-52 expanded
@[simp]
lemma isBddFun_translate : IsBddFun ((translate x) f) ↔ IsBddFun f := by simp [IsBddFun]


-- @@ L54-54 verbatim
protected alias ⟨_, IsBddFun.translate⟩ := isBddFun_translate


-- @@ L56-56 verbatim
end Bornology
