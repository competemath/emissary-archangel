/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionEigen
public import BernoulliRegular.Reflection.SingularKummer.FiniteGroupComparison


-- @@ L11-26 verbatim
/-!
# Singular Kummer: elementary quotient components

This file defines the elementary quotient

```text
  V = A / pA
```

for an additive abelian group `A`, equips it with its natural `ZMod p`-module
structure, and transports a `Delta = (ZMod p)ˣ` action on `A` to a linear
action on `V`.

The `i`-th component of `V` is the range of the same character projection used
elsewhere in the singular-Kummer argument.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace BernoulliRegular

-- @@ L33-33 verbatim
namespace Reflection

-- @@ L34-34 verbatim
namespace SingularKummer


-- @@ L36-36 verbatim
namespace ElementaryQuotientComponent


-- @@ L38-38 verbatim
variable {p : ℕ}

-- @@ L39-39 verbatim
variable {A : Type*} [AddCommGroup A]


-- @@ L41-43 verbatim
/-- The elementary quotient `V = A / pA`. -/
abbrev ElementaryQuotient (A : Type*) [AddCommGroup A] (p : ℕ) : Type _ :=
  elementaryQuotient A p


-- @@ L45-48 verbatim
/-- The quotient map `A -> A / pA`. -/
def quotientMap (A : Type*) [AddCommGroup A] (p : ℕ) :
    A →+ ElementaryQuotient A p :=
  QuotientAddGroup.mk' (multiplesSubgroup A p)


-- @@ L50-53 verbatim
@[simp]
theorem quotientMap_apply (p : ℕ) (x : A) :
    quotientMap A p x = (QuotientAddGroup.mk x : ElementaryQuotient A p) :=
  rfl


-- @@ L55-59 verbatim
/-- The quotient map `A -> A / pA` is surjective. -/
theorem quotientMap_surjective (p : ℕ) :
    Function.Surjective (quotientMap A p) := by
  simpa [quotientMap, ElementaryQuotient] using
    QuotientAddGroup.mk'_surjective (multiplesSubgroup A p)


-- @@ L61-66 verbatim
/-- The quotient `A / pA` is naturally a `ZMod p`-module. -/
instance instModuleZModElementaryQuotient :
    Module (ZMod p) (ElementaryQuotient A p) :=
  QuotientAddGroup.zmodModule (n := p) (H := multiplesSubgroup A p) (by
    intro x
    exact ⟨x, rfl⟩)


-- @@ L68-76 verbatim
/-- An additive equivalence of `A` preserves the subgroup `pA`. -/
theorem multiplesSubgroup_le_comap_addEquiv
    (p : ℕ) (e : A ≃+ A) :
    multiplesSubgroup A p ≤
      (multiplesSubgroup A p).comap e.toAddMonoidHom := by
  rintro x ⟨y, rfl⟩
  change e (p • y) ∈ multiplesSubgroup A p
  rw [map_nsmul]
  exact ⟨e y, rfl⟩


-- @@ L78-98 verbatim
/-- An additive equivalence of `A` induces an additive equivalence of
`A / pA`. -/
def quotientAddEquiv (p : ℕ) (e : A ≃+ A) :
    ElementaryQuotient A p ≃+
      ElementaryQuotient A p where
  toFun :=
    QuotientAddGroup.map (multiplesSubgroup A p) (multiplesSubgroup A p)
      e.toAddMonoidHom (multiplesSubgroup_le_comap_addEquiv p e)
  invFun :=
    QuotientAddGroup.map (multiplesSubgroup A p) (multiplesSubgroup A p)
      e.symm.toAddMonoidHom (multiplesSubgroup_le_comap_addEquiv p e.symm)
  left_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on
    simp [QuotientAddGroup.map_mk]
  right_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on
    simp [QuotientAddGroup.map_mk]
  map_add' := fun x y =>
    map_add _ x y


-- @@ L100-105 verbatim
@[simp]
theorem quotientAddEquiv_mk (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientAddEquiv p e
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk (e x) :=
  rfl


-- @@ L107-115 verbatim
/-- An additive equivalence of `A` induces a `ZMod p`-linear equivalence of
`A / pA`. -/
def quotientLinearEquiv (p : ℕ) (e : A ≃+ A) :
    ElementaryQuotient A p ≃ₗ[ZMod p]
      ElementaryQuotient A p :=
  { (quotientAddEquiv p e).toAddMonoidHom.toZModLinearMap p with
    invFun := quotientAddEquiv p e.symm
    left_inv := (quotientAddEquiv p e).left_inv
    right_inv := (quotientAddEquiv p e).right_inv }


-- @@ L117-122 verbatim
@[simp]
theorem quotientLinearEquiv_mk (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientLinearEquiv p e
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk (e x) :=
  rfl


-- @@ L124-128 verbatim
@[simp]
theorem quotientLinearEquiv_quotientMap (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientLinearEquiv p e (quotientMap A p x) =
      quotientMap A p (e x) :=
  rfl


-- @@ L130-137 verbatim
@[simp]
theorem zmod_smul_eq_val_nsmul [NeZero p]
    (a : ZMod p) (x : ElementaryQuotient A p) :
    a • x = a.val • x := by
  calc
    a • x = (a.val : ZMod p) • x := by
      rw [ZMod.natCast_zmod_val a]
    _ = a.val • x := Nat.cast_smul_eq_nsmul (ZMod p) a.val x


-- @@ L139-152 verbatim
/-- A `Delta` action on `A` induces a linear `Delta` action on `V = A / pA`. -/
def elementaryQuotientAction [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    CharacterProjection.Delta p →*
      ElementaryQuotient A p ≃ₗ[ZMod p] ElementaryQuotient A p where
  toFun d := quotientLinearEquiv p (Multiplicative.toAdd (ρ d))
  map_one' := by
    ext x
    induction x using QuotientAddGroup.induction_on
    simp [quotientLinearEquiv]
  map_mul' a b := by
    ext x
    induction x using QuotientAddGroup.induction_on
    simp [quotientLinearEquiv, map_mul]


-- @@ L154-162 verbatim
/-- The induced `Delta` action on `A / pA` is the quotient of the action on
`A`. -/
@[simp]
theorem elementaryQuotientAction_quotientMap [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p) (x : A) :
    elementaryQuotientAction (p := p) ρ d (quotientMap A p x) =
      quotientMap A p ((Multiplicative.toAdd (ρ d)) x) :=
  rfl


-- @@ L164-171 verbatim
@[simp]
theorem elementaryQuotientAction_mk [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p) (x : A) :
    elementaryQuotientAction (p := p) ρ d
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk ((Multiplicative.toAdd (ρ d)) x) :=
  rfl


-- @@ L173-178 verbatim
/-- The character projection acting on the elementary quotient `V = A / pA`. -/
abbrev elementaryProjection [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    ElementaryQuotient A p →ₗ[ZMod p] ElementaryQuotient A p :=
  CharacterProjection.characterProjection (p := p) i
    (elementaryQuotientAction (p := p) ρ)


-- @@ L180-184 verbatim
/-- The `i`-th component of `V = A / pA`. -/
abbrev elementaryComponent [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    Submodule (ZMod p) (ElementaryQuotient A p) :=
  LinearMap.range (elementaryProjection (p := p) i ρ)


-- @@ L186-190 verbatim
theorem elementaryComponent_eq_range_projection [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    elementaryComponent (p := p) i ρ =
      LinearMap.range (elementaryProjection (p := p) i ρ) :=
  rfl


-- @@ L192-198 verbatim
theorem mem_elementaryComponent_iff_exists [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    {x : ElementaryQuotient A p} :
    x ∈ elementaryComponent (p := p) i ρ ↔
      ∃ y : ElementaryQuotient A p,
        elementaryProjection (p := p) i ρ y = x :=
  Iff.rfl


-- @@ L200-203 verbatim
/-- Nontriviality of the `i`-th component of `V = A / pA`. -/
def ElementaryComponentNontrivial [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) : Prop :=
  elementaryComponent (p := p) i ρ ≠ ⊥


-- @@ L205-212 verbatim
theorem exists_ne_zero_mem_elementaryComponent [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    (h : ElementaryComponentNontrivial (p := p) i ρ) :
    ∃ x : ElementaryQuotient A p,
      x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ := by
  obtain ⟨x, hxmem, hxne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨x, hxne, hxmem⟩


-- @@ L214-221 verbatim
theorem elementaryComponentNontrivial_of_exists_ne_zero_mem [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    (h : ∃ x : ElementaryQuotient A p,
      x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ) :
    ElementaryComponentNontrivial (p := p) i ρ := by
  obtain ⟨x, hxne, hxmem⟩ := h
  rw [ElementaryComponentNontrivial]
  exact (Submodule.ne_bot_iff _).2 ⟨x, hxmem, hxne⟩


-- @@ L223-229 verbatim
theorem elementaryComponentNontrivial_iff_exists_ne_zero_mem [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    ElementaryComponentNontrivial (p := p) i ρ ↔
      ∃ x : ElementaryQuotient A p,
        x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ :=
  ⟨exists_ne_zero_mem_elementaryComponent,
    elementaryComponentNontrivial_of_exists_ne_zero_mem⟩


-- @@ L231-231 verbatim
end ElementaryQuotientComponent


-- @@ L233-233 verbatim
end SingularKummer

-- @@ L234-234 verbatim
end Reflection

-- @@ L235-235 verbatim
end BernoulliRegular


-- @@ L237-237 verbatim
end


-- @@ L239-239 verbatim
end
