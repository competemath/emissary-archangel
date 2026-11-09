/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelIdempotent


-- @@ L10-23 verbatim
/-!
# Singular Kummer: exact finite-level projections for additive actions

This file applies the exact finite-level character idempotent to an additive
action.  If a finite group `D` acts on an additive group `A` by additive
automorphisms and `A` is viewed as a `ZMod m`-module, then a character

```text
  chi : D -> (ZMod m)^*
```

defines an exact finite-level projection.  Its range is the subgroup on which
the action has character `chi`.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace BernoulliRegular

-- @@ L30-30 verbatim
namespace Reflection

-- @@ L31-31 verbatim
namespace SingularKummer


-- @@ L33-33 verbatim
namespace FiniteLevelAdditiveProjection


-- @@ L35-35 verbatim
open FiniteLevelIdempotent


-- @@ L37-37 verbatim
variable {m : ℕ}

-- @@ L38-38 verbatim
variable {D A : Type*} [Group D] [Fintype D]

-- @@ L39-39 verbatim
variable [AddCommGroup A] [Module (ZMod m) A]


-- @@ L41-48 verbatim
/-- An additive equivalence is `ZMod m`-linear for the canonical `ZMod m`
module structure on an additive group. -/
def addEquivToZModLinearEquiv (e : A ≃+ A) :
    A ≃ₗ[ZMod m] A :=
  { e.toAddMonoidHom.toZModLinearMap m with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }


-- @@ L50-53 verbatim
@[simp]
theorem addEquivToZModLinearEquiv_apply (e : A ≃+ A) (x : A) :
    addEquivToZModLinearEquiv (m := m) e x = e x :=
  rfl


-- @@ L55-64 verbatim
/-- A group action by additive automorphisms, made linear over `ZMod m`. -/
def linearAction (rho : D →* Multiplicative (A ≃+ A)) :
    D →* A ≃ₗ[ZMod m] A where
  toFun d := addEquivToZModLinearEquiv (m := m) (Multiplicative.toAdd (rho d))
  map_one' := by
    ext x
    simp [addEquivToZModLinearEquiv]
  map_mul' a b := by
    ext x
    simp [addEquivToZModLinearEquiv, map_mul]


-- @@ L66-70 verbatim
omit [Fintype D] in
@[simp]
theorem linearAction_apply (rho : D →* Multiplicative (A ≃+ A)) (d : D) (x : A) :
    linearAction (m := m) rho d x = Multiplicative.toAdd (rho d) x :=
  rfl


-- @@ L72-76 verbatim
/-- The exact finite-level projection attached to an additive action and a
multiplicative character. -/
abbrev projection (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) :
    A →ₗ[ZMod m] A :=
  FiniteLevelIdempotent.projection (m := m) (linearAction (m := m) rho) chi


-- @@ L78-81 verbatim
/-- The additive subgroup cut out by the exact finite-level projection. -/
abbrev componentSubgroup (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) :
    AddSubgroup A :=
  (LinearMap.range (projection (m := m) rho chi)).toAddSubgroup


-- @@ L83-86 verbatim
/-- The same subgroup as a `ZMod m`-submodule. -/
abbrev componentSubmodule (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) :
    Submodule (ZMod m) A :=
  LinearMap.range (projection (m := m) rho chi)


-- @@ L88-92 verbatim
theorem mem_componentSubgroup_iff
    (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) {x : A} :
    x ∈ componentSubgroup (m := m) rho chi ↔
      x ∈ LinearMap.range (projection (m := m) rho chi) :=
  Iff.rfl


-- @@ L94-102 verbatim
/-- Elements in the exact projection subgroup satisfy the finite-level
character relation. -/
theorem apply_eq_character_smul_of_mem_component
    (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ)
    (d : D) {x : A}
    (hx : x ∈ componentSubgroup (m := m) rho chi) :
    Multiplicative.toAdd (rho d) x = (chi d : ZMod m) • x :=
  FiniteLevelIdempotent.mem_range_apply
    (m := m) (linearAction (m := m) rho) chi d hx


-- @@ L104-112 verbatim
/-- The exact finite-level projection acts as the identity on its own range. -/
theorem projection_apply_eq_self_of_mem_component
    (hcard : IsUnit (Fintype.card D : ZMod m))
    (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ)
    {x : A}
    (hx : x ∈ componentSubgroup (m := m) rho chi) :
    projection (m := m) rho chi x = x :=
  FiniteLevelIdempotent.projection_apply_eq_self_of_mem_range
    (m := m) hcard (linearAction (m := m) rho) chi hx


-- @@ L114-121 verbatim
/-- Idempotence of the exact finite-level additive projection. -/
theorem projection_apply_projection
    (hcard : IsUnit (Fintype.card D : ZMod m))
    (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) (x : A) :
    projection (m := m) rho chi (projection (m := m) rho chi x) =
      projection (m := m) rho chi x :=
  FiniteLevelIdempotent.projection_apply_projection
    (m := m) hcard (linearAction (m := m) rho) chi x


-- @@ L123-123 verbatim
end FiniteLevelAdditiveProjection


-- @@ L125-125 verbatim
end SingularKummer

-- @@ L126-126 verbatim
end Reflection

-- @@ L127-127 verbatim
end BernoulliRegular


-- @@ L129-129 verbatim
end


-- @@ L131-131 verbatim
end
