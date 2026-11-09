/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.SingularKummer.ElementaryQuotientComponent
public import BernoulliRegular.Reflection.SingularKummer.ProjectedSubgroupComparison


-- @@ L11-22 verbatim
/-!
# Singular Kummer: integral lifts of character projections

The character projection on `A / pA` and on `A[p]` has coefficients in
`ZMod p`.  To apply the finite-group comparison to an actual subgroup of `A`,
we use the integer lift obtained by replacing each coefficient by its standard
representative in `ℕ`.

This file defines that lift and proves that, after passing to `A / pA` or
restricting to `A[p]`, it recovers the corresponding `ZMod p` character
projection.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace BernoulliRegular

-- @@ L29-29 verbatim
namespace Reflection

-- @@ L30-30 verbatim
namespace SingularKummer


-- @@ L32-32 verbatim
namespace IntegralCharacterProjection


-- @@ L34-34 verbatim
open ElementaryQuotientComponent

-- @@ L35-35 verbatim
open TorsionComponent


-- @@ L37-37 verbatim
variable {p : ℕ} [NeZero p]

-- @@ L38-38 verbatim
variable {A : Type*} [AddCommGroup A]


-- @@ L40-46 verbatim
/-- The integer-coefficient lift of the `i`-th character projection. -/
def integralProjection
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    A →+ A :=
  ∑ d : CharacterProjection.Delta p,
    (CharacterProjection.characterProjectionCoefficient (p := p) i d).val •
      (Multiplicative.toAdd (ρ d)).toAddMonoidHom


-- @@ L48-55 verbatim
@[simp]
theorem integralProjection_apply
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) (x : A) :
    integralProjection (p := p) i ρ x =
      ∑ d : CharacterProjection.Delta p,
        (CharacterProjection.characterProjectionCoefficient (p := p) i d).val •
          (Multiplicative.toAdd (ρ d)) x := by
  simp [integralProjection]


-- @@ L57-61 verbatim
/-- The finite subgroup of `A` obtained as the range of the integer lift. -/
abbrev integralComponentSubgroup
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    AddSubgroup A :=
  (integralProjection (p := p) i ρ).range


-- @@ L63-69 verbatim
/-- The integer lift induces the usual character projection on `A / pA`. -/
theorem quotientMap_integralProjection
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) (x : A) :
    quotientMap A p (integralProjection (p := p) i ρ x) =
      elementaryProjection (p := p) i ρ (quotientMap A p x) := by
  simp [integralProjection, CharacterProjection.characterProjection,
    CharacterProjection.projection]


-- @@ L71-78 verbatim
/-- On `A[p]`, the integer lift is the usual torsion character projection. -/
theorem torsionProjection_apply_coe
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (x : PTorsion A p) :
    ((torsionProjection (p := p) i ρ x : PTorsion A p) : A) =
      integralProjection (p := p) i ρ x.1 := by
  simp [integralProjection, torsionProjection, CharacterProjection.characterProjection,
    CharacterProjection.projection]


-- @@ L80-80 verbatim
end IntegralCharacterProjection


-- @@ L82-82 verbatim
end SingularKummer

-- @@ L83-83 verbatim
end Reflection

-- @@ L84-84 verbatim
end BernoulliRegular


-- @@ L86-86 verbatim
end


-- @@ L88-88 verbatim
end
