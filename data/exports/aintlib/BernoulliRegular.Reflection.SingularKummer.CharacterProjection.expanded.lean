module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Equiv.Basic
public import BernoulliRegular.Reflection.SingularKummer.ComponentProjection


-- @@ L7-16 verbatim
/-!
# Singular Kummer: additive character projections

This file records the additive linear algebra used for the character-component
part of the singular-Kummer argument.  For a `ZMod p`-module with a linear action of
`Delta = (ZMod p)ˣ`, a character projection is a finite `ZMod p`-linear
combination of the action operators.  Any equivariant linear map commutes with
these projections, and a surjective equivariant map maps the source projection
range onto the target projection range.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace BernoulliRegular

-- @@ L23-23 verbatim
namespace Reflection

-- @@ L24-24 verbatim
namespace SingularKummer


-- @@ L26-26 verbatim
namespace CharacterProjection


-- @@ L28-28 verbatim
variable (p : ℕ)


-- @@ L30-33 verbatim
/-- The cyclotomic Galois group in the explicit model used for character
indices. -/
abbrev Delta : Type :=
  (ZMod p)ˣ


-- @@ L35-35 verbatim
variable {p}

-- @@ L36-36 verbatim
variable [NeZero p]

-- @@ L37-37 verbatim
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

-- @@ L38-38 verbatim
variable [Module (ZMod p) M] [Module (ZMod p) N]


-- @@ L40-46 verbatim
/-- A finite linear combination of the operators in a `Delta`-action.  The
standard character projection is obtained by using the usual character
coefficients. -/
def projection
    (ρ : Delta p →* M ≃ₗ[ZMod p] M) (c : Delta p → ZMod p) :
    M →ₗ[ZMod p] M :=
  ∑ a : Delta p, c a • (ρ a : M →ₗ[ZMod p] M)


-- @@ L48-53 verbatim
@[simp]
theorem projection_apply
    (ρ : Delta p →* M ≃ₗ[ZMod p] M) (c : Delta p → ZMod p) (x : M) :
    projection (p := p) ρ c x =
      ∑ a : Delta p, c a • ρ a x := by
  simp [projection]


-- @@ L55-58 verbatim
/-- Coefficients for the `i`-th character projection.  The coefficient attached
to `a` is `|Delta|⁻¹ a⁻ᶦ`, with values in `ZMod p`. -/
def characterProjectionCoefficient (i : ℕ) (a : Delta p) : ZMod p :=
  (Fintype.card (Delta p) : ZMod p)⁻¹ * (((a⁻¹ : Delta p) : ZMod p) ^ i)


-- @@ L60-64 verbatim
/-- The finite-sum projection attached to the `i`-th character. -/
def characterProjection
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) :
    M →ₗ[ZMod p] M :=
  projection (p := p) ρ (characterProjectionCoefficient (p := p) i)


-- @@ L66-75 verbatim
/-- Equivariant linear maps commute with every finite-sum projection. -/
theorem map_projection_apply
    (ρM : Delta p →* M ≃ₗ[ZMod p] M)
    (ρN : Delta p →* N ≃ₗ[ZMod p] N)
    (f : M →ₗ[ZMod p] N)
    (hf : ∀ (a : Delta p) (x : M), f (ρM a x) = ρN a (f x))
    (c : Delta p → ZMod p) (x : M) :
    f (projection (p := p) ρM c x) =
      projection (p := p) ρN c (f x) := by
  simp [projection, hf]


-- @@ L77-88 verbatim
/-- Commutation of an equivariant linear map with a finite-sum projection,
as an equality of linear maps. -/
theorem projection_commute
    (ρM : Delta p →* M ≃ₗ[ZMod p] M)
    (ρN : Delta p →* N ≃ₗ[ZMod p] N)
    (f : M →ₗ[ZMod p] N)
    (hf : ∀ (a : Delta p) (x : M), f (ρM a x) = ρN a (f x))
    (c : Delta p → ZMod p) :
    f.comp (projection (p := p) ρM c) =
      (projection (p := p) ρN c).comp f := by
  ext x
  exact map_projection_apply (p := p) ρM ρN f hf c x


-- @@ L90-102 verbatim
/-- A surjective equivariant linear map maps the range of a source projection
onto the range of the matching target projection. -/
theorem map_projection_range_eq_range_of_surjective
    (ρM : Delta p →* M ≃ₗ[ZMod p] M)
    (ρN : Delta p →* N ≃ₗ[ZMod p] N)
    (f : M →ₗ[ZMod p] N)
    (hf_surj : Function.Surjective f)
    (hf : ∀ (a : Delta p) (x : M), f (ρM a x) = ρN a (f x))
    (c : Delta p → ZMod p) :
    Submodule.map f (LinearMap.range (projection (p := p) ρM c)) =
      LinearMap.range (projection (p := p) ρN c) := by
  rw [← LinearMap.range_comp, projection_commute (p := p) ρM ρN f hf c]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hf_surj)


-- @@ L104-117 verbatim
/-- The previous range-surjectivity statement for the standard `i`-th
character projection. -/
theorem map_characterProjection_range_eq_range_of_surjective
    (i : ℕ)
    (ρM : Delta p →* M ≃ₗ[ZMod p] M)
    (ρN : Delta p →* N ≃ₗ[ZMod p] N)
    (f : M →ₗ[ZMod p] N)
    (hf_surj : Function.Surjective f)
    (hf : ∀ (a : Delta p) (x : M), f (ρM a x) = ρN a (f x)) :
    Submodule.map f (LinearMap.range (characterProjection (p := p) i ρM)) =
      LinearMap.range (characterProjection (p := p) i ρN) :=
  map_projection_range_eq_range_of_surjective
    (p := p) ρM ρN f hf_surj hf
    (characterProjectionCoefficient (p := p) i)


-- @@ L119-119 verbatim
end CharacterProjection


-- @@ L121-121 verbatim
end SingularKummer

-- @@ L122-122 verbatim
end Reflection

-- @@ L123-123 verbatim
end BernoulliRegular


-- @@ L125-125 verbatim
end


-- @@ L127-127 verbatim
end
