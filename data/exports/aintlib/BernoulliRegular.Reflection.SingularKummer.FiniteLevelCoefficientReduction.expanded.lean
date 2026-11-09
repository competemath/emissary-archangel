module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelFinalBridge


-- @@ L5-12 verbatim
/-!
# Singular Kummer: reduction of finite-level idempotent coefficients

The final finite-level bridge needs the exact idempotent coefficients to reduce
to the usual mod-`p` character-projection coefficients.  This file proves that
this follows formally from the corresponding reduction of the character and
invertibility of `|Delta|` at the finite level.
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace BernoulliRegular

-- @@ L19-19 verbatim
namespace Reflection

-- @@ L20-20 verbatim
namespace SingularKummer


-- @@ L22-22 verbatim
namespace FiniteLevelCoefficientReduction


-- @@ L24-24 verbatim
variable {p m : ℕ} [NeZero p] [NeZero m]


-- @@ L26-37 verbatim
omit [NeZero m] in
/-- Inversion of `|Delta|` is compatible with reduction from `ZMod m` to
`ZMod p`, provided `|Delta|` is a unit modulo `m`. -/
theorem cast_card_delta_inv
    (hm : p ∣ m)
    (hcard : IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod m)) :
    ZMod.castHom hm (ZMod p)
        ((Fintype.card (CharacterProjection.Delta p) : ZMod m)⁻¹) =
      ((Fintype.card (CharacterProjection.Delta p) : ZMod p)⁻¹) := by
  refine (ZMod.inv_eq_of_mul_eq_one p _ _ ?_).symm
  simpa [-ZMod.castHom_apply, map_mul, map_one] using congrArg (ZMod.castHom hm (ZMod p))
    (ZMod.mul_inv_of_unit (Fintype.card (CharacterProjection.Delta p) : ZMod m) hcard)


-- @@ L39-55 verbatim
omit [NeZero m] in
/-- If a finite-level character reduces to `a ↦ a^i`, then its exact
idempotent coefficients reduce to the usual mod-`p` coefficients. -/
theorem coefficient_cast_eq_of_character_cast
    (hm : p ∣ m)
    (hcard : IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod m))
    (i : ℕ)
    (chi : CharacterProjection.Delta p →* (ZMod m)ˣ)
    (hchi : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p) (chi d : ZMod m) = ((d : ZMod p) ^ i))
    (d : CharacterProjection.Delta p) :
    ZMod.castHom hm (ZMod p)
        (FiniteLevelIdempotent.coefficient (m := m) chi d) =
      CharacterProjection.characterProjectionCoefficient (p := p) i d := by
  rw [FiniteLevelIdempotent.coefficient,
    CharacterProjection.characterProjectionCoefficient, map_mul,
    cast_card_delta_inv (p := p) (m := m) hm hcard, hchi d⁻¹]


-- @@ L57-57 verbatim
variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A] [Finite A]


-- @@ L59-76 verbatim
/-- Version of the finite-level bridge where coefficient reduction is derived
from character reduction. -/
theorem torsionComponentNontrivial_of_finiteLevelCharacter_cast
    (hcardp : IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod p))
    (hcardm : IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod m))
    (hm : p ∣ m) (i : ℕ)
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (chi : CharacterProjection.Delta p →* (ZMod m)ˣ)
    (hchi : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p) (chi d : ZMod m) = ((d : ZMod p) ^ i))
    (hV : ElementaryQuotientComponent.ElementaryComponentNontrivial
      (p := p) i rho) :
    TorsionComponent.TorsionComponentNontrivial (p := p) i rho :=
  FiniteLevelFinalBridge.torsionComponentNontrivial_of_finiteLevelCharacter
    (p := p) (m := m) hcardp hm i rho chi
    (coefficient_cast_eq_of_character_cast
      (p := p) (m := m) hm hcardm i chi hchi)
    hchi hV


-- @@ L78-78 verbatim
end FiniteLevelCoefficientReduction


-- @@ L80-80 verbatim
end SingularKummer

-- @@ L81-81 verbatim
end Reflection

-- @@ L82-82 verbatim
end BernoulliRegular


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end
