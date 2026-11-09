/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.UnitQuotient.Components


-- @@ L10-22 verbatim
/-!
# Unit quotients: final structure package

This file is the `T040c` layer.  It packages the explicit structure theorem
for the unit power quotient in the form used by reflection:

`E / E^(p^N) ≃ ℤ/p ⊕ (ℤ/p^N)^((p - 3) / 2)`.

The quotient is multiplicative, so the additive target is wrapped in
`Multiplicative`.  The package also records equivariance for the declared
`Δ = (ZMod p)ˣ` action and keeps the component-size data from `T040b`
available from the same object.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace BernoulliRegular


-- @@ L30-30 verbatim
set_option linter.unusedSectionVars false


-- @@ L32-32 verbatim
variable (p N : ℕ) [Fact p.Prime]

-- @@ L33-33 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L35-37 verbatim
/-- The free summand index set in the unit quotient structure theorem. -/
abbrev CyclotomicUnitQuotientFreeIndex : Type :=
  Fin ((p - 3) / 2)


-- @@ L39-41 verbatim
/-- The additive model `ℤ/p ⊕ (ℤ/p^N)^((p - 3) / 2)`. -/
abbrev CyclotomicUnitQuotientAdditiveModel : Type :=
  ZMod p × (CyclotomicUnitQuotientFreeIndex p → ZMod (p ^ N))


-- @@ L43-45 verbatim
/-- The multiplicative model for `E / E^(p^N)`. -/
abbrev CyclotomicUnitQuotientModel : Type :=
  Multiplicative (CyclotomicUnitQuotientAdditiveModel p N)


-- @@ L47-59 verbatim
/-- The final structure package for `E / E^(p^N)`, including the `Δ`-component
sizes and an equivariant multiplicative isomorphism with the explicit model. -/
structure CyclotomicUnitQuotientStructure where
  componentStructure :
    CyclotomicUnitQuotientComponentStructure (p := p) (N := N) K
  modelAction : CyclotomicUnitDelta p →* MulAut (CyclotomicUnitQuotientModel p N)
  modelEquiv :
    CyclotomicUnitPowerQuotient (p := p) (N := N) K ≃*
      CyclotomicUnitQuotientModel p N
  equivariant :
    ∀ (a : CyclotomicUnitDelta p)
      (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K),
      modelEquiv (componentStructure.action.act a x) = modelAction a (modelEquiv x)


-- @@ L61-61 verbatim
namespace CyclotomicUnitQuotientStructure


-- @@ L63-63 verbatim
variable {p N K}


-- @@ L65-68 verbatim
/-- The `Δ`-action on the source quotient. -/
abbrev sourceAction (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K) :
    CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K :=
  S.componentStructure.action


-- @@ L70-74 verbatim
/-- The character-tagged component package attached to a final structure
theorem. -/
abbrev components (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K) :
    CyclotomicUnitQuotientComponentStructure (p := p) (N := N) K :=
  S.componentStructure


-- @@ L76-81 verbatim
/-- The final multiplicative equivalence
`E/E^(p^N) ≃ ℤ/p ⊕ (ℤ/p^N)^((p - 3)/2)`. -/
def structureEquiv (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K) :
    CyclotomicUnitPowerQuotient (p := p) (N := N) K ≃*
      CyclotomicUnitQuotientModel p N :=
  S.modelEquiv


-- @@ L83-91 verbatim
/-- Equivariance of the final structure isomorphism for the declared
`Δ`-actions. -/
theorem structureEquiv_equivariant
    (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K)
    (a : CyclotomicUnitDelta p)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    S.structureEquiv (S.sourceAction.act a x) =
      S.modelAction a (S.structureEquiv x) :=
  S.equivariant a x


-- @@ L93-100 verbatim
/-- Component cardinality in the final structure package. -/
theorem component_natCard_eq_pow
    (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K)
    (χ : MulChar (CyclotomicUnitDelta p) ℚ) :
    Nat.card (S.components.component χ).Carrier =
      p ^ (S.components.torsionContribution χ + N * S.components.freeContribution χ) :=
  CyclotomicUnitQuotientComponentStructure.component_natCard_eq_pow
    (p := p) (N := N) (K := K) S.components χ


-- @@ L102-102 verbatim
end CyclotomicUnitQuotientStructure


-- @@ L104-106 verbatim
/-- The `E/E^p` specialization used by the vanishing ticket. -/
abbrev CyclotomicUnitModPQuotient : Type _ :=
  CyclotomicUnitPowerQuotient (p := p) (N := 1) K


-- @@ L108-110 verbatim
/-- The final structure package specialized to `E/E^p`. -/
abbrev CyclotomicUnitModPStructure : Type _ :=
  CyclotomicUnitQuotientStructure (p := p) (N := 1) K


-- @@ L112-112 verbatim
end BernoulliRegular
