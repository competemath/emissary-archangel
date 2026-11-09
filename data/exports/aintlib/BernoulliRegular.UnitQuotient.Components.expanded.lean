/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.UnitQuotient.Torsion
public import BernoulliRegular.Idempotents
public import Mathlib.Data.ZMod.Basic


-- @@ L12-23 verbatim
/-!
# Unit quotients: power quotients and `Δ`-components

This file is the `T040b` layer.  It defines the quotient `E / E^(p^N)` for
`E = 𝒪_Kˣ`, records the exponent-killing lemma for the quotient map, and
packages the `Δ = (ZMod p)ˣ`-component size data used by reflection.

The component decomposition is kept data-driven: later files can instantiate
the supplied components with the intrinsic idempotent construction, while the
reflection layer can already consume stable character-tagged subgroups and
their computed cardinal exponents.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace BernoulliRegular


-- @@ L31-31 verbatim
set_option linter.unusedSectionVars false


-- @@ L33-33 verbatim
variable (p N : ℕ) [Fact p.Prime]

-- @@ L34-34 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L36-39 verbatim
/-- The Galois character group `Δ = (ZMod p)ˣ` indexing unit-quotient
components. -/
abbrev CyclotomicUnitDelta : Type :=
  (ZMod p)ˣ


-- @@ L41-43 verbatim
/-- The subgroup `E^(p^N)` of `p^N`-th powers in the unit group. -/
abbrev CyclotomicUnitPowerSubgroup : Subgroup (CyclotomicUnitGroup K) :=
  (powMonoidHom (p ^ N) : CyclotomicUnitGroup K →* CyclotomicUnitGroup K).range


-- @@ L45-47 verbatim
/-- The unit power quotient `E / E^(p^N)`. -/
abbrev CyclotomicUnitPowerQuotient : Type _ :=
  CyclotomicUnitGroup K ⧸ CyclotomicUnitPowerSubgroup (p := p) (N := N) K


-- @@ L49-52 verbatim
/-- The quotient map `E → E / E^(p^N)`. -/
def cyclotomicUnitPowerClass :
    CyclotomicUnitGroup K →* CyclotomicUnitPowerQuotient (p := p) (N := N) K :=
  QuotientGroup.mk' (CyclotomicUnitPowerSubgroup (p := p) (N := N) K)


-- @@ L54-57 verbatim
@[simp]
theorem cyclotomicUnitPowerClass_apply (u : CyclotomicUnitGroup K) :
    cyclotomicUnitPowerClass (p := p) (N := N) K u = QuotientGroup.mk u :=
  rfl


-- @@ L59-63 verbatim
/-- The quotient map kills `p^N`-th powers. -/
theorem cyclotomicUnitPowerClass_pow_eq_one (u : CyclotomicUnitGroup K) :
    cyclotomicUnitPowerClass (p := p) (N := N) K (u ^ (p ^ N)) = 1 :=
  (QuotientGroup.eq_one_iff (N := CyclotomicUnitPowerSubgroup (p := p) (N := N) K)
    (u ^ (p ^ N))).2 ⟨u, rfl⟩


-- @@ L65-71 verbatim
/-- Every element of `E / E^(p^N)` is killed by `p^N`. -/
theorem cyclotomicUnitPowerQuotient_pow_eq_one
    (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    x ^ (p ^ N) = 1 := by
  refine QuotientGroup.induction_on x fun u => ?_
  rw [← QuotientGroup.mk_pow]
  exact cyclotomicUnitPowerClass_pow_eq_one (p := p) (N := N) K u


-- @@ L73-76 verbatim
/-- A declared action of `Δ = (ZMod p)ˣ` on the unit power quotient. -/
structure CyclotomicUnitQuotientDeltaAction where
  toMulAut : CyclotomicUnitDelta p →*
    MulAut (CyclotomicUnitPowerQuotient (p := p) (N := N) K)


-- @@ L78-78 verbatim
namespace CyclotomicUnitQuotientDeltaAction


-- @@ L80-80 verbatim
variable {p N K}


-- @@ L82-87 verbatim
/-- Apply the declared `Δ`-action. -/
def act (A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K)
    (a : CyclotomicUnitDelta p)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    CyclotomicUnitPowerQuotient (p := p) (N := N) K :=
  A.toMulAut a x


-- @@ L89-94 verbatim
@[simp]
theorem act_one (A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    A.act 1 x = x := by
  change A.toMulAut 1 x = x
  simp


-- @@ L96-101 verbatim
@[simp]
theorem act_mul (A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K)
    (a : CyclotomicUnitDelta p)
    (x y : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    A.act a (x * y) = A.act a x * A.act a y :=
  map_mul (A.toMulAut a) x y


-- @@ L103-109 verbatim
theorem act_comp (A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K)
    (a b : CyclotomicUnitDelta p)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    A.act (a * b) x = A.act a (A.act b x) := by
  change A.toMulAut (a * b) x = A.toMulAut a (A.toMulAut b x)
  rw [map_mul]
  rfl


-- @@ L111-111 verbatim
end CyclotomicUnitQuotientDeltaAction


-- @@ L113-122 verbatim
/-- A character-tagged subgroup of `E/E^(p^N)`, stable under the declared
`Δ`-action, with its computed cardinal exponent. -/
structure CyclotomicUnitQuotientComponent
    (A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K) where
  character : MulChar (CyclotomicUnitDelta p) ℚ
  carrier : Subgroup (CyclotomicUnitPowerQuotient (p := p) (N := N) K)
  stable : ∀ a ⦃x : CyclotomicUnitPowerQuotient (p := p) (N := N) K⦄,
    x ∈ carrier → A.act a x ∈ carrier
  cardExponent : ℕ
  natCard_eq : Nat.card (carrier : Type _) = p ^ cardExponent


-- @@ L124-124 verbatim
namespace CyclotomicUnitQuotientComponent


-- @@ L126-126 verbatim
variable {p N K}

-- @@ L127-127 verbatim
variable {A : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K}


-- @@ L129-131 verbatim
instance : CoeOut (CyclotomicUnitQuotientComponent (p := p) (N := N) (K := K) A)
    (Subgroup (CyclotomicUnitPowerQuotient (p := p) (N := N) K)) :=
  ⟨carrier⟩


-- @@ L133-136 verbatim
/-- The underlying subgroup as a type. -/
abbrev Carrier (C : CyclotomicUnitQuotientComponent (p := p) (N := N) (K := K) A) :
    Type _ :=
  C.carrier


-- @@ L138-144 verbatim
/-- Stability of a component under the declared `Δ`-action. -/
theorem act_mem
    (C : CyclotomicUnitQuotientComponent (p := p) (N := N) (K := K) A)
    (a : CyclotomicUnitDelta p) {x : CyclotomicUnitPowerQuotient (p := p) (N := N) K}
    (hx : x ∈ C.carrier) :
    A.act a x ∈ C.carrier :=
  C.stable a hx


-- @@ L146-150 verbatim
/-- Cardinality of a component in the computed `p`-power form. -/
theorem natCard_eq_pow
    (C : CyclotomicUnitQuotientComponent (p := p) (N := N) (K := K) A) :
    Nat.card C.Carrier = p ^ C.cardExponent :=
  C.natCard_eq


-- @@ L152-152 verbatim
end CyclotomicUnitQuotientComponent


-- @@ L154-168 verbatim
/-- The full character-component size package for `E/E^(p^N)`.

The functions `torsionContribution` and `freeContribution` separate the
roots-of-unity contribution from the free-unit contribution; the exponent
formula records the effect of quotienting the free part by `p^N`. -/
structure CyclotomicUnitQuotientComponentStructure where
  action : CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K
  component : MulChar (CyclotomicUnitDelta p) ℚ →
    CyclotomicUnitQuotientComponent (p := p) (N := N) (K := K) action
  component_character : ∀ χ, (component χ).character = χ
  torsionContribution : MulChar (CyclotomicUnitDelta p) ℚ → ℕ
  freeContribution : MulChar (CyclotomicUnitDelta p) ℚ → ℕ
  componentExponent_eq :
    ∀ χ, (component χ).cardExponent =
      torsionContribution χ + N * freeContribution χ


-- @@ L170-170 verbatim
namespace CyclotomicUnitQuotientComponentStructure


-- @@ L172-172 verbatim
variable {p N K}


-- @@ L174-179 verbatim
/-- The component tagged by a character has that character. -/
theorem component_character_eq
    (S : CyclotomicUnitQuotientComponentStructure (p := p) (N := N) K)
    (χ : MulChar (CyclotomicUnitDelta p) ℚ) :
    (S.component χ).character = χ :=
  S.component_character χ


-- @@ L181-193 verbatim
/-- Cardinality of a component after substituting the torsion/free exponent
formula. -/
theorem component_natCard_eq_pow
    (S : CyclotomicUnitQuotientComponentStructure (p := p) (N := N) K)
    (χ : MulChar (CyclotomicUnitDelta p) ℚ) :
    Nat.card (S.component χ).Carrier =
      p ^ (S.torsionContribution χ + N * S.freeContribution χ) := by
  calc
    Nat.card (S.component χ).Carrier = p ^ (S.component χ).cardExponent :=
      CyclotomicUnitQuotientComponent.natCard_eq_pow (p := p) (N := N) (K := K)
        (S.component χ)
    _ = p ^ (S.torsionContribution χ + N * S.freeContribution χ) := by
      rw [S.componentExponent_eq χ]


-- @@ L195-195 verbatim
end CyclotomicUnitQuotientComponentStructure


-- @@ L197-197 verbatim
end BernoulliRegular
