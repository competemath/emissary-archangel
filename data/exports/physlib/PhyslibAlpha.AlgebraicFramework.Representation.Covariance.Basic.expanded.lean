/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Symmetry
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.EffectValuedMeasure
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic


-- @@ L13-32 verbatim
/-!

# Covariant measurements

A measurement is *covariant* under a symmetry when transforming the outcome and transforming the
assigned effect agree — a rotated detector, pointed at a rotated direction, reads out the same
statistics a rotation of the original detector would have. This file lays the foundation: a
measurable action of a group on the outcome space, a symmetry's action on effects (extending
`Symmetry`'s existing action on states, `OrderUnit/Symmetry.lean`, to the dual side), and the
covariance predicate on a POVM itself.

## Main definitions

- `UnitalPositiveLinearMap.mapEffect`, `Symmetry.instSMulEffect` : a channel — in particular a
  symmetry — sends effects to effects.
- `MeasurableAction G Ω` : `G` acts on `Ω` by measurable bijections.
- `EffectValuedMeasure.IsCovariant` : `μ (g • S) = ρ g • μ S`, the abstract form of
  `E(gS) = α_g(E(S))`.

-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open scoped Pointwise


-- @@ L38-38 verbatim
section EffectAction


-- @@ L40-41 verbatim
variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsOrderUnit E]


-- @@ L43-46 expanded
/-- A channel sends effects to effects: positivity gives `0 ≤ φ e`, and monotonicity applied to
`e ≤ 1` together with unitality gives `φ e ≤ φ 1 = 1`. -/
def UnitalPositiveLinearMap.mapEffect (φ : UnitalPositiveLinearMap ℝ E E) (e : Effect E) :
    Effect E :=
  ⟨φ (e : E), φ.map_nonneg e.2.1, (φ.monotone' e.2.2).trans_eq (map_one φ)⟩


-- @@ L48-51 expanded
omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] in
@[simp]
lemma UnitalPositiveLinearMap.coe_mapEffect (φ : UnitalPositiveLinearMap ℝ E E) (e : Effect E) :
    (φ.mapEffect e : E) = φ (e : E) :=
  rfl


-- @@ L53-55 verbatim
/-- A symmetry acts on effects the way it acts on `E` itself, via the underlying channel — the
dual of `Symmetry`'s existing action on states (`OrderUnit/Symmetry.lean`). -/
instance Symmetry.instSMulEffect : SMul (Symmetry E) (Effect E) := ⟨fun φ e => φ.1.mapEffect e⟩


-- @@ L57-60 verbatim
omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] in
@[simp]
lemma Symmetry.coe_smul_effect (φ : Symmetry E) (e : Effect E) :
    ((φ • e : Effect E) : E) = φ.1 (e : E) := rfl


-- @@ L62-64 verbatim
instance Symmetry.instMulActionEffect : MulAction (Symmetry E) (Effect E) where
  one_smul e := Subtype.ext (by simp)
  mul_smul φ ψ e := Subtype.ext (by simp [UnitalPositiveLinearMap.comp_apply])


-- @@ L66-66 verbatim
end EffectAction


-- @@ L68-68 verbatim
section MeasurableAction


-- @@ L70-75 verbatim
/-- `G` acts on the measurable space `Ω`, and every group element moves points measurably. Since
this holds for `g` and `g⁻¹` both, the action is by measurable *bijections*: `MeasurableSet.smul`
below shows it moves measurable sets to measurable sets, not merely points. -/
class MeasurableAction (G Ω : Type*) [Group G] [MeasurableSpace Ω] [MulAction G Ω] : Prop where
  /-- Every group element acts as a measurable map. -/
  measurable_smul : ∀ g : G, Measurable (fun x : Ω => g • x)


-- @@ L77-77 verbatim
variable {G Ω : Type*} [Group G] [MeasurableSpace Ω] [MulAction G Ω] [MeasurableAction G Ω]


-- @@ L79-91 verbatim
/-- The image of a measurable set under the action of a group element is again measurable:
`g • S` is the preimage of `S` under the (measurable) action of `g⁻¹`. -/
lemma measurableSet_smul {S : Set Ω} (hS : MeasurableSet S) (g : G) : MeasurableSet (g • S) := by
  have heq : g • S = (fun x => g⁻¹ • x) ⁻¹' S := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rwa [inv_smul_smul]
    · intro hx
      exact ⟨g⁻¹ • x, hx, by rw [smul_inv_smul]⟩
  rw [heq]
  exact MeasurableSet.preimage hS (MeasurableAction.measurable_smul g⁻¹)


-- @@ L93-93 verbatim
end MeasurableAction


-- @@ L95-95 verbatim
section Covariant


-- @@ L97-99 verbatim
variable {G Ω E : Type*} [Group G] [MeasurableSpace Ω] [MulAction G Ω] [MeasurableAction G Ω]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E]
  [One E] [IsOrderUnit E]


-- @@ L101-107 verbatim
/-- A measurement (POVM) `μ` is **covariant** under an action of `G` on the outcome space,
transported to the physical system via `ρ : G →* Symmetry E`, when transforming the outcome set
and transforming the assigned effect agree: `μ(g • S) = ρ(g) • μ(S)`. This is the abstract form of
`E(gS) = α_g(E(S))` — a rotated detector pointed at a rotated direction reads out what a rotation
of the original detector would have. -/
def EffectValuedMeasure.IsCovariant (ρ : G →* Symmetry E) (μ : EffectValuedMeasure Ω E) : Prop :=
  ∀ (g : G) (S : Set Ω) (hS : MeasurableSet S), μ (g • S) (measurableSet_smul hS g) = ρ g • μ S hS


-- @@ L109-109 verbatim
end Covariant


-- @@ L111-118 verbatim
/-! ## Covariant channels: the general intertwiner picture

Not every physical transformation has a measurable outcome space to be covariant "under" the way
a measurement is — a channel `φ : E₁ →ₚ₁[ℝ] E₂` between two systems is covariant simply when
transporting the input and transporting the output agree, with no measurable space in sight:
channels are also intertwiners. This is the general form; a covariant measurement (above) is the
special case where `E₂ = B_b(Ω,Σ)`'s dual role is replaced by `E₁` itself carrying the classical
outcome action. -/


-- @@ L120-120 verbatim
section CovariantChannel


-- @@ L122-125 verbatim
variable {G E₁ E₂ E₃ : Type*} [Group G]
  [AddCommGroup E₁] [PartialOrder E₁] [Module ℝ E₁] [One E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [Module ℝ E₂] [One E₂]
  [AddCommGroup E₃] [PartialOrder E₃] [Module ℝ E₃] [One E₃]


-- @@ L127-132 expanded
/-- A channel `φ : E₁ →ₚ₁[ℝ] E₂` is **covariant** under symmetry actions `ρ₁`, `ρ₂` of `G` on the
two systems when transporting the input along `ρ₁ g` then applying `φ`, or applying `φ` then
transporting the output along `ρ₂ g`, agree — the channel intertwines the two actions. -/
def UnitalPositiveLinearMap.IsCovariant (ρ₁ : G →* Symmetry E₁) (ρ₂ : G →* Symmetry E₂)
    (φ : UnitalPositiveLinearMap ℝ E₁ E₂) : Prop :=
  ∀ g : G, φ.comp (ρ₁ g).1 = (ρ₂ g).1.comp φ


-- @@ L134-138 verbatim
/-- The identity channel is covariant under any action of `G`, against itself: it trivially
intertwines an action with itself. -/
lemma UnitalPositiveLinearMap.isCovariant_id (ρ : G →* Symmetry E₁) :
    (UnitalPositiveLinearMap.id ℝ E₁).IsCovariant ρ ρ := fun g => by
  rw [UnitalPositiveLinearMap.id_comp, UnitalPositiveLinearMap.comp_id]


-- @@ L140-147 expanded
/-- Covariance is preserved by composition: a covariant channel followed by a covariant channel is
covariant for the actions at the two ends, with the middle system's action cancelling out. -/
lemma UnitalPositiveLinearMap.IsCovariant.comp {ρ₁ : G →* Symmetry E₁} {ρ₂ : G →* Symmetry E₂}
    {ρ₃ : G →* Symmetry E₃} {ψ : UnitalPositiveLinearMap ℝ E₂ E₃}
    {φ : UnitalPositiveLinearMap ℝ E₁ E₂} (hψ : ψ.IsCovariant ρ₂ ρ₃) (hφ : φ.IsCovariant ρ₁ ρ₂) :
    (ψ.comp φ).IsCovariant ρ₁ ρ₃ := fun g => by
  rw [UnitalPositiveLinearMap.comp_assoc, hφ g, ← UnitalPositiveLinearMap.comp_assoc, hψ g,
    UnitalPositiveLinearMap.comp_assoc]


-- @@ L149-149 verbatim
end CovariantChannel
