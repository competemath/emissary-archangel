/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import TNLean.Algebra.GeneralizedCocycleInversion


-- @@ L9-36 verbatim
/-!
# Positive generalized cocycles

This file proves arXiv:2502.20257, `cor:positive_trivial`, lines 5950--5960.
A positive complex unit means an element of the embedded subgroup
`Units NNReal → Units ℂ`, rather than a complex number with positive real part.

For a positive generalized cocycle `Ω`, finite-group power trivialization gives
`Ω ^ |G| = dχ₀`. The determinant cochain `χ₀` can contain permutation signs, so
we first take its pointwise norm and then its positive `|G|`-th root. If also
`Ω * hat Ω = 1`, the source's refined witness is

`χ = sqrt (χ₀ / hat χ₀)`.

The block label is retained throughout. No transitivity or finiteness assumption
is imposed on the block-label type.

**Local fix (block index):** The source writes `χ_g` in the corollary, while
its preceding determinant construction gives `χ_g^x`. The block label is
necessary in general. See
`docs/paper-gaps/fbc25_positive_generalized_cocycle_block_index.tex`.

**Local fix (determinant sign):** The source invokes the positive-root
bijection without addressing that the determinant primitive can carry the sign
of the regular permutation. We first take the pointwise norm and then the
positive root. See
`docs/paper-gaps/fbc25_positive_generalized_cocycle_determinant_sign.tex`.
-/


-- @@ L38-38 verbatim
namespace TNLean.Algebra


-- @@ L40-40 verbatim
variable {G X : Type*} [Group G] [MulAction G X]


-- @@ L42-42 verbatim
namespace PositiveUnits


-- @@ L44-46 verbatim
/-- The multiplicative embedding of nonnegative-real units into complex units. -/
def embedding : Units NNReal →* Units ℂ :=
  Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom


-- @@ L48-50 verbatim
/-- The norm of a complex unit, regarded as a nonnegative-real unit. -/
noncomputable def norm : Units ℂ →* Units NNReal :=
  Units.map nnnormHom.toMonoidHom


-- @@ L52-54 verbatim
/-- Raising nonnegative-real units to a real power is a multiplicative map. -/
noncomputable def rpow (r : ℝ) : Units NNReal →* Units NNReal :=
  Units.map (NNReal.rpowMonoidHom r)


-- @@ L56-59 verbatim
/-- The canonical positive real power of a complex unit: take its norm, apply
`NNReal.rpow`, and embed the result back into the complex units. -/
noncomputable def positiveRpow (r : ℝ) : Units ℂ →* Units ℂ :=
  embedding.comp ((rpow r).comp norm)


-- @@ L61-65 verbatim
/-- A complex unit is strictly positive when it belongs to the image of the
unit group of the nonnegative reals. Since a unit of `ℝ≥0` is nonzero, this is
exactly membership in the embedded subgroup `ℝ_{>0} ⊆ ℂˣ`. -/
def IsPositive (z : Units ℂ) : Prop :=
  z ∈ Set.range embedding


-- @@ L67-73 verbatim
/-- Taking the norm is a left inverse to the positive-unit embedding. -/
@[simp]
theorem norm_embedding (r : Units NNReal) : norm (embedding r) = r := by
  apply Units.ext
  apply NNReal.eq
  change ‖((r : NNReal) : ℂ)‖ = (r : NNReal)
  exact Complex.norm_of_nonneg r.val.property


-- @@ L75-77 verbatim
/-- A canonical positive real power is positive-valued. -/
theorem isPositive_positiveRpow (r : ℝ) (z : Units ℂ) : IsPositive (positiveRpow r z) := by
  exact ⟨rpow r (norm z), rfl⟩


-- @@ L79-84 verbatim
/-- Positive real powers recover the usual `NNReal.rpow` on embedded positive
units. -/
@[simp]
theorem positiveRpow_embedding (s : ℝ) (r : Units NNReal) :
    positiveRpow s (embedding r) = embedding (rpow s r) := by
  simp [positiveRpow]


-- @@ L86-94 verbatim
/-- The positive `n`-th root raised to the `n`-th power recovers a positive
complex unit. -/
theorem positiveRpow_inv_natCast_pow {z : Units ℂ} (hz : IsPositive z)
    {n : ℕ} (hn : n ≠ 0) : positiveRpow (n : ℝ)⁻¹ z ^ n = z := by
  obtain ⟨r, rfl⟩ := hz
  rw [positiveRpow_embedding, ← map_pow]
  apply congrArg embedding
  apply Units.ext
  simpa [rpow, Units.coe_map] using NNReal.rpow_inv_natCast_pow (r : NNReal) hn


-- @@ L96-96 verbatim
end PositiveUnits


-- @@ L98-98 verbatim
namespace ActionTensorGauge


-- @@ L100-103 verbatim
/-- A block-dependent scalar one-cochain is positive-valued when every value
lies in the embedded subgroup `ℝ_{>0} ⊆ ℂˣ`. -/
def IsPositiveValued (χ : ActionTensorGauge G X) : Prop :=
  ∀ g x, PositiveUnits.IsPositive (χ g x)


-- @@ L105-109 verbatim
/-- Apply the canonical positive real-power homomorphism pointwise to a
block-dependent one-cochain. -/
noncomputable def positiveRpow (r : ℝ) (χ : ActionTensorGauge G X) :
    ActionTensorGauge G X :=
  fun g x => PositiveUnits.positiveRpow r (χ g x)


-- @@ L111-115 verbatim
omit [Group G] [MulAction G X] in
/-- Pointwise positive real powers are positive-valued. -/
theorem isPositiveValued_positiveRpow (r : ℝ) (χ : ActionTensorGauge G X) :
    IsPositiveValued (positiveRpow r χ) :=
  fun g x => PositiveUnits.isPositive_positiveRpow r (χ g x)


-- @@ L117-122 verbatim
/-- Generalized coboundaries preserve pointwise division. -/
theorem coboundary_div (χ ψ : ActionTensorGauge G X) :
    coboundary (χ / ψ) = coboundary χ / coboundary ψ := by
  funext x g h
  simp only [coboundary, Pi.div_apply, div_eq_mul_inv, mul_inv_rev, inv_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]


-- @@ L124-129 verbatim
/-- Pointwise positive real powers commute with the generalized coboundary. -/
theorem coboundary_positiveRpow (r : ℝ) (χ : ActionTensorGauge G X) :
    coboundary (positiveRpow r χ) =
      fun x g h => PositiveUnits.positiveRpow r (coboundary χ x g h) := by
  funext x g h
  simp [coboundary, positiveRpow]


-- @@ L131-131 verbatim
end ActionTensorGauge


-- @@ L133-133 verbatim
namespace LSymbol


-- @@ L135-138 verbatim
/-- A block-dependent scalar two-cochain is positive-valued when every value
lies in the embedded subgroup `ℝ_{>0} ⊆ ℂˣ`. -/
def IsPositiveValued (Ω : LSymbol G X) : Prop :=
  ∀ x g h, PositiveUnits.IsPositive (Ω x g h)


-- @@ L140-144 verbatim
/-- The positive primitive obtained from the determinant cochain: take the
pointwise norm and then the positive `|G|`-th root. -/
noncomputable def positivePrimitive [Fintype G] (Ω : LSymbol G X) :
    ActionTensorGauge G X :=
  ActionTensorGauge.positiveRpow (Fintype.card G : ℝ)⁻¹ (determinantCochain Ω)


-- @@ L146-149 verbatim
/-- The determinant/root primitive is positive-valued. -/
theorem isPositiveValued_positivePrimitive [Fintype G] (Ω : LSymbol G X) :
    ActionTensorGauge.IsPositiveValued (positivePrimitive Ω) :=
  ActionTensorGauge.isPositiveValued_positiveRpow _ _


-- @@ L151-181 verbatim
/-- Every positive generalized scalar cocycle of a finite group is a
block-dependent coboundary with a positive primitive.

The proof follows arXiv:2502.20257, `cor:positive_trivial`, lines 5950--5956.
Unlike the abbreviated notation in the source, the witness retains its block
label. The determinant supplied by finite-group power trivialization is first
replaced pointwise by its norm because permutation signs need not be positive. -/
theorem exists_positive_coboundary [Finite G] {Ω : LSymbol G X}
    (hΩ : IsGeneralizedCocycle Ω) (hpos : IsPositiveValued Ω) :
    ∃ χ : ActionTensorGauge G X,
      ActionTensorGauge.IsPositiveValued χ ∧
        Ω = ActionTensorGauge.coboundary χ := by
  let _ := Fintype.ofFinite G
  refine ⟨positivePrimitive Ω, isPositiveValued_positivePrimitive Ω, ?_⟩
  funext x g h
  let n := Fintype.card G
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hpow := pow_card_eq_coboundary_apply hΩ x g h
  calc
    Ω x g h = PositiveUnits.positiveRpow (n : ℝ)⁻¹ (Ω x g h) ^ n :=
      (PositiveUnits.positiveRpow_inv_natCast_pow (hpos x g h) hn).symm
    _ = PositiveUnits.positiveRpow (n : ℝ)⁻¹ (Ω x g h ^ n) := by
      rw [map_pow]
    _ = PositiveUnits.positiveRpow (n : ℝ)⁻¹
        (ActionTensorGauge.coboundary (determinantCochain Ω) x g h) := by
      rw [hpow]
    _ = ActionTensorGauge.coboundary (positivePrimitive Ω) x g h := by
      have hcob := congrFun (congrFun (congrFun
        (ActionTensorGauge.coboundary_positiveRpow (n : ℝ)⁻¹
          (determinantCochain Ω)) x) g) h
      simpa [positivePrimitive, n] using hcob.symm


-- @@ L183-218 verbatim
/-- Under `Ω * hat Ω = 1`, the positive primitive can be chosen to satisfy
`χ * hat χ = 1` as well.

Starting from a positive primitive `χ₀`, this is exactly the source choice
`χ = sqrt (χ₀ / hat χ₀)` from arXiv:2502.20257,
`cor:positive_trivial`, lines 5955--5959. -/
theorem exists_positive_coboundary_hat_mul_eq_one [Finite G]
    {Ω : LSymbol G X} (hΩ : IsGeneralizedCocycle Ω)
    (hpos : IsPositiveValued Ω) (hhat : Ω * hat Ω = 1) :
    ∃ χ : ActionTensorGauge G X,
      ActionTensorGauge.IsPositiveValued χ ∧
        Ω = ActionTensorGauge.coboundary χ ∧
          χ * ActionTensorGauge.hat χ = 1 := by
  obtain ⟨χ₀, _, hχ₀⟩ := exists_positive_coboundary hΩ hpos
  let χ : ActionTensorGauge G X :=
    ActionTensorGauge.positiveRpow (2 : ℝ)⁻¹ (χ₀ / ActionTensorGauge.hat χ₀)
  refine ⟨χ, ActionTensorGauge.isPositiveValued_positiveRpow _ _, ?_, ?_⟩
  · rw [ActionTensorGauge.coboundary_positiveRpow,
      ActionTensorGauge.coboundary_div, ← hat_coboundary, ← hχ₀]
    funext x g h
    have hhatApply : Ω x g h * hat Ω x g h = 1 := by
      simpa only [Pi.mul_apply, Pi.one_apply] using
        congrFun (congrFun (congrFun hhat x) g) h
    have hquot : Ω x g h / hat Ω x g h = Ω x g h ^ 2 := by
      rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_left hhatApply, pow_two]
    change Ω x g h = PositiveUnits.positiveRpow (2 : ℝ)⁻¹
      (Ω x g h / hat Ω x g h)
    rw [hquot]
    rw [map_pow]
    exact (PositiveUnits.positiveRpow_inv_natCast_pow (hpos x g h) (by decide)).symm
  · funext g x
    change χ g x * ActionTensorGauge.hat χ g x = 1
    dsimp only [χ, ActionTensorGauge.hat, ActionTensorGauge.positiveRpow, Pi.div_apply]
    simp only [inv_inv, inv_smul_smul]
    rw [← map_mul]
    simp


-- @@ L220-220 verbatim
end LSymbol


-- @@ L222-222 verbatim
end TNLean.Algebra
