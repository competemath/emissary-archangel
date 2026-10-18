/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByNXCoordFormula
import EllipticCurves.Torsion.NsmulYPeriodic


-- @@ L9-77 verbatim
/-!
# `y(n • 𝒫) = ωₙ/(2ψₙ³)` at the generic point — the `y`-half of the identification of the two `[n]∗`

`EllipticCurves.FunctionField.MulByNXCoordFormula` proves `x(n • 𝒫) = Φₙ(genX)/ΨSqₙ(genX)` at the
generic point and says, in its scope section, exactly what it leaves:

> **It does not identify the two `[n]∗`s.** … what is proved is that the two constructions agree on
> `genX`, which is the `x`-half of that identification and the only half a degree count consumes.

**This file supplies the other half**, and with it `#405`'s deliverable 3: the generic-point images
of *both* coordinate generators under `mulByNEndo` are the written-down division-polynomial
expressions.

## Why this is now a corollary, and was not when `#405` was written

`#405` marks its deliverable 3 *"NOT READY — this is `#251`, do not do it here"*, on the grounds
that `x(n • P) = Φₙ/ΨSqₙ` was available at `n = 2, 3` only.  That is no longer the state of the
tree, and **both** halves are merged:

* the `x`-half — `WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero`
  (`EllipticCurves.Torsion.NsmulOrder`), every index, over any field with `(2 : F) ≠ 0`;
* the `y`-half — `WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
  (`EllipticCurves.Torsion.NsmulYPeriodic`), every index, **under the same hypothesis**
  `ΨSqₙ(x) ≠ 0` the `x`-half asks.

Both are statements about points of a curve over a field, and the generic point `𝒫 = (genX, genY)`
is a point of the curve `W ⁄ F(W)` over the field `F(W)`.  So each applies there with `F := F(W)`
and `W := W ⁄ F(W)`, and — exactly as for the `x`-half — no descent, no specialisation and no
function-field machinery is involved.  ⚠️ **The content is in the merged theorems; what is new here
is only that the generic point is a point.**

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.CoordinateRing.ψ_gen_ne_zero` : **`#405`'s deliverable 1** — `ψₙ` does
  not vanish at the generic point, at every index with `(n : F) ≠ 0`.  The general-`n` form of the
  merged `psiTwo_gen_ne`.
* `WeierstrassCurve.Affine.CoordinateRing.yCoord_nsmul_genericPoint` : `y(n • 𝒫) = ωₙ/(2ψₙ³)`,
  spelled through `WeierstrassCurve.Affine.omegaY`.
* `WeierstrassCurve.Affine.CoordinateRing.two_mul_ψ_pow_mul_yCoord_nsmul_genericPoint` : the same
  cleared of its denominator, so `ωₙ`'s numerator and the parity factor are visible.
* `WeierstrassCurve.Affine.CoordinateRing.mulByNEndo_genY_eq_omegaY` and
  `…mulByNEndo_genX_eq_ΦDivΨSq` : the two generator images of `[n]∗` in division-polynomial form.
* `WeierstrassCurve.Affine.CoordinateRing.mulByNEndo_eq_of_genX_genY` : **the identification** —
  any ring endomorphism of `F(W)` fixing `F` and carrying `genX`, `genY` to those two expressions
  *is* `mulByNEndo n`.
* `WeierstrassCurve.Affine.CoordinateRing.yCoord_nsmul_genericPoint_five_y2EqX3AddOne` : the
  non-vacuity certificate, `y² = x³ + 1` over `ℚ` at `n = 5`.

## ⚠️ What this does NOT do, and one thing it makes unnecessary

* **It builds no second `[n]∗`.**  `#405`'s deliverable 2 proposes `divPolyCoordHom`/`divPolyEndo`
  via `AdjoinRoot.lift` from `equation_div_of_ψ_ne_zero`.  With both generator images now known,
  that construction would be a *duplicate definition of `mulByNEndo`* rather than a second object:
  `mulByNEndo_eq_of_genX_genY` says any such lift equals `mulByNEndo n`.  ⚠️ The hypothesis
  mismatch `#405` records is real and is why this is stated as it is — the division-polynomial
  description carries `(n : F) ≠ 0` (through `ΨSqₙ(genX) ≠ 0`) and `mulByNEndo` does not.
* **It says nothing about `#E[n] = n²`.**  A generator image is not a point count; that gate is
  `#1506` scope item 1.
* **`#1184`'s arbitrary-ring coprimality, `#962` and `#639` are untouched.**
* ⚠️ **It does not weaken any hypothesis of the merged degree tower.**
  `EllipticCurves.FunctionField.MulByNDegreeGeneral` consumes the `x`-half only, and nothing here
  is in its import closure.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
-/


-- @@ L79-79 verbatim
open Polynomial


-- @@ L81-81 verbatim
namespace WeierstrassCurve.Affine


-- @@ L83-83 verbatim
namespace CoordinateRing


-- @@ L85-85 verbatim
variable {F : Type*} [Field F] {W : Affine F}


-- @@ L87-88 verbatim
/-- The base-changed curve `W ⁄ F(W)`, on which the generic point lives. -/
local notation "WF" => W.map (algebraMap F W.FunctionField)


-- @@ L90-97 verbatim
/-- `(2 : F(W)) ≠ 0` from `(2 : F) ≠ 0`.  ⚠️ A copy of the `private` lemma of the same name in
`EllipticCurves.FunctionField.MulByNXCoordFormula`; the duplication is forced by its privacy, not
by a difference in statement. -/
private lemma two_ne_zero_functionField (h2 : (2 : F) ≠ 0) : (2 : W.FunctionField) ≠ 0 := by
  intro h
  refine h2 ((algebraMap F W.FunctionField).injective ?_)
  rw [map_ofNat, map_zero]
  exact h


-- @@ L99-117 verbatim
/-- **`ψₙ` does not vanish at the generic point**, at every index with `(n : F) ≠ 0` — `#405`'s
deliverable 1, and the general-`n` form of `WeierstrassCurve.Affine.CoordinateRing.psiTwo_gen_ne`
(`EllipticCurves.FunctionField.MulByTwoPullback`).

⚠️ The route is **not** the one `#405` proposes.  That issue suggests going through
`AdjoinRoot.mk_ne_zero_of_natDegree_lt`, as the merged `n = 2` case does.  It is cheaper to go
through the square: `ψₙ(genX, genY)² = ΨSqₙ(genX)` (`ψ_sq_evalEval` at `equation_gen`), and
`ΨSqₙ(genX) ≠ 0` is the merged `eval_ΨSq_genX_ne_zero` — `genX` is transcendental and `ΨSqₙ` is a
nonzero polynomial when `(n : F) ≠ 0`.  ⚠️ So the hypothesis really is `(n : F) ≠ 0` and not
`n ≠ 0`, which is what `#405` predicted.  At `n = 2` the hypothesis is `psiTwo_gen_ne`'s in
`Int.cast` spelling and the conclusion is the same, so this **does** subsume the merged `n = 2`
case; that one is left in place because it runs on a different argument — the `Y`-degree bound
through `AdjoinRoot.mk_ne_zero_of_natDegree_lt` — and is what `MulByTwoPullback` consumes.

⚠️ This does **not** need `[W.IsElliptic]`: `equation_gen` and `eval_ΨSq_genX_ne_zero` do not. -/
theorem ψ_gen_ne_zero {n : ℤ} (hn : ((n : ℤ) : F) ≠ 0) :
    ((WF).ψ n).evalEval (genX W) (genY W) ≠ 0 := by
  intro h
  exact eval_ΨSq_genX_ne_zero hn (by rw [← ψ_sq_evalEval equation_gen, h]; ring)


-- @@ L119-119 verbatim
variable [W.IsElliptic]


-- @@ L121-136 verbatim
open Classical in
/-- **`y(n • 𝒫) = ωₙ(genX, genY)/(2·ψₙ(genX, genY)³)`**, at every index with `((n : ℤ) : F) ≠ 0`,
over a field of characteristic `≠ 2`.

This is `WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`) applied to the curve `W ⁄ F(W)` at the point `𝒫`, exactly
as `xCoord_nsmul_genericPoint` applies `hasXCoordFormula_of_two_ne_zero` there.  Its one hypothesis
is `ΨSqₙ(genX) ≠ 0`, which is `eval_ΨSq_genX_ne_zero`. -/
theorem yCoord_nsmul_genericPoint (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0) :
    (n • genericPoint (W := W)).yCoord
      = (WF).omegaY (genX W) (genY W) (n : ℤ) := by
  obtain ⟨h', hP⟩ :=
    nsmul_eq_some_omegaY_of_ΨSq_ne_zero (W := WF)
      (two_ne_zero_functionField h2) nonsingular_gen (n := n) (eval_ΨSq_genX_ne_zero hn)
  rw [show (genericPoint (W := W)) = Point.some (genX W) (genY W) nonsingular_gen from rfl, hP,
    Point.yCoord_some]


-- @@ L138-155 verbatim
open Classical in
/-- **The cleared form**: `2·ψₙ³·y(n • 𝒫)` is the numerator of `ωₙ`, with no division anywhere.

⚠️ The parity factor `if Even n then 1 else ψ₂` is `WeierstrassCurve.Affine.omegaY`'s own
definition (`EllipticCurves.Torsion.NsmulYCoord`) and is not a normalisation chosen here; it
descends from `WeierstrassCurve.Ω_factor`, which carries `ψ₂` at even `n` and `ψ₂²` at odd `n` at
the level of the bivariate `Ψ`.  The denominator cleared is nonzero — `ψ_gen_ne_zero` and
`(2 : F(W)) ≠ 0` — which is what makes the two forms equivalent. -/
theorem two_mul_ψ_pow_mul_yCoord_nsmul_genericPoint (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) :
    2 * ((WF).ψ (n : ℤ)).evalEval (genX W) (genY W) ^ 3 * (n • genericPoint (W := W)).yCoord
      = (if Even (n : ℤ) then 1 else 2 * genY W + (WF).a₁ * genX W + (WF).a₃) *
            ((WF).preΩ (n : ℤ)).eval (genX W) -
          ((WF).ψ (n : ℤ)).evalEval (genX W) (genY W) *
            ((WF).a₁ * ((WF).Φ (n : ℤ)).eval (genX W) +
              (WF).a₃ * ((WF).ΨSq (n : ℤ)).eval (genX W)) := by
  rw [yCoord_nsmul_genericPoint h2 hn, omegaY, mul_div_cancel₀]
  exact mul_ne_zero (two_ne_zero_functionField h2) (pow_ne_zero 3 (ψ_gen_ne_zero hn))


-- @@ L157-157 verbatim
/-! ## The two generator images of `[n]∗` -/


-- @@ L159-168 verbatim
open Classical in
/-- **`[n]∗` on the second generator, in division-polynomial form**: `genY ↦ ωₙ/(2ψₙ³)`.

⚠️ This is the statement `EllipticCurves.FunctionField.MulByNXCoordFormula` records as the half of
the identification of the two `[n]∗`s that it does **not** prove. -/
theorem mulByNEndo_genY_eq_omegaY (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) :
    mulByNEndo n hT (genY W)
      = (WF).omegaY (genX W) (genY W) (n : ℤ) := by
  rw [mulByNEndo_genY, yCoord_nsmul_genericPoint h2 hn]


-- @@ L170-178 verbatim
/-- **`[n]∗` on the first generator, in division-polynomial form**: `genX ↦ Φₙ(genX)/ΨSqₙ(genX)`.
⚠️ No new content — `mulByNEndo_genX` composed with the merged `xCoord_nsmul_genericPoint`
(`EllipticCurves.FunctionField.MulByNXCoordFormula`); it is stated here so that the pair can be
read off in one place. -/
theorem mulByNEndo_genX_eq_ΦDivΨSq (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) :
    mulByNEndo n hT (genX W)
      = aeval (genX W) (W.Φ (n : ℤ)) / aeval (genX W) (W.ΨSq (n : ℤ)) := by
  rw [mulByNEndo_genX, xCoord_nsmul_genericPoint h2 hn]


-- @@ L180-200 verbatim
open Classical in
/-- **The identification of the two `[n]∗`s** — `#405`'s deliverable 3, in the form that makes its
deliverable 2 unnecessary.

Any ring endomorphism of `F(W)` which fixes `F` and sends the two generators to the *written-down*
division-polynomial expressions is `mulByNEndo n`.  ⚠️ So a second `[n]∗` built by
`AdjoinRoot.lift` from `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` — `#405`'s deliverable 2
— would be a duplicate definition of this one and not a second object, **at every index with
`((n : ℤ) : F) ≠ 0`**.  ⚠️ Outside that range the two constructions genuinely differ in what they
can even be stated for, which is the hypothesis mismatch `#405` records. -/
theorem mulByNEndo_eq_of_genX_genY (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord)
    {f : W.FunctionField →+* W.FunctionField}
    (hc : ∀ c : F, f (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c)
    (hX : f (genX W) = aeval (genX W) (W.Φ (n : ℤ)) / aeval (genX W) (W.ΨSq (n : ℤ)))
    (hY : f (genY W) = (WF).omegaY (genX W) (genY W) (n : ℤ)) :
    f = mulByNEndo n hT :=
  functionField_ringHom_ext
    (fun c => by rw [hc c, mulByNEndo_algebraMap_base])
    (by rw [hX, mulByNEndo_genX_eq_ΦDivΨSq h2 hn])
    (by rw [hY, mulByNEndo_genY_eq_omegaY h2 hn])


-- @@ L202-214 verbatim
/-- **Non-vacuity certificate**: the hypotheses `[W.IsElliptic]`, `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0` are jointly satisfiable and the formula really does hold somewhere —
`y² = x³ + 1` over `ℚ` at `n = 5`, the curve and index `EllipticCurves.Torsion.XSupport` and
`EllipticCurves.Torsion.OmegaPairCoprime` use for their own certificates.

⚠️ It is stated over `ℚ`, not over an algebraic closure: nothing in this file needs one. -/
theorem yCoord_nsmul_genericPoint_five_y2EqX3AddOne :
    ((5 : ℕ) • genericPoint (W := EllipticCurves.Fixture.y2EqX3AddOne ℚ)).yCoord
      = ((EllipticCurves.Fixture.y2EqX3AddOne ℚ).map
            (algebraMap ℚ (EllipticCurves.Fixture.y2EqX3AddOne ℚ).FunctionField)).omegaY
          (genX (EllipticCurves.Fixture.y2EqX3AddOne ℚ))
          (genY (EllipticCurves.Fixture.y2EqX3AddOne ℚ)) ((5 : ℕ) : ℤ) :=
  yCoord_nsmul_genericPoint (by norm_num) (by norm_num)


-- @@ L216-216 verbatim
end CoordinateRing


-- @@ L218-218 verbatim
end WeierstrassCurve.Affine
