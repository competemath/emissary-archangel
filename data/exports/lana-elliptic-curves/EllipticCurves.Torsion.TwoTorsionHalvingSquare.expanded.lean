/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.HalvingExtension


-- @@ L8-109 verbatim
/-!
# The halving quartic is a square exactly at a `2`-torsion point

`EllipticCurves.Torsion.HalvingExtension` builds a separable extension over which a **`2`-torsion**
point of `W` acquires a halving, and the identity it runs on is

```
Φ₂ - C x₀ · Ψ₂Sq = (halvingX x₀)²      (`Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`)
```

under the hypothesis `hx₀ : W.Ψ₂Sq.eval x₀ = 0`.  That file's `## What is *not* here` says of the
other case, in terms:

> **A halving of a point that is not `2`-torsion.**  `hx₀ : W.Ψ₂Sq.eval x₀ = 0` is a hypothesis of
> the square identity and of everything downstream of it.

and adds that **nothing below in that file** states the case, *"in either direction"*.  **This file
states one of those two directions**, and that bullet points here for it.  The hypothesis is not
merely sufficient: it is **necessary**, and necessary in the strongest available sense — not only is
the quartic then not *that* square, it is not the square of **any** polynomial.

## The mechanism: the defect is linear and its `X`-coefficient is `2·Ψ₂Sq(x₀)`

The identity above is the vanishing of a defect that exists with no hypothesis at all.  Writing
`K := 4x₀² + b₂x₀ + b₄`, so that `halvingX x₀ = X² - 2x₀·X - K/2`, expansion gives

```
(halvingX x₀)² - (Φ₂ - C x₀ · Ψ₂Sq) = C (2·Ψ₂Sq(x₀))·X + C ((K/2)² + b₈ + b₆x₀)
```

for **every** `x₀`, away from characteristic `2` (`halvingX_sq_sub_Φ_two_sub_C_mul_Ψ₂Sq`).  ⚠️ **The
`X²` coefficient cancels identically and the `X` coefficient is `Ψ₂Sq` read at `x₀`, doubled** — so
one coefficient of one expansion carries the whole converse, and `b_relation` is not needed for it.
Only the *constant* coefficient needs `b_relation`, and it is the landed identity that supplies its
vanishing rather than the other way round (`sq_halvingX_const_of_root`).

## Why `IsSquare` and not just `halvingX`

A converse phrased at `halvingX` would say only that *this* quadratic fails.  The sharper statement
is that no quadratic succeeds, and it costs a three-line degree argument rather than a coefficient
comparison.  Write `H := halvingX x₀` and `D` for the defect.  If `Φ₂ - C x₀ · Ψ₂Sq = Q · Q` then
`(H - Q)(H + Q) = D`, whose degree is at most `1`; but `(H - Q) + (H + Q) = C 2 · H` has degree
exactly `2`, so one factor has degree at least `2`, and a product of two nonzero polynomials over a
field has the degree of the sum.  Hence a factor vanishes, hence `D = 0`.  ⚠️ **Nothing in that
argument looks at `Q`'s degree or leading coefficient**, which is what keeps it short.

## Main statements

**The hypotheses the bullets omit**, keyed on the binders and not on the names.  **All eight**
statements listed below bind `(2 : F) ≠ 0`, and **three** bind one thing more:
`not_isSquare_Φ_two_sub_C_mul_Ψ₂Sq` binds `W.Ψ₂Sq.eval x₀ ≠ 0`, `sq_halvingX_const_of_root` binds
`W.Ψ₂Sq.eval x₀ = 0`, and `eval_Ψ₂Sq_eq_zero_of_isSquare` binds
`IsSquare (W.Φ 2 - C x₀ * W.Ψ₂Sq)`.  The remaining **five** bind nothing beyond `(2 : F) ≠ 0`.
`x₀` is **explicit** in those five and **implicit** in the three, which is the same split read
from the other side.  ⚠️ **No statement below binds a typeclass hypothesis beyond `[Field F]`** —
no `[W.IsElliptic]`, no `[DecidableEq F]`, no `[IsAlgClosed F]` — and **none binds
`W.Ψ₂Sq.Separable`**.  ⚠️ `W` is a bare `WeierstrassCurve.Affine F` throughout and is never assumed
elliptic, so these statements reach singular Weierstrass curves as well; that is inherited from
`Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`, which needs no ellipticity either.

* `WeierstrassCurve.Affine.halvingX_sq_sub_Φ_two_sub_C_mul_Ψ₂Sq`: the defect identity, with no
  hypothesis on `x₀`.
* `WeierstrassCurve.Affine.degree_halvingX_sq_sub_le` and
  `WeierstrassCurve.Affine.coeff_one_halvingX_sq_sub`: the two readings of the defect the converse
  uses — its degree is at most `1`, and its `X`-coefficient is `2·Ψ₂Sq(x₀)`.
* `WeierstrassCurve.Affine.eval_Ψ₂Sq_eq_zero_of_isSquare`: **the converse** — if the quartic is a
  square in `F[X]` then `x₀` is a root of `Ψ₂Sq`.
* `WeierstrassCurve.Affine.isSquare_Φ_two_sub_C_mul_Ψ₂Sq_iff` and
  `WeierstrassCurve.Affine.Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq_iff`: the two `iff`s, the second
  being the landed identity's own statement turned into a characterisation.
* `WeierstrassCurve.Affine.not_isSquare_Φ_two_sub_C_mul_Ψ₂Sq`: the negative form, which is the one
  a reader of `HalvingExtension`'s bullet is looking for.
* `WeierstrassCurve.Affine.sq_halvingX_const_of_root`: the constant coefficient of the defect,
  read at a root — a `b`-invariant identity that falls out of the landed theorem.

## What is *not* here

* ⚠️ **Separability of the quartic for `x₀` outside the `2`-torsion.**  The same bullet of
  `HalvingExtension` records that the quartic is generically separable there, italicising the word.
  Nothing below says that: *not a square* is strictly weaker than *separable* — a quartic can fail
  to be a square and still have a repeated root — and the separable statement needs a quartic
  discriminant, which the section headed
  *"The quartic is not separable, and that is why this is not `#1985` again"* records as
  unavailable at this index.  **This file settles the square question and leaves the separability
  question open**, so the bullet's *"in either direction"* is narrowed in one direction only.
* **Any statement about halvings.**  No point of `W` appears below, and nothing here is said about
  `exists_nsmul_two_eq_some_of_root` or about any extension of `F`.  The bridge from *"the quartic
  is not a square"* to *"the halving costs a quartic extension rather than a quadratic one"* is a
  degree argument this file does not make.
* **Characteristic `2`.**  `halvingX` divides by `2` and every statement below carries
  `(2 : F) ≠ 0`; nothing here decides anything at characteristic `2`, in either direction.
* **`n = 3`, and `n` in general.**  Every statement below is at `n = 2`: `Φ 2`, `Ψ₂Sq` and one
  quadratic.  Nothing is stated at a general index.

## Non-vacuity

`EllipticCurves.Fixture.y2EqX3SubX` at `R = ℚ` — the curve `y² = x³ - x`, whose `2`-torsion cubic
is `4X³ - 4X` with roots `0`, `1`, `-1` — certifies **both** verdicts of the `iff` on one curve:
`x₀ = 0` is a root and the quartic is a square there, and `x₀ = 2` is not a root and the quartic is
a square for no polynomial.  ⚠️ **Both halves are needed**: a curve exhibiting only the negative
verdict would leave `isSquare_Φ_two_sub_C_mul_Ψ₂Sq_iff` green with its left side never satisfied.
-/


-- @@ L111-111 verbatim
open Polynomial


-- @@ L113-114 verbatim
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])


-- @@ L116-116 verbatim
namespace WeierstrassCurve.Affine


-- @@ L118-118 verbatim
variable {F : Type*} [Field F] {W : Affine F}


-- @@ L120-120 verbatim
/-! ## The defect of the square identity -/


-- @@ L122-139 expanded
/-- **The square identity has a linear defect, and it exists at every `x₀`.**

`(halvingX x₀)² - (Φ₂ - C x₀ · Ψ₂Sq)` is `C (2·Ψ₂Sq(x₀))·X + C ((K/2)² + b₈ + b₆x₀)` with
`K = 4x₀² + b₂x₀ + b₄`.  ⚠️ **No hypothesis on `x₀`**, and no `b_relation`: the `X³` and `X²`
coefficients cancel on the identity `2·(K/2) = K` alone, which is the only place `(2 : F) ≠ 0` is
used.  `Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq` is the statement that both remaining coefficients
vanish at a root of `Ψ₂Sq`; this lemma is what is left when the root hypothesis is dropped. -/
theorem halvingX_sq_sub_Φ_two_sub_C_mul_Ψ₂Sq (h2 : (2 : F) ≠ 0) (x₀ : F) :
    (W.halvingX x₀) ^ 2 - (W.Φ 2 - C x₀ * W.Ψ₂Sq) =
      C (2 * W.Ψ₂Sq.eval x₀) * X +
        C (((4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) / 2) ^ 2 + W.b₈ + W.b₆ * x₀) :=
  by
  set c : F := (4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) / 2 with hcdef
  have hc : 2 * c = 4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄ := by rw [hcdef]; field_simp
  have hev : W.Ψ₂Sq.eval x₀ = 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ := by
    simp [WeierstrassCurve.Ψ₂Sq]
  rw [hev, Φ_two, WeierstrassCurve.Ψ₂Sq, halvingX, ← hcdef]
  linear_combination (norm :=
    (simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]; ring1))
    (C (-1 : F) * X ^ 2 + C (2 * x₀) * X) * congrArg C hc


-- @@ L141-147 verbatim
/-- **The defect has degree at most `1`.**  This is the half of the defect identity the degree
argument in `eval_Ψ₂Sq_eq_zero_of_isSquare` consumes; the quartic and the square of the quadratic
agree in their top three coefficients whatever `x₀` is. -/
theorem degree_halvingX_sq_sub_le (h2 : (2 : F) ≠ 0) (x₀ : F) :
    ((W.halvingX x₀) ^ 2 - (W.Φ 2 - C x₀ * W.Ψ₂Sq)).degree ≤ 1 := by
  rw [halvingX_sq_sub_Φ_two_sub_C_mul_Ψ₂Sq h2]
  compute_degree


-- @@ L149-154 verbatim
/-- **The defect's `X`-coefficient is `Ψ₂Sq` read at `x₀`, doubled.**  This is the whole converse:
one coefficient of one expansion, with no `b_relation` and no hypothesis on `x₀`. -/
theorem coeff_one_halvingX_sq_sub (h2 : (2 : F) ≠ 0) (x₀ : F) :
    ((W.halvingX x₀) ^ 2 - (W.Φ 2 - C x₀ * W.Ψ₂Sq)).coeff 1 = 2 * W.Ψ₂Sq.eval x₀ := by
  rw [halvingX_sq_sub_Φ_two_sub_C_mul_Ψ₂Sq h2, coeff_add, coeff_C_mul, coeff_X_one, coeff_C,
    mul_one, if_neg one_ne_zero, add_zero]


-- @@ L156-156 verbatim
/-! ## The converse -/


-- @@ L158-199 verbatim
/-- **If the halving quartic is a square in `F[X]`, the point is `2`-torsion.**

The converse of `Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`, and it quantifies over *every* polynomial
rather than over the one that file builds.  ⚠️ **The proof never looks at `Q`'s degree or leading
coefficient.**  With `H := halvingX x₀` and `D` the defect, `(H - Q)(H + Q) = D` has degree at most
`1` while `(H - Q) + (H + Q) = C 2 · H` has degree exactly `2`, so one summand has degree at least
`2`; over a field the degree of a product of nonzero factors is the sum of their degrees, so a
factor must vanish and then `D = 0`.  Reading `D`'s `X`-coefficient finishes it. -/
theorem eval_Ψ₂Sq_eq_zero_of_isSquare (h2 : (2 : F) ≠ 0) {x₀ : F}
    (hsq : IsSquare (W.Φ 2 - C x₀ * W.Ψ₂Sq)) : W.Ψ₂Sq.eval x₀ = 0 := by
  obtain ⟨Q, hQ⟩ := hsq
  set D : F[X] := (W.halvingX x₀) ^ 2 - (W.Φ 2 - C x₀ * W.Ψ₂Sq) with hDdef
  have hfac : (W.halvingX x₀ - Q) * (W.halvingX x₀ + Q) = D := by rw [hDdef, hQ]; ring
  have hdegD : D.degree ≤ 1 := degree_halvingX_sq_sub_le h2 x₀
  have hsum : (W.halvingX x₀ - Q) + (W.halvingX x₀ + Q) = C 2 * W.halvingX x₀ := by
    rw [map_ofNat]; ring
  have hD0 : D = 0 := by
    by_contra hne
    have hne₁ : W.halvingX x₀ - Q ≠ 0 := fun h => hne (by rw [← hfac, h, zero_mul])
    have hne₂ : W.halvingX x₀ + Q ≠ 0 := fun h => hne (by rw [← hfac, h, mul_zero])
    have hdegsum :
        (2 : WithBot ℕ) ≤ max (W.halvingX x₀ - Q).degree (W.halvingX x₀ + Q).degree := by
      have hCH : (C (2 : F) * W.halvingX x₀).degree = 2 := by
        rw [degree_C_mul (by simpa using h2), degree_halvingX]
      calc (2 : WithBot ℕ) = (C (2 : F) * W.halvingX x₀).degree := hCH.symm
        _ = ((W.halvingX x₀ - Q) + (W.halvingX x₀ + Q)).degree := by rw [hsum]
        _ ≤ _ := degree_add_le _ _
    have hmul : D.degree = (W.halvingX x₀ - Q).degree + (W.halvingX x₀ + Q).degree := by
      rw [← hfac, degree_mul]
    have hge₁ : (0 : WithBot ℕ) ≤ (W.halvingX x₀ - Q).degree := zero_le_degree_iff.mpr hne₁
    have hge₂ : (0 : WithBot ℕ) ≤ (W.halvingX x₀ + Q).degree := zero_le_degree_iff.mpr hne₂
    rcases max_cases (W.halvingX x₀ - Q).degree (W.halvingX x₀ + Q).degree with
      ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hdegsum
      have : (2 : WithBot ℕ) ≤ D.degree := hmul ▸ le_add_of_le_of_nonneg hdegsum hge₂
      exact absurd (this.trans hdegD) (by decide)
    · rw [he] at hdegsum
      have : (2 : WithBot ℕ) ≤ D.degree := hmul ▸ le_add_of_nonneg_of_le hge₁ hdegsum
      exact absurd (this.trans hdegD) (by decide)
  have hcoeff := coeff_one_halvingX_sq_sub (W := W) h2 x₀
  rw [← hDdef, hD0, coeff_zero] at hcoeff
  exact (mul_eq_zero.mp hcoeff.symm).resolve_left h2


-- @@ L201-205 verbatim
/-- **The halving quartic is a square exactly at a root of `Ψ₂Sq`.** -/
theorem isSquare_Φ_two_sub_C_mul_Ψ₂Sq_iff (h2 : (2 : F) ≠ 0) (x₀ : F) :
    IsSquare (W.Φ 2 - C x₀ * W.Ψ₂Sq) ↔ W.Ψ₂Sq.eval x₀ = 0 := by
  refine ⟨eval_Ψ₂Sq_eq_zero_of_isSquare h2, fun hx₀ => ⟨W.halvingX x₀, ?_⟩⟩
  rw [Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq h2 hx₀, sq]


-- @@ L207-212 verbatim
/-- **The landed identity holds exactly at a root of `Ψ₂Sq`** — the same characterisation read at
the one quadratic `HalvingExtension` builds. -/
theorem Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq_iff (h2 : (2 : F) ≠ 0) (x₀ : F) :
    W.Φ 2 - C x₀ * W.Ψ₂Sq = (W.halvingX x₀) ^ 2 ↔ W.Ψ₂Sq.eval x₀ = 0 :=
  ⟨fun h => eval_Ψ₂Sq_eq_zero_of_isSquare h2 ⟨W.halvingX x₀, by rw [h, sq]⟩,
    Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq h2⟩


-- @@ L214-219 verbatim
/-- **Away from the `2`-torsion the halving quartic is the square of nothing** — the statement
`EllipticCurves.Torsion.HalvingExtension`'s *"A halving of a point that is not `2`-torsion"* bullet
leaves open in this direction. -/
theorem not_isSquare_Φ_two_sub_C_mul_Ψ₂Sq (h2 : (2 : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ ≠ 0) : ¬ IsSquare (W.Φ 2 - C x₀ * W.Ψ₂Sq) :=
  fun hsq => hx₀ (eval_Ψ₂Sq_eq_zero_of_isSquare h2 hsq)


-- @@ L221-230 verbatim
/-- **The constant coefficient of the defect, read at a root** — `((4x₀² + b₂x₀ + b₄)/2)²` is
`-(b₈ + b₆x₀)` there.  It is the half of the square identity that `b_relation` pays for, and it is
recovered here from the landed theorem rather than reproved. -/
theorem sq_halvingX_const_of_root (h2 : (2 : F) ≠ 0) {x₀ : F} (hx₀ : W.Ψ₂Sq.eval x₀ = 0) :
    ((4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) / 2) ^ 2 + W.b₈ + W.b₆ * x₀ = 0 := by
  have hD : (W.halvingX x₀) ^ 2 - (W.Φ 2 - C x₀ * W.Ψ₂Sq) = 0 := by
    rw [Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq h2 hx₀, sub_self]
  have := congrArg (fun p => Polynomial.eval 0 p)
    (hD.symm.trans (halvingX_sq_sub_Φ_two_sub_C_mul_Ψ₂Sq h2 x₀))
  simpa using this.symm


-- @@ L232-232 verbatim
/-! ## Non-vacuity -/


-- @@ L234-234 verbatim
section Nonvacuity


-- @@ L236-236 verbatim
open EllipticCurves.Fixture


-- @@ L238-243 verbatim
/-! The certificate curve is `EllipticCurves.Fixture.y2EqX3SubX` at `R = ℚ`: `y² = x³ - x`, whose
`2`-torsion cubic is `4X³ - 4X`, with roots `0`, `1` and `-1`.  ⚠️ **Both verdicts of
`isSquare_Φ_two_sub_C_mul_Ψ₂Sq_iff` are computed on that one curve** — `x₀ = 0` is a root and
`x₀ = 2` is not — because a certificate exhibiting only the negative verdict would leave the `iff`
green with its left-hand side never satisfied, and one exhibiting only the positive verdict would
certify nothing this file adds. -/


-- @@ L245-249 verbatim
private lemma eval_Ψ₂Sq_y2EqX3SubX (x : ℚ) :
    (y2EqX3SubX ℚ).Ψ₂Sq.eval x = 4 * x ^ 3 - 4 * x := by
  simp [WeierstrassCurve.Ψ₂Sq, y2EqX3SubX, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring


-- @@ L251-256 verbatim
/-- **The positive verdict.**  `0` is a root of the certificate curve's `2`-torsion cubic, so the
halving quartic there is a square — this is `Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq` inhabited. -/
private theorem isSquare_y2EqX3SubX_zero :
    IsSquare ((y2EqX3SubX ℚ).Φ 2 - C 0 * (y2EqX3SubX ℚ).Ψ₂Sq) := by
  rw [isSquare_Φ_two_sub_C_mul_Ψ₂Sq_iff (by norm_num), eval_Ψ₂Sq_y2EqX3SubX]
  norm_num


-- @@ L258-265 verbatim
/-- **The negative verdict.**  `2` is not a root — the cubic reads `24` there — so the halving
quartic at `x₀ = 2` is the square of no polynomial over `ℚ`.  ⚠️ This is the statement
`EllipticCurves.Torsion.HalvingExtension`'s bullet leaves open, inhabited. -/
private theorem not_isSquare_y2EqX3SubX_two :
    ¬ IsSquare ((y2EqX3SubX ℚ).Φ 2 - C 2 * (y2EqX3SubX ℚ).Ψ₂Sq) := by
  refine not_isSquare_Φ_two_sub_C_mul_Ψ₂Sq (by norm_num) ?_
  rw [eval_Ψ₂Sq_y2EqX3SubX]
  norm_num


-- @@ L267-267 verbatim
end Nonvacuity


-- @@ L269-269 verbatim
end WeierstrassCurve.Affine
