/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Galois.NormalClosureSeparable
import EllipticCurves.Torsion.DoublingSurjective
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure


-- @@ L12-178 verbatim
/-!
# The halving extension of a `2`-torsion point is separable

Let `W` be an elliptic curve over a field `F` of characteristic `≠ 2` and let `S = (x₀, y₀)` be a
`2`-torsion point of `W` — equivalently, a point whose `x`-coordinate is a root of the `2`-torsion
cubic `Ψ₂Sq`.  `EllipticCurves.Torsion.DoublingSurjective`'s `exists_nsmul_two_eq_some_of_root`
halves `S` as soon as the quartic `Φ₂ - C x₀ · Ψ₂Sq` has a root carrying a point of `W` above it.
This file builds a finite **separable** extension of `F` over which that happens, and draws the
`IsGalois` conclusion a descent argument consumes.

## ⚠️ The quartic is not separable, and that is why this is not `#1985` again

`EllipticCurves.Torsion.TwoTorsionSplittingField` (`#1985`) settles the other input to the same
chain by proving `Ψ₂Sq` separable and taking a splitting field.  **That argument cannot be copied
here by substitution.**  Over an algebraic closure the roots of `Φ₂ - C x₀ · Ψ₂Sq` are the
`x`-coordinates of the four points `Q` with `2 • Q = S`; `Q` and `-Q` share an `x`-coordinate and
`-Q = Q ⊕ S`, because `S` is `2`-torsion, so four roots counted with multiplicity sit over at most
two distinct values and the quartic has a repeated root.  A route through
`Cubic.discr_ne_zero_iff_roots_nodup`'s quartic analogue, or through
`Polynomial.nodup_aroots_iff_of_splits` on the quartic, fails on a true statement.

## The mechanism: the quartic is a perfect square, and its square root is what to adjoin

⚠️ **The repeated root is not an obstruction, it is the method.**  Write `K := 4x₀² + b₂x₀ + b₄`.
Then, for any root `x₀` of `Ψ₂Sq` and away from characteristic `2`,

```
Φ₂ - C x₀ · Ψ₂Sq = (X² - C (2x₀) · X - C (K / 2))²        (`Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`)
```

as an identity in `F[X]`.  The two inputs are `Ψ₂Sq.eval x₀ = 0` and Mathlib's
`WeierstrassCurve.b_relation` (`4b₈ = b₂b₆ - b₄²`); no hypothesis beyond `(2 : F) ≠ 0` is used and
the curve need not be elliptic for the identity itself.  The monic quadratic on the right is
`halvingX` below, and **adjoining a root of it is adjoining the `x`-coordinate of a halving**,
because a root of `halvingX` is a root of the quartic.

That quadratic is separable exactly when `Ψ₂Sq` is separable at `x₀`, and the reason is an
arithmetic coincidence worth naming:

```
discriminant (halvingX x₀) = (2x₀)² + 2K = (derivative Ψ₂Sq).eval x₀     (`discrim_halvingX`)
```

so `separable_halvingX` takes the hypothesis `W.Ψ₂Sq.Separable` and reads it at `x₀` through
`Polynomial.eval_ne_zero_of_isCoprime` (`EllipticCurves.DivisionPolynomial.Coprime`).
⚠️ **`W.Ψ₂Sq.Separable` is taken as a hypothesis and is not reproved here.**  It is exactly
`#1985`'s `separable_Ψ₂Sq`, whose branch is not merged at the time of writing; the `Nonvacuity`
section below discharges it over `ℚ` from an explicit Bézout certificate, so nothing in this file
waits on that branch.

The `y`-coordinate costs a second quadratic and is easier: `halvingY x` is the Weierstrass equation
read as a quadratic in `y`, and its discriminant is `Ψ₂Sq.eval x` (`discrim_halvingY`), which is
nonzero at a root of `halvingX` because `Φ₂` and `Ψ₂Sq` have no common root
(`eval_Φ_two_ne_zero_of_root_ΨSq`) — that is `Ψ₂Sq_eval_ne_zero_of_root_halvingX`, and it is the
statement *"a halving of a nonzero `2`-torsion point has order `4` and so is not itself
`2`-torsion"* in the form the polynomials see.

## The field

`halvingField W x₀` is the two-step tower: a splitting field `L₁` of `halvingX x₀` over `F`, then a
splitting field of the `y`-quadratic over `L₁`.  Each floor is a splitting field of a separable
quadratic, hence Galois, so the tower is finite and separable over `F`
(`isSeparable_halvingField`, `finiteDimensional_halvingField`).

⚠️ **Separable and finite is not Galois**, normality not being transitive, so the Galois statement
is made about the normal closure: `isGalois_normalClosure_halvingField`.  That step mentions no
curve, and it is not taken here: `EllipticCurves.Galois.NormalClosureSeparable` states it for an
arbitrary separable extension, records why `IsGalois.normalClosure` does not supply it at
this tree's pin, and this file's theorem is the corollary of it at the halving field.

## Main statements

**The hypotheses the bullets omit**, listed here rather than in each bullet and written out per
declaration.  *A root hypothesis* below means a hypothesis of the form `….eval … = 0` — of `Ψ₂Sq`,
or of either quadratic, over `F` or over an extension of it.  The five groups partition this file's
**36** public declarations except for two rows that sit outside them: `discrim_halvingX`, in the
note that closes the last group, and `Polynomial.separable_quadratic`, which takes no hypothesis
but its own discriminant one.

* `(2 : F) ≠ 0`, a root `hx₀ : W.Ψ₂Sq.eval x₀ = 0`, and neither `W.Ψ₂Sq.Separable` nor
  `[W.IsElliptic]`: `Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq` and `eval_Φ_two_eq_of_root_halvingX`.
* `(2 : F) ≠ 0` and `W.Ψ₂Sq.Separable` and `hx₀`, and **not** `[W.IsElliptic]`:
  `separable_halvingX` and `isGalois_halvingXField`.
* `(2 : F) ≠ 0` and `[W.IsElliptic]`, with `hx₀` where an `x₀` is named:
  `Ψ₂Sq_eval_ne_zero_of_root_halvingX`, `Ψ₂Sq_eval_halvingXRoot_ne_zero`, `isGalois_halvingField`,
  `exists_nsmul_two_eq_some_of_roots` and `exists_nsmul_two_eq_halvingField` — the last two taking a
  `[DecidableEq _]` as well, which the `Point` group structure needs — and, with
  `W.Ψ₂Sq.Separable` also, `isSeparable_halvingField` and `isGalois_normalClosure_halvingField`.
* A root hypothesis, and neither `(2 : F) ≠ 0` nor `[W.IsElliptic]` nor `W.Ψ₂Sq.Separable`:
  `eval_Ψ₂Sq_baseChange` (`hx₀` itself), `equation_of_eval_halvingY_eq_zero` (a root of the
  `y`-quadratic), `eval_halvingX_baseChange` and `eval_halvingY_baseChange` (a root of a quadratic
  over the lower field).
* ⚠️ **Neither `(2 : F) ≠ 0` nor `[W.IsElliptic]` nor a root hypothesis**: `halvingX`, `halvingY`,
  `halvingX_monic`, `halvingY_monic`, `degree_halvingX`, `degree_halvingY`, `discrim_halvingY`,
  `separable_halvingY` — whose `W.Ψ₂Sq.eval x ≠ 0` is the negation of a root hypothesis and not one
  — `map_halvingX`, `map_halvingY`, `halvingXField`, `halvingXRoot`, `eval_halvingXRoot`,
  `halvingYPoly`, `halvingField`, `halvingYRoot`, `eval_halvingYRoot`,
  `finiteDimensional_halvingXField` and `finiteDimensional_halvingField`.
  ⚠️ `discrim_halvingX` is in none of the five groups: it takes `(2 : F) ≠ 0` and **no** root
  hypothesis, the only public declaration here that does, because it is an identity at every `x₀`.

* `Polynomial.separable_quadratic`: a monic quadratic with nonzero discriminant is separable.  The
  only **public** declaration here that mentions no curve, and the only one in namespace
  `Polynomial`.
* `WeierstrassCurve.Affine.halvingX`: the monic quadratic whose roots are the `x`-coordinates of the
  halvings of the `2`-torsion point at `x₀`;
* `WeierstrassCurve.Affine.Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`: the quartic is its square;
* `WeierstrassCurve.Affine.discrim_halvingX`: its discriminant is `(derivative Ψ₂Sq).eval x₀`;
* `WeierstrassCurve.Affine.separable_halvingX`: it is separable;
* `WeierstrassCurve.Affine.halvingY` and `WeierstrassCurve.Affine.separable_halvingY`: the
  `y`-quadratic above an `x`, and its separability;
* `WeierstrassCurve.Affine.exists_nsmul_two_eq_some_of_roots`: a root of each quadratic halves the
  point;
* `WeierstrassCurve.Affine.halvingXField` and `WeierstrassCurve.Affine.halvingField`: the two floors
  of the tower;
* `WeierstrassCurve.Affine.isGalois_halvingXField` and
  `WeierstrassCurve.Affine.isGalois_halvingField`: each floor is Galois over the one below;
* `WeierstrassCurve.Affine.isSeparable_halvingField` and
  `WeierstrassCurve.Affine.finiteDimensional_halvingField`: the tower is separable and finite
  over `F`;
* `WeierstrassCurve.Affine.isGalois_normalClosure_halvingField`: its normal closure is Galois
  over `F`;
* `WeierstrassCurve.Affine.exists_nsmul_two_eq_halvingField`: `S` is `2`-divisible over the tower.

## What is *not* here

* **A discharge of `hprin` over a general field.**  `#962` records that gate and this file supplies
  one of its ledger rows.  No statement below mentions a divisor, a place or a principal divisor,
  and the assembly of `#1985`, this file, Hilbert 90 and PR #757 is the row after this one.
* **A reproof of `#1985`.**  `W.Ψ₂Sq.Separable` is a hypothesis everywhere it is used below and is
  never derived from the discriminant; `Cubic.discr_ne_zero_iff_roots_nodup` is **not used** — no
  proof below invokes it, and the only other mention of it in this file says just that the route
  through its quartic analogue fails — and `EllipticCurves.Torsion.TwoTorsionSplittingField` is not
  imported.
* **`n = 3`.**  Every statement below is at `n = 2`: `Φ 2`, `Ψ₂Sq` and the two quadratics.  Nothing
  is stated at a general index and nothing here applies to
  `EllipticCurves.Torsion.ThreeTorsionStructure`.
* **A halving of a point that is not `2`-torsion.**  `hx₀ : W.Ψ₂Sq.eval x₀ = 0` is a hypothesis of
  the square identity and of everything downstream of it.  ⚠️ For an `S` outside `E[2]` the quartic
  is generically *separable* and the whole mechanism of this file is unnecessary there; **nothing
  below** states that case, in either direction.  ⚠️ **One of the two directions is stated
  elsewhere**, and it is the one this file's own mechanism decides:
  `EllipticCurves.Torsion.TwoTorsionHalvingSquare` proves that the quartic is the square of **no**
  polynomial over `F` when `W.Ψ₂Sq.eval x₀ ≠ 0` (`not_isSquare_Φ_two_sub_C_mul_Ψ₂Sq`), and that the
  two sides are equivalent (`isSquare_Φ_two_sub_C_mul_Ψ₂Sq_iff`), so
  `Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`'s root hypothesis is necessary and not merely sufficient.
  *Not a square* is strictly weaker than *separable* — a quartic can fail to be a square and still
  have a repeated root — so the separability called generic above is left open there too, in that
  module's own `## What is *not* here`.
* **Characteristic `2`.**  `halvingX` divides by `2` and is junk there; every statement that uses it
  non-trivially carries `(2 : F) ≠ 0`.  Nothing below decides whether a halving extension is
  separable in characteristic `2`.
* **`IsGalois F (halvingField W x₀)` itself.**  It is `IsGalois` in two steps and the composite need
  not be normal; the normal closure is where the Galois statement is made.

## Non-vacuity

The `Nonvacuity` section certifies over `ℚ` on `EllipticCurves.Fixture.y2EqX3SubX` — `y² = x³ - x`,
the curve this tree names as having full rational `2`-torsion and **no rational halving of any of
it** — that the extension this file produces is a **proper** one: `halvingX 0` is `X² + 1`, which
has no rational root, so the halving `x`-coordinate is outside the image of `ℚ`.  It also discharges
`W.Ψ₂Sq.Separable` there from an explicit Bézout certificate, which is what makes the main theorems
of this file inhabited without `#1985`'s branch.  ⚠️ A curve whose `2`-torsion point is already
`2`-divisible over `ℚ` — `EllipticCurves.Fixture.y2EqX3Add4X` is one, its `halvingX 0` being
`X² - 4` — would leave everything below green and certify only the case in which the tower is `ℚ`
itself.
-/


-- @@ L180-180 verbatim
open Polynomial


-- @@ L182-183 verbatim
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])


-- @@ L185-185 verbatim
namespace Polynomial


-- @@ L187-204 expanded
/-- **A monic quadratic with nonzero discriminant is separable.**

The Bézout certificate is one line: `(derivative p)² - C 4 * p = C (b² - 4c)`, which is a unit
whenever the discriminant is.  ⚠️ It takes no hypothesis on the characteristic: in characteristic
`2` the discriminant is `b²`, and `X² + C b * X + C c` with `b ≠ 0` is separable there.

⚠️ **No quadratic case of this was found in the pinned Mathlib** — searched for the name and for a
`Separable` statement over `X ^ 2 + C b * X + C c`, and `Polynomial.separable_X_pow_sub_C` is the
nearest thing there is — so it is stated here, and it is an upstream candidate as it stands. -/
theorem separable_quadratic {K : Type*} [Field K] {b c : K} (hD : b ^ 2 - 4 * c ≠ 0) :
    (X ^ 2 + C b * X + C c : K[X]).Separable :=
  by
  have hderiv : derivative (X ^ 2 + C b * X + C c : K[X]) = C 2 * X + C b := by
    simp [derivative_add, derivative_mul, derivative_pow]
  rw [Polynomial.Separable, hderiv]
  refine ⟨C (-4 * (b ^ 2 - 4 * c)⁻¹), C ((b ^ 2 - 4 * c)⁻¹) * (C 2 * X + C b), ?_⟩
  have h : (C ((b ^ 2 - 4 * c)⁻¹) * C (b ^ 2 - 4 * c) : K[X]) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hD, C_1]
  linear_combination (norm :=
    (simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]; ring1)) h


-- @@ L206-206 verbatim
end Polynomial


-- @@ L208-208 verbatim
namespace WeierstrassCurve.Affine


-- @@ L210-210 verbatim
variable {F : Type*} [Field F] {W : Affine F}


-- @@ L212-213 verbatim
private lemma four_ne_zero_of_two_ne_zero' (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2


-- @@ L215-215 verbatim
/-! ## The halving quadratic -/


-- @@ L217-227 verbatim
variable (W) in
/-- **The halving quadratic at `x₀`**: the monic quadratic
`X² - 2x₀·X - (4x₀² + b₂x₀ + b₄)/2`.

For a root `x₀` of `Ψ₂Sq` and away from characteristic `2` its square is the quartic
`Φ₂ - C x₀ · Ψ₂Sq` (`Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq`), so a root of it is an `x`-coordinate of
a halving of the `2`-torsion point at `x₀`.  ⚠️ Nothing constrains `x₀` in the definition; the root
hypothesis enters at the identity and at everything downstream of it, and in characteristic `2` the
division by `2` makes this junk. -/
noncomputable def halvingX (x₀ : F) : F[X] :=
  X ^ 2 + C (-(2 * x₀)) * X + C (-((4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) / 2))


-- @@ L229-230 verbatim
theorem halvingX_monic (x₀ : F) : (W.halvingX x₀).Monic := by
  rw [halvingX]; monicity!


-- @@ L232-233 verbatim
theorem degree_halvingX (x₀ : F) : (W.halvingX x₀).degree = 2 := by
  rw [halvingX]; compute_degree!


-- @@ L235-257 expanded
/-- **The quartic cut out by halving is the square of the halving quadratic.**

The identity that makes this file possible: it turns *"the polynomial has a repeated root"* from an
obstruction into a construction, since a root of a square is a root of its square root.  The two
inputs are the root hypothesis and Mathlib's `WeierstrassCurve.b_relation` (`4b₈ = b₂b₆ - b₄²`);
both sides are multiplied by `C 4` first, because the constant coefficient of the quadratic carries
a division by `2` that no ring identity sees. -/
theorem Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq (h2 : (2 : F) ≠ 0) {x₀ : F} (hx₀ : W.Ψ₂Sq.eval x₀ = 0) :
    W.Φ 2 - C x₀ * W.Ψ₂Sq = (W.halvingX x₀) ^ 2 :=
  by
  set c : F := (4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) / 2 with hcdef
  have hc : 2 * c = 4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄ := by rw [hcdef]; field_simp
  have hE2 : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0 := by
    simpa [Ψ₂Sq, eval_add, eval_mul, eval_pow] using hx₀
  have hE2' : (C (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) : F[X]) = 0 := by
    rw [hE2, map_zero]
  have hb' : (C (4 * W.b₈) : F[X]) = C (W.b₂ * W.b₆ - W.b₄ ^ 2) := by rw [W.b_relation]
  have key : C (4 : F) * (W.Φ 2 - C x₀ * W.Ψ₂Sq) = C (4 : F) * (W.halvingX x₀) ^ 2 :=
    by
    rw [Φ_two, Ψ₂Sq, halvingX, ← hcdef]
    linear_combination (norm :=
      (simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]; ring1))
      (C (-8 : F) * X + C (-(4 * x₀ + W.b₂))) * hE2' + (C (-1 : F)) * hb' +
        (C (4 : F) * X ^ 2 + C (-(8 * x₀)) * X + C (-(2 * c) - (4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄))) *
          congrArg C hc
  exact mul_left_cancel₀ (by simpa using four_ne_zero_of_two_ne_zero' h2) key


-- @@ L259-271 verbatim
/-- **The discriminant of the halving quadratic is `Ψ₂Sq` differentiated at `x₀`.**

`b² - 4c` for `halvingX x₀` is `4x₀² + 2(4x₀² + b₂x₀ + b₄) = 12x₀² + 2b₂x₀ + 2b₄`, and that is
`derivative (4X³ + b₂X² + 2b₄X + b₆)` evaluated at `x₀` on the nose.  It is the whole reason
separability of the cubic buys separability of the quadratic. -/
theorem discrim_halvingX (h2 : (2 : F) ≠ 0) (x₀ : F) :
    (-(2 * x₀)) ^ 2 - 4 * (-((4 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) / 2))
      = (derivative W.Ψ₂Sq).eval x₀ := by
  simp only [WeierstrassCurve.Ψ₂Sq, derivative_add, derivative_mul, derivative_C, derivative_X,
    derivative_pow, eval_add, eval_mul, eval_pow, eval_C, eval_X, zero_mul, add_zero, zero_add,
    mul_one]
  field_simp
  ring


-- @@ L273-284 verbatim
/-- **The halving quadratic is separable** at a root of a separable `Ψ₂Sq`.

⚠️ `W.Ψ₂Sq.Separable` is a **hypothesis**: it is `#1985`'s `separable_Ψ₂Sq`
(`EllipticCurves.Torsion.TwoTorsionSplittingField`), which this file does not import and does not
reprove.  Read at `x₀` through `Polynomial.eval_ne_zero_of_isCoprime`, it says the derivative does
not vanish there, which `discrim_halvingX` turns into the discriminant condition. -/
theorem separable_halvingX (h2 : (2 : F) ≠ 0) (hsep : W.Ψ₂Sq.Separable) {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ = 0) : (W.halvingX x₀).Separable := by
  rw [halvingX]
  refine Polynomial.separable_quadratic ?_
  rw [discrim_halvingX h2]
  exact Polynomial.eval_ne_zero_of_isCoprime hsep.symm hx₀


-- @@ L286-293 verbatim
/-- **A root of the halving quadratic is a root of the quartic**, in the cleared-denominator form
`exists_nsmul_two_eq_some_of_root` consumes. -/
theorem eval_Φ_two_eq_of_root_halvingX (h2 : (2 : F) ≠ 0) {x₀ : F} (hx₀ : W.Ψ₂Sq.eval x₀ = 0)
    {x : F} (hx : (W.halvingX x₀).eval x = 0) :
    (W.Φ 2).eval x = x₀ * W.Ψ₂Sq.eval x := by
  have := congrArg (eval x) (Φ_two_sub_C_mul_Ψ₂Sq_eq_halvingX_sq h2 hx₀)
  simp only [eval_sub, eval_mul, eval_C, eval_pow, hx] at this
  linear_combination this


-- @@ L295-306 verbatim
/-- **A halving `x`-coordinate is never a `2`-torsion `x`-coordinate.**

The geometric content is that a halving of a nonzero `2`-torsion point has order `4`; the proof is
that a common root of the quartic and of `Ψ₂Sq` would be a common root of `Φ₂` and `Ψ₂Sq`, and
`eval_Φ_two_ne_zero_of_root_ΨSq` (`EllipticCurves.Torsion.DoublingSurjective`) says there are none.
This is what makes the `y`-quadratic separable. -/
theorem Ψ₂Sq_eval_ne_zero_of_root_halvingX [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x₀ : F}
    (hx₀ : W.Ψ₂Sq.eval x₀ = 0) {x : F} (hx : (W.halvingX x₀).eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  intro h0
  refine eval_Φ_two_ne_zero_of_root_ΨSq x (by rwa [ΨSq_two]) ?_
  rw [eval_Φ_two_eq_of_root_halvingX h2 hx₀ hx, h0, mul_zero]


-- @@ L308-308 verbatim
/-! ## The halving `y`-quadratic -/


-- @@ L310-314 verbatim
variable (W) in
/-- **The Weierstrass equation above `x`, read as a monic quadratic in `y`.**  A root of it is a
`y`-coordinate of a point of `W` over `x` (`equation_of_eval_halvingY_eq_zero`). -/
noncomputable def halvingY (x : F) : F[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))


-- @@ L316-317 verbatim
theorem halvingY_monic (x : F) : (W.halvingY x).Monic := by
  rw [halvingY]; monicity!


-- @@ L319-320 verbatim
theorem degree_halvingY (x : F) : (W.halvingY x).degree = 2 := by
  rw [halvingY]; compute_degree!


-- @@ L322-333 verbatim
/-- **The discriminant of the `y`-quadratic is `Ψ₂Sq` evaluated at `x`.**

This is `Ψ₂Sq_eval_eq_sq` (`EllipticCurves.Torsion.TwoTorsion`) read backwards: `Ψ₂Sq.eval x` is
`(2y + a₁x + a₃)²` at a point, and `(a₁x + a₃)² + 4(x³ + a₂x² + a₄x + a₆)` is that same expression
before a point is chosen.  ⚠️ Stated in the `a`-invariants on the left, with `Ψ₂Sq` on the right;
it is an identity, so it holds at every `x` and takes no hypothesis. -/
theorem discrim_halvingY (x : F) :
    (W.a₁ * x + W.a₃) ^ 2 - 4 * (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
      = W.Ψ₂Sq.eval x := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring


-- @@ L335-338 verbatim
/-- **The `y`-quadratic is separable away from the `2`-torsion `x`-coordinates.** -/
theorem separable_halvingY {x : F} (hx : W.Ψ₂Sq.eval x ≠ 0) : (W.halvingY x).Separable := by
  rw [halvingY]
  exact Polynomial.separable_quadratic (by rw [discrim_halvingY]; exact hx)


-- @@ L340-345 verbatim
/-- **A root of the `y`-quadratic is a point of `W`.** -/
theorem equation_of_eval_halvingY_eq_zero {x y : F} (h : (W.halvingY x).eval y = 0) :
    W.Equation x y := by
  rw [equation_iff']
  simp only [halvingY, eval_add, eval_mul, eval_pow, eval_C, eval_X] at h
  linear_combination h


-- @@ L347-347 verbatim
/-! ## The halving, over any field carrying a root of each quadratic -/


-- @@ L349-361 verbatim
/-- **A `2`-torsion point is twice another point as soon as both quadratics have a root.**

The conditional form, over any field and with no algebraic closure: this is
`exists_nsmul_two_eq_some_of_root` (`EllipticCurves.Torsion.DoublingSurjective`) with its quartic
hypothesis supplied by `eval_Φ_two_eq_of_root_halvingX` and its point supplied by
`equation_of_eval_halvingY_eq_zero`.  Everything below builds a field in which the two roots
exist. -/
theorem exists_nsmul_two_eq_some_of_roots [DecidableEq F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {x₀ y₀ : F} (hQ : W.Nonsingular x₀ y₀) (hx₀ : W.Ψ₂Sq.eval x₀ = 0) {x y : F}
    (hx : (W.halvingX x₀).eval x = 0) (hy : (W.halvingY x).eval y = 0) :
    ∃ P : W.Point, 2 • P = Point.some x₀ y₀ hQ :=
  exists_nsmul_two_eq_some_of_root hQ (equation_of_eval_halvingY_eq_zero hy)
    (by simpa only [ΨSq_two] using eval_Φ_two_eq_of_root_halvingX h2 hx₀ hx)


-- @@ L363-363 verbatim
/-! ## Base change -/


-- @@ L365-370 verbatim
/-- Both quadratics are defined by the `a`- and `b`-invariants, so both commute with a field
homomorphism.  ⚠️ For `halvingX` this needs `map_div₀`: the constant coefficient divides by `2`. -/
theorem map_halvingX {K : Type*} [Field K] (f : F →+* K) (x₀ : F) :
    (W.map f).halvingX (f x₀) = (W.halvingX x₀).map f := by
  simp [halvingX, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, map_div₀, map_ofNat,
    Polynomial.map_neg, Polynomial.map_ofNat]


-- @@ L372-375 verbatim
theorem map_halvingY {K : Type*} [Field K] (f : F →+* K) (x : F) :
    (W.map f).halvingY (f x) = (W.halvingY x).map f := by
  simp [halvingY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, Polynomial.map_neg]


-- @@ L377-377 verbatim
/-! ## The first floor: adjoining the halving `x`-coordinate -/


-- @@ L379-381 verbatim
/-- **A splitting field of the halving quadratic.** -/
noncomputable abbrev halvingXField (W : Affine F) (x₀ : F) : Type _ :=
  (W.halvingX x₀).SplittingField


-- @@ L383-386 verbatim
/-- A root of the halving quadratic in its splitting field. -/
noncomputable def halvingXRoot (W : Affine F) (x₀ : F) : W.halvingXField x₀ :=
  rootOfSplits (IsSplittingField.splits (W.halvingXField x₀) (W.halvingX x₀))
    (by rw [Polynomial.degree_map, degree_halvingX]; exact two_ne_zero)


-- @@ L388-393 verbatim
theorem eval_halvingXRoot {W : Affine F} (x₀ : F) :
    ((W⁄(W.halvingXField x₀)).halvingX (algebraMap F (W.halvingXField x₀) x₀)).eval
      (W.halvingXRoot x₀) = 0 := by
  rw [show (W⁄(W.halvingXField x₀)) = W.map (algebraMap F (W.halvingXField x₀)) from rfl,
    map_halvingX]
  exact eval_rootOfSplits _ _


-- @@ L395-395 verbatim
section Tower


-- @@ L397-397 verbatim
variable {W : Affine F} {x₀ : F}


-- @@ L399-405 verbatim
/-- **The first floor is Galois**, being a splitting field of a separable polynomial.

⚠️ It does **not** take `[W.IsElliptic]`: the separability of `halvingX` is read off
`W.Ψ₂Sq.Separable`, which is a hypothesis here, and the discriminant is never computed from `Δ`. -/
theorem isGalois_halvingXField (h2 : (2 : F) ≠ 0) (hsep : W.Ψ₂Sq.Separable)
    (hx₀ : W.Ψ₂Sq.eval x₀ = 0) : IsGalois F (W.halvingXField x₀) :=
  IsGalois.of_separable_splitting_field (p := W.halvingX x₀) (separable_halvingX h2 hsep hx₀)


-- @@ L407-410 verbatim
/-- **The first floor is finite over `F`.**  ⚠️ `Polynomial.IsSplittingField.finiteDimensional`
takes no separability, which is why this carries neither `(2 : F) ≠ 0` nor `[W.IsElliptic]`. -/
theorem finiteDimensional_halvingXField : FiniteDimensional F (W.halvingXField x₀) :=
  IsSplittingField.finiteDimensional _ (W.halvingX x₀)


-- @@ L412-416 verbatim
/-- A numeral that is nonzero in `F` stays nonzero in a field extension.  ⚠️ Duplicated on purpose:
the copies in `EllipticCurves.FunctionField` are downstream of `Torsion/`. -/
private lemma algebraMap_two_ne_zero' {L : Type*} [Field L] [Algebra F L] (h2 : (2 : F) ≠ 0) :
    (2 : L) ≠ 0 := by
  rw [← map_ofNat (algebraMap F L) 2, ne_eq, map_eq_zero]; exact h2


-- @@ L418-423 verbatim
/-- A `2`-torsion `x`-coordinate stays one after base change. -/
theorem eval_Ψ₂Sq_baseChange {L : Type*} [Field L] [Algebra F L] (hx₀ : W.Ψ₂Sq.eval x₀ = 0) :
    (W⁄L).Ψ₂Sq.eval (algebraMap F L x₀) = 0 := by
  rw [show (W⁄L) = W.map (algebraMap F L) from rfl, WeierstrassCurve.map_Ψ₂Sq, eval_map,
    ← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply]
  simp [hx₀]


-- @@ L425-433 verbatim
/-- **The halving `x`-coordinate is not `2`-torsion**, which is what makes the second floor
separable. -/
theorem Ψ₂Sq_eval_halvingXRoot_ne_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (hx₀ : W.Ψ₂Sq.eval x₀ = 0) :
    (W⁄(W.halvingXField x₀)).Ψ₂Sq.eval (W.halvingXRoot x₀) ≠ 0 := by
  haveI : (W⁄(W.halvingXField x₀)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (W.halvingXField x₀))).IsElliptic
  exact Ψ₂Sq_eval_ne_zero_of_root_halvingX (algebraMap_two_ne_zero' h2)
    (eval_Ψ₂Sq_baseChange hx₀) (eval_halvingXRoot x₀)


-- @@ L435-435 verbatim
end Tower


-- @@ L437-437 verbatim
/-! ## The second floor: adjoining the halving `y`-coordinate -/


-- @@ L439-441 verbatim
/-- The `y`-quadratic above the chosen halving `x`-coordinate, over the first floor. -/
noncomputable def halvingYPoly (W : Affine F) (x₀ : F) : (W.halvingXField x₀)[X] :=
  (W⁄(W.halvingXField x₀)).halvingY (W.halvingXRoot x₀)


-- @@ L443-446 verbatim
/-- **The halving field** of the `2`-torsion point at `x₀`: the halving `x`-coordinate adjoined to
`F`, and then the halving `y`-coordinate adjoined to that. -/
noncomputable abbrev halvingField (W : Affine F) (x₀ : F) : Type _ :=
  (W.halvingYPoly x₀).SplittingField


-- @@ L448-451 verbatim
/-- A root of the `y`-quadratic in the halving field. -/
noncomputable def halvingYRoot (W : Affine F) (x₀ : F) : W.halvingField x₀ :=
  rootOfSplits (IsSplittingField.splits (W.halvingField x₀) (W.halvingYPoly x₀))
    (by rw [Polynomial.degree_map, halvingYPoly, degree_halvingY]; exact two_ne_zero)


-- @@ L453-456 verbatim
theorem eval_halvingYRoot (W : Affine F) (x₀ : F) :
    ((W.halvingYPoly x₀).map
      (algebraMap (W.halvingXField x₀) (W.halvingField x₀))).eval (W.halvingYRoot x₀) = 0 :=
  eval_rootOfSplits _ _


-- @@ L458-458 verbatim
section Separability


-- @@ L460-460 verbatim
variable {W : Affine F} {x₀ : F}


-- @@ L462-466 verbatim
/-- **The second floor is Galois over the first.** -/
theorem isGalois_halvingField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hx₀ : W.Ψ₂Sq.eval x₀ = 0) :
    IsGalois (W.halvingXField x₀) (W.halvingField x₀) :=
  IsGalois.of_separable_splitting_field (p := W.halvingYPoly x₀)
    (separable_halvingY (Ψ₂Sq_eval_halvingXRoot_ne_zero h2 hx₀))


-- @@ L468-475 verbatim
/-- **The halving field is separable over `F`** — the statement `#962`'s ledger row asks for, and
the one the quartic's repeated root appeared to forbid.  Separability is transitive even though
normality is not, so the two Galois floors give it directly. -/
theorem isSeparable_halvingField [W.IsElliptic] (h2 : (2 : F) ≠ 0) (hsep : W.Ψ₂Sq.Separable)
    (hx₀ : W.Ψ₂Sq.eval x₀ = 0) : Algebra.IsSeparable F (W.halvingField x₀) := by
  haveI := isGalois_halvingXField h2 hsep hx₀
  haveI := isGalois_halvingField (W := W) h2 hx₀
  exact Algebra.IsSeparable.trans F (W.halvingXField x₀) (W.halvingField x₀)


-- @@ L477-482 verbatim
/-- **The halving field is finite over `F`.** -/
theorem finiteDimensional_halvingField : FiniteDimensional F (W.halvingField x₀) := by
  haveI : FiniteDimensional F (W.halvingXField x₀) := finiteDimensional_halvingXField
  haveI : FiniteDimensional (W.halvingXField x₀) (W.halvingField x₀) :=
    IsSplittingField.finiteDimensional _ (W.halvingYPoly x₀)
  exact FiniteDimensional.trans F (W.halvingXField x₀) (W.halvingField x₀)


-- @@ L484-498 verbatim
/-- **The Galois closure of the halving field is Galois over `F`.**

`EllipticCurves.Galois.NormalClosureSeparable`'s `isGalois_normalClosure_of_isSeparable` at the
instance this file has just proved.  ⚠️ **Every line of the field-theoretic argument is there and
none of it is here**: that lemma is this proof with the curve deleted, and the deletion costs
nothing because the argument never reads `W`, `h2`, `hsep` or `hx₀` except through
`isSeparable_halvingField`.  ⚠️ **`finiteDimensional_halvingField` is not used either**, here or
there — `lake lint` convicted the finiteness hypothesis as unused when the leaf was written with
it, and `IsGalois` asks only for normal and separable. -/
theorem isGalois_normalClosure_halvingField [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (hsep : W.Ψ₂Sq.Separable) (hx₀ : W.Ψ₂Sq.eval x₀ = 0) :
    IsGalois F (IntermediateField.normalClosure F (W.halvingField x₀)
      (AlgebraicClosure (W.halvingField x₀))) := by
  haveI := isSeparable_halvingField h2 hsep hx₀
  exact _root_.isGalois_normalClosure_of_isSeparable F (W.halvingField x₀)


-- @@ L500-500 verbatim
end Separability


-- @@ L502-502 verbatim
/-! ## The halving, over the halving field -/


-- @@ L504-504 verbatim
section Halving


-- @@ L506-506 verbatim
variable {W : Affine F} {x₀ : F}


-- @@ L508-513 verbatim
/-- `((W⁄L₁)⁄L) = (W⁄L)` in a tower, which is `WeierstrassCurve.map_baseChange` at the
`IsScalarTower` map. -/
private lemma baseChange_baseChange (W : Affine F) (L₁ : Type*) [Field L₁] [Algebra F L₁]
    (L : Type*) [Field L] [Algebra F L] [Algebra L₁ L] [IsScalarTower F L₁ L] :
    ((W⁄L₁)⁄L) = (W⁄L) :=
  WeierstrassCurve.map_baseChange (R := F) W (IsScalarTower.toAlgHom F L₁ L)


-- @@ L515-515 verbatim
section Bridge


-- @@ L517-518 verbatim
variable {L₁ L : Type*} [Field L₁] [Field L] [Algebra F L₁] [Algebra F L] [Algebra L₁ L]
  [IsScalarTower F L₁ L]


-- @@ L520-528 verbatim
/-- A root of the halving quadratic over `L₁` is one over any extension of `L₁`. -/
theorem eval_halvingX_baseChange {r : L₁}
    (hr : ((W⁄L₁).halvingX (algebraMap F L₁ x₀)).eval r = 0) :
    ((W⁄L).halvingX (algebraMap F L x₀)).eval (algebraMap L₁ L r) = 0 := by
  rw [← baseChange_baseChange W L₁ L,
    show ((W⁄L₁)⁄L) = (W⁄L₁).map (algebraMap L₁ L) from rfl,
    IsScalarTower.algebraMap_apply F L₁ L x₀, map_halvingX, eval_map, ← Polynomial.aeval_def,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, ← eval_map, ← map_halvingX]
  simp [Algebra.algebraMap_self, hr]


-- @@ L530-536 verbatim
/-- A root of the `y`-quadratic over `L₁`, seen over `L`. -/
theorem eval_halvingY_baseChange {x : L₁} {y : L}
    (hy : (((W⁄L₁).halvingY x).map (algebraMap L₁ L)).eval y = 0) :
    ((W⁄L).halvingY (algebraMap L₁ L x)).eval y = 0 := by
  rw [← baseChange_baseChange W L₁ L,
    show ((W⁄L₁)⁄L) = (W⁄L₁).map (algebraMap L₁ L) from rfl, map_halvingY]
  exact hy


-- @@ L538-538 verbatim
end Bridge


-- @@ L540-554 verbatim
/-- **A `2`-torsion point is twice another point over its halving field.**

The conclusion `#962`'s halving row needs, together with `isSeparable_halvingField` and
`finiteDimensional_halvingField` for the descent that consumes it. -/
theorem exists_nsmul_two_eq_halvingField [DecidableEq (W.halvingField x₀)] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {y₀ : F} (hQ : W.Nonsingular x₀ y₀) (hx₀ : W.Ψ₂Sq.eval x₀ = 0) :
    ∃ P : (W⁄(W.halvingField x₀)).Point,
      2 • P = Point.some (algebraMap F (W.halvingField x₀) x₀)
        (algebraMap F (W.halvingField x₀) y₀)
        ((W.map_nonsingular (algebraMap F (W.halvingField x₀)).injective x₀ y₀).mpr hQ) := by
  haveI : (W⁄(W.halvingField x₀)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (W.halvingField x₀))).IsElliptic
  exact exists_nsmul_two_eq_some_of_roots (algebraMap_two_ne_zero' h2) _
    (eval_Ψ₂Sq_baseChange hx₀) (eval_halvingX_baseChange (eval_halvingXRoot x₀))
    (y := W.halvingYRoot x₀) (eval_halvingY_baseChange (eval_halvingYRoot W x₀))


-- @@ L556-556 verbatim
end Halving


-- @@ L558-558 verbatim
/-! ## Non-vacuity -/


-- @@ L560-560 verbatim
section Nonvacuity


-- @@ L562-562 verbatim
open EllipticCurves.Fixture


-- @@ L564-570 verbatim
/-! The certificate curve is `EllipticCurves.Fixture.y2EqX3SubX` at `R = ℚ`: `y² = x³ - x`, whose
`2`-torsion cubic is `4X³ - 4X` and whose `2`-torsion point `(0, 0)` has **no rational halving**.
⚠️ **What this block tests is that the tower this file produces is a proper extension of `ℚ`** —
`halvingX 0` is `X² + 1` and `halvingXRoot_y2EqX3SubX_not_mem_range` says its root is outside the
image of `ℚ`.  Substituting `EllipticCurves.Fixture.y2EqX3Add4X`, whose `halvingX 0` is `X² - 4`
and whose `(0, 0)` is `2 • (2, 4)` already over `ℚ`, would leave everything below green and certify
only the case in which the tower is `ℚ` itself. -/


-- @@ L572-573 verbatim
private lemma halvingX_y2EqX3SubX : (y2EqX3SubX ℚ).halvingX 0 = X ^ 2 + C 1 := by
  simp [halvingX, y2EqX3SubX, WeierstrassCurve.b₂, WeierstrassCurve.b₄]


-- @@ L575-577 verbatim
private lemma eval_Ψ₂Sq_y2EqX3SubX_zero : (y2EqX3SubX ℚ).Ψ₂Sq.eval 0 = 0 := by
  simp [WeierstrassCurve.Ψ₂Sq, y2EqX3SubX, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]


-- @@ L579-584 expanded
private lemma Ψ₂Sq_y2EqX3SubX : (y2EqX3SubX ℚ).Ψ₂Sq = C 4 * X ^ 3 - C 4 * X :=
  by
  simp only [WeierstrassCurve.Ψ₂Sq, y2EqX3SubX, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  norm_num
  ring


-- @@ L586-607 expanded
/-- **The `2`-torsion cubic of the certificate curve is separable**, from a Bézout certificate
written out rather than from a discriminant.  ⚠️ This is what makes the theorems above inhabited
**without** `#1985`'s branch: `separable_halvingX`'s `W.Ψ₂Sq.Separable` is discharged here by hand.
-/
private theorem separable_Ψ₂Sq_y2EqX3SubX : (y2EqX3SubX ℚ).Ψ₂Sq.Separable :=
  by
  have hderiv : derivative ((y2EqX3SubX ℚ).Ψ₂Sq) = C 12 * X ^ 2 - C 4 :=
    by
    rw [Ψ₂Sq_y2EqX3SubX]
    simp only [derivative_sub, derivative_mul, derivative_C, derivative_X, derivative_pow, zero_mul,
      zero_add, mul_one, Nat.cast_ofNat, Nat.add_one_sub_one]
    simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
    ring
  rw [Polynomial.Separable, hderiv, Ψ₂Sq_y2EqX3SubX]
  have key :
    (C (-9 : ℚ) * X) * (C 4 * X ^ 3 - C 4 * X) + (C 3 * X ^ 2 - C 2) * (C 12 * X ^ 2 - C 4) =
      C (8 : ℚ) :=
    by simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]; ring
  refine ⟨C (8 : ℚ)⁻¹ * (C (-9) * X), C (8 : ℚ)⁻¹ * (C 3 * X ^ 2 - C 2), ?_⟩
  calc
    C (8 : ℚ)⁻¹ * (C (-9) * X) * (C 4 * X ^ 3 - C 4 * X) +
          C (8 : ℚ)⁻¹ * (C 3 * X ^ 2 - C 2) * (C 12 * X ^ 2 - C 4) =
        C (8 : ℚ)⁻¹ *
          ((C (-9 : ℚ) * X) * (C 4 * X ^ 3 - C 4 * X) +
            (C 3 * X ^ 2 - C 2) * (C 12 * X ^ 2 - C 4)) :=
      by ring
    _ = C (8 : ℚ)⁻¹ * C (8 : ℚ) := by rw [key]
    _ = 1 := by rw [← C_mul]; norm_num


-- @@ L609-614 verbatim
/-- **The halving quadratic has no rational root** for `y² = x³ - x` at `(0, 0)`: it is `X² + 1`. -/
private theorem eval_halvingX_y2EqX3SubX_ne_zero (x : ℚ) :
    ((y2EqX3SubX ℚ).halvingX 0).eval x ≠ 0 := by
  rw [halvingX_y2EqX3SubX]
  simp only [eval_add, eval_pow, eval_X, eval_C]
  nlinarith [sq_nonneg x]


-- @@ L616-625 verbatim
/-- **The tower is a proper extension of `ℚ`**: the halving `x`-coordinate is not rational. -/
private theorem halvingXRoot_y2EqX3SubX_not_mem_range :
    (y2EqX3SubX ℚ).halvingXRoot 0 ∉
      Set.range (algebraMap ℚ ((y2EqX3SubX ℚ).halvingXField 0)) := by
  rintro ⟨q, hq⟩
  have h : (((y2EqX3SubX ℚ).halvingX 0).map
      (algebraMap ℚ ((y2EqX3SubX ℚ).halvingXField 0))).eval
      ((y2EqX3SubX ℚ).halvingXRoot 0) = 0 := eval_rootOfSplits _ _
  rw [← hq, eval_map, Polynomial.eval₂_hom] at h
  exact eval_halvingX_y2EqX3SubX_ne_zero q ((map_eq_zero _).mp h)


-- @@ L627-629 verbatim
private lemma nonsingular_zero_y2EqX3SubX : (y2EqX3SubX ℚ).Nonsingular 0 0 := by
  refine equation_iff_nonsingular.mp ?_
  simp [equation_iff', y2EqX3SubX]


-- @@ L631-631 verbatim
private noncomputable instance : DecidableEq ((y2EqX3SubX ℚ).halvingField 0) := Classical.decEq _


-- @@ L633-637 verbatim
/-- **The halving field of `(0, 0)` on `y² = x³ - x` is separable over `ℚ`**, with no hypothesis at
all. -/
private theorem isSeparable_halvingField_y2EqX3SubX :
    Algebra.IsSeparable ℚ ((y2EqX3SubX ℚ).halvingField 0) :=
  isSeparable_halvingField (by norm_num) separable_Ψ₂Sq_y2EqX3SubX eval_Ψ₂Sq_y2EqX3SubX_zero


-- @@ L639-649 verbatim
/-- **`(0, 0)` is `2`-divisible over the halving field**, with no hypothesis at all — where it is
not `2`-divisible over `ℚ`, `halvingXRoot_y2EqX3SubX_not_mem_range` being the obstruction. -/
private theorem exists_nsmul_two_eq_y2EqX3SubX :
    ∃ P : ((y2EqX3SubX ℚ)⁄((y2EqX3SubX ℚ).halvingField 0)).Point,
      2 • P = Point.some (algebraMap ℚ ((y2EqX3SubX ℚ).halvingField 0) 0)
        (algebraMap ℚ ((y2EqX3SubX ℚ).halvingField 0) 0)
        (((y2EqX3SubX ℚ).map_nonsingular
          (algebraMap ℚ ((y2EqX3SubX ℚ).halvingField 0)).injective 0 0).mpr
            nonsingular_zero_y2EqX3SubX) :=
  exists_nsmul_two_eq_halvingField (by norm_num) nonsingular_zero_y2EqX3SubX
    eval_Ψ₂Sq_y2EqX3SubX_zero


-- @@ L651-651 verbatim
end Nonvacuity


-- @@ L653-653 verbatim
end WeierstrassCurve.Affine
