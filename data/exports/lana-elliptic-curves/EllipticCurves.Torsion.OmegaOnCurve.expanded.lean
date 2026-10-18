/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaDivisionPolynomial
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree


-- @@ L9-197 verbatim
/-!
# The on-curve identity for the division-polynomial coordinates, at general `n`

Mathlib leaves the `y`-coordinate division polynomials `ωₙ` as a `TODO`, so there is no statement
on the current pin that the multiplication-by-`n` coordinates `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` lie on the curve
— the *on-curve identity* that the function-field pullback `[n]∗ : F(W) → F(W)` consumes.
`EllipticCurves.Torsion.OmegaTwo` and `EllipticCurves.Torsion.OmegaThree` state it at `n = 2` and
`n = 3`; both now import this file and read off their theorems from the engine below.

This file separates that work into the part that depends on `n` and the part that does not, in
exactly the shape `EllipticCurves.Torsion.NsmulSurjective` uses for the surjectivity engine.

## The one index-dependent input

Everything reduces to a **single univariate polynomial identity** in `R[X]`, packaged as the
predicate `WeierstrassCurve.HasPreΩSq`:

```
preΩₙ² · (if Even n then 1 else Ψ₂Sq) =
  4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³
```

with `preΩₙ = preΨₙ₊₂·preΨₙ₋₁² − preΨₙ₋₂·preΨₙ₊₁²` the univariate `y`-numerator of
`EllipticCurves.Torsion.OmegaDivisionPolynomial`.  It is the completed-square form of the
Weierstrass equation at the point `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)`, with all denominators cleared.

### Why the parity factor is `if Even n then 1 else Ψ₂Sq`, and why the coordinates are `ωₙ/ψₙ³`

The factor is a **theorem of the imported file**, not a fudge fitted to a degree count.
`EllipticCurves.Torsion.OmegaDivisionPolynomial` proves `Ω_factor`,
`Ψₙ₊₂·Ψₙ₋₁² − Ψₙ₋₂·Ψₙ₊₁² = (if Even n then ψ₂ else ψ₂²)·C(preΩₙ)`, and `ψ_mul_Ω`,
`ψ₂ₙ·ψ₂ = ψₙ·Ωₙ`.  At a point `(x, y)` of `W` at which `ψ₂` does not vanish those combine, after
cancelling the common `ψ₂`, into `WeierstrassCurve.Affine.ψ_two_mul_evalEval`:

```
(if Even n then 1 else ψ₂(x, y)) · preΩₙ(x) = ψ₂ₙ(x, y) / ψₙ(x, y).
```

That is what earns this file's repeated claim that its coordinates are `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)`: the
`y`-value of `WeierstrassCurve.Affine.equation_of_hasPreΩSqAt` below is `ωₙ/ψₙ³` for `ωₙ` in the
classical normalisation

```
2ωₙ = ψ₂ₙ/ψₙ − (a₁Φₙ + a₃ψₙ²)·ψₙ
```

of [Silverman, AEC][silverman2009], Exercise 3.7.  The factor in `HasPreΩSq` is the **square** of
the one in that numerator, which is why it reads `Ψ₂Sq` there and `2y + a₁x + a₃` in the `y`-value.

⚠️ **The degree count is kept, and it is an independent check rather than the evidence.**  It is
what predicted the shape before any of this was in Lean: `preΩₙ` has degree `3n²/2` for even `n` but
only `(3n² − 3)/2` for odd `n`, the missing `3` being the degree of `Ψ₂Sq`.

⚠️ **`preΨ₄_sq` is literally this identity at `n = 2`**, and the `n = 3` case is literally the
same algebra that `tripling_equation` used to run inline.  Both are univariate `CommRing` facts
about `preΨ`, so both live in `EllipticCurves.Torsion.OmegaDivisionPolynomial`; the `n = 3` one is
`hasPreΩSqAt_three` below, and it is proved here exactly once.

## Main definitions

* `WeierstrassCurve.HasPreΩSq`: the identity above, as a predicate on the index `n`.
* `WeierstrassCurve.HasPreΩSqAt`: the same identity evaluated at a single `x`.  This is what the
  engine actually consumes, and it is the weaker of the two — see the note on `n = 3` below.
* `WeierstrassCurve.HasΨSqDoubling`: **the same identity with `preΩ` eliminated**,
  `ΨSq₂ₙ = ΨSqₙ·(4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³)` — see the section below.

## Main statements

* `WeierstrassCurve.hasPreΩSq_zero`, `WeierstrassCurve.hasPreΩSq_one`,
  `WeierstrassCurve.hasPreΩSq_two`: the polynomial identity at `n = 0`, `1`, `2`, over an arbitrary
  commutative ring and in every characteristic.
* `WeierstrassCurve.HasPreΩSq.neg`: the identity is an even function of the index, so those three
  give `n ∈ {0, ±1, ±2}`.
* `WeierstrassCurve.HasPreΩSq.at`: the polynomial identity implies the evaluated one.  ⚠️ At a
  *single* `x` there is no way back, but from the evaluated identity at **every** point of an
  infinite integral domain there is: `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt` in
  `EllipticCurves.Torsion.OmegaCharZero`.
* `WeierstrassCurve.Affine.hasPreΩSqAt_three`: the evaluated identity at `n = 3`, over a field of
  characteristic `≠ 2`.
* `WeierstrassCurve.Affine.equation_of_hasPreΩSqAt`: **the uniform half, written once.**  Given the
  identity at `n` and at the point's own `x`, the division-polynomial coordinates at `n` satisfy the
  Weierstrass equation, over any field of characteristic `≠ 2`, at any point of `W` with
  `ψₙ(x, y) ≠ 0`.
* `WeierstrassCurve.Affine.equation_of_hasPreΩSq`: the same from the polynomial identity.
* `WeierstrassCurve.hasPreΩSq_iff_hasΨSqDoubling`: over an integral domain at an index that is
  nonzero in the base, the crux is **equivalent** to `HasΨSqDoubling`.  Its two halves,
  `HasPreΩSq.hasΨSqDoubling` (unconditional) and `hasPreΩSq_of_hasΨSqDoubling`, are stated
  separately.

## The crux written in Mathlib's vocabulary alone

`HasPreΩSq` is stated in terms of `preΩ`, which is this project's construction and appears nowhere
in Mathlib.  `ΨSq_two_mul` of `EllipticCurves.Torsion.OmegaDivisionPolynomial` —
`ΨSq₂ₙ = ΨSqₙ·(preΩₙ²·(if Even n then 1 else Ψ₂Sq))` — supplies the parity-corrected `preΩₙ²` as a
ratio of Mathlib's own polynomials, and multiplying the crux through by `ΨSqₙ` therefore removes
`preΩ` from it entirely:

```
ΨSq₂ₙ = ΨSqₙ · (4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³).
```

The bracket is `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` homogenised at `(Φₙ, ΨSqₙ)`, so this says that the
duplication map's denominator, evaluated at the multiplication-by-`n` coordinates, is the
multiplication-by-`2n` denominator — **the denominator half of "duplication composes with
multiplication by `n`"**, which is a classical statement about a classical object.

⚠️ **It is exactly as hard as `HasPreΩSq` and no easier.**  `hasPreΩSq_iff_hasΨSqDoubling` is an
equivalence; nothing is discharged by it.  What it buys is that the open question is now stated in
symbols Mathlib defines, so it can be searched for, asked upstream, and recognised — none of which
is possible for a statement about `preΩ`.

## ⚠️ What this does and does not settle

**Nothing is proved here at any index that was not already available.**  The instances are `n = 0`
and `n = 1` (both immediate), `n = 2` (the merged `preΨ₄_sq`) and `n = 3` (the algebra that the
merged `tripling_equation` used to run inline).  What the file settles is **how much is needed at a
new index, and that it is exactly one univariate identity** — no bivariate work, no hypothesis on
`(n : F)`, no algebraically closed base, and no group-law input.  `HasPreΩSq` at general `n` **was**
the crux left in issue `#404`; it is proved, at every index and over every commutative ring, by
`WeierstrassCurve.hasPreΩSq` of `EllipticCurves.Torsion.OmegaCrux`, whose only index-dependent
inputs are this file's `n = 1` and `n = 2` and `EllipticCurves.Torsion.OmegaCharZero`'s `n = 3`.
⚠️ **`n = 1` and `n = 2` below are two of the three base cases of that proof** — the third is the
*polynomial* `hasPreΩSq_three` of `EllipticCurves.Torsion.OmegaCharZero`, not the evaluated `n = 3`
instance here — **and `n = 0` is the `n = 0` branch of `hasPreΩSq` rather than a base case of the
induction.  So "nothing is proved here that was not already available" is unchanged, and none of
the four instances is decoration.**

⚠️ **`HasΨSqDoubling` proves nothing either.**  It is an equivalent phrasing of the same crux at the
same index, and the equivalence — not a one-way reduction — is the whole of what is claimed for it.
The reduction that does weaken the hypothesis is
`EllipticCurves.Torsion.OmegaCharZero`'s `hasPreΩSq_of_forall_hasΨSqDoubling_algClosed`, and even
that weakens the *hypothesis*, not the *statement*.

⚠️ **The `n = 3` instance here is the evaluated `hasPreΩSqAt_three`; the polynomial identity at
`n = 3` is `WeierstrassCurve.hasPreΩSq_three` and lives in
`EllipticCurves.Torsion.OmegaCharZero`.**  It is derived from the evaluated one and adds no algebra;
the next section is why it had to be derived rather than proved here.

⚠️ **What proving `n = 3` in the polynomial form directly would have cost, and why that is a
measurement rather than a preference.**  The polynomial identity at `n = 3` is true over `ℤ` — it
needs no characteristic
hypothesis — but `4b₈ = b₂b₆ − b₄²` is not available as a substitution over an arbitrary ring, so
`ring1` must be run with the `aᵢ` as atoms.  Expanded that way each side of the `n = 3` identity has
**9903 monomials in six atoms**, and the two ways of putting that to `ring1` were both measured
here:

* in `R[X]` it **does** close — `3 m 38 s` for the module elaborated in isolation — but the same
  declaration was **killed by `lake build` with exit `137`, out of memory**, and a proof that only
  survives outside the build is not a proof this file can carry;
* restated as a plain `CommRing` auxiliary lemma, to drop the polynomial-ring overhead, `ring1` was
  still climbing through **10.5 GB resident** after 90 s and was killed by hand.

With `b₂, b₄, b₆` kept as atoms and `b₈` eliminated by division by `4` the same identity has
**545 monomials** and closes in seconds — which is exactly what `hasPreΩSqAt_three` does, and
exactly why it needs a field of characteristic `≠ 2`.  The remaining characteristic-free route, a
`linear_combination` against `b_relation`, needs a cofactor that was computed here by exact
division and has **275 monomials**: a hundred-line constant with no independent meaning.  None of
the three was worth taking; the engine assumes characteristic `≠ 2` regardless, so the evaluated
form loses nothing at the point of use.

⚠️ **All three of those routes attack the identity directly over the general ring, and that is why
the enumeration read as exhaustive when it was not.**  There is a fourth, and it is the one that
won: do not attack it over the general ring at all.  Prove the **evaluated** identity over a
characteristic-`0` field, where `4` is a unit and the 545-monomial form above is legal, and then
descend — `Polynomial.funext` over an infinite domain turns "at every point" into the polynomial
identity, and `EllipticCurves.Torsion.OmegaUniversal`'s base change carries that down to every
commutative ring.  That is `WeierstrassCurve.hasPreΩSq_three`, and its entire proof is
`hasPreΩSqAt_three` fed through `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt_charZero`:
**zero new algebra, and the 9903-monomial expansion is never run.**  The measurements above stand
unchanged — they are what routes 1–3 cost — and the conclusion that none of the three is worth
taking stands too; what moved is that none of them has to be taken.  ⚠️ Expect the same blind spot
at `n = 4`: the question to ask first is not "how do I make `ring1` survive over `R`" but "what does
this identity cost where `2`, `3` and `4` are units".

⚠️ **This is an on-curve identity for the classical division-polynomial coordinates, not a statement
about `n • P`.**  Identifying `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with the group-law multiple is a genuinely
separate step — it is what `EllipticCurves.Torsion.DoublingCoords` and
`EllipticCurves.Torsion.TriplingCoords` do at `n = 2` and `n = 3`.  ⚠️ In general it is issue
`#251` on the `x`-half and `#1500` on the `y`-half, and **both are now closed** —
`hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) and
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), each at
every index over a field with `(2 : F) ≠ 0` and under `ΨSqₙ(x) ≠ 0`.  Both are downstream of this
file; the separateness claimed above is unaffected, only its openness.  The two
`OmegaTwo`/`OmegaThree` docstrings make the same disclaimer and it is unchanged.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/


-- @@ L199-199 verbatim
open Polynomial

-- @@ L200-200 verbatim
open scoped Polynomial.Bivariate


-- @@ L202-203 verbatim
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])


-- @@ L205-205 verbatim
namespace WeierstrassCurve


-- @@ L207-207 verbatim
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


-- @@ L209-230 verbatim
/-- **The `y`-coordinate on-curve identity at index `n`**, as a predicate on `n`:

```
preΩₙ² · (if Even n then 1 else Ψ₂Sq) =
  4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³
```

This is the completed-square form `(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆` of the Weierstrass
equation, evaluated at the division-polynomial coordinates `X = Φₙ/ΨSqₙ` and `Y = ωₙ/ψₙ³` and
cleared of denominators.  The parity factor `if Even n then 1 else Ψ₂Sq` is the square of the one
in the `y`-numerator, which `WeierstrassCurve.Affine.ψ_two_mul_evalEval` identifies with `ψ₂ₙ/ψₙ`;
see the module docstring, where the degree count on `preΩₙ` is retained as an independent check.

It is the one index-dependent input of `WeierstrassCurve.Affine.equation_of_hasPreΩSq` below, and
establishing it at general `n` was the crux left in issue `#404`.  ⚠️ It is now a theorem —
`WeierstrassCurve.hasPreΩSq` of `EllipticCurves.Torsion.OmegaCrux` — so
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` there is `equation_of_hasPreΩSq` with this
hypothesis discharged. -/
def HasPreΩSq (n : ℤ) : Prop :=
  W.preΩ n ^ 2 * (if Even n then 1 else W.Ψ₂Sq) =
    4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n + 2 * C W.b₄ * W.Φ n * W.ΨSq n ^ 2 +
      C W.b₆ * W.ΨSq n ^ 3


-- @@ L232-241 verbatim
/-- **The `y`-coordinate on-curve identity at index `n`, evaluated at a single `x`.**  This is what
the engine consumes: the on-curve verification happens at one point, so the polynomial identity is
more than it needs.  ⚠️ At a single `x` it is also strictly weaker, and the difference is not
academic — at `n = 3` the evaluated form is the only one this file can afford to prove, for the
reasons the module docstring measures.  Quantified over **every** point of an infinite integral
domain it is not weaker at all: see `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt`. -/
def HasPreΩSqAt (n : ℤ) (x : R) : Prop :=
  (W.preΩ n).eval x ^ 2 * (if Even n then 1 else W.Ψ₂Sq.eval x) =
    4 * (W.Φ n).eval x ^ 3 + W.b₂ * (W.Φ n).eval x ^ 2 * (W.ΨSq n).eval x +
      2 * W.b₄ * (W.Φ n).eval x * (W.ΨSq n).eval x ^ 2 + W.b₆ * (W.ΨSq n).eval x ^ 3


-- @@ L243-248 verbatim
/-- **The polynomial identity gives the evaluated one at every `x`.** -/
lemma HasPreΩSq.at {W : WeierstrassCurve R} {n : ℤ} (h : W.HasPreΩSq n) (x : R) :
    W.HasPreΩSqAt n x := by
  have H := congrArg (Polynomial.eval x) h
  simpa only [HasPreΩSqAt, eval_mul, eval_pow, eval_add, eval_ofNat, eval_C,
    apply_ite (Polynomial.eval x), eval_one] using H


-- @@ L250-254 verbatim
/-- **The identity is an even function of the index.**  `preΩ`, `Φ` and `ΨSq` are all even in `n`,
so the three instances below cover `n ∈ {0, ±1, ±2}`. -/
lemma HasPreΩSq.neg {W : WeierstrassCurve R} {n : ℤ} (h : W.HasPreΩSq n) : W.HasPreΩSq (-n) := by
  simp only [HasPreΩSq, preΩ_neg, Φ_neg, ΨSq_neg, even_neg]
  exact h


-- @@ L256-259 verbatim
/-- **The identity at `n = 0`.**  `preΩ₀ = 2`, `Φ₀ = 1` and `ΨSq₀ = 0`, so both sides are `4`. -/
lemma hasPreΩSq_zero : W.HasPreΩSq 0 := by
  rw [HasPreΩSq, preΩ]
  norm_num


-- @@ L261-269 expanded
/-- **The identity at `n = 1`.**  `preΩ₁ = 1`, `Φ₁ = X` and `ΨSq₁ = 1`, so it is the definition of
`Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`. -/
lemma hasPreΩSq_one : W.HasPreΩSq 1 :=
  by
  rw [HasPreΩSq, preΩ, if_neg (by decide : ¬Even (1 : ℤ)), Φ_one, ΨSq_one, Ψ₂Sq]
  simp only [show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num,
    show (1 : ℤ) - 2 = -1 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, preΨ_three, preΨ_zero,
    preΨ_two, preΨ_neg, preΨ_one]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  ring1


-- @@ L271-276 verbatim
/-- **The identity at `n = 2`.**  Since `preΩ₂ = preΨ₄` and `ΨSq₂ = Ψ₂Sq`, this is exactly the
merged `WeierstrassCurve.preΨ₄_sq` of `EllipticCurves.Torsion.OmegaDivisionPolynomial`, which is
where the duplication formula's heavy algebra already lives. -/
lemma hasPreΩSq_two : W.HasPreΩSq 2 := by
  rw [HasPreΩSq, preΩ_two, if_pos even_two, ΨSq_two, mul_one]
  exact W.preΨ₄_sq


-- @@ L278-278 verbatim
/-! ### The crux with `preΩ` eliminated -/


-- @@ L280-304 verbatim
/-- **The crux restated with no `preΩ` in it**: the `2n`-division denominator is the `n`-division
denominator times the duplication denominator at the `n`-division coordinates,

```
ΨSq₂ₙ = ΨSqₙ · (4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³)   in R[X].
```

The bracket is the homogenisation of `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` at `(Φₙ, ΨSqₙ)`, so the
identity says exactly that `x ↦ Φ₂(x)/Ψ₂Sq(x)` composed with `x ↦ Φₙ(x)/ΨSqₙ(x)` has the same
denominator as `x ↦ Φ₂ₙ(x)/ΨSq₂ₙ(x)` — **the denominator half of "duplication composes with
multiplication by `n`"**.

⚠️ **Every symbol here is Mathlib's.**  `Φ`, `ΨSq` and `Ψ₂Sq` are
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`'s; `preΩ`, `Ω` and `ω` do
not appear.  That is the point of the reformulation: `WeierstrassCurve.HasPreΩSq` states the same
mathematics in a vocabulary this project invented, and a statement in a private vocabulary cannot be
searched for upstream, asked about, or recognised as classical.  This one can.

⚠️ **It is a restatement, not a simplification.**  `hasPreΩSq_iff_hasΨSqDoubling` below is an
equivalence, so this is exactly as hard as `HasPreΩSq` and no easier; nothing about `#404`'s crux is
discharged by naming it.  What changes is what a prover is looking at. -/
def HasΨSqDoubling (n : ℤ) : Prop :=
  W.ΨSq (2 * n) =
    W.ΨSq n * (4 * W.Φ n ^ 3 + C W.b₂ * W.Φ n ^ 2 * W.ΨSq n +
      2 * C W.b₄ * W.Φ n * W.ΨSq n ^ 2 + C W.b₆ * W.ΨSq n ^ 3)


-- @@ L306-310 verbatim
/-- **`HasPreΩSq n` gives `HasΨSqDoubling n`, over an arbitrary `CommRing`.**  Multiply the crux by
`ΨSqₙ` and read the left-hand side off `ΨSq_two_mul`; the parity factor of `HasPreΩSq` is the one
`ΨSq_two_mul` supplies, which is why nothing is left over. -/
theorem HasPreΩSq.hasΨSqDoubling {n : ℤ} (h : W.HasPreΩSq n) : W.HasΨSqDoubling n := by
  rw [HasΨSqDoubling, ΨSq_two_mul, ← h]


-- @@ L312-324 verbatim
/-- **The converse, over an integral domain at an index that is not zero in the base.**  The
`ΨSqₙ` that `HasPreΩSq.hasΨSqDoubling` multiplied in is cancelled again; Mathlib's
`WeierstrassCurve.ΨSq_ne_zero` supplies `ΨSqₙ ≠ 0` from `(n : R) ≠ 0`.

⚠️ `hn` is doing real work and is not a proof artefact that a better argument would remove.  At
`n = 0` the statement `HasΨSqDoubling 0` reads `0 = 0 * _` and carries no information whatever,
while `HasPreΩSq 0` reads `4 = 4` and is `hasPreΩSq_zero`; so the two are **not** equivalent at
`n = 0`, and no proof of this direction can cover it.  What is lost is only that index: the
conclusion there is already available unconditionally. -/
theorem hasPreΩSq_of_hasΨSqDoubling [IsDomain R] {n : ℤ} (hn : (n : R) ≠ 0)
    (h : W.HasΨSqDoubling n) : W.HasPreΩSq n := by
  rw [HasΨSqDoubling, ΨSq_two_mul] at h
  exact mul_left_cancel₀ (W.ΨSq_ne_zero hn) h


-- @@ L326-335 verbatim
/-- **The two forms of the crux are equivalent.**  Proving `HasΨSqDoubling n` for every curve over
every commutative ring is the same job as proving `HasPreΩSq n`, and it is stated entirely in
Mathlib's division-polynomial vocabulary.

⚠️ Both are now theorems (`WeierstrassCurve.hasΨSqDoubling` and `WeierstrassCurve.hasPreΩSq`,
`EllipticCurves.Torsion.OmegaCrux`), and this equivalence is the crossing the closing proof makes:
the induction runs on `HasΨSqDoubling`, the base cases are stated as `HasPreΩSq`. -/
theorem hasPreΩSq_iff_hasΨSqDoubling [IsDomain R] {n : ℤ} (hn : (n : R) ≠ 0) :
    W.HasPreΩSq n ↔ W.HasΨSqDoubling n :=
  ⟨fun h => h.hasΨSqDoubling W, hasPreΩSq_of_hasΨSqDoubling W hn⟩


-- @@ L337-337 verbatim
namespace Affine


-- @@ L339-339 verbatim
variable {F : Type*} [Field F] {W : Affine F} {x y : F}


-- @@ L341-358 verbatim
/-- **The evaluated identity at `n = 3`**, over a field of characteristic `≠ 2`.

Since `preΩ₃ = preΨ₅ − preΨ₄²` and `ΨSq₃ = Ψ₃²`, this is the univariate step that
`WeierstrassCurve.Affine.tripling_equation` (`EllipticCurves.Torsion.OmegaThree`) used to run
inline, stated at a general `x` and proved here once.  ⚠️ The characteristic hypothesis is an
artefact of the proof, not of the
statement: `4b₈ = b₂b₆ − b₄²` is eliminated by dividing by `4`, which keeps `b₂`, `b₄`, `b₆` as
`ring` atoms and the normal form small.  The module docstring records what the characteristic-free
route costs. -/
lemma hasPreΩSqAt_three (h2 : (2 : F) ≠ 0) (x : F) : W.HasPreΩSqAt 3 x := by
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hb8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by
    rw [eq_div_iff h4]; linear_combination W.b_relation
  rw [HasPreΩSqAt, if_neg (by decide : ¬Even (3 : ℤ)), preΩ_three, preΨ_five, ΨSq_three, Φ_three]
  simp only [Ψ₃, preΨ₄, Ψ₂Sq, eval_mul, eval_add, eval_sub, eval_pow, eval_ofNat, eval_C, eval_X]
  rw [hb8]
  field_simp
  ring


-- @@ L360-428 verbatim
set_option maxHeartbeats 1000000 in
-- The proof clears the `ψₙ`-denominators of a division at a general index and normalises the
-- resulting rational identity twice (`hlin` and `hmain`), which needs a raised heartbeat limit.
/-- **The division-polynomial coordinates at `n` lie on the curve**, given the one univariate
identity `W.HasPreΩSqAt n x` at the point's own `x`.

For a point `(x, y)` on `W` over a field of characteristic `≠ 2` with `ψₙ(x, y) ≠ 0`, the point
`(Φₙ(x)/ΨSqₙ(x), ωₙ(x, y)/ψₙ(x, y)³)` satisfies the Weierstrass equation, where the `n`-division
`y`-coordinate value is

```
ωₙ(x, y) = ((if Even n then 1 else 2y + a₁x + a₃)·preΩₙ(x) − ψₙ(x, y)·(a₁Φₙ(x) + a₃ΨSqₙ(x)))/2.
```

This is the uniform half of the on-curve identity, written once.  ⚠️ The `if Even n` in the
numerator is the same parity factor as in `HasPreΩSq`, and it is not cosmetic: for odd `n` the
"`ψ₂`-value" `2Y + a₁X + a₃` of the multiple carries a factor of `2y + a₁x + a₃`, whose square is
`Ψ₂Sq(x)`, and for even `n` it does not.  `doubling_equation` and `tripling_equation` are the
`n = 2` and `n = 3` cases, and are derived from this theorem in `EllipticCurves.Torsion.OmegaTwo`
and `EllipticCurves.Torsion.OmegaThree`; their statements stay where they are, since they are
merged public API with consumers in `FunctionField/`. -/
theorem equation_of_hasPreΩSqAt {n : ℤ} (hΩ : W.HasPreΩSqAt n x) (h : W.Equation x y)
    (h2 : (2 : F) ≠ 0) (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.Equation ((W.Φ n).eval x / (W.ΨSq n).eval x)
      (((if Even n then 1 else 2 * y + W.a₁ * x + W.a₃) * (W.preΩ n).eval x -
          (W.ψ n).evalEval x y * (W.a₁ * (W.Φ n).eval x + W.a₃ * (W.ΨSq n).eval x)) /
        (2 * (W.ψ n).evalEval x y ^ 3)) := by
  rw [HasPreΩSqAt] at hΩ
  rw [equation_iff]
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have ht : (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
    have H := ψ_sq_evalEval h 2
    rwa [ψ_two_evalEval, ΨSq_two] at H
  -- The parity factor, packaged so that the rest of the argument runs once rather than twice:
  -- `e` is the numerator's factor and `e²` is the one in `HasPreΩSqAt`.
  obtain ⟨e, hev, hesq⟩ :
      ∃ e : F, (if Even n then (1 : F) else 2 * y + W.a₁ * x + W.a₃) = e ∧
        e ^ 2 = if Even n then 1 else W.Ψ₂Sq.eval x := by
    rcases Int.even_or_odd n with hn | hn
    · exact ⟨1, if_pos hn, by rw [if_pos hn]; ring⟩
    · have hne : ¬Even n := Int.not_even_iff_odd.mpr hn
      exact ⟨_, if_neg hne, by rw [if_neg hne]; exact ht⟩
  rw [hev]
  rw [← hesq] at hΩ
  set s := (W.ψ n).evalEval x y with hs_def
  set Φv := (W.Φ n).eval x with hΦ_def
  set Ψv := (W.ΨSq n).eval x with hΨ_def
  set Ov := (W.preΩ n).eval x with hO_def
  have hs : s ^ 2 = Ψv := ψ_sq_evalEval h n
  have hΨne : Ψv ≠ 0 := by rw [← hs]; exact pow_ne_zero 2 hψ
  set X' := Φv / Ψv with hX'
  set Y' := (e * Ov - s * (W.a₁ * Φv + W.a₃ * Ψv)) / (2 * s ^ 3) with hY'
  -- The `ψ₂`-value of the multiple: the `a₁` and `a₃` corrections in `ωₙ` cancel exactly.
  have hlin : 2 * Y' + W.a₁ * X' + W.a₃ = e * Ov / s ^ 3 := by
    rw [hY', hX', ← hs]
    field_simp
    ring
  -- The on-curve `b`-relation for the multiple.
  have hmain : (2 * Y' + W.a₁ * X' + W.a₃) ^ 2 =
      4 * X' ^ 3 + W.b₂ * X' ^ 2 + 2 * W.b₄ * X' + W.b₆ := by
    have hd : Ov ^ 2 * e ^ 2 = 4 * Φv ^ 3 + W.b₂ * Φv ^ 2 * s ^ 2 +
        2 * W.b₄ * Φv * (s ^ 2) ^ 2 + W.b₆ * (s ^ 2) ^ 3 := by rw [hs]; exact hΩ
    rw [hlin, div_pow, mul_pow, hX', ← hs]
    field_simp
    linear_combination hd
  -- Deduce the Weierstrass equation from the `b`-relation (characteristic `≠ 2`).
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hmain
  refine mul_left_cancel₀ h4 ?_
  linear_combination hmain


-- @@ L430-439 verbatim
/-- **The division-polynomial coordinates at `n` lie on the curve**, given the polynomial identity
`W.HasPreΩSq n`.  The `HasPreΩSqAt` form above is what the proof uses; this is the shape a
general-`n` theorem would be stated in. -/
theorem equation_of_hasPreΩSq {n : ℤ} (hΩ : W.HasPreΩSq n) (h : W.Equation x y) (h2 : (2 : F) ≠ 0)
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.Equation ((W.Φ n).eval x / (W.ΨSq n).eval x)
      (((if Even n then 1 else 2 * y + W.a₁ * x + W.a₃) * (W.preΩ n).eval x -
          (W.ψ n).evalEval x y * (W.a₁ * (W.Φ n).eval x + W.a₃ * (W.ΨSq n).eval x)) /
        (2 * (W.ψ n).evalEval x y ^ 3)) :=
  equation_of_hasPreΩSqAt (HasPreΩSq.at hΩ x) h h2 hψ


-- @@ L441-441 verbatim
end Affine


-- @@ L443-443 verbatim
end WeierstrassCurve
