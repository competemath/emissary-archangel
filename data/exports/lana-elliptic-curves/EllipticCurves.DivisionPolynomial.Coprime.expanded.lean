/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic


-- @@ L8-300 verbatim
/-!
# Coprimality of division polynomials: `(Φ₂, Ψ₂Sq)`, `(Ψ₃, Ψ₂Sq)`, `(Φ₃, ΨSq₃)`, general `n`

For a Weierstrass curve `W` over a commutative ring, the division polynomials

```
Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆,     Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈,
Φ₂   = X⁴ − b₄X² − 2b₆X − b₈ = X·Ψ₂Sq − Ψ₃
```

satisfy an explicit Bézout identity with right-hand side `Δ²`:

```lean
bezout_Φ_two_Ψ₂Sq : W.bezoutΦTwo * W.Φ 2 + W.bezoutΨ₂Sq * W.Ψ₂Sq = C (W.Δ ^ 2)
```

Hence when `Δ` is a unit — in particular for `[W.IsElliptic]` — the pairs `(Φ₂, Ψ₂Sq)` and
`(Ψ₃, Ψ₂Sq)` are **coprime**.

Geometrically the second statement says that no point of `W` is both `2`-torsion and `3`-torsion,
which is exactly what fails on a singular curve; and indeed the identity is *false* without `Δ`, so
the discriminant is genuinely load-bearing rather than decorative.

The pair `(Φ₃, ΨSq₃)` is here too, and it is **not** obtained the same way — see the section on the
`n = 3` certificate below.

## Why an explicit certificate rather than a root argument

The classical proof is "a common root would be a point that is both `2`- and `3`-torsion, hence
`O`, which is not affine". That argument needs the torsion characterisation
`n • P = O ↔ Ψₙ(x P) = 0`, which is a substantial separate development. The Bézout certificate
needs none of it, works over an arbitrary commutative ring, and is checked by `ring1`.

Mathlib has no coprimality statement anywhere under
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` (checked against `v4.32.0`), so
everything here is new; it is an upstream candidate, since nothing
below mentions function fields, places or divisors.  ⚠️ That is now truest of the general-`n`
reduction, which uses only Mathlib's own `Φ` and `ΨSq` and holds over an arbitrary commutative
ring: it is the piece of this file with no hypothesis to negotiate.

## Where the certificate comes from, and the one subtlety

`bezoutΦTwo` and `bezoutΨ₂Sq` are the cofactors produced by the adjugate of the Sylvester matrix of
the pair, so the identity they satisfy in the **free** polynomial ring `ℤ[b₂, b₄, b₆, b₈][X]` has
right-hand side the resultant

```
Res(Ψ₂Sq, Φ₂) = b₂⁴b₈² − 6b₂³b₄b₆b₈ + … − 256b₈³
```

which is **not** `Δ²` there — `b₂, b₄, b₆, b₈` are not independent. The two differ by an explicit
multiple of `4b₈ − b₂b₆ + b₄²`, which vanishes by Mathlib's `WeierstrassCurve.b_relation`. That is
why the proof below is a `linear_combination` against `b_relation` rather than a bare `ring1`: the
identity is true for Weierstrass curves and false for free `b`-parameters.

Because the relation is used in the form `4b₈ = b₂b₆ − b₄²` and never divided by, **nothing here
needs `2` or `3` to be invertible**; the results hold in every characteristic.

## The `n = 3` certificate is a congruence, not a resultant

A Bézout identity for `(Φ₃, ΨSq₃)` itself is not viable: `deg Φ₃ = 9` and `deg ΨSq₃ = 8`, so the
Sylvester matrix is `17 × 17` and its adjugate cofactors are polynomials no `ring1` call would
survive. What replaces it, in `preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul`, is the congruence

```
preΨ₄² ≡ Ψ₂Sq⁴   (mod Ψ₃),
```

which is `ψ₂(2P) = ψ₄(P)/ψ₂(P)⁴` read univariately and then reduced by `Φ₂ = X·Ψ₂Sq − Ψ₃`; its
cofactor is a five-term expression in `X`, `Ψ₂Sq` and `Ψ₃`. From it, `isCoprime_Ψ₃_Ψ₂Sq` alone
gives `IsCoprime preΨ₄ Ψ₃`, and `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq` with `ΨSq₃ = Ψ₃²` finishes.

So the discriminant still does all the work at `n = 3`, but only through the `n = 2` certificate:
**no new Bézout identity is computed**, and the two `Δ²`-certificates above remain the only ones in
this file.

## ⚠️ At general `n`, `Φ` is not the difficulty — and this file now says so with a theorem

Mathlib *defines* `Φₙ = X · ΨSqₙ − preΨₙ₊₁ · preΨₙ₋₁ · Eₙ`, where `Eₙ` is `1` for even `n` and
`Ψ₂Sq` for odd `n`.  Two consequences, both unconditional in `n` and in the ring:

* modulo `ΨSqₙ`, `Φₙ` **is** the adjacent product `−preΨₙ₊₁ · preΨₙ₋₁ · Eₙ`
  (`Φ_eq_neg_adjacent_add`);
* the square of that product is `ΨSqₙ₊₁ · ΨSqₙ₋₁` (`ΨSq_succ_mul_ΨSq_pred`) — because `n + 1` and
  `n - 1` have the same parity, so the two `if`s in `ΨSq` contribute `Eₙ²` between them.

Together they give `isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent`:

```lean
IsCoprime (W.ΨSq (n + 1) * W.ΨSq (n - 1)) (W.ΨSq n) → IsCoprime (W.Φ n) (W.ΨSq n)
```

with **no `[W.IsElliptic]`, no hypothesis on `n`, and no characteristic assumption**.  So the
general-`n` problem is not about `Φ` at all: it is the classical statement that `ψₘ` and `ψₙ` have
no common root when `gcd(m, n) = 1`, specialised to `m = n ± 1`.

⚠️ **This proves no new coprimality.**  It transports one, and it is recorded here because the
board had the general case filed as *"a much larger induction"* with no route written down; the
route is now written down and the remaining obligation is a statement about `ΨSq` alone.  The two
`example`s at the end of the file discharge that obligation at `n = 2` and `n = 3` and so recover
both merged results through the general lemma — `n = 3` included, whose hand proof is precisely
this argument done once by hand.

## ⚠️ The pointwise weakening is not a cheaper target, and that is a negative result

`EllipticCurves.Torsion.NsmulSurjective` reduces surjectivity of `[n]` on `E(F̄)` to two inputs, of
which the second is **not** the coprimality above but the strictly weaker pointwise statement

```lean
∀ x, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0
```

and that file records that this tree obtains the weakening at `n = 2` and `n = 3` with no Bézout
certificate at all, where the `IsCoprime` instances here cost a `Δ²` certificate and a congruence
argument reusing it.  On that evidence `#1184`'s planning note asks whether the weakening is the
cheaper **general** target and should be spiked first.

The answer is **no**, and `eval_Φ_ne_zero_iff_of_eval_ΨSq_eq_zero` is the reason: at a root of
`ΨSqₙ` the identity `Φ_eq_neg_adjacent_add` leaves `Φₙ(x) = −preΨₙ₊₁(x)·preΨₙ₋₁(x)·Eₙ(x)`, whose
square is `ΨSqₙ₊₁(x)·ΨSqₙ₋₁(x)` by `ΨSq_succ_mul_ΨSq_pred`.  Over a ring with no zero divisors that
makes the pointwise statement for `(Φₙ, ΨSqₙ)` **equivalent** to the pointwise statement for the
adjacent pair, where the `IsCoprime` reduction is an implication in one direction only.

⚠️ **So the weakening buys exactly the Bézout certificate and nothing else.**  It does not touch the
`ΨSq`-neighbour difficulty, which is the whole of what survives either reduction.  A worker
choosing between the two general targets is choosing between `IsCoprime (ΨSqₙ₊₁ · ΨSqₙ₋₁) (ΨSqₙ)`
and *"`ΨSqₙ₊₁ · ΨSqₙ₋₁` and `ΨSqₙ` have no common root"*, and both floors recorded in
*"What is not here"* below apply to the second exactly as they apply to the first.

⚠️ **What this does not say.**  It does not say the two general targets are equivalent — they are
not, and `#1184`'s remains the stronger.  It says that the `Φ`-to-`ΨSq` *reduction step*, which is
where the observed `n = 2`/`n = 3` saving lives, is available in both registers at the same price.
Whether a future proof of the surviving `ΨSq` obligation is easier pointwise than in Bézout form is
untouched by anything here.

⚠️ **One thing the pointwise register does buy, and it is a hypothesis count rather than a route.**
The two `example`s at the end of the file land the `hroot` instances
`eval_Φ_two_ne_zero_of_root_ΨSq` and `eval_Φ_three_ne_zero_of_root_ΨSq` with `[IsAlgClosed F]` and
`(2 : F) ≠ 0` **both dropped**, because they go through `isCoprime_Ψ₃_Ψ₂Sq` in this file rather
than through a statement about the points above an `x`.

⚠️ **That sentence used to end *"it is measured in that section and acted on nowhere"*, and it has
since been acted on.**  Both downstream statements were narrowed to exactly the hypotheses measured
here, in `EllipticCurves.Torsion.DoublingSurjective` and
`EllipticCurves.Torsion.TriplingSurjective`, which import this file directly and transitively.
Nothing in this file moved: the two `example`s stay `example`s, and what they measure is now what
the two downstream theorems say.

## The de-duplication question, decided (`#1255`)

`Polynomial.eval_ne_zero_of_isCoprime` at the top of this file used to be `private`, and its
docstring used to end:

> ⚠️ `private` because it is not this file's subject and because it already exists twice — once in
> Mathlib in the `aeval` shape it is derived from here, and once hand-proved as
> `eval_Φ_ne_zero_of_isCoprime` (`EllipticCurves.Torsion.NsmulSurjective`), which specialises it to
> `(Φₙ, ΨSqₙ)` and reproves it from the Bézout witness.  That duplication is a `#699`-class
> question about a file outside this one's import closure, so it is recorded here and not acted on.

⚠️ **That sentence is RETIRED: it has been acted on, and what it recorded was an undercount.**
The census at `68fd254` — read from source, not inferred from names — found **five** sites, not
three, because PR #465 had since inlined the same step twice more:

1. `Polynomial.aeval_ne_zero_of_isCoprime`, Mathlib — the mathematics; `aeval`, a disjunction.
2. the helper above, in this file — the general `eval` adapter, two lines, and it was `private`.
3. `eval_Φ_ne_zero_of_isCoprime` (`EllipticCurves.Torsion.NsmulSurjective`) — specialised to
   `(Φₙ, ΨSqₙ)`, and a **six-line reproof** that unfolded the Bézout witness by hand.
4. `eval_Φ_three_ne_zero_of_root_ΨSq` (`EllipticCurves.Torsion.TriplingSurjective`) — a local
   `have key`, the general adapter restated *inside a proof*.
5. `eval_Φ_two_ne_zero_of_root_ΨSq` (`EllipticCurves.Torsion.DoublingSurjective`) — the same step
   inlined at its single use.

**Sites 4 and 5 are gone**, and they cost nothing to remove: both files already import this one, so
de-privatising the helper — the option the `#699`-class framing did not enumerate — was purely
subtractive, with **no new import in any file**.  Site 3 stays, and stays *specialised*; what
changed there is that its six-line unfolding of the Bézout witness is now a two-line derivation
from Mathlib, so it is an **adapter and not a reproof**.

⚠️ **Two copies remain and that is the decision, not an omission.**  After the above there is
exactly one general `eval` adapter in this tree (the one above) and one specialised statement that
cannot see it — `EllipticCurves.Torsion.NsmulSurjective` is **not** in this file's dependents and
this file imports nothing from the project, so they are siblings with no meet.  The two routes that
would remove the second copy were priced and both rejected:

* **Upstream an `eval` form to Mathlib** and consume it from both.  The only route that genuinely
  removes a copy — and the helper above is stated and named for exactly that — but it is not this
  tree's to land, so it cannot be this issue's deliverable.
* **A new shared low-level file** imported by this one and by `NsmulSurjective`.  Measured at
  `68fd254`: this file's `EllipticCurves`-import closure is **0** and `NsmulSurjective`'s is **7**,
  containing no common module.  A new leaf would take them to **1** and **8** — spending this
  file's empty-closure property — and would remove **no** declaration at all, since the specialised
  statement stays either way and its proof is two lines from Mathlib or one line from a shared
  home.  Not worth it.

## Main definitions and statements

⚠️ Every public declaration of this file is listed.  Two of them are `def`s, which is why the
heading is not `## Main results`.  All but the first are in namespace `WeierstrassCurve`.

* `Polynomial.eval_ne_zero_of_isCoprime` — coprime polynomials have no common root, in `eval`
  form: the only declaration here that mentions no curve, and the only one in namespace
  `Polynomial`.  See *"The de-duplication question, decided"* above for why it lives in this file;
* `WeierstrassCurve.bezoutΦTwo` and `WeierstrassCurve.bezoutΨ₂Sq` — the two Sylvester-adjugate
  cofactors the `Δ²` certificate is stated with;
* `WeierstrassCurve.Φ_two_eq` — `Φ₂ = X·Ψ₂Sq − Ψ₃` (**relocated** here from
  `EllipticCurves.Torsion.DoublingSurjective`, which now imports it);
* `WeierstrassCurve.bezout_Φ_two_Ψ₂Sq` and `WeierstrassCurve.bezout_Ψ₃_Ψ₂Sq` — the certificates;
* `WeierstrassCurve.preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul` — the `n = 3` congruence, over an arbitrary
  commutative ring;
* **`WeierstrassCurve.isCoprime_Φ_two_Ψ₂Sq`**, **`WeierstrassCurve.isCoprime_Ψ₃_Ψ₂Sq`**,
  `WeierstrassCurve.isCoprime_preΨ₄_Ψ₃` and **`WeierstrassCurve.isCoprime_Φ_three_ΨSq_three`** —
  the coprimality, for `[W.IsElliptic]`;
* `WeierstrassCurve.Φ_eq_neg_adjacent_add` and `WeierstrassCurve.ΨSq_succ_mul_ΨSq_pred` — the two
  unconditional identities behind the general-`n` reduction;
* **`WeierstrassCurve.isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent`** and its two-hypothesis form
  `WeierstrassCurve.isCoprime_Φ_ΨSq_of_isCoprime_ΨSq` — the reduction itself, at every `n : ℤ` over
  an arbitrary commutative ring;
* `WeierstrassCurve.eval_Φ_sq_of_eval_ΨSq_eq_zero` — at a root of `ΨSqₙ`, `Φₙ(x)² =
  ΨSqₙ₊₁(x)·ΨSqₙ₋₁(x)`, over an arbitrary commutative ring;
* `WeierstrassCurve.eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero` and its two-factor form
  `WeierstrassCurve.eval_Φ_ne_zero_of_eval_ΨSq_ne_zero` — the pointwise reduction;
* **`WeierstrassCurve.eval_Φ_ne_zero_iff_of_eval_ΨSq_eq_zero`** and its quantified form
  `WeierstrassCurve.forall_eval_Φ_ne_zero_iff` — the pointwise reduction as an **equivalence**, for
  `[NoZeroDivisors R]`.

## What is *not* here

* The general `IsCoprime (W.Φ n) (W.ΨSq n)`. Only `n = 2` and `n = 3` are proved, and — as *"The
  `n = 3` certificate is a congruence, not a resultant"* above sets out — `n = 3` is **not** a
  certificate of its own: it runs through `preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul` and back to the `n = 2`
  certificate, so `bezout_Φ_two_Ψ₂Sq` and `bezout_Ψ₃_Ψ₂Sq` remain the only `Δ²`-identities here.
  The general case *over an arbitrary commutative ring* is `#1184`.  ⚠️ Over a **field** of
  characteristic `≠ 2` on an elliptic curve it is closed —
  `WeierstrassCurve.Affine.isCoprime_Φ_ΨSq` (`EllipticCurves.Torsion.CoprimeAdjacent`) — and with
  it `[F(W) : [n]∗F(W)] = n²` at general `n`
  (`EllipticCurves.FunctionField.MulByNDegreeGeneral`), so the rung-3 paragraph of
  `EllipticCurves.FunctionField.MulByNPlacePullback` no longer names this as an outstanding input.
  ⚠️ **The clause this bullet used to carry has been corrected** — it read *"each by its own ad-hoc
  certificate"*, which the section named above contradicts.
  ⚠️ **A second clause has been narrowed**: it read *"the general case is a much larger
  induction"*, with no route written down.  Half of it is now discharged unconditionally — see
  *"At general `n`, `Φ` is not the difficulty"* above — and what an induction is still owed is
  `IsCoprime (W.ΨSq (n + 1) * W.ΨSq (n - 1)) (W.ΨSq n)`, in which `Φ` does not appear.
* **`IsCoprime (W.ΨSq (n + 1) * W.ΨSq (n - 1)) (W.ΨSq n)` at general `n`, over an arbitrary
  commutative ring** — the obligation the reduction leaves, and the only thing between this file
  and the general case *in this file's generality*.  ⚠️ Its pointwise weakening,
  *"`ΨSqₙ₊₁ · ΨSqₙ₋₁` and `ΨSqₙ` have no common root in `R`"*, is **equally** missing over an
  arbitrary ring and is the obligation the pointwise reduction leaves; see *"The pointwise
  weakening is not a cheaper target"* above.  Of the two routes:
  * the **root argument** — a common root would be an `x`-coordinate that is both `n`- and
    `(n ± 1)`-torsion, hence `O`, which is not affine — has been **run**, and it lands the
    statement at every `n : ℤ` for an elliptic curve **over a field of characteristic `≠ 2`**:
    `WeierstrassCurve.Affine.isCoprime_ΨSq_adjacent`
    (`EllipticCurves.Torsion.CoprimeAdjacent`), with
    `WeierstrassCurve.Affine.isCoprime_Φ_ΨSq` the `Φ` form obtained through the reduction below.
    ⚠️ **That does not discharge this bullet**, and the difference is not a technicality: this file
    asks nothing of the base ring, nothing of the characteristic and nothing of the curve, and the
    route above needs all three — it lifts a root to a *point*, which needs a smooth curve over a
    field in which `2` is invertible, and it descends through
    `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`, which is a statement about fields.
    ⚠️ This bullet used to say the root argument *"needs `#251` and a base change to `F̄`; neither
    is imported here"*.  Both halves have since been supplied — `#251`'s dictionary by
    `EllipticCurves.Torsion.TwoTorsionOrder` and the base change by the Mathlib lemma named above —
    and neither is imported here **still**, which is why the statement below this file's own
    hypotheses remains open.
  * the **recurrence argument**, which is the only known route to the arbitrary-ring form, runs
    through the divisibility structure of `preΨ`, which is
    Mathlib's `preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄`.  ⚠️ That `normEDS` satisfies
    `IsEllipticDvdSequence` is an explicit **Mathlib TODO**
    (`Mathlib.NumberTheory.EllipticDivisibilitySequence`).  `IsEllipticDvdSequence` is
    `IsEllipticSequence ∧ IsDvdSequence`, and its **first** conjunct is what this development
    tracks as `#254` / `#258` / `#260`.  ⚠️ Even granted in full it yields *divisibility*, not the
    strong-divisibility `gcd(ψₘ, ψₙ) = ψ_{gcd(m, n)}` that coprimality of neighbours needs — so it
    is a lower bound on the work here, not a route.
* Any statement about **torsion points**, or `n • P = O ↔ Ψₙ = 0`.  ⚠️ **This bullet used to read
  *"Any statement about roots, torsion points, or `n • P = O ↔ Ψₙ = 0`"*, and the first word of that
  list is no longer true**: `eval_Φ_sq_of_eval_ΨSq_eq_zero` and the three statements built on it are
  statements about roots.  What has not changed, and is what the bullet was protecting, is that no
  root here is ever the `x`-coordinate of a point — the pointwise statements quantify over `x : R`
  and know nothing of `W.Point`, so the torsion characterisation is still absent **here**.  ⚠️ It
  is `#251`'s, and `#251` is closed: `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic`
  (`EllipticCurves.Torsion.TwoTorsionOrder`), which is not in this file's import closure.
* Anything about `RatFunc`, function fields, or the degree of `[n]`. The consumers are the middle
  steps of the towers computing `[F(W) : [2]∗F(W)] = 4` and `[F(W) : [3]∗F(W)] = 9`, in
  `EllipticCurves.FunctionField.MulByTwoDegree` and
  `EllipticCurves.FunctionField.MulByThreeDegree`; each reads `Φₙ/ΨSqₙ` as a reduced fraction and
  needs exactly the coprimality proved here.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
* L. Washington, *Elliptic Curves: Number Theory and Cryptography*, §3.2.
-/


-- @@ L302-302 verbatim
open Polynomial


-- @@ L304-305 verbatim
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])


-- @@ L307-311 verbatim
/-! ## The `eval` shadow of `Polynomial.aeval_ne_zero_of_isCoprime`

⚠️ **Not about elliptic curves**, and the only declaration in this file that is not.  It is here
because every consumer of it in this tree is downstream of this file and there is nowhere cheaper
to put it — see *"The de-duplication question, decided"* in the module docstring. -/


-- @@ L313-313 verbatim
namespace Polynomial


-- @@ L315-333 verbatim
/-- **Coprime polynomials have no common root**, in `eval` form.

Mathlib has this as `Polynomial.aeval_ne_zero_of_isCoprime`, whose conclusion is the disjunction
`aeval s p ≠ 0 ∨ aeval s q ≠ 0` over an arbitrary `Nontrivial` algebra; at `S = R` the two shapes
differ by `Polynomial.coe_aeval_eq_eval` and by discharging one side of the disjunction from the
hypothesis.  ⚠️ **Mathlib has no `eval`-shaped form**: grepped at `v4.32.0`, the `aeval` lemma has
its declaration in `Mathlib/Algebra/Polynomial/RingDivision.lean` and exactly three uses
(`FieldTheory/IsAlgClosed/Basic`, `FieldTheory/RatFunc/Luroth`,
`FieldTheory/SplittingField/Construction`), none of them an `eval` restatement.  So this two-line
adapter is the whole content, and it is an upstream candidate exactly as it stands.

⚠️ **This is deliberately in namespace `Polynomial` and not in `WeierstrassCurve`**, because
nothing about it mentions a curve: it is stated for arbitrary `a b : R[X]` over an arbitrary
`Nontrivial` commutative semiring, which is strictly more general than the `[CommRing R]
[IsDomain R]` the section that used to hold it supplies. -/
theorem eval_ne_zero_of_isCoprime {R : Type*} [CommSemiring R] [Nontrivial R] {a b : R[X]}
    (h : IsCoprime a b) {x : R} (hb : b.eval x = 0) : a.eval x ≠ 0 := by
  have h' := Polynomial.aeval_ne_zero_of_isCoprime (S := R) h x
  simpa [Polynomial.coe_aeval_eq_eval, hb] using h'


-- @@ L335-335 verbatim
end Polynomial


-- @@ L337-337 verbatim
namespace WeierstrassCurve


-- @@ L339-339 verbatim
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


-- @@ L341-341 verbatim
/-! ### The Bézout cofactors -/


-- @@ L343-355 verbatim
/-- The cofactor of `Φ₂` in the Bézout identity `bezout_Φ_two_Ψ₂Sq`.  It is the `Φ₂`-part of the
adjugate of the Sylvester matrix of the pair `(Ψ₂Sq, Φ₂)`. -/
noncomputable def bezoutΦTwo : R[X] :=
  C (-8 * W.b₂ ^ 2 * W.b₄ ^ 2 + 8 * W.b₂ ^ 3 * W.b₆ + 288 * W.b₄ ^ 3 - 336 * W.b₂ * W.b₄ * W.b₆
      + 16 * W.b₂ ^ 2 * W.b₈ + 1296 * W.b₆ ^ 2 - 384 * W.b₄ * W.b₈)
      * X ^ 2
    + C (-2 * W.b₂ ^ 3 * W.b₄ ^ 2 + 2 * W.b₂ ^ 4 * W.b₆ + 72 * W.b₂ * W.b₄ ^ 3
      - 80 * W.b₂ ^ 2 * W.b₄ * W.b₆ - 144 * W.b₄ ^ 2 * W.b₆ + 360 * W.b₂ * W.b₆ ^ 2
      + 32 * W.b₂ * W.b₄ * W.b₈ - 576 * W.b₆ * W.b₈)
      * X
    + C (-4 * W.b₂ ^ 2 * W.b₄ ^ 3 + 5 * W.b₂ ^ 3 * W.b₄ * W.b₆ - W.b₂ ^ 4 * W.b₈ + 144 * W.b₄ ^ 4
      - 204 * W.b₂ * W.b₄ ^ 2 * W.b₆ + W.b₂ ^ 2 * W.b₆ ^ 2 + 48 * W.b₂ ^ 2 * W.b₄ * W.b₈
      + 864 * W.b₄ * W.b₆ ^ 2 - 384 * W.b₄ ^ 2 * W.b₈ - 176 * W.b₂ * W.b₆ * W.b₈ + 256 * W.b₈ ^ 2)


-- @@ L357-372 verbatim
/-- The cofactor of `Ψ₂Sq` in the Bézout identity `bezout_Φ_two_Ψ₂Sq`. -/
noncomputable def bezoutΨ₂Sq : R[X] :=
  C (2 * W.b₂ ^ 2 * W.b₄ ^ 2 - 2 * W.b₂ ^ 3 * W.b₆ - 72 * W.b₄ ^ 3 + 84 * W.b₂ * W.b₄ * W.b₆
      - 4 * W.b₂ ^ 2 * W.b₈ - 324 * W.b₆ ^ 2 + 96 * W.b₄ * W.b₈)
      * X ^ 3
    + C (-W.b₂ ^ 2 * W.b₄ * W.b₆ + W.b₂ ^ 3 * W.b₈ + 36 * W.b₄ ^ 2 * W.b₆ - 9 * W.b₂ * W.b₆ ^ 2
      - 32 * W.b₂ * W.b₄ * W.b₈ + 144 * W.b₆ * W.b₈)
      * X ^ 2
    + C (-2 * W.b₂ ^ 2 * W.b₄ ^ 3 + 2 * W.b₂ ^ 3 * W.b₄ * W.b₆ + 72 * W.b₄ ^ 4
      - 84 * W.b₂ * W.b₄ ^ 2 * W.b₆ + 2 * W.b₂ ^ 2 * W.b₆ ^ 2 + 2 * W.b₂ ^ 2 * W.b₄ * W.b₈
      + 270 * W.b₄ * W.b₆ ^ 2 - 48 * W.b₄ ^ 2 * W.b₈ + 8 * W.b₂ * W.b₆ * W.b₈ - 64 * W.b₈ ^ 2)
      * X
    + C (-3 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ + 4 * W.b₂ ^ 3 * W.b₆ ^ 2 - W.b₂ ^ 3 * W.b₄ * W.b₈
      + 108 * W.b₄ ^ 3 * W.b₆ - 162 * W.b₂ * W.b₄ * W.b₆ ^ 2 + 36 * W.b₂ * W.b₄ ^ 2 * W.b₈
      + 7 * W.b₂ ^ 2 * W.b₆ * W.b₈ + 729 * W.b₆ ^ 3 - 432 * W.b₄ * W.b₆ * W.b₈
      + 16 * W.b₂ * W.b₈ ^ 2)


-- @@ L374-374 verbatim
/-! ### The identities -/


-- @@ L376-388 verbatim
/-- **`Φ₂ = X · Ψ₂Sq - Ψ₃`.** Both sides are `X⁴ - b₄X² - 2b₆X - b₈`: the `X³` terms of `X · Ψ₂Sq`
and `Ψ₃` agree, and the remaining coefficients differ by `2b₄ - 3b₄ = -b₄` and `b₆ - 3b₆ = -2b₆`.

It is also what transfers the Bézout certificate below from `Φ₂` to `Ψ₃`.

**Relocated, not new.**  This lemma was proved in `EllipticCurves.Torsion.DoublingSurjective`; it is
a general fact about `Φ`, `Ψ₂Sq` and `Ψ₃` over an arbitrary commutative ring, with no torsion point
in it, so it belongs at the bottom of the import hierarchy rather than in the torsion tree.  That
file now imports it from here; the proof is unchanged. -/
lemma Φ_two_eq : W.Φ 2 = X * W.Ψ₂Sq - W.Ψ₃ := by
  rw [Φ_two, Ψ₂Sq, Ψ₃]
  simp only [map_ofNat, C_mul]
  ring1


-- @@ L390-407 expanded
/-- **The Bézout certificate for `Φ₂` and `Ψ₂Sq`, with right-hand side `Δ²`.**

The cofactors come from the Sylvester adjugate, so in the free ring `ℤ[b₂, b₄, b₆, b₈][X]` the
combination equals the resultant, not `Δ²`; the two differ by a multiple of `4b₈ − b₂b₆ + b₄²`,
which is `0` by `b_relation`.  That multiple is the `linear_combination` coefficient below. -/
theorem bezout_Φ_two_Ψ₂Sq : W.bezoutΦTwo * W.Φ 2 + W.bezoutΨ₂Sq * W.Ψ₂Sq = C (W.Δ ^ 2) :=
  by
  have hb : (4 : R[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 :=
    by
    have h := congrArg (C : R →+* R[X]) W.b_relation
    simp only [map_ofNat, C_sub, C_mul, C_pow] at h
    exact h
  rw [bezoutΦTwo, bezoutΨ₂Sq, Φ_two, Ψ₂Sq, Δ]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  linear_combination (norm := ring1)
    (-64 * C W.b₄ ^ 4 + 80 * C W.b₂ * C W.b₄ ^ 2 * C W.b₆ - 4 * C W.b₂ ^ 2 * C W.b₆ ^ 2 -
                12 * C W.b₂ ^ 2 * C W.b₄ * C W.b₈ -
              324 * C W.b₄ * C W.b₆ ^ 2 +
            112 * C W.b₄ ^ 2 * C W.b₈ +
          32 * C W.b₂ * C W.b₆ * C W.b₈ -
        64 * C W.b₈ ^ 2) *
      hb


-- @@ L409-415 verbatim
/-- **The Bézout certificate for `Ψ₃` and `Ψ₂Sq`**, obtained from `bezout_Φ_two_Ψ₂Sq` through
`Φ_two_eq`. -/
theorem bezout_Ψ₃_Ψ₂Sq :
    (-W.bezoutΦTwo) * W.Ψ₃ + (W.bezoutΦTwo * X + W.bezoutΨ₂Sq) * W.Ψ₂Sq = C (W.Δ ^ 2) := by
  have h := W.bezout_Φ_two_Ψ₂Sq
  rw [W.Φ_two_eq] at h
  linear_combination h


-- @@ L417-417 verbatim
/-! ### The `n = 3` certificate, via a congruence rather than a resultant -/


-- @@ L419-455 expanded
/-- **`preΨ₄² ≡ Ψ₂Sq⁴ modulo Ψ₃`**, with the cofactor written out.

The naive route to `IsCoprime (Φ₃) (ΨSq₃)` is a Bézout certificate for the pair itself, whose
Sylvester matrix is `17 × 17`; the resultant has weight `48` in `b₂, …, b₈` and neither it nor its
cofactors is a polynomial a `ring1` call would survive.  This congruence replaces the whole of it,
and it is small because it is a *composite* of two facts already in the tree:

* `ψ₂(2P) = ψ₄(P)/ψ₂(P)⁴` — in univariate form, `preΨ₄²` is `Ψ₂Sq` evaluated at the duplication
  fraction `Φ₂/Ψ₂Sq`, cleared of denominators:
  `preΨ₄² = 4Φ₂³ + b₂Φ₂²Ψ₂Sq + 2b₄Φ₂Ψ₂Sq² + b₆Ψ₂Sq³`;
* `Φ_two_eq`, i.e. `Φ₂ = X·Ψ₂Sq − Ψ₃`.

Substituting the second into the first and discarding every term carrying a factor `Ψ₃` leaves
`Ψ₂Sq³·(4X³ + b₂X² + 2b₄X + b₆) = Ψ₂Sq⁴`; what is discarded is `Ψ₃` times the cofactor below.
Geometrically: a point with `Ψ₃(x) = 0` has `2P = −P`, so `ψ₂(2P)² = ψ₂(P)²` up to the fourth power
of `ψ₂(P)` coming from the denominator — a `4`-torsion point is never `3`-torsion.

As with `bezout_Φ_two_Ψ₂Sq` the identity is **false** in the free ring `ℤ[b₂, b₄, b₆, b₈][X]` and
holds only against `b_relation`, which is why the proof is a `linear_combination` and not a
`ring1`; the correction term is the explicit degree-`8` multiplier below.  Nothing is divided by, so
this holds in every characteristic. -/
theorem preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul :
    W.preΨ₄ ^ 2 =
      W.Ψ₂Sq ^ 4 +
        W.Ψ₃ *
          ((12 * X + C W.b₂) * W.Ψ₂Sq * W.Ψ₃ - 4 * W.Ψ₃ ^ 2 -
            (12 * X ^ 2 + C (2 * W.b₂) * X + C (2 * W.b₄)) * W.Ψ₂Sq ^ 2) :=
  by
  have hb : (4 : R[X]) * C W.b₈ = C W.b₂ * C W.b₆ - C W.b₄ ^ 2 :=
    by
    have h := congrArg (C : R →+* R[X]) W.b_relation
    simp only [map_ofNat, C_sub, C_mul, C_pow] at h
    exact h
  rw [preΨ₄, Ψ₂Sq, Ψ₃]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  linear_combination (norm := ring1)
    (13 * X ^ 8 + 8 * C W.b₂ * X ^ 7 + 28 * C W.b₄ * X ^ 6 + C W.b₂ ^ 2 * X ^ 6 +
                            38 * C W.b₆ * X ^ 5 +
                          6 * C W.b₂ * C W.b₄ * X ^ 5 +
                        22 * C W.b₈ * X ^ 4 +
                      8 * C W.b₄ ^ 2 * X ^ 4 +
                    7 * C W.b₂ * C W.b₆ * X ^ 4 +
                  16 * C W.b₄ * C W.b₆ * X ^ 3 +
                4 * C W.b₂ * C W.b₈ * X ^ 3 +
              7 * C W.b₆ ^ 2 * X ^ 2 +
            8 * C W.b₄ * C W.b₈ * X ^ 2 +
          6 * C W.b₆ * C W.b₈ * X +
        C W.b₈ ^ 2) *
      hb


-- @@ L457-462 verbatim
/-! ### The general-`n` reduction: `Φₙ` disappears

Everything in this section holds over an arbitrary commutative ring, at every `n : ℤ`, with no
`[W.IsElliptic]` and no hypothesis on `n`.  It is stated separately from the two certificates above
because it proves no coprimality at all: it *transports* one.
-/


-- @@ L464-472 verbatim
/-- **`Φₙ` is `X · ΨSqₙ` minus the adjacent product**, which is Mathlib's definition of `Φ`
rearranged so that the `ΨSqₙ`-multiple is visible.

Writing `Eₙ := if Even n then 1 else Ψ₂Sq`, the adjacent product is `preΨₙ₊₁ · preΨₙ₋₁ · Eₙ`. -/
theorem Φ_eq_neg_adjacent_add (n : ℤ) :
    W.Φ n = -(W.preΨ (n + 1) * W.preΨ (n - 1) * (if Even n then 1 else W.Ψ₂Sq))
      + W.ΨSq n * X := by
  rw [WeierstrassCurve.Φ]
  ring


-- @@ L474-489 verbatim
/-- **The adjacent product is a square: `ΨSqₙ₊₁ · ΨSqₙ₋₁ = (preΨₙ₊₁ · preΨₙ₋₁ · Eₙ)²`.**

`n + 1` and `n - 1` have the same parity, opposite to `n`'s, so the two `if`s in `ΨSq` fire
together and the factor they contribute is `Ψ₂Sq²` when `n` is odd and `1` when `n` is even —
which is exactly `Eₙ²`.  Nothing is divided by and no hypothesis on `n` is needed. -/
theorem ΨSq_succ_mul_ΨSq_pred (n : ℤ) :
    W.ΨSq (n + 1) * W.ΨSq (n - 1)
      = (W.preΨ (n + 1) * W.preΨ (n - 1) * (if Even n then 1 else W.Ψ₂Sq)) ^ 2 := by
  have hs : ¬Even (n + 1) ↔ Even n := by simp
  have hp : ¬Even (n - 1) ↔ Even n := by simp
  simp only [ΨSq]
  by_cases hn : Even n
  · rw [if_neg (by simpa [hs] using hn), if_neg (by simpa [hp] using hn), if_pos hn]
    ring
  · rw [if_pos (by simpa [hs] using hn), if_pos (by simpa [hp] using hn), if_neg hn]
    ring


-- @@ L491-491 verbatim
section ImplicitW


-- @@ L493-493 verbatim
variable {W}


-- @@ L495-512 verbatim
/-- **`IsCoprime (Φₙ) (ΨSqₙ)` follows from coprimality of the *adjacent* division polynomials**,
at every `n : ℤ`, over an arbitrary commutative ring, with no `[W.IsElliptic]`.

Modulo `ΨSqₙ` the identity `Φ_eq_neg_adjacent_add` leaves `Φₙ ≡ −preΨₙ₊₁ · preΨₙ₋₁ · Eₙ`, and
`ΨSq_succ_mul_ΨSq_pred` says the square of that product is `ΨSqₙ₊₁ · ΨSqₙ₋₁`.  A factor of a
coprime element is coprime, so the hypothesis descends to the product itself and
`IsCoprime.add_mul_left_left` finishes.

⚠️ **This eliminates `Φ` from the general-`n` problem.**  What is left is a statement about `ΨSq`
alone, and it is the classical *"`ψₘ` and `ψₙ` have no common root unless `gcd(m, n) > 1`"* at
`m = n ± 1`.  That statement is **not** proved in this development at general `n`; see this file's
`## What is *not* here`. -/
theorem isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent {n : ℤ}
    (h : IsCoprime (W.ΨSq (n + 1) * W.ΨSq (n - 1)) (W.ΨSq n)) :
    IsCoprime (W.Φ n) (W.ΨSq n) := by
  rw [W.ΨSq_succ_mul_ΨSq_pred n] at h
  rw [W.Φ_eq_neg_adjacent_add n]
  exact (h.of_isCoprime_of_dvd_left (dvd_pow_self _ two_ne_zero)).neg_left.add_mul_left_left X


-- @@ L514-518 verbatim
/-- The two-hypothesis form of `isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent`, which is the shape an
induction on the recurrence would produce: `ΨSqₙ` coprime to each neighbour separately. -/
theorem isCoprime_Φ_ΨSq_of_isCoprime_ΨSq {n : ℤ} (hs : IsCoprime (W.ΨSq (n + 1)) (W.ΨSq n))
    (hp : IsCoprime (W.ΨSq (n - 1)) (W.ΨSq n)) : IsCoprime (W.Φ n) (W.ΨSq n) :=
  isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent (hs.mul_left hp)


-- @@ L520-554 verbatim
/-! ### The pointwise reduction, and why the weaker statement is not the cheaper target

⚠️ **`EllipticCurves.Torsion.NsmulSurjective` does not consume `IsCoprime (Φₙ) (ΨSqₙ)`.**  Its
surjectivity engine takes the strictly weaker *pointwise* hypothesis
`∀ x, ΨSqₙ(x) = 0 → Φₙ(x) ≠ 0`, and recorded that this tree obtained that weakening at `n = 2` and
`n = 3` without any Bézout certificate — where the two `IsCoprime` instances above cost an explicit
`Δ²` certificate and a congruence argument reusing it.  `#1184`'s planning note asks, on that
evidence, whether the pointwise statement is therefore the cheaper **general** target and should be
spiked first.

⚠️ **The past tense is deliberate.**  The two certificate-free arguments still exist, as `example`s
in the two downstream files, but they are no longer how those files' `hroot` instances are proved:
both now route through this file, paying a `Δ`-certificate for a *neighbouring* pair in order to
drop `[IsAlgClosed F]` and `(2 : F) ≠ 0`.  That trade changes nothing below — the question `#1184`'s
note asks is about general `n`, where neither certificate is available at all.

The lemmas below answer that, and the answer is **no**.  At a root of `ΨSqₙ` the identity
`Φ_eq_neg_adjacent_add` leaves `Φₙ(x) = −preΨₙ₊₁(x) · preΨₙ₋₁(x) · Eₙ(x)`, whose square is
`ΨSqₙ₊₁(x) · ΨSqₙ₋₁(x)` by `ΨSq_succ_mul_ΨSq_pred`.  So over a ring with no zero divisors the
pointwise statement for `(Φₙ, ΨSqₙ)` is **equivalent** to the pointwise statement for the adjacent
pair — `eval_Φ_ne_zero_iff_of_eval_ΨSq_eq_zero` — exactly as
`isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent` makes the Bézout statements interderivable in one
direction.

⚠️ **What the weakening buys is therefore precisely the Bézout certificate and nothing else.**  It
does not touch the `ΨSq`-neighbour difficulty, which is the whole of what survives the reduction
above and is what this file's `## What is *not* here` records as open.  A worker choosing between
the two targets is choosing between `IsCoprime (ΨSqₙ₊₁ · ΨSqₙ₋₁) (ΨSqₙ)` and *"`ΨSqₙ₊₁ · ΨSqₙ₋₁`
and `ΨSqₙ` have no common root in `R`"*; the `Φ` in the question was never the difficulty in either
form.

Everything here holds at every `n : ℤ` with no `[W.IsElliptic]` and no hypothesis on `n`; only the
converse direction asks for `[NoZeroDivisors R]`, and it asks for it because `a ^ 2 = 0` does not
imply `a = 0` in a ring with nilpotents.
-/


-- @@ L556-568 verbatim
/-- **At a root of `ΨSqₙ`, the square of `Φₙ` is the adjacent product.**

`Φ_eq_neg_adjacent_add` writes `Φₙ` as `−preΨₙ₊₁ · preΨₙ₋₁ · Eₙ + ΨSqₙ · X`, so the `ΨSqₙ`-multiple
drops out at a root and what is left is `±` the adjacent product; `ΨSq_succ_mul_ΨSq_pred` says the
square of that product is `ΨSqₙ₊₁ · ΨSqₙ₋₁`, and the sign disappears in the squaring.

⚠️ The hypothesis is used exactly once and only to delete the `ΨSqₙ · X` term.  Nothing here is
divided by, so this holds over an arbitrary commutative ring at every `n : ℤ`. -/
theorem eval_Φ_sq_of_eval_ΨSq_eq_zero {n : ℤ} {x : R} (hx : (W.ΨSq n).eval x = 0) :
    (W.Φ n).eval x ^ 2 = (W.ΨSq (n + 1)).eval x * (W.ΨSq (n - 1)).eval x := by
  rw [← eval_mul, W.ΨSq_succ_mul_ΨSq_pred n, W.Φ_eq_neg_adjacent_add n]
  simp only [eval_pow, eval_add, eval_neg, eval_mul, hx, zero_mul, add_zero]
  ring


-- @@ L570-582 verbatim
/-- **The pointwise analogue of `isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent`**: at a root of `ΨSqₙ`
at which the adjacent product does not vanish, `Φₙ` does not vanish either.

This is the direction the surjectivity engine of `EllipticCurves.Torsion.NsmulSurjective` consumes,
and like the `IsCoprime` reduction it eliminates `Φ` from the problem.  It needs no hypothesis on
`R` beyond `CommRing`: if `Φₙ(x)` were `0` its square would be `0` too, and
`eval_Φ_sq_of_eval_ΨSq_eq_zero` identifies that square with the adjacent product. -/
theorem eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero {n : ℤ} {x : R} (hx : (W.ΨSq n).eval x = 0)
    (h : (W.ΨSq (n + 1)).eval x * (W.ΨSq (n - 1)).eval x ≠ 0) : (W.Φ n).eval x ≠ 0 := by
  intro h0
  refine h ?_
  rw [← eval_Φ_sq_of_eval_ΨSq_eq_zero hx, h0]
  ring


-- @@ L584-584 verbatim
section NoZeroDivisors


-- @@ L586-586 verbatim
variable [NoZeroDivisors R]


-- @@ L588-593 verbatim
/-- The two-factor form of `eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero`, matching
`isCoprime_Φ_ΨSq_of_isCoprime_ΨSq`'s relation to the one-factor reduction. -/
theorem eval_Φ_ne_zero_of_eval_ΨSq_ne_zero {n : ℤ} {x : R} (hx : (W.ΨSq n).eval x = 0)
    (hs : (W.ΨSq (n + 1)).eval x ≠ 0) (hp : (W.ΨSq (n - 1)).eval x ≠ 0) :
    (W.Φ n).eval x ≠ 0 :=
  eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero hx (mul_ne_zero hs hp)


-- @@ L595-603 verbatim
/-- **The reduction is an equivalence**, and that is the point of this section: at a root of `ΨSqₙ`,
`Φₙ` is nonzero *if and only if* the adjacent product is.

⚠️ This is the sense in which the pointwise weakening of `#1184` is **not** a cheaper general
target.  The reverse implication is where `[NoZeroDivisors R]` is spent — `Φₙ(x) ^ 2` being `0` is
all the identity gives, and over a ring with nilpotents that is weaker than `Φₙ(x) = 0`. -/
theorem eval_Φ_ne_zero_iff_of_eval_ΨSq_eq_zero {n : ℤ} {x : R} (hx : (W.ΨSq n).eval x = 0) :
    (W.Φ n).eval x ≠ 0 ↔ (W.ΨSq (n + 1)).eval x * (W.ΨSq (n - 1)).eval x ≠ 0 := by
  rw [← eval_Φ_sq_of_eval_ΨSq_eq_zero hx, ne_eq, ne_eq, pow_eq_zero_iff two_ne_zero]


-- @@ L605-613 verbatim
/-- The quantified form.  The left-hand side is verbatim the second hypothesis of
`nsmul_surjective_of_hasXCoordFormula` (`EllipticCurves.Torsion.NsmulSurjective`), so this says what
that engine's remaining index-dependent input *is*, once `Φ` is removed from it. -/
theorem forall_eval_Φ_ne_zero_iff {n : ℤ} :
    (∀ x : R, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0) ↔
      ∀ x : R, (W.ΨSq n).eval x = 0 →
        (W.ΨSq (n + 1)).eval x * (W.ΨSq (n - 1)).eval x ≠ 0 :=
  ⟨fun h x hx => (eval_Φ_ne_zero_iff_of_eval_ΨSq_eq_zero hx).mp (h x hx),
    fun h x hx => (eval_Φ_ne_zero_iff_of_eval_ΨSq_eq_zero hx).mpr (h x hx)⟩


-- @@ L615-615 verbatim
end NoZeroDivisors


-- @@ L617-617 verbatim
end ImplicitW


-- @@ L619-619 verbatim
/-! ### Coprimality -/


-- @@ L621-621 verbatim
section IsElliptic


-- @@ L623-623 verbatim
variable [W.IsElliptic]


-- @@ L625-632 verbatim
/-- Any Bézout combination landing on `C (Δ²)` witnesses coprimality, because `Δ` is a unit. -/
private theorem isCoprime_of_eq_C_Δ_sq {a b p q : R[X]}
    (h : a * p + b * q = C (W.Δ ^ 2)) : IsCoprime p q := by
  obtain ⟨w, hw⟩ := (W.isUnit_Δ.pow 2).map (C : R →+* R[X])
  refine ⟨(↑w⁻¹ : R[X]) * a, (↑w⁻¹ : R[X]) * b, ?_⟩
  have hring : (↑w⁻¹ : R[X]) * a * p + (↑w⁻¹ : R[X]) * b * q
      = (↑w⁻¹ : R[X]) * (a * p + b * q) := by ring
  rw [hring, h, ← hw, ← Units.val_mul, inv_mul_cancel, Units.val_one]


-- @@ L634-636 verbatim
/-- **`Φ₂` and `Ψ₂Sq` are coprime** on an elliptic curve. -/
theorem isCoprime_Φ_two_Ψ₂Sq : IsCoprime (W.Φ 2) W.Ψ₂Sq :=
  W.isCoprime_of_eq_C_Δ_sq W.bezout_Φ_two_Ψ₂Sq


-- @@ L638-641 verbatim
/-- **`Ψ₃` and `Ψ₂Sq` are coprime** on an elliptic curve: no point is both `2`-torsion and
`3`-torsion.  This is the statement that fails on a singular curve. -/
theorem isCoprime_Ψ₃_Ψ₂Sq : IsCoprime W.Ψ₃ W.Ψ₂Sq :=
  W.isCoprime_of_eq_C_Δ_sq W.bezout_Ψ₃_Ψ₂Sq


-- @@ L643-652 verbatim
/-- **`preΨ₄` and `Ψ₃` are coprime** on an elliptic curve: no point is simultaneously of order
dividing `4` but not `2`, and of order `3`.

The certificate is the congruence `preΨ₄² ≡ Ψ₂Sq⁴ (mod Ψ₃)` together with `isCoprime_Ψ₃_Ψ₂Sq`; no
Bézout identity for this pair is computed. -/
theorem isCoprime_preΨ₄_Ψ₃ : IsCoprime W.preΨ₄ W.Ψ₃ := by
  have h : IsCoprime (W.preΨ₄ ^ 2) W.Ψ₃ := by
    rw [W.preΨ₄_sq_eq_Ψ₂Sq_pow_add_Ψ₃_mul]
    exact (W.isCoprime_Ψ₃_Ψ₂Sq.symm.pow_left).add_mul_left_left _
  exact h.of_isCoprime_of_dvd_left (dvd_pow_self _ two_ne_zero)


-- @@ L654-667 verbatim
/-- **`Φ₃` and `ΨSq₃` are coprime** on an elliptic curve — the reduced-fraction hypothesis that the
degree computation `[F(x) : F(x₃)] = 9` needs of `x(3P) = Φ₃/ΨSq₃`.

`ΨSq₃ = Ψ₃²`, so it suffices to be coprime to `Ψ₃`; and `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq` is congruent to
`−preΨ₄·Ψ₂Sq` modulo `Ψ₃`, where both factors are coprime to `Ψ₃` — the second by
`isCoprime_Ψ₃_Ψ₂Sq`, the first by `isCoprime_preΨ₄_Ψ₃`. -/
theorem isCoprime_Φ_three_ΨSq_three : IsCoprime (W.Φ 3) (W.ΨSq 3) := by
  have hΦ : W.Φ 3 = -(W.preΨ₄ * W.Ψ₂Sq) + W.Ψ₃ * (X * W.Ψ₃) := by
    rw [WeierstrassCurve.Φ_three]; ring1
  have h : IsCoprime (W.Φ 3) W.Ψ₃ := by
    rw [hΦ]
    exact ((W.isCoprime_preΨ₄_Ψ₃.mul_left W.isCoprime_Ψ₃_Ψ₂Sq.symm).neg_left).add_mul_left_left _
  rw [WeierstrassCurve.ΨSq_three]
  exact h.pow_right


-- @@ L669-679 verbatim
/-! #### ⚠️ The general reduction, validated at both merged indices

`isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent` is unconditional, so nothing above rules out its
hypothesis being unsatisfiable.  The two examples below discharge it at the only two indices at
which this file proves anything, and in doing so **re-derive both merged coprimality statements
through the general route** — including `isCoprime_Φ_three_ΨSq_three`, whose hand proof above is
the `n = 3` instance of exactly this argument.

⚠️ They are `example`s and not theorems on purpose: their statements are literally
`isCoprime_Φ_two_Ψ₂Sq` (`ΨSq 2 = Ψ₂Sq`) and `isCoprime_Φ_three_ΨSq_three`, so naming them would put
two names on one statement. -/


-- @@ L681-687 verbatim
/-- **The reduction at `n = 2`.**  The adjacent product is `ΨSq₃ · ΨSq₁ = Ψ₃² · 1`, so the
hypothesis is `isCoprime_Ψ₃_Ψ₂Sq` squared. -/
example : IsCoprime (W.Φ 2) (W.ΨSq 2) := by
  refine isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent ?_
  rw [show (2 : ℤ) + 1 = 3 from rfl, show (2 : ℤ) - 1 = 1 from rfl, ΨSq_three, ΨSq_one, ΨSq_two,
    mul_one]
  exact W.isCoprime_Ψ₃_Ψ₂Sq.pow_left


-- @@ L689-696 verbatim
/-- **The reduction at `n = 3`.**  The adjacent product is `ΨSq₄ · ΨSq₂ = preΨ₄² · Ψ₂Sq · Ψ₂Sq`
against `ΨSq₃ = Ψ₃²`, so the hypothesis is `isCoprime_preΨ₄_Ψ₃` and `isCoprime_Ψ₃_Ψ₂Sq` — the same
two inputs the hand proof above uses, assembled by the general lemma instead of by hand. -/
example : IsCoprime (W.Φ 3) (W.ΨSq 3) := by
  refine isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent ?_
  rw [show (3 : ℤ) + 1 = 4 from rfl, show (3 : ℤ) - 1 = 2 from rfl, ΨSq_four, ΨSq_two, ΨSq_three]
  exact ((W.isCoprime_preΨ₄_Ψ₃.pow_left.mul_left W.isCoprime_Ψ₃_Ψ₂Sq.symm).mul_left
    W.isCoprime_Ψ₃_Ψ₂Sq.symm).pow_right


-- @@ L698-751 verbatim
/-! #### ⚠️ The pointwise reduction, validated at the same two indices — and it lands both merged
`hroot` instances with strictly fewer hypotheses

`eval_Φ_ne_zero_of_eval_ΨSq_adjacent_ne_zero` is unconditional too, so nothing above rules out
*its* hypothesis being unsatisfiable.  The two examples below discharge it at `n = 2` and `n = 3`
from the same inputs the two `IsCoprime` examples use, one point at a time.

⚠️ **What they land already exists downstream, and this is a measurement rather than a
duplication.**  Their conclusions are the conclusions of `eval_Φ_two_ne_zero_of_root_ΨSq`
(`EllipticCurves.Torsion.DoublingSurjective`) and `eval_Φ_three_ne_zero_of_root_ΨSq`
(`EllipticCurves.Torsion.TriplingSurjective`) — the two `hroot` instances of
`exists_nsmul_eq_of_hasXCoordFormula` — character for character once `Affine F` is unfolded to
`WeierstrassCurve F`, which it is by `abbrev`.

⚠️ **The three sentences that used to follow have been acted on and are retired.**  They read:

> **The hypotheses are not the same**, and that is the point of putting them here: the merged
> statements carry, at `n = 2` and at `n = 3` alike, `[Field F]`, `[IsAlgClosed F]`,
> `[W.IsElliptic]` and `(2 : F) ≠ 0`; the route below carries `[CommRing R]`, `[IsDomain R]` and
> `[W.IsElliptic]`, and nothing else. … **Nothing is changed at either site here** — narrowing a
> merged signature is a separate decision with its own call-site check, and this section records
> the measurement so that decision can be made on it.

That decision has been made and the call-site check run: both downstream statements now carry
`[Field F]` and `[W.IsElliptic]` and nothing else, and each is proved by the corresponding
`example` below, transcribed into the ambient `[Field F]`.  The remaining difference is only that
those files fix a field where this one takes a domain.

⚠️ **What the narrowing cost, recorded here because this is where the trade is visible.**  The
merged proofs reached `hroot` through `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`
(`EllipticCurves.Torsion.ThreeTorsionStructure`), a statement about the points above an `x`, which
is where the closure and the characteristic condition came from — and which needs **no Bézout
certificate of any kind**.  The route below reaches it through `isCoprime_Ψ₃_Ψ₂Sq` and
`isCoprime_preΨ₄_Ψ₃`, which carry neither hypothesis but **do** rest on the `Δ` certificates at the
top of this file.  Both downstream files therefore keep their old proof verbatim, as an `example`
under the old hypotheses, so that neither route leaves the tree.

⚠️ **`DoublingSurjective` imports this file directly and `TriplingSurjective` imports
`DoublingSurjective`**, which is what made the narrowing a `#699`-class de-duplication question
rather than an import problem.

⚠️ **They are `example`s and not theorems** for the reason the `IsCoprime` pair above gives: the
statements already have names downstream, and a third name on the same statement is the worse
outcome.

⚠️ **`[IsDomain R]` appears here and nowhere else in this file**, and it is spent in three places,
none of them in a general statement: `pow_ne_zero` at `n = 2`, `pow_eq_zero_iff` extracting
`Ψ₃(x) = 0` from `ΨSq₃(x) = 0` at `n = 3` — both `NoZeroDivisors` — and `Nontrivial` for
`Polynomial.eval_ne_zero_of_isCoprime`, without which `1 = 0` is not a contradiction.  ⚠️ **That
last clause used to read *"`Nontrivial` inside the `IsCoprime`-to-root helper below"***, and the
word *below* is no longer right: `#1255` made that helper public and moved it to the top of this
file, where it is stated at `[CommSemiring R] [Nontrivial R]` and asks for no domain at all.  The
general lemmas above ask for `NoZeroDivisors` at most, and two of the four ask for nothing beyond
`CommRing`. -/


-- @@ L753-753 verbatim
section Domain


-- @@ L755-755 verbatim
variable [IsDomain R]


-- @@ L757-765 verbatim
/-- **The pointwise reduction at `n = 2`.**  The adjacent product is `ΨSq₃ · ΨSq₁ = Ψ₃² · 1`, so the
hypothesis is `isCoprime_Ψ₃_Ψ₂Sq` read at the root — the same input the `IsCoprime` example above
uses, one point at a time. -/
example (x : R) (hx : (W.ΨSq 2).eval x = 0) : (W.Φ 2).eval x ≠ 0 := by
  refine eval_Φ_ne_zero_of_eval_ΨSq_ne_zero hx ?_ ?_
  · rw [show (2 : ℤ) + 1 = 3 from rfl, ΨSq_three, eval_pow]
    exact pow_ne_zero _ (eval_ne_zero_of_isCoprime W.isCoprime_Ψ₃_Ψ₂Sq (by rwa [ΨSq_two] at hx))
  · rw [show (2 : ℤ) - 1 = 1 from rfl, ΨSq_one, eval_one]
    exact one_ne_zero


-- @@ L767-781 verbatim
/-- **The pointwise reduction at `n = 3`.**  The adjacent product is `ΨSq₄ · ΨSq₂
= preΨ₄² · Ψ₂Sq · Ψ₂Sq`, so the hypotheses are `isCoprime_preΨ₄_Ψ₃` and `isCoprime_Ψ₃_Ψ₂Sq` at the
root — again the two inputs of the `IsCoprime` example above, and of the hand proof of
`isCoprime_Φ_three_ΨSq_three` before it. -/
example (x : R) (hx : (W.ΨSq 3).eval x = 0) : (W.Φ 3).eval x ≠ 0 := by
  have h3 : W.Ψ₃.eval x = 0 := by
    refine pow_eq_zero_iff two_ne_zero |>.mp ?_
    rw [← eval_pow, ← ΨSq_three]
    exact hx
  refine eval_Φ_ne_zero_of_eval_ΨSq_ne_zero hx ?_ ?_
  · rw [show (3 : ℤ) + 1 = 4 from rfl, ΨSq_four, eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero _ (eval_ne_zero_of_isCoprime W.isCoprime_preΨ₄_Ψ₃ h3))
      (eval_ne_zero_of_isCoprime W.isCoprime_Ψ₃_Ψ₂Sq.symm h3)
  · rw [show (3 : ℤ) - 1 = 2 from rfl, ΨSq_two]
    exact eval_ne_zero_of_isCoprime W.isCoprime_Ψ₃_Ψ₂Sq.symm h3


-- @@ L783-783 verbatim
end Domain


-- @@ L785-785 verbatim
end IsElliptic


-- @@ L787-787 verbatim
end WeierstrassCurve
