/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DivisionPolynomialEval


-- @@ L8-98 verbatim
/-!
# The `y`-coordinate division-polynomial numerators `Ωₙ` and their factorisation

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` develops the
`x`-coordinate division polynomials (`ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, ΨSq, Ψ, Φ, ψ, φ`) but explicitly leaves
the *`y`-coordinate* division polynomials `ωₙ` as a `TODO`. The downstream files
`EllipticCurves/Torsion/OmegaTwo.lean` and `EllipticCurves/Torsion/OmegaThree.lean` supply the
*point-evaluated* on-curve identity for the duplication (`n = 2`) and tripling (`n = 3`) maps.

This file builds the **general-`n` substrate** those low-index files use implicitly, in a form
reusable by the multiplication-by-`n` function-field pullback `[n]∗ : F(W) → F(W)`.

The `y`-coordinate of `[n]P` is governed by the bracket appearing in the index-doubling formula
`ψ₂ₙ = ψₙ · (ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²) / ψ₂` (Silverman AEC, Exercise 3.7). We name

* `WeierstrassCurve.preΩ n`, the **univariate** numerator
  `preΩₙ = preΨₙ₊₂·preΨₙ₋₁² − preΨₙ₋₂·preΨₙ₊₁² ∈ R[X]`, and
* `WeierstrassCurve.Ω n`, the **bivariate** numerator
  `Ωₙ = ψₙ₊₂·ψₙ₋₁² − ψₙ₋₂·ψₙ₊₁² ∈ R[X][Y]`,

and establish:

* `preΨ_five` : the closed form `preΨ₅ = preΨ₄·Ψ₂Sq² − Ψ₃³`, from the odd `preΨ'` recurrence.
* `preΨ₄_sq` : the univariate identity `preΨ₄² = 4Φ₂³ + b₂Φ₂²Ψ₂Sq + 2b₄Φ₂Ψ₂Sq² + b₆Ψ₂Sq³` relating
  `preΨ₄`, `Φ₂` and `Ψ₂Sq`.
* `preΩ_two`/`preΩ_three` : `preΩ₂ = preΨ₄` and `preΩ₃ = preΨ₅ − preΨ₄²`, reconciling with the exact
  univariate factors `Kᵥ` used in `OmegaTwo`/`OmegaThree` (validating the general definition against
  the two independently-proved low-index cases).
* `preΩ_neg` : `preΩ` is an even function of the index.
* `map_preΩ` : `preΩ` commutes with base change, the `preΩ` member of Mathlib's
  `map_preΨ` / `map_ΨSq` / `map_Φ` family.
* `ψ_mul_Ω` : the index-doubling bridge `ψ₂ₙ · ψ₂ = ψₙ · Ωₙ`, a repackaging of Mathlib's `ψ_even`.
* `Ω_factor` : the parity factorisation, at the level of the honest bivariate polynomials `Ψ`,
  `Ψₙ₊₂·Ψₙ₋₁² − Ψₙ₋₂·Ψₙ₊₁² = (if Even n then ψ₂ else ψ₂²)·C(preΩₙ)`, exhibiting the bivariate
  numerator as a power of `ψ₂` times the univariate `preΩₙ` — the parity split that makes the
  `y`-coordinate of `[n]P` computable from univariate data.
* `preΨ_two_mul` : the same index doubling **univariately and with no hypotheses**,
  `preΨ₂ₙ = preΨₙ·preΩₙ`, which is Mathlib's `preΨ_even` with the common `preΨₙ` pulled out.
* `ΨSq_two_mul` : its squared form `ΨSq₂ₙ = ΨSqₙ·(preΩₙ²·(if Even n then 1 else Ψ₂Sq))`, whose
  parity factor is the one in `EllipticCurves.Torsion.OmegaOnCurve`'s `HasPreΩSq` — this is the
  lemma that removes `preΩ` from that predicate.
* `Affine.ψ_two_mul_evalEval` : the two preceding lemmas combined and the common factor of `ψ₂`
  cancelled, at a point `(x, y)` of `W` where `ψ₂` does not vanish:
  `ψ₂ₙ(x, y) = ψₙ(x, y)·(if Even n then 1 else ψ₂(x, y))·preΩₙ(x)`.  Equivalently
  `(if Even n then 1 else ψ₂)·preΩₙ = ψ₂ₙ/ψₙ`, which is the quantity Silverman's `ωₙ` is built
  from, and it is what identifies the parity factor of
  `EllipticCurves.Torsion.OmegaOnCurve`'s `HasPreΩSq` as this factorisation rather than a bare
  degree count.  ⚠️ Pointwise only, and the restriction is a property of the **bivariate** pair:
  `Ω_factor` is about `Ψ` and `Ω` is defined from `ψ`, and the two agree only after evaluation at a
  point of `W`.  Univariately there is no such restriction — that is `preΨ_two_mul` above.
* `Affine.ψ_four_evalEval` : the `n = 2` specialisation, landing on Mathlib's `ψ_four`; a
  non-vacuity check on the general statement rather than new content.

`preΨ_five` and `preΨ₄_sq` are pure `CommRing` statements about `preΨ` — no point, no field, no
characteristic hypothesis — and they feed the `n = 2` and `n = 3` instances of the general-`n`
on-curve engine in `EllipticCurves.Torsion.OmegaOnCurve`, which is why they live here rather than
in the point-level files that used to hold them.

The remaining crux for the full general-`n` on-curve identity `W.Equation (Φₙ/ΨSqₙ) (ωₙ/ψₙ³)` is the
**univariate** identity `WeierstrassCurve.HasPreΩSq` of `EllipticCurves.Torsion.OmegaOnCurve` — the
`ΨSqₙ`-weighted, parity-corrected analogue of `preΨ₄_sq` at general `n`, established there for
`n ∈ {0, ±1, ±2}`, and at `n = 3` in the evaluated form `HasPreΩSqAt` there and in the polynomial
form in `EllipticCurves.Torsion.OmegaCharZero`. It is the *only*
index-dependent input: the uniform half `WeierstrassCurve.Affine.equation_of_hasPreΩSqAt` derives
the Weierstrass equation at the division-polynomial coordinates from it alone, over any field of
characteristic `≠ 2` at a point with `ψₙ(x, y) ≠ 0`. This file supplies the numerator infrastructure
both consume.

⚠️ `ΨSq_two_mul` above is what lets that crux be restated **without `preΩ`**, as
`WeierstrassCurve.HasΨSqDoubling` in `EllipticCurves.Torsion.OmegaOnCurve`; the two are equivalent
and neither is easier. So `preΩ` is the vocabulary the crux was *first written in*, not a
constituent of it — which is worth knowing before extending this file with further `preΩ` lemmas
aimed at the crux.

⚠️ Identifying `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with the group-law multiple `n • P` is a **separate** statement
(`#251`), not an equivalent of the above and not a gate on it — `equation_of_hasPreΩSqAt` takes no
group-law input. `EllipticCurves.Torsion.DoublingCoords` and `EllipticCurves.Torsion.TriplingCoords`
supply it at `n = 2` and `n = 3`. The `OmegaTwo`/`OmegaThree` docstrings make the same disclaimer,
`OmegaTwo` calling the `2 • P` identification "a separate, harder statement not proved here" and
`OmegaThree` calling the `3 • P` one "a separate statement" that `TriplingCoords` does prove.
⚠️ That separate statement is now available at **every** index and not only at `2` and `3`:
`WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, `#1500`), whose `x`-half is
`hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`, `#251`) — each at every
index over a field with `(2 : F) ≠ 0`, and the `y`-half under `ΨSqₙ(x) ≠ 0` besides.  Both are
downstream of this file and neither is consumed here.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/


-- @@ L100-100 verbatim
open Polynomial

-- @@ L101-101 verbatim
open scoped Polynomial.Bivariate


-- @@ L103-104 verbatim
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])


-- @@ L106-106 verbatim
namespace WeierstrassCurve


-- @@ L108-108 verbatim
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


-- @@ L110-115 verbatim
/-- The closed form of the auxiliary `5`-division polynomial `preΨ₅ = preΨ₄·Ψ₂Sq² − Ψ₃³`, obtained
from the odd recurrence for `preΨ'`. -/
lemma preΨ_five : W.preΨ 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  have H := W.preΨ'_odd 0
  norm_num [preΨ'_four, preΨ'_two, preΨ'_one, preΨ'_three] at H
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, preΨ_ofNat]; exact H


-- @@ L117-126 expanded
/-- The key univariate division-polynomial identity underlying the duplication formula: the square
of `preΨ₄` is the cubic in `Φ₂` and `Ψ₂Sq` with the `bᵢ` as coefficients. Equivalently, this is the
statement that `(Φ₂/Ψ₂Sq, preΨ₄/(2 ψ₂³))` — up to the linear correction absorbed into `ω₂` — solves
the Weierstrass equation after clearing the `ψ₂²`-denominators. -/
lemma preΨ₄_sq :
    W.preΨ₄ ^ 2 =
      4 * W.Φ 2 ^ 3 + C W.b₂ * W.Φ 2 ^ 2 * W.Ψ₂Sq + 2 * C W.b₄ * W.Φ 2 * W.Ψ₂Sq ^ 2 +
        C W.b₆ * W.Ψ₂Sq ^ 3 :=
  by
  rw [Φ_two, preΨ₄, Ψ₂Sq, b₂, b₄, b₆, b₈]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  ring1


-- @@ L128-132 verbatim
/-- The **univariate** `y`-coordinate division-polynomial numerator
`preΩₙ = preΨₙ₊₂·preΨₙ₋₁² − preΨₙ₋₂·preΨₙ₊₁² ∈ R[X]`. It is the univariate factor of the bracket in
the index-doubling formula `ψ₂ₙ = ψₙ·(ψₙ₊₂ψₙ₋₁² − ψₙ₋₂ψₙ₊₁²)/ψ₂` (see `Ω_factor`). -/
noncomputable def preΩ (n : ℤ) : R[X] :=
  W.preΨ (n + 2) * W.preΨ (n - 1) ^ 2 - W.preΨ (n - 2) * W.preΨ (n + 1) ^ 2


-- @@ L134-137 verbatim
/-- The **bivariate** `y`-coordinate division-polynomial numerator
`Ωₙ = ψₙ₊₂·ψₙ₋₁² − ψₙ₋₂·ψₙ₊₁² ∈ R[X][Y]`, i.e. `ψₙ · Ωₙ = ψ₂ₙ · ψ₂` (see `ψ_mul_Ω`). -/
noncomputable def Ω (n : ℤ) : R[X][Y] :=
  W.ψ (n + 2) * W.ψ (n - 1) ^ 2 - W.ψ (n - 2) * W.ψ (n + 1) ^ 2


-- @@ L139-146 verbatim
/-- `preΩ₂ = preΨ₄`: the univariate `y`-numerator at `n = 2` is exactly the factor `preΨ₄` used in
`OmegaTwo.doubling_equation`. -/
@[simp]
lemma preΩ_two : W.preΩ 2 = W.preΨ₄ := by
  rw [preΩ, show (2 : ℤ) + 2 = 4 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num,
    show (2 : ℤ) - 2 = 0 by norm_num, show (2 : ℤ) + 1 = 3 by norm_num, preΨ_four, preΨ_one,
    preΨ_zero]
  ring


-- @@ L148-155 verbatim
/-- `preΩ₃ = preΨ₅ − preΨ₄²`: the univariate `y`-numerator at `n = 3` is exactly the factor
`Kᵥ = preΨ₅ − preΨ₄²` used in `OmegaThree.tripling_equation`. -/
@[simp]
lemma preΩ_three : W.preΩ 3 = W.preΨ 5 - W.preΨ₄ ^ 2 := by
  rw [preΩ, show (3 : ℤ) + 2 = 5 by norm_num, show (3 : ℤ) - 1 = 2 by norm_num,
    show (3 : ℤ) - 2 = 1 by norm_num, show (3 : ℤ) + 1 = 4 by norm_num, preΨ_two, preΨ_one,
    preΨ_four]
  ring


-- @@ L157-163 verbatim
/-- `preΩ` is an even function of the index: `preΩ₋ₙ = preΩₙ`. -/
@[simp]
lemma preΩ_neg (n : ℤ) : W.preΩ (-n) = W.preΩ n := by
  rw [preΩ, preΩ, show -n + 2 = -(n - 2) by ring, show -n - 1 = -(n + 1) by ring,
    show -n - 2 = -(n + 2) by ring, show -n + 1 = -(n - 1) by ring, preΨ_neg, preΨ_neg, preΨ_neg,
    preΨ_neg]
  ring


-- @@ L165-171 verbatim
/-- **`preΩ` commutes with base change**: `(W.map f).preΩ n = (W.preΩ n).map f`.  This is the
`preΩ` member of Mathlib's `map_preΨ` / `map_ΨSq` / `map_Φ` family, and it is what lets a
statement about `preΩ` be proved once over the universal curve and specialised — see
`EllipticCurves.Torsion.OmegaUniversal`. -/
lemma map_preΩ {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (W.map f).preΩ n = (W.preΩ n).map f := by
  simp only [preΩ, map_preΨ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]


-- @@ L173-177 verbatim
/-- **The index-doubling bridge.** `ψ₂ₙ · ψ₂ = ψₙ · Ωₙ`, a repackaging of Mathlib's `ψ_even` with
the bivariate `y`-numerator `Ωₙ` factored out. -/
lemma ψ_mul_Ω (n : ℤ) : W.ψ (2 * n) * W.ψ₂ = W.ψ n * W.Ω n := by
  rw [Ω]
  linear_combination W.ψ_even n


-- @@ L179-201 verbatim
/-- **The parity factorisation of the bivariate `y`-numerator.** At the level of the honest
bivariate polynomials `Ψ`,
`Ψₙ₊₂·Ψₙ₋₁² − Ψₙ₋₂·Ψₙ₊₁² = (if Even n then ψ₂ else ψ₂²)·C(preΩₙ)`. Since `Ψₙ` carries a factor of
`ψ₂` exactly for even `n`, the bivariate numerator is `ψ₂` (for even `n`) or `ψ₂²` (for odd `n`)
times the univariate `preΩₙ`. -/
lemma Ω_factor (n : ℤ) :
    W.Ψ (n + 2) * W.Ψ (n - 1) ^ 2 - W.Ψ (n - 2) * W.Ψ (n + 1) ^ 2 =
      (if Even n then W.ψ₂ else W.ψ₂ ^ 2) * C (W.preΩ n) := by
  simp only [WeierstrassCurve.Ψ, preΩ, C_sub, C_mul, C_pow]
  rcases Int.even_or_odd n with hn | hn
  · have h2 : Even (n + 2) := hn.add even_two
    have h2' : Even (n - 2) := hn.sub even_two
    have h1 : ¬Even (n - 1) := by simp [parity_simps, hn]
    have h1' : ¬Even (n + 1) := by simp [parity_simps, hn]
    rw [if_pos hn, if_pos h2, if_pos h2', if_neg h1, if_neg h1']
    ring
  · have hne : ¬Even n := by simp [parity_simps, hn]
    have h2 : ¬Even (n + 2) := by simp [parity_simps, hn]
    have h2' : ¬Even (n - 2) := by simp [parity_simps, hn]
    have h1 : Even (n - 1) := by simp [parity_simps, hn]
    have h1' : Even (n + 1) := by simp [parity_simps, hn]
    rw [if_neg hne, if_neg h2, if_neg h2', if_pos h1, if_pos h1']
    ring


-- @@ L203-220 verbatim
/-- **The index-doubling bridge, at the univariate level and with no hypotheses at all**:
`preΨ₂ₙ = preΨₙ · preΩₙ`.

This is Mathlib's `preΨ_even` with the common factor of `preΨₙ` pulled out, and the bracket that
remains is `preΩₙ` on the nose.  ⚠️ It is the univariate counterpart of `ψ_mul_Ω`, but it is
**strictly stronger in shape than that lemma is**: `ψ_mul_Ω` carries a spurious factor of `ψ₂` on
each side, which `Affine.ψ_two_mul_evalEval` below can only cancel at a point where `ψ₂` does not
vanish, and only after `ψ_evalEval` has reconciled `ψ` with `Ψ`.  Here there is nothing to cancel
and nothing to reconcile: `preΨ` and `preΩ` are both univariate, the identity is an equation in
`R[X]` over an arbitrary `CommRing`, and it holds at the `2`-torsion points too.

⚠️ `Affine.ψ_two_mul_evalEval`'s docstring says that it is *"a pointwise statement and there is no
polynomial-level version"*.  That remark is about the **bivariate** pair `Ψ`/`Ω` — `Ω_factor` is
stated for `Ψ` while `Ω` is defined from `ψ`, and those agree only on the curve.  It is not a claim
that index doubling has no polynomial-level form, and this lemma is that form. -/
lemma preΨ_two_mul (n : ℤ) : W.preΨ (2 * n) = W.preΨ n * W.preΩ n := by
  rw [preΨ_even, preΩ]
  ring


-- @@ L222-240 verbatim
/-- **Index doubling for the squared division polynomial**:
`ΨSq₂ₙ = ΨSqₙ · (preΩₙ² · (if Even n then 1 else Ψ₂Sq))`.

The parity factor on the right is exactly the one in `EllipticCurves.Torsion.OmegaOnCurve`'s
`WeierstrassCurve.HasPreΩSq`, and that is not a coincidence: this lemma is what turns that
predicate into a statement with no `preΩ` in it — see
`WeierstrassCurve.hasPreΩSq_iff_hasΨSqDoubling` there.

⚠️ The two branches meet: `ΨSqₙ` carries `Ψ₂Sq` exactly when `n` is even and the parity factor
carries it exactly when `n` is odd, so the product carries it in both cases, which is what makes
the left-hand side — with `2n` always even — come out uniformly. -/
lemma ΨSq_two_mul (n : ℤ) :
    W.ΨSq (2 * n) = W.ΨSq n * (W.preΩ n ^ 2 * if Even n then 1 else W.Ψ₂Sq) := by
  rw [ΨSq, ΨSq, preΨ_two_mul, if_pos (even_two_mul n)]
  rcases Int.even_or_odd n with hn | hn
  · simp only [if_pos hn]
    ring
  · simp only [if_neg (Int.not_even_iff_odd.mpr hn)]
    ring


-- @@ L242-242 verbatim
namespace Affine


-- @@ L244-244 verbatim
variable {F : Type*} [Field F] {W : Affine F} {x y : F}


-- @@ L246-292 verbatim
/-- **The index-doubling formula at a point, with the parity factor made explicit.**  For a point
`(x, y)` of `W` at which `ψ₂` does not vanish,

```
ψ₂ₙ(x, y) = ψₙ(x, y) · (if Even n then 1 else ψ₂(x, y)) · preΩₙ(x).
```

This is `ψ_mul_Ω` (`ψ₂ₙ·ψ₂ = ψₙ·Ωₙ`) combined with `Ω_factor` (`Ωₙ = ψ₂^(1 or 2)·preΩₙ` after
`ψ_evalEval`), with the one common factor of `ψ₂` cancelled.  Equivalently
`(if Even n then 1 else ψ₂)·preΩₙ = ψ₂ₙ/ψₙ`, which is the quantity Silverman's `ωₙ` is built from:
`2ωₙ = ψ₂ₙ/ψₙ − ψₙ·(a₁Φₙ + a₃ΨSqₙ)` (AEC, Exercise 3.7).

⚠️ **`hψ₂` is not decoration.**  The proof cancels a common factor of `ψ₂` at the point, and
`ψ₂(x, y) = 2y + a₁x + a₃` vanishes exactly at the `2`-torsion points of `W`; there the identity
carries no information, since `ψ_mul_Ω` reads `0 = ψₙ·Ωₙ` after evaluation.

⚠️ This is a **pointwise** statement and there is no polynomial-level version *of it*: `Ω_factor`
is stated for the honest bivariate `Ψ`, while `Ω` is defined from `ψ`, and `ψₙ` is only *congruent*
to `Ψₙ` modulo `W.polynomial`.  They agree only after evaluation at a point of `W`, via
`ψ_evalEval`, which is what `h` supplies.

⚠️ **That restriction is a fact about the bivariate polynomials, not about index doubling.**  The
univariate identity `preΨ_two_mul`, `preΨ₂ₙ = preΨₙ·preΩₙ`, holds in `R[X]` over an arbitrary
`CommRing` with no point, no `Equation` and no `ψ₂ ≠ 0` — including at the `2`-torsion points where
this lemma carries no information.  Read the sentence above as *"`ψ` and `Ψ` do not agree off the
curve"*, not as *"index doubling is available only pointwise"*. -/
lemma ψ_two_mul_evalEval (h : W.Equation x y) (hψ₂ : (W.ψ 2).evalEval x y ≠ 0) (n : ℤ) :
    (W.ψ (2 * n)).evalEval x y =
      (W.ψ n).evalEval x y * (if Even n then 1 else (W.ψ 2).evalEval x y) *
        (W.preΩ n).eval x := by
  have hΩ : (W.Ω n).evalEval x y =
      (if Even n then (W.ψ 2).evalEval x y else (W.ψ 2).evalEval x y ^ 2) *
        (W.preΩ n).eval x := by
    have hf := congrArg (Polynomial.evalEval x y) (W.Ω_factor n)
    simp only [WeierstrassCurve.Ω, evalEval, eval_mul, eval_sub, eval_pow, apply_ite,
      ψ_evalEval h, ψ_two, evalEval_C] at hf ⊢
    convert hf using 2
  have hbridge := congrArg (Polynomial.evalEval x y) (W.ψ_mul_Ω n)
  rw [← ψ_two] at hbridge
  simp only [evalEval, eval_mul] at hbridge
  refine mul_right_cancel₀ hψ₂ ?_
  simp only [evalEval] at hΩ ⊢
  rw [hbridge, hΩ]
  rcases Int.even_or_odd n with hn | hn
  · rw [if_pos hn, if_pos hn]; ring
  · have hne : ¬Even n := Int.not_even_iff_odd.mpr hn
    rw [if_neg hne, if_neg hne]; ring


-- @@ L294-306 verbatim
/-- **Non-vacuity at `n = 2`: the general index-doubling formula lands on Mathlib's `ψ_four`.**
Specialising `ψ_two_mul_evalEval` at `n = 2` uses `preΩ₂ = preΨ₄` and the even branch of the parity
factor, and produces `ψ₄(x, y) = ψ₂(x, y)·preΨ₄(x)` — which is exactly Mathlib's
`ψ_four : ψ₄ = C preΨ₄ · ψ₂` evaluated at `(x, y)`.

⚠️ This is a **check on the general statement, not new content**: the same identity holds at every
`(x, y)` with no hypotheses at all, straight from `ψ_four`.  It is proved here through the engine
precisely so that a general statement which failed to specialise to the known `n = 2` factorisation
would break the build. -/
lemma ψ_four_evalEval (h : W.Equation x y) (hψ₂ : (W.ψ 2).evalEval x y ≠ 0) :
    (W.ψ 4).evalEval x y = (W.ψ 2).evalEval x y * W.preΨ₄.eval x := by
  have H := ψ_two_mul_evalEval h hψ₂ 2
  rwa [show (2 : ℤ) * 2 = 4 by norm_num, if_pos even_two, mul_one, preΩ_two] at H


-- @@ L308-308 verbatim
end Affine


-- @@ L310-310 verbatim
end WeierstrassCurve
