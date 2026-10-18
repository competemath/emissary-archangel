/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByNDegreeTower
import EllipticCurves.Torsion.NsmulOrder


-- @@ L9-114 verbatim
/-!
# `x(n • 𝒫) = Φₙ(x)/ΨSqₙ(x)` at the generic point, and the first of the three degree gates

`EllipticCurves.FunctionField.MulByNDegreeTower` reduces `[F(W) : [n]∗F(W)] = n²` at general `n` to
three gates, of which the first is

> `nMulRatFunc W n = ΦDivΨSq W n` — the `x`-coordinate of `n • 𝒫`, produced by the group law, is the
> *written-down* fraction `Φₙ/ΨSqₙ`.

This file discharges that gate at every index `n` with `((n : ℤ) : F) ≠ 0`, over any field of
characteristic `≠ 2`.  **The two remaining gates are `#1184`'s coprimality and `(n : F) ≠ 0`
itself.**  ⚠️ The two spellings in the sentence above are **both right and not interchangeable**:
gate 3 is `natDegree_ΨSq`'s hypothesis at `n : ℤ`, where `((n : ℤ) : F)` is a no-op cast, while a
theorem below indexed `n : ℕ` binds `((n : ℤ) : F) ≠ 0`, which there is a different term.
⚠️ **Not every theorem below is indexed `n : ℕ`**: `eval_ΨSq_genX_ne_zero` is `n : ℤ`, so its
`(n : F) ≠ 0` is right for the gate's own reason — and its subject is `ΨSq_ne_zero` besides.
`EllipticCurves.FunctionField.MulByNDegreeTower`'s gate list says so where the gates are named.

⚠️ **Both have since been settled, and neither here.**  `#1184`'s coprimality holds at every
`n : ℤ` for an elliptic curve over a field of characteristic `≠ 2`
(`WeierstrassCurve.Affine.isCoprime_ΨSq_adjacent`, `EllipticCurves.Torsion.CoprimeAdjacent`), and
`EllipticCurves.FunctionField.MulByNDegreeGeneral` composes it with the last theorem below to give
`[F(W) : [n]∗F(W)] = n²` with no unsupplied hypothesis.  ⚠️ Neither module is in this one's import
closure, and they sit differently: `MulByNDegreeGeneral` is **downstream** (it imports this file),
while `EllipticCurves.Torsion.CoprimeAdjacent` is **import-incomparable** with it — its only import
is `EllipticCurves.Torsion.TwoTorsionOrder`, and it reaches no `FunctionField` module at all.
Nothing below changed, and the hypothesis-carrying forms are still the right shape here.

## Where it comes from: one merged theorem, applied over the wrong field on purpose

`WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) is `HasXCoordFormula W n` at **every** index over **any**
field of characteristic `≠ 2`.  It is a statement about points of a curve over a field, and the
generic point `𝒫 = (genX W, genY W)` is a point of the curve `W ⁄ F(W)` over the field `F(W)`.  So
it applies there, with `F := F(W)` and `W := W.map (algebraMap F F(W))`, and no descent, no
specialisation and no function-field machinery is involved.

⚠️ **That is the whole content of the coordinate formula below.**  It is short because the work was
done at the level of points; what is new is only the observation that the generic point is a point.
The transcendence section below is a second, separate argument.

Its one hypothesis, `ΨSqₙ` not vanishing at `genX`, is `eval_ΨSq_genX_ne_zero` below: `genX` is
transcendental over `F` (`transcendental_genX`) and `ΨSqₙ` is a nonzero polynomial when
`(n : F) ≠ 0` (Mathlib's `ΨSq_ne_zero`), and a nonzero polynomial does not vanish at a
transcendental element.

## The transcendence hypothesis, discharged without an algebraic closure

`mulByNEndo n` exists only given `Transcendental F (n • 𝒫).xCoord`.  On `main` that is discharged
by `transcendental_xCoord_nsmul_of_isAlgClosed` (`EllipticCurves.FunctionField.MulByNTranscendence`)
under `[IsAlgClosed F]`, `(2 : F) ≠ 0` and `n ≠ 0`.  With the coordinate formula in hand the
dominance argument of `isAlgebraic_genX_of_two`
(`EllipticCurves.FunctionField.MulByTwoEndomorphism`) runs verbatim at general `n`:
`Φₙ` has degree `n²` with leading coefficient `1` while `natDegree ΨSqₙ ≤ n² − 1`, so
`Φₙ − t·ΨSqₙ` is a nonzero polynomial annihilating `genX` over the relative algebraic closure.

⚠️ The two readings are **incomparable, not nested**: both ask `(2 : F) ≠ 0`, and beyond that this
one asks `((n : ℤ) : F) ≠ 0` and no closure where the merged one asks a closure and only `n ≠ 0`.
Over an algebraically closed field of characteristic `p` with `p ∣ n`, the merged one applies and
this one does not.  Neither supersedes the other and the merged statement is untouched.

⚠️ **And one clause below does not name that transcendence**, under `README.md`'s derivability
exemption: `finrank_mulByNFieldRange_eq_sq` takes
`hT : Transcendental F (n • 𝒫).xCoord` as an ordinary argument, because the subfield whose degree is
measured depends on it, and `hT` follows from the two conditions its clause already names, by
`transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero` above.  That is the exemption's own
worked example, and `finrank_mulByNFieldRange_eq_sq_of_isCoprime_ΨSq_adjacent` below carries the
derivation out.  ⚠️ `(2 : F) ≠ 0` fails the same test — it is derivable from nothing any clause here
names, not from `((n : ℤ) : F) ≠ 0` and not from the coprimality — so it stays named, and every
headline below that makes a hypothesis-list claim carries it.

## ⚠️ What this file does *not* do

* **It does not prove `[F(W) : [n]∗F(W)] = n²` unconditionally.**  `#1184` —
  `IsCoprime (ΨSq (n+1) · ΨSq (n−1)) (ΨSqₙ)` at general `n` — is untouched *here*, and
  `finrank_mulByNFieldRange_eq_sq_of_isCoprime_ΨSq_adjacent` below carries it as a hypothesis.  What
  changes is that `#1184` and `((n : ℤ) : F) ≠ 0` are the **only** two hypotheses between this tree
  and the general-`n` degree; before, `#251` stood beside them.  ⚠️ The first of the two was
  discharged afterwards, in `EllipticCurves.Torsion.CoprimeAdjacent`, and the composition is
  `EllipticCurves.FunctionField.MulByNDegreeGeneral` — the latter downstream of this file, the
  former **import-incomparable** with it.
* **It says nothing about `#E[n] = n²`.**  The counting step — a separable isogeny has as many
  points in its kernel as its degree — is in this tree at no index, as
  `EllipticCurves.FunctionField.MulByTwoDegree`'s scope section records.  A field degree is not a
  point count.
* **It does not identify the two `[n]∗`s.**  `EllipticCurves.FunctionField.MulByNPullback`'s
  `mulByNEndo` is built from the group law, and `#405`'s *second*, division-polynomial `[n]∗` is not
  built here; what is proved is that the two constructions agree on `genX`, which is the `x`-half of
  that identification and the only half a degree count consumes.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.eval_ΨSq_genX_ne_zero` : `ΨSqₙ(genX) ≠ 0`.
* `WeierstrassCurve.Affine.CoordinateRing.xCoord_nsmul_genericPoint` : **the coordinate formula at
  the generic point**, `x(n • 𝒫) = Φₙ(genX)/ΨSqₙ(genX)`, with `(2 : F) ≠ 0`, at every index with
  `((n : ℤ) : F) ≠ 0`.
* `…CoordinateRing.transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero` : the transcendence
  hypothesis, with no algebraic closure.
* `WeierstrassCurve.Affine.CoordinateRing.nMulRatFunc_eq_ΦDivΨSq` : **gate 1**, discharged.
* `WeierstrassCurve.Affine.CoordinateRing.finrank_mulByNFieldRange_eq_sq_of_isCoprime_ΨSq_adjacent`:
  `[F(W) : [n]∗F(W)] = n²`, with `#1184` as its only remaining mathematical hypothesis.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.4.
-/


-- @@ L116-116 verbatim
open Polynomial Module


-- @@ L118-118 verbatim
namespace WeierstrassCurve.Affine


-- @@ L120-120 verbatim
namespace CoordinateRing


-- @@ L122-122 verbatim
variable {F : Type*} [Field F] {W : Affine F}


-- @@ L124-129 verbatim
/-- `(2 : F(W)) ≠ 0` from `(2 : F) ≠ 0`: the structure map of a field extension is injective. -/
private lemma two_ne_zero_functionField (h2 : (2 : F) ≠ 0) : (2 : W.FunctionField) ≠ 0 := by
  intro h
  refine h2 ((algebraMap F W.FunctionField).injective ?_)
  rw [map_ofNat, map_zero]
  exact h


-- @@ L131-142 verbatim
/-- **`ΨSqₙ` does not vanish at the generic `x`-coordinate.**

`genX W` is transcendental over `F` (`transcendental_genX`), so no nonzero polynomial over `F`
vanishes at it, and `ΨSqₙ` is nonzero exactly when `(n : F) ≠ 0` (Mathlib's `ΨSq_ne_zero`).

⚠️ This is the hypothesis of `HasXCoordFormula` read on the curve `W ⁄ F(W)`, which is why it is
stated for `(W.map (algebraMap F F(W))).ΨSq` rather than for `W.ΨSq`; the two differ by
`WeierstrassCurve.map_ΨSq`. -/
theorem eval_ΨSq_genX_ne_zero {n : ℤ} (hn : ((n : ℤ) : F) ≠ 0) :
    ((W.map (algebraMap F W.FunctionField)).ΨSq n).eval (genX W) ≠ 0 := by
  rw [WeierstrassCurve.map_ΨSq, eval_map, ← aeval_def]
  exact fun h => transcendental_genX ⟨W.ΨSq n, W.ΨSq_ne_zero hn, h⟩


-- @@ L144-144 verbatim
variable [W.IsElliptic]


-- @@ L146-158 verbatim
open Classical in
/-- **The coordinate formula at the generic point**, in the base-changed spelling that
`HasXCoordFormula` produces.  `xCoord_nsmul_genericPoint` below is the same statement with the
polynomials pulled back to `F[X]`. -/
theorem xCoord_nsmul_genericPoint' (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0) :
    (n • genericPoint (W := W)).xCoord
      = ((W.map (algebraMap F W.FunctionField)).Φ (n : ℤ)).eval (genX W)
        / ((W.map (algebraMap F W.FunctionField)).ΨSq (n : ℤ)).eval (genX W) := by
  obtain ⟨y', h', hP⟩ :=
    hasXCoordFormula_of_two_ne_zero (W := W.map (algebraMap F W.FunctionField))
      (two_ne_zero_functionField h2) n nonsingular_gen (eval_ΨSq_genX_ne_zero hn)
  rw [show (genericPoint (W := W)) = Point.some (genX W) (genY W) nonsingular_gen from rfl, hP,
    Point.xCoord_some]


-- @@ L160-171 verbatim
/-- **`x(n • 𝒫) = Φₙ(genX)/ΨSqₙ(genX)`**, at every index with `((n : ℤ) : F) ≠ 0`, over a field of
characteristic `≠ 2`.

This is `WeierstrassCurve.Affine.HasXCoordFormula` — merged at every index in
`EllipticCurves.Torsion.NsmulOrder` — applied to the curve `W ⁄ F(W)` at the point `𝒫`.  It is the
statement `EllipticCurves.FunctionField.MulByNXCoordRatFunc` calls *"the presentation
`nMulRatFunc W n` lacks"*, and gate 1 of `EllipticCurves.FunctionField.MulByNDegreeTower`. -/
theorem xCoord_nsmul_genericPoint (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0) :
    (n • genericPoint (W := W)).xCoord
      = aeval (genX W) (W.Φ (n : ℤ)) / aeval (genX W) (W.ΨSq (n : ℤ)) := by
  rw [xCoord_nsmul_genericPoint' h2 hn, WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq,
    eval_map, eval_map, ← aeval_def, ← aeval_def]


-- @@ L173-174 verbatim
/-- The relative algebraic closure of `F` in the function field `F(W)`. -/
local notation "K" => algebraicClosure F W.FunctionField


-- @@ L176-229 verbatim
/-- **`x(n • 𝒫)` is transcendental over `F`**, at every index with `((n : ℤ) : F) ≠ 0`, over a field
of characteristic `≠ 2` — with **no** algebraic closure of `F`.

The dominance argument of `isAlgebraic_genX_of_two`
(`EllipticCurves.FunctionField.MulByTwoEndomorphism`) at general `n`: if `u := x(n • 𝒫)` were
algebraic over `F` then `genX` would be a root of `q := Φₙ − u·ΨSqₙ` over the relative algebraic
closure `K`, and `q ≠ 0` because its coefficient in degree `n²` is `1` — Mathlib's `coeff_Φ` gives
`Φₙ` leading coefficient `1` there, and `natDegree_ΨSq_le` puts `ΨSqₙ` strictly below it.  That
contradicts `transcendental_genX`.

⚠️ `n ≠ 0` is what makes `n² − 1 < n²`, and it comes from `hn`; at `n = 0` the two degrees are both
`0` and the argument has nothing to say.

⚠️ **This does not supersede `transcendental_xCoord_nsmul_of_isAlgClosed`**
(`EllipticCurves.FunctionField.MulByNTranscendence`), and is not superseded by it: both ask
`(2 : F) ≠ 0`, and beyond that one asks `[IsAlgClosed F]` and `n ≠ 0` where this one asks
`((n : ℤ) : F) ≠ 0` and no closure.  Over an algebraically closed field of characteristic `p` with
`p ∣ n` only the merged one applies. -/
theorem transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0) : Transcendental F (n • genericPoint (W := W)).xCoord := by
  intro hu
  set φ := algebraMap F W.FunctionField with hφ
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hden : ((W.map φ).ΨSq (n : ℤ)).eval (genX W) ≠ 0 := eval_ΨSq_genX_ne_zero hn
  set u := (n • genericPoint (W := W)).xCoord with hu_def
  have hrel : u * ((W.map φ).ΨSq (n : ℤ)).eval (genX W)
      = ((W.map φ).Φ (n : ℤ)).eval (genX W) := by
    rw [hu_def, xCoord_nsmul_genericPoint' h2 hn]
    exact div_mul_cancel₀ _ hden
  set uK : K := ⟨u, mem_algebraicClosure_iff.mpr hu⟩ with huK
  set q : K[X] := (W.Φ (n : ℤ)).map (algebraMap F K)
    - C uK * (W.ΨSq (n : ℤ)).map (algebraMap F K) with hq
  have hjK : (algebraMap (↥K) W.FunctionField).comp (algebraMap F (↥K)) = φ := by
    rw [hφ, IsScalarTower.algebraMap_eq F (↥K) W.FunctionField]
  have hqmap : q.map (algebraMap (↥K) W.FunctionField)
      = (W.map φ).Φ (n : ℤ) - C u * (W.map φ).ΨSq (n : ℤ) := by
    rw [hq, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      Polynomial.map_map, hjK, ← WeierstrassCurve.map_Φ, ← WeierstrassCurve.map_ΨSq]
    congr 2
  have hlt : ((n : ℤ).natAbs ^ 2 - 1) < (n : ℤ).natAbs ^ 2 := by
    have : 1 ≤ (n : ℤ).natAbs ^ 2 := Nat.one_le_pow _ _ (by simpa using Nat.pos_of_ne_zero hn0)
    omega
  have hqne : q ≠ 0 := by
    intro h0
    have hcoeff : (q.map (algebraMap (↥K) W.FunctionField)).coeff ((n : ℤ).natAbs ^ 2) = 1 := by
      rw [hqmap, coeff_sub, coeff_C_mul, (W.map φ).coeff_Φ (n : ℤ),
        coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt ((W.map φ).natDegree_ΨSq_le (n : ℤ)) hlt),
        mul_zero, sub_zero]
    rw [h0, Polynomial.map_zero, coeff_zero] at hcoeff
    exact zero_ne_one hcoeff
  have hroot : (aeval (genX W)) q = 0 := by
    rw [aeval_def, ← eval_map, hqmap, eval_sub, eval_mul, eval_C, hrel, sub_self]
  exact transcendental_genX (IsAlgebraic.restrictScalars F ⟨q, hqne, hroot⟩)


-- @@ L231-231 verbatim
/-! ## Gate 1 of the degree tower -/


-- @@ L233-247 verbatim
open Classical in
/-- **Gate 1, discharged**: the rational function `nMulRatFunc W n` produced by the group law *is*
the written-down fraction `Φₙ/ΨSqₙ`, at every index with `((n : ℤ) : F) ≠ 0`, over a field of
characteristic `≠ 2`.

`EllipticCurves.FunctionField.MulByNXCoordRatFunc` states the two merged instances of this,
`nMulRatFunc_two` and `nMulRatFunc_three`, and records that no other index was available.  The
argument here is theirs: both sides have the same image in `F(W)` and `RatFunc F → F(W)` is
injective, with `xCoord_nsmul_genericPoint` supplying the image at general `n`. -/
theorem nMulRatFunc_eq_ΦDivΨSq (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0) :
    nMulRatFunc W n = ΦDivΨSq W (n : ℤ) := by
  refine (algebraMap (RatFunc F) W.FunctionField).injective ?_
  rw [algebraMap_nMulRatFunc, xCoord_nsmul_genericPoint h2 hn, ΦDivΨSq, map_div₀,
    algebraMap_ratFunc_algebraMap, algebraMap_ratFunc_algebraMap, aeval_genX_eq_algebraMap,
    aeval_genX_eq_algebraMap]


-- @@ L249-259 verbatim
/-- **`[F(W) : [n]∗F(W)] = n²`**, at every index with `((n : ℤ) : F) ≠ 0`, over a field of
characteristic `≠ 2`, given the coprimality of `Φₙ` and `ΨSqₙ`.

⚠️ The transcendence argument of `mulByNEndoAlgHom` is a *parameter of the statement*, because the
subfield whose degree is measured depends on it.  Any proof of it gives the same subfield; the
`hT`-free form below fixes one. -/
theorem finrank_mulByNFieldRange_eq_sq (h2 : (2 : F) ≠ 0) (n : ℕ)
    (hT : Transcendental F (n • genericPoint (W := W)).xCoord) (hn : ((n : ℤ) : F) ≠ 0)
    (hcop : IsCoprime (W.Φ (n : ℤ)) (W.ΨSq (n : ℤ))) :
    finrank ↥(mulByNEndoAlgHom n hT).fieldRange W.FunctionField = n ^ 2 :=
  finrank_mulByNFieldRange_of_nMulRatFunc_eq n hT hn hcop (nMulRatFunc_eq_ΦDivΨSq h2 hn)


-- @@ L261-283 verbatim
/-- **`[F(W) : [n]∗F(W)] = n²` with `#1184` as its only remaining mathematical hypothesis.**

`hadj` is exactly the statement `#1184` is: `IsCoprime (ΨSq_{n+1} · ΨSq_{n−1}) (ΨSqₙ)`.
`isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent` (`EllipticCurves.DivisionPolynomial.Coprime`) turns it
into the `Φ`/`ΨSq` coprimality the degree count consumes, and this file supplies everything else.

⚠️ Read this as *"two gates, not three"*: `((n : ℤ) : F) ≠ 0` and `#1184`, over a field of
characteristic `≠ 2` — which is `h2`, a binder of this statement rather than a fourth gate.  It is
**not** a proof that the degree is `n²`.  ⚠️ `hadj` is discharged at every `n : ℤ` by
`WeierstrassCurve.Affine.isCoprime_ΨSq_adjacent` (`EllipticCurves.Torsion.CoprimeAdjacent`, not in
this file's import closure), and
`EllipticCurves.FunctionField.MulByNDegreeGeneral.finrank_mulByNFieldRange_eq_sq_of_two_ne_zero`
is this theorem with it supplied; the hypothesis-carrying form is kept here because this file must
not import that one. -/
theorem finrank_mulByNFieldRange_eq_sq_of_isCoprime_ΨSq_adjacent (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : ((n : ℤ) : F) ≠ 0)
    (hadj : IsCoprime (W.ΨSq ((n : ℤ) + 1) * W.ΨSq ((n : ℤ) - 1)) (W.ΨSq (n : ℤ))) :
    finrank
      ↥(mulByNEndoAlgHom n
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero (W := W) h2 hn)).fieldRange
      W.FunctionField = n ^ 2 :=
  finrank_mulByNFieldRange_eq_sq (W := W) h2 n _ hn
    (isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent hadj)


-- @@ L285-292 verbatim
/-! ## ⚠️ Non-vacuity: the two indices at which the remaining gate is also discharged

The statements above have an unsupplied hypothesis and could in principle be vacuous.  They are
not: at `n = 2` and `n = 3` the merged coprimality certificates discharge it and the conclusion is
a number.  ⚠️ Since this file was written the hypothesis has also been discharged at **every**
index, in the **import-incomparable** `EllipticCurves.Torsion.CoprimeAdjacent`; the checks below
are kept because they are the ones available in this file's own import closure.
-/


-- @@ L294-294 verbatim
section Nonvacuity


-- @@ L296-306 verbatim
/-- **`[F(W) : [2]∗F(W)] = 4`**, through the general-`n` route, with the merged
`isCoprime_Φ_two_Ψ₂Sq` supplying gate 2.  ⚠️ This is not a new theorem —
`finrank_mulByTwoFieldRange` is merged — it is the check that the general statement evaluates. -/
example (h2 : (2 : F) ≠ 0) :
    finrank
      ↥(mulByNEndoAlgHom 2
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero (W := W) h2
          (by simpa using h2))).fieldRange
      W.FunctionField = 2 ^ 2 :=
  finrank_mulByNFieldRange_eq_sq (W := W) h2 2 _ (by simpa using h2)
    (by simpa [WeierstrassCurve.ΨSq_two] using W.isCoprime_Φ_two_Ψ₂Sq)


-- @@ L308-316 verbatim
/-- **`[F(W) : [3]∗F(W)] = 9`**, likewise, with `isCoprime_Φ_three_ΨSq_three`. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    finrank
      ↥(mulByNEndoAlgHom 3
        (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero (W := W) h2
          (by simpa using h3))).fieldRange
      W.FunctionField = 3 ^ 2 :=
  finrank_mulByNFieldRange_eq_sq (W := W) h2 3 _ (by simpa using h3)
    (by simpa using W.isCoprime_Φ_three_ΨSq_three)


-- @@ L318-325 verbatim
open Classical in
/-- **Gate 1 at `n = 5`**, the smallest index outside `{2, 3}` — the certificate that the general
statement is not a restatement of the two merged instances.

⚠️ `n = 5` has no coprimality certificate in this tree, so there is no `finrank` here: this is gate
1 alone, which is exactly the gate this file discharges. -/
example (h2 : (2 : F) ≠ 0) (h5 : (5 : F) ≠ 0) : nMulRatFunc W 5 = ΦDivΨSq W (5 : ℤ) :=
  nMulRatFunc_eq_ΦDivΨSq h2 (by simpa using h5)


-- @@ L327-327 verbatim
end Nonvacuity


-- @@ L329-329 verbatim
end CoordinateRing


-- @@ L331-331 verbatim
end Affine


-- @@ L333-333 verbatim
end WeierstrassCurve
