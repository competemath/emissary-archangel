/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.FunctionFieldBaseChangeN
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN
import EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange


-- @@ L12-166 verbatim
/-!
# The alternating property at general `n` over an arbitrary field: the halving point descends

Silverman *AEC* III.8.1(b).  `EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN` proves
`e_n(T, T) = 1` at an arbitrary `n` over an arbitrary field, but carrying **two** hypotheses: the
`#418` datum `hprin`, and a halving point `P` with `[n]P = T`.  This file removes the second at
**every `n ≠ 0`**, exactly as
`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange` removes it at `n = 2` and `n = 3`.
⚠️ It used to do so only at `3`-smooth `n`; the `_of_ne_zero` statements below are that restriction
lifted (`#1549` group 2), and the `3`-smooth forms are kept as independent routes.

`hprin` stays.  ⚠️ It is `#418`, it is an *existence* statement, and existence does not descend —
`WeilPairingAlternatingBaseChange`'s test, which this file does not weaken: **base change carries
conclusions down, not hypotheses up.**  The halving point is used to prove an *equality* in `F(W)`,
and equalities descend.

## What made this reachable, and what it cost

The `n = 2` descent (`translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_baseChange`) needs three
things pushed along `functionFieldMap`: the nonsingularity of `T`, the telescoping relation, and
the `n`-th root relation.  At general `n` two of those had no transporter:

* the `n`-th root relation mentions `[n]∗`, and `FunctionFieldBaseChange` had only
  `functionFieldMap_mulByTwoEndo` and `functionFieldMap_mulByThreeEndo`;
* the telescoping relation is indexed by `i • T` for `T : W.Point`, and
  `functionFieldMap_translateEndo` is indexed by an **affine pair** — the interior factor at
  `i ≡ 0` translates by the point at infinity, which that lemma cannot express.

Both are supplied by `EllipticCurves.FunctionField.FunctionFieldBaseChangeN`
(`functionFieldMap_mulByNEndo` and `functionFieldMap_translatePointEndo`).  ⚠️ The second was
*not* on anyone's list: `#1333` predicted the telescope row would "vanish entirely" because gate A
produces `htel` upstairs.  It does — and that is precisely why `htel` has to be carried *down*,
which needs the `W.Point`-indexed intertwiner.  Producing a datum upstairs does not remove the
need to transport it; it only changes which direction it travels.

## ⚠️ Where the `3`-smoothness entered, and what each half of it cost to remove

`hfac` was consumed in exactly one place: `exists_nsmul_eq_of_smooth`
(`EllipticCurves.Torsion.NsmulSmoothSurjective`), the halving point over `F̄`.  The transcendence
over `F̄` is `transcendental_xCoord_nsmul_of_isAlgClosed`, general in `n ≠ 0`.  So the first index
these statements did not reach was `n = 5` **for the halving point** — and a general-`n`
`[n]`-surjectivity on `E(F̄)` lifts them all to every `n` with nothing else changing.

⚠️ **That surjectivity was never missing, and swapping it in is measured now (`#1549` group 2): it
costs nothing.**  `nsmul_surjective_of_two_ne_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`) is
`[n]`-surjectivity on `E(F̄)` at every `n ≠ 0` with `(2 : F) ≠ 0`, under the same instances
`exists_nsmul_eq_of_smooth` was already being called with at this file's one call site — so
`…_of_baseChange_of_ne_zero` and `…_of_hprin_n_of_baseChange_of_ne_zero` below are the two
statements above with `hfac` deleted and **no index condition, no `h3` and no instance** put in its
place.  ⚠️ This paragraph used to say the substitution was *unmeasured*; that is what changed, and
the `#251` an older version of it blamed had already been closed.

⚠️ In `…_of_smooth` below the transcendence over `F` is discharged too, by
`transcendental_xCoord_nsmul_of_smooth`, and *that* one genuinely needs `3`-smoothness and `h3`.
So the two uses of `hfac` in that statement have different reasons, and they come off at **different
prices**: the halving point for free, the transcendence for `((n : ℤ) : F) ≠ 0` — which is exactly
what `exists_weilPairingElt_self_eq_one_of_ne_zero_of_baseChange` pays, and why that statement has
an index hypothesis while the two above it have none.

## Main statements

⚠️ **Every statement below takes `(2 : F) ≠ 0`, and every one but the last takes `n ≠ 0`** — the
last takes `((n : ℤ) : F) ≠ 0`, which gives it.  The two `translatePointEndo_…` forms take the
telescope `htel` and the `n`-th-power identity `hpow`; the four `exists_weilPairingElt_…` forms
take the nonsingular `n`-torsion `T` and `hprin`.  The non-constancy of `x([n]𝒫)` is a hypothesis
of both `translatePointEndo_…` forms and of the two whose names carry `_of_hprin_n`; the other two
discharge it, which is what their bullets say.

⚠️ **Where a bullet says nothing about hypotheses, read it against this register; where a bullet
counts them, the count is that bullet's own claim and no register makes it true.**  Naming some
without counting is neither, and sits under this register unchanged; reporting one *discharged* is a
gate-discharge claim, which `README.md` `### Gate-discharge claims` governs.  That is the house form
`#1647` decided (`EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN`, PR #658), and this
list is one of the reasons it had to be decided at all: it carries hypothesis counts of its own,
below.

⚠️ **It replaces a universal that this list had falsified before the universal was written.**
This register formerly closed *"The bullets give the conclusions and not the hypotheses"*
(`#1626`, PR #654), while the rows below saying *"are the whole hypothesis list"* had been on the
page since `#1611` (PR #641) and `#1619` (PR #643), and the ⚠️ block under them argues for them at
length.  ⚠️ **Those counts are not the defect and are untouched**: they are the form `README.md`
`### Module-block bullets` mandates, because *"A register says what a list omits.  It cannot make a
count true"* — so the universal is the sentence that had to go, and not the rows (`#1650`).

* `WeierstrassCurve.Affine.translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange` — gate B
  (`WeilPairingAlternatingWorkhorseN`) with its halving-point hypothesis **removed, not relocated**,
  over an arbitrary field at `3`-smooth `n`.
* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange` —
  `e_n(T, T) = 1` over an arbitrary field, so that `h2`, `n ≠ 0`, `3`-smoothness, the
  transcendence, the nonsingular `n`-torsion `T` and `hprin` are the whole hypothesis list;
  `hprin` is the only gate.
* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_smooth_of_baseChange` — the same
  with the transcendence discharged as well, so that `h2`, `h3`, `n ≠ 0`, `3`-smoothness, the
  nonsingular `n`-torsion `T` and `hprin` are the whole hypothesis list.
  ⚠️ **Both of those two lists used to stop at `hprin`, naming neither `n ≠ 0` nor `T`, and the
  `n ≠ 0` was not the same omission twice.**  In the first it *is* derivable from what the bullet
  names — the transcendence is unsatisfiable at `n = 0`, where `(0 • 𝒫).xCoord` is `0` and hence
  algebraic — so that row sat under `README.md`'s derivability exemption, whose price is that
  *"the derivation is cited once in the module block"*, and no citation had been written.
  ⚠️ In the second there is no exemption to use and the claim was **false**: `hfac` is *vacuously*
  true at `n = 0` (`Nat.primeFactors 0 = ∅`) and neither `h2` nor `h3` says anything about the
  index, so `n ≠ 0` followed from nothing the bullet named — while the statement consumes it, in
  `transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac`.  Naming the hypothesis in both is
  cheaper than citing a derivation in one, and it leaves the two rows making the same kind of claim
  in the same register.  ⚠️ `T` is named rather than left to *"the setting"* (`README.md`
  `### Gate-discharge claims`) because that register carries claims about **gates** and says in
  terms that it *"is not a licence to say the signature is short"*; and, more simply, because both
  rows make a **count** claim, which `README.md` `### Module-block bullets` puts beyond the reach
  of any register at all — *"A register says what a list omits.  It cannot make a count true."*
  So *"the setting"* was never available to these two, whatever it turns out to cover.
  ⚠️ **That ground is deliberately independent of whether `h` is a data argument** of
  `pointClosedPoint h.left` (`#1631`, since ruled: it is): the clearance is a licence to omit a
  binder, not a bar on naming one, so a count naming all seven explicit propositional binders is
  true under either answer.  ⚠️ `EllipticCurves.Torsion.WronskianSeparable` stands on the **same**
  ground, and gives it first: its block reads *"Every bullet above names the whole explicit
  hypothesis list of the declaration it is about"*, then *"And that includes `h : W.Equation x y`"*
  — so it is a count that names the binder there too (`#1620`, PR #647).  ⚠️ **What differs is the
  second ground each block adds, not the kind of row.**  That file adds *"bullet 3 makes no
  gate-discharge claim at all"*, and that one is **not** available here: the row above for
  `exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange` ends *"`hprin` is the only gate"*,
  so it makes exactly such a claim.  A ground therefore does not transfer between two blocks
  merely because their rows agree in kind — read every claim the row itself makes, and which
  register can reach each of them follows.
  ⚠️ The **declaration headlines** of both statements were already compliant — each names
  `3`-smooth `n ≠ 0` — and are untouched.  It was only this block that was short of them, which is
  the layer `#1614` was filed on.
* `WeierstrassCurve.Affine.translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange_of_ne_zero`
  and `…exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange_of_ne_zero` — the first two at
  **every** `n ≠ 0` (`#1549` group 2).  ⚠️ Despite the `_of_ne_zero` suffix,
  which marks the general layer on this front, neither takes `((n : ℤ) : F) ≠ 0`: they are the
  `3`-smooth forms with `hfac` deleted and nothing put in its place.
* `WeierstrassCurve.Affine.exists_weilPairingElt_self_eq_one_of_ne_zero_of_baseChange` — the third
  at every `n` with `(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0`.  ⚠️ This one **does** take an index
  hypothesis, because it also discharges the transcendence over `F`; `h3` and `hfac` are both gone.
  The `_of_smooth` form is a corollary of it, compiled in the `example` beside it.

`Recovery` derives the merged `exists_weilPairingElt_self_eq_one_of_hprin_two` and
`…_of_hprin_three` (`WeilPairingAlternatingBaseChange`) from the general form, verbatim.

## What is *not* here

* `hprin` (`#418`, `#962`).
* The `μ`-valued twins.  ⚠️ Deliberately: they are `#1334`'s re-scoped deliverable, together with
  the `μ` forms of the merged general-`n` assembly, and splitting them across two PRs would put two
  authors in the same three-line neighbourhood again.
* Nothing on the index axis.  ⚠️ This bullet used to read *"`n = 5` and beyond — the obstruction is
  the halving point"*; the halving point is `nsmul_surjective_of_two_ne_zero` now and `n = 5` is
  reached, by all three `_of_ne_zero` statements below.
* The divisor half of base change (`#692`).  Nothing here wants it: no statement below mentions
  `divisor` on the `F̄` side, and `hprin` is never transported.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(b).
-/


-- @@ L168-168 verbatim
open Polynomial IsDedekindDomain


-- @@ L170-170 verbatim
namespace WeierstrassCurve.Affine


-- @@ L172-172 verbatim
open CoordinateRing


-- @@ L174-174 verbatim
variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xT yT : F}


-- @@ L176-176 verbatim
local notation3 "K" => AlgebraicClosure F


-- @@ L178-178 verbatim
/-! ### Gate B without the halving point -/


-- @@ L180-222 verbatim
open Classical in
/-- **Translation by `T` fixes the `n`-th root, over an arbitrary field with `(2 : F) ≠ 0`.**

`translatePointEndo_eq_self_of_prod_eq_of_pow_eq` (`WeilPairingAlternatingWorkhorseN`) with the
halving hypothesis `[n]P = T` **removed** — not relocated — at every `3`-smooth `n ≠ 0`.

`htel` and `hpow` are equations in `F(W)`, so they push forward along `functionFieldMap`; over `F̄`
the halving point is `exists_nsmul_eq_of_smooth`; and the conclusion, being an equality, comes back
through `functionFieldMap_injective`.  ⚠️ `T` is an arbitrary `W.Point` and is **not** assumed
affine: `basePointMap` is additive, so `[i]T` transports as `[i]` of the transported `T` whether or
not either is at infinity. -/
theorem translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn0 : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {T : W.Point}
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, translatePointEndo (i • T) f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f) :
    translatePointEndo T g = g := by
  have h2' : (2 : K) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have hn' : Transcendental K
      (n • genericPoint (W := W.map (algebraMap F K))).xCoord :=
    transcendental_xCoord_nsmul_of_isAlgClosed h2' hn0
  have hgne : functionFieldMap W K g ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W K)).mpr hg
  obtain ⟨P, hP⟩ := exists_nsmul_eq_of_smooth h2' hn0 hfac (basePointMap W K T)
  have htel' : ∏ i ∈ Finset.range n,
      translatePointEndo (i • basePointMap W K T) (functionFieldMap W K f)
        = algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c) := by
    rw [← functionFieldMap_algebraMap_base, ← htel, map_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [functionFieldMap_translatePointEndo, map_nsmul]
  have hpow' : algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c₀)
      * functionFieldMap W K g ^ n = mulByNEndo n hn' (functionFieldMap W K f) := by
    rw [← functionFieldMap_algebraMap_base, ← map_pow, ← map_mul, hpow,
      functionFieldMap_mulByNEndo hn hn']
  have key : translatePointEndo (basePointMap W K T) (functionFieldMap W K g)
      = functionFieldMap W K g :=
    translatePointEndo_eq_self_of_prod_eq_of_pow_eq hn0 hn' hP hgne
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc)
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc₀) htel' hpow'
  refine functionFieldMap_injective W K ?_
  rw [functionFieldMap_translatePointEndo]
  exact key


-- @@ L224-224 verbatim
/-! ### The assembly over an arbitrary field -/


-- @@ L226-264 verbatim
open Classical in
/-- **`e_n(T, T) = 1` over an arbitrary field with `(2 : F) ≠ 0`, at every `3`-smooth `n ≠ 0` with a
non-constant `[n]∗` and every nonsingular `n`-torsion `T`**, with `hprin` (`#418`) the only gate.

`exists_weilPairingElt_self_eq_one_of_hprin_n` (`WeilPairingAlternatingAssemblyN`) is this statement
with the halving point `[n]P = T` added as a hypothesis **and `h2` and `hfac` dropped**: those two
are what the descent spends over `F̄` to produce the halving point it no longer takes, so the
explicit hypothesis lists are *not* otherwise identical.  The conclusions are.  The proof is that
one with gate B replaced by its descended form. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn0 : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ := exists_prod_translatePointEndo_eq_algebraMap h htors
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByNEndo n hn f ≠ 0 := fun hz =>
    hf ((mulByNEndo n hn).injective (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  have htinv : translateEndo h.left g = g := by
    have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange h2 hn0 hfac hn hg
      hc hc₀ htel hpow
    rwa [show Point.some xT yT h = torsionPoint h.left from rfl,
      translatePointEndo_torsionPoint] at key
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩


-- @@ L266-289 verbatim
open Classical in
/-- **`e_n(T, T) = 1` over an arbitrary field at every `3`-smooth `n ≠ 0` with `(2 : F) ≠ 0` and
`(3 : F) ≠ 0`**, taking the nonsingular `n`-torsion `T`, with `hprin` the only hypothesis that is
not about the characteristic.

The transcendence is discharged by `transcendental_xCoord_nsmul_of_smooth`, which is where `h3`
enters — the halving point needs neither `h3` nor, over `F̄`, the transcendence.  See the module
docstring for why `hfac` is doing two different jobs here. -/
theorem exists_weilPairingElt_self_eq_one_of_smooth_of_baseChange (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange h2 hn0 hfac _ h htors hprin



-- @@ L292-306 verbatim
/-! ### The same at every `n ≠ 0`

`hfac` is consumed in exactly one place in this file — `exists_nsmul_eq_of_smooth`, the halving
point over `F̄` — and `nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`) is the same conclusion under the same instances at
**every** `n ≠ 0` with `(2 : F) ≠ 0`.  The module docstring above recorded that substitution as
*"not measured"*.  It is measured now, and the answer is that it costs nothing: the two statements
below are the two above with `hfac` deleted and **no index condition put in its place**.

⚠️ The `[(W.map (algebraMap F K)).IsElliptic]` instance the surjectivity needs is the same one
`exists_nsmul_eq_of_smooth` was already using at this call site, so no instance is added either.

⚠️ Both `_of_smooth` routes are **kept**: `exists_nsmul_eq_of_smooth` halves by iterated `2`- and
`3`-descent and consumes no division polynomial, while `nsmul_surjective_of_two_ne_zero` runs
through the `ΨSq`-root dictionary.  The `example` below compiles the containment. -/


-- @@ L308-348 verbatim
open Classical in
/-- **Translation by `T` fixes the `n`-th root, over an arbitrary field with `(2 : F) ≠ 0`, at
every `n ≠ 0` with a non-constant `[n]∗`.**

`translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange` with `hfac` removed and nothing put
in its place.  The proof is that one with the halving point produced by
`nsmul_surjective_of_two_ne_zero` instead of `exists_nsmul_eq_of_smooth`; every other step is
unchanged, and in particular `hn` is still a hypothesis rather than a discharge — this statement is
about the descent, not about the transcendence. -/
theorem translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange_of_ne_zero
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {T : W.Point}
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, translatePointEndo (i • T) f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f) :
    translatePointEndo T g = g := by
  have h2' : (2 : K) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have hn' : Transcendental K
      (n • genericPoint (W := W.map (algebraMap F K))).xCoord :=
    transcendental_xCoord_nsmul_of_isAlgClosed h2' hn0
  have hgne : functionFieldMap W K g ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W K)).mpr hg
  obtain ⟨P, hP⟩ := nsmul_surjective_of_two_ne_zero h2' hn0 (basePointMap W K T)
  have htel' : ∏ i ∈ Finset.range n,
      translatePointEndo (i • basePointMap W K T) (functionFieldMap W K f)
        = algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c) := by
    rw [← functionFieldMap_algebraMap_base, ← htel, map_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [functionFieldMap_translatePointEndo, map_nsmul]
  have hpow' : algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c₀)
      * functionFieldMap W K g ^ n = mulByNEndo n hn' (functionFieldMap W K f) := by
    rw [← functionFieldMap_algebraMap_base, ← map_pow, ← map_mul, hpow,
      functionFieldMap_mulByNEndo hn hn']
  have key : translatePointEndo (basePointMap W K T) (functionFieldMap W K g)
      = functionFieldMap W K g :=
    translatePointEndo_eq_self_of_prod_eq_of_pow_eq hn0 hn' hP hgne
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc)
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc₀) htel' hpow'
  refine functionFieldMap_injective W K ?_
  rw [functionFieldMap_translatePointEndo]
  exact key


-- @@ L350-364 verbatim
open Classical in
/-- **`…_of_baseChange` is a corollary of `…_of_baseChange_of_ne_zero`** — its statement verbatim,
`hfac` binder and binder *name* included, proved from the general form.  ⚠️ `have _hfac := hfac` is
what lets the binder keep its name: `--wfail` rejects an explicit hypothesis that is never
referenced, and renaming it would break the verbatim restatement this `example` exists to make. -/
example (h2 : (2 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {T : W.Point}
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : ∏ i ∈ Finset.range n, translatePointEndo (i • T) f = algebraMap F W.FunctionField c)
    (hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f) :
    translatePointEndo T g = g :=
  have _hfac := hfac
  translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange_of_ne_zero h2 hn0 hn hg hc hc₀
    htel hpow


-- @@ L366-404 verbatim
open Classical in
/-- **`e_n(T, T) = 1` at every `n ≠ 0` with a non-constant `[n]∗`, over an arbitrary field with
`(2 : F) ≠ 0`, and at every nonsingular `n`-torsion `T`**, with `hprin` (`#418`) the only gate.

`exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange` with `hfac` removed and nothing put in
its place.  ⚠️ `hn` stays a hypothesis: over an *arbitrary* `F` the transcendence is not free, and
discharging it is what `exists_weilPairingElt_self_eq_one_of_ne_zero_of_baseChange` below does, at
the cost of `((n : ℤ) : F) ≠ 0`.  The halving point costs nothing, and that is the whole content of
this statement. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange_of_ne_zero (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn0 : n ≠ 0)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀ = divisor W (mulByNEndo n hn f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n = mulByNEndo n hn f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ := exists_prod_translatePointEndo_eq_algebraMap h htors
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByNEndo n hn f ≠ 0 := fun hz =>
    hf ((mulByNEndo n hn).injective (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hpow : algebraMap F W.FunctionField c₀ * g ^ n = mulByNEndo n hn f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  have htinv : translateEndo h.left g = g := by
    have key := translatePointEndo_eq_self_of_prod_eq_of_pow_eq_of_baseChange_of_ne_zero h2 hn0 hn
      hg hc hc₀ htel hpow
    rwa [show Point.some xT yT h = torsionPoint h.left from rfl,
      translatePointEndo_torsionPoint] at key
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩


-- @@ L406-439 verbatim
open Classical in
/-- **`e_n(T, T) = 1` over an arbitrary field at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`**, taking the nonsingular `n`-torsion `T`, with `hprin` the only hypothesis
that is not about the characteristic.

Both `3`-smooth inputs of `exists_weilPairingElt_self_eq_one_of_smooth_of_baseChange` are gone at
once, and they are gone for two different reasons — which is the distinction the module docstring
draws:

* the **transcendence over `F`**, by `transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero`
  (`EllipticCurves.FunctionField.MulByNXCoordFormula`).  ⚠️ This is what `hn` buys, and it is the
  only hypothesis this statement has that `…_of_hprin_n_of_baseChange_of_ne_zero` does not;
* the **halving point over `F̄`**, by `nsmul_surjective_of_two_ne_zero`, for free.

So `h3` is gone as well: it entered only through `transcendental_xCoord_nsmul_of_smooth`. -/
theorem exists_weilPairingElt_self_eq_one_of_ne_zero_of_baseChange (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hn : ((n : ℤ) : F) ≠ 0)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n
              (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n
                (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero h2 hn) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange_of_ne_zero h2
    (by rintro rfl; simp at hn) _ h htors hprin


-- @@ L441-472 verbatim
open Classical in
/-- **`…_of_smooth_of_baseChange` is a corollary of `…_of_ne_zero_of_baseChange`** — its statement
verbatim, `h3` and `hfac` binders included, proved from the general form.

`Nat.intCast_ne_zero_of_smooth` (`EllipticCurves.Torsion.ThreePrimary`) supplies
`((n : ℤ) : F) ≠ 0` from `3`-smoothness, and the two `mulByNEndo` terms carry different
transcendence proofs: they match by proof irrelevance, which is why the term-mode proof below
elaborates with no `simp only` bridging the two.

⚠️ This paragraph used to cite a lemma named *intCastBaseChange_ne_zero_of_smooth* — a `private`
copy this file never actually grew, because the shared form landed first, so the citation resolved
to nothing (`#1552`).  It also said *"the two `exact`s below"*, and there is one term.
⚠️ The retired name is deliberately **not** in backticks: backticks are how this development marks
a live citation, and every name-resolution check keys on them, so quoting a dead name in them
re-arms the very check that found this. -/
example (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0)
    (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : W.Nonsingular xT yT) (htors : Point.some xT yT h ∈ W.torsion n)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (n : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        n • divisor W g₀
          = divisor W (mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac) f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (n : ℤ)
          - Finsupp.single (none : ProjPoint W) (n : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ n
            = mulByNEndo n (transcendental_xCoord_nsmul_of_smooth h2 h3 hn0 hfac) f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_ne_zero_of_baseChange h2
    (Nat.intCast_ne_zero_of_smooth h2 h3 hn0 hfac) h htors hprin


-- @@ L474-479 verbatim
/-! ### Recovery of the merged `n = 2` and `n = 3` arbitrary-field assemblies

`#907`'s rule.  Both merged headlines of `WeilPairingAlternatingBaseChange` come back out of the
general form, verbatim, through `mulByNEndo_two` / `mulByNEndo_three`.  Each is `private`: a public
copy would duplicate a merged name.
-/


-- @@ L481-481 verbatim
section Recovery


-- @@ L483-483 verbatim
variable {x₂ y₂ x₃ y₃ : F}


-- @@ L485-491 verbatim
omit [W.IsElliptic] in
/-- `3`-smoothness at a prime index: the only prime factor of a prime `p` is `p` itself. -/
private lemma primeFactors_eq_two_or_three_of_prime {p : ℕ} (hp : p.Prime)
    (h : p = 2 ∨ p = 3) : ∀ q ∈ p.primeFactors, q = 2 ∨ q = 3 := fun q hq => by
  rw [Nat.mem_primeFactors] at hq
  rw [(Nat.prime_dvd_prime_iff_eq hq.1 hp).mp hq.2.1]
  exact h


-- @@ L493-512 verbatim
open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_hprin_two`
(`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`), recovered. -/
private theorem exists_weilPairingElt_self_eq_one_of_hprin_two_of_general (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange (n := 2) h2
    (by norm_num) (primeFactors_eq_two_or_three_of_prime Nat.prime_two (Or.inl rfl))
    (transcendental_xCoord_two_nsmul (W := W) h2) h htors
    (by simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_two h2, Nat.cast_ofNat] using key


-- @@ L514-533 verbatim
open Classical in
/-- `exists_weilPairingElt_self_eq_one_of_hprin_three`
(`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChange`), recovered. -/
private theorem exists_weilPairingElt_self_eq_one_of_hprin_three_of_general (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₃ y₃) (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f)) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
          translateEndo h.left g = g ∧ weilPairingElt h.left g = 1 := by
  have key := exists_weilPairingElt_self_eq_one_of_hprin_n_of_baseChange (n := 3) h2
    (by norm_num) (primeFactors_eq_two_or_three_of_prime Nat.prime_three (Or.inr rfl))
    (transcendental_xCoord_three_nsmul (W := W) h2 h3) h htors
    (by simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using hprin)
  simpa only [mulByNEndo_three h2 h3, Nat.cast_ofNat] using key


-- @@ L535-535 verbatim
end Recovery


-- @@ L537-580 verbatim
/-! ### Non-vacuity at `n = 6`, over a field that is not algebraically closed — and at `n = 10`

⚠️ `hprin` is `#418` and it stays bound below: nothing in the tree discharges it at `n = 6` or at
`n = 10` over `ℚ`, which is this certificate's setting.

⚠️ **RETIRED.**  This paragraph opened *"`hprin` is `#418` and cannot be discharged at any index, so
it stays bound below"* until `ecfb3e9` (2026-09-07, `#1843`, PR #723), and *at any index* is a
universal negative that was already false before `ecfb3e9` touched the file — so it is retired
rather than qualified, and what `ecfb3e9` adds is not what falsified it.  Three merged declarations
falsify it: `exists_gS_two_of_isAlgClosed` (`#791`) and `exists_gS_three_of_isAlgClosed` (`#825`)
discharge it over `F̄` at `n = 2` and `n = 3`, and `exists_gS_two_of_card`
(`EllipticCurves.FunctionField.PullbackPrincipalityTwoRationalTorsion`) discharges it at `n = 2`
over an arbitrary field with `(2 : F) ≠ 0` — `ℚ` included — from rational `2`-torsion and a halving.
What `ecfb3e9` adds is the general-index `F̄` form, `exists_gS_n_of_isAlgClosed`
(`EllipticCurves.FunctionField.PullbackPrincipalityN`), at every `n` with `(2 : F) ≠ 0` and
`((n : ℤ) : F) ≠ 0`.  ⚠️ **The replacement above is a statement about `n = 6` and `n = 10` over `ℚ`
and about nothing else**, because that is what this section certifies and every wider reading of the
old sentence is one of the three falsifications.  ⚠️ **Those four addresses read *this commit* until
they were re-keyed, and one of the four had already gone wrong** (`#1877`).  `README.md`'s
`### Gate-discharge claims` rules that an indexical address in a file is resolved by `git log -S` on
the words the clause is about, and that the per-line `git blame` a reader actually performs is
unsound.  `aadc404` (2026-09-07, `#1861`, PR #727) completed a reach clause in this block and
reflowed two of its lines, so the fourth copy came to sit on a line `aadc404` owns and blame
returned that commit for a sentence about the general-index form it does not add — what it adds is
`(2 : F) ≠ 0` in the `n = 2` clause above.  Whitespace-normalised, `git log -S` puts all four at
`ecfb3e9`; at `7c0460d`, the tree this re-key was measured against, blame agreed with it on three of
the four.  **Nothing retires**: the claim about what the paragraph read, and about the commit at
which it stopped reading it, is the same claim, and only its anchor changes.

What is certified is that **every other hypothesis of the `3`-smooth headline is simultaneously
satisfiable over `ℚ`** at an index no merged statement reaches: the elliptic instance,
`(2 : ℚ) ≠ 0`, `(3 : ℚ) ≠ 0`, `n ≠ 0`, `3`-smoothness, an affine nonsingular `T`, and
`T ∈ torsion 6`.  The halving point is not in that list because the theorem produces it — which is
the whole content of this file.

⚠️ `ℚ` is **not** algebraically closed (`rat_not_isAlgClosed'`), so neither the merged
`exists_weilPairingElt_self_eq_one_of_hprin_n_of_algClosed` nor `exists_nsmul_eq_of_smooth` applies
directly here.  That is what makes this a certificate for the descent rather than a restatement of
the algebraically closed corollary.

⚠️ The curve is `y² = x³ + 1`, **not** this subtree's default `y² = x³ − x`: on the default every
affine rational point is `2`-torsion, so there is no point of order `3` on it.  A certificate
resting on a false hypothesis proves nothing (`#916`), so `htors` is proved rather than assumed.
-/


-- @@ L582-582 verbatim
section Nonvacuity


-- @@ L584-593 verbatim
/-- **`ℚ` is not algebraically closed**, from `X² + X + 1` having no rational root.  Re-derived
because `WeilPairingAlternatingBaseChange`'s copy is `private`. -/
private lemma rat_not_isAlgClosed' : ¬ IsAlgClosed ℚ := by
  intro hcl
  obtain ⟨q, hq⟩ := hcl.exists_root (X ^ 2 + X + 1 : ℚ[X]) (by
    rw [show (X ^ 2 + X + 1 : ℚ[X]) = C 1 * X ^ 2 + C 1 * X + C 1 by simp,
      degree_quadratic one_ne_zero]
    exact two_ne_zero)
  rw [IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hq
  nlinarith [sq_nonneg (2 * q + 1)]


-- @@ L595-595 verbatim
private lemma exampleTwoNeZero : (2 : ℚ) ≠ 0 := by norm_num


-- @@ L597-597 verbatim
private lemma exampleThreeNeZero : (3 : ℚ) ≠ 0 := by norm_num


-- @@ L599-600 verbatim
/-! The certificate curve `y² = x³ + 1` is the shared `EllipticCurves.Fixture.y2EqX3AddOne`, whose
single `[CharZero F]` instance also supplies `IsElliptic` here. -/


-- @@ L602-602 verbatim
open EllipticCurves.Fixture


-- @@ L604-608 verbatim
/-- `T = (0, 1)` is a nonsingular point of `y² = x³ + 1`. -/
private lemma exampleNonsingularT : (y2EqX3AddOne ℚ).Nonsingular 0 1 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩ <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.negY]


-- @@ L610-621 verbatim
open Classical in
/-- `[2]T = −T`: the tangent at `(0, 1)` is horizontal, and doubling returns `(0, −1)`. -/
private lemma exampleDouble :
    Point.some (0 : ℚ) 1 exampleNonsingularT + Point.some (0 : ℚ) 1 exampleNonsingularT
      = -Point.some (0 : ℚ) 1 exampleNonsingularT := by
  have hy : (1 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 0 1 := by
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  rw [Point.add_self_of_Y_ne hy, Point.neg_some, Point.some.injEq]
  constructor <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.slope]


-- @@ L623-627 verbatim
open Classical in
/-- `T` has order `3`. -/
private lemma exampleThreeTorsion :
    ((3 : ℕ) • Point.some (0 : ℚ) 1 exampleNonsingularT : (y2EqX3AddOne ℚ).Point) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul, exampleDouble, neg_add_cancel]


-- @@ L629-633 verbatim
open Classical in
/-- Hence `T` is `6`-torsion, without having order `6`. -/
private lemma exampleSixTorsion :
    Point.some (0 : ℚ) 1 exampleNonsingularT ∈ (y2EqX3AddOne ℚ).torsion 6 := by
  rw [mem_torsion_iff, show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, exampleThreeTorsion, add_zero]


-- @@ L635-641 verbatim
/-- `6` is `3`-smooth. -/
private lemma exampleSmooth : ∀ p ∈ (6 : ℕ).primeFactors, p = 2 ∨ p = 3 := by
  intro p hp
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Finset.mem_union, Nat.Prime.primeFactors Nat.prime_two,
    Nat.Prime.primeFactors Nat.prime_three, Finset.mem_singleton, Finset.mem_singleton] at hp
  exact hp


-- @@ L643-671 verbatim
open Classical in
/-- **Every hypothesis but `hprin` is simultaneously satisfiable at `n = 6` over `ℚ`.**

⚠️ The `by convert exampleSixTorsion` is not decoration: `ℚ` has a genuine `DecidableEq` instance,
so `exampleSixTorsion`'s `torsion` is indexed by `instDecidableEqRat` while the headline — general
in `F` and elaborated `open Classical in` — is indexed by `Classical.propDecidable`.  `convert`
discharges the difference by `Subsingleton.elim`.  It does not arise in the merged blocks over
`AlgebraicClosure ℚ`, which has no decidable equality. -/
example
    (hprin : ∀ f : (y2EqX3AddOne ℚ).FunctionField, f ≠ 0 →
      divisor (y2EqX3AddOne ℚ) f
          = Finsupp.single (pointClosedPoint exampleNonsingularT.left) ((6 : ℕ) : ℤ) →
        ∃ g₀ : (y2EqX3AddOne ℚ).FunctionField, g₀ ≠ 0 ∧
          (6 : ℕ) • divisor (y2EqX3AddOne ℚ) g₀ = divisor (y2EqX3AddOne ℚ)
            (mulByNEndo 6 (transcendental_xCoord_nsmul_of_smooth exampleTwoNeZero
              exampleThreeNeZero (by norm_num) exampleSmooth) f)) :
    ∃ f : (y2EqX3AddOne ℚ).FunctionField, f ≠ 0 ∧
      divisorProj (y2EqX3AddOne ℚ) f
          = Finsupp.single (some (pointClosedPoint exampleNonsingularT.left)) ((6 : ℕ) : ℤ)
            - Finsupp.single (none : ProjPoint (y2EqX3AddOne ℚ)) ((6 : ℕ) : ℤ) ∧
        ∃ g : (y2EqX3AddOne ℚ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2EqX3AddOne ℚ).CoordinateRingˣ, (u : (y2EqX3AddOne ℚ).CoordinateRing) • g ^
              (6 : ℕ)
            = mulByNEndo 6 (transcendental_xCoord_nsmul_of_smooth exampleTwoNeZero
                exampleThreeNeZero (by norm_num) exampleSmooth) f) ∧
          translateEndo exampleNonsingularT.left g = g ∧
            weilPairingElt exampleNonsingularT.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_smooth_of_baseChange exampleTwoNeZero exampleThreeNeZero
    (by norm_num) exampleSmooth exampleNonsingularT (by convert exampleSixTorsion) hprin



-- @@ L674-684 verbatim
/-! #### And at `n = 10`, which no `_of_smooth` statement in this file can state

⚠️ **`n = 6` cannot falsify the general layer.**  `6 = 2 · 3` is `3`-smooth, so every certificate
above is equally a certificate for the `_of_smooth` headlines, and a *"general"* wrapper that
happened to be instantiable only at `{2, 3}`-indices would pass it.  `#1549`'s verification bar asks
for an index that is **even and not `3`-smooth**; `10 = 2 · 5` is the smallest.

The witness is the other rational point of small order on the same curve: `(−1, 0)` is `2`-torsion
on `y² = x³ + 1` (`y = negY y` forces `2y = 0`, and `x³ = −1` over `ℚ` forces `x = −1`), hence
`10`-torsion.  ⚠️ Write the factorisation as `10 = 2 * 5` and not `5 * 2`: `mul_nsmul` reads
`(m * n) • a = n • m • a`, so it is the *left* factor that gets applied first. -/


-- @@ L686-690 verbatim
/-- `(−1, 0)` is a nonsingular point of `y² = x³ + 1`. -/
private lemma exampleNonsingularNegOne : (y2EqX3AddOne ℚ).Nonsingular (-1) 0 := by
  rw [nonsingular_iff]
  refine ⟨?_, Or.inl ?_⟩ <;>
    norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.negY]


-- @@ L692-697 verbatim
open Classical in
/-- `(−1, 0)` is `2`-torsion: it is its own negative. -/
private lemma exampleTwoTorsionNegOne :
    Point.some (-1 : ℚ) 0 exampleNonsingularNegOne ∈ (y2EqX3AddOne ℚ).torsion 2 := by
  rw [mem_torsion_iff, two_nsmul, Point.add_self_of_Y_eq
    (by norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY])]


-- @@ L699-704 verbatim
open Classical in
/-- Hence `(−1, 0)` is `10`-torsion, and `10 = 2 · 5` is even and not `3`-smooth. -/
private lemma exampleTenTorsionNegOne :
    Point.some (-1 : ℚ) 0 exampleNonsingularNegOne ∈ (y2EqX3AddOne ℚ).torsion 10 := by
  rw [mem_torsion_iff, show (10 : ℕ) = 2 * 5 from rfl, mul_nsmul,
    mem_torsion_iff.mp exampleTwoTorsionNegOne, smul_zero]


-- @@ L706-735 verbatim
open Classical in
/-- **Every hypothesis but `hprin` is simultaneously satisfiable at `n = 10` over `ℚ`.**

The strongest non-vacuity statement in this file: `10` is even and not `3`-smooth
(`Nat.ten_not_smooth`), so **no `_of_smooth` statement in this file can state this at any
hypotheses**, and the general layer is therefore not a `{2, 3}`-parametrised statement in disguise.

⚠️ The base field is `ℚ`, which is not algebraically closed (`rat_not_isAlgClosed'`) — so this is
also evidence that the descent is doing work, not that `[IsAlgClosed F]` is silently in scope. -/
example
    (hprin : ∀ f : (y2EqX3AddOne ℚ).FunctionField, f ≠ 0 →
      divisor (y2EqX3AddOne ℚ) f
          = Finsupp.single (pointClosedPoint exampleNonsingularNegOne.left) ((10 : ℕ) : ℤ) →
        ∃ g₀ : (y2EqX3AddOne ℚ).FunctionField, g₀ ≠ 0 ∧
          (10 : ℕ) • divisor (y2EqX3AddOne ℚ) g₀ = divisor (y2EqX3AddOne ℚ)
            (mulByNEndo 10 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
              exampleTwoNeZero (by norm_num)) f)) :
    ∃ f : (y2EqX3AddOne ℚ).FunctionField, f ≠ 0 ∧
      divisorProj (y2EqX3AddOne ℚ) f
          = Finsupp.single (some (pointClosedPoint exampleNonsingularNegOne.left)) ((10 : ℕ) : ℤ)
            - Finsupp.single (none : ProjPoint (y2EqX3AddOne ℚ)) ((10 : ℕ) : ℤ) ∧
        ∃ g : (y2EqX3AddOne ℚ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2EqX3AddOne ℚ).CoordinateRingˣ, (u : (y2EqX3AddOne ℚ).CoordinateRing) • g ^
              (10 : ℕ)
            = mulByNEndo 10 (transcendental_xCoord_nsmul_genericPoint_of_intCast_ne_zero
                exampleTwoNeZero (by norm_num)) f) ∧
          translateEndo exampleNonsingularNegOne.left g = g ∧
            weilPairingElt exampleNonsingularNegOne.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_ne_zero_of_baseChange exampleTwoNeZero (by norm_num)
    exampleNonsingularNegOne (by convert exampleTenTorsionNegOne) hprin


-- @@ L737-737 verbatim
end Nonvacuity


-- @@ L739-739 verbatim
end WeierstrassCurve.Affine
