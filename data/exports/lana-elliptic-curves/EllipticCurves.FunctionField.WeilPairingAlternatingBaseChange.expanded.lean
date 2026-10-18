/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.FunctionFieldBaseChange
import EllipticCurves.FunctionField.WeilPairingAlternatingMu
import EllipticCurves.FunctionField.WeilPairingAlternatingThree
import EllipticCurves.FunctionField.WeilPairingAlternatingTwo


-- @@ L12-154 verbatim
/-!
# The alternating property over an arbitrary field: the halving point descends

Silverman *AEC* III.8.1(b): the Weil pairing is alternating, `e_n(T, T) = 1`.

`EllipticCurves.FunctionField.WeilPairingAlternating{Two,Three}` prove this over an **algebraically
closed** field, carrying `hprin` (`#418`) as their one gated hypothesis.  This file removes the
`[IsAlgClosed F]`, leaving `hprin` exactly as it was.

## ⚠️ `[IsAlgClosed F]` had TWO independent sources on this front, not one

Three session notes on this board record `hprin` over a general field as *"the only thing confining
all of the above to `F̄`"*.  **That was false.**  At `n = 2`, `[IsAlgClosed F]` enters
`WeilPairingAlternatingTwo` twice and independently:

1. through **`hprin`** — the principality of `[2]∗((T) − (O))`, discharged over `F̄` by `#791`; and
2. through **`exists_equation_nsmul_two_eq`** (`WeilPairingAlternatingTwo`), which produces the
   halving point `P` with `[2]P = T` and needs it to be **rational**.

Progress on the first does nothing about the second.  `WeilPairingAlternatingThree`'s docstring
states the `n = 3` version of source 2 explicitly (*"`[IsAlgClosed F]` — in exactly one place,
`exists_equation_nsmul_three_eq`, to produce `P`"*).

**This file removes source 2 outright, at both `n`.**  After it the compressed claim is true.

## Why source 2 descends and source 1 does not

The workhorses `translateEndo_eq_self_of_mul_algebraMap_sq_eq` and
`…_cube_eq` are already stated over an **arbitrary** field, and their hypotheses are equations
**in `F(W)`** — the telescoping `htel : f · τ_T∗f · … = c` and the root relation
`hsq : c₀ · gⁿ = [n]∗f` — together with the halving-point data.  So the halving point is used to
prove an *equality*, and an equality in `F(W)` may be checked after the **injective** base-change
map `functionFieldMap` of
`EllipticCurves.FunctionField.FunctionFieldBaseChange` (`#692`).  Push `htel` and `hsq` up to
`F̄(W⁄F̄)`, obtain the halving point *there*, run the ungated workhorse, and pull the conclusion
`τ_T∗ g = g` back through injectivity.

> ⚠️ **`hprin` does not descend and nothing here suggests it might.**  It is an *existence*
> statement and its witness lives upstairs.  **Base change carries conclusions down; it does not
> carry hypotheses up.**  The test that separates the two sources is: *is the obstruction used to
> prove an equality, or to produce a witness?*  Worth applying to every remaining `[IsAlgClosed F]`
> on this front before assuming it is `hprin` in disguise.

⚠️ **No divisor-level base-change compatibility is used here.**  The three endomorphism
intertwiners (`functionFieldMap_translateEndo`, `_mulByTwoEndo`, `_mulByThreeEndo`) are the whole
input.

⚠️ **That sentence used to continue** *"and `#692`'s *Remaining work* section will lead a reader to
expect otherwise"*, **and it no longer will**: `FunctionFieldBaseChange`'s `## Remaining work` used
to price `weilPairingElt` as part of the divisor half, and `#1271` removed the clause and supplied
the transport as `functionFieldMap_weilPairingElt`
(`EllipticCurves.FunctionField.WeilPairingEltBaseChange`) — one `rw`, from `map_div₀` and
`functionFieldMap_translateEndo`.  Do not go looking for the misleading sentence; it is quoted as
retired in the very section it used to be in.  ⚠️ The *first* half of this paragraph is untouched by
that: `divisor` and `divisorProj` still do not transport, that is still `#692`'s open remainder, and
nothing below uses them.

## Main results

* `translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_baseChange` — the merged `n = 2` workhorse with
  the halving-point hypotheses `hP` and `hdouble` **deleted**, over an arbitrary field.  They are
  not moved into another hypothesis; they disappear.
* `translateEndo_eq_self_of_mul_algebraMap_cube_eq_of_baseChange` — the `n = 3` twin.
* `exists_weilPairingElt_self_eq_one_of_hprin_{two,three}` — `e_n(T, T) = 1` over an arbitrary
  field.  These are `exists_weilPairingElt_self_eq_one_of_algClosed_{two,three}` **verbatim minus
  `[IsAlgClosed F]`**: same `hprin`, same conclusion, no hypothesis added.
* `exists_weilPairingMu_self_eq_one_of_hprin_{two,three}` — the `μ_n(F)` companions.

## Two things the `n = 3` descent needs that `n = 2` does not

* The cube workhorse takes `htors` at the `translatePoint` level, which the square one does not, so
  `3`-torsion has to be known **over `F̄`**.  It is obtained without any point-level base-change
  bridge, from the side-condition-free criterion `mem_torsion_three_some_iff'` (`Ψ₃.eval x = 0`)
  together with Mathlib's `map_Ψ₃` — an equation between polynomials, which transports for free.
* Its `htel` mentions translation by `−T`, whose `y`-index over `F̄` is
  `(W⁄F̄).negY (ι x₃) (ι y₃)` where the transported statement produces `ι (W.negY x₃ y₃)`.  ⚠️ Proof
  irrelevance does **not** close that — the two are equal only through
  `WeierstrassCurve.Affine.map_negY`, and one `simp only [hnegY]` is needed at that point.

## Scope

`[Field F] {W : Affine F} [W.IsElliptic]`, plus the characteristic hypotheses the concrete isogenies
need.  **No `[IsAlgClosed F]` anywhere in this file.**  No rung 4, no Ward, no
`[IsDedekindDomain W.CoordinateRing]` hypothesis (global for `[W.IsElliptic]` since
`CoordinateRingNormalGeneral`).

On naming: `_two` and `_three` track the **isogeny**, per the `## Naming` section of
`EllipticCurves.FunctionField.WeilPairing` (`#886`).  ⚠️ They do not say the exponent is fixed —
`exists_weilPairingMu_self_eq_one_of_hprin_two` quantifies over every `n ≠ 0` for its `μ_n(F)`,
and its `n = 2`-ness is entirely in `mulByTwoEndo`.  An unsuffixed name on this front means
isogeny-general, and no declaration here is.

On placement: everything here is stated in `WeierstrassCurve.Affine`, not in its `CoordinateRing`
sub-namespace, because that is where each declaration's un-base-changed twin lives
(`translateEndo_eq_self_of_mul_algebraMap_sq_eq` and
`exists_weilPairingElt_self_eq_one_of_algClosed_two`, both in `WeilPairingAlternatingTwo`).
⚠️ The `open CoordinateRing` below is what makes the two look alike from inside a file, and it is
why a namespace mismatch here is invisible to the build: a consumer sitting in
`WeierstrassCurve.Affine` with the same `open` resolves either spelling.  `#print axioms` on the
fully-qualified name is the only thing that checks it.

Out of scope: discharging `hprin` over a general field, which is now the **only** gate; the
divisor-level half of `#692`; general `n` (⚠️ no longer `#251`, which is closed — see below);
anything about `WeilPairingAlternating{Two,Three}`, which are untouched.

⚠️ **That bullet read *"general `n` (`#404`'s `ωₙ`)"*, then *"general `n` (`#251`)"*, and both of
those are now closed.**  PR #557 proved the on-curve identity for `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` at every index
over a field with `(2 : F) ≠ 0` and under `ψₙ(x, y) ≠ 0` —
`WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero`, `EllipticCurves.Torsion.OmegaCrux`.  The
*other* statement this tree also called `ωₙ` — the identification of those coordinates with the
**group-law** multiple `n • P` — is `#251` on its `x`-half and `#1500` on its `y`-half, and **both
are closed**: `hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) and
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` (`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579), each at
every index over a field with `(2 : F) ≠ 0` and under the same `ΨSqₙ(x) ≠ 0`.  ⚠️ That was the step
`hprin` reaches through `MulByTwoFibreAffine`/`MulByThreeFibre`, whose own input is
`addY_self_eq_div` (`EllipticCurves.Torsion.DoublingCoords`) and its `n = 3` mirror — and that input
now exists at every index.  ⚠️ **Whether it unblocks those two fibre descriptions is still NOT
measured**, here or anywhere in this tree, and the bullet is still retired because the reason it
gave is false and not because a replacement reason was found.  ⚠️ **But a general-`n` fibre
description no longer waits on that question**: `pullbackDivisorN_single_eq_sum_torsion_of_ne_zero`
(`EllipticCurves.FunctionField.MulByNFibre`, `#1540`, PR #612) is merged at every `n` with
`(2 : F) ≠ 0` and `((n : ℤ) : F) ≠ 0` over `F̄`, reached through the place layer rather than by
generalising those two files — whose coordinate inputs enter only at `n = 2` and `n = 3` — and
`exists_gS_n_of_isAlgClosed` (`EllipticCurves.FunctionField.PullbackPrincipalityN`, `#1843`)
consumes it.  ⚠️ So the sentence above is **short and not false**: what it declines to measure is a
route, and the destination that route was wanted for has since been reached without it.  The
two-reading account is
`EllipticCurves.FunctionField.MulByNPullback`.

## Non-vacuity

⚠️ Certified over **`ℚ`**, which is *not* algebraically closed (`rat_not_isAlgClosed` below proves
it, from `X² + X + 1` having no rational root).  A certificate over `AlgebraicClosure ℚ` would be
vacuous here: it is precisely the algebraically closed case that was already merged.  On
`y² = x³ − x` over `ℚ` the point `T = (0, 0)` is affine, nonsingular and `2`-torsion, and
`(2 : ℚ) ≠ 0` — so every hypothesis of the `n = 2` headline except `hprin` is satisfied on a curve
over a field where `exists_equation_nsmul_two_eq` is **unavailable**.  `y² + y = x³` with
`T = (0, 0)` does the same at `n = 3`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.1(b).
-/


-- @@ L156-156 verbatim
namespace WeierstrassCurve.Affine


-- @@ L158-158 verbatim
open CoordinateRing


-- @@ L160-160 verbatim
variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x₂ y₂ x₃ y₃ : F}


-- @@ L162-162 verbatim
local notation3 "K" => AlgebraicClosure F


-- @@ L164-203 verbatim
open Classical in
/-- **Translation by a `2`-torsion point fixes the square root, over an arbitrary field with
`(2 : F) ≠ 0`.**

This is `translateEndo_eq_self_of_mul_algebraMap_sq_eq` (`WeilPairingAlternatingTwo`) with its two
halving-point hypotheses `hP` and `hdouble` **removed** — not relocated, removed — and with
`[IsAlgClosed F]` absent.

The halving point is recovered over `F̄`, where `exists_equation_nsmul_two_eq` supplies it
unconditionally.  `htel` and `hsq` are equations in `F(W)`, so they push forward along
`functionFieldMap`; the merged workhorse then runs over `F̄`; and its conclusion, being an equality,
comes back through `functionFieldMap_injective`. -/
theorem translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_baseChange
    (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x₂ y₂)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : f * translateEndo h.left f = algebraMap F W.FunctionField c)
    (hsq : algebraMap F W.FunctionField c₀ * g ^ 2 = mulByTwoEndo h2 f) :
    translateEndo h.left g = g := by
  have h2' : (2 : K) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have h' : (W.map (algebraMap F K)).Nonsingular (algebraMap F K x₂) (algebraMap F K y₂) :=
    (map_nonsingular W (f := algebraMap F K) (algebraMap F K).injective x₂ y₂).mpr h
  have hgne : functionFieldMap W K g ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W K)).mpr hg
  have htel' : functionFieldMap W K f * translateEndo h'.left (functionFieldMap W K f)
      = algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c) := by
    rw [← functionFieldMap_translateEndo h.left, ← map_mul, htel,
      functionFieldMap_algebraMap_base]
  have hsq' : algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c₀)
      * functionFieldMap W K g ^ 2 = mulByTwoEndo h2' (functionFieldMap W K f) := by
    rw [← functionFieldMap_algebraMap_base, ← map_pow, ← map_mul, hsq,
      functionFieldMap_mulByTwoEndo h2 h2']
  obtain ⟨xP, yP, hP, hdouble⟩ := exists_equation_nsmul_two_eq h2' h'
  have key : translateEndo h'.left (functionFieldMap W K g) = functionFieldMap W K g :=
    translateEndo_eq_self_of_mul_algebraMap_sq_eq h2' hP h'.left
      (translatePoint_add hP hP h'.left hdouble) hgne
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc)
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc₀) htel' hsq'
  refine functionFieldMap_injective W K ?_
  rw [functionFieldMap_translateEndo h.left]
  exact key


-- @@ L205-236 verbatim
open Classical in
/-- **`e_2(T, T) = 1` over an arbitrary field with `(2 : F) ≠ 0`, at every nonsingular `2`-torsion
`T`**, with `hprin` (`#418`) as the only gate.

`exists_weilPairingElt_self_eq_one_of_algClosed_two` (`WeilPairingAlternatingTwo`) is this statement
with `[IsAlgClosed F]` added; the hypotheses and the conclusion are otherwise identical, and the
proof is that one two lines shorter — the `exists_equation_nsmul_two_eq` step is gone. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_two (h2 : (2 : F) ≠ 0)
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
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ := exists_mul_translateEndo_eq_algebraMap h htors
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByTwoEndo h2 f ≠ 0 := fun hz =>
    hf ((mulByTwoEndo h2).injective (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hsq : algebraMap F W.FunctionField c₀ * g ^ 2 = mulByTwoEndo h2 f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  have htinv : translateEndo h.left g = g :=
    translateEndo_eq_self_of_mul_algebraMap_sq_eq_of_baseChange h2 h hg hc hc₀ htel hsq
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩


-- @@ L238-263 verbatim
open Classical in
/-- **The alternating property at `n = 2` in the value group, over an arbitrary field with
`(2 : F) ≠ 0`, at every nonsingular `2`-torsion `T`, taking `hprin` (`#418`).**

`weilPairingMu` is indexed by a proof that the pairing element is an `n`-th root of unity, so the
statement produces one; it costs nothing, since the previous theorem gives `e_2(T, T) = 1` and
`1 ^ n = 1`.  The `n` carries only the `[NeZero n]` that `weilPairingMu` binds, for the same
reason — this is the group identity of `μ_n(F)` for whichever `n ≠ 0` the caller packaged the
value in. -/
theorem exists_weilPairingMu_self_eq_one_of_hprin_two (h2 : (2 : F) ≠ 0)
    (h : W.Nonsingular x₂ y₂) (htors : Point.some x₂ y₂ h ∈ W.torsion 2)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (2 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        2 • divisor W g₀ = divisor W (mulByTwoEndo h2 f))
    (n : ℕ) [NeZero n] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (2 : ℤ)
          - Finsupp.single (none : ProjPoint W) (2 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 2 = mulByTwoEndo h2 f) ∧
          ∃ hpow : weilPairingElt h.left g ^ n = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, htinv, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_hprin_two h2 h htors hprin
  exact ⟨f, hf, hdivproj, g, hg, hu, by rw [halt, one_pow],
    weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩


-- @@ L265-317 verbatim
open Classical in
/-- **Translation by a `3`-torsion point fixes the cube root, over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`.**

The `n = 3` twin, with `exists_equation_nsmul_three_eq`'s halving data removed.  ⚠️ Two steps have
no `n = 2` counterpart: `3`-torsion must be transported to `F̄` (done through
`mem_torsion_three_some_iff'` and `map_Ψ₃`, so no point-level base-change bridge is needed), and the
`−T` index of `htel` needs `map_negY` rather than proof irrelevance. -/
theorem translateEndo_eq_self_of_mul_algebraMap_cube_eq_of_baseChange
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h : W.Nonsingular x₃ y₃)
    (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
    {f g : W.FunctionField} (hg : g ≠ 0) {c c₀ : F} (hc : c ≠ 0) (hc₀ : c₀ ≠ 0)
    (htel : f * translateEndo h.left f * translateEndo ((W.equation_neg x₃ y₃).mpr h.left) f
      = algebraMap F W.FunctionField c)
    (hcube : algebraMap F W.FunctionField c₀ * g ^ 3 = mulByThreeEndo h2 h3 f) :
    translateEndo h.left g = g := by
  have h2' : (2 : K) ≠ 0 := algebraMap_ofNat_ne_zero h2
  have h3' : (3 : K) ≠ 0 := algebraMap_ofNat_ne_zero h3
  have h' : (W.map (algebraMap F K)).Nonsingular (algebraMap F K x₃) (algebraMap F K y₃) :=
    (map_nonsingular W (f := algebraMap F K) (algebraMap F K).injective x₃ y₃).mpr h
  have htorsK : Point.some (algebraMap F K x₃) (algebraMap F K y₃) h'
      ∈ (W.map (algebraMap F K)).torsion 3 := by
    rw [mem_torsion_three_some_iff', WeierstrassCurve.map_Ψ₃, Polynomial.eval_map_apply,
      mem_torsion_three_some_iff'.mp htors, map_zero]
  have hnegY : (W.map (algebraMap F K)).negY (algebraMap F K x₃) (algebraMap F K y₃)
      = algebraMap F K (W.negY x₃ y₃) := WeierstrassCurve.Affine.map_negY (algebraMap F K) x₃ y₃
  have hgne : functionFieldMap W K g ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldMap_injective W K)).mpr hg
  have htel0 : functionFieldMap W K f * translateEndo h'.left (functionFieldMap W K f)
      * translateEndo (((W.equation_neg x₃ y₃).mpr h.left).map (algebraMap F K))
          (functionFieldMap W K f)
      = algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c) := by
    rw [← functionFieldMap_translateEndo h.left,
      ← functionFieldMap_translateEndo ((W.equation_neg x₃ y₃).mpr h.left),
      ← map_mul, ← map_mul, htel, functionFieldMap_algebraMap_base]
  have hcube' : algebraMap K (W.map (algebraMap F K)).FunctionField (algebraMap F K c₀)
      * functionFieldMap W K g ^ 3 = mulByThreeEndo h2' h3' (functionFieldMap W K f) := by
    rw [← functionFieldMap_algebraMap_base, ← map_pow, ← map_mul, hcube,
      functionFieldMap_mulByThreeEndo h2 h3 h2' h3']
  obtain ⟨xP, yP, xQ, yQ, hP, hQ, hdouble, hsum⟩ := exists_equation_nsmul_three_eq h2' h' htorsK
  have htorsK' : torsionPoint h'.left + torsionPoint h'.left + torsionPoint h'.left = 0 :=
    add_add_self_eq_zero_of_mem_torsion_three htorsK
  have key : translateEndo h'.left (functionFieldMap W K g) = functionFieldMap W K g := by
    refine translateEndo_eq_self_of_mul_algebraMap_cube_eq h2' h3' hP hQ h'.left
      (translatePoint_add hP hP hQ hdouble) (translatePoint_add hP hQ h'.left hsum)
      (translatePoint_add_add_self h'.left htorsK') hgne
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc)
      ((map_ne_zero_iff _ (algebraMap F K).injective).mpr hc₀) ?_ hcube'
    simp only [hnegY]
    exact htel0
  refine functionFieldMap_injective W K ?_
  rw [functionFieldMap_translateEndo h.left]
  exact key


-- @@ L319-350 verbatim
open Classical in
/-- **`e_3(T, T) = 1` over an arbitrary field with `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at every
nonsingular `3`-torsion `T`**, with `hprin` as the only gate: the `n = 3` twin of
`exists_weilPairingElt_self_eq_one_of_hprin_two`, and
`exists_weilPairingElt_self_eq_one_of_algClosed_three` minus `[IsAlgClosed F]`. -/
theorem exists_weilPairingElt_self_eq_one_of_hprin_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x₃ y₃) (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
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
  obtain ⟨f, hf, hdivproj, c, hc, htel⟩ :=
    exists_mul_translateEndo_mul_translateEndo_eq_algebraMap h htors
  obtain ⟨g, hg, hgdiv⟩ :=
    hprin f hf (divisor_eq_single_of_divisorProj_eq_single_sub_single hdivproj)
  have hfne : mulByThreeEndo h2 h3 f ≠ 0 := fun hz =>
    hf ((mulByThreeEndo h2 h3).injective (by rw [hz, map_zero]))
  obtain ⟨u, hu⟩ := exists_smul_pow_eq_of_nsmul_divisor hfne hg hgdiv
  obtain ⟨c₀, hc₀, hueq⟩ := isUnit_iff_exists_eq_algebraMap.mp u.isUnit
  have hcube : algebraMap F W.FunctionField c₀ * g ^ 3 = mulByThreeEndo h2 h3 f := by
    rw [← hu, Algebra.smul_def, hueq, ← IsScalarTower.algebraMap_apply]
  have htinv : translateEndo h.left g = g :=
    translateEndo_eq_self_of_mul_algebraMap_cube_eq_of_baseChange h2 h3 h htors hg hc hc₀
      htel hcube
  exact ⟨f, hf, hdivproj, g, hg, ⟨u, hu⟩, htinv,
    weilPairingElt_self_of_translateEndo_fixed h.left hg htinv⟩


-- @@ L352-371 verbatim
open Classical in
/-- **The alternating property at `n = 3` in the value group, over an arbitrary field with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0`, at every nonsingular `3`-torsion `T`, taking `hprin`.** -/
theorem exists_weilPairingMu_self_eq_one_of_hprin_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : W.Nonsingular x₃ y₃) (htors : Point.some x₃ y₃ h ∈ W.torsion 3)
    (hprin : ∀ f : W.FunctionField, f ≠ 0 →
      divisor W f = Finsupp.single (pointClosedPoint h.left) (3 : ℤ) →
      ∃ g₀ : W.FunctionField, g₀ ≠ 0 ∧
        3 • divisor W g₀ = divisor W (mulByThreeEndo h2 h3 f))
    (n : ℕ) [NeZero n] :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisorProj W f = Finsupp.single (some (pointClosedPoint h.left)) (3 : ℤ)
          - Finsupp.single (none : ProjPoint W) (3 : ℤ) ∧
        ∃ g : W.FunctionField, g ≠ 0 ∧
          (∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • g ^ 3 = mulByThreeEndo h2 h3 f) ∧
          ∃ hpow : weilPairingElt h.left g ^ n = 1, weilPairingMu h.left hpow = 1 := by
  obtain ⟨f, hf, hdivproj, g, hg, hu, htinv, halt⟩ :=
    exists_weilPairingElt_self_eq_one_of_hprin_three h2 h3 h htors hprin
  exact ⟨f, hf, hdivproj, g, hg, hu, by rw [halt, one_pow],
    weilPairingMu_self_of_translateEndo_fixed h.left hg _ htinv⟩


-- @@ L373-379 verbatim
/-! ### Non-vacuity, over a field that is NOT algebraically closed

⚠️ The base field below is **`ℚ`**.  A certificate over `AlgebraicClosure ℚ` would be vacuous for
this file — the algebraically closed case is exactly what was already merged.  `hprin` is a
hypothesis of both headlines, so what is certified is that **every other hypothesis is
simultaneously satisfiable over a field where `exists_equation_nsmul_two_eq` is unavailable**, which
is the whole content of the file. -/


-- @@ L381-381 verbatim
section Nonvacuity


-- @@ L383-383 verbatim
open Polynomial


-- @@ L385-395 verbatim
/-- **`ℚ` is not algebraically closed**, from `X² + X + 1` having no rational root (its discriminant
is `−3`).  This is what makes the certificates below non-vacuous rather than a restatement of the
merged `F̄` headlines. -/
private lemma rat_not_isAlgClosed : ¬ IsAlgClosed ℚ := by
  intro hcl
  obtain ⟨q, hq⟩ := hcl.exists_root (X ^ 2 + X + 1 : ℚ[X]) (by
    rw [show (X ^ 2 + X + 1 : ℚ[X]) = C 1 * X ^ 2 + C 1 * X + C 1 by simp,
      degree_quadratic one_ne_zero]
    exact two_ne_zero)
  rw [IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hq
  nlinarith [sq_nonneg (2 * q + 1)]


-- @@ L397-397 verbatim
private lemma exampleTwo : (2 : ℚ) ≠ 0 := by norm_num


-- @@ L399-399 verbatim
private lemma exampleThree : (3 : ℚ) ≠ 0 := by norm_num


-- @@ L401-403 verbatim
/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, whose single
`[CharZero F]` instance also supplies `IsElliptic` here. -/


-- @@ L405-405 verbatim
open EllipticCurves.Fixture


-- @@ L407-409 verbatim
private lemma exampleNs : (y2EqX3SubX ℚ).Nonsingular 0 0 :=
  (y2EqX3SubX ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])


-- @@ L411-414 verbatim
open Classical in
private lemma exampleTors :
    Point.some (0 : ℚ) 0 exampleNs ∈ (y2EqX3SubX ℚ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNs).mpr (by norm_num [y2EqX3SubX])


-- @@ L416-444 verbatim
open Classical in
/-- **The `n = 2` headline applies on a curve over `ℚ`**, with `hprin` the only hypothesis left.

⚠️ `ℚ` is not algebraically closed (`rat_not_isAlgClosed`), so the merged
`exists_weilPairingElt_self_eq_one_of_algClosed_two` does **not** apply here and neither does
`exists_equation_nsmul_two_eq`, which is the point.

⚠️ The `by convert exampleTors` is not decoration.  `ℚ` has a genuine `DecidableEq` instance, so the
`torsion` in `exampleTors` is indexed by `instDecidableEqRat` while the headline — stated for a
general `F` under `open Classical in` — is indexed by `Classical.propDecidable`.  The two
`AddSubgroup`s are propositionally but not syntactically equal; `convert` discharges the difference
by `Subsingleton.elim`.  This does not arise in the merged non-vacuity blocks on this front because
they all sit over `AlgebraicClosure ℚ`, which has no decidable equality. -/
example (hprin : ∀ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 →
      divisor (y2EqX3SubX ℚ) f
        = Finsupp.single (pointClosedPoint exampleNs.left) (2 : ℤ) →
      ∃ g₀ : (y2EqX3SubX ℚ).FunctionField, g₀ ≠ 0 ∧
        2 • divisor (y2EqX3SubX ℚ) g₀
          = divisor (y2EqX3SubX ℚ) (mulByTwoEndo exampleTwo f)) :
    ∃ f : (y2EqX3SubX ℚ).FunctionField, f ≠ 0 ∧
      divisorProj (y2EqX3SubX ℚ) f
          = Finsupp.single (some (pointClosedPoint exampleNs.left)) (2 : ℤ)
            - Finsupp.single (none : ProjPoint (y2EqX3SubX ℚ)) (2 : ℤ) ∧
        ∃ g : (y2EqX3SubX ℚ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2EqX3SubX ℚ).CoordinateRingˣ,
            (u : (y2EqX3SubX ℚ).CoordinateRing) • g ^ 2 = mulByTwoEndo exampleTwo f) ∧
          translateEndo exampleNs.left g = g ∧ weilPairingElt exampleNs.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_two exampleTwo exampleNs
    (by convert exampleTors) hprin


-- @@ L446-448 verbatim
private lemma exampleNsThree : (y2AddYEqX3 ℚ).Nonsingular 0 0 :=
  (y2AddYEqX3 ℚ).equation_iff_nonsingular.mp (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Affine.equation_iff])


-- @@ L450-455 verbatim
open Classical in
private lemma exampleTorsThree :
    Point.some (0 : ℚ) 0 exampleNsThree ∈ (y2AddYEqX3 ℚ).torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [y2AddYEqX3, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])


-- @@ L457-476 verbatim
open Classical in
/-- **The `n = 3` headline applies on a curve over `ℚ`**, with `hprin` the only hypothesis left. -/
example (hprin : ∀ f : (y2AddYEqX3 ℚ).FunctionField, f ≠ 0 →
      divisor (y2AddYEqX3 ℚ) f
        = Finsupp.single (pointClosedPoint exampleNsThree.left) (3 : ℤ) →
      ∃ g₀ : (y2AddYEqX3 ℚ).FunctionField, g₀ ≠ 0 ∧
        3 • divisor (y2AddYEqX3 ℚ) g₀
          = divisor (y2AddYEqX3 ℚ) (mulByThreeEndo exampleTwo exampleThree f)) :
    ∃ f : (y2AddYEqX3 ℚ).FunctionField, f ≠ 0 ∧
      divisorProj (y2AddYEqX3 ℚ) f
          = Finsupp.single (some (pointClosedPoint exampleNsThree.left)) (3 : ℤ)
            - Finsupp.single (none : ProjPoint (y2AddYEqX3 ℚ)) (3 : ℤ) ∧
        ∃ g : (y2AddYEqX3 ℚ).FunctionField, g ≠ 0 ∧
          (∃ u : (y2AddYEqX3 ℚ).CoordinateRingˣ,
            (u : (y2AddYEqX3 ℚ).CoordinateRing) • g ^ 3
              = mulByThreeEndo exampleTwo exampleThree f) ∧
          translateEndo exampleNsThree.left g = g ∧
            weilPairingElt exampleNsThree.left g = 1 :=
  exists_weilPairingElt_self_eq_one_of_hprin_three exampleTwo exampleThree exampleNsThree
    (by convert exampleTorsThree) hprin


-- @@ L478-478 verbatim
end Nonvacuity


-- @@ L480-480 verbatim
end WeierstrassCurve.Affine
