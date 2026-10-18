/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OddTorsionCount


-- @@ L8-148 verbatim
/-!
# `#E[n] = n²` at odd `n`, reduced to one Wronskian identity and one coprimality

Issue `#1506`.  `EllipticCurves.Torsion.OddTorsionCount` proves that over an algebraically closed
field of characteristic `≠ 2`, at an odd `n` with `char F ∤ n`,

```
#E[n] = n²   ↔   Separable (preΨₙ),
```

so the last gate on the `p`-primary tower (`EllipticCurves.Torsion.PrimaryTower`, `#1490` item 3)
is the separability of one univariate polynomial.  **This file discharges that gate from two
inputs, neither of which mentions torsion, points, or the group law.**  ⚠️ Both inputs are proved
downstream (`EllipticCurves.Torsion.OmegaPairCoprime` and `EllipticCurves.Torsion.OmegaChordSum`),
so at odd `n` the chain that starts here is unconditional; see
`EllipticCurves.Torsion.PrimaryTowerOdd`.

## The two inputs

* the **Wronskian identity** — this is `[n]∗ω = nω` on the invariant differential, written in
  `F[X]` with no differentials:

  ```
  Φₙ′ · ΨSqₙ  −  Φₙ · ΨSqₙ′  =  n · preΨₙ · preΩₙ ;
  ```

* `IsCoprime (preΨₙ) (preΩₙ)`.

⚠️ **Neither is proved here, and this file is not a proof of `#E[n] = n²`.**  It is the assembly,
in the idiom of `WeierstrassCurve.Affine.nonempty_torsionPow_addEquiv_of_card`
(`EllipticCurves.Torsion.PrimaryTowerAlgClosed`): one signature from which a reader can see the
whole of what is owed.  `#1506` records the route to each input, and the evidence for both.

## Why those two inputs suffice, in three lines

`Separable p` **is** `IsCoprime p p′`.  At odd `n` the parity branch of `ΨSqₙ` is trivial, so
`ΨSqₙ = preΨₙ²` and the identity divides by `preΨₙ` — which is nonzero because `char F ∤ n` — to

```
Φₙ′ · preΨₙ  −  2 · Φₙ · preΨₙ′  =  n · preΩₙ .
```

A Bézout certificate for `(preΨₙ, preΩₙ)` therefore becomes one for `(preΨₙ, preΨₙ′)` after
substituting `preΩₙ = n⁻¹·(Φₙ′·preΨₙ − 2Φₙ·preΨₙ′)`, and `n⁻¹` exists exactly because
`(n : F) ≠ 0`.

⚠️ **`(n : F) ≠ 0` is spent in exactly one place and that is the point.**  It is the only step that
can fail, and it must be able to fail: in characteristic `p` the conclusion `#E[p] = p²` is false.
A route that did not consume the hypothesis there would be proving something untrue.

## Main statements

⚠️ Every public declaration of this file is listed.

* `WeierstrassCurve.Affine.separable_preΨ_of_wronskian` : `Separable (preΨₙ)` from the two inputs,
  at **odd** `n` over any field with `char F ∤ n`; **no** algebraic closure, **no**
  `[W.IsElliptic]`, and **nothing about `(2 : F)`**.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_wronskian` : `#E[n] = n²` from the same two inputs
  at the same odd `n` with `char F ∤ n`, plus what `card_torsion_eq_sq_iff_separable_preΨ` itself
  asks — `[IsAlgClosed F]`, `[W.IsElliptic]` and `(2 : F) ≠ 0`.
* `WeierstrassCurve.Affine.ψ_add_mul_ψ_sub_eq_neg_Φ_mul_ΨSq` : `ψ_{n+q}·ψ_{n−q} = −Φₙ(x)·ΨSq_q(x)`
  at a point `(x, y)` **on the curve** where `ψₙ` vanishes, at every `q`.  ⚠️ Merged content,
  repackaged: it is `ψ_add_mul_ψ_sub_evalEval` with one term killed.  ⚠️ **Named for its
  conclusion, not for its hypothesis**: `WeierstrassCurve.Affine.ψ_add_mul_ψ_sub_of_ψ_eq_zero`
  (`EllipticCurves.Torsion.NsmulYPeriodic`) is a *different* statement — Ward at `(d, n, 1, 0)`,
  `ψ_{d+n}·ψ_{d−n} = ψ_{d+1}·ψ_{d−1}·ψₙ²` — and renaming this one back would break the root import.
* `WeierstrassCurve.Affine.eval_preΩ_ne_zero_of_eval_preΨ_eq_zero` and
  `WeierstrassCurve.Affine.isCoprime_preΨ_preΩ` : the **second** input reduced to a single pointwise
  identity `hpair`, spending three merged facts on the way.  Over `F̄` with `[W.IsElliptic]` and
  `(2 : F) ≠ 0`, at an odd `n ≠ 0`; the first is the pointwise form and adds a root `x` of `preΨₙ`.
* `WeierstrassCurve.Affine.card_torsion_eq_sq_of_wronskian_of_pair` : both reductions composed.
  Over `F̄` with `[W.IsElliptic]` and `(2 : F) ≠ 0`, at an odd `n ≠ 0` with `char F ∤ n`,
  `#E[n] = n²` with the two equations `hid` and `hpair` **the only gates left**.

⚠️ **Every bullet above names the whole explicit hypothesis list of the declaration it is about**,
and this list carries **no register** at its head on purpose.  It used to mix registers — bullet 1
naming its own hypotheses and its own negatives, bullet 2 a different set, bullet 4 naming only the
gate its two declarations reduce, and `…_of_wronskian_of_pair` asserting there were none — which is
what `README.md` `### Scope of the rules above` forbids.

⚠️ **And that includes `h : W.Equation x y`, which is why bullet 3 says *"on the curve"*.**  The
conclusion of `ψ_add_mul_ψ_sub_eq_neg_Φ_mul_ΨSq` typechecks without `h`, so `h` is a hypothesis
and **not** a data argument of the object the bullet is about — being an explicit argument of that
object is the **necessary** half of the data-argument clearance (`README.md` `### Reach clauses`,
`#1631`), and this conclusion takes no such argument.  ⚠️ This used to cite the clearance
`### Module-block bullets` gave `residueDegreeN n hn p`; that reading is withdrawn, the verdict on
this row is not, and it never rested on it.  Nor is it left to
`### Gate-discharge claims`' *"the setting"*: bullet 3 makes no gate-discharge claim at all, and
that register carries claims about **gates**, saying in terms that it *"is not a licence to say
the signature is short"*.  The same reading repaired
`EllipticCurves.FunctionField.WeilPairingAlternatingBaseChangeN`'s two rows (`#1619`, PR #643).

⚠️ **A register at the head would have to say *"except"* twice**, which is why there is none.
`ψ_add_mul_ψ_sub_eq_neg_Φ_mul_ΨSq` is at every `n : ℤ` and takes neither `Odd n` nor an index
condition; and the index condition of the other five is not one clause but two —
`separable_preΨ_of_wronskian`, `card_torsion_eq_sq_of_wronskian` and `…_of_wronskian_of_pair` bind
`(n : F) ≠ 0`, which is where the proof divides by `preΨₙ`, while
`eval_preΩ_ne_zero_of_eval_preΨ_eq_zero` and `isCoprime_preΨ_preΩ` bind only `n ≠ 0`.
⚠️ `…_of_wronskian_of_pair` binds **both**, which is why its bullet names both — and `n ≠ 0` is
named beside `Odd n` in bullets 4 and 5, the rows whose signatures carry it separately, even though
`¬ Odd 0` derives it; bullets 1 and 2 do not name it because those two signatures do not bind it.
Instance arguments need **not** be listed (`README.md` `### Reach clauses`), and `[DecidableEq F]`
is named nowhere above; the mentions that do appear (*"over `F̄`"*, *"`[W.IsElliptic]`"*, and
bullet 1's three absences) were each checked against the declaration's own instance list.

⚠️ So the gate is **two identities**, not a research programme: the Wronskian one, and `hpair`.

⚠️ **`hpair` is now proved** — `EllipticCurves.Torsion.OmegaPairCoprime`, `#1506` scope item 2 —
so what is left of the gate is the Wronskian identity alone.  The unconditional forms of
`isCoprime_preΨ_preΩ` and `card_torsion_eq_sq_of_wronskian_of_pair` live there; the hypothesised
forms below are kept because they are what states, in one signature, what each half costs.

⚠️ The hypothesis gap between the two is real and is worth reading off the signatures: separability
of `preΨₙ` is a statement about one polynomial over any field, while turning it into a point count
needs the curve to be elliptic and the field to be closed.  The Wronskian identity is asked for
only at the single index `n`, not at every index.

## What is *not* here

* **No proof of either input.**  `#1506` scope item 1; item 2 is discharged downstream in
  `EllipticCurves.Torsion.OmegaPairCoprime`, which imports this file.  ⚠️ Both inputs are now proved
  downstream — item 1 by `WeierstrassCurve.hasWronskianId` (`EllipticCurves.Torsion.OmegaChordSum`)
  — so the hypotheses below are dischargeable, and none of them is proved *here*, which is what this
  bullet is about.
* **Nothing at even `n`.**  `card_torsion_eq_sq_iff_separable_preΨ` is odd-`n` only, and the
  division by `preΨₙ` above uses `ΨSqₙ = preΨₙ²`, which is the odd branch.
* **Nothing about `#1184`'s arbitrary-ring coprimality**, `#403`/`#405`, or the function field.
  ⚠️ In particular this is **not** the fibre route: `card_fibre_comapProjPointN_projPointOfPoint`
  (`EllipticCurves.FunctionField.MulByNFibre`) computes its `n²` *from* `card_torsion_eq_sq_of_
  smooth`, so it cannot supply this count without circularity.
* **No change to `PrimaryTower`'s gate list or to `#293`.**  This file only renames what is owed.
  ⚠️ This bullet used to continue *"Those record `#E[p] = p²` as open, and it is open"*, which is
  false at odd `p`: `card_torsion_eq_sq_of_odd` (`EllipticCurves.Torsion.OmegaChordSum`) proves it,
  `EllipticCurves.Torsion.PrimaryTowerOdd` discharges the gate list with it, and `#293`'s odd half
  goes with it.  The bullet's own claim — that nothing changes *in this file* — still holds.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10, III.5.3 (the
  invariant differential and `[n]∗ω = nω`) and III.6 Cor 6.4.
-/


-- @@ L150-150 verbatim
open Polynomial


-- @@ L152-152 verbatim
namespace WeierstrassCurve.Affine


-- @@ L154-154 verbatim
variable {F : Type*} [Field F] {W : Affine F}


-- @@ L156-190 verbatim
/-- **`preΨₙ` is separable**, at an odd `n` invertible in `F`, given the Wronskian identity and the
coprimality of `preΨₙ` with `preΩₙ`.

⚠️ Read the hypotheses as the statement: the mathematics is `hid` and `hcop`, and everything below
is the Bézout bookkeeping.  See `#1506` for what is known about each.

`hid` is `[n]∗ω = nω` cleared of denominators; `hcop` says `preΨₙ` and `preΩₙ` have no common
factor, equivalently — since `preΨ₂ₙ = preΨₙ·preΩₙ` — that no root of `preΨₙ` is a repeated root of
`preΨ₂ₙ` for that reason. -/
theorem separable_preΨ_of_wronskian {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hid : derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
        W.Φ (n : ℤ) * derivative (W.ΨSq (n : ℤ)) =
      (n : F[X]) * W.preΨ (n : ℤ) * W.preΩ (n : ℤ))
    (hcop : IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ))) :
    (W.preΨ (n : ℤ)).Separable := by
  have hcast : (((n : ℤ)) : F) ≠ 0 := by push_cast; exact hn
  have hp0 : W.preΨ (n : ℤ) ≠ 0 := W.preΨ_ne_zero (R := F) hcast
  -- at an odd index the parity branch of `ΨSq` is trivial
  have hoddZ : Odd ((n : ℤ)) := by exact_mod_cast hodd
  have hsq : W.ΨSq (n : ℤ) = W.preΨ (n : ℤ) ^ 2 := by
    rw [WeierstrassCurve.ΨSq, if_neg (Int.not_even_iff_odd.mpr hoddZ), mul_one]
  -- divide the identity by `preΨₙ`
  have hdiv : derivative (W.Φ (n : ℤ)) * W.preΨ (n : ℤ) -
      2 * W.Φ (n : ℤ) * derivative (W.preΨ (n : ℤ)) = (n : F[X]) * W.preΩ (n : ℤ) := by
    refine mul_left_cancel₀ hp0 ?_
    rw [hsq] at hid
    simp only [derivative_pow, Nat.cast_ofNat, map_ofNat] at hid ⊢
    linear_combination hid
  -- turn a Bézout certificate for `(preΨₙ, preΩₙ)` into one for `(preΨₙ, preΨₙ′)`
  obtain ⟨u, v, huv⟩ := hcop
  refine (separable_def' _).2 ⟨u + v * C ((n : F)⁻¹) * derivative (W.Φ (n : ℤ)),
    -(2 * v * C ((n : F)⁻¹) * W.Φ (n : ℤ)), ?_⟩
  have hC : C ((n : F)⁻¹) * (n : F[X]) = 1 := by
    rw [← C_eq_natCast, ← C_mul, inv_mul_cancel₀ hn, C_1]
  linear_combination huv + v * C ((n : F)⁻¹) * hdiv + v * W.preΩ (n : ℤ) * hC


-- @@ L192-208 verbatim
/-- **`#E[n] = n²` with `(2 : F) ≠ 0`, at odd `n` with `(n : F) ≠ 0`** — `#1490`'s remaining gate,
reduced to the Wronskian identity and the `preΨₙ`/`preΩₙ` coprimality.

⚠️ This is not a proof that `#E[n] = n²`; it is the statement that those two polynomial facts are
all that stands between `main` and it.  The `↔` of
`WeierstrassCurve.Affine.card_torsion_eq_sq_iff_separable_preΨ` also says there is no cheaper
substitute: any proof of this conclusion proves `preΨₙ` separable. -/
theorem card_torsion_eq_sq_of_wronskian [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hodd : Odd n) (hn : (n : F) ≠ 0)
    (hid : derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
        W.Φ (n : ℤ) * derivative (W.ΨSq (n : ℤ)) =
      (n : F[X]) * W.preΨ (n : ℤ) * W.preΩ (n : ℤ))
    (hcop : IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ))) :
    Nat.card (W.torsion n) = n ^ 2 :=
  (card_torsion_eq_sq_iff_separable_preΨ h2 hodd hn).2
    (separable_preΨ_of_wronskian hodd hn hid hcop)


-- @@ L210-214 verbatim
/-! ## Reducing the second input to one pointwise identity

`IsCoprime (preΨₙ) (preΩₙ)` is not a fresh front: everything it needs is on `main` **except** one
equation.  This section spends the merged facts and leaves that equation exposed.
-/


-- @@ L216-216 verbatim
variable {x y : F}


-- @@ L218-231 verbatim
/-- **`ψ_{n+q}·ψ_{n−q} = −Φₙ(x)·ΨSq_q(x)` at a point where `ψₙ` vanishes**, at every `q`.

`WeierstrassCurve.Affine.ψ_add_mul_ψ_sub_evalEval` (`EllipticCurves.Torsion.XDifference`) reads
`ψ_{p+q}ψ_{p−q} = Φ_q·ΨSq_p − Φ_p·ΨSq_q`; at `p = n` the first term dies because `ΨSqₙ(x)` is
`ψₙ(x, y)²`.  ⚠️ The right-hand side does not involve `y`, so the product `ψ_{n+q}·ψ_{n−q}` is
constant on the `y`-fibre — that is what makes `q = 1` and `q = 2` below into non-vanishing
statements about `x` alone. -/
theorem ψ_add_mul_ψ_sub_eq_neg_Φ_mul_ΨSq (h : W.Equation x y) {n : ℤ}
    (hz : (W.ψ n).evalEval x y = 0) (q : ℤ) :
    (W.ψ (n + q)).evalEval x y * (W.ψ (n - q)).evalEval x y =
      -((W.Φ n).eval x * (W.ΨSq q).eval x) := by
  have hsq : (W.ΨSq n).eval x = 0 := by rw [← ψ_sq_evalEval h n, hz]; ring
  rw [ψ_add_mul_ψ_sub_evalEval h n q, hsq]
  ring


-- @@ L233-279 verbatim
/-- **`preΩₙ` does not vanish at a root of `preΨₙ`** — scope item 2 of `#1506`, reduced to `hpair`.

Everything except `hpair` is merged.  ⚠️ Read the proof as a budget: `Φₙ(x) ≠ 0` is
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` (`EllipticCurves.Torsion.TwoTorsionOrder`, PR #569) and
`Ψ₂Sq(x) ≠ 0` is `eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero` (`EllipticCurves.Torsion.OddTorsionCount`,
PR #574); together with `ψ_add_mul_ψ_sub_eq_neg_Φ_mul_ΨSq` at `q = 1` and `q = 2` they give
`ψ_{n−1}(x, y) ≠ 0` and `ψ_{n+2}(x, y) ≠ 0`.  `hpair` then collapses `Ωₙ` to `2·ψ_{n+2}·ψ_{n−1}²`,
and `WeierstrassCurve.Ω_factor` divides out the `ψ₂²`.

⚠️ `hpair` is the whole content of this statement.  It says the two summands of `Ωₙ` are
negatives of one another at a point where `ψₙ` vanishes; equivalently, since their product is
`−Φₙ³·Ψ₂Sq` by the two instances above, that `(ψ_{n+2}·ψ_{n−1}²)² = Φₙ³·Ψ₂Sq`.  ⚠️ It is **not** a
consequence of `ψ_add_mul_ψ_sub` alone: that relation determines `ψ_{n+k}·ψ_{n−k}` for each `k` and
says nothing relating different `k`, which is exactly what `hpair` needs.  It **is** a consequence
of the `k`-general `ψ_shift_symm_of_ψ_eq_zero`, and is proved from it in
`EllipticCurves.Torsion.OmegaPairCoprime` (`ψ_pair_of_equation`). -/
theorem eval_preΩ_ne_zero_of_eval_preΨ_eq_zero [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {n : ℕ} (hodd : Odd n) (hn : n ≠ 0)
    (hpair : ∀ x y : F, W.Equation x y → (W.ψ (n : ℤ)).evalEval x y = 0 →
      (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
        -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2))
    {x : F} (hx : (W.preΨ (n : ℤ)).eval x = 0) :
    (W.preΩ (n : ℤ)).eval x ≠ 0 := by
  obtain ⟨y, hxy⟩ := exists_equation (W := W) h2 x
  have hΨSq : (W.ΨSq (n : ℤ)).eval x = 0 := by
    rw [ΨSq_natCast_eq_sq_of_odd hodd, eval_pow, hx, zero_pow (two_ne_zero (α := ℕ))]
  have hψn : (W.ψ (n : ℤ)).evalEval x y = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by rw [ψ_sq_evalEval hxy, hΨSq])
  have hΦ : (W.Φ (n : ℤ)).eval x ≠ 0 := eval_Φ_ne_zero_of_eval_ΨSq_eq_zero h2 hn x hΨSq
  have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 := eval_Ψ₂Sq_ne_zero_of_eval_preΨ_eq_zero h2 hodd hx
  -- `ψ_{n−1}(x, y) ≠ 0` and `ψ_{n+2}(x, y) ≠ 0`
  have h1 := ψ_add_mul_ψ_sub_eq_neg_Φ_mul_ΨSq hxy hψn 1
  rw [WeierstrassCurve.ΨSq_one, eval_one, mul_one] at h1
  have hm1 : (W.ψ ((n : ℤ) - 1)).evalEval x y ≠ 0 := fun hc => hΦ (by
    rw [hc, mul_zero] at h1; simpa using h1.symm)
  have h2' := ψ_add_mul_ψ_sub_eq_neg_Φ_mul_ΨSq hxy hψn 2
  rw [WeierstrassCurve.ΨSq_two] at h2'
  have hp2 : (W.ψ ((n : ℤ) + 2)).evalEval x y ≠ 0 := fun hc => (mul_ne_zero hΦ hΨ₂) (by
    rw [hc, zero_mul] at h2'; simpa using h2'.symm)
  -- `Ωₙ` collapses, and `Ω_factor` divides out the `ψ₂²`
  have hfac := congrArg (Polynomial.evalEval x y) (W.Ω_factor (n : ℤ))
  rw [if_neg (Int.not_even_iff_odd.mpr (by exact_mod_cast hodd : Odd ((n : ℤ))))] at hfac
  simp only [evalEval_mul, evalEval_sub, evalEval_pow, evalEval_C, ← ψ_evalEval hxy] at hfac
  intro hΩ
  rw [hΩ, mul_zero] at hfac
  exact mul_ne_zero (mul_ne_zero h2 hp2) (pow_ne_zero 2 hm1) (by
    linear_combination hfac + hpair x y hxy hψn)


-- @@ L281-296 verbatim
/-- **`IsCoprime (preΨₙ) (preΩₙ)`** over an algebraically closed field, from `hpair`.

The descent is the same one PR #576 used for `isCoprime_ΨSq_adjacent` —
`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` — and it is trivial here because the base
field is already closed, so no `AlgebraicClosure F` transport is needed. -/
theorem isCoprime_preΨ_preΩ [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hodd : Odd n) (hn : n ≠ 0)
    (hpair : ∀ x y : F, W.Equation x y → (W.ψ (n : ℤ)).evalEval x y = 0 →
      (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
        -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2)) :
    IsCoprime (W.preΨ (n : ℤ)) (W.preΩ (n : ℤ)) := by
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K := F) _ _ _).mpr fun a => ?_
  simp only [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id]
  by_cases hp : (W.preΨ (n : ℤ)).eval a = 0
  · exact Or.inr (eval_preΩ_ne_zero_of_eval_preΨ_eq_zero h2 hodd hn hpair hp)
  · exact Or.inl hp


-- @@ L298-313 verbatim
/-- **`#E[n] = n²` with `(2 : F) ≠ 0`, at odd `n ≠ 0` with `(n : F) ≠ 0`, from two equations** —
the two reductions of this file composed.

⚠️ This is a statement about what is owed, not a proof of its conclusion.  Read the two hypotheses:
`hid` is `[n]∗ω = nω` in `F[X]`, and `hpair` says the two summands of `Ωₙ` are negatives at a point
where `ψₙ` vanishes.  `#1506` scope items 1 and 2. -/
theorem card_torsion_eq_sq_of_wronskian_of_pair [DecidableEq F] [IsAlgClosed F] [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hodd : Odd n) (hn : (n : F) ≠ 0) (hn0 : n ≠ 0)
    (hid : derivative (W.Φ (n : ℤ)) * W.ΨSq (n : ℤ) -
        W.Φ (n : ℤ) * derivative (W.ΨSq (n : ℤ)) =
      (n : F[X]) * W.preΨ (n : ℤ) * W.preΩ (n : ℤ))
    (hpair : ∀ x y : F, W.Equation x y → (W.ψ (n : ℤ)).evalEval x y = 0 →
      (W.ψ ((n : ℤ) + 2)).evalEval x y * (W.ψ ((n : ℤ) - 1)).evalEval x y ^ 2 =
        -((W.ψ ((n : ℤ) - 2)).evalEval x y * (W.ψ ((n : ℤ) + 1)).evalEval x y ^ 2)) :
    Nat.card (W.torsion n) = n ^ 2 :=
  card_torsion_eq_sq_of_wronskian h2 hodd hn hid (isCoprime_preΨ_preΩ h2 hodd hn0 hpair)


-- @@ L315-315 verbatim
end WeierstrassCurve.Affine


-- @@ L317-328 verbatim
/-! ## ⚠️ Non-vacuity of the Wronskian hypothesis, and a measurement of what proving it costs

`hid` is an implication's hypothesis, so it is worth knowing that it is **not** vacuous.  It is
proved outright below at `n = 1` and `n = 2`, by expanding both sides.

⚠️ **And the measurement, which is the more useful half.**  The same script at `n = 3` — the first
index where `Φₙ` and `ΨSqₙ` are not small — **exceeds `maxRecDepth` inside the `C`-normalisation,
before `ring` is even reached**, in 20 s.  Raising `maxRecDepth` is a `set_option` and this
development does not use them.  So `#1506` scope item 1 cannot be done index by index and cannot be
done by expansion: it needs the `normEDS` induction or the universal-curve route, and a worker who
starts by trying `n = 5` directly will only rediscover this.
-/


-- @@ L330-330 verbatim
namespace WeierstrassCurve


-- @@ L332-332 verbatim
open Polynomial


-- @@ L334-335 verbatim
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])


-- @@ L337-337 verbatim
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


-- @@ L339-349 verbatim
/-- The Wronskian identity at `n = 1`, over an arbitrary commutative ring.  `Φ₁ = X`, `ΨSq₁ = 1`
and `preΩ₁ = 1`, so both sides are `1`. -/
example : derivative (W.Φ 1) * W.ΨSq 1 - W.Φ 1 * derivative (W.ΨSq 1)
    = (1 : R[X]) * W.preΨ 1 * W.preΩ 1 := by
  have h : W.preΩ 1 = 1 := by
    rw [preΩ, show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num,
      show (1 : ℤ) - 2 = -1 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, preΨ_zero, preΨ_two,
      preΨ_neg, preΨ_one]
    ring
  rw [Φ_one, ΨSq_one, preΨ_one, h]
  simp


-- @@ L351-361 verbatim
/-- The Wronskian identity at `n = 2`, over an arbitrary commutative ring — `Φ₂′·Ψ₂Sq −
Φ₂·Ψ₂Sq′ = 2·preΨ₄`, both sides expanded in the `bᵢ`.  ⚠️ This is the first index that is not
formal, and it is the last one that expands within the default `maxRecDepth`. -/
example : derivative (W.Φ 2) * W.ΨSq 2 - W.Φ 2 * derivative (W.ΨSq 2)
    = (2 : R[X]) * W.preΨ 2 * W.preΩ 2 := by
  rw [Φ_two, ΨSq_two, preΨ_two, preΩ_two, Ψ₂Sq, preΨ₄, b₂, b₄, b₆, b₈]
  simp only [derivative_sub, derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C, Nat.cast_ofNat]
  C_simp
  push_cast
  ring


-- @@ L363-363 verbatim
end WeierstrassCurve
