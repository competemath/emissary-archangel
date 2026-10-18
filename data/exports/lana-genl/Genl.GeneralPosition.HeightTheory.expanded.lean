/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Genl.Mathlib.Order.BoundedDiscrepancy


-- @@ L8-45 verbatim
/-!
# The height formalism of Mochizuki's "Arithmetic elliptic curves in general position"

This file introduces an abstract interface for the theory of heights on hyperbolic curves
over number fields, as reviewed in §1 of [mochizuki2010]. The interface `Genl.HeightTheory`
records exactly the data that is needed to *state* Theorem 2.1 of [mochizuki2010]:

- a type of "curves", to be thought of as pairs `(X, D)` of a smooth, proper, geometrically
  connected curve `X` over a number field together with a reduced effective divisor
  `D ⊆ X`, with `U_X := X \ D`;
- for each curve the set of algebraic points `U_X(ℚ̄)`, filtered by the degree
  `[F(x) : ℚ]` of the minimal field of definition `F(x)` of a point `x`
  (cf. Example 1.3 (i) of [mochizuki2010]);
- the predicates "`U_X` is a hyperbolic curve" (i.e. `deg ω_X(D) > 0`) and "`D = ∅`";
- the height `ht_{ω_X(D)}` associated to the log canonical bundle `ω_X(D)`
  (Definition 1.2 (i)), the log-different `log-diff_X` (Definition 1.5 (iii)) and the
  log-conductor `log-cond_D` (Definition 1.5 (iv)), all real valued functions on
  `U_X(ℚ̄)`;
- a distinguished curve, the *tripod* `(ℙ¹_ℚ, {0, 1, ∞})`, together with the collection of
  *compactly bounded subsets* `K_V ⊆ U_ℙ(ℚ̄)` whose support contains a fixed finite set of
  prime numbers `Σ` (Example 1.3 (ii)).

The set `Σ` of Theorem 2.1 of [mochizuki2010] is implicit in the field `CBS`: it does not
appear anywhere else in the statement of the theorem.

All functions are taken to be genuine functions rather than BD-classes; the statements
only refer to their BD-classes via the relations `≲[s]` and `≈[s]` of
`Genl.Mathlib.Order.BoundedDiscrepancy`.

Everything in this file is *data*; the substantial inputs from arithmetic geometry that
the proof of Theorem 2.1 consumes are recorded separately in
`Genl.GeneralPosition.ProofPackage`.

## References

- [mochizuki2010] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), 1–28.
-/


-- @@ L47-47 verbatim
universe u


-- @@ L49-49 verbatim
namespace Genl


-- @@ L51-95 verbatim
/-- An abstract height formalism in the sense of §1 of [mochizuki2010], containing the
data needed to state Theorem 2.1 of loc. cit.

A term `X : T.Curve` should be thought of as a pair `(X, D)` of a smooth, proper,
geometrically connected curve over a number field and a reduced effective divisor on it,
and `T.Pt X` as the set of algebraic points of `U_X = X \ D`. -/
structure HeightTheory where
  /-- The "curves" of the theory: pairs `(X, D)` of a smooth, proper, geometrically
  connected curve `X` over a number field and a reduced effective divisor `D ⊆ X`. -/
  Curve : Type u
  /-- The set of algebraic points `U_X(ℚ̄)` of `U_X = X \ D`. -/
  Pt : Curve → Type u
  /-- `U_X` is a hyperbolic curve, i.e. `deg ω_X(D) > 0`. -/
  Hyperbolic : Curve → Prop
  /-- The divisor `D` of the pair `(X, D)` is empty. -/
  DivisorFree : Curve → Prop
  /-- `ptLE X d` is the set `U_X(ℚ̄)^{≤d}` of points whose minimal field of definition
  has degree `≤ d` over `ℚ` (Example 1.3 (i) of [mochizuki2010]). -/
  ptLE : (X : Curve) → ℕ → Set (Pt X)
  /-- `ptEQ X d` is the set `U_X(ℚ̄)^{=d}` of points whose minimal field of definition
  has degree exactly `d` over `ℚ` (Example 1.3 (i) of [mochizuki2010]). -/
  ptEQ : (X : Curve) → ℕ → Set (Pt X)
  /-- There are no points of degree `≤ 0`. -/
  ptLE_zero : ∀ X, ptLE X 0 = ∅
  /-- `U_X(ℚ̄)^{≤ d + 1} = U_X(ℚ̄)^{≤ d} ∪ U_X(ℚ̄)^{= d + 1}`. -/
  ptLE_succ : ∀ X d, ptLE X (d + 1) = ptLE X d ∪ ptEQ X (d + 1)
  /-- A representative of the BD-class of height functions `ht_{ω_X(D)}` associated to
  the log canonical bundle `ω_X(D)` (Definition 1.2 (i), Proposition 1.4 (iii) of
  [mochizuki2010]). -/
  htCan : (X : Curve) → Pt X → ℝ
  /-- The log-different function `log-diff_X` (Definition 1.5 (iii) of
  [mochizuki2010]). -/
  logDiff : (X : Curve) → Pt X → ℝ
  /-- The log-conductor function `log-cond_D` (Definition 1.5 (iv) of
  [mochizuki2010]). -/
  logCond : (X : Curve) → Pt X → ℝ
  /-- The tripod `(ℙ¹_ℚ, {0, 1, ∞})`. -/
  tripod : Curve
  /-- The tripod is a hyperbolic curve. -/
  hyperbolic_tripod : Hyperbolic tripod
  /-- The collection of compactly bounded subsets `K_V ⊆ U_ℙ(ℚ̄)` whose support `V`
  contains the fixed finite set of primes `Σ` (Example 1.3 (ii) of [mochizuki2010]). -/
  CBS : Type u
  /-- The underlying set of algebraic points of a compactly bounded subset. -/
  cbsSet : CBS → Set (Pt tripod)


-- @@ L97-97 verbatim
namespace HeightTheory


-- @@ L99-99 verbatim
variable (T : HeightTheory)


-- @@ L101-110 expanded
/-- Statement (i) of Theorem 2.1 of [mochizuki2010]: the Effective Mordell/ABC/Vojta
conjecture. For every hyperbolic curve `U_X = X \ D` over a number field, every positive
integer `d` and every `ε > 0`, the inequality of BD-classes

`ht_{ω_X(D)} ≲ (1 + ε) (log-diff_X + log-cond_D)`

holds on `U_X(ℚ̄)^{≤d}`. -/
def StatementI : Prop :=
  ∀ X,
    T.Hyperbolic X →
      ∀ (d : ℕ) (ε : ℝ),
        0 < ε → DiscrepancyLE (T.htCan X) ((1 + ε) • (T.logDiff X + T.logCond X)) (T.ptLE X d)


-- @@ L112-123 expanded
/-- Statement (ii) of Theorem 2.1 of [mochizuki2010]: the ABC conjecture for
`Σ`-supported compactly bounded subsets. For every compactly bounded subset
`K_V ⊆ U_ℙ(ℚ̄)` whose support contains `Σ`, every positive integer `d` and every `ε > 0`,
the inequality of BD-classes

`ht_{ω_ℙ(C)} ≲ (1 + ε) (log-diff_ℙ + log-cond_C)`

holds on `K_V ∩ U_ℙ(ℚ̄)^{≤d}`, where `C = {0, 1, ∞} ⊆ ℙ = ℙ¹_ℚ`. -/
def StatementII : Prop :=
  ∀ (d : ℕ) (ε : ℝ),
    0 < ε →
      ∀ K : T.CBS,
        DiscrepancyLE (T.htCan T.tripod) ((1 + ε) • (T.logDiff T.tripod + T.logCond T.tripod))
          (T.cbsSet K ∩ T.ptLE T.tripod d)


-- @@ L125-125 verbatim
end HeightTheory


-- @@ L127-127 verbatim
end Genl
