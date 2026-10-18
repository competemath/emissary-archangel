/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Genl.GeneralPosition.HeightTheory


-- @@ L8-51 verbatim
/-!
# The arithmetic-geometric inputs to the proof of Theorem 2.1

The proof of the implication (ii) ⇒ (i) of Theorem 2.1 of [mochizuki2010] consumes a
number of substantial inputs from arithmetic geometry, all of which are external to the
formal ε-bookkeeping of the proof itself:

- the existence of connected finite étale Galois coverings of hyperbolic curves that are
  ramified at prescribed points with prescribed ramification index (a consequence of the
  structure of étale fundamental groups of hyperbolic curves in characteristic zero),
  together with the comparison of heights, log-differents and log-conductors along such
  coverings (Propositions 1.4, 1.6, 1.7 of [mochizuki2010]);
- the theory of noncritical Belyi maps ([mochizuki2004], Theorem 2.5), combined with a
  compactness argument for the sets of local points at the places of a finite set `V`, and
  again Propositions 1.4, 1.6, 1.7 of [mochizuki2010].

This file records these inputs as the two fields of the structure
`Genl.HeightTheory.ProofPackage`:

- `Covering X d ε'` (packaged by the field `covering`) corresponds to the first paragraph
  of the proof of Theorem 2.1 (p. 13 of [mochizuki2010]): a Galois covering `Y → X`,
  ramified exactly over `D` with large ramification index, along which points of degree
  `≤ d` lift to points of degree `≤ d'`, heights compare via
  `ht_{ω_X(D)} ∘ π ≲ (1 + ε') ht_{ω_Y}`, and log-differents compare via Proposition 1.7 (i).
- `BelyiDescent X d ε` (packaged by the field `belyi`) corresponds to the second half of
  the proof (pp. 13–14 of [mochizuki2010]): if the inequality of statement (i) *fails* on
  `X(ℚ̄)^{=d}` for a hyperbolic `X` with `D = ∅`, there are a subset `Ξ ⊆ X(ℚ̄)^{=d}` on
  which the failure persists after dropping any bounded part, a noncritical Belyi map
  `φ : X → ℙ` mapping `Ξ` into a compactly bounded subset `K_V`, and the comparison
  (in)equalities of heights, log-differents and log-conductors along `φ` printed in the
  displayed chain on p. 14, with `E := φ^{-1}(C)_red` and a number `q > deg E / deg ω_X`
  (see `BelyiDescent` for why `q = deg E / deg ω_X` itself cannot be used).

Instantiating `ProofPackage` for the "true" height theory of curves over number fields
amounts to formalising §1 of [mochizuki2010] together with the noncritical Belyi maps of
[mochizuki2004]; this is tracked in the project blueprint.

## References

- [mochizuki2010] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), 1–28.
- [mochizuki2004] S. Mochizuki, *Noncritical Belyi maps*,
  Math. J. Okayama Univ. **46** (2004), 105–113.
-/


-- @@ L53-53 verbatim
universe u


-- @@ L55-55 verbatim
namespace Genl


-- @@ L57-57 verbatim
namespace HeightTheory


-- @@ L59-59 verbatim
variable (T : HeightTheory.{u})


-- @@ L61-92 expanded
/-- The output of the first paragraph of the proof of Theorem 2.1 of [mochizuki2010],
for a hyperbolic curve `(X, D)`, a degree bound `d` and a tolerance `ε' > 0`: a connected
finite étale Galois covering `Y → X` of the underlying curves, ramified at each point of
`E = (D ×_X Y)_red` with the same large ramification index `e`, considered as a divisor
free pair `(Y, ∅)`.

The fields `surjOn`, `logDiff_le` and `htCan_le` package, respectively: that every point
of `U_X(ℚ̄)^{≤d}` lifts to a point of `U_Y(ℚ̄)^{≤d'}` where `d' = d · deg(Y/X)`; the
comparison `log-diff_Y ≲ log-diff_X + log-cond_D` on `U_Y(ℚ̄)^{≤d'}` from
Proposition 1.7 (i); and the comparison `ht_{ω_X(D)} ∘ π ≲ (1 + ε') ht_{ω_Y}` on
`U_Y(ℚ̄)^{≤d'}` obtained from Propositions 1.4 (i), (ii), (iii) and 1.7 (ii) by choosing
the ramification index `e` sufficiently large. -/
structure Covering (X : T.Curve) (d : ℕ) (ε' : ℝ) where
  /-- The covering curve `Y`, regarded as the pair `(Y, ∅)`. -/
  Y : T.Curve
  /-- `Y` is again hyperbolic. -/
  hyperbolic : T.Hyperbolic Y
  /-- The divisor of the pair `(Y, ∅)` is empty. -/
  divisorFree : T.DivisorFree Y
  /-- The degree bound `d' = d · deg(Y/X)` for lifted points. -/
  d' : ℕ
  /-- The map `U_Y(ℚ̄) → U_X(ℚ̄)` induced by the covering `Y → X`. -/
  π : T.Pt Y → T.Pt X
  /-- Every point of `U_X(ℚ̄)^{≤d}` lifts to a point of `U_Y(ℚ̄)^{≤d'}`. -/
  surjOn : Set.SurjOn π (T.ptLE Y d') (T.ptLE X d)
  /-- Proposition 1.7 (i) of [mochizuki2010] applied to `Y → X`:
    `log-diff_Y ≲ log-diff_X + log-cond_D` on `U_Y(ℚ̄)^{≤d'}`. -/
  logDiff_le : DiscrepancyLE (T.logDiff Y) (T.logDiff X ∘ π + T.logCond X ∘ π) (T.ptLE Y d')
  /-- The height comparison `ht_{ω_X(D)} ∘ π ≲ (1 + ε') ht_{ω_Y}` on `U_Y(ℚ̄)^{≤d'}`,
    from `deg(ω_X(D)|_Y) ≤ (1 + ε') deg(ω_Y)` for `e` sufficiently large together with
    Propositions 1.4 (i), (ii), (iii) of [mochizuki2010]. -/
  htCan_le : DiscrepancyLE (T.htCan X ∘ π) ((1 + ε') • T.htCan Y) (T.ptLE Y d')


-- @@ L94-164 expanded
/-- The output of the second half of the proof of Theorem 2.1 of [mochizuki2010]
(pp. 13–14), for a divisor free hyperbolic curve `X` on which the inequality of statement
(i) fails on `X(ℚ̄)^{=d}` for the tolerance `ε`: a set `Ξ ⊆ X(ℚ̄)^{=d}` witnessing the
failure in the strong form `unbounded`, together with (the map on points of) a noncritical
Belyi map `φ : X → ℙ` that is unramified over `U_ℙ`, noncritical at the finitely many limit
tuples of `Ξ`, and maps `Ξ` into `K_V ∩ U_ℙ(ℚ̄)^{≤d'}` for a compactly bounded subset
`K_V` whose support contains `Σ`.

Writing `E = φ^{-1}(C)_red ⊆ X`, the remaining fields package the displayed comparisons
on p. 14 of [mochizuki2010], as (in)equalities of BD-classes on `Ξ`:

- `htCan_equiv`: `ht_{ω_X} ≈ ht_{ω_ℙ(C)} ∘ φ - ht_E`, from `φ^* ω_ℙ(C) ≅ ω_X(E)` and
  Proposition 1.4 (i), (iii);
- `logDiff_comp_le`: `log-diff_ℙ ∘ φ + log-cond_C ∘ φ ≲ log-diff_X + log-cond_E`, from
  Proposition 1.7 (i) applied to `φ` (with `e = 1`);
- `logCondE_le`: `log-cond_E ≲ ht_E`, from Proposition 1.6;
- `htE_le`: `ht_E ≲ q • ht_{ω_X}` for a real number `q > deg E / deg ω_X`.

Here `ht_E` denotes a representative of the BD-class of heights associated to the line
bundle `O_X(E)`, and `log-cond_E` the log-conductor of the pair `(X, E)`.

**On `htE_le`.** The chain printed on p. 14 of [mochizuki2010] uses
`ε' · ht_E ≈ ε' · (deg E / deg ω_X) · ht_{ω_X}`. For genuine Weil heights this fails in
general, even in the `≲` direction: `ht_E − (deg E / deg ω_X) · ht_{ω_X}` is (up to
`O(1)`) the height attached to the degree `0` class `E − (deg E / deg ω_X) · K_X` of
`Pic(X) ⊗ ℚ`, which is unbounded above and below on `X(ℚ̄)^{=d}` (it grows like the
square root of `ht_{ω_X}`, by the Néron–Tate theory of the Jacobian) as soon as this class
is not torsion. What does hold, by Proposition 1.4 (i), (ii), (iii) of loc. cit. (a line
bundle of positive degree on a curve has a height bounded below), is `ht_E ≲ q · ht_{ω_X}`
for every real `q > deg E / deg ω_X`. Since the proof only uses the upper bound
(and `q > 0` is arbitrary there), the field records exactly this. -/
structure BelyiDescent (X : T.Curve) (d : ℕ) (ε : ℝ) where
  /-- The subset `Ξ ⊆ X(ℚ̄)^{=d}` on which the inequality of statement (i) fails
    persistently. -/
  Ξ : Set (T.Pt X)
  /-- The map on algebraic points induced by the noncritical Belyi map `φ : X → ℙ`. -/
  φ : T.Pt X → T.Pt T.tripod
  /-- The compactly bounded subset `K_V ⊆ U_ℙ(ℚ̄)` produced from the images under `φ` of
    sufficiently small compact neighbourhoods of the limit tuples of `Ξ` at the places of
    `V ⊇ Σ`. -/
  K : T.CBS
  /-- A degree bound `d'` with `φ(Ξ) ⊆ U_ℙ(ℚ̄)^{≤d'}`. -/
  d' : ℕ
  /-- A representative of the BD-class of heights associated to `O_X(E)`,
    `E = φ^{-1}(C)_red`. -/
  htE : T.Pt X → ℝ
  /-- The log-conductor of the pair `(X, E)`. -/
  logCondE : T.Pt X → ℝ
  /-- A real number `q > deg E / deg ω_X` (for instance `deg E / deg ω_X + 1`). -/
  q : ℝ
  /-- `q` is positive. -/
  q_pos : 0 < q
  /-- `Ξ` consists of points of degree exactly `d`. -/
  subset : Ξ ⊆ T.ptEQ X d
  /-- The failure of the inequality of statement (i) persists on `Ξ` after enlarging the
    constant arbitrarily. -/
  unbounded : ∀ C : ℝ, ∃ x ∈ Ξ, (1 + ε) * T.logDiff X x + C < T.htCan X x
  /-- `φ` maps `Ξ` into `K_V ∩ U_ℙ(ℚ̄)^{≤d'}`. -/
  mapsTo : Set.MapsTo φ Ξ (T.cbsSet K ∩ T.ptLE T.tripod d')
  /-- `ht_{ω_X} ≈ ht_{ω_ℙ(C)} ∘ φ - ht_E` on `Ξ`, from `φ^* ω_ℙ(C) ≅ ω_X(E)` and
    Proposition 1.4 (i), (iii) of [mochizuki2010]. -/
  htCan_equiv : DiscrepancyEquiv (T.htCan X) (T.htCan T.tripod ∘ φ - htE) Ξ
  /-- `log-diff_ℙ ∘ φ + log-cond_C ∘ φ ≲ log-diff_X + log-cond_E` on `Ξ`, from
    Proposition 1.7 (i) of [mochizuki2010] applied to `φ` with `e = 1`. -/
  logDiff_comp_le :
    DiscrepancyLE (T.logDiff T.tripod ∘ φ + T.logCond T.tripod ∘ φ) (T.logDiff X + logCondE) Ξ
  /-- `log-cond_E ≲ ht_E` on `Ξ`, from Proposition 1.6 of [mochizuki2010]. -/
  logCondE_le : DiscrepancyLE logCondE htE Ξ
  /-- `ht_E ≲ q • ht_{ω_X}` on `Ξ`, from `deg E < q · deg ω_X` and
    Proposition 1.4 (i), (ii), (iii) of [mochizuki2010]. -/
  htE_le : DiscrepancyLE htE (q • T.htCan X) Ξ


-- @@ L166-178 expanded
/-- The arithmetic-geometric inputs to the proof of the implication (ii) ⇒ (i) of
Theorem 2.1 of [mochizuki2010]: the existence of the ramified coverings used in the
reduction to the divisor free case, and of the noncritical Belyi maps together with the
compactness argument used in the divisor free case. See `Covering` and `BelyiDescent` for
the precise content. -/
structure ProofPackage where
  /-- Ramified coverings with large ramification index exist (first paragraph of the
    proof of Theorem 2.1 of [mochizuki2010]). -/
  covering : ∀ X, T.Hyperbolic X → ∀ (d : ℕ) (ε' : ℝ), 0 < ε' → T.Covering X d ε'
  /-- Noncritical Belyi maps and the compactness argument (pp. 13–14 of the proof of
    Theorem 2.1 of [mochizuki2010]). -/
  belyi :
    ∀ X,
      T.Hyperbolic X →
        T.DivisorFree X →
          ∀ (d : ℕ) (ε : ℝ),
            0 < ε →
              ¬(DiscrepancyLE (T.htCan X) ((1 + ε) • T.logDiff X) (T.ptEQ X d)) →
                T.BelyiDescent X d ε


-- @@ L180-180 verbatim
end HeightTheory


-- @@ L182-182 verbatim
end Genl
