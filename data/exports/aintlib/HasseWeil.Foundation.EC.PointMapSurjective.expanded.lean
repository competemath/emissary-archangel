/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.Frobenius.FrobeniusFixedPoint


-- @@ L8-32 verbatim
/-!
# Surjectivity of `Affine.Point.map` and the geometric Frobenius over `K̄`

Mathlib's `WeierstrassCurve.Affine.Point.map f : W'⟮F⟯ →+ W'⟮K⟯` (induced by a field hom
`f : F →ₐ[S] K`) is **surjective whenever `f` is surjective**: a target point `some x' y' h'` lifts
to `some x y h` with `f x = x'`, `f y = y'`, whose source-nonsingularity is `baseChange_nonsingular`
applied to `h'`.

The payoff is **the geometric Frobenius `geomFrobeniusPoint W = Affine.Point.map (Frobenius)` over
`L = AlgebraicClosure K` is bijective** (`geomFrobeniusPoint_bijective` /
`geomFrobeniusPoint_surjective`): the `q`-power Frobenius `K`-algebra hom of `K̄` is the underlying
map of the automorphism `frobeniusAlgEquivOfAlgebraic K K̄` (`Gal(K̄/K)`, since `K̄/K`
is algebraic),
hence bijective; surjectivity transfers through `Point.map`.

This is the elementary half of Silverman III.4.10a for the Frobenius factor.  (It does **not**
discharge surjectivity of `1 − π` or `r·π − s`, which is the Lang/finite-morphism content: see
`HasseWeil/WeilPairing/SeparableWitnesses.lean`.)  It is a reusable building block.

## References

* mathlib: `WeierstrassCurve.Affine.Point.map`, `WeierstrassCurve.Affine.baseChange_nonsingular`,
  `FiniteField.frobeniusAlgEquivOfAlgebraic`.
* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10a.
-/


-- @@ L34-34 verbatim
open WeierstrassCurve


-- @@ L36-36 verbatim
namespace HasseWeil


-- @@ L38-38 verbatim
/-! ### Surjectivity of mathlib's `Affine.Point.map` -/


-- @@ L40-40 verbatim
section MapSurjective


-- @@ L42-45 verbatim
variable {R S F K : Type*} [CommRing R] [CommRing S] {W' : WeierstrassCurve R}
  [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
  [Algebra R K] [Algebra S K] [IsScalarTower R S K]


-- @@ L47-68 verbatim
/-- **`Affine.Point.map` of a surjective field hom is surjective.**  For `f : F →ₐ[S] K` surjective,
the induced group hom `W'⟮F⟯ →+ W'⟮K⟯` is onto: a target `some x' y' h'` is the image of
`some x y h`, where `x, y` are `f`-preimages of `x', y'` and `h` is `h'` transported back through
`WeierstrassCurve.Affine.baseChange_nonsingular f.injective`. -/
theorem affinePointMap_surjective {f : F →ₐ[S] K} (hf : Function.Surjective f) :
    Function.Surjective (WeierstrassCurve.Affine.Point.map (W' := W') f) := by
  rintro (_ | ⟨x', y', h'⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨x, hx⟩ := hf x'
    obtain ⟨y, hy⟩ := hf y'
    -- Source-nonsingularity from target-nonsingularity (transport across `f`, injective).
    -- `baseChange_nonsingular` wants `f` as an `R`-algebra hom; restrict scalars (same map).
    have hns : (W'.baseChange F).toAffine.Nonsingular x y := by
      have h'' : (W'.baseChange K).toAffine.Nonsingular
          ((f.restrictScalars R) x) ((f.restrictScalars R) y) := by
        show (W'.baseChange K).toAffine.Nonsingular (f x) (f y)
        rw [hx, hy]; exact h'
      exact (WeierstrassCurve.Affine.baseChange_nonsingular (W := W')
        (f := f.restrictScalars R) (f.restrictScalars R).injective x y).mp h''
    refine ⟨WeierstrassCurve.Affine.Point.some x y hns, ?_⟩
    rw [WeierstrassCurve.Affine.Point.map_some]
    exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hx, hy⟩


-- @@ L70-70 verbatim
end MapSurjective


-- @@ L72-72 verbatim
/-! ### The geometric Frobenius over `K̄` is bijective -/


-- @@ L74-74 verbatim
section GeomFrobenius


-- @@ L76-76 verbatim
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

-- @@ L77-78 verbatim
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
  [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]


-- @@ L80-81 verbatim
noncomputable local instance instDecEqACSurjFrob : DecidableEq (AlgebraicClosure K) :=
  Classical.decEq _


-- @@ L83-96 verbatim
omit [DecidableEq K] in
/-- **The geometric Frobenius `K`-algebra hom of `K̄` is surjective.**  It is the underlying map of
the automorphism `FiniteField.frobeniusAlgEquivOfAlgebraic K K̄` (`K̄/K` algebraic ⟹ the
`q`-power is
an automorphism), so it is bijective; here we record surjectivity. -/
theorem frobeniusAlgHom_surjective_algebraicClosure :
    Function.Surjective
      (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) := by
  -- The `q`-power AlgHom and the `q`-power AlgEquiv (`frobeniusAlgEquivOfAlgebraic`) agree as maps.
  have hcoe : ⇑(FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) =
      ⇑(FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
    rw [FiniteField.coe_frobeniusAlgHom, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  rw [hcoe]
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).surjective


-- @@ L98-108 verbatim
omit [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [DecidableEq K] in
/-- **The geometric Frobenius point map over `K̄` is surjective** (Silverman III.4.10a, Frobenius
factor).  `geomFrobeniusPoint W = Affine.Point.map (Frobenius)` and the Frobenius `K`-algebra hom of
`K̄` is surjective (`frobeniusAlgHom_surjective_algebraicClosure`), so `affinePointMap_surjective`
applies. -/
theorem geomFrobeniusPoint_surjective :
    Function.Surjective (geomFrobeniusPoint W) := by
  change Function.Surjective (WeierstrassCurve.Affine.Point.map (W' := W)
    (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)))
  exact affinePointMap_surjective (W' := W) frobeniusAlgHom_surjective_algebraicClosure


-- @@ L110-121 verbatim
omit [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [DecidableEq K] in
/-- **The geometric Frobenius point map over `K̄` is bijective.**  Surjective by
`geomFrobeniusPoint_surjective`; injective as `Affine.Point.map` of an injective field hom
(`WeierstrassCurve.Affine.Point.map_injective`). -/
theorem geomFrobeniusPoint_bijective :
    Function.Bijective (geomFrobeniusPoint W) := by
  refine ⟨?_, geomFrobeniusPoint_surjective W⟩
  change Function.Injective (WeierstrassCurve.Affine.Point.map (W' := W)
    (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)))
  exact WeierstrassCurve.Affine.Point.map_injective
    (FiniteField.frobeniusAlgHom K (AlgebraicClosure K))


-- @@ L123-123 verbatim
end GeomFrobenius


-- @@ L125-125 verbatim
end HasseWeil
