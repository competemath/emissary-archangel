module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IntegerCoords


-- @@ L4-15 verbatim
/-!
# Basic lemmas about `scaledCoord`

This file relates `coord` and `scaledCoord` and records that, in an orthonormal frame, equality of
all scaled coordinates determines the vector.

## Main statements
* `sqrt8_ne_zero`
* `coord_eq_scaledCoord_div_sqrt8`
* `scaledCoord_sub`
* `eq_of_scaledCoord_eq`
-/


-- @@ L17-17 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open scoped RealInnerProductSpace


-- @@ L23-23 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L25-28 verbatim
/-- `Real.sqrt 8` is nonzero. -/
public lemma sqrt8_ne_zero : (Real.sqrt 8 : ℝ) ≠ 0 := by
  have : (0 : ℝ) < 8 := by norm_num
  exact Real.sqrt_ne_zero'.2 this


-- @@ L30-34 verbatim
/-- The coordinate `coord e i x` is `scaledCoord e i x / √8`. -/
public lemma coord_eq_scaledCoord_div_sqrt8
    (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x : ℝ²⁴) :
    coord e i x = scaledCoord e i x / Real.sqrt 8 := by
  simp [scaledCoord]


-- @@ L36-39 verbatim
/-- `scaledCoord` is additive with respect to subtraction. -/
public lemma scaledCoord_sub (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x y : ℝ²⁴) :
    scaledCoord e i (x - y) = scaledCoord e i x - scaledCoord e i y := by
  simp [scaledCoord, coord, inner_sub_right, mul_sub]


-- @@ L41-56 verbatim
/-- In an orthonormal frame, a vector is determined by its `scaledCoord` values. -/
public lemma eq_of_scaledCoord_eq
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) {x y : ℝ²⁴}
    (h : ∀ i : Fin 24, scaledCoord e i x = scaledCoord e i y) :
    x = y := by
  have hcoord : ∀ i : Fin 24, coord e i x = coord e i y := by
    intro i
    have := congrArg (fun t : ℝ => t / Real.sqrt 8) (h i)
    simpa [coord_eq_scaledCoord_div_sqrt8] using this
  calc
    x = ∑ i : Fin 24, (coord e i x) • e i := coord_eq_of_orthonormal e he x
    _ = ∑ i : Fin 24, (coord e i y) • e i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [hcoord i]
    _ = y := (coord_eq_of_orthonormal e he y).symm


-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
