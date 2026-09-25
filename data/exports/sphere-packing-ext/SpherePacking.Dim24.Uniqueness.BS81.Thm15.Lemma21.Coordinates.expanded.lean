module
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


-- @@ L5-18 verbatim
/-!
# Coordinates in a `D₂₄` frame

In BS81 Lemma 21 we work in `ℝ²⁴` with an orthonormal frame `e : Fin 24 → ℝ²⁴` coming from the
embedding `D₂₄ ⊆ latticeL C` (Lemma 20). This file defines the coordinate function `coord` and
records the basic expansions in an orthonormal basis (coordinate formula and Parseval).

## Main definitions
* `coord`

## Main statements
* `coord_eq_of_orthonormal`
* `norm_sq_eq_sum_coord_sq`
-/



-- @@ L21-21 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open scoped RealInnerProductSpace Pointwise


-- @@ L27-27 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L29-31 verbatim
/-- Coordinates of a vector in an orthonormal frame `e : Fin 24 → ℝ²⁴`. -/
@[expose] public def coord (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x : ℝ²⁴) : ℝ :=
  ⟪e i, x⟫


-- @@ L33-40 verbatim
private lemma top_le_span_range_of_orthonormal (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) :
    (⊤ : Submodule ℝ ℝ²⁴) ≤ Submodule.span ℝ (Set.range e) := by
  have htop : Submodule.span ℝ (Set.range e) = ⊤ := by
    have hcard : Fintype.card (Fin 24) = Module.finrank ℝ ℝ²⁴ := by
      -- `finrank(ℝ²⁴) = 24`
      simp [finrank_euclideanSpace]
    exact he.linearIndependent.span_eq_top_of_card_eq_finrank hcard
  exact htop.ge


-- @@ L42-49 verbatim
/-- Expansion of a vector in an orthonormal frame via the coordinates `coord`. -/
public theorem coord_eq_of_orthonormal
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) (x : ℝ²⁴) :
    x = ∑ i : Fin 24, (coord e i x) • e i := by
  let b : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ :=
    OrthonormalBasis.mk he (top_le_span_range_of_orthonormal e he)
  -- Expand `x` in the orthonormal basis and rewrite `coord`.
  simpa [coord, b, OrthonormalBasis.coe_mk] using (OrthonormalBasis.sum_repr' b x).symm


-- @@ L51-59 verbatim
/-- Parseval's identity: the squared norm is the sum of squared coordinates in an orthonormal
frame. -/
public theorem norm_sq_eq_sum_coord_sq
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) (x : ℝ²⁴) :
    ‖x‖ ^ 2 = ∑ i : Fin 24, (coord e i x) ^ 2 := by
  let b : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ :=
    OrthonormalBasis.mk he (top_le_span_range_of_orthonormal e he)
  -- Parseval in the orthonormal basis.
  simpa [coord, b, OrthonormalBasis.coe_mk] using (OrthonormalBasis.sum_sq_inner_right b x).symm


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
