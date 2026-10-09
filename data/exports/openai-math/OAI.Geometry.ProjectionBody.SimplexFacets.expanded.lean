import OAI.Geometry.ProjectionBody.ConvexGeometry
import OAI.Geometry.ProjectionBody.FacetCover
import Mathlib.Analysis.InnerProductSpace.Projection.Basic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open Set


-- @@ L10-10 verbatim
namespace ProjectionCounterexample


-- @@ L12-16 verbatim
/-- Coordinate linear functional on the Euclidean space. -/
def coordinateFunctional {d : ℕ} (i : Fin d) : E d →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L18-19 verbatim
@[simp] theorem coordinateFunctional_apply {d : ℕ} (i : Fin d) (x : E d) :
    coordinateFunctional i x = x i := rfl


-- @@ L21-24 verbatim
/-- Outward defining functionals: the sum facet, then the coordinate facets. -/
def simplexFunctional (d : ℕ) : Option (Fin d) → E d →ₗ[ℝ] ℝ
  | none => ∑ i, coordinateFunctional i
  | some i => -coordinateFunctional i


-- @@ L26-28 verbatim
def simplexLevel {d : ℕ} : Option (Fin d) → ℝ
  | none => 1
  | some _ => 0


-- @@ L30-32 verbatim
@[simp] theorem simplexFunctional_none (d : ℕ) (x : E d) :
    simplexFunctional d none x = ∑ i, x i := by
  simp [simplexFunctional]


-- @@ L34-35 verbatim
@[simp] theorem simplexFunctional_some {d : ℕ} (i : Fin d) (x : E d) :
    simplexFunctional d (some i) x = -x i := rfl


-- @@ L37-52 verbatim
theorem simplex_eq_halfspaceBody (d : ℕ) :
    simplex d = halfspaceBody (simplexFunctional d) simplexLevel := by
  rw [simplex_eq_coordinates]
  ext x
  constructor
  · rintro ⟨hx, hs⟩ i
    cases i with
    | none => simpa [simplexLevel] using hs
    | some i => simpa [simplexLevel] using neg_nonpos.mpr (hx i)
  · intro hx
    constructor
    · intro i
      have := hx (some i)
      simpa [simplexLevel] using this
    · have := hx none
      simpa [simplexLevel] using this


-- @@ L54-71 verbatim
/-- Every nonzero direction has a visible defining facet of the simplex. -/
theorem simplex_has_positive_slope {d : ℕ} {u : E d} (hu : u ≠ 0) :
    ∃ i, 0 < simplexFunctional d i u := by
  by_contra h
  have hall (i : Option (Fin d)) : simplexFunctional d i u ≤ 0 :=
    le_of_not_gt (fun hi => h ⟨i, hi⟩)
  have hcoords (i : Fin d) : 0 ≤ u i := by
    have := hall (some i)
    simpa using this
  have hsum : ∑ i, u i = 0 := by
    apply le_antisymm
    · simpa using hall none
    · exact Finset.sum_nonneg fun i _ => hcoords i
  have hzero : ∀ i : Fin d, u i = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hcoords i)).mp hsum
  apply hu
  ext i
  exact hzero i


-- @@ L73-75 verbatim
theorem simplex_functional_balance {d : ℕ} (u : E d) :
    ∑ i, simplexFunctional d i u = 0 := by
  simp [Fintype.sum_option, Finset.sum_neg_distrib]


-- @@ L77-79 verbatim
theorem simplex_absolute_slopes {d : ℕ} (u : E d) :
    ∑ i, |simplexFunctional d i u| = (∑ i, |u i|) + |∑ i, u i| := by
  simp [Fintype.sum_option, add_comm]


-- @@ L81-85 verbatim
theorem simplex_boundingFace_coordinate {d : ℕ} (i : Fin d) :
    boundingFace (simplexFunctional d) simplexLevel (some i) =
      {x ∈ simplex d | x i = 0} := by
  ext x
  simp [boundingFace, ← simplex_eq_halfspaceBody, simplexLevel]


-- @@ L87-91 verbatim
theorem simplex_boundingFace_sum (d : ℕ) :
    boundingFace (simplexFunctional d) simplexLevel none =
      {x ∈ simplex d | ∑ i, x i = 1} := by
  ext x
  simp [boundingFace, ← simplex_eq_halfspaceBody, simplexLevel]


-- @@ L93-93 verbatim
end ProjectionCounterexample


-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
end OAI
