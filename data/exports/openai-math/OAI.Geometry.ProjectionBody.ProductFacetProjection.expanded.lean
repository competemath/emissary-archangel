import OAI.Geometry.ProjectionBody.ProductFacetGraphs
import OAI.Geometry.ProjectionBody.GraphProjection


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped RealInnerProductSpace


-- @@ L9-9 verbatim
namespace ProjectionCounterexample


-- @@ L11-33 verbatim
/-- The true projected area scale of each product facet chart. -/
theorem productFacetProjection_normDet (i : Bool × Option (Fin 10))
    {u : E 20} (hu : ‖u‖ = 1) :
    ((project u).toLinearMap.comp (productFacetLinear i)).normDet =
      |productFunctional i u| := by
  rcases i with ⟨b, i⟩
  cases b
  · cases i with
    | none =>
      rw [productFacetLinear_first_sum, graphProjection_normDet _ _ hu,
        firstSumGraph_normal_inner]
      rfl
    | some i =>
      rw [productFacetLinear_first_coordinate, coordinateProjection_normDet _ hu]
      simp [firstBlock]
  · cases i with
    | none =>
      rw [productFacetLinear_second_sum, graphProjection_normDet _ _ hu,
        secondSumGraph_normal_inner]
      rfl
    | some i =>
      rw [productFacetLinear_second_coordinate, coordinateProjection_normDet _ hu]
      simp [secondBlock]


-- @@ L35-35 verbatim
end ProjectionCounterexample


-- @@ L37-37 verbatim
end


-- @@ L39-39 verbatim
end OAI
