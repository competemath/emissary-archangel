import OAI.Geometry.ProjectionBody.SimplexVolume
import OAI.Geometry.ProjectionBody.ProductFacetCharts


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open Set MeasureTheory


-- @@ L9-9 verbatim
namespace ProjectionCounterexample


-- @@ L11-15 verbatim
theorem volume_productBody :
    volume productBody = ENNReal.ofReal (1 / ((Nat.factorial 10 : ℝ) * Nat.factorial 10)) := by
  simpa only [productBody, simplex_eq_coordinates, firstBlock, secondBlock,
    Set.mem_ofPred_eq, WithLp.ofLp_toLp] using
    volume_euclideanSimplexProduct 10 10


-- @@ L17-28 verbatim
theorem volume_productFacetDomain (b : Bool) :
    volume (productFacetDomain b) =
      ENNReal.ofReal (1 / ((Nat.factorial 9 : ℝ) * Nat.factorial 10)) := by
  cases b
  · simpa only [productFacetDomain, simplex_eq_coordinates, Set.preimage,
      Set.mem_prod, Set.mem_ofPred_eq, DiagonalZonotope.finAddEquivProd_apply,
      WithLp.ofLp_toLp] using
      volume_euclideanSimplexProduct 9 10
  · simpa only [productFacetDomain, simplex_eq_coordinates, Set.preimage,
      Set.mem_prod, Set.mem_ofPred_eq, DiagonalZonotope.finAddEquivProd_apply, WithLp.ofLp_toLp,
      mul_comm] using
      volume_euclideanSimplexProduct 10 9


-- @@ L30-35 verbatim
theorem productFacetDomain_compact (b : Bool) : IsCompact (productFacetDomain b) := by
  cases b
  · exact (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).toHomeomorph.isCompact_preimage.mpr
      ((simplex_compact 9).prod (simplex_compact 10))
  · exact (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).toHomeomorph.isCompact_preimage.mpr
      ((simplex_compact 10).prod (simplex_compact 9))


-- @@ L37-37 verbatim
end ProjectionCounterexample


-- @@ L39-39 verbatim
end


-- @@ L41-41 verbatim
end OAI
