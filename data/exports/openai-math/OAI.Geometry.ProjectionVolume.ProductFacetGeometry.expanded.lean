import OAI.Geometry.ProjectionVolume.ProductProjection


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set


-- @@ L7-7 verbatim
namespace Paper092


-- @@ L9-17 verbatim
theorem productFacet_inl_eq_preimage (a : Option (Fin 10)) :
    productFacet (.inl a) = splitBlocks ⁻¹' (simplexFacet 10 a ×ˢ standardSimplex 10) := by
  ext x
  change ((firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10) ∧
    simplexCoordinates (firstBlock x) a = 0) ↔
      ((firstBlock x ∈ standardSimplex 10 ∧ simplexCoordinates (firstBlock x) a = 0) ∧
        secondBlock x ∈ standardSimplex 10)
  exact ⟨fun ⟨⟨hx, hy⟩, ha⟩ => ⟨⟨hx, ha⟩, hy⟩,
    fun ⟨⟨hx, ha⟩, hy⟩ => ⟨⟨hx, hy⟩, ha⟩⟩


-- @@ L19-26 verbatim
theorem productFacet_inr_eq_preimage (a : Option (Fin 10)) :
    productFacet (.inr a) = splitBlocks ⁻¹' (standardSimplex 10 ×ˢ simplexFacet 10 a) := by
  ext x
  change ((firstBlock x ∈ standardSimplex 10 ∧ secondBlock x ∈ standardSimplex 10) ∧
    simplexCoordinates (secondBlock x) a = 0) ↔
      (firstBlock x ∈ standardSimplex 10 ∧
        (secondBlock x ∈ standardSimplex 10 ∧ simplexCoordinates (secondBlock x) a = 0))
  exact and_assoc


-- @@ L28-28 verbatim
end Paper092


-- @@ L30-30 verbatim
end OAI
