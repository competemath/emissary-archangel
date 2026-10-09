import OAI.Geometry.ProjectionBody.ProductFacetCharts
import OAI.Geometry.ProjectionBody.ProductFacetIndices


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped RealInnerProductSpace


-- @@ L9-9 verbatim
namespace ProjectionCounterexample


-- @@ L11-15 verbatim
lemma firstBlock_productFacetLinear_first (i : Option (Fin 10)) (x : E 19) :
    firstBlock (productFacetLinear (false, i) x) =
      simplexFacetLinear 9 i ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).1 := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (false, i) x)).1 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]


-- @@ L17-21 verbatim
lemma secondBlock_productFacetLinear_first (i : Option (Fin 10)) (x : E 19) :
    secondBlock (productFacetLinear (false, i) x) =
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).2 := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (false, i) x)).2 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]


-- @@ L23-27 verbatim
lemma firstBlock_productFacetLinear_second (i : Option (Fin 10)) (x : E 19) :
    firstBlock (productFacetLinear (true, i) x) =
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).1 := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (true, i) x)).1 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]


-- @@ L29-33 verbatim
lemma secondBlock_productFacetLinear_second (i : Option (Fin 10)) (x : E 19) :
    secondBlock (productFacetLinear (true, i) x) =
      simplexFacetLinear 9 i ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).2 := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (true, i) x)).2 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]


-- @@ L35-56 verbatim
lemma productFacetLinear_first_coordinate (i : Fin 10) :
    productFacetLinear (false, some i) = (insertZero (i.castAdd 10)).toLinearMap := by
  ext x j
  induction j using (i.castAdd 10).succAboveCases
  · change firstBlock (productFacetLinear (false, some i) x) i = _
    rw [firstBlock_productFacetLinear_first]
    simp [simplexFacetLinear]
  · rename_i j
    simp only [LinearIsometry.coe_toLinearMap]
    rw [insertZero_succAbove]
    induction j using Fin.addCases (m := 9) (n := 10) with
    | left j =>
      rw [first_succAbove_first]
      change firstBlock (productFacetLinear (false, some i) x) (i.succAbove j) = _
      rw [firstBlock_productFacetLinear_first]
      simp only [simplexFacetLinear, LinearIsometry.coe_toLinearMap, insertZero_succAbove]
      rfl
    | right j =>
      rw [first_succAbove_second]
      change secondBlock (productFacetLinear (false, some i) x) j = _
      rw [secondBlock_productFacetLinear_first]
      rfl


-- @@ L58-79 verbatim
lemma productFacetLinear_second_coordinate (i : Fin 10) :
    productFacetLinear (true, some i) = (insertZero (i.natAdd 10)).toLinearMap := by
  ext x j
  induction j using (i.natAdd 10).succAboveCases
  · change secondBlock (productFacetLinear (true, some i) x) i = _
    rw [secondBlock_productFacetLinear_second]
    simp [simplexFacetLinear]
  · rename_i j
    simp only [LinearIsometry.coe_toLinearMap]
    rw [insertZero_succAbove]
    induction j using Fin.addCases (m := 10) (n := 9) with
    | left j =>
      rw [second_succAbove_first]
      change firstBlock (productFacetLinear (true, some i) x) j = _
      rw [firstBlock_productFacetLinear_second]
      rfl
    | right j =>
      rw [second_succAbove_second]
      change secondBlock (productFacetLinear (true, some i) x) (i.succAbove j) = _
      rw [secondBlock_productFacetLinear_second]
      simp only [simplexFacetLinear, LinearIsometry.coe_toLinearMap, insertZero_succAbove]
      rfl


-- @@ L81-82 verbatim
/-- Graph coefficient vector for the first block's sum facet. -/
def firstSumGraph : E 19 := (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (allOnes 9, 0)


-- @@ L84-85 verbatim
/-- Graph coefficient vector for the second block's sum facet. -/
def secondSumGraph : E 19 := (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (0, allOnes 9)


-- @@ L87-93 verbatim
lemma inner_firstSumGraph (x : E 19) :
    ⟪firstSumGraph, x⟫ = ⟪allOnes 9, ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10) x).1⟫ := by
  rw [DiagonalZonotope.inner_finAdd 9 10]
  have h : (@EuclideanSpace.finAddEquivProd ℝ _ 9 10) firstSumGraph =
      (allOnes 9, 0) := (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).apply_symm_apply _
  rw [h]
  simp only [inner_zero_left, add_zero]


-- @@ L95-101 verbatim
lemma inner_secondSumGraph (x : E 19) :
    ⟪secondSumGraph, x⟫ = ⟪allOnes 9, ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9) x).2⟫ := by
  rw [DiagonalZonotope.inner_finAdd 10 9]
  have h : (@EuclideanSpace.finAddEquivProd ℝ _ 10 9) secondSumGraph =
      (0, allOnes 9) := (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).apply_symm_apply _
  rw [h]
  simp only [inner_zero_left, zero_add]


-- @@ L103-124 verbatim
lemma productFacetLinear_first_sum :
    productFacetLinear (false, none) = graphLinear ((Fin.last 9).castAdd 10) firstSumGraph := by
  ext x j
  induction j using ((Fin.last 9).castAdd 10).succAboveCases
  · rw [graphLinear_same, inner_firstSumGraph]
    change firstBlock (productFacetLinear (false, none) x) (Fin.last 9) = _
    rw [firstBlock_productFacetLinear_first]
    simp [simplexFacetLinear]
  · rename_i j
    rw [graphLinear_succAbove]
    induction j using Fin.addCases (m := 9) (n := 10) with
    | left j =>
      rw [first_succAbove_first]
      change firstBlock (productFacetLinear (false, none) x) ((Fin.last 9).succAbove j) = _
      rw [firstBlock_productFacetLinear_first]
      simp only [simplexFacetLinear, graphLinear_succAbove]
      rfl
    | right j =>
      rw [first_succAbove_second]
      change secondBlock (productFacetLinear (false, none) x) j = _
      rw [secondBlock_productFacetLinear_first]
      rfl


-- @@ L126-147 verbatim
lemma productFacetLinear_second_sum :
    productFacetLinear (true, none) = graphLinear ((Fin.last 9).natAdd 10) secondSumGraph := by
  ext x j
  induction j using ((Fin.last 9).natAdd 10).succAboveCases
  · rw [graphLinear_same, inner_secondSumGraph]
    change secondBlock (productFacetLinear (true, none) x) (Fin.last 9) = _
    rw [secondBlock_productFacetLinear_second]
    simp [simplexFacetLinear]
  · rename_i j
    rw [graphLinear_succAbove]
    induction j using Fin.addCases (m := 10) (n := 9) with
    | left j =>
      rw [second_succAbove_first]
      change firstBlock (productFacetLinear (true, none) x) j = _
      rw [firstBlock_productFacetLinear_second]
      rfl
    | right j =>
      rw [second_succAbove_second]
      change secondBlock (productFacetLinear (true, none) x) ((Fin.last 9).succAbove j) = _
      rw [secondBlock_productFacetLinear_second]
      simp only [simplexFacetLinear, graphLinear_succAbove]
      rfl


-- @@ L149-152 verbatim
@[simp] lemma blockJoin_first {n m : ℕ} (x : E n) (y : E m) (i : Fin n) :
    (@EuclideanSpace.finAddEquivProd ℝ _ n m).symm (x, y) (i.castAdd m) = x i := by
  exact congrArg (fun z : E n × E m => z.1 i)
    ((@EuclideanSpace.finAddEquivProd ℝ _ n m).apply_symm_apply (x, y))


-- @@ L154-157 verbatim
@[simp] lemma blockJoin_second {n m : ℕ} (x : E n) (y : E m) (i : Fin m) :
    (@EuclideanSpace.finAddEquivProd ℝ _ n m).symm (x, y) (i.natAdd n) = y i := by
  exact congrArg (fun z : E n × E m => z.2 i)
    ((@EuclideanSpace.finAddEquivProd ℝ _ n m).apply_symm_apply (x, y))


-- @@ L159-161 verbatim
lemma graphNormal_succAbove {n : ℕ} (i : Fin (n + 1)) (a : E n) (j : Fin n) :
    graphNormal i a (i.succAbove j) = a j := by
  simp [graphNormal]


-- @@ L163-177 verbatim
lemma firstSumGraph_normal :
    graphNormal ((Fin.last 9).castAdd 10) firstSumGraph =
      (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm (allOnes 10, 0) := by
  ext j
  induction j using ((Fin.last 9).castAdd 10).succAboveCases
  · rw [graphNormal_same, blockJoin_first]
    rfl
  · rename_i j
    rw [graphNormal_succAbove]
    induction j using Fin.addCases (m := 9) (n := 10) with
    | left j =>
      rw [first_succAbove_first (Fin.last 9) j, firstSumGraph, blockJoin_first, blockJoin_first]
      rfl
    | right j =>
      rw [first_succAbove_second (Fin.last 9) j, firstSumGraph, blockJoin_second, blockJoin_second]


-- @@ L179-193 verbatim
lemma secondSumGraph_normal :
    graphNormal ((Fin.last 9).natAdd 10) secondSumGraph =
      (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm (0, allOnes 10) := by
  ext j
  induction j using ((Fin.last 9).natAdd 10).succAboveCases
  · rw [graphNormal_same, blockJoin_second]
    rfl
  · rename_i j
    rw [graphNormal_succAbove]
    induction j using Fin.addCases (m := 10) (n := 9) with
    | left j =>
      rw [second_succAbove_first (Fin.last 9) j, secondSumGraph, blockJoin_first, blockJoin_first]
    | right j =>
      rw [second_succAbove_second (Fin.last 9) j, secondSumGraph, blockJoin_second, blockJoin_second]
      rfl


-- @@ L195-200 verbatim
lemma firstSumGraph_normal_inner (u : E 20) :
    ⟪graphNormal ((Fin.last 9).castAdd 10) firstSumGraph, u⟫ =
      simplexFunctional 10 none (firstBlock u) := by
  rw [firstSumGraph_normal, DiagonalZonotope.inner_finAdd 10 10,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [inner_zero_left, add_zero, inner_allOnes, firstBlock_finAdd, simplexFunctional_none]


-- @@ L202-207 verbatim
lemma secondSumGraph_normal_inner (u : E 20) :
    ⟪graphNormal ((Fin.last 9).natAdd 10) secondSumGraph, u⟫ =
      simplexFunctional 10 none (secondBlock u) := by
  rw [secondSumGraph_normal, DiagonalZonotope.inner_finAdd 10 10,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [inner_zero_left, zero_add, inner_allOnes, secondBlock_finAdd, simplexFunctional_none]


-- @@ L209-209 verbatim
end ProjectionCounterexample


-- @@ L211-211 verbatim
end


-- @@ L213-213 verbatim
end OAI
