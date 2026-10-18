import OAI.AlgebraicGeometry.StableCoordinate.GradedPresentationMap
import OAI.AlgebraicGeometry.StableCoordinate.GradedPresentationKernel
import OAI.AlgebraicGeometry.StableCoordinate.PrincipalInitialRelation


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-12 verbatim
/-!
# The actual associated graded presentation for the source hypersurface

This identifies the Rees special fiber of the source quotient filtration with
the exact degeneration ring `Obstruction.G`, with its independent generators.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace StableCoordinate.AssociatedGradedPresentation


-- @@ L18-18 verbatim
open MvPolynomial Obstruction WeightedInitial Filtration GradedPresentationMap


-- @@ L20-26 verbatim
/-- The two source-weight APIs describe precisely the same integer weight. -/
theorem monomialWeight_eq_weight :
    Filtration.monomialWeight = Finsupp.weight presentationWeight := by
  apply Finsupp.addHom_ext
  intro i n
  rw [Finsupp.weight_single]
  fin_cases i <;> simp [Filtration.monomialWeight, presentationWeight ]


-- @@ L28-28 verbatim
variable (k : Type*) [CommRing k]


-- @@ L30-35 verbatim
/-- The span-of-monomials source filtration agrees with the coefficientwise
weighted filtration used to establish the leading-relation theorem. -/
theorem piece_eq_boundedSubmodule (d : ℤ) :
    Filtration.piece k d = boundedSubmodule presentationWeight d := by
  rw [boundedSubmodule_eq_span]
  simp only [Filtration.piece, monomialWeight_eq_weight]


-- @@ L37-37 verbatim
variable {k}

-- @@ L38-38 verbatim
variable {A : Type*} [CommRing A] [Algebra k A]


-- @@ L40-46 verbatim
/-- Every bounded image representative criterion is now proved for the actual
source filtration, rather than assumed for an abstract filtered algebra. -/
theorem imagePiece_mem_iff (φ : P k 5 →ₐ[k] A) (p : P k 5) (d : ℤ) :
    φ p ∈ imagePiece φ d ↔
      ∃ r : P k 5, Bounded presentationWeight r d ∧ φ r = φ p := by
  rw [imagePiece, piece_eq_boundedSubmodule]
  exact GradedPresentationKernel.mem_boundedImage_iff presentationWeight φ p d



-- @@ L49-56 verbatim
/-- The coefficient of the actual source Rees map is the image of the matching
weighted homogeneous component. -/
theorem reesMap_coeff_weighted (φ : P k 5 →ₐ[k] A) (p : P k 5) (d : ℤ) :
    (reesMap φ p : LaurentPolynomial A).coeff d =
      φ (weightedHomogeneousComponent presentationWeight d p) := by
  classical
  rw [reesMap_coeff, weightedHomogeneousComponent_apply, Finset.sum_filter]
  simp only [monomialWeight_eq_weight]


-- @@ L58-58 verbatim
variable (k)


-- @@ L60-61 verbatim
/-- The actual polynomial presentation map of the source hypersurface. -/
abbrev quotientMap : P k 5 →ₐ[k] Obstruction.A k := Ideal.Quotient.mkₐ k (idealA k)


-- @@ L63-64 verbatim
/-- The actual Rees associated graded algebra of the source image filtration. -/
abbrev associatedGraded := imageGr (quotientMap k)


-- @@ L66-68 verbatim
/-- The actual polynomial map onto the source's associated graded algebra. -/
abbrev gradedPresentationMap : P k 5 →ₐ[k] associatedGraded k :=
  gradedMap (quotientMap k)


-- @@ L70-70 verbatim
variable [IsDomain k]


-- @@ L72-82 verbatim
/-- Vanishing of an actual homogeneous symbol is exactly vanishing modulo the
exact relation `Hstar`. -/
theorem homogeneous_symbol_eq_zero_iff (p : P k 5) (d : ℤ)
    (hp : p.IsWeightedHomogeneous presentationWeight d) :
    quotientMap k p ∈ imagePiece (quotientMap k) (d - 1) ↔ p ∈ idealG k := by
  have h := GradedPresentationKernel.homogeneous_image_mem_lower_iff presentationWeight
    (quotientMap k) (imagePiece (quotientMap k)) (imagePiece_mem_iff (quotientMap k))
    (H k) 1 (PrincipalInitialRelation.H_isTopDegree k).1
    (PrincipalInitialRelation.H_isTopDegree k).2
    (by exact Ideal.Quotient.mkₐ_ker k (idealA k)) hp
  simpa only [idealA, idealG, H_degree_one_component k] using h



-- @@ L85-95 verbatim
/-- The full kernel of the actual polynomial map is exactly `(Hstar)`. -/
theorem gradedPresentation_ker :
    RingHom.ker (gradedPresentationMap k).toRingHom = idealG k := by
  have h := GradedPresentationKernel.kernel_eq_top_principal presentationWeight
    (quotientMap k) (imagePiece (quotientMap k)) (imagePiece_mono (quotientMap k))
    (imagePiece_mem_iff (quotientMap k)) (H k) 1
    (PrincipalInitialRelation.H_isTopDegree k).1
    (PrincipalInitialRelation.H_isTopDegree k).2
    (by exact Ideal.Quotient.mkₐ_ker k (idealA k))
    (reesMap (quotientMap k)) (reesMap_coeff_weighted (quotientMap k))
  simpa only [gradedPresentationMap, gradedMap, idealG, H_degree_one_component k] using h


-- @@ L97-101 verbatim
/-- The complete concrete associated-graded presentation, with no graded-domain
or source-presentation hypothesis added. -/
def associatedGradedEquiv : Obstruction.G k ≃ₐ[k] associatedGraded k :=
  (Ideal.quotientEquivAlgOfEq k (gradedPresentation_ker k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (gradedMap_surjective (quotientMap k)))


-- @@ L103-107 verbatim
@[simp]
theorem associatedGradedEquiv_mk (p : P k 5) :
    associatedGradedEquiv k (Ideal.Quotient.mk (idealG k) p) =
      gradedPresentationMap k p := by
  rfl


-- @@ L109-116 verbatim
/-- The presentation equivalence preserves the designated generator symbols. -/
@[simp]
theorem associatedGradedEquiv_gX (i : Fin 5) :
    associatedGradedEquiv k (gX k i) =
      FilteredRees.initial (imagePiece (quotientMap k)) (imagePiece_mono (quotientMap k))
        (monomialWeight (Finsupp.single i 1)) (variableElement (quotientMap k) i) := by
  rw [gX, associatedGradedEquiv_mk]
  exact gradedMap_X (quotientMap k) i


-- @@ L118-118 verbatim
end StableCoordinate.AssociatedGradedPresentation


-- @@ L120-120 verbatim
end


-- @@ L122-122 verbatim
end OAI
