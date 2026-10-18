import OAI.AlgebraicGeometry.StableCoordinate.LaurentPresentation
import OAI.AlgebraicGeometry.StableCoordinate.ModificationPieces


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-12 verbatim
/-!
# The degeneration embeds into the affine-modification Laurent model

This file uses the canonical source map from `LaurentPresentation` and
identifies its image with the extended Rees algebra.  Injectivity is supplied
by the separate localization/domain argument; it is not assumed here.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace StableCoordinate.ModificationEmbedding


-- @@ L18-18 verbatim
open MvPolynomial

-- @@ L19-19 verbatim
open scoped LaurentPolynomial


-- @@ L21-21 verbatim
namespace LP

-- @@ L22-22 verbatim
abbrev C {R : Type*} [CommRing R] := LaurentPolynomial.C (R := R)

-- @@ L23-23 verbatim
abbrev T {R : Type*} [CommRing R] := LaurentPolynomial.T (R := R)

-- @@ L24-24 verbatim
end LP


-- @@ L26-26 verbatim
open Obstruction


-- @@ L28-28 verbatim
variable (k : Type*) [CommRing k]


-- @@ L30-31 verbatim
/-- Alias for the canonical source-ordered Laurent coordinate values. -/
abbrev values := LaurentPresentation.laurentValues k


-- @@ L33-35 verbatim
/-- Polynomial evaluation before taking the degeneration quotient. -/
def polynomialMap : P k 5 →ₐ[k] LaurentPolynomial (B k) :=
  MvPolynomial.aeval (values k)


-- @@ L37-40 verbatim
@[simp]
theorem polynomialMap_X (i : Fin 5) :
    polynomialMap k (X i) = values k i :=
  MvPolynomial.aeval_X _ _


-- @@ L42-43 verbatim
/-- Alias for the canonical map from `G` to `B[τ,τ⁻¹]`. -/
abbrev toLaurent := LaurentPresentation.toLaurentBase k


-- @@ L45-48 verbatim
@[simp]
theorem toLaurent_mk (p : P k 5) :
    toLaurent k (Ideal.Quotient.mk (idealG k) p) = polynomialMap k p :=
  rfl


-- @@ L50-53 verbatim
@[simp]
theorem toLaurent_gX (i : Fin 5) :
    toLaurent k (gX k i) = values k i :=
  LaurentPresentation.toLaurentBase_gX k i


-- @@ L55-64 verbatim
theorem values_mem (i : Fin 5) :
    values k i ∈ ModificationPieces.modification (I k) := by
  fin_cases i
  · exact ModificationPieces.T_one_mem_modification _
  · exact (ModificationPieces.modification (I k)).algebraMap_mem _
  · exact (ModificationPieces.modification (I k)).algebraMap_mem _
  · apply ModificationPieces.numerator_mem_modification
    exact Ideal.subset_span (by simp)
  · apply ModificationPieces.numerator_mem_modification
    exact Ideal.subset_span (by simp)


-- @@ L66-77 verbatim
theorem polynomialMap_mem (p : P k 5) :
    polynomialMap k p ∈ ModificationPieces.modification (I k) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [polynomialMap, MvPolynomial.aeval_C, LaurentPolynomial.algebraMap_apply]
      exact (ModificationPieces.modification (I k)).algebraMap_mem _
  | add p q hp hq =>
      rw [map_add]
      exact (ModificationPieces.modification (I k)).add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul, polynomialMap_X]
      exact (ModificationPieces.modification (I k)).mul_mem hp (values_mem k i)


-- @@ L79-83 verbatim
/-- Every element of the actual source degeneration lands in the affine modification. -/
theorem toLaurent_mem (a : G k) :
    toLaurent k a ∈ ModificationPieces.modification (I k) := by
  induction a using Quotient.inductionOn with
  | h p => exact polynomialMap_mem k p


-- @@ L85-97 verbatim
/-- The source generator weights are exactly opposite their Laurent exponents. -/
theorem values_homogeneous (i : Fin 5) :
    ModificationPieces.Homogeneous (presentationWeight i) (values k i) := by
  fin_cases i
  · exact ModificationPieces.homogeneous_single (-1) (1 : B k)
  · exact ModificationPieces.homogeneous_C (sB k)
  · exact ModificationPieces.homogeneous_C (bX k 3)
  · change ModificationPieces.Homogeneous 1 (LP.C (f0 k) * LP.T (-1))
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    exact ModificationPieces.homogeneous_single 1 (f0 k)
  · change ModificationPieces.Homogeneous 1 (LP.C (g0 k) * LP.T (-1))
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    exact ModificationPieces.homogeneous_single 1 (g0 k)


-- @@ L99-105 verbatim
/-- An actual weighted homogeneous representative maps to the corresponding
single Laurent degree; no grading of a quotient is postulated. -/
theorem polynomialMap_homogeneous {p : P k 5} {d : ℤ}
    (hp : p.IsWeightedHomogeneous presentationWeight d) :
    ModificationPieces.Homogeneous d (polynomialMap k p) :=
  ModificationPieces.homogeneous_aeval presentationWeight (values k)
    (values_homogeneous k) hp


-- @@ L107-113 verbatim
/-- Positive-degree homogeneous representatives have numerators in the
appropriate power of the exact source ideal. -/
theorem polynomialMap_positive_piece {p : P k 5} {ℓ : ℕ}
    (hp : p.IsWeightedHomogeneous presentationWeight (ℓ : ℤ)) :
    ∃ h ∈ I k ^ ℓ, polynomialMap k p = LP.C h * LP.T (-(ℓ : ℤ)) :=
  ModificationPieces.homogeneous_numerator (polynomialMap_mem k p)
    (polynomialMap_homogeneous k hp)


-- @@ L115-122 verbatim
/-- The extraction needed for the noncoordinate obstruction, stated directly
for nonzero Laurent images of homogeneous representatives. -/
theorem polynomialMap_positive_nonzero_numerator {p : P k 5} {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hp : p.IsWeightedHomogeneous presentationWeight (ℓ : ℤ))
    (hne : polynomialMap k p ≠ 0) :
    ∃ h ∈ I k, h ≠ 0 ∧ polynomialMap k p = LP.C h * LP.T (-(ℓ : ℤ)) :=
  ModificationPieces.positive_nonzero_numerator hℓ (polynomialMap_mem k p)
    (polynomialMap_homogeneous k hp) hne


-- @@ L124-137 verbatim
/-- The canonical map's image is a `B`-subalgebra, since the base map is a
section on constant Laurent polynomials. -/
def imageSubalgebra : Subalgebra (B k) (LaurentPolynomial (B k)) where
  carrier := Set.range (toLaurent k)
  zero_mem' := ⟨0, map_zero _⟩
  one_mem' := ⟨1, map_one _⟩
  add_mem' := by
    rintro p q ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ _ _⟩
  mul_mem' := by
    rintro p q ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ _ _⟩
  algebraMap_mem' r :=
    ⟨LaurentPresentation.baseMap k r, LaurentPresentation.toLaurentBase_baseMap k r⟩


-- @@ L139-150 verbatim
/-- Exact affine-modification image, with the actual source's two-generator center. -/
theorem image_eq_modification :
    imageSubalgebra k = ModificationPieces.modification (I k) := by
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    exact toLaurent_mem k a
  · rw [I, ModificationPieces.modification_pair_eq]
    apply Algebra.adjoin_le
    rintro p (rfl | rfl | rfl)
    · exact ⟨gX k 0, toLaurent_gX k 0⟩
    · exact ⟨gX k 3, toLaurent_gX k 3⟩
    · exact ⟨gX k 4, toLaurent_gX k 4⟩


-- @@ L152-155 verbatim
theorem range_toLaurent :
    Set.range (toLaurent k) = (ModificationPieces.modification (I k) : Set _) := by
  change (imageSubalgebra k : Set (LaurentPolynomial (B k))) = _
  rw [image_eq_modification]


-- @@ L157-157 verbatim
end StableCoordinate.ModificationEmbedding


-- @@ L159-159 verbatim
end


-- @@ L161-161 verbatim
end OAI
