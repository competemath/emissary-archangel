import NLAlib.ForMathlib.Analysis.CStarAlgebra.CStarMatrixPiLp
import NLAlib.Probability.Free.WordFields
import NLAlib.Matrix.Norms.Core


-- @@ L5-15 verbatim
/-!
# Actual compatible matrix amplification of the concrete word operators

Scalar matrix coefficients act faithfully and isometrically on the native
Hilbert direct sum of word Hilbert spaces. Operator-valued coefficient blocks
use the canonical `CStarMatrix` representation; they do not use the scalar
Euclidean matrix adapter or a new matrix norm. This supplies actual bounded
self-adjoint matrix-valued reference linear combinations.

No faithful amplified state, free law, or spectral comparison is assumed.
-/


-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
set_option autoImplicit false


-- @@ L20-20 verbatim
open scoped Classical ComplexOrder


-- @@ L22-22 verbatim
namespace NLAlib


-- @@ L24-26 verbatim
/-- The actual finite matrix amplification of the concrete word Hilbert
space, equipped with its native Hilbert direct-sum norm. -/
abbrev WordMatrixHilbertSpace (D ι : Type*) := PiLp 2 (fun _ : D => WordHilbertSpace ι)


-- @@ L28-28 verbatim
variable {D ι : Type*} [Fintype D] [DecidableEq D]

-- @@ L29-29 verbatim
local notation "W" => WordHilbertSpace ι

-- @@ L30-30 verbatim
local notation "K" => WordMatrixHilbertSpace D ι

-- @@ L31-31 verbatim
local notation "B" => W →L[ℂ] W


-- @@ L33-36 verbatim
/-- Actual scalar C*-matrix coefficients act on the word Hilbert direct sum
by the canonical faithful bounded block representation. -/
def wordCStarCoefficientHom : CStarMatrix D D ℂ →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  CStarMatrix.toPiLpStarAlgHom.comp (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B))


-- @@ L38-43 verbatim
private theorem word_scalar_operator_injective :
    Function.Injective (StarAlgHom.ofId ℂ B) := by
  intro z w hzw
  have h := congrArg (wordVacuumExpectation ι) hzw
  simpa only [StarAlgHom.ofId_apply, Algebra.algebraMap_eq_smul_one,
    map_smul, wordVacuumExpectation_one, smul_eq_mul, mul_one] using h


-- @@ L45-50 verbatim
/-- The coefficient representation is injective, proved from the actual
normalized vacuum rather than any nontriviality assumption on the alphabet. -/
theorem wordCStarCoefficientHom_injective :
    Function.Injective (wordCStarCoefficientHom (D := D) (ι := ι)) :=
  CStarMatrix.toPiLpStarAlgHom_injective.comp
    (CStarMatrix.mapStarAlgHom_injective _ word_scalar_operator_injective)


-- @@ L52-56 verbatim
/-- Scalar C*-matrix coefficients retain exactly their canonical native norm
in the actual amplified word representation, including empty matrix dimension. -/
theorem norm_wordCStarCoefficientHom (A : CStarMatrix D D ℂ) :
    ‖wordCStarCoefficientHom (ι := ι) A‖ = ‖A‖ :=
  NonUnitalStarAlgHom.norm_map wordCStarCoefficientHom wordCStarCoefficientHom_injective A


-- @@ L58-61 verbatim
/-- The genuine scalar matrix-coefficient embedding, bundled as a native
star-algebra homomorphism into bounded operators on the word direct sum. -/
def wordMatrixCoefficientHom : Matrix D D ℂ →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  wordCStarCoefficientHom.comp CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom


-- @@ L63-69 verbatim
/-- The actual coordinate action of a scalar matrix coefficient. -/
@[simp]
theorem wordMatrixCoefficientHom_apply (A : Matrix D D ℂ) (v : K) (i : D) :
    wordMatrixCoefficientHom A v i = ∑ j, A i j • v j := by
  simp [wordMatrixCoefficientHom, wordCStarCoefficientHom,
    StarAlgHom.ofId_apply, Algebra.algebraMap_eq_smul_one]
  rfl


-- @@ L71-78 verbatim
open scoped Matrix.Norms.L2Operator in
/-- The actual scalar coefficient embedding preserves the named matrix
spectral norm exactly, with no dimension factor. -/
theorem norm_wordMatrixCoefficientHom (A : Matrix D D ℂ) :
    ‖wordMatrixCoefficientHom (ι := ι) A‖ = specNorm A := by
  change ‖wordCStarCoefficientHom (CStarMatrix.ofMatrix A)‖ = specNorm A
  rw [norm_wordCStarCoefficientHom, CStarMatrix.norm_ofMatrix_complex]
  exact (specNorm_eq_norm A).symm


-- @@ L80-84 verbatim
/-- A Hermitian scalar matrix coefficient gives an actual self-adjoint
bounded operator under the compatible coefficient embedding. -/
theorem isSelfAdjoint_wordMatrixCoefficientHom {A : Matrix D D ℂ} (hA : A.IsHermitian) :
    IsSelfAdjoint (wordMatrixCoefficientHom (ι := ι) A) :=
  hA.isSelfAdjoint.map wordMatrixCoefficientHom


-- @@ L86-90 verbatim
/-- An actual scalar matrix coefficient tensored with an actual bounded
word-space operator, realized by native bounded-operator matrix entries. -/
def wordMatrixTensor (A : Matrix D D ℂ) (T : B) : K →L[ℂ] K :=
  CStarMatrix.toPiLpStarAlgHom (D := D) (H := W)
    (CStarMatrix.ofMatrix (fun i j => A i j • T))


-- @@ L92-98 verbatim
/-- The concrete coefficient-operator block action has the expected finite
column formula. No tensor product completion is assumed. -/
@[simp]
theorem wordMatrixTensor_apply (A : Matrix D D ℂ) (T : B) (v : K) (i : D) :
    wordMatrixTensor A T v i = ∑ j, A i j • T (v j) := by
  simp [wordMatrixTensor, CStarMatrix.ofMatrix]
  rfl


-- @@ L100-108 verbatim
/-- The identity coefficient amplifies a word-space operator diagonally. -/
@[simp]
theorem wordMatrixTensor_one_apply (T : B) (v : K) (i : D) :
    wordMatrixTensor (1 : Matrix D D ℂ) T v i = T (v i) := by
  rw [wordMatrixTensor_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp


-- @@ L110-121 verbatim
/-- The actual coefficient-operator block factors as its scalar coefficient
embedding times the diagonal amplification of its word-space operator. -/
theorem wordMatrixTensor_eq_coefficient_mul (A : Matrix D D ℂ) (T : B) :
    wordMatrixTensor A T = wordMatrixCoefficientHom A * wordMatrixTensor 1 T := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change wordMatrixTensor A T v i =
    wordMatrixCoefficientHom A (wordMatrixTensor 1 T v) i
  rw [wordMatrixTensor_apply, wordMatrixCoefficientHom_apply]
  simp only [wordMatrixTensor_one_apply]


-- @@ L123-133 verbatim
/-- Actual scalar matrix coefficients commute with every diagonal
word-space operator amplification, from complex linearity of that operator. -/
theorem commute_wordMatrixCoefficientHom_wordMatrixTensor_one (A : Matrix D D ℂ) (T : B) :
    Commute (wordMatrixCoefficientHom A) (wordMatrixTensor 1 T) := by
  change _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    wordMatrixCoefficientHom_apply, wordMatrixTensor_one_apply, map_sum, map_smul]


-- @@ L135-139 verbatim
/-- The actual coefficient-operator block uses precisely the canonical
native C*-matrix norm, with no new norm chosen for raw matrix entries. -/
theorem norm_wordMatrixTensor (A : Matrix D D ℂ) (T : B) :
    ‖wordMatrixTensor A T‖ = ‖CStarMatrix.ofMatrix (fun i j => A i j • T)‖ :=
  CStarMatrix.norm_toPiLpStarAlgHom _


-- @@ L141-151 verbatim
/-- Hermitian coefficients and self-adjoint word-space operators yield a
genuine self-adjoint amplified block operator. -/
theorem isSelfAdjoint_wordMatrixTensor {A : Matrix D D ℂ} (hA : A.IsHermitian)
    {T : B} (hT : IsSelfAdjoint T) : IsSelfAdjoint (wordMatrixTensor A T) := by
  apply (CStarMatrix.isSelfAdjoint_toPiLpStarAlgHom_iff _).mpr
  change star (CStarMatrix.ofMatrix (fun i j => A i j • T)) =
    CStarMatrix.ofMatrix (fun i j => A i j • T)
  apply CStarMatrix.ext
  intro i j
  change star (A j i • T) = A i j • T
  rw [star_smul, hT.star_eq, hA.apply]


-- @@ L153-157 verbatim
/-- The actual matrix-coefficient linear reference on the concrete
Hilbert space. Its operator norm and spectrum are native bounded-operator ones. -/
def wordMatrixLinearCombination [Fintype ι] (A₀ : Matrix D D ℂ)
    (A : ι → Matrix D D ℂ) : K →L[ℂ] K :=
  wordMatrixCoefficientHom A₀ + ∑ i, wordMatrixTensor (A i) (wordField i)


-- @@ L159-168 verbatim
/-- Actual Hermitian matrix coefficients give a self-adjoint concrete
matrix-amplified linear reference operator. -/
theorem isSelfAdjoint_wordMatrixLinearCombination [Fintype ι]
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian) {A : ι → Matrix D D ℂ}
    (hA : ∀ i, (A i).IsHermitian) : IsSelfAdjoint (wordMatrixLinearCombination A₀ A) := by
  unfold wordMatrixLinearCombination
  exact IsSelfAdjoint.add (R := K →L[ℂ] K)
    (isSelfAdjoint_wordMatrixCoefficientHom (ι := ι) hA₀)
    (isSelfAdjoint_sum _ (fun i _ =>
      isSelfAdjoint_wordMatrixTensor (hA i) (isSelfAdjoint_wordField i)))


-- @@ L170-170 verbatim
end NLAlib
