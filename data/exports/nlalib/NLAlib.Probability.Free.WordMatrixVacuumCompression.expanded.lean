import NLAlib.Probability.Free.WordNativeMatrixLinearCombination
import NLAlib.Probability.Free.WordCatalanMoments
import NLAlib.Matrix.Norms.EntryBounds
import NLAlib.Probability.Free.WordMatrixVacuum
import NLAlib.Matrix.Basic.NormalizedTrace


-- @@ L7-15 verbatim
/-!
# Entrywise vacuum compression of native operator matrices

The actual vacuum coefficient map is linear, has a native operator-norm
bound, and factors rank-one vacuum sandwiches into ordinary matrix products.
The left field and right annihilator give the same vacuum row coefficient.
These identities concern the concrete operators, without a distributional
or Dyson-equation premise.
-/


-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L20-20 verbatim
open scoped Classical InnerProduct Matrix

-- @@ L21-21 verbatim
namespace NLAlib

-- @@ L22-22 verbatim
variable {D ι : Type*} [Fintype D] [DecidableEq D]

-- @@ L23-23 verbatim
local notation "W" => WordHilbertSpace ι

-- @@ L24-24 verbatim
local notation "B" => W →L[ℂ] W

-- @@ L25-25 verbatim
local notation "M" => CStarMatrix D D B


-- @@ L27-37 verbatim
/-- Entrywise compression by the actual unit word vacuum. -/
def wordMatrixVacuumCompression : M →ₗ[ℂ] Matrix D D ℂ where
  toFun T i j := wordVacuumExpectation ι (T i j)
  map_add' S T := by
    ext i j
    change wordVacuumExpectation ι (S i j+T i j)=_
    exact map_add _ _ _
  map_smul' z T := by
    ext i j
    change wordVacuumExpectation ι (z•T i j)=z•wordVacuumExpectation ι (T i j)
    exact map_smul _ _ _


-- @@ L39-42 verbatim
omit [Fintype D] [DecidableEq D] in
/-- The compression is the genuine vacuum matrix coefficient in each entry. -/
@[simp] theorem wordMatrixVacuumCompression_apply (T : M) (i j : D) :
    wordMatrixVacuumCompression T i j=wordVacuumExpectation ι (T i j) := rfl


-- @@ L44-53 verbatim
omit [DecidableEq D] in
/-- Each vacuum matrix coefficient is bounded by the native matrix operator norm. -/
theorem norm_wordVacuumExpectation_entry_le (T : M) (i j : D) :
    ‖wordVacuumExpectation ι (T i j)‖≤‖T‖ := by
  calc
    _ ≤ ‖wordVacuum ι‖*‖T i j (wordVacuum ι)‖ := norm_inner_le_norm _ _
    _ ≤ ‖wordVacuum ι‖*(‖T i j‖*‖wordVacuum ι‖) :=
      mul_le_mul_of_nonneg_left ((T i j).le_opNorm _) (norm_nonneg _)
    _ ≤ ‖T‖ := by simpa only [norm_wordVacuum,one_mul,mul_one] using
      (show ‖T i j‖≤‖T‖ from CStarMatrix.norm_entry_le_norm)


-- @@ L55-69 verbatim
open scoped Matrix.Norms.L2Operator in
/-- A dimension bound for the actual compressed matrix spectral norm. -/
theorem specNorm_wordMatrixVacuumCompression_le (T : M) :
    specNorm (wordMatrixVacuumCompression T)≤(Fintype.card D : ℝ)*‖T‖ := by
  have hf : frobSq (wordMatrixVacuumCompression T)≤(Fintype.card D : ℝ)^2*‖T‖^2 := by
    rw [frobSq_eq_sum_norm_sq]
    calc
      _ ≤ ∑ _i : D,∑ _j : D,‖T‖^2 := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _)
          (norm_wordVacuumExpectation_entry_le T i j) 2
      _ = _ := by simp; ring
  have hh := (specNorm_sq_le_frobSq (wordMatrixVacuumCompression T)).trans hf
  have hn := specNorm_nonneg (wordMatrixVacuumCompression T)
  have hd : 0≤(Fintype.card D : ℝ)*‖T‖ := by positivity
  nlinarith only [hh,hn,hd]


-- @@ L71-73 verbatim
/-- The coefficient matrix tensored with the rank-one vacuum projection. -/
def wordMatrixVacuumSandwich (A : Matrix D D ℂ) : M :=
  CStarMatrix.ofMatrix (fun i j => A i j•wordVacuumProjection ι)


-- @@ L75-91 verbatim
omit [DecidableEq D] in
/-- Actual rank-one insertion factors the compressed operator product into a matrix product. -/
theorem wordMatrixVacuumCompression_mul_sandwich_mul (S T : M) (A : Matrix D D ℂ) :
    wordMatrixVacuumCompression (S*wordMatrixVacuumSandwich A*T)=
      wordMatrixVacuumCompression S*A*wordMatrixVacuumCompression T := by
  ext i j
  simp only [wordMatrixVacuumCompression_apply,CStarMatrix.mul_apply,map_sum,
    Matrix.mul_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  change wordVacuumExpectation ι (S i l*(A l k•wordVacuumProjection ι)*T k j)=_
  rw [mul_smul_comm,smul_mul_assoc,map_smul,
    wordVacuumExpectation_mul_projection_mul]
  simp only [smul_eq_mul]
  ring


-- @@ L93-101 verbatim
/-- Left and right annihilation give the same vacuum row functional. -/
theorem wordVacuumExpectation_annihilation_eq_right (i : ι) (T : B) :
    wordVacuumExpectation ι (wordAnnihilation i*T)=
      wordVacuumExpectation ι (wordRightAnnihilation i*T) := by
  simp only [wordVacuumExpectation_apply,ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply,wordAnnihilation,wordRightAnnihilation,
    ← ContinuousLinearMap.adjoint_inner_left]
  congr 1
  simp [wordVacuum,LinearIsometry.coe_toContinuousLinearMap]


-- @@ L103-114 verbatim
omit [Fintype D] [DecidableEq D] in
/-- The left field vacuum row equals the actual right annihilator vacuum row. -/
theorem wordVacuumExpectation_wordField_mul_eq_rightAnnihilation (i : ι) (t : B) :
    wordVacuumExpectation ι (wordField i*t)=
      wordVacuumExpectation ι (wordRightAnnihilation i*t) := by
  have hc : wordVacuumExpectation ι ((wordCreation i).toContinuousLinearMap*t)=0 := by
    rw [wordVacuumExpectation_apply,ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left (wordCreation i).toContinuousLinearMap
        (t (wordVacuum ι)) (wordVacuum ι)]
    change inner ℂ (wordAnnihilation i (wordVacuum ι)) (t (wordVacuum ι))=0
    simp only [wordAnnihilation_wordVacuum,inner_zero_left]
  rw [wordField,add_mul,map_add,hc,zero_add,wordVacuumExpectation_annihilation_eq_right]


-- @@ L116-121 verbatim
omit [Fintype D] [DecidableEq D] in
/-- A right annihilator on the vacuum column gives expectation zero. -/
theorem wordVacuumExpectation_mul_rightAnnihilation (i : ι) (t : B) :
    wordVacuumExpectation ι (t*wordRightAnnihilation i)=0 := by
  simp [wordVacuumExpectation_apply,ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply,wordVacuum]


-- @@ L123-129 verbatim
omit [Fintype D] in
/-- Compression preserves the actual identity matrix, including empty dimension. -/
@[simp] theorem wordMatrixVacuumCompression_one :
    wordMatrixVacuumCompression (1 : M)=1 := by
  ext i j
  by_cases hij : i=j <;> simp [wordMatrixVacuumCompression_apply,
    Matrix.one_apply,hij]


-- @@ L131-142 verbatim
/-- Scalar matrix multiplication on the left passes through actual vacuum compression. -/
theorem wordMatrixVacuumCompression_scalar_mul (A : Matrix D D ℂ) (t : M) :
    wordMatrixVacuumCompression
      (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) (CStarMatrix.ofMatrix A)*t)=
      A*wordMatrixVacuumCompression t := by
  ext i j
  simp only [wordMatrixVacuumCompression_apply,CStarMatrix.mul_apply,map_sum,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change wordVacuumExpectation ι ((A i k•(1 : B))*t k j)=_
  rw [smul_mul_assoc,one_mul,map_smul]
  rfl


-- @@ L144-156 verbatim
/-- Scalar matrix multiplication on the right passes through actual vacuum compression. -/
theorem wordMatrixVacuumCompression_mul_scalar (t : M) (A : Matrix D D ℂ) :
    wordMatrixVacuumCompression
      (t*CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) (CStarMatrix.ofMatrix A))=
      wordMatrixVacuumCompression t*A := by
  ext i j
  simp only [wordMatrixVacuumCompression_apply,CStarMatrix.mul_apply,map_sum,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change wordVacuumExpectation ι (t i k*(A k j•(1 : B)))=_
  rw [mul_smul_comm,mul_one,map_smul]
  simp only [smul_eq_mul]
  exact mul_comm _ _


-- @@ L158-164 verbatim
omit [Fintype D] [DecidableEq D] in
/-- Actual vacuum compression commutes with the adjoint. -/
theorem wordMatrixVacuumCompression_star (T : M) :
    wordMatrixVacuumCompression (star T)=(wordMatrixVacuumCompression T)ᴴ := by
  ext a b
  simp only [wordMatrixVacuumCompression_apply,CStarMatrix.star_apply,
    wordVacuumExpectation_star,Matrix.conjTranspose_apply]


-- @@ L166-169 verbatim
omit [DecidableEq D] in
/-- Normalized trace of the actual vacuum compression is exactly the native normalized matrix vacuum, including empty dimension. -/
theorem normalizedTrace_wordMatrixVacuumCompression (T : M) :
    normalizedTrace (wordMatrixVacuumCompression T)=wordMatrixVacuumExpectation T := rfl


-- @@ L171-171 verbatim
end NLAlib
