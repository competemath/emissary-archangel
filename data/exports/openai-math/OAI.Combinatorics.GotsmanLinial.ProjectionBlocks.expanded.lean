import OAI.Combinatorics.GotsmanLinial.HilbertSchmidt
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-14 verbatim
/-!
# Matrix blocks of a finite orthogonal projection family

The Hilbert--Schmidt quantity below is the explicit sum of squared entry norms
rather than an ambient matrix norm instance.
-/


-- @@ L16-16 verbatim
open scoped BigOperators ComplexConjugate

-- @@ L17-17 verbatim
open Module


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace LeanBlast.GotsmanLinial


-- @@ L23-23 verbatim
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]


-- @@ L25-30 verbatim
/-- A finite orthogonal decomposition of the identity by Hermitian projections. -/
structure OrthogonalProjectionFamily (P : κ → Matrix ι ι ℂ) : Prop where
  selfAdjoint : ∀ k, IsSelfAdjoint (P k)
  idempotent : ∀ k, P k * P k = P k
  orthogonal : ∀ r s, r ≠ s → P r * P s = 0
  sum_eq_one : ∑ k, P k = 1


-- @@ L32-32 verbatim
namespace OrthogonalProjectionFamily


-- @@ L34-34 verbatim
variable {P : κ → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)


-- @@ L36-36 verbatim
include hP


-- @@ L38-39 verbatim
theorem conjTranspose_eq (k : κ) : (P k).conjTranspose = P k := by
  simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using hP.selfAdjoint k


-- @@ L41-46 verbatim
theorem mul_eq_ite [DecidableEq κ] (r s : κ) :
    P r * P s = if r = s then P r else 0 := by
  by_cases hrs : r = s
  · subst s
    simp [hP.idempotent]
  · simp [hrs, hP.orthogonal r s hrs]


-- @@ L48-48 verbatim
end OrthogonalProjectionFamily


-- @@ L50-50 verbatim
variable {P : κ → Matrix ι ι ℂ}


-- @@ L52-55 verbatim
theorem sum_projection_blocks (hP : OrthogonalProjectionFamily P) (B : Matrix ι ι ℂ) :
    (∑ r, ∑ s, P s * B * P r) = B := by
  simp_rw [← Matrix.sum_mul, hP.sum_eq_one, Matrix.one_mul]
  rw [← Matrix.mul_sum, hP.sum_eq_one, Matrix.mul_one]


-- @@ L57-60 verbatim
theorem projection_block_ext (hP : OrthogonalProjectionFamily P)
    {A B : Matrix ι ι ℂ} (h : ∀ r s, P s * A * P r = P s * B * P r) : A = B := by
  rw [← sum_projection_blocks hP A, ← sum_projection_blocks hP B]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => h r s


-- @@ L62-64 verbatim
/-- The real-valued spectral multiplier defined by the projection family. -/
def matrixGrading (P : κ → Matrix ι ι ℂ) (weight : κ → ℝ) : Matrix ι ι ℂ :=
  ∑ k, (weight k : ℂ) • P k


-- @@ L66-70 verbatim
theorem projection_mul_matrixGrading (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (s : κ) : P s * matrixGrading P weight = (weight s : ℂ) • P s := by
  classical
  simp only [matrixGrading, Matrix.mul_sum, Matrix.mul_smul, hP.mul_eq_ite]
  simp


-- @@ L72-76 verbatim
theorem matrixGrading_mul_projection (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (r : κ) : matrixGrading P weight * P r = (weight r : ℂ) • P r := by
  classical
  simp only [matrixGrading, Matrix.sum_mul, Matrix.smul_mul, hP.mul_eq_ite]
  simp


-- @@ L78-92 verbatim
theorem projection_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B - B * matrixGrading P weight) * P r =
      ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  calc
    P s * (matrixGrading P weight * B) * P r -
        P s * (B * matrixGrading P weight) * P r =
      (P s * matrixGrading P weight) * B * P r -
        P s * B * (matrixGrading P weight * P r) := by simp only [Matrix.mul_assoc]
    _ = ((weight s : ℂ) • P s) * B * P r -
        P s * B * ((weight r : ℂ) • P r) := by
      rw [projection_mul_matrixGrading hP, matrixGrading_mul_projection hP]
    _ = ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Complex.ofReal_sub, sub_smul]


-- @@ L94-108 verbatim
theorem projection_anticommutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B + B * matrixGrading P weight) * P r =
      ((weight s + weight r : ℝ) : ℂ) • (P s * B * P r) := by
  rw [Matrix.mul_add, Matrix.add_mul]
  calc
    P s * (matrixGrading P weight * B) * P r +
        P s * (B * matrixGrading P weight) * P r =
      (P s * matrixGrading P weight) * B * P r +
        P s * B * (matrixGrading P weight * P r) := by simp only [Matrix.mul_assoc]
    _ = ((weight s : ℂ) • P s) * B * P r +
        P s * B * ((weight r : ℂ) • P r) := by
      rw [projection_mul_matrixGrading hP, matrixGrading_mul_projection hP]
    _ = ((weight s + weight r : ℝ) : ℂ) • (P s * B * P r) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Complex.ofReal_add, add_smul]


-- @@ L110-113 verbatim
omit [DecidableEq ι] in
theorem trace_projection_sandwich (Q A : Matrix ι ι ℂ) (hQ : Q * Q = Q) :
    Matrix.trace (Q * A * Q) = Matrix.trace (Q * A) := by
  rw [Matrix.trace_mul_cycle, hQ]


-- @@ L115-123 verbatim
theorem hsNormSq_projection_mul (hP : OrthogonalProjectionFamily P)
    (s : κ) (B : Matrix ι ι ℂ) :
    hsNormSq (P s * B) = (Matrix.trace (B.conjTranspose * P s * B)).re := by
  rw [hsNormSq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  congr 2
  calc
    (B.conjTranspose * P s) * (P s * B) =
        B.conjTranspose * (P s * P s) * B := by simp only [Matrix.mul_assoc]
    _ = B.conjTranspose * P s * B := by rw [hP.idempotent]


-- @@ L125-131 verbatim
theorem hsNormSq_mul_projection (hP : OrthogonalProjectionFamily P)
    (r : κ) (B : Matrix ι ι ℂ) :
    hsNormSq (B * P r) = (Matrix.trace (P r * (B.conjTranspose * B))).re := by
  rw [hsNormSq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  have heq : (P r * B.conjTranspose) * (B * P r) =
      P r * (B.conjTranspose * B) * P r := by simp only [Matrix.mul_assoc]
  rw [heq, trace_projection_sandwich _ _ (hP.idempotent r)]


-- @@ L133-138 verbatim
theorem hsNormSq_left_projection_decomposition (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) : hsNormSq B = ∑ s, hsNormSq (P s * B) := by
  simp_rw [hsNormSq_projection_mul hP]
  rw [← Complex.re_sum, ← Matrix.trace_sum]
  simp_rw [← Matrix.sum_mul]
  rw [← Matrix.mul_sum, hP.sum_eq_one, Matrix.mul_one, hsNormSq_eq_re_trace]


-- @@ L140-144 verbatim
theorem hsNormSq_right_projection_decomposition (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) : hsNormSq B = ∑ r, hsNormSq (B * P r) := by
  simp_rw [hsNormSq_mul_projection hP]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    hP.sum_eq_one, Matrix.one_mul, hsNormSq_eq_re_trace]


-- @@ L146-152 verbatim
theorem hsNormSq_block_parseval (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) :
    hsNormSq B = ∑ r, ∑ s, hsNormSq (P s * B * P r) := by
  rw [hsNormSq_right_projection_decomposition hP B]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [Matrix.mul_assoc] using hsNormSq_left_projection_decomposition hP (B * P r)


-- @@ L154-166 verbatim
theorem hsNormSq_matrixGrading (hP : OrthogonalProjectionFamily P) (weight : κ → ℝ) :
    hsNormSq (matrixGrading P weight) = ∑ r, weight r ^ 2 * hsNormSq (P r) := by
  classical
  rw [hsNormSq_block_parseval hP]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single r]
  · rw [projection_mul_matrixGrading hP, Matrix.smul_mul, hP.idempotent,
      hsNormSq_real_smul]
  · intro s _ hsr
    rw [projection_mul_matrixGrading hP, Matrix.smul_mul,
      hP.orthogonal s r hsr, smul_zero, hsNormSq_zero]
  · simp


-- @@ L168-174 verbatim
theorem hsNormSq_matrixGrading_trace (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) :
    hsNormSq (matrixGrading P weight) = ∑ r, weight r ^ 2 * (Matrix.trace (P r)).re := by
  rw [hsNormSq_matrixGrading hP]
  apply Finset.sum_congr rfl
  intro r _
  rw [hsNormSq_projection (P r) (hP.conjTranspose_eq r) (hP.idempotent r)]


-- @@ L176-183 verbatim
theorem sum_hsNormSq_blocks_column (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r : κ) (hB : B.conjTranspose * B = 1) :
    (∑ s, hsNormSq (P s * B * P r)) = hsNormSq (P r) := by
  calc
    (∑ s, hsNormSq (P s * B * P r)) = hsNormSq (B * P r) := by
      simpa only [Matrix.mul_assoc] using
        (hsNormSq_left_projection_decomposition hP (B * P r)).symm
    _ = hsNormSq (P r) := hsNormSq_mul_left_of_unitary B (P r) hB


-- @@ L185-189 verbatim
theorem sum_hsNormSq_blocks_row (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (s : κ) (hB : B * B.conjTranspose = 1) :
    (∑ r, hsNormSq (P s * B * P r)) = hsNormSq (P s) := by
  rw [← hsNormSq_right_projection_decomposition hP (P s * B)]
  exact hsNormSq_mul_right_of_unitary (P s) B hB


-- @@ L191-195 verbatim
theorem sum_hsNormSq_blocks_column_trace (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r : κ) (hB : B.conjTranspose * B = 1) :
    (∑ s, hsNormSq (P s * B * P r)) = (Matrix.trace (P r)).re := by
  rw [sum_hsNormSq_blocks_column hP B r hB]
  exact hsNormSq_projection (P r) (hP.conjTranspose_eq r) (hP.idempotent r)


-- @@ L197-201 verbatim
theorem sum_hsNormSq_blocks_row_trace (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (s : κ) (hB : B * B.conjTranspose = 1) :
    (∑ r, hsNormSq (P s * B * P r)) = (Matrix.trace (P s)).re := by
  rw [sum_hsNormSq_blocks_row hP B s hB]
  exact hsNormSq_projection (P s) (hP.conjTranspose_eq s) (hP.idempotent s)


-- @@ L203-208 verbatim
theorem hsNormSq_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) :
    hsNormSq (matrixGrading P weight * B - B * matrixGrading P weight) =
      ∑ r, ∑ s, (weight s - weight r) ^ 2 * hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_commutator hP, hsNormSq_real_smul]


-- @@ L210-215 verbatim
theorem hsNormSq_anticommutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) :
    hsNormSq (matrixGrading P weight * B + B * matrixGrading P weight) =
      ∑ r, ∑ s, (weight s + weight r) ^ 2 * hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_anticommutator hP, hsNormSq_real_smul]


-- @@ L217-219 verbatim
/-- The degree grading associated to projections indexed from zero to `n`. -/
def degreeGrading {n : ℕ} (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixGrading P fun k => (k.val : ℝ)


-- @@ L221-223 verbatim
/-- The degree grading centered at `n / 2`. -/
def centeredGrading {n : ℕ} (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixGrading P fun k => (k.val : ℝ) - (n : ℝ) / 2


-- @@ L225-229 verbatim
theorem hsNormSq_centeredGrading {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    hsNormSq (centeredGrading P) =
      ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * hsNormSq (P k) :=
  hsNormSq_matrixGrading hP _


-- @@ L231-235 verbatim
theorem hsNormSq_centeredGrading_trace {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    hsNormSq (centeredGrading P) =
      ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * (Matrix.trace (P k)).re :=
  hsNormSq_matrixGrading_trace hP _


-- @@ L237-242 verbatim
theorem centeredGrading_eq {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    centeredGrading P = degreeGrading P - (((n : ℝ) / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  simp only [centeredGrading, degreeGrading, matrixGrading, Complex.ofReal_sub, sub_smul,
    Finset.sum_sub_distrib]
  rw [← Finset.smul_sum, hP.sum_eq_one]


-- @@ L244-251 verbatim
theorem projection_centered_anticommutator {n : ℕ}
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r s : Fin (n + 1)) :
    P s * (centeredGrading P * B + B * centeredGrading P) * P r =
      (((s.val : ℝ) + (r.val : ℝ) - n : ℝ) : ℂ) • (P s * B * P r) := by
  rw [centeredGrading, projection_anticommutator hP]
  congr 2
  ring


-- @@ L253-260 verbatim
theorem hsNormSq_centered_anticommutator {n : ℕ}
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) :
    hsNormSq (centeredGrading P * B + B * centeredGrading P) =
      ∑ r, ∑ s, ((s.val : ℝ) + (r.val : ℝ) - n) ^ 2 *
        hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_centered_anticommutator hP, hsNormSq_real_smul]


-- @@ L262-262 verbatim
section OperatorTransport


-- @@ L264-265 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]


-- @@ L267-267 verbatim
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E


-- @@ L269-274 verbatim
/-- Matrix representation of a continuous operator in an orthonormal basis,
bundled with its algebraic compatibility. -/
def operatorMatrixEquiv (b : OrthonormalBasis ι ℂ E) :
    (E →L[ℂ] E) ≃ₐ[ℂ] Matrix ι ι ℂ :=
  (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).symm.trans
    (LinearMap.toMatrixOrthonormal b).toAlgEquiv


-- @@ L276-279 verbatim
/-- Matrix entries for the counting orthonormal basis or any chosen
orthonormal basis. -/
def operatorMatrix (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) : Matrix ι ι ℂ :=
  operatorMatrixEquiv b T


-- @@ L281-282 verbatim
theorem operatorMatrix_eq_toMatrix (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) :
    operatorMatrix b T = LinearMap.toMatrixOrthonormal b T.toLinearMap := rfl


-- @@ L284-286 verbatim
theorem operatorMatrix_apply (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (i j : ι) :
    operatorMatrix b T i j = inner ℂ (b i) (T (b j)) :=
  LinearMap.toMatrixOrthonormal_apply_apply b T.toLinearMap i j


-- @@ L288-289 verbatim
theorem operatorMatrix_injective (b : OrthonormalBasis ι ℂ E) :
    Function.Injective (operatorMatrix b) := (operatorMatrixEquiv b).injective


-- @@ L291-293 verbatim
@[simp]
theorem operatorMatrix_zero (b : OrthonormalBasis ι ℂ E) :
    operatorMatrix b (0 : E →L[ℂ] E) = 0 := map_zero (operatorMatrixEquiv b)


-- @@ L295-297 verbatim
@[simp]
theorem operatorMatrix_one (b : OrthonormalBasis ι ℂ E) :
    operatorMatrix b (1 : E →L[ℂ] E) = 1 := map_one (operatorMatrixEquiv b)


-- @@ L299-302 verbatim
@[simp]
theorem operatorMatrix_add (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A + B) = operatorMatrix b A + operatorMatrix b B :=
  map_add (operatorMatrixEquiv b) A B


-- @@ L304-307 verbatim
@[simp]
theorem operatorMatrix_sub (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A - B) = operatorMatrix b A - operatorMatrix b B :=
  map_sub (operatorMatrixEquiv b) A B


-- @@ L309-312 verbatim
@[simp]
theorem operatorMatrix_mul (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A * B) = operatorMatrix b A * operatorMatrix b B :=
  map_mul (operatorMatrixEquiv b) A B


-- @@ L314-317 verbatim
@[simp]
theorem operatorMatrix_smul (b : OrthonormalBasis ι ℂ E) (z : ℂ) (T : E →L[ℂ] E) :
    operatorMatrix b (z • T) = z • operatorMatrix b T :=
  (operatorMatrixEquiv b).toLinearEquiv.map_smul z T


-- @@ L319-322 verbatim
@[simp]
theorem operatorMatrix_sum (b : OrthonormalBasis ι ℂ E) (T : κ → E →L[ℂ] E) :
    operatorMatrix b (∑ k, T k) = ∑ k, operatorMatrix b (T k) :=
  map_sum (operatorMatrixEquiv b) T Finset.univ


-- @@ L324-328 verbatim
theorem operatorMatrix_isSelfAdjoint (b : OrthonormalBasis ι ℂ E)
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) : IsSelfAdjoint (operatorMatrix b T) := by
  have hlin : IsSelfAdjoint T.toLinearMap :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff T).mpr hT
  exact hlin.map (LinearMap.toMatrixOrthonormal b)


-- @@ L330-342 verbatim
/-- Transfer an actually constructed orthogonal family of Hilbert-space
projections to the matrix interface used by the block estimates. -/
theorem orthogonalProjectionFamily_operatorMatrix (b : OrthonormalBasis ι ℂ E)
    (T : κ → E →L[ℂ] E)
    (hself : ∀ k, IsSelfAdjoint (T k))
    (hidem : ∀ k, T k * T k = T k)
    (horth : ∀ r s, r ≠ s → T r * T s = 0)
    (hsum : ∑ k, T k = 1) :
    OrthogonalProjectionFamily (fun k => operatorMatrix b (T k)) where
  selfAdjoint k := operatorMatrix_isSelfAdjoint b (T k) (hself k)
  idempotent k := by rw [← operatorMatrix_mul, hidem k]
  orthogonal r s hrs := by rw [← operatorMatrix_mul, horth r s hrs, operatorMatrix_zero]
  sum_eq_one := by rw [← operatorMatrix_sum, hsum, operatorMatrix_one]


-- @@ L344-344 verbatim
end OperatorTransport


-- @@ L346-352 verbatim
/-- The standard-basis matrix representation is inverse to the standard
Euclidean continuous linear operator associated to a matrix. -/
@[simp]
theorem operatorMatrix_toEuclideanCLM (A : Matrix ι ι ℂ) :
    operatorMatrix (EuclideanSpace.basisFun ι ℂ)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) = A :=
  (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun ι ℂ)).apply_symm_apply A


-- @@ L354-354 verbatim
end LeanBlast.GotsmanLinial


-- @@ L356-356 verbatim
end


-- @@ L358-358 verbatim
end OAI
