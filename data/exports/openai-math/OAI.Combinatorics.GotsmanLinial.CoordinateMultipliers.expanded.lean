import OAI.Combinatorics.GotsmanLinial.Statement
import OAI.Combinatorics.GotsmanLinial.HilbertSchmidt
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-15 verbatim
/-!
# Actual diagonal sign and coordinate operators on the cube

The matrices here act on the cube with its counting inner product.  Their
continuous linear maps act on `EuclideanSpace`, so all operator-norm statements
refer to the intended Euclidean norm.  The Hilbert--Schmidt statements use the
explicit squared-entry sum `hsNormSq`.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open scoped BigOperators Matrix


-- @@ L21-21 verbatim
namespace LeanBlast.GotsmanLinial


-- @@ L23-23 verbatim
variable {n : ℕ}


-- @@ L25-27 verbatim
/-- Multiplication by a real function on the cube, represented in the point-mass basis. -/
def signMatrix (h : Cube n → ℝ) : Matrix (Cube n) (Cube n) ℂ :=
  Matrix.diagonal (fun x => (h x : ℂ))


-- @@ L29-31 verbatim
/-- The actual cube coordinate-sign matrix `Z_i`. -/
def coordinateSignMatrix (i : Fin n) : Matrix (Cube n) (Cube n) ℂ :=
  signMatrix (fun x => cubeCoord x i)


-- @@ L33-35 verbatim
@[simp] theorem signMatrix_apply (h : Cube n → ℝ) (x y : Cube n) :
    signMatrix h x y = if x = y then (h x : ℂ) else 0 := by
  simp [signMatrix, Matrix.diagonal_apply]


-- @@ L37-38 verbatim
@[simp] theorem signMatrix_apply_self (h : Cube n → ℝ) (x : Cube n) :
    signMatrix h x x = (h x : ℂ) := by simp


-- @@ L40-42 verbatim
@[simp] theorem coordinateSignMatrix_apply (i : Fin n) (x y : Cube n) :
    coordinateSignMatrix i x y = if x = y then (cubeCoord x i : ℂ) else 0 :=
  signMatrix_apply _ x y


-- @@ L44-46 verbatim
@[simp] theorem signMatrix_conjTranspose (h : Cube n → ℝ) :
    (signMatrix h).conjTranspose = signMatrix h := by
  simp [signMatrix, Matrix.diagonal_conjTranspose]


-- @@ L48-50 verbatim
@[simp] theorem signMatrix_star (h : Cube n → ℝ) :
    star (signMatrix h) = signMatrix h :=
  signMatrix_conjTranspose h


-- @@ L52-53 verbatim
theorem signMatrix_isHermitian (h : Cube n → ℝ) : (signMatrix h).IsHermitian :=
  signMatrix_conjTranspose h


-- @@ L55-63 verbatim
/-- A sign-valued real diagonal is an involution. -/
theorem signMatrix_mul_self (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : signMatrix h * signMatrix h = 1 := by
  classical
  rw [signMatrix, Matrix.diagonal_mul_diagonal]
  have hs : (fun x => (h x : ℂ) * (h x : ℂ)) = fun _ : Cube n => (1 : ℂ) := by
    funext x
    rcases hh x with hx | hx <;> simp [hx]
  rw [hs, Matrix.diagonal_one]


-- @@ L65-68 verbatim
theorem signMatrix_conjTranspose_mul (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    (signMatrix h).conjTranspose * signMatrix h = 1 := by
  rw [signMatrix_conjTranspose, signMatrix_mul_self h hh]


-- @@ L70-73 verbatim
theorem signMatrix_mul_conjTranspose (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    signMatrix h * (signMatrix h).conjTranspose = 1 := by
  rw [signMatrix_conjTranspose, signMatrix_mul_self h hh]


-- @@ L75-79 verbatim
theorem signMatrix_unitary (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    signMatrix h ∈ Matrix.unitaryGroup (Cube n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, signMatrix_star]
  exact signMatrix_mul_self h hh


-- @@ L81-88 verbatim
/-- A real sign diagonal commutes with every complex diagonal weight. -/
theorem signMatrix_commute_diagonal (h : Cube n → ℝ) (d : Cube n → ℂ) :
    Commute (signMatrix h) (Matrix.diagonal d) := by
  change signMatrix h * Matrix.diagonal d = Matrix.diagonal d * signMatrix h
  simp only [signMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _


-- @@ L90-92 verbatim
theorem signMatrix_mul_diagonal_comm (h : Cube n → ℝ) (d : Cube n → ℂ) :
    signMatrix h * Matrix.diagonal d = Matrix.diagonal d * signMatrix h :=
  (signMatrix_commute_diagonal h d).eq


-- @@ L94-96 verbatim
@[simp] theorem signMatrix_mulVec (h : Cube n → ℝ) (v : Cube n → ℂ) (x : Cube n) :
    (signMatrix h *ᵥ v) x = (h x : ℂ) * v x := by
  simp [signMatrix, Matrix.mulVec_diagonal]


-- @@ L98-101 verbatim
theorem hsNormSq_signMatrix (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : hsNormSq (signMatrix h) = (2 : ℝ) ^ n := by
  rw [hsNormSq_of_unitary _ (signMatrix_conjTranspose_mul h hh), card_cube]
  simp


-- @@ L103-105 verbatim
@[simp] theorem coordinateSignMatrix_conjTranspose (i : Fin n) :
    (coordinateSignMatrix i).conjTranspose = coordinateSignMatrix i :=
  signMatrix_conjTranspose _


-- @@ L107-109 verbatim
@[simp] theorem coordinateSignMatrix_star (i : Fin n) :
    star (coordinateSignMatrix i) = coordinateSignMatrix i :=
  signMatrix_star _


-- @@ L111-112 verbatim
theorem coordinateSignMatrix_isHermitian (i : Fin n) :
    (coordinateSignMatrix i).IsHermitian := signMatrix_isHermitian _


-- @@ L114-116 verbatim
@[simp] theorem coordinateSignMatrix_mul_self (i : Fin n) :
    coordinateSignMatrix i * coordinateSignMatrix i = 1 :=
  signMatrix_mul_self _ (fun x => cubeCoord_cases x i)


-- @@ L118-119 verbatim
@[simp] theorem coordinateSignMatrix_conjTranspose_mul (i : Fin n) :
    (coordinateSignMatrix i).conjTranspose * coordinateSignMatrix i = 1 := by simp


-- @@ L121-122 verbatim
@[simp] theorem coordinateSignMatrix_mul_conjTranspose (i : Fin n) :
    coordinateSignMatrix i * (coordinateSignMatrix i).conjTranspose = 1 := by simp


-- @@ L124-126 verbatim
theorem coordinateSignMatrix_unitary (i : Fin n) :
    coordinateSignMatrix i ∈ Matrix.unitaryGroup (Cube n) ℂ :=
  signMatrix_unitary _ (fun x => cubeCoord_cases x i)


-- @@ L128-130 verbatim
theorem coordinateSignMatrix_commute_diagonal (i : Fin n) (d : Cube n → ℂ) :
    Commute (coordinateSignMatrix i) (Matrix.diagonal d) :=
  signMatrix_commute_diagonal _ d


-- @@ L132-135 verbatim
theorem coordinateSignMatrix_mul_diagonal_comm (i : Fin n) (d : Cube n → ℂ) :
    coordinateSignMatrix i * Matrix.diagonal d =
      Matrix.diagonal d * coordinateSignMatrix i :=
  (coordinateSignMatrix_commute_diagonal i d).eq


-- @@ L137-139 verbatim
@[simp] theorem coordinateSignMatrix_mulVec (i : Fin n) (v : Cube n → ℂ) (x : Cube n) :
    (coordinateSignMatrix i *ᵥ v) x = (cubeCoord x i : ℂ) * v x :=
  signMatrix_mulVec _ v x


-- @@ L141-143 verbatim
@[simp] theorem hsNormSq_coordinateSignMatrix (i : Fin n) :
    hsNormSq (coordinateSignMatrix i) = (2 : ℝ) ^ n :=
  hsNormSq_signMatrix _ (fun x => cubeCoord_cases x i)


-- @@ L145-148 verbatim
/-- The same diagonal action on the counting-inner-product Euclidean space. -/
def signMultiplier (h : Cube n → ℝ) :
    EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n) :=
  Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)


-- @@ L150-153 verbatim
/-- The actual coordinate multiplier on Euclidean space. -/
def coordinateMultiplier (i : Fin n) :
    EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n) :=
  signMultiplier (fun x => cubeCoord x i)


-- @@ L155-156 verbatim
@[simp] theorem toEuclideanCLM_signMatrix (h : Cube n → ℝ) :
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) = signMultiplier h := rfl


-- @@ L158-160 verbatim
@[simp] theorem toEuclideanCLM_coordinateSignMatrix (i : Fin n) :
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (coordinateSignMatrix i) =
      coordinateMultiplier i := rfl


-- @@ L162-166 verbatim
@[simp] theorem signMultiplier_apply (h : Cube n → ℝ)
    (v : EuclideanSpace ℂ (Cube n)) (x : Cube n) :
    signMultiplier h v x = (h x : ℂ) * v x := by
  change (signMatrix h *ᵥ fun y => v y) x = _
  exact signMatrix_mulVec h _ x


-- @@ L168-171 verbatim
@[simp] theorem coordinateMultiplier_apply (i : Fin n)
    (v : EuclideanSpace ℂ (Cube n)) (x : Cube n) :
    coordinateMultiplier i v x = (cubeCoord x i : ℂ) * v x :=
  signMultiplier_apply _ v x


-- @@ L173-177 verbatim
theorem signMultiplier_isSelfAdjoint (h : Cube n → ℝ) :
    IsSelfAdjoint (signMultiplier h) := by
  change star (Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)) =
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)
  rw [← map_star, signMatrix_star]


-- @@ L179-180 verbatim
theorem coordinateMultiplier_isSelfAdjoint (i : Fin n) :
    IsSelfAdjoint (coordinateMultiplier i) := signMultiplier_isSelfAdjoint _


-- @@ L182-186 verbatim
theorem signMultiplier_mul_self (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : signMultiplier h * signMultiplier h = 1 := by
  change Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) *
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) = 1
  rw [← map_mul, signMatrix_mul_self h hh, map_one]


-- @@ L188-190 verbatim
@[simp] theorem coordinateMultiplier_mul_self (i : Fin n) :
    coordinateMultiplier i * coordinateMultiplier i = 1 :=
  signMultiplier_mul_self _ (fun x => cubeCoord_cases x i)


-- @@ L192-199 verbatim
theorem norm_signMultiplier_apply (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) (v : EuclideanSpace ℂ (Cube n)) :
    ‖signMultiplier h v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  rcases hh x with hx | hx <;> simp [signMultiplier_apply, hx]


-- @@ L201-203 verbatim
@[simp] theorem norm_coordinateMultiplier_apply (i : Fin n)
    (v : EuclideanSpace ℂ (Cube n)) : ‖coordinateMultiplier i v‖ = ‖v‖ :=
  norm_signMultiplier_apply _ (fun x => cubeCoord_cases x i) v


-- @@ L205-209 verbatim
theorem norm_signMultiplier_le_one (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : ‖signMultiplier h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp [norm_signMultiplier_apply h hh]


-- @@ L211-212 verbatim
theorem norm_coordinateMultiplier_le_one (i : Fin n) : ‖coordinateMultiplier i‖ ≤ 1 :=
  norm_signMultiplier_le_one _ (fun x => cubeCoord_cases x i)


-- @@ L214-214 verbatim
end LeanBlast.GotsmanLinial


-- @@ L216-216 verbatim
end


-- @@ L218-218 verbatim
end OAI
