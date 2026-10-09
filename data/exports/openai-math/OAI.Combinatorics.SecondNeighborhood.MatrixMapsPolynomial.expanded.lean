import OAI.Combinatorics.SecondNeighborhood.GenericRankCoefficients
import OAI.Combinatorics.SecondNeighborhood.MatrixMaps


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SeymourSecondNeighborhood.Pruning


-- @@ L8-8 verbatim
open scoped Classical Matrix


-- @@ L10-10 verbatim
variable {X : Type*} [Fintype X] [DecidableEq X]


-- @@ L12-16 verbatim
noncomputable def matrixLPolynomial (r : X → X → Prop) (R C : Finset (X × X)) :
    Matrix ↥(Z r R C) ↥R (MvPolynomial (CoefficientVariables X) ℝ) :=
  supportedVariableMatrix
    (fun z left => z.1.2 = left.1.2 ∧ r left.1.1 z.1.1)
    (fun z left => Sum.inl (left.1.1, z.1.1))


-- @@ L18-22 verbatim
noncomputable def matrixNPolynomial (r : X → X → Prop) (R C : Finset (X × X)) :
    Matrix ↥C ↥(Z r R C) (MvPolynomial (CoefficientVariables X) ℝ) :=
  supportedVariableMatrix
    (fun right z => right.1.1 = z.1.1 ∧ r right.1.2 z.1.2)
    (fun right z => Sum.inr (right.1.2, z.1.2))


-- @@ L24-31 verbatim
@[simp] theorem matrixLPolynomial_apply (r : X → X → Prop)
    (R C : Finset (X × X)) (z : ↥(Z r R C)) (left : ↥R) :
    matrixLPolynomial r R C z left =
      if z.1.2 = left.1.2 ∧ r left.1.1 z.1.1
      then MvPolynomial.X (Sum.inl (left.1.1, z.1.1)) else 0 := by
  classical
  by_cases h : z.1.2 = left.1.2 ∧ r left.1.1 z.1.1 <;>
    simp [matrixLPolynomial, supportedVariableMatrix, h]


-- @@ L33-40 verbatim
@[simp] theorem matrixNPolynomial_apply (r : X → X → Prop)
    (R C : Finset (X × X)) (right : ↥C) (z : ↥(Z r R C)) :
    matrixNPolynomial r R C right z =
      if right.1.1 = z.1.1 ∧ r right.1.2 z.1.2
      then MvPolynomial.X (Sum.inr (right.1.2, z.1.2)) else 0 := by
  classical
  by_cases h : right.1.1 = z.1.1 ∧ r right.1.2 z.1.2 <;>
    simp [matrixNPolynomial, supportedVariableMatrix, h]


-- @@ L42-51 verbatim
@[simp] theorem eval_matrixLPolynomial (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixLPolynomial r R C) =
      matrixL r R C (selectedA r v) := by
  classical
  ext z left
  by_cases hcoord : z.1.2 = left.1.2 <;>
    by_cases harrow : r left.1.1 z.1.1 <;>
    simp [evalPolynomialMatrix_apply, matrixLPolynomial_apply, matrixL_apply,
      selectedA, hcoord, harrow]


-- @@ L53-62 verbatim
@[simp] theorem eval_matrixNPolynomial (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixNPolynomial r R C) =
      matrixN r R C (selectedB r v) := by
  classical
  ext right z
  by_cases hcoord : right.1.1 = z.1.1 <;>
    by_cases harrow : r right.1.2 z.1.2 <;>
    simp [evalPolynomialMatrix_apply, matrixNPolynomial_apply, matrixN_apply,
      selectedB, hcoord, harrow]


-- @@ L64-70 verbatim
@[simp] theorem eval_matrixNPolynomial_transpose (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixNPolynomial r R C)ᵀ =
      (matrixN r R C (selectedB r v))ᵀ := by
  have h := eval_matrixNPolynomial r R C v
  ext z right
  exact congrFun (congrFun h right) z


-- @@ L72-72 verbatim
end SeymourSecondNeighborhood.Pruning


-- @@ L74-74 verbatim
end OAI
