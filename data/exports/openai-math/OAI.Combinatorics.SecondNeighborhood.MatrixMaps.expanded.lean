import OAI.Combinatorics.SecondNeighborhood.PruningDefinitions
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
namespace SeymourSecondNeighborhood.Pruning


-- @@ L9-9 verbatim
variable {V : Type*}


-- @@ L11-12 verbatim
def SupportedCoefficients (r : V → V → Prop) (a : V → V → ℝ) : Prop :=
  ∀ x y, ¬ r x y → a x y = 0


-- @@ L14-18 verbatim
theorem SupportedCoefficients.of_ne_zero {r : V → V → Prop}
    {a : V → V → ℝ} (ha : SupportedCoefficients r a) {x y : V}
    (hxy : a x y ≠ 0) : r x y := by
  by_contra h
  exact hxy (ha x y h)


-- @@ L20-20 verbatim
variable [Fintype V] [DecidableEq V]


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-26 verbatim
def matrixL (r : V → V → Prop) (R C : Finset (V × V)) (a : V → V → ℝ) :
    Matrix ↥(Z r R C) ↥R ℝ :=
  Matrix.of fun z left => if z.val.2 = left.val.2 then a left.val.1 z.val.1 else 0


-- @@ L28-30 verbatim
def matrixN (r : V → V → Prop) (R C : Finset (V × V)) (b : V → V → ℝ) :
    Matrix ↥C ↥(Z r R C) ℝ :=
  Matrix.of fun right z => if right.val.1 = z.val.1 then b right.val.2 z.val.2 else 0


-- @@ L32-34 verbatim
def matrixB (r : V → V → Prop) (R C : Finset (V × V)) (b : V → V → ℝ) :
    Matrix ↥(H r R C) ↥R ℝ :=
  Matrix.of fun h left => if h.val.1 = left.val.1 then b h.val.2 left.val.2 else 0


-- @@ L36-38 verbatim
def matrixA (r : V → V → Prop) (R C : Finset (V × V)) (a : V → V → ℝ) :
    Matrix ↥C ↥(H r R C) ℝ :=
  Matrix.of fun right h => if right.val.2 = h.val.2 then a h.val.1 right.val.1 else 0


-- @@ L40-43 verbatim
@[simp] theorem matrixL_apply (r : V → V → Prop) (R C : Finset (V × V))
    (a : V → V → ℝ) (z : ↥(Z r R C)) (left : ↥R) :
    matrixL r R C a z left =
      if z.val.2 = left.val.2 then a left.val.1 z.val.1 else 0 := rfl


-- @@ L45-48 verbatim
@[simp] theorem matrixN_apply (r : V → V → Prop) (R C : Finset (V × V))
    (b : V → V → ℝ) (right : ↥C) (z : ↥(Z r R C)) :
    matrixN r R C b right z =
      if right.val.1 = z.val.1 then b right.val.2 z.val.2 else 0 := rfl


-- @@ L50-53 verbatim
@[simp] theorem matrixB_apply (r : V → V → Prop) (R C : Finset (V × V))
    (b : V → V → ℝ) (h : ↥(H r R C)) (left : ↥R) :
    matrixB r R C b h left =
      if h.val.1 = left.val.1 then b h.val.2 left.val.2 else 0 := rfl


-- @@ L55-58 verbatim
@[simp] theorem matrixA_apply (r : V → V → Prop) (R C : Finset (V × V))
    (a : V → V → ℝ) (right : ↥C) (h : ↥(H r R C)) :
    matrixA r R C a right h =
      if right.val.2 = h.val.2 then a h.val.1 right.val.1 else 0 := rfl


-- @@ L60-60 verbatim
end

-- @@ L61-61 verbatim
end SeymourSecondNeighborhood.Pruning


-- @@ L63-63 verbatim
end OAI
