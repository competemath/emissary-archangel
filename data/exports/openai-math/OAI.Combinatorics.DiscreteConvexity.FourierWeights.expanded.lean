import OAI.Combinatorics.DiscreteConvexity.Bernoulli
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators


-- @@ L9-9 verbatim
namespace TalagrandDiscreteConvexity


-- @@ L11-13 verbatim
/-- The alternating factor for a coordinate inside the differentiated set. -/
def correction (q : ℝ) (bit : Bool) : ℝ :=
  if bit then -(1 - q) else 1 - q


-- @@ L15-15 verbatim
@[simp] theorem correction_false (q : ℝ) : correction q false = 1 - q := rfl


-- @@ L17-17 verbatim
@[simp] theorem correction_true (q : ℝ) : correction q true = -(1 - q) := rfl


-- @@ L19-19 verbatim
variable {V : Type*} [Fintype V] [DecidableEq V]


-- @@ L21-23 verbatim
/-- Coordinate product defining the alternating partial expectation. -/
def rowKernel (q : ℝ) (U : Finset V) (x : V → Bool) : ℝ :=
  ∏ i, if i ∈ U then correction q (x i) else bitWeight q (x i)


-- @@ L25-28 verbatim
/-- Exactly `(1-q)^|U|` times the alternating sum over the coordinates in `U`,
with independent Bernoulli expectation on its complement. -/
def b (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) : ℝ :=
  ∑ x, f x * rowKernel q U x


-- @@ L30-32 verbatim
/-- The nonnegative weights used by both global and exceptional-set bounds. -/
def w (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) : ℝ :=
  (b q f U) ^ 2


-- @@ L34-54 verbatim
/-- Separate the alternating coordinates from the independent outside mass. -/
theorem rowKernel_eq_alternating_product (q : ℝ) (U : Finset V) (x : V → Bool) :
    rowKernel q U x = (1 - q) ^ U.card *
      (∏ i ∈ U, if x i then (-1 : ℝ) else 1) *
      ∏ i ∈ Finset.univ \ U, bitWeight q (x i) := by
  have hsplit : rowKernel q U x =
      (∏ i ∈ U, correction q (x i)) *
        ∏ i ∈ Finset.univ \ U, bitWeight q (x i) := by
    simpa only [rowKernel, Finset.piecewise, Finset.univ_inter] using
      (Finset.prod_piecewise Finset.univ U
        (fun i => correction q (x i)) (fun i => bitWeight q (x i)))
  have hc : (∏ i ∈ U, correction q (x i)) =
      (1 - q) ^ U.card * ∏ i ∈ U, if x i then (-1 : ℝ) else 1 := by
    calc
      (∏ i ∈ U, correction q (x i)) =
          ∏ i ∈ U, (1 - q) * (if x i then (-1 : ℝ) else 1) := by
        apply Finset.prod_congr rfl
        intro i _
        cases x i <;> simp [correction]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [hsplit, hc]


-- @@ L56-64 verbatim
/-- The explicit alternating partial-expectation formula for the coefficient. -/
theorem b_eq_alternating_sum (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) :
    b q f U = (1 - q) ^ U.card *
      ∑ x, f x * (∏ i ∈ U, if x i then (-1 : ℝ) else 1) *
        ∏ i ∈ Finset.univ \ U, bitWeight q (x i) := by
  simp only [b, rowKernel_eq_alternating_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ac_rfl


-- @@ L66-68 verbatim
@[simp] theorem rowKernel_empty (q : ℝ) (x : V → Bool) :
    rowKernel q ∅ x = cubeWeight q x := by
  simp [rowKernel, cubeWeight]


-- @@ L70-76 verbatim
/-- The empty coefficient is the original biased expectation. -/
@[simp] theorem b_empty (q : ℝ) (f : (V → Bool) → ℝ) :
    b q f ∅ = cubeExpectation q f := by
  simp only [b, rowKernel_empty, cubeExpectation]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _


-- @@ L78-79 verbatim
theorem w_nonneg (q : ℝ) (f : (V → Bool) → ℝ) (U : Finset V) :
    0 ≤ w q f U := sq_nonneg _


-- @@ L81-81 verbatim
end TalagrandDiscreteConvexity


-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end OAI
