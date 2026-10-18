import OAI.AlgebraicGeometry.StableCoordinate.Definitions
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-14 verbatim
/-!
# The explicit polynomial has total degree five

The leading homogeneous part is `-2 * Q^2 * (X 1 + X 3)`, of degree five.
The remaining part has degree at most four.  Nonvanishing is checked by
ordinary evaluation, rather than assumed from a displayed expression.
-/


-- @@ L16-16 verbatim
namespace StableCoordinate


-- @@ L18-18 verbatim
open MvPolynomial


-- @@ L20-25 verbatim
/-- The quadratic form in the displayed formula is homogeneous of degree two. -/
theorem Q_isHomogeneous : Q.IsHomogeneous 2 := by
  unfold Q
  exact ((isHomogeneous_X_pow (1 : Fin 4) 2).sub
    (isHomogeneous_X_pow (3 : Fin 4) 2)).add
    ((isHomogeneous_X ℂ (0 : Fin 4)).mul (isHomogeneous_X ℂ (2 : Fin 4)))


-- @@ L27-31 verbatim
/-- Evaluate at `(x₁,x₂,x₃,x₄)=(0,1,0,0)`. -/
theorem Q_ne_zero : Q ≠ 0 := by
  intro h
  have he := congrArg (eval (fun i : Fin 4 => if i.val = 1 then (1 : ℂ) else 0)) h
  norm_num [Q] at he


-- @@ L33-34 verbatim
/-- The source's quadratic auxiliary expression has exact degree two. -/
theorem Q_totalDegree : Q.totalDegree = 2 := Q_isHomogeneous.totalDegree Q_ne_zero


-- @@ L36-39 verbatim
private theorem x2_add_x4_ne_zero : (X (1 : Fin 4) + X 3 : R 4) ≠ 0 := by
  intro h
  have he := congrArg (eval (fun i : Fin 4 => if i.val = 1 then (1 : ℂ) else 0)) h
  norm_num at he


-- @@ L41-72 verbatim
/-- The exact degree-five property advertised by the principal target. -/
theorem f_totalDegree : f.totalDegree = 5 := by
  let top : R 4 := -(2 * Q ^ 2 * (X 1 + X 3))
  let low : R 4 := X 0 - 2 * Q * (X 0 * X 3)
  have htop_hom : top.IsHomogeneous 5 := by
    have hh := (((Q_isHomogeneous.pow 2).mul
      ((isHomogeneous_X ℂ (1 : Fin 4)).add (isHomogeneous_X ℂ (3 : Fin 4)))).C_mul
        (2 : ℂ)).neg
    simpa only [top, map_ofNat, mul_assoc, show 2 * 2 + 1 = 5 from rfl] using hh
  have htop_ne : top ≠ 0 := by
    dsimp [top]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 Q_ne_zero))
      x2_add_x4_ne_zero)
  have htop_deg : top.totalDegree = 5 := htop_hom.totalDegree htop_ne
  have hnum : (2 : R 4).totalDegree = 0 := by
    rw [← map_ofNat (C : ℂ →+* R 4) 2, totalDegree_C]
  have hinner : (X (0 : Fin 4) * X 3 : R 4).totalDegree ≤ 2 := by
    simpa using totalDegree_mul (X (0 : Fin 4) : R 4) (X 3)
  have hmul : (2 * Q * (X 0 * X 3) : R 4).totalDegree ≤ 4 := by
    calc
      _ ≤ (2 * Q : R 4).totalDegree + (X 0 * X 3 : R 4).totalDegree := totalDegree_mul _ _
      _ ≤ ((2 : R 4).totalDegree + Q.totalDegree) + 2 :=
        Nat.add_le_add (totalDegree_mul _ _) hinner
      _ = 4 := by rw [hnum, Q_totalDegree]
  have hlow_deg : low.totalDegree ≤ 4 := by
    exact (totalDegree_sub _ _).trans (max_le (by simp) hmul)
  have hsplit : f = top + low := by
    dsimp [f, top, low]
    ring
  rw [hsplit, totalDegree_add_eq_left_of_totalDegree_lt]
  · exact htop_deg
  · omega


-- @@ L74-74 verbatim
end StableCoordinate


-- @@ L76-76 verbatim
end OAI
