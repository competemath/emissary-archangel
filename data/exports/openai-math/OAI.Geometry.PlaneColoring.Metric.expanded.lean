import OAI.Geometry.PlaneColoring.Basic


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace Problem160


-- @@ L9-12 verbatim
/-- Triangular lattice with nearest-neighbor spacing `4/5`. -/
def triangularLattice (a b : ℤ) : Plane :=
  WithLp.toLp 2 ![(4 / 5 : ℝ) * ((a : ℝ) + (b : ℝ)/2),
    (2 * Real.sqrt 3 / 5 : ℝ) * b]


-- @@ L14-15 verbatim
@[simp] theorem triangularLattice_zero (a b : ℤ) :
    triangularLattice a b 0 = (4 / 5 : ℝ) * ((a : ℝ) + (b : ℝ)/2) := rfl


-- @@ L17-18 verbatim
@[simp] theorem triangularLattice_one (a b : ℤ) :
    triangularLattice a b 1 = (2 * Real.sqrt 3 / 5 : ℝ) * b := rfl


-- @@ L20-27 verbatim
theorem triangularLattice_norm_sq (a b : ℤ) :
    ‖triangularLattice a b‖ ^ 2 =
      (16 / 25 : ℝ) * ((a : ℝ)^2 + (a : ℝ)*b + (b : ℝ)^2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, triangularLattice_zero, triangularLattice_one]
  ring_nf
  norm_num
  ring


-- @@ L29-32 verbatim
theorem triangularLattice_sub (a b c d : ℤ) :
    triangularLattice a b - triangularLattice c d = triangularLattice (a-c) (b-d) := by
  ext i
  fin_cases i <;> simp [triangularLattice] <;> ring


-- @@ L34-38 verbatim
theorem triangularLattice_dist_sq (a b c d : ℤ) :
    dist (triangularLattice a b) (triangularLattice c d) ^ 2 =
      (16 / 25 : ℝ) * (((a-c : ℤ) : ℝ)^2 +
        ((a-c : ℤ) : ℝ)*(b-d : ℤ) + ((b-d : ℤ) : ℝ)^2) := by
  rw [dist_eq_norm, triangularLattice_sub, triangularLattice_norm_sq]


-- @@ L40-48 verbatim
theorem triangularLattice_dist_gt_two (a b c d : ℤ)
    (h : 7 ≤ (a-c)^2 + (a-c)*(b-d) + (b-d)^2) :
    (2 : ℝ) < dist (triangularLattice a b) (triangularLattice c d) := by
  have hr : (7 : ℝ) ≤ ((a-c : ℤ) : ℝ)^2 +
      ((a-c : ℤ) : ℝ)*(b-d : ℤ) + ((b-d : ℤ) : ℝ)^2 := by
    exact_mod_cast h
  have heq := triangularLattice_dist_sq a b c d
  have hd := dist_nonneg (x := triangularLattice a b) (y := triangularLattice c d)
  nlinarith


-- @@ L50-58 verbatim
theorem dist_triangularLattice_sq (x : Plane) (a b : ℤ) :
    dist x (triangularLattice a b)^2 =
      (16 / 25 : ℝ) *
        (((5 / 4 : ℝ) * x 0 - ((a : ℝ) + (b : ℝ)/2))^2 +
         ((5 / 4 : ℝ) * x 1 - Real.sqrt 3 * b / 2)^2) := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, triangularLattice_zero,
    triangularLattice_one]
  ring


-- @@ L60-66 verbatim
theorem dist_triangularLattice_le_of_coordinates (x : Plane) (a b : ℤ)
    (h : ((5 / 4 : ℝ) * x 0 - ((a : ℝ) + (b : ℝ)/2))^2 +
         ((5 / 4 : ℝ) * x 1 - Real.sqrt 3 * b / 2)^2 ≤ (1 / 3 : ℝ)) :
    dist x (triangularLattice a b) ≤ (7 / 15 : ℝ) := by
  have heq := dist_triangularLattice_sq x a b
  have hd := dist_nonneg (x := x) (y := triangularLattice a b)
  nlinarith


-- @@ L68-68 verbatim
end Problem160


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
end OAI
