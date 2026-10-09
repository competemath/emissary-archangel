import Mathlib.LinearAlgebra.Matrix.Determinant.Basic


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators


-- @@ L8-8 verbatim
namespace DiagonalZonotope

-- @@ L9-9 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]


-- @@ L11-20 verbatim
/-- Replacing one identity column by the all-ones vector leaves determinant one. -/
theorem det_identity_updateCol_ones (i : ι) :
    ((1 : Matrix ι ι R).updateCol i (fun _ => 1)).det = 1 := by
  have h := Matrix.det_updateCol_sum (1 : Matrix ι ι R) i (fun _ => (1 : R))
  have hc : (fun k : ι => ∑ j : ι, (1 : R) • (1 : Matrix ι ι R) k j) =
      (fun _ : ι => (1 : R)) := by
    funext k
    simp [Matrix.one_apply]
  rw [hc] at h
  simpa using h


-- @@ L22-22 verbatim
end DiagonalZonotope


-- @@ L24-24 verbatim
end


-- @@ L26-26 verbatim
end OAI
