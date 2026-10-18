import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-11 verbatim
/-!
# The determinant-one linear substitution in the stabilization construction

This module formalizes the `L,N` change of variables in Section 2 of the source.
It uses six genuinely independent polynomial generators, in the order
`p,s,u,F,J,w`.  All results hold over any commutative coefficient ring.
-/


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
namespace StableCoordinate.Linearization


-- @@ L17-17 verbatim
open MvPolynomial


-- @@ L19-19 verbatim
variable (k : Type*) [CommRing k]


-- @@ L21-21 verbatim
abbrev P := MvPolynomial (Fin 6) k


-- @@ L23-24 verbatim
/-- The part of the auxiliary quadratic not containing `p`. -/
def x0 : P k := X 1 ^ 2 - X 2 ^ 2


-- @@ L26-27 verbatim
/-- The first new linear coordinate, denoted `L` in the manuscript. -/
def l : P k := x0 k ^ 2 * X 3 - (1 + 2 * X 1 * x0 k) * X 4


-- @@ L29-30 verbatim
/-- The second new linear coordinate, denoted `N` in the manuscript. -/
def n : P k := (1 - 2 * X 1 * x0 k) * X 3 + 4 * X 1 ^ 2 * X 4


-- @@ L32-33 verbatim
/-- The inverse formula for `F` in terms of the slots now called `L,N`. -/
def inverseF : P k := 4 * X 1 ^ 2 * X 3 + (1 + 2 * X 1 * x0 k) * X 4


-- @@ L35-36 verbatim
/-- The inverse formula for `J` in terms of the slots now called `L,N`. -/
def inverseJ : P k := -(1 - 2 * X 1 * x0 k) * X 3 + x0 k ^ 2 * X 4


-- @@ L38-40 verbatim
/-- Substitution `F ↦ L`, `J ↦ N`, fixing the other four generators. -/
def forward : P k →ₐ[k] P k :=
  aeval ![X 0, X 1, X 2, l k, n k, X 5]


-- @@ L42-44 verbatim
/-- The inverse determinant-one substitution. -/
def backward : P k →ₐ[k] P k :=
  aeval ![X 0, X 1, X 2, inverseF k, inverseJ k, X 5]


-- @@ L46-48 verbatim
@[simp] theorem forward_X (i : Fin 6) :
    forward k (X i) = ![X 0, X 1, X 2, l k, n k, X 5] i := by
  simp [forward]


-- @@ L50-52 verbatim
@[simp] theorem backward_X (i : Fin 6) :
    backward k (X i) = ![X 0, X 1, X 2, inverseF k, inverseJ k, X 5] i := by
  simp [backward]


-- @@ L54-55 verbatim
@[simp] theorem forward_x0 : forward k (x0 k) = x0 k := by
  simp [x0]


-- @@ L57-58 verbatim
@[simp] theorem backward_x0 : backward k (x0 k) = x0 k := by
  simp [x0]

 
-- @@ L60-62 verbatim
theorem backward_comp_forward : (backward k).comp (forward k) = AlgHom.id k (P k) := by
  ext i : 1
  fin_cases i <;> simp [l, n, inverseF, inverseJ, map_ofNat] <;> ring

 
-- @@ L64-66 verbatim
theorem forward_comp_backward : (forward k).comp (backward k) = AlgHom.id k (P k) := by
  ext i : 1
  fin_cases i <;> simp [l, n, inverseF, inverseJ, map_ofNat] <;> ring


-- @@ L68-71 verbatim
/-- The exact determinant-one `L,N` change is a polynomial algebra automorphism. -/
def equiv : P k ≃ₐ[k] P k :=
  AlgEquiv.ofAlgHom (forward k) (backward k)
    (forward_comp_backward k) (backward_comp_forward k)


-- @@ L73-73 verbatim
@[simp] theorem equiv_apply (p : P k) : equiv k p = forward k p := rfl


-- @@ L75-75 verbatim
@[simp] theorem equiv_symm_apply (p : P k) : (equiv k).symm p = backward k p := rfl


-- @@ L77-78 verbatim
/-- The source's auxiliary quadratic including `p F`. -/
def x : P k := x0 k + X 0 * X 3


-- @@ L80-81 verbatim
/-- The source hypersurface relation, extended by the independent variable `w`. -/
def h : P k := x k ^ 2 * X 3 - (1 + 2 * X 1 * x k) * X 4 - X 0 * X 4 ^ 2 - X 2


-- @@ L83-84 verbatim
/-- The polynomial remainder `Q₀` in the source equation `H = L-u+p Q₀`. -/
def q0 : P k := 2 * x0 k * X 3 ^ 2 + X 0 * X 3 ^ 3 - 2 * X 1 * X 3 * X 4 - X 4 ^ 2


-- @@ L86-89 verbatim
/-- The divisibility identity used to remove the nonlinear remainder. -/
theorem h_expansion : h k = l k - X 2 + X 0 * q0 k := by
  unfold h x l q0
  ring


-- @@ L91-94 verbatim
/-- `Q₀` written in the new linear coordinates. -/
def qTrans : P k :=
  2 * x0 k * inverseF k ^ 2 + X 0 * inverseF k ^ 3 -
    2 * X 1 * inverseF k * inverseJ k - inverseJ k ^ 2


-- @@ L96-97 verbatim
@[simp] theorem backward_q0 : backward k (q0 k) = qTrans k := by
  simp [q0, qTrans, map_ofNat]


-- @@ L99-101 verbatim
@[simp] theorem backward_l : backward k (l k) = X 3 := by
  have hh := DFunLike.congr_fun (backward_comp_forward k) (X 3)
  simpa using hh


-- @@ L103-105 verbatim
@[simp] theorem backward_n : backward k (n k) = X 4 := by
  have hh := DFunLike.congr_fun (backward_comp_forward k) (X 4)
  simpa using hh


-- @@ L107-110 verbatim
/-- The source equation after the inverse `L,N` substitution. -/
theorem backward_h : backward k (h k) = X 3 - X 2 + X 0 * qTrans k := by
  rw [h_expansion]
  simp


-- @@ L112-114 verbatim
/-- Subtract the transformed remainder from the independent new variable. -/
def minusShear : P k →ₐ[k] P k :=
  aeval ![X 0, X 1, X 2, X 3, X 4, X 5 - qTrans k]


-- @@ L116-118 verbatim
/-- Inverse shear, adding the transformed remainder. -/
def plusShear : P k →ₐ[k] P k :=
  aeval ![X 0, X 1, X 2, X 3, X 4, X 5 + qTrans k]


-- @@ L120-122 verbatim
@[simp] theorem minusShear_X (i : Fin 6) :
    minusShear k (X i) = ![X 0, X 1, X 2, X 3, X 4, X 5 - qTrans k] i := by
  simp [minusShear]


-- @@ L124-126 verbatim
@[simp] theorem plusShear_X (i : Fin 6) :
    plusShear k (X i) = ![X 0, X 1, X 2, X 3, X 4, X 5 + qTrans k] i := by
  simp [plusShear]


-- @@ L128-129 verbatim
@[simp] theorem minusShear_qTrans : minusShear k (qTrans k) = qTrans k := by
  simp [qTrans, inverseF, inverseJ, x0, map_ofNat]


-- @@ L131-132 verbatim
@[simp] theorem plusShear_qTrans : plusShear k (qTrans k) = qTrans k := by
  simp [qTrans, inverseF, inverseJ, x0, map_ofNat]

 
-- @@ L134-137 verbatim
theorem plusShear_comp_minusShear :
    (plusShear k).comp (minusShear k) = AlgHom.id k (P k) := by
  ext i : 1
  fin_cases i <;> simp

 
-- @@ L139-142 verbatim
theorem minusShear_comp_plusShear :
    (minusShear k).comp (plusShear k) = AlgHom.id k (P k) := by
  ext i : 1
  fin_cases i <;> simp


-- @@ L144-147 verbatim
/-- The independent-variable shear is a polynomial algebra automorphism. -/
def shearEquiv : P k ≃ₐ[k] P k :=
  AlgEquiv.ofAlgHom (minusShear k) (plusShear k)
    (minusShear_comp_plusShear k) (plusShear_comp_minusShear k)


-- @@ L149-149 verbatim
@[simp] theorem shearEquiv_apply (p : P k) : shearEquiv k p = minusShear k p := rfl


-- @@ L151-154 verbatim
/-- The full linearization automorphism, turning `H+p w` into an equation linear
in the slot formerly called `F`, while fixing `p`. -/
def normalization : P k ≃ₐ[k] P k :=
  (equiv k).symm.trans (shearEquiv k)


-- @@ L156-157 verbatim
@[simp] theorem normalization_p : normalization k (X 0) = X 0 := by
  simp [normalization]


-- @@ L159-160 verbatim
@[simp] theorem normalization_s : normalization k (X 1) = X 1 := by
  simp [normalization]


-- @@ L162-163 verbatim
@[simp] theorem normalization_u : normalization k (X 2) = X 2 := by
  simp [normalization]


-- @@ L165-170 verbatim
/-- The exact polynomial equation needed for the final variable elimination. -/
theorem normalization_stabilized_h :
    normalization k (h k + X 0 * X 5) = X 3 - X 2 + X 0 * X 5 := by
  change minusShear k (backward k (h k + X 0 * X 5)) = _
  simp [backward_h]
  ring


-- @@ L172-172 verbatim
end StableCoordinate.Linearization


-- @@ L174-174 verbatim
end


-- @@ L176-176 verbatim
end OAI
