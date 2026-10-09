import OAI.AlgebraicGeometry.AbhyankarSathaye.Presentation
import Mathlib.Algebra.MvPolynomial.Equiv


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-11 verbatim
/-!
# The polynomial algebra structure of the zero fiber

Composing elimination, lifting, the plane parametrization, and a permutation
of variables gives the complex algebra isomorphism with `ℂ[X,Y,T]`.
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
namespace AbhyankarSathaye

-- @@ L15-15 verbatim
open MvPolynomial Presentation


-- @@ L17-21 verbatim
def variableOrder : Fin 3 ≃ Fin 3 where
  toFun := ![2,0,1]
  invFun := ![1,2,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl


-- @@ L23-24 verbatim
def flattenPlane : Polynomial (MvPolynomial (Fin 2) ℂ) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  (MvPolynomial.finSuccEquiv ℂ 2).symm.trans (renameEquiv ℂ variableOrder)


-- @@ L26-29 verbatim
@[simp] theorem flattenPlane_symm_X0 : flattenPlane.symm (X 0) = Polynomial.C (X 0) := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 0)) = _
  rw [rename_X]
  exact finSuccEquiv_X_succ (j := (0 : Fin 2))


-- @@ L31-34 verbatim
@[simp] theorem flattenPlane_symm_X1 : flattenPlane.symm (X 1) = Polynomial.C (X 1) := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 1)) = _
  rw [rename_X]
  exact finSuccEquiv_X_succ (j := (1 : Fin 2))


-- @@ L36-39 verbatim
@[simp] theorem flattenPlane_symm_X2 : flattenPlane.symm (X 2) = Polynomial.X := by
  change MvPolynomial.finSuccEquiv ℂ 2 (rename variableOrder.symm (X 2)) = _
  rw [rename_X]
  exact finSuccEquiv_X_zero


-- @@ L41-43 verbatim
@[simp] theorem flattenPlane_C_X0 : flattenPlane (Polynomial.C (X 0)) = X 0 := by
  apply flattenPlane.symm.injective
  simp

-- @@ L44-46 verbatim
@[simp] theorem flattenPlane_C_X1 : flattenPlane (Polynomial.C (X 1)) = X 1 := by
  apply flattenPlane.symm.injective
  simp

-- @@ L47-49 verbatim
@[simp] theorem flattenPlane_X : flattenPlane Polynomial.X = X 2 := by
  apply flattenPlane.symm.injective
  simp


-- @@ L51-53 verbatim
def liftedEquiv : L ≃ₐ[ℂ] Polynomial B :=
  (Lifting.equivalence hB xB yB sB (Alpha xB sB) (Beta xB yB sB)
    (Plane.relation_cusp ℂ) (Plane.bezout ℂ)).restrictScalars ℂ


-- @@ L55-56 verbatim
def planeExtensionEquiv : Polynomial B ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 2) ℂ) :=
  Polynomial.mapAlgEquiv (Plane.equivalence ℂ)


-- @@ L58-60 verbatim
def fiberEquiv : (R ⧸ Ideal.span {F}) ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  Presentation.eliminationEquiv.symm.trans
    (liftedEquiv.trans (planeExtensionEquiv.trans flattenPlane))


-- @@ L62-62 verbatim
end AbhyankarSathaye


-- @@ L64-64 verbatim
end


-- @@ L66-66 verbatim
end OAI
