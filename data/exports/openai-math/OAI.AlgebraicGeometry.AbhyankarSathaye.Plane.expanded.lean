import OAI.AlgebraicGeometry.AbhyankarSathaye.Quotient
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# A polynomial presentation of the affine plane

The relations `h = 1 + P x y s` and `x² + y³ = h * s` give a polynomial
algebra with coordinates `x + s³` and `y - s²`. The auxiliary variables are
ordered as `h, x, y, s`.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
namespace AbhyankarSathaye.Plane

-- @@ L17-17 verbatim
open MvPolynomial


-- @@ L19-19 verbatim
variable (K : Type*) [CommRing K]


-- @@ L21-21 verbatim
def relH : MvPolynomial (Fin 4) K := X 0-1-P (X 1) (X 2) (X 3)

-- @@ L22-22 verbatim
def relCusp : MvPolynomial (Fin 4) K := X 1^2+X 2^3-X 3*X 0

-- @@ L23-23 verbatim
def ideal : Ideal (MvPolynomial (Fin 4) K) := Ideal.span {relH K, relCusp K}

-- @@ L24-24 verbatim
abbrev Q := MvPolynomial (Fin 4) K ⧸ ideal K

-- @@ L25-25 verbatim
def qmap : MvPolynomial (Fin 4) K →ₐ[K] Q K := Ideal.Quotient.mkₐ K (ideal K)

-- @@ L26-26 verbatim
def qvar (i : Fin 4) : Q K := qmap K (X i)


-- @@ L28-35 verbatim
theorem relation_h : qvar K 0 = 1+P (qvar K 1) (qvar K 2) (qvar K 3) := by
  have hz : qmap K (relH K) = 0 := quotient_pair_left (relH K) (relCusp K)
  have hh : qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3) = 0 := by
    simpa [relH, qvar] using hz
  calc
    _ = (qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3))+
        (1+P (qvar K 1) (qvar K 2) (qvar K 3)) := by ring
    _ = _ := by rw [hh, zero_add]


-- @@ L37-41 verbatim
theorem relation_cusp : (qvar K 1)^2+(qvar K 2)^3 = qvar K 0*qvar K 3 := by
  have hz : qmap K (relCusp K) = 0 := quotient_pair_right (relH K) (relCusp K)
  have hh : (qvar K 1)^2+(qvar K 2)^3-qvar K 3*qvar K 0 = 0 := by
    simpa [relCusp, qvar] using hz
  simpa [mul_comm] using sub_eq_zero.mp hh


-- @@ L43-45 verbatim
theorem shift_s : (qvar K 1+(qvar K 3)^3)^2+(qvar K 2-(qvar K 3)^2)^3 = qvar K 3 := by
  rw [shift_universal, relation_cusp, relation_h]
  ring


-- @@ L47-55 verbatim
theorem bezout : Alpha (qvar K 1) (qvar K 3)*qvar K 0+
    Beta (qvar K 1) (qvar K 2) (qvar K 3)*qvar K 2 = 1 := by
  have he := bezout_certificate (qvar K 0) (qvar K 1) (qvar K 2) (qvar K 3)
  have hh : qvar K 0-1-P (qvar K 1) (qvar K 2) (qvar K 3) = 0 := by
    rw [relation_h]; ring
  have hc : (qvar K 1)^2+(qvar K 2)^3-qvar K 3*qvar K 0 = 0 := by
    rw [relation_cusp]; ring
  rw [hh, hc, mul_zero, mul_zero, sub_zero] at he
  exact sub_eq_zero.mp he


-- @@ L57-57 verbatim
def planeS : MvPolynomial (Fin 2) K := X 0^2+X 1^3

-- @@ L58-58 verbatim
def planeX : MvPolynomial (Fin 2) K := X 0-(planeS K)^3

-- @@ L59-59 verbatim
def planeY : MvPolynomial (Fin 2) K := X 1+(planeS K)^2

-- @@ L60-60 verbatim
def planeH : MvPolynomial (Fin 2) K := 1+P (planeX K) (planeY K) (planeS K)

-- @@ L61-62 verbatim
def values : Fin 4 → MvPolynomial (Fin 2) K :=
  ![planeH K, planeX K, planeY K, planeS K]


-- @@ L64-73 verbatim
theorem plane_cusp : (planeX K)^2+(planeY K)^3 = planeH K*planeS K := by
  have he := shift_universal (planeX K) (planeY K) (planeS K)
  have hx : planeX K+(planeS K)^3 = X 0 := by unfold planeX; ring
  have hy : planeY K-(planeS K)^2 = X 1 := by unfold planeY; ring
  rw [hx, hy] at he
  change planeS K = (planeX K)^2+(planeY K)^3-planeS K*P (planeX K) (planeY K) (planeS K) at he
  calc
    _ = (planeS K)+planeS K*P (planeX K) (planeY K) (planeS K) := by
      exact (eq_sub_iff_add_eq.mp he).symm
    _ = _ := by unfold planeH; ring


-- @@ L75-78 verbatim
def forward : Q K →ₐ[K] MvPolynomial (Fin 2) K :=
  lift_pair (relH K) (relCusp K) (aeval (values K))
    (by simp [relH, values, planeH])
    (by simp [relCusp, values, plane_cusp, mul_comm])


-- @@ L80-82 verbatim
@[simp] theorem forward_qvar (i : Fin 4) : forward K (qvar K i) = values K i := by
  change aeval (values K) (X i) = values K i
  exact aeval_X _ _


-- @@ L84-85 verbatim
def backward : MvPolynomial (Fin 2) K →ₐ[K] Q K :=
  aeval ![qvar K 1+(qvar K 3)^3, qvar K 2-(qvar K 3)^2]


-- @@ L87-88 verbatim
@[simp] theorem backward_planeS : backward K (planeS K) = qvar K 3 := by
  simpa [backward, planeS] using shift_s K


-- @@ L90-92 verbatim
@[simp] theorem backward_planeX : backward K (planeX K) = qvar K 1 := by
  simp only [planeX, map_sub, map_pow, backward_planeS]
  simp [backward]


-- @@ L94-96 verbatim
@[simp] theorem backward_planeY : backward K (planeY K) = qvar K 2 := by
  simp only [planeY, map_add, map_pow, backward_planeS]
  simp [backward]


-- @@ L98-99 verbatim
@[simp] theorem backward_planeH : backward K (planeH K) = qvar K 0 := by
  simpa [planeH] using (relation_h K).symm


-- @@ L101-104 verbatim
theorem forward_backward : (forward K).comp (backward K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [backward, values, planeX, planeY]


-- @@ L106-112 verbatim
theorem backward_forward : (backward K).comp (forward K) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change backward K (forward K (qvar K i)) = qvar K i
  rw [forward_qvar]
  fin_cases i <;> simp [values]


-- @@ L114-115 verbatim
def equivalence : Q K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  AlgEquiv.ofAlgHom (forward K) (backward K) (forward_backward K) (backward_forward K)


-- @@ L117-117 verbatim
end AbhyankarSathaye.Plane


-- @@ L119-119 verbatim
end


-- @@ L121-121 verbatim
end OAI
