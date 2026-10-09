import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-14 verbatim
/-!
# Polynomial identities for the cusp and the explicit hypersurface

The polynomials `S` and `P` give the identity
`(x + s³)² + (y - s²)³ = s * (1 + F)`. The Bézout certificate is valid over
every commutative ring. In the ambient complex polynomial ring, the variables
are ordered as `h, u, v, w`.
-/


-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
namespace AbhyankarSathaye


-- @@ L19-20 verbatim
def S {B : Type*} [CommRing B] (h u v w : B) : B :=
  2*u^3*v + 3*u^4*w + h*(v^2 - 3*u^2*w^2) + h^2*w^3


-- @@ L22-23 verbatim
def P {B : Type*} [CommRing B] (x y s : B) : B :=
  -2*s^2*x + 3*s*y^2 - 3*s^3*y


-- @@ L25-26 verbatim
def Alpha {B : Type*} [CommRing B] (x s : B) : B :=
  1 + 2*s^2*x + 4*s^5


-- @@ L28-29 verbatim
def Beta {B : Type*} [CommRing B] (x y s : B) : B :=
  (3*s^3 - 3*s*y)*(1 + 2*s^2*x) - 4*s^4*y^2


-- @@ L31-34 verbatim
theorem cusp_universal {B : Type*} [CommRing B] (h u v w : B) :
    (u^3 + h*v)^2 + (-u^2 + h*w)^3 = h*S h u v w := by
  unfold S
  ring


-- @@ L36-39 verbatim
theorem shift_universal {B : Type*} [CommRing B] (x y s : B) :
    (x + s^3)^2 + (y - s^2)^3 = x^2 + y^3 - s*P x y s := by
  unfold P
  ring


-- @@ L41-45 verbatim
theorem bezout_certificate {B : Type*} [CommRing B] (h x y s : B) :
    Alpha x s*h + Beta x y s*y - 1 =
      (1 + 2*s^2*x)*(h - 1 - P x y s) - 4*s^4*(x^2 + y^3 - s*h) := by
  unfold Alpha Beta P
  ring


-- @@ L47-47 verbatim
abbrev R := MvPolynomial (Fin 4) ℂ


-- @@ L49-49 verbatim
def h : R := MvPolynomial.X 0

-- @@ L50-50 verbatim
def u : R := MvPolynomial.X 1

-- @@ L51-51 verbatim
def v : R := MvPolynomial.X 2

-- @@ L52-52 verbatim
def w : R := MvPolynomial.X 3

-- @@ L53-53 verbatim
def x : R := u^3 + h*v

-- @@ L54-54 verbatim
def y : R := -u^2 + h*w

-- @@ L55-55 verbatim
def s : R := S h u v w

-- @@ L56-56 verbatim
def p : R := P x y s

-- @@ L57-57 verbatim
def F : R := h - p - 1

-- @@ L58-58 verbatim
def shiftX : R := x + s^3

-- @@ L59-59 verbatim
def shiftY : R := y - s^2


-- @@ L61-61 verbatim
theorem cusp : x^2 + y^3 = h*s := cusp_universal h u v w


-- @@ L63-64 verbatim
theorem shift : shiftX^2 + shiftY^3 = x^2 + y^3 - s*p :=
  shift_universal x y s


-- @@ L66-69 verbatim
theorem ambient : shiftX^2 + shiftY^3 = s*(1 + F) := by
  rw [shift, cusp]
  unfold F
  ring


-- @@ L71-71 verbatim
end AbhyankarSathaye


-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end OAI
