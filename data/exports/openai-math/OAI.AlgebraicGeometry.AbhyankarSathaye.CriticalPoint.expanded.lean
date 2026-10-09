import OAI.AlgebraicGeometry.AbhyankarSathaye.Identities
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.NormNum


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-13 verbatim
/-!
# An explicit critical point away from the zero fiber

At `(h,u,v,w) = (2,0,-1/2,1/2)`, the value of `F` is `-1` and every
partial derivative vanishes. Differentiating the ambient polynomial identity
proves the latter without expanding `F`.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
namespace AbhyankarSathaye

-- @@ L17-17 verbatim
open MvPolynomial


-- @@ L19-20 verbatim
def criticalPoint (i : Fin 4) : ℂ :=
  if i = 0 then 2 else if i = 1 then 0 else if i = 2 then -1/2 else 1/2


-- @@ L22-22 verbatim
@[simp] theorem criticalPoint_h : criticalPoint 0 = 2 := rfl

-- @@ L23-23 verbatim
@[simp] theorem criticalPoint_u : criticalPoint 1 = 0 := rfl

-- @@ L24-24 verbatim
@[simp] theorem criticalPoint_v : criticalPoint 2 = -1/2 := rfl

-- @@ L25-25 verbatim
@[simp] theorem criticalPoint_w : criticalPoint 3 = 1/2 := rfl


-- @@ L27-28 verbatim
theorem eval_x : eval criticalPoint x = -1 := by
  norm_num [x, u, h, v]


-- @@ L30-31 verbatim
theorem eval_y : eval criticalPoint y = 1 := by
  norm_num [y, u, h, w]


-- @@ L33-34 verbatim
theorem eval_s : eval criticalPoint s = 1 := by
  norm_num [s, S, u, h, v, w]


-- @@ L36-37 verbatim
theorem eval_p : eval criticalPoint p = 2 := by
  norm_num [p, P, eval_x, eval_y, eval_s]


-- @@ L39-40 verbatim
theorem eval_F : eval criticalPoint F = -1 := by
  norm_num [F, h, eval_p]


-- @@ L42-43 verbatim
theorem eval_shiftX : eval criticalPoint shiftX = 0 := by
  norm_num [shiftX, eval_x, eval_s]


-- @@ L45-46 verbatim
theorem eval_shiftY : eval criticalPoint shiftY = 0 := by
  norm_num [shiftY, eval_y, eval_s]


-- @@ L48-55 verbatim
theorem critical_of_ambient_identity {σ B : Type*} [CommRing B]
    (A D E f : MvPolynomial σ B) (point : σ → B)
    (hid : A^2 + D^3 = E*(1+f))
    (hA : eval point A = 0) (hD : eval point D = 0)
    (hE : eval point E = 1) (hf : eval point f = -1) (i : σ) :
    eval point (pderiv i f) = 0 := by
  have hd := congrArg (fun z => eval point (pderiv i z)) hid
  simpa [pderiv_pow, pderiv_mul, hA, hD, hE, hf] using hd.symm


-- @@ L57-59 verbatim
theorem critical_derivatives (i : Fin 4) : eval criticalPoint (pderiv i F) = 0 :=
  critical_of_ambient_identity shiftX shiftY s F criticalPoint ambient
    eval_shiftX eval_shiftY eval_s eval_F i


-- @@ L61-61 verbatim
end AbhyankarSathaye


-- @@ L63-63 verbatim
end


-- @@ L65-65 verbatim
end OAI
