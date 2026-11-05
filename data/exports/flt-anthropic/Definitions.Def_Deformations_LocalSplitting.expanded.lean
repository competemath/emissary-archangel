import Mathlib


-- @@ L3-3 verbatim
set_option autoImplicit false


-- @@ L5-5 verbatim
open Module


-- @@ L7-7 verbatim
namespace TaylorWiles


-- @@ L9-9 verbatim
variable {A : Type*} [CommRing A]


-- @@ L11-11 verbatim
local notation "M₂ " A => Matrix (Fin 2) (Fin 2) A


-- @@ L13-21 verbatim
structure IsEigenIdempotent (M : M₂ A) (a b : A) (e : M₂ A) : Prop where

  idem : e * e = e

  trace_eq_one : e.trace = 1

  mul_left : M * e = a • e

  mul_right : M * ((1 : M₂ A) - e) = b • ((1 : M₂ A) - e)


-- @@ L23-23 verbatim
def eigenIdempotent (M : M₂ A) (b v : A) : M₂ A := v • (M - b • (1 : M₂ A))


-- @@ L25-26 verbatim
theorem eigenIdempotent_def (M : M₂ A) (b v : A) :
    eigenIdempotent M b v = v • (M - b • (1 : M₂ A)) := rfl


-- @@ L28-28 verbatim
end TaylorWiles
