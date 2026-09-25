module

public import Mathlib.Algebra.Polynomial.Bivariate


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
local notation3:max R "[X][Y]" => Polynomial (Polynomial R)

-- @@ L8-8 verbatim
local notation3:max "Y" => Polynomial.C (Polynomial.X)


-- @@ L10-10 verbatim
namespace Polynomial

-- @@ L11-13 verbatim
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

-- TODO: bundle this

-- @@ L14-20 expanded
noncomputable def aevalAEval (x y : A) : Polynomial (Polynomial R) →ₐ[R] A
    where
  toFun p := eval y (eval₂ (mapRingHom (algebraMap R A)) (C x) p)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' r := by simp


-- @@ L22-22 verbatim
@[simp] lemma aevalAEval_X (x y : A) : aevalAEval (R := R) x y X = x := by simp [aevalAEval]

-- @@ L23-23 expanded
@[simp]
lemma aevalAEval_Y (x y : A) : aevalAEval (R := R) x y (Polynomial.C (Polynomial.X)) = y := by
  simp [aevalAEval]


-- @@ L25-25 verbatim
end Polynomial
