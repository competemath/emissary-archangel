import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation


-- @@ L9-9 verbatim
abbrev P := MvPolynomial (Fin 5) ℂ


-- @@ L11-11 verbatim
def p : P := MvPolynomial.X 0

-- @@ L12-12 verbatim
def s : P := MvPolynomial.X 1

-- @@ L13-13 verbatim
def u : P := MvPolynomial.X 2

-- @@ L14-14 verbatim
def F : P := MvPolynomial.X 3

-- @@ L15-15 verbatim
def J : P := MvPolynomial.X 4

-- @@ L16-16 verbatim
def x : P := s ^ 2 + u ^ 3 + p ^ 2 * F

-- @@ L17-17 verbatim
def H : P := x ^ 2 * F - (1 + 2 * s * x) * J - p ^ 2 * J ^ 2 - p * u

-- @@ L18-18 verbatim
abbrev A := P ⧸ Ideal.span {H}


-- @@ L20-23 verbatim
def MainStatement : Prop :=
  Algebra.FiniteType ℂ A ∧ IsDomain A ∧ ringKrullDim A = 4 ∧
  Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) ∧
  ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ)


-- @@ L25-25 verbatim
end ComplexCancellation


-- @@ L27-27 verbatim
end


-- @@ L29-29 verbatim
end OAI
