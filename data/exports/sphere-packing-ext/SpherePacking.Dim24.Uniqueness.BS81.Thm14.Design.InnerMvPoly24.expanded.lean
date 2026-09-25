module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs


-- @@ L4-13 verbatim
/-!
# Inner-product monomials as homogeneous polynomials

We encode `x ↦ ⟪u,x⟫` as a degree-1 multivariate polynomial, and hence encode products of powers
`(⟪u,x⟫)^i * (⟪v,x⟫)^j` as homogeneous polynomials of degree `i+j`.

This is shared by:
- the derivation of BS81 equation (11) from moment identities, and
- the "44 common neighbors" computation (BS81 Lemma 18(ii)).
-/


-- @@ L15-15 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open scoped BigOperators RealInnerProductSpace


-- @@ L21-21 verbatim
open Finset MvPolynomial


-- @@ L23-23 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L25-27 verbatim
/-- The `MvPolynomial` representing the linear form `x ↦ ⟪u,x⟫` on `ℝ²⁴`. -/
@[expose] public def innerMvPoly24 (u : ℝ²⁴) : MvPolynomial (Fin 24) ℝ :=
  (Finset.univ : Finset (Fin 24)).sum fun i => MvPolynomial.C (u i) * MvPolynomial.X i


-- @@ L29-33 verbatim
lemma innerMvPoly24_isHomogeneous (u : ℝ²⁴) : (innerMvPoly24 u).IsHomogeneous 1 := by
  unfold innerMvPoly24
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  simpa using (MvPolynomial.isHomogeneous_C_mul_X (R := ℝ) (r := u i) (i := i))


-- @@ L35-38 verbatim
/-- Powers of `innerMvPoly24 u` are homogeneous: `(innerMvPoly24 u)^m` has degree `m`. -/
public lemma innerMvPoly24_pow_isHomogeneous (u : ℝ²⁴) (m : ℕ) :
    ((innerMvPoly24 u) ^ m).IsHomogeneous m := by
  simpa [Nat.one_mul] using (innerMvPoly24_isHomogeneous (u := u)).pow m


-- @@ L40-43 verbatim
/-- Evaluating `innerMvPoly24 u` at `x` gives the inner product `⟪u,x⟫`. -/
public lemma mvPolyEval24_innerMvPoly24 (u x : ℝ²⁴) :
    mvPolyEval24 (innerMvPoly24 u) x = (⟪u, x⟫ : ℝ) := by
  simp [mvPolyEval24, innerMvPoly24, PiLp.inner_apply, mul_comm]


-- @@ L45-45 verbatim
attribute [grind =] mvPolyEval24_innerMvPoly24


-- @@ L47-53 verbatim
/-- Evaluating `(innerMvPoly24 u)^m` at `x` gives `(⟪u,x⟫)^m`. -/
public lemma mvPolyEval24_innerMvPoly24_pow (u x : ℝ²⁴) (m : ℕ) :
    mvPolyEval24 ((innerMvPoly24 u) ^ m) x = (⟪u, x⟫ : ℝ) ^ m := by
  have h :
      (MvPolynomial.eval x.ofLp) (innerMvPoly24 u) = (⟪u, x⟫ : ℝ) := by
    simpa [mvPolyEval24] using (mvPolyEval24_innerMvPoly24 (u := u) (x := x))
  simp [mvPolyEval24, h]


-- @@ L55-65 verbatim
/-- Evaluate a product of powers of inner-product polynomials. -/
public lemma mvPolyEval24_innerMvPoly24_pow_mul_pow (u v x : ℝ²⁴) (i j : ℕ) :
    mvPolyEval24 (((innerMvPoly24 u) ^ i) * ((innerMvPoly24 v) ^ j)) x =
      (⟪u, x⟫ : ℝ) ^ i * (⟪v, x⟫ : ℝ) ^ j := by
  have hu :
      (MvPolynomial.eval x.ofLp) (innerMvPoly24 u) = (⟪u, x⟫ : ℝ) := by
    simpa [mvPolyEval24] using (mvPolyEval24_innerMvPoly24 (u := u) (x := x))
  have hv :
      (MvPolynomial.eval x.ofLp) (innerMvPoly24 v) = (⟪v, x⟫ : ℝ) := by
    simpa [mvPolyEval24] using (mvPolyEval24_innerMvPoly24 (u := v) (x := x))
  simp [mvPolyEval24, hu, hv]


-- @@ L67-72 verbatim
/-- Homogeneity of `((innerMvPoly24 u)^i) * ((innerMvPoly24 v)^j)`. -/
public lemma innerMvPoly24_pow_mul_pow_isHomogeneous (u v : ℝ²⁴) (i j : ℕ) :
    (((innerMvPoly24 u) ^ i) * ((innerMvPoly24 v) ^ j)).IsHomogeneous (i + j) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    (innerMvPoly24_pow_isHomogeneous (u := u) (m := i)).mul
      (innerMvPoly24_pow_isHomogeneous (u := v) (m := j))


-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm14
