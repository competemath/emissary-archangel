/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import LeanPool.Koethe.ShiftWitness.Band


-- @@ L11-17 verbatim
/-!
# The rational-function eigenvector of the backward shifts

Nonzero edge triples give nonzero degree-at-most-two polynomials. Their images
in `RatFunc k` are invertible. Reciprocal prefix products produce a genuine
(non-finitely-supported) eigenvector on the full function space.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace KoetheCounterexample

-- @@ L24-24 verbatim
namespace ShiftWitness


-- @@ L26-26 verbatim
universe u

-- @@ L27-27 verbatim
variable {k : Type u} [Field k]


-- @@ L29-32 verbatim
/-- A triple encoded as a polynomial of degree at most two. -/
def edgePolynomial (z : Triple k) : Polynomial k :=
  Polynomial.C (z 0) + Polynomial.X * Polynomial.C (z 1) +
    Polynomial.X ^ 2 * Polynomial.C (z 2)


-- @@ L34-45 verbatim
theorem edgePolynomial_ne_zero (z : Triple k) (hz : z ≠ 0) :
    edgePolynomial z ≠ 0 := by
  intro h
  apply hz
  funext i
  fin_cases i
  · have hc := congrArg (fun p : Polynomial k => p.coeff 0) h
    simpa [edgePolynomial] using hc
  · have hc := congrArg (fun p : Polynomial k => p.coeff 1) h
    simpa [edgePolynomial, Polynomial.coeff_mul_C] using hc
  · have hc := congrArg (fun p : Polynomial k => p.coeff 2) h
    simpa [edgePolynomial, Polynomial.coeff_mul_C] using hc


-- @@ L47-49 verbatim
/-- The polynomial edge weight embedded faithfully in the rational-function field. -/
def edge (z : Triple k) : RatFunc k :=
  algebraMap (Polynomial k) (RatFunc k) (edgePolynomial z)


-- @@ L51-56 verbatim
theorem edge_eq (z : Triple k) :
    edge z = algebraMap k (RatFunc k) (z 0) +
      RatFunc.X * algebraMap k (RatFunc k) (z 1) +
      RatFunc.X ^ 2 * algebraMap k (RatFunc k) (z 2) := by
  simp only [edge, edgePolynomial, map_add, map_mul, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_eq_C]


-- @@ L58-59 verbatim
theorem edge_ne_zero (z : Triple k) (hz : z ≠ 0) : edge z ≠ 0 :=
  RatFunc.algebraMap_ne_zero (edgePolynomial_ne_zero z hz)


-- @@ L61-63 verbatim
/-- Reciprocal prefix products, defined on the full sequence module. -/
def eigenvector (v : ℕ → Triple k) : Space (RatFunc k) :=
  fun n => (∏ i ∈ Finset.range n, edge (v i))⁻¹


-- @@ L65-66 verbatim
@[simp] theorem eigenvector_zero (v : ℕ → Triple k) : eigenvector v 0 = 1 := by
  simp [eigenvector]


-- @@ L68-71 verbatim
theorem eigenvector_ne_zero (v : ℕ → Triple k) : eigenvector v ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this


-- @@ L73-77 verbatim
theorem edge_mul_eigenvector_succ (v : ℕ → Triple k) (hv : ∀ n, v n ≠ 0) (n : ℕ) :
    edge (v n) * eigenvector v (n + 1) = eigenvector v n := by
  rw [eigenvector, Finset.prod_range_succ, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (edge_ne_zero (v n) (hv n)), one_mul]
  rfl


-- @@ L79-91 verbatim
/-- The combined shift with transcendental scalar coefficients fixes a nonzero
vector. This is not a scalar combination over the ground field `k`. -/
theorem combined_shift_eigenvector (v : ℕ → Triple k) (hv : ∀ n, v n ≠ 0) :
    (backShift v 0 + (RatFunc.X : RatFunc k) • backShift v 1 +
      (RatFunc.X : RatFunc k) ^ 2 • backShift v 2 : End (RatFunc k)) (eigenvector v) =
      eigenvector v := by
  ext n
  change algebraMap k (RatFunc k) (v n 0) * eigenvector v (n + 1) +
      RatFunc.X * (algebraMap k (RatFunc k) (v n 1) * eigenvector v (n + 1)) +
      RatFunc.X ^ 2 * (algebraMap k (RatFunc k) (v n 2) * eigenvector v (n + 1)) = _
  calc
    _ = edge (v n) * eigenvector v (n + 1) := by rw [edge_eq]; ring
    _ = eigenvector v n := edge_mul_eigenvector_succ v hv n


-- @@ L93-93 verbatim
end ShiftWitness

-- @@ L94-94 verbatim
end KoetheCounterexample


-- @@ L96-96 verbatim
end
