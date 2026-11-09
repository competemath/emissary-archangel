/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Ramification
import Mathlib.FieldTheory.Finite.Basic


-- @@ L9-21 verbatim
/-!
# Kernel-Degree Theorem and Frobenius Fixed Points

For elliptic curves over finite fields:
- Rational points = Frobenius fixed points = ker(1-π)
- For separable isogenies: #ker(φ) = deg(φ)

The first fact is pure group theory. The second requires ramification theory.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], Proposition III.4.10, V.1.1
-/


-- @@ L23-23 verbatim
open WeierstrassCurve FiniteField


-- @@ L25-25 verbatim
namespace HasseWeil


-- @@ L27-35 verbatim
/-! ### Frobenius fixed points

Over `K = F_q`: the Frobenius `π : x ↦ x^q` acts as the identity on K-rational
coordinates (since `a^q = a` for `a ∈ F_q`). So every K-rational point is fixed
by π, and (1-π) kills exactly the K-rational points.

Formally: `Point.map (frobeniusAlgHom K K) = id` on `E(K)` because
`frobeniusAlgHom K K = AlgHom.id K K` (the Frobenius is the identity on `F_q`).
-/


-- @@ L37-37 verbatim
section FrobeniusId


-- @@ L39-39 verbatim
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]


-- @@ L41-47 verbatim
omit [DecidableEq K] in
/-- The Frobenius algebra homomorphism is the identity on `F_q` itself.
    This is because `a^q = a` for all `a ∈ F_q` (the defining property of `F_q`). -/
theorem frobeniusAlgHom_eq_id :
    frobeniusAlgHom K K = AlgHom.id K K := by
  apply AlgHom.ext; intro a
  simp [pow_card]


-- @@ L49-49 verbatim
end FrobeniusId


-- @@ L51-56 verbatim
/-! ### Group-theoretic fiber size

For any group homomorphism φ : G → H between abelian groups, all fibers over
points in the image have the same cardinality as ker(φ). This follows from
the bijection `φ⁻¹(Q) ≅ ker(φ)` via translation by a preimage of Q.
-/


-- @@ L58-58 verbatim
section FiberSize


-- @@ L60-60 verbatim
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

-- @@ L61-61 verbatim
variable [Fintype G] [DecidableEq G] [DecidableEq H]

-- @@ L62-62 verbatim
variable (φ : G →+ H)


-- @@ L64-73 verbatim
/-- The fiber of a group homomorphism over any point in the image is in bijection
    with the kernel. -/
noncomputable def fiberEquivKer (Q : H) (P₀ : G) (hP₀ : φ P₀ = Q) :
    {P : G // φ P = Q} ≃ φ.ker := {
  toFun := fun ⟨P, hP⟩ ↦ ⟨P - P₀, by
    simp [AddMonoidHom.mem_ker, map_sub, hP, hP₀]⟩
  invFun := fun ⟨K, hK⟩ ↦ ⟨K + P₀, by
    simp [AddMonoidHom.mem_ker.mp hK, hP₀]⟩
  left_inv := fun ⟨P, _⟩ ↦ by simp
  right_inv := fun ⟨K, _⟩ ↦ by simp }


-- @@ L75-81 verbatim
omit [DecidableEq G] in
/-- All fibers of a group homomorphism over points in the image have the same
    cardinality as the kernel. -/
theorem card_fiber_eq_card_ker (Q : H) (hQ : Q ∈ Set.range φ) :
    Fintype.card {P : G // φ P = Q} = Fintype.card φ.ker := by
  obtain ⟨P₀, hP₀⟩ := hQ
  exact Fintype.card_congr (fiberEquivKer φ Q P₀ hP₀)


-- @@ L83-83 verbatim
end FiberSize


-- @@ L85-85 verbatim
end HasseWeil
