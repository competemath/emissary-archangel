import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Nullstellensatz


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-12 verbatim
/-!
# Polynomial maps induced by coordinate-ring maps

The maps in this file carry actual coordinate polynomials and satisfy polynomial
composition identities. In particular, the geometric interpretation of an algebra
equivalence below is not merely a set-theoretic bijection of complex points.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace StableCoordinate

-- @@ L17-17 verbatim
namespace AmbientMaps


-- @@ L19-19 verbatim
open MvPolynomial


-- @@ L21-21 verbatim
variable {k : Type*} [CommSemiring k]

-- @@ L22-22 verbatim
variable {σ τ υ : Type*}


-- @@ L24-27 verbatim
/-- The point map contravariantly induced by a homomorphism of polynomial algebras. -/
def pointMap (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (x : σ → k) : τ → k :=
  fun i => aeval x (φ (X i))


-- @@ L29-36 verbatim
/-- Pulling back a polynomial and evaluating agrees with evaluating it on the point map. -/
theorem aeval_pointMap (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (x : σ → k) (p : MvPolynomial τ k) :
    aeval (pointMap φ x) p = aeval x (φ p) := by
  have h : aeval (pointMap φ x) = (aeval x).comp φ := by
    ext i
    simp [pointMap]
  exact AlgHom.congr_fun h p


-- @@ L38-42 verbatim
@[simp]
theorem pointMap_id (x : σ → k) :
    pointMap (AlgHom.id k (MvPolynomial σ k)) x = x := by
  funext i
  simp [pointMap]


-- @@ L44-49 verbatim
/-- Composition is reversed, as it must be for maps of coordinate rings. -/
theorem pointMap_comp (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (ψ : MvPolynomial υ k →ₐ[k] MvPolynomial τ k) (x : σ → k) :
    pointMap (φ.comp ψ) x = pointMap ψ (pointMap φ x) := by
  funext i
  exact (aeval_pointMap φ x (ψ (X i))).symm


-- @@ L51-57 verbatim
/-- A polynomial isomorphism, with inverse identities in the polynomial rings,
not just identities of functions on the base field. -/
structure PolynomialEquiv (k : Type*) [CommSemiring k] (σ τ : Type*) where
  forward : τ → MvPolynomial σ k
  inverse : σ → MvPolynomial τ k
  forward_inverse : ∀ i, aeval forward (inverse i) = X i
  inverse_forward : ∀ i, aeval inverse (forward i) = X i


-- @@ L59-59 verbatim
namespace PolynomialEquiv


-- @@ L61-73 verbatim
/-- An algebra isomorphism supplies polynomial coordinates for both directions. -/
def ofAlgEquiv (e : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k) :
    PolynomialEquiv k σ τ where
  forward i := e (X i)
  inverse i := e.symm (X i)
  forward_inverse i := by
    change aeval (e.toAlgHom ∘ X) (e.symm (X i)) = X i
    rw [← aeval_unique e.toAlgHom]
    exact e.apply_symm_apply (X i)
  inverse_forward i := by
    change aeval (e.symm.toAlgHom ∘ X) (e (X i)) = X i
    rw [← aeval_unique e.symm.toAlgHom]
    exact e.symm_apply_apply (X i)


-- @@ L75-77 verbatim
/-- The forward polynomial map. -/
def toPointMap (e : PolynomialEquiv k σ τ) (x : σ → k) : τ → k :=
  fun i => aeval x (e.forward i)


-- @@ L79-81 verbatim
/-- The inverse polynomial map. -/
def invPointMap (e : PolynomialEquiv k σ τ) (y : τ → k) : σ → k :=
  fun i => aeval y (e.inverse i)


-- @@ L83-88 verbatim
@[simp]
theorem invPointMap_toPointMap (e : PolynomialEquiv k σ τ) (x : σ → k) :
    e.invPointMap (e.toPointMap x) = x := by
  funext i
  change aeval (fun j => aeval x (e.forward j)) (e.inverse i) = x i
  rw [← comp_aeval_apply e.forward (aeval x), e.forward_inverse, aeval_X]


-- @@ L90-95 verbatim
@[simp]
theorem toPointMap_invPointMap (e : PolynomialEquiv k σ τ) (y : τ → k) :
    e.toPointMap (e.invPointMap y) = y := by
  funext i
  change aeval (fun j => aeval y (e.inverse j)) (e.forward i) = y i
  rw [← comp_aeval_apply e.inverse (aeval y), e.inverse_forward, aeval_X]


-- @@ L97-102 verbatim
/-- The underlying point equivalence, retaining its polynomial witnesses in `e`. -/
def toEquiv (e : PolynomialEquiv k σ τ) : (σ → k) ≃ (τ → k) where
  toFun := e.toPointMap
  invFun := e.invPointMap
  left_inv := e.invPointMap_toPointMap
  right_inv := e.toPointMap_invPointMap


-- @@ L104-107 verbatim
@[simp]
theorem ofAlgEquiv_toPointMap
    (e : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k) (x : σ → k) :
    (ofAlgEquiv e).toPointMap x = pointMap e.toAlgHom x := rfl


-- @@ L109-112 verbatim
@[simp]
theorem ofAlgEquiv_invPointMap
    (e : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k) (y : τ → k) :
    (ofAlgEquiv e).invPointMap y = pointMap e.symm.toAlgHom y := rfl


-- @@ L114-114 verbatim
end PolynomialEquiv


-- @@ L116-124 verbatim
/-- An ambient algebra equivalence transports every level set by an explicitly
polynomial point equivalence. The inverse direction is the one matching pullback. -/
theorem pointMap_levelSet (e : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (p : MvPolynomial τ k) (c : k) :
    pointMap e.toAlgHom ⁻¹' {y | aeval y p = c} =
      {x | aeval x (e p) = c} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, aeval_pointMap]
  rfl


-- @@ L126-126 verbatim
end AmbientMaps

-- @@ L127-127 verbatim
end StableCoordinate


-- @@ L129-129 verbatim
end


-- @@ L131-131 verbatim
end OAI
