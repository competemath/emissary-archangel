/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FiniteProperClosure
import ModularCurves.ForMathlib.FiniteProjectiveFactorization


-- @@ L11-16 verbatim
/-!
# Projectivity of finite proper closures

The scheme-theoretic closure inside a nonempty finite product of projectively factored schemes
still has a projective factorization over the affine base.
-/


-- @@ L18-18 verbatim
open CategoryTheory


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
namespace AlgebraicGeometry.Scheme.FiniteProperClosure


-- @@ L26-26 verbatim
variable {R : Type u} [CommRing R] {T : Scheme.{u}}

-- @@ L27-27 verbatim
variable {ι : Type u} [Finite ι] [Nonempty ι]

-- @@ L28-28 verbatim
variable {Z : ι → Scheme.{u}} (p : ∀ i, Z i ⟶ Spec (.of R))

-- @@ L29-29 verbatim
variable (q : T ⟶ Spec (.of R)) (f : ∀ i, T ⟶ Z i)

-- @@ L30-30 verbatim
variable (hf : ∀ i, f i ≫ p i = q)


-- @@ L32-37 verbatim
/-- A scheme-theoretic closure in a nonempty finite projective product is projective. -/
lemma π_isProjectiveFactorization
    (hp : ∀ i, AlgebraicGeometry.IsProjectiveFactorization (p i)) :
    AlgebraicGeometry.IsProjectiveFactorization (π p q f hf) :=
  (FiniteProperProduct.π_isProjectiveFactorization p hp).comp_isClosedImmersion
    (inclusion p q f hf) (by infer_instance)


-- @@ L39-39 verbatim
end AlgebraicGeometry.Scheme.FiniteProperClosure
