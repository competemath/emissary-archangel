/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.HomogeneousProjProper
import ModularCurves.ForMathlib.HomogenizedProjStandardEmbedding


-- @@ L11-16 verbatim
/-!
# Projective factorizations over affine schemes

A morphism to an affine scheme has a projective factorization if it factors through a closed
immersion into a finite-dimensional polynomial projective space over the same base.
-/


-- @@ L18-18 verbatim
open CategoryTheory


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L26-26 verbatim
namespace AlgebraicGeometry


-- @@ L28-33 verbatim
/-- A factorization through a closed subscheme of finite-dimensional projective space. -/
def IsProjectiveFactorization {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (d : ℕ) (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R)),
    IsClosedImmersion i ∧
      i ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1)) = f


-- @@ L35-35 verbatim
namespace IsProjectiveFactorization


-- @@ L37-37 verbatim
variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

-- @@ L38-38 verbatim
variable {f : X ⟶ Spec (.of R)}


-- @@ L40-48 verbatim
/-- A morphism admitting a projective factorization is proper. -/
lemma isProper (h : IsProjectiveFactorization f) : IsProper f := by
  obtain ⟨d, i, hi, hif⟩ := h
  letI : IsClosedImmersion i := hi
  letI : IsProper
      (MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (d + 1))) :=
    MvPolynomial.homogeneousProjπ_isProper
  rw [← hif]
  infer_instance


-- @@ L50-58 verbatim
/-- Precomposition with a closed immersion preserves projective factorizations. -/
lemma comp_isClosedImmersion (h : IsProjectiveFactorization f)
    (i : Y ⟶ X) (hi : IsClosedImmersion i) :
    IsProjectiveFactorization (i ≫ f) := by
  obtain ⟨d, j, hj, hjf⟩ := h
  letI : IsClosedImmersion i := hi
  letI : IsClosedImmersion j := hj
  refine ⟨d, i ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hjf]


-- @@ L60-60 verbatim
end IsProjectiveFactorization


-- @@ L62-62 verbatim
end AlgebraicGeometry


-- @@ L64-64 verbatim
namespace MvPolynomial


-- @@ L66-66 verbatim
open AlgebraicGeometry


-- @@ L68-68 verbatim
variable {R : Type u} [CommRing R] {κ : Type} {n : ℕ}


-- @@ L70-77 verbatim
/-- Every homogenized projective closure has a projective factorization over its coefficient
spectrum. -/
lemma homogenizedProjπ_isProjectiveFactorization
    (g : κ → MvPolynomial (Fin n) R) (d : κ → ℕ) :
    IsProjectiveFactorization (homogenizedProjπ g d) :=
  ⟨n, homogenizedProjStandardι g d,
    homogenizedProjStandardι_isClosedImmersion g d,
    homogenizedProjStandardι_comp_homogeneousProjπ g d⟩


-- @@ L79-79 verbatim
end MvPolynomial
