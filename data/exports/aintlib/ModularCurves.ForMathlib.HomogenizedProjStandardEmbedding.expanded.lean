/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.HomogeneousProjReindex


-- @@ L10-15 verbatim
/-!
# Standard projective embeddings of homogenized closures

A homogenized presentation in `Fin n` affine variables is naturally a closed subscheme of
projective space with `Fin (n+1)` homogeneous coordinates.
-/


-- @@ L17-17 verbatim
namespace MvPolynomial


-- @@ L19-19 verbatim
open AlgebraicGeometry CategoryTheory


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
variable {R : Type u} [CommRing R] {κ : Type} {n : ℕ}


-- @@ L27-27 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L29-34 verbatim
/-- The homogenized projective closure embedded in standard polynomial projective space. -/
def homogenizedProjStandardι
    (g : κ → MvPolynomial (Fin n) R) (d : κ → ℕ) :
    homogenizedProj g d ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R) :=
  homogenizedProjι g d ≫
    (homogeneousProjReindexIso R (_root_.finSuccEquiv n).symm).hom


-- @@ L36-43 verbatim
/-- The standard projective embedding of a homogenized closure is a closed immersion. -/
lemma homogenizedProjStandardι_isClosedImmersion
    (g : κ → MvPolynomial (Fin n) R) (d : κ → ℕ) :
    IsClosedImmersion (homogenizedProjStandardι g d) := by
  haveI : IsClosedImmersion (homogenizedProjι g d) :=
    homogenizedProjι_isClosedImmersion g d
  unfold homogenizedProjStandardι
  infer_instance


-- @@ L45-55 verbatim
/-- The standard projective embedding of a homogenized closure lies over the coefficient
spectrum. -/
lemma homogenizedProjStandardι_comp_homogeneousProjπ
    (g : κ → MvPolynomial (Fin n) R) (d : κ → ℕ) :
    homogenizedProjStandardι g d ≫
        homogeneousProjπ (R := R) (σ := Fin (n + 1)) =
      homogenizedProjπ g d := by
  unfold homogenizedProjStandardι
  rw [Category.assoc,
    homogeneousProjReindexIso_hom_comp_homogeneousProjπ,
    homogenizedProjι_comp_homogeneousProjπ]


-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
end MvPolynomial
