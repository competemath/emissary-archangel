/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.RelativeProjectiveFactorization


-- @@ L10-15 verbatim
/-!
# Chosen data in a relative projective factorization

This file gives stable names to the dimension and closed embedding contained in a relative
projective factorization.
-/


-- @@ L17-17 verbatim
open CategoryTheory


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
universe u


-- @@ L23-23 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L25-25 verbatim
namespace AlgebraicGeometry.IsRelativeProjectiveFactorization


-- @@ L27-27 verbatim
variable {R : Type u} [CommRing R] {X S : Scheme.{u}}

-- @@ L28-28 verbatim
variable {s : S ⟶ Spec (.of R)} {f : X ⟶ S}


-- @@ L30-32 verbatim
/-- A chosen relative projective dimension. -/
def chosenDimension (h : IsRelativeProjectiveFactorization s f) : ℕ :=
  h.choose


-- @@ L34-37 verbatim
/-- The chosen closed embedding into relative projective space. -/
def chosenEmbedding (h : IsRelativeProjectiveFactorization s f) :
    X ⟶ relativeProjectiveScheme s h.chosenDimension :=
  h.choose_spec.choose


-- @@ L39-43 verbatim
/-- The chosen embedding is a closed immersion. -/
lemma chosenEmbedding_isClosedImmersion
    (h : IsRelativeProjectiveFactorization s f) :
    IsClosedImmersion h.chosenEmbedding :=
  h.choose_spec.choose_spec.1


-- @@ L45-45 verbatim
attribute [local instance] chosenEmbedding_isClosedImmersion


-- @@ L47-52 verbatim
/-- Projection of the chosen embedding to the base recovers the original morphism. -/
@[reassoc]
lemma chosenEmbedding_relativeProjectiveToBase
    (h : IsRelativeProjectiveFactorization s f) :
    h.chosenEmbedding ≫ relativeProjectiveToBase s h.chosenDimension = f :=
  h.choose_spec.choose_spec.2


-- @@ L54-57 verbatim
/-- The absolute projective-space map underlying the chosen relative factorization. -/
def chosenProjectiveMap (h : IsRelativeProjectiveFactorization s f) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (h.chosenDimension + 1)) R) :=
  h.chosenEmbedding ≫ relativeProjectiveToProjective s h.chosenDimension


-- @@ L59-69 verbatim
/-- The chosen projective map is compatible with the structural map to the affine base. -/
@[reassoc]
lemma chosenProjectiveMap_homogeneousProjπ
    (h : IsRelativeProjectiveFactorization s f) :
    h.chosenProjectiveMap ≫
        MvPolynomial.homogeneousProjπ
          (R := R) (σ := Fin (h.chosenDimension + 1)) =
      f ≫ s := by
  rw [chosenProjectiveMap, Category.assoc,
    ← relativeProjective_projection_condition]
  exact h.chosenEmbedding_relativeProjectiveToBase_assoc s


-- @@ L71-71 verbatim
end AlgebraicGeometry.IsRelativeProjectiveFactorization
