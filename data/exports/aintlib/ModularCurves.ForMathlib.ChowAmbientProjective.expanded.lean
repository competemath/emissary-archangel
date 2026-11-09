/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.AffineProjectiveClosureFactorization
import ModularCurves.ForMathlib.FiniteProperClosureProjective
import ModularCurves.ForMathlib.NoetherianChowCover


-- @@ L12-17 verbatim
/-!
# Projectivity of the Chow ambient scheme

The finite scheme-theoretic closure assembled from a nonempty finite affine cover has an explicit
projective factorization over the affine base.
-/


-- @@ L19-19 verbatim
open CategoryTheory


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover


-- @@ L27-27 verbatim
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

-- @@ L28-28 verbatim
variable (xπ : X ⟶ Spec (.of R)) {ι : Type u} [Finite ι] [Nonempty ι]

-- @@ L29-29 verbatim
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

-- @@ L30-30 verbatim
variable [IsNoetherian X] [LocallyOfFinitePresentation xπ]


-- @@ L32-37 verbatim
/-- The ambient finite closure in the Chow construction is projective over the affine base. -/
lemma chowAmbientπ_isProjectiveFactorization :
    AlgebraicGeometry.IsProjectiveFactorization (chowAmbientπ xπ U hU) := by
  unfold chowAmbientπ
  apply FiniteProperClosure.π_isProjectiveFactorization
  exact projectiveπ_isProjectiveFactorization xπ U hU


-- @@ L39-39 verbatim
end AlgebraicGeometry.Scheme.FiniteAffineImageCover
