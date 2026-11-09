/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FiniteAffineImageProjective
import ModularCurves.ForMathlib.ProjectiveFactorization


-- @@ L11-16 verbatim
/-!
# Projective factorizations of affine compactifications

The homogenized projective closures chosen by finite algebra presentations, and the wrappers
through which the Chow construction uses them, have the concrete projective factorization.
-/


-- @@ L18-18 verbatim
open CategoryTheory


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
namespace Algebra.Presentation


-- @@ L26-26 verbatim
variable {R S : Type u} {κ : Type} [CommRing R] [CommRing S] [Algebra R S]

-- @@ L27-27 verbatim
variable {n : ℕ}


-- @@ L29-34 verbatim
/-- A finite-variable presentation's projective closure has a projective factorization. -/
lemma projectiveClosureπ_isProjectiveFactorization
    (P : Presentation R S (Fin n) κ) :
    AlgebraicGeometry.IsProjectiveFactorization (projectiveClosureπ P) :=
  MvPolynomial.homogenizedProjπ_isProjectiveFactorization P.relation
    (fun j => (P.relation j).totalDegree)


-- @@ L36-36 verbatim
end Algebra.Presentation


-- @@ L38-38 verbatim
namespace AlgebraicGeometry.Scheme.AffineProjectiveClosure


-- @@ L40-40 verbatim
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

-- @@ L41-41 verbatim
variable (f : X ⟶ Spec (.of R)) [IsAffine X] [LocallyOfFinitePresentation f]


-- @@ L43-50 verbatim
/-- The chosen projective closure of an affine finitely presented morphism has a projective
factorization. -/
lemma π_isProjectiveFactorization :
    IsProjectiveFactorization (π f) := by
  letI := algebra f
  letI := finitePresentation f
  exact Algebra.Presentation.projectiveClosureπ_isProjectiveFactorization
    (presentation f)


-- @@ L52-52 verbatim
end AlgebraicGeometry.Scheme.AffineProjectiveClosure


-- @@ L54-54 verbatim
namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover


-- @@ L56-56 verbatim
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

-- @@ L57-57 verbatim
variable (xπ : X ⟶ Spec (.of R)) {ι : Type u} (U : ι → X.Opens)


-- @@ L59-67 verbatim
/-- Every projective compactification used by a finite affine image cover has a projective
factorization. -/
lemma projectiveπ_isProjectiveFactorization [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    IsProjectiveFactorization (projectiveπ xπ U hU i) := by
  letI : IsAffine (chart U i).toScheme := chart_isAffineOpen U hU i
  letI : LocallyOfFinitePresentation (chartπ xπ U i) :=
    chartπ_locallyOfFinitePresentation xπ U i
  exact AffineProjectiveClosure.π_isProjectiveFactorization (chartπ xπ U i)


-- @@ L69-69 verbatim
end AlgebraicGeometry.Scheme.FiniteAffineImageCover
