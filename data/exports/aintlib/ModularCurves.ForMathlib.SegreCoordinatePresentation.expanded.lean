/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from the algebraic part of Clawristotle's
`CoherentCohomologyFinite.SegreCoordinatePresentation`.
-/
import ModularCurves.ForMathlib.SegreDiagonalSurjectivity
import Mathlib.Algebra.MvPolynomial.Equiv


-- @@ L12-17 verbatim
/-!
# The coordinate presentation of the Segre image

The standard coordinates of the target projective space are reindexed by pairs.
The homogeneous coordinate ring of the image is the range of the resulting map.
-/


-- @@ L19-19 verbatim
open scoped TensorProduct


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
universe u


-- @@ L25-25 verbatim
namespace MvPolynomial


-- @@ L27-29 verbatim
/-- The dimension of the target of `ℙ^m × ℙ^n ↪ ℙ^(mn+m+n)`. -/
def segreDimension (m n : ℕ) : ℕ :=
  m * n + m + n


-- @@ L31-34 verbatim
lemma segreDimension_succ (m n : ℕ) :
    segreDimension m n + 1 = (m + 1) * (n + 1) := by
  simp only [segreDimension]
  ring


-- @@ L36-39 verbatim
/-- Reindex the target coordinates by pairs of coordinates of the two factors. -/
def segreIndexEquiv (m n : ℕ) :
    Fin (segreDimension m n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
  (finCongr (segreDimension_succ m n)).trans finProdFinEquiv.symm


-- @@ L41-47 verbatim
/-- The Segre coordinate map with standard target coordinates. -/
def segreStandardCoordinateHom
    (R : Type u) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin (segreDimension m n + 1)) R →ₐ[R]
      MvPolynomial (Fin (m + 1)) R ⊗[R] MvPolynomial (Fin (n + 1)) R :=
  (segreCoordinateHom R m n).comp
    (MvPolynomial.renameEquiv R (segreIndexEquiv m n)).toAlgHom


-- @@ L49-57 verbatim
@[simp]
lemma segreStandardCoordinateHom_X
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (segreDimension m n + 1)) :
    segreStandardCoordinateHom R m n (X i) =
      X (segreIndexEquiv m n i).1 ⊗ₜ[R] X (segreIndexEquiv m n i).2 := by
  change segreCoordinateHom R m n
    (rename (segreIndexEquiv m n) (X i)) = _
  rw [rename_X, segreCoordinateHom_X]


-- @@ L59-62 verbatim
/-- The homogeneous coordinate ring of the Segre image. -/
abbrev SegreCoordinateRing
    (R : Type u) [CommRing R] (m n : ℕ) :=
  (segreStandardCoordinateHom R m n).range


-- @@ L64-69 verbatim
/-- The coordinate map with codomain restricted to its image. -/
abbrev segreRangeCoordinateHom
    (R : Type u) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin (segreDimension m n + 1)) R →ₐ[R]
      SegreCoordinateRing R m n :=
  (segreStandardCoordinateHom R m n).rangeRestrict


-- @@ L71-74 verbatim
lemma segreRangeCoordinateHom_surjective
    (R : Type u) [CommRing R] (m n : ℕ) :
    Function.Surjective (segreRangeCoordinateHom R m n) :=
  AlgHom.rangeRestrict_surjective _


-- @@ L76-83 verbatim
@[simp]
lemma segreRangeCoordinateHom_val
    (R : Type u) [CommRing R] (m n : ℕ)
    (p : MvPolynomial (Fin (segreDimension m n + 1)) R) :
    ((segreRangeCoordinateHom R m n p : SegreCoordinateRing R m n) :
      MvPolynomial (Fin (m + 1)) R ⊗[R] MvPolynomial (Fin (n + 1)) R) =
        segreStandardCoordinateHom R m n p :=
  rfl


-- @@ L85-85 verbatim
end MvPolynomial
