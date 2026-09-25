/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2


-- @@ L10-35 verbatim
/-!
# Relabelling linear equivalences

## i. Overview

This module provides linear equivalences obtained by relabelling the index type of a finite
function space `d → R` or of `EuclideanSpace 𝕜 d` along an index equivalence `e : d ≃ d₂`,
together with lemmas relating them to `Matrix.reindex`.

## ii. Key results

- `LinearEquiv.ofRelabel` : the `R`-linear equivalence `(d₂ → R) ≃ₗ[R] (d → R)` induced by an
  index equivalence `e : d ≃ d₂`.
- `LinearEquiv.euclideanOfRelabel` : the `EuclideanSpace` analogue of `ofRelabel`.
- `Matrix.reindex_toLin'` and `Matrix.reindex_toEuclideanLin` : reindexing a matrix conjugates
  its associated linear map by these relabelling equivalences.

## iii. Table of contents

- A. Relabelling linear equivalences
- B. Reindexing matrices and their linear maps

## iv. References

* None.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
variable {d d₁ d₂ d₃ R 𝕜 : Type*} [RCLike 𝕜]


-- @@ L41-45 verbatim
/-!

## A. Relabelling linear equivalences

-/


-- @@ L47-47 verbatim
namespace LinearEquiv


-- @@ L49-49 verbatim
variable {R : Type*} [Semiring R]


-- @@ L51-58 verbatim
variable (R) in
/-- The `R`-linear equivalence `(d₂ → R) ≃ₗ[R] (d → R)` that relabels the coordinates of a
function along an index equivalence `e : d ≃ d₂`. This is the linear-equivalence packaging of
`Equiv.piCongrLeft`. -/
@[simps]
def ofRelabel (e : d ≃ d₂) : (d₂ → R) ≃ₗ[R] (d → R) := by
  refine' { e.symm.piCongrLeft (fun _ ↦ R) with .. }
  <;> (intros; ext; simp [Equiv.piCongrLeft_apply])


-- @@ L60-60 verbatim
variable (e : d ≃ d₂)


-- @@ L62-69 verbatim
variable (𝕜) in
/-- The `𝕜`-linear equivalence `EuclideanSpace 𝕜 d₂ ≃ₗ[𝕜] EuclideanSpace 𝕜 d` that relabels the
coordinates of a vector along an index equivalence `e : d ≃ d₂`. This is the `EuclideanSpace`
analogue of `LinearEquiv.ofRelabel`, obtained by transporting it across the `WithLp`
identifications. -/
@[simps!]
def euclideanOfRelabel (e : d ≃ d₂) : EuclideanSpace 𝕜 d₂ ≃ₗ[𝕜] EuclideanSpace 𝕜 d :=
  (WithLp.linearEquiv 2 𝕜 _).trans ((ofRelabel _ e).trans (WithLp.linearEquiv 2 𝕜 _).symm)


-- @@ L71-73 verbatim
@[simp]
theorem ofRelabel_refl : ofRelabel R (.refl d) = LinearEquiv.refl R (d → R) := by
  rfl


-- @@ L75-78 verbatim
@[simp]
theorem euclideanOfRelabel_refl : euclideanOfRelabel 𝕜 (.refl d) =
    LinearEquiv.refl 𝕜 (EuclideanSpace 𝕜 d) := by
  rfl


-- @@ L80-80 verbatim
end LinearEquiv


-- @@ L82-86 verbatim
/-!

## B. Reindexing matrices and their linear maps

-/


-- @@ L88-88 verbatim
namespace Matrix


-- @@ L90-90 verbatim
variable {R : Type*} [CommSemiring R]

-- @@ L91-91 verbatim
variable [Fintype d] [DecidableEq d]

-- @@ L92-92 verbatim
variable [Fintype d₂] [DecidableEq d₂]


-- @@ L94-98 verbatim
theorem reindex_toLin' (e : d₁ ≃ d₃) (f : d₂ ≃ d) (M : Matrix d₁ d₂ R) :
    (M.reindex e f).toLin' = (LinearEquiv.ofRelabel R e.symm) ∘ₗ
      M.toLin' ∘ₗ (LinearEquiv.ofRelabel R f) := by
  ext
  simp [mulVec, dotProduct, Equiv.piCongrLeft_apply]


-- @@ L100-104 verbatim
theorem reindex_toEuclideanLin (e : d₁ ≃ d₃) (f : d₂ ≃ d) (M : Matrix d₁ d₂ 𝕜) :
    (M.reindex e f).toEuclideanLin = (LinearEquiv.euclideanOfRelabel 𝕜 e.symm) ∘ₗ
      M.toEuclideanLin ∘ₗ (LinearEquiv.euclideanOfRelabel 𝕜 f) := by
  ext
  simp [mulVec, dotProduct, Equiv.piCongrLeft_apply]


-- @@ L106-109 verbatim
theorem reindex_right_toLin' (e : d ≃ d₂) (M : Matrix d₃ d R) :
    (M.reindex (.refl d₃) e).toLin' = M.toLin' ∘ₗ (LinearEquiv.ofRelabel R e) := by
  rw [reindex_toLin']
  simp


-- @@ L111-115 verbatim
theorem reindex_right_toEuclideanLin (e : d ≃ d₂) (M : Matrix d₃ d 𝕜) :
    (M.reindex (.refl d₃) e).toEuclideanLin =
      M.toEuclideanLin ∘ₗ (LinearEquiv.euclideanOfRelabel 𝕜 e) := by
  ext
  simp [mulVec, dotProduct, Equiv.piCongrLeft_apply]


-- @@ L117-120 verbatim
theorem reindex_left_toLin' (e : d₁ ≃ d₃) (M : Matrix d₁ d₂ R) :
    (M.reindex e (.refl d₂)).toLin' = (LinearEquiv.ofRelabel R e.symm) ∘ M.toLin' := by
  rw [Matrix.reindex_toLin']
  simp


-- @@ L122-126 verbatim
theorem reindex_left_toEuclideanLin (e : d₁ ≃ d₃) (M : Matrix d₁ d₂ 𝕜) :
    (M.reindex e (.refl d₂)).toEuclideanLin =
      (LinearEquiv.euclideanOfRelabel 𝕜 e.symm) ∘ M.toEuclideanLin := by
  rw [Matrix.reindex_toEuclideanLin]
  simp


-- @@ L128-128 verbatim
end Matrix
