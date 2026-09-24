/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Structure.InvariantSubspaceDecomp
import TNLean.MPS.Core.BlockingInfrastructure


-- @@ L10-25 verbatim
/-!
# Basic projection word lemmas for cyclic-sector decompositions

This file contains the projection-word identities used throughout the
cyclic-sector normalization argument.

## Main declarations

* `leftSectorTensor`
* `left_mul_evalWord_leftSectorTensor_of_commutes`
* `leftSectorTensor_supported`

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
-/


-- @@ L27-27 verbatim
open scoped Matrix BigOperators ComplexOrder MatrixOrder

-- @@ L28-28 verbatim
open Matrix Finset Complex


-- @@ L30-30 verbatim
namespace MPSTensor


-- @@ L32-32 verbatim
variable {d D : ℕ}


-- @@ L34-34 verbatim
section BasicProjectionWordLemmas


-- @@ L36-60 verbatim
/-- Left-multiply every letter by `P`. -/
noncomputable def leftSectorTensor (P : MatrixAlg D) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => P * A i

lemma left_mul_evalWord_leftSectorTensor_of_commutes
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d),
      P * Kraus.evalWord (leftSectorTensor P A) w = P * Kraus.evalWord A w := by
  intro w
  induction w with
  | nil =>
      simp only [Kraus.evalWord]
  | cons i w ih =>
      simp only [leftSectorTensor, Kraus.evalWord]
      calc P * (P * A i * Kraus.evalWord (leftSectorTensor P A) w)
          = P * P * A i * Kraus.evalWord (leftSectorTensor P A) w := by
            simp only [Matrix.mul_assoc]
        _ = P * A i * Kraus.evalWord (leftSectorTensor P A) w := by rw [hPidem]
        _ = A i * (P * Kraus.evalWord (leftSectorTensor P A) w) := by
            rw [← Matrix.mul_assoc, hComm i, Matrix.mul_assoc]
        _ = A i * (P * Kraus.evalWord A w) := by rw [ih]
        _ = P * (A i * Kraus.evalWord A w) := by
            rw [← Matrix.mul_assoc, ← hComm i, Matrix.mul_assoc]


-- @@ L62-74 verbatim
/-- A left-sector tensor is supported on the sector projection. -/
lemma leftSectorTensor_supported
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ i : Fin d, P * leftSectorTensor P A i * P = leftSectorTensor P A i := by
  intro i
  simp only [leftSectorTensor]
  calc
    P * (P * A i) * P = P * P * A i * P := by
      simp only [Matrix.mul_assoc]
    _ = P * A i * P := by rw [hPidem]
    _ = P * A i := by rw [hComm i, Matrix.mul_assoc, hPidem]


-- @@ L76-76 verbatim
end BasicProjectionWordLemmas


-- @@ L78-78 verbatim
end MPSTensor
