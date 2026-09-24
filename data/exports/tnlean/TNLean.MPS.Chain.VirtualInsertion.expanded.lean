/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.OneSidedInverse


-- @@ L8-15 verbatim
/-!
# Physical realization map for virtual insertions

For an injective MPS tensor `A : Fin d → M_D(ℂ)`, a virtual insertion `X` on a bond
can be re-expressed as a physical operation on the local physical index.
This file defines the corresponding realization maps using the decomposition map
constructed in `OneSidedInverse`.
-/


-- @@ L17-17 verbatim
open scoped Matrix BigOperators


-- @@ L19-19 verbatim
namespace MPSTensor


-- @@ L21-21 verbatim
variable {d D : ℕ}


-- @@ L23-28 verbatim
/-- The physical realization of a right virtual insertion.
For injective `A`, `physRealize A hA X` is the `d × d` matrix of coefficients
that rewrites each `A i * X` in the spanning family `{A j}`. -/
noncomputable def physRealize (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => Kraus.decompositionMap (A := A) hA (A i * X) j


-- @@ L30-35 verbatim
/-- Defining property of `physRealize`: each right-inserted matrix decomposes
in the span of `{A j}` with coefficients read from `physRealize`. -/
theorem physRealize_spec (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    A i * X = ∑ j, (physRealize A hA X) i j • A j :=
  (Kraus.decompositionMap_sum (A := A) hA (A i * X)).symm


-- @@ L37-41 verbatim
/-- Left-bond analogue of `physRealize`:
`physRealizeLeft A hA X` captures coefficients that rewrite each `X * A i`. -/
noncomputable def physRealizeLeft (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => Kraus.decompositionMap (A := A) hA (X * A i) j


-- @@ L43-47 verbatim
/-- Defining property for the left-bond realization map. -/
theorem physRealizeLeft_spec (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    X * A i = ∑ j, (physRealizeLeft A hA X) i j • A j :=
  (Kraus.decompositionMap_sum (A := A) hA (X * A i)).symm


-- @@ L49-78 verbatim
/-- `physRealize` preserves multiplication. -/
theorem physRealize_mul (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physRealize A hA (X * Y) = physRealize A hA X * physRealize A hA Y := by
  ext i k
  change Kraus.decompositionMap (A := A) hA (A i * (X * Y)) k =
    (physRealize A hA X * physRealize A hA Y) i k
  have hdecomp :
      Kraus.decompositionMap (A := A) hA (A i * (X * Y))
        = ∑ j, (physRealize A hA X) i j • Kraus.decompositionMap (A := A) hA (A j * Y) := by
    calc
      Kraus.decompositionMap (A := A) hA (A i * (X * Y))
          = Kraus.decompositionMap (A := A) hA ((A i * X) * Y) := by
              simp [Matrix.mul_assoc]
      _ = Kraus.decompositionMap (A := A) hA ((∑ j, (physRealize A hA X) i j • A j) * Y) := by
            rw [← physRealize_spec A hA X i]
      _ = Kraus.decompositionMap (A := A) hA (∑ j, (physRealize A hA X) i j • (A j * Y)) := by
            simp [Finset.sum_mul]
      _ = ∑ j, (physRealize A hA X) i j • Kraus.decompositionMap (A := A) hA (A j * Y) := by
            simp
  calc
    Kraus.decompositionMap (A := A) hA (A i * (X * Y)) k
        = (∑ j, (physRealize A hA X) i j • Kraus.decompositionMap (A := A) hA (A j * Y)) k := by
            simpa using congrArg (fun f => f k) hdecomp
    _ = ∑ j, (physRealize A hA X) i j * (Kraus.decompositionMap (A := A) hA (A j * Y)) k := by
          simp
    _ = ∑ j, (physRealize A hA X) i j * (physRealize A hA Y) j k := by
          simp [physRealize]
    _ = (physRealize A hA X * physRealize A hA Y) i k := by
          simp [Matrix.mul_apply]


-- @@ L80-84 verbatim
/-- Three-site coefficient with a virtual insertion `X` between the first and
second local tensors. -/
def virtualInsertCoeff (A₁ A₂ A₃ : MPSTensor d D)
    (σ : Fin 3 → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  Matrix.trace (A₁ (σ 0) * X * A₂ (σ 1) * A₃ (σ 2))


-- @@ L86-89 verbatim
@[simp] lemma virtualInsertCoeff_eq (A₁ A₂ A₃ : MPSTensor d D)
    (σ : Fin 3 → Fin d) (X : Matrix (Fin D) (Fin D) ℂ) :
    virtualInsertCoeff A₁ A₂ A₃ σ X =
      Matrix.trace (A₁ (σ 0) * X * A₂ (σ 1) * A₃ (σ 2)) := rfl


-- @@ L91-91 verbatim
end MPSTensor
