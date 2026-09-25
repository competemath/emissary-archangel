/-
Copyright (c) 2025 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Div

-- @@ L9-39 verbatim
/-!

# Matrix divergence on Space

## i. Overview

In this module we define the matrix divergence operator on matrix-valued
functions from `Space d`.

For a field `T : Space d → Matrix (Fin d) (Fin d) ℝ`, the matrix divergence is
the vector field whose `i`th component is

`∑ j, ∂[j] (fun x => T x i j) x`.

## ii. Key results

- `matrixDiv` : The divergence of a matrix-valued function on `Space d`.

## iii. Table of contents

- A. The matrix divergence on functions
  - A.1. Basic equalities
  - A.2. The matrix divergence on the zero function
  - A.3. The matrix divergence on a constant function
  - A.4. The matrix divergence distributes over addition
  - A.5. The matrix divergence distributes over scalar multiplication

## iv. References

* None.
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
open Physlib


-- @@ L45-45 verbatim
namespace Space


-- @@ L47-51 verbatim
/-!

## A. The matrix divergence on functions

-/


-- @@ L53-62 verbatim
/-- The divergence of a matrix-valued spatial field.

For a field `T : Space d → Matrix (Fin d) (Fin d) ℝ`, `matrixDiv T` is the
vector field whose `i`th component is

`∑ j, ∂[j] (fun x => T x i j) x`.
-/
noncomputable def matrixDiv (d : ℕ) (T : Space d → Matrix (Fin d) (Fin d) ℝ) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x => WithLp.toLp 2 fun i =>
  div (fun y : Space d => WithLp.toLp 2 fun j => T y i j) x


-- @@ L64-68 verbatim
/-!

### A.1. Basic equalities

-/


-- @@ L70-74 expanded
@[simp]
lemma matrixDiv_apply (d : ℕ) (T : Space d → Matrix (Fin d) (Fin d) ℝ) (x : Space d) (i : Fin d) :
    matrixDiv d T x i = ∑ j, (deriv j) (fun x => T x i j) x := by simp [matrixDiv, div]


-- @@ L76-80 verbatim
/-!

### A.2. The matrix divergence on the zero function

-/


-- @@ L82-87 expanded
@[simp]
lemma matrixDiv_zero (d : ℕ) : matrixDiv d (0 : Space d → Matrix (Fin d) (Fin d) ℝ) = 0 :=
  by
  ext x i
  change (∑ j : Fin d, (deriv j) (fun _ : Space d => (0 : ℝ)) x) = 0
  simp


-- @@ L89-93 verbatim
/-!

### A.3. The matrix divergence on a constant function

-/


-- @@ L95-100 expanded
@[simp]
lemma matrixDiv_const (d : ℕ) (T : Matrix (Fin d) (Fin d) ℝ) :
    matrixDiv d (fun _ : Space d => T) = 0 := by
  ext x i
  change (∑ j : Fin d, (deriv j) (fun _ : Space d => T i j) x) = 0
  simp


-- @@ L102-106 verbatim
/-!

### A.4. The matrix divergence distributes over addition

-/


-- @@ L108-123 expanded
lemma matrixDiv_add (d : ℕ) (T1 T2 : Space d → Matrix (Fin d) (Fin d) ℝ) (hT1 : Differentiable ℝ T1)
    (hT2 : Differentiable ℝ T2) : matrixDiv d (T1 + T2) = matrixDiv d T1 + matrixDiv d T2 :=
  by
  ext x i
  change
    (∑ j, (deriv j) (fun x => (T1 x + T2 x) i j) x) =
      (∑ j, (deriv j) (fun x => T1 x i j) x) + ∑ j, (deriv j) (fun x => T2 x i j) x
  rw [← Finset.sum_add_distrib]
  congr
  funext j
  change
    (deriv j) ((fun x => T1 x i j) + fun x => T2 x i j) x =
      (deriv j) (fun x => T1 x i j) x + (deriv j) (fun x => T2 x i j) x
  rw [deriv_add]
  · rfl
  · exact differentiable_pi.mp (differentiable_pi.mp hT1 i) j
  · exact differentiable_pi.mp (differentiable_pi.mp hT2 i) j


-- @@ L125-129 verbatim
/-!

### A.5. The matrix divergence distributes over scalar multiplication

-/


-- @@ L131-143 expanded
lemma matrixDiv_smul (d : ℕ) (T : Space d → Matrix (Fin d) (Fin d) ℝ) (k : ℝ)
    (hT : Differentiable ℝ T) : matrixDiv d (k • T) = k • matrixDiv d T :=
  by
  ext x i
  change (∑ j, (deriv j) (fun x => (k • T x) i j) x) = k * ∑ j, (deriv j) (fun x => T x i j) x
  rw [Finset.mul_sum]
  congr
  funext j
  change (deriv j) (k • fun x => T x i j) x = k • (deriv j) (fun x => T x i j) x
  rw [deriv_const_smul]
  · rfl
  · exact differentiable_pi.mp (differentiable_pi.mp hT i) j


-- @@ L145-145 verbatim
end Space
