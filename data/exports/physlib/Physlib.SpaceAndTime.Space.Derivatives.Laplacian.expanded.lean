/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Div

-- @@ L9-35 verbatim
/-!

# The Laplacian operator on `Space d`

## i. Overview

In this module we define the Laplacian operator on functions and vector-valued
functions defined on `Space d`.

## ii. Key results

- `laplacian` : The Laplacian operator on scalar functions on `Space d`.
- `laplacianVec` : The Laplacian operator on vector-valued functions on `Space d`.
- `distLaplacian` : The Laplacian operator on distributions on `Space d`.

## iii. Table of contents

- A. Laplacian on functions to ℝ
  - A.1. Relation between laplacian and divergence of gradient
- B. Laplacian on vector valued functions
- C. Laplacian of distributions
  - C.1. Laplacian of constant distributions

## iv. References

* None.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
namespace Space


-- @@ L41-45 verbatim
/-!

## A. Laplacian on functions to ℝ

-/


-- @@ L47-49 expanded
/-- The scalar `laplacian` operator. -/
noncomputable def laplacian {d} (f : Space d → ℝ) : Space d → ℝ :=
  div (∇ f)


-- @@ L51-52 verbatim
@[inherit_doc laplacian]
scoped[Space] notation "Δ" => laplacian


-- @@ L54-58 verbatim
/-!

### A.1. Relation between laplacian and divergence of gradient

-/


-- @@ L60-63 expanded
lemma laplacian_eq_sum_snd_deriv {d} (f : Space d → ℝ) :
    Δ f = fun x => ∑ i, (deriv i) ((deriv i) f) x :=
  by
  unfold laplacian div grad
  simp


-- @@ L65-69 verbatim
/-!

## B. Laplacian on vector valued functions

-/


-- @@ L71-75 verbatim
/-- The vector `laplacianVec` operator. -/
noncomputable def laplacianVec {d} (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x => WithLp.toLp 2 fun i =>
  -- get i-th component of `f`
  Δ (fun x => f x i) x


-- @@ L77-78 verbatim
@[inherit_doc laplacianVec]
scoped[Space] notation "Δᵥ" => laplacianVec


-- @@ L80-80 verbatim
open Physlib Distribution


-- @@ L82-86 verbatim
/-!

## C. Laplacian of distributions

-/


-- @@ L88-91 expanded
/-- The distributional `distLaplacian` operator. -/
noncomputable def distLaplacian {d} :
    (Distribution ℝ (Space d) ℝ) →ₗ[ℝ] Distribution ℝ (Space d) ℝ :=
  distDiv ∘ₗ distGrad


-- @@ L93-94 verbatim
@[inherit_doc distLaplacian]
scoped[Space] notation "Δᵈ" => distLaplacian


-- @@ L96-100 verbatim
/-!

### C.1. Laplacian of constant distributions

-/


-- @@ L102-105 verbatim
@[simp]
lemma distLaplacian_const {d : ℕ} (c : ℝ) :
    Δᵈ (Distribution.const ℝ (Space d) c) = 0 := by
  simp [distLaplacian, distGrad_const]


-- @@ L107-107 verbatim
end Space
