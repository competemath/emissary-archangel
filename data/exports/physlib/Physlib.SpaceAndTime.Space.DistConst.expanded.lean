/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Curl

-- @@ L9-32 verbatim
/-!

# The constant distribution on space

## i. Overview

In this module we define the constant distribution from `Space d` to a module `M`.
That is the distribution which sends every Schwartz function to its
integral multiplied by a fixed element `m : M`.

We show that the derivatives of this constant distribution are zero.
## ii. Key results

- `distConst` : The constant distribution from `Space d` to a module `M`.

## iii. Table of contents

- A. The definition of the constant distribution
- B. Derivatives of the constant distribution

## iv. References

* None.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open Physlib


-- @@ L38-38 verbatim
namespace Space

-- @@ L39-39 verbatim
open Distribution


-- @@ L41-45 verbatim
/-!

## A. The definition of the constant distribution

-/


-- @@ L47-50 expanded
/-- The constant distribution from `Space d` to a module `M` associated with
  `m : M`. -/
noncomputable def distConst {M} [NormedAddCommGroup M] [NormedSpace ℝ M] (d : ℕ) (m : M) :
    Distribution ℝ (Space d) M :=
  const ℝ (Space d) m


-- @@ L52-56 verbatim
/-!

## B. Derivatives of the constant distribution

-/


-- @@ L58-62 verbatim
@[simp]
lemma distDeriv_distConst {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (m : M) :
    distDeriv μ (distConst d m) = 0 := by
  simp [distDeriv, distConst]


-- @@ L64-67 verbatim
@[simp]
lemma distGrad_distConst {d} (m : ℝ) :
    distGrad (distConst d m) = 0 := by
  simp [distConst]


-- @@ L69-72 verbatim
@[simp]
lemma distDiv_distConst {d} (m : EuclideanSpace ℝ (Fin d)) :
    distDiv (distConst d m) = 0 := by
  simp [distDiv, distConst]


-- @@ L74-77 verbatim
@[simp]
lemma distCurl_distConst (m : EuclideanSpace ℝ (Fin 3)) :
    distCurl (distConst 3 m) = 0 := by
  simp [distCurl, distConst]


-- @@ L79-79 verbatim
end Space
