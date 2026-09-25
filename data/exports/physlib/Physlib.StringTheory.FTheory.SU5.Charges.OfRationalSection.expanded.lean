/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.TODO.Basic
public import Mathlib.Data.Fintype.Sets

-- @@ L10-53 verbatim
/-!

# Allowed charges

## i. Overview

Within SU(5) F-theory with 10d and 5-bar matter fields there are constraints on the
allowed U(1) charges the fields can have.
These constraints are determined in arXiv:1504.05593 [ref: lawrie_schafer_nameki_wong_2015].
They are related to the
distinct configurations of the zero-section (`σ₀`) relativity to the
additional rational section (`σ₁`s) in codimension one fiber.
For our purposes here, we currently just state the constraints found
in arXiv:1504.05593 [ref: lawrie_schafer_nameki_wong_2015], and leave the proof and derivation
of these constraints to future work.

## ii. Key results

- `CodimensionOneConfig` : The distinct configurations of the
  zero-section (`σ₀`) relativity to the additional rational section (`σ₁`s) in
  the codimension one fiber, `I₅`.
- `CodimensionOneConfig.allowedBarFiveCharges` : The allowed
  `U(1)`-charges of matter in the 5-bar representation of `SU(5)`
  given a `CodimensionOneConfig`.
- `CodimensionOneConfig.allowedTenCharges` : The allowed
  `U(1)`-charges of matter in the 10d representation of `SU(5)`
  given a `CodimensionOneConfig`.

## iii. Table of contents

- A. The distinct section configurations
  - A.1. The finiteness of the set of configurations
- B. The allowed charges given a configuration
  - B.1. The allowed charges of the 5-bar matter
  - B.2. The allowed charges of the 10d matter
  - B.3. The finiteness of the allowed charges

## iv. References

* The main reference for the material in this section: Lawrie, Schafer-Nameki and Wong, F-theory
  and All Things Rational: Surveying U(1) Symmetries with Rational Sections, page 6.
  [ref: lawrie_schafer_nameki_wong_2015]
* See also footnote 4 of 1507.05961. [ref: arxiv_1507_05961]
-/


-- @@ L55-55 verbatim
@[expose] public section


-- @@ L57-60 verbatim
TODO "The results in this file are currently stated, but not proved.
  They should should be proved following e.g. https://arxiv.org/pdf/1504.05593
  [ref: lawrie_schafer_nameki_wong_2015].
  This is a large project."


-- @@ L62-62 verbatim
namespace FTheory


-- @@ L64-64 verbatim
namespace SU5


-- @@ L66-70 verbatim
/-!

## A. The distinct section configurations

-/


-- @@ L72-84 verbatim
/-- The distinct codimension one configurations of the
  zero-section (`σ₀`) relativity to the additional rational section (`σ₁`s). -/
inductive CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the same `ℙ¹` of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(01)}` -/
  | same : CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the nearest neighbor `ℙ¹`s of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(0|1)}` -/
  | nearestNeighbor : CodimensionOneConfig
  /-- `σ₀` and `σ₁` intersect the next to nearest neighbor `ℙ¹`s of the `I₅` Kodaira fiber.
    This is sometimes denoted `I₅^{(0||1)}` -/
  | nextToNearestNeighbor : CodimensionOneConfig
deriving DecidableEq


-- @@ L86-86 verbatim
namespace CodimensionOneConfig


-- @@ L88-92 verbatim
/-!

### A.1. The finiteness of the set of configurations

-/


-- @@ L94-96 verbatim
instance : Fintype CodimensionOneConfig where
  elems := {same, nearestNeighbor, nextToNearestNeighbor}
  complete := by rintro (_ | _ | _) <;> decide


-- @@ L98-102 verbatim
/-!

## B. The allowed charges given a configuration

-/


-- @@ L104-108 verbatim
/-!

### B.1. The allowed charges of the 5-bar matter

-/


-- @@ L110-115 verbatim
/-- The allowed `U(1)`-charges of matter in the 5-bar representation of `SU(5)`
  given a `CodimensionOneConfig`. -/
def allowedBarFiveCharges : CodimensionOneConfig → Finset ℤ
  | same => {-3, -2, -1, 0, 1, 2, 3}
  | nearestNeighbor => {-14, -9, -4, 1, 6, 11}
  | nextToNearestNeighbor => {-13, -8, -3, 2, 7, 12}


-- @@ L117-121 verbatim
/-!

### B.2. The allowed charges of the 10d matter

-/


-- @@ L123-128 verbatim
/-- The allowed `U(1)`-charges of matter in the 10d representation of `SU(5)`
  given a `CodimensionOneConfig`. -/
def allowedTenCharges : CodimensionOneConfig → Finset ℤ
  | same => {-3, -2, -1, 0, 1, 2, 3}
  | nearestNeighbor => {-12, -7, -2, 3, 8, 13}
  | nextToNearestNeighbor => {-9, -4, 1, 6, 11}


-- @@ L130-134 verbatim
/-!

### B.3. The finiteness of the allowed charges

-/


-- @@ L136-139 verbatim
instance : (I : CodimensionOneConfig) → Fintype I.allowedBarFiveCharges
  | same => inferInstance
  | nearestNeighbor => inferInstance
  | nextToNearestNeighbor => inferInstance


-- @@ L141-144 verbatim
instance : (I : CodimensionOneConfig) → Fintype I.allowedTenCharges
  | same => inferInstance
  | nearestNeighbor => inferInstance
  | nextToNearestNeighbor => inferInstance


-- @@ L146-146 verbatim
end CodimensionOneConfig

-- @@ L147-147 verbatim
end SU5


-- @@ L149-149 verbatim
end FTheory
