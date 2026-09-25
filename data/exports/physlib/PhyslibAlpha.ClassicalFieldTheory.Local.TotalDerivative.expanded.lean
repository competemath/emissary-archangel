/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.JetPoint

-- @@ L9-35 verbatim
/-!
# Total derivatives on local jet-dependent functions

## i. Overview

This module defines total derivatives of local jet-dependent functions by differentiating their
evaluation along jets of fields.

For the first local stage, this keeps the operator close to the use made in the Euler-Lagrange
formula, without yet introducing a separate coordinate-level derivative calculus on `JetPoint`.

## ii. Key results

- `ClassicalFieldTheory.Local.evalOnJet` : evaluate a jet-dependent function along a field.
- `ClassicalFieldTheory.Local.totalDerivative` : total derivative in one coordinate direction.
- `ClassicalFieldTheory.Local.iteratedTotalDerivative` : iterated total derivative indexed by a
  multi-index.

## iii. Table of contents

- A. Evaluation on jets
- B. Total derivatives

## iv. References

* None.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
open Physlib


-- @@ L41-41 verbatim
namespace ClassicalFieldTheory

-- @@ L42-42 verbatim
namespace Local


-- @@ L44-47 verbatim
/-!
## A. Evaluation on jets

-/


-- @@ L49-53 verbatim
/-- Evaluate a local jet-dependent function along the `k`-jet of a field. -/
noncomputable def evalOnJet (k : ℕ) (F : JetPoint d m k → ℝ)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    Space d → ℝ :=
  fun x => F (jetAt k f x)


-- @@ L55-58 verbatim
/-!
## B. Total derivatives

-/


-- @@ L60-63 expanded
/-- The total derivative of a jet-dependent function in the coordinate direction `i`. -/
noncomputable def totalDerivative (k : ℕ) (i : Fin d) (F : JetPoint d m k → ℝ)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Space d → ℝ :=
  (deriv i) (evalOnJet k F f)


-- @@ L65-68 expanded
/-- The iterated total derivative indexed by a multi-index. -/
noncomputable def iteratedTotalDerivative (k : ℕ) (I : MultiIndex d) (F : JetPoint d m k → ℝ)
    (f : Space d → EuclideanSpace ℝ (Fin m)) : Space d → ℝ :=
  (iteratedDeriv I) (evalOnJet k F f)


-- @@ L70-73 verbatim
@[simp]
lemma evalOnJet_apply (k : ℕ) (F : JetPoint d m k → ℝ)
    (f : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) :
    evalOnJet k F f x = F (jetAt k f x) := rfl


-- @@ L75-78 expanded
@[simp]
lemma totalDerivative_eq (k : ℕ) (i : Fin d) (F : JetPoint d m k → ℝ)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    totalDerivative k i F f = (deriv i) (fun x => F (jetAt k f x)) :=
  rfl


-- @@ L80-83 expanded
@[simp]
lemma iteratedTotalDerivative_eq (k : ℕ) (I : MultiIndex d) (F : JetPoint d m k → ℝ)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    iteratedTotalDerivative k I F f = (iteratedDeriv I) (fun x => F (jetAt k f x)) :=
  rfl


-- @@ L85-88 verbatim
lemma iteratedTotalDerivative_zero (k : ℕ) (F : JetPoint d m k → ℝ)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    iteratedTotalDerivative k (0 : MultiIndex d) F f = evalOnJet k F f := by
  simp [iteratedTotalDerivative]


-- @@ L90-94 verbatim
lemma iteratedTotalDerivative_single (k : ℕ) (i : Fin d) (F : JetPoint d m k → ℝ)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    iteratedTotalDerivative k (Physlib.MultiIndex.increment 0 i) F f =
      totalDerivative k i F f := by
  simp [iteratedTotalDerivative, totalDerivative]


-- @@ L96-96 verbatim
end Local

-- @@ L97-97 verbatim
end ClassicalFieldTheory
