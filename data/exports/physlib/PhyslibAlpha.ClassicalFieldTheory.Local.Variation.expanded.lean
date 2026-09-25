/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.ClassicalFieldTheory.Local.Variation

-- @@ L9-24 verbatim
/-!
# Alpha extensions for admissible local variations

## i. Overview

This module adds the Euclidean component API needed by the coordinate-readout CFT stack in
`PhyslibAlpha`.

The underlying `AdmissibleVariation` structure remains the maintained one from `Physlib`; this file
only adds helper lemmas used by the Alpha development.

## ii. Key results

- `ClassicalFieldTheory.Local.AdmissibleVariation.coord_euclidean`

-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
open Physlib


-- @@ L30-30 verbatim
namespace ClassicalFieldTheory

-- @@ L31-31 verbatim
namespace Local


-- @@ L33-33 verbatim
namespace AdmissibleVariation


-- @@ L35-35 verbatim
variable {d m : ℕ}


-- @@ L37-42 verbatim
/-- A Euclidean component of an admissible variation is again a test function. -/
@[fun_prop]
lemma coord_euclidean (η : AdmissibleVariation d (EuclideanSpace ℝ (Fin m))) (a : Fin m) :
    IsTestFunction (fun x => (η.toFun x) a) := by
  exact η.isTestFunction.comp_left (g := fun v : EuclideanSpace ℝ (Fin m) => v a)
    (by simp) (by fun_prop)


-- @@ L44-44 verbatim
end AdmissibleVariation


-- @@ L46-46 verbatim
end Local

-- @@ L47-47 verbatim
end ClassicalFieldTheory
