/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.Mathematics.VariationalCalculus.IsTestFunction

-- @@ L9-32 verbatim
/-!
# Admissible local variations

## i. Overview

This module packages the admissible variations used in the local first-variation problem.

For the first local stage, a variation is admissible if it is a smooth compactly supported map
`Space d → U` for a real normed vector space `U`. This reuses the existing `IsTestFunction`
predicate rather than introducing a second support calculus.

## ii. Key results

- `ClassicalFieldTheory.Local.AdmissibleVariation` : compactly supported smooth variations.

## iii. Table of contents

- A. Admissible variations
- B. Basic operations on admissible variations

## iv. References

* None.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open MeasureTheory

-- @@ L37-37 verbatim
open Physlib


-- @@ L39-39 verbatim
namespace ClassicalFieldTheory

-- @@ L40-40 verbatim
namespace Local


-- @@ L42-45 verbatim
/-!
## A. Admissible variations

-/


-- @@ L47-52 verbatim
/-- An admissible local variation is a smooth compactly supported map `Space d → U`. -/
structure AdmissibleVariation (d : ℕ) (U : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U] where
  /-- The underlying variation function. -/
  toFun : Space d → U
  /-- Smoothness and compact support of the variation. -/
  isTestFunction : IsTestFunction toFun


-- @@ L54-54 verbatim
namespace AdmissibleVariation


-- @@ L56-56 verbatim
variable {d : ℕ} {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]


-- @@ L58-61 verbatim
/-!
## B. Basic operations on admissible variations

-/


-- @@ L63-64 verbatim
instance : CoeFun (AdmissibleVariation d U) (fun _ => Space d → U) where
  coe η := η.toFun


-- @@ L66-66 verbatim
attribute [fun_prop] AdmissibleVariation.isTestFunction


-- @@ L68-70 verbatim
/-- An admissible variation has compact support. -/
lemma hasCompactSupport (η : AdmissibleVariation d U) : HasCompactSupport (η.toFun) :=
  η.isTestFunction.supp


-- @@ L72-75 verbatim
/-- View an admissible variation as a compactly supported continuous map. -/
noncomputable def toCompactlySupportedContinuousMap (η : AdmissibleVariation d U) :
    CompactlySupportedContinuousMap (Space d) U :=
  η.isTestFunction.toCompactlySupportedContinuousMap


-- @@ L77-80 verbatim
noncomputable instance : Zero (AdmissibleVariation d U) where
  zero :=
    { toFun := fun _ => 0
      isTestFunction := IsTestFunction.zero }


-- @@ L82-83 verbatim
@[simp]
lemma zero_apply (x : Space d) : (0 : AdmissibleVariation d U) x = 0 := rfl


-- @@ L85-88 verbatim
noncomputable instance : Neg (AdmissibleVariation d U) where
  neg η :=
    { toFun := fun x => -η x
      isTestFunction := η.isTestFunction.neg }


-- @@ L90-91 verbatim
@[simp]
lemma neg_apply (η : AdmissibleVariation d U) (x : Space d) : (-η) x = -η x := rfl


-- @@ L93-96 verbatim
noncomputable instance : Add (AdmissibleVariation d U) where
  add η ξ :=
    { toFun := fun x => η x + ξ x
      isTestFunction := η.isTestFunction.add ξ.isTestFunction }


-- @@ L98-99 verbatim
@[simp]
lemma add_apply (η ξ : AdmissibleVariation d U) (x : Space d) : (η + ξ) x = η x + ξ x := rfl


-- @@ L101-104 verbatim
noncomputable instance : Sub (AdmissibleVariation d U) where
  sub η ξ :=
    { toFun := fun x => η x - ξ x
      isTestFunction := η.isTestFunction.sub ξ.isTestFunction }


-- @@ L106-107 verbatim
@[simp]
lemma sub_apply (η ξ : AdmissibleVariation d U) (x : Space d) : (η - ξ) x = η x - ξ x := rfl


-- @@ L109-113 verbatim
noncomputable instance : SMul ℝ (AdmissibleVariation d U) where
  smul c η :=
    { toFun := fun x => c • η x
      isTestFunction := IsTestFunction.smul_left (f := fun _ : Space d => c) (g := η.toFun)
        (by fun_prop) η.isTestFunction }


-- @@ L115-117 verbatim
@[simp]
lemma smul_apply (c : ℝ) (η : AdmissibleVariation d U) (x : Space d) :
    (c • η) x = c • η x := rfl


-- @@ L119-122 verbatim
@[fun_prop]
lemma coord {m : ℕ} (η : AdmissibleVariation d (Space m)) (a : Fin m) :
    IsTestFunction (fun x => (η.toFun x).coord a) := by
  simpa [Space.coord] using IsTestFunction.coord η.isTestFunction a


-- @@ L124-124 verbatim
end AdmissibleVariation


-- @@ L126-126 verbatim
end Local

-- @@ L127-127 verbatim
end ClassicalFieldTheory
