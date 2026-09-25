/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Tactic.DeriveFintype

-- @@ L9-36 verbatim
/-!

# The field labels

## i. Overview

To each field and it's conjugate in the `SU(5)` SUSY GUT we assign a label,
namely an element of the inductive type `FieldLabel`.

This field label will be used to specify the representations of fields present in
terms of the lagrangian.

## ii. Key results

The key results are
- `FieldLabel` : the inductive type of field labels.
- `FieldLabel.RParity` : the R-parity of a field label, being `1` if it is in
  the non-trivial representation and `0` otherwise.

## iii. Table of contents

- A. The field labels
- B. R-parity of a field label

## iv. References

* None.
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
namespace SuperSymmetry

-- @@ L41-41 verbatim
namespace SU5


-- @@ L43-52 verbatim
/-!

## A. The field labels

The inductive type `FieldLabel` is defined, with one constructor for each field
and it's conjugate present in the `SU(5)` SUSY GUT.

Note that there is only one `10` representation, as it is self-conjugate.

-/


-- @@ L54-63 verbatim
/-- The types of field present in an SU(5) GUT. -/
inductive FieldLabel
  | fiveBarHu
  | fiveHu
  | fiveBarHd
  | fiveHd
  | fiveBarMatter
  | fiveMatter
  | tenMatter
deriving DecidableEq


-- @@ L65-67 verbatim
instance : Fintype FieldLabel where
  elems := {.fiveBarHu, .fiveHu, .fiveBarHd, .fiveHd, .fiveBarMatter, .fiveMatter, .tenMatter}
  complete := fun x => by cases x <;> decide


-- @@ L69-76 verbatim
/-!

## B. R-parity of a field label

We define the R-parity of a field label, being `1` if it is in the non-trivial
representation and `0` otherwise.

-/


-- @@ L78-87 verbatim
/-- The R-Parity of a field, landing on `1` if it is in the non-trivial representation
  and `0` otherwise. -/
def FieldLabel.RParity : FieldLabel → Fin 2
  | fiveBarHu => 0
  | fiveHu => 0
  | fiveBarHd => 0
  | fiveHd => 0
  | fiveBarMatter => 1
  | fiveMatter => 1
  | tenMatter => 1


-- @@ L89-89 verbatim
end SU5

-- @@ L90-90 verbatim
end SuperSymmetry
