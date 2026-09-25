/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Data.Real.Basic

-- @@ L9-33 verbatim
/-!

# The Speed of Light

## i. Overview

In this module we define a type for the speed of light in a vacuum,
along with some basic properties. An element of this type is a positive real number,
and should be thought of as the speed of light in some chosen but arbitrary system of units.

## ii. Key results

- `SpeedOfLight` : The type of speeds of light in a vacuum.

## iii. Table of contents

- A. The Speed of Light type
- B. Instances on the type
- C. The instance of one
- D. Positivity properties

## iv. References

* None.
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-41 verbatim
/-!

## A. The Speed of Light type

-/


-- @@ L43-48 verbatim
/-- The speed of light in a vacuum. An element of this type should be thought of as
  the speed of light in some chosen but arbitrary system of units. -/
structure SpeedOfLight where
  /-- The underlying value of the speed of light. -/
  val : ℝ
  pos : 0 < val


-- @@ L50-50 verbatim
namespace SpeedOfLight


-- @@ L52-56 verbatim
/-!

## B. Instances on the type

-/


-- @@ L58-58 verbatim
instance : Coe SpeedOfLight ℝ := ⟨SpeedOfLight.val⟩


-- @@ L60-67 verbatim
/-!

## C. The instance of one

We define the instance of one for `SpeedOfLight` to be the speed of light equal to `1`.
This is useful when we are working in units where the speed of light is equal to one.

-/


-- @@ L69-69 verbatim
instance : One SpeedOfLight := ⟨1, by grind⟩


-- @@ L71-72 verbatim
@[simp]
lemma val_one : (1 : SpeedOfLight).val = 1 := rfl


-- @@ L74-78 verbatim
/-!

## D. Positivity properties

-/


-- @@ L80-81 verbatim
@[simp]
lemma val_pos (c : SpeedOfLight) : 0 < (c : ℝ) := c.pos


-- @@ L83-84 verbatim
@[simp]
lemma val_nonneg (c : SpeedOfLight) : 0 ≤ (c : ℝ) := le_of_lt c.pos


-- @@ L86-87 verbatim
@[simp]
lemma val_ne_zero (c : SpeedOfLight) : (c : ℝ) ≠ 0 := ne_of_gt c.pos


-- @@ L89-89 verbatim
end SpeedOfLight
