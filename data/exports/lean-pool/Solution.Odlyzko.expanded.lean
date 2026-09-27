/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project, √2
-/

module

public import LeanPool.Odlyzko


-- @@ L11-22 verbatim
/-!
# Solution: Odlyzko bound for root discriminants

Challenge: `odlyzko-root-discriminant-bound` (`Challenge.Odlyzko`)
Proves: `Challenge.Odlyzko.abs_discr_ge`
Solved by: The FLT Project, √2
Pool project: `odlyzko-bound`

This module restates the challenge statement under its own name and proves it. It must not import
the challenge module: comparator exports both environments separately and checks that the statements
agree, which is what makes the verdict independent of the statement file.
-/


-- @@ L24-26 verbatim
/-!
# Solution to the Odlyzko root-discriminant challenge
-/


-- @@ L28-28 verbatim
public section


-- @@ L30-30 verbatim
namespace Challenge.Odlyzko


-- @@ L32-32 verbatim
open Module NumberField


-- @@ L34-38 verbatim
/-- A totally complex number field of degree at least 18 has absolute
discriminant at least `8.25` raised to its degree. -/
theorem abs_discr_ge (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K :=
  NumberField.Odlyzko.odlyzkoBound K hdim


-- @@ L40-40 verbatim
end Challenge.Odlyzko
