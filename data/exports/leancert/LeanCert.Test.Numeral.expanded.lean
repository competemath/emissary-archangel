/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Meta.ToExpr
import LeanCert.Tactic.IntervalAuto


-- @@ L9-13 verbatim
/-!
# Numeric Extraction Regression Tests

Smoke tests for canonical rational extraction through reification.
-/


-- @@ L15-15 verbatim
namespace LeanCert.Test.Numeral


-- @@ L17-17 verbatim
def myRat : ℚ := 9 / 500


-- @@ L19-19 verbatim
#leancert_reflect (fun _x : Real => ((9 / 500 : Rat) : Real))

-- @@ L20-20 verbatim
#leancert_reflect (fun _x : Real => (myRat : Real))

-- @@ L21-21 verbatim
#leancert_reflect (fun x : Real => x + (((-2 : Int) : Real) + 3))

-- @@ L22-22 verbatim
#leancert_reflect (fun x : Real => x + 2.72)

-- @@ L23-23 verbatim
#leancert_reflect (fun x : Real => x + ((1 : Nat) : Real))


-- @@ L25-27 verbatim
theorem interval_bound_nat_cast :
    ∀ x ∈ Set.Icc (0 : Real) 1, x + ((1 : Nat) : Real) ≤ (2 : Rat) := by
  certify_bound


-- @@ L29-29 verbatim
end LeanCert.Test.Numeral
