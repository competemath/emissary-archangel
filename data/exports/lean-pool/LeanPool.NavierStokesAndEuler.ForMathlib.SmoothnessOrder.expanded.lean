/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.ENat.Basic


-- @@ L11-17 verbatim
/-!
# Comparing smoothness orders with infinity

The outer top of `WithTop ℕ∞` is analytic regularity. Every other order is
at most smooth regularity. This characterization lets simplification handle
finite derivative orders without depending on their numeral representation.
-/


-- @@ L19-19 verbatim
public section


-- @@ L21-21 verbatim
namespace NavierStokesAndEuler


-- @@ L23-27 verbatim
theorem le_infinity_iff_ne_top (n : WithTop ℕ∞) :
    n ≤ (⊤ : ℕ∞) ↔ n ≠ ⊤ := by
  cases n with
  | top => simp
  | coe n => simp


-- @@ L29-29 verbatim
end NavierStokesAndEuler
