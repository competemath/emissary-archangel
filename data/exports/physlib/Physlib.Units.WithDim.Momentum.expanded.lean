/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic

-- @@ L9-15 verbatim
/-!
# Momentum

In this module we define the type `Momentum`, which represents the momentum of a particle
in `d`-dimensional space, in an arbitrary (but given) set of units.

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Dimension


-- @@ L21-23 verbatim
/-- Momentum in `d`-dimensional space in an arbitrary, but given, set of units.
  In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum. -/
abbrev Momentum (d : ℕ := 3) : Type := WithDim (M𝓭 * L𝓭 * T𝓭⁻¹) (Fin d → ℝ)
