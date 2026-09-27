/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.Defs
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Main
import Mathlib.Tactic.Positivity.Finset


-- @@ L13-39 verbatim
/-!
# Public interface: the `n = 1_000_000` lower bound

This file is a **human-facing entry point**.

If you want a single module to import (or open in an editor) to see what is proved and what the
objects mean, use this file.

## The graph family

All combinatorial objects live in `Distributed2Coloring.LowerBound.Defs`:

* `Vertex n` is an injective triple of symbols `(a,b,c)` with values in `{0,1,…,n-1}`.
* `Edge n` is an injective quadruple `(a,b,c,d)` encoding the directed edge
  `(a,b,c) → (b,c,d)` via `Edge.src` and `Edge.dst`.
* `Coloring n := Vertex n → Bool` is a 2-coloring of vertices.
* `monoFraction f : ℚ` is the fraction of edges whose endpoints have equal color.

## The main theorem

The main claim proved in this project is:

* `Distributed2Coloring.LowerBound.N1000000.monoFraction_ge_23879`

It states that for `n = 1_000_000`, every coloring has monochromatic-edge fraction at least
`23879/100000 = 0.23879`.
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
namespace Distributed2Coloring.LowerBound



-- @@ L46-46 verbatim
namespace N1000000Interface


-- @@ L48-49 verbatim
/-- The concrete parameter used in the main theorem: `n = 1_000_000`. -/
abbrev n₀ : Nat := N1000000Data.n


-- @@ L51-59 verbatim
/--
Convenience wrapper for the main theorem (to avoid re-declaring names from
`Distributed2Coloring.LowerBound.N1000000`).

See `Distributed2Coloring.LowerBound.N1000000.monoFraction_ge_23879`.
-/
theorem monoFraction_ge_23879 (f : Coloring n₀) :
    (23879 : ℚ) / 100000 ≤ monoFraction f := by
  simpa [n₀] using (N1000000.monoFraction_ge_23879 (f := f))


-- @@ L61-61 verbatim
end N1000000Interface


-- @@ L63-63 verbatim
end Distributed2Coloring.LowerBound
