/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.Defs
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000WeakDuality
import LeanPool.TwoColoringOneRound.LowerBound.N1000000BCompressionForB
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Bound
import Mathlib.Tactic.Positivity.Finset


-- @@ L14-16 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000Main
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L22-22 verbatim
namespace N1000000


-- @@ L24-24 verbatim
open Distributed2Coloring.LowerBound.N1000000BCompressionForB

-- @@ L25-25 verbatim
open Distributed2Coloring.LowerBound.N1000000Bound

-- @@ L26-26 verbatim
open Distributed2Coloring.LowerBound.N1000000Data

-- @@ L27-27 verbatim
open Distributed2Coloring.LowerBound.N1000000Relaxation

-- @@ L28-28 verbatim
open Distributed2Coloring.LowerBound.N1000000RelaxationPsdSoundness

-- @@ L29-29 verbatim
open Distributed2Coloring.LowerBound.N1000000WeakDuality


-- @@ L31-32 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n

-- @@ L33-34 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ

-- @@ L35-36 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Block := N1000000WeakDuality.Block


-- @@ L38-53 verbatim
/--
Main deliverable (kernel-checked):

For `n = 1,000,000`, every `Coloring n` has monochromatic-edge fraction at least `23879/100000`.

Definitions:
- `Coloring` / `monoFraction` / `Edge.monochromatic` are in `Distributed2Coloring.LowerBound.Defs`.
- The proof combines a precomputed exact rational dual certificate with weak duality, and shows the
  required PSD constraints for `xFromColoring f` via a compression/congruence argument.
-/
theorem monoFraction_ge_23879 (f : Coloring n) :
    (23879 : Q) / 100000 ≤ monoFraction f := by
  have hcomp : CompressionHypScaled := N1000000BCompressionForB.compressionHypScaled
  have hpsd : ∀ r : Block, (S (xFromColoring f) r).PosSemidef :=
    psd_of_compressionHypScaled hcomp f
  exact N1000000Bound.monoFraction_ge_23879_of_psd (f := f) hpsd


-- @@ L55-55 verbatim
end N1000000


-- @@ L57-57 verbatim
end Distributed2Coloring.LowerBound
