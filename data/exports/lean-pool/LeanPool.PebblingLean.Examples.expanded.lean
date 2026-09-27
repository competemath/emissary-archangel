/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import LeanPool.PebblingLean.Hypercube
import Mathlib.Tactic.Bound.Init


-- @@ L11-16 verbatim
/-!
# Small examples

These definitions give named vertices and distributions for testing the basic
API on low-dimensional cubes.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace PebblingLean


-- @@ L22-22 verbatim
namespace Hypercube


-- @@ L24-26 verbatim
/-- The all-zero vertex of a hypercube. -/
def zeroVertex (n : ℕ) : HypercubeVertex n :=
  fun _ => false


-- @@ L28-30 verbatim
/-- The all-one vertex of a hypercube. -/
def oneVertex (n : ℕ) : HypercubeVertex n :=
  fun _ => true


-- @@ L32-33 verbatim
theorem dist_zero_zero (n : ℕ) : dist (zeroVertex n) (zeroVertex n) = 0 := by
  exact dist_self (zeroVertex n)


-- @@ L35-35 verbatim
end Hypercube


-- @@ L37-37 verbatim
namespace Examples


-- @@ L39-41 verbatim
/-- Three pebbles on one vertex of the square `Q_2`. -/
def squareThreeAtZero : Pebbling (HypercubeVertex 2) :=
  fun x => if x = Hypercube.zeroVertex 2 then 3 else 0


-- @@ L43-43 verbatim
end Examples


-- @@ L45-45 verbatim
end PebblingLean
