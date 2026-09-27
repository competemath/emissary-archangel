/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos132ConvexK3.Basic
public import Mathlib.Data.Fin.VecNotation


-- @@ L11-17 verbatim
/-!
# Exact rational regression witnesses

Kernel-reduced checks for the three configurations used during the convex
`k = 3` campaign.  Keeping them at the basic layer lets global counterexample
regressions use them without importing the closure stack.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace LeanPool.Erdos132ConvexK3.Witnesses


-- @@ L23-23 verbatim
open LeanPool.Erdos132ConvexK3


-- @@ L25-27 verbatim
/-- Attempt 2's exact integer heptagon, in positive cyclic order. -/
def heptagon : Fin 7 → Point ℚ :=
  ![(0, 0), (72, 0), (45, 68), (40, 75), (36, 77), (32, 75), (27, 68)]


-- @@ L29-31 verbatim
theorem heptagon_strict_convex : CyclicStrictConvex heptagon := by
  unfold CyclicStrictConvex
  decide +kernel


-- @@ L33-36 verbatim
theorem heptagon_top_three :
    HasTopThreeDistanceClasses heptagon 7225 6649 5353 := by
  unfold HasTopThreeDistanceClasses
  decide +kernel


-- @@ L38-45 verbatim
theorem heptagon_double_ladder :
    sqDist (heptagon 0) (heptagon 6) = 5353 ∧
    sqDist (heptagon 0) (heptagon 5) = 6649 ∧
    sqDist (heptagon 0) (heptagon 4) = 7225 ∧
    sqDist (heptagon 1) (heptagon 2) = 5353 ∧
    sqDist (heptagon 1) (heptagon 3) = 6649 ∧
    sqDist (heptagon 1) (heptagon 4) = 7225 := by
  decide +kernel


-- @@ L47-48 verbatim
theorem heptagon_x_degree : vertexDegree heptagon 7225 6649 5353 0 = 5 := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Attempt 3's exact nine-point low-altitude insertion witness. -/
def ninePoint : Fin 9 → Point ℚ :=
  ![(0, 0), (180, -1), (370, -1), (570, 0), (309, 862),
    (300, 875), (285, 880), (270, 875), (261, 862)]


-- @@ L55-57 verbatim
theorem ninePoint_strict_convex : CyclicStrictConvex ninePoint := by
  unfold CyclicStrictConvex
  decide +kernel


-- @@ L59-62 verbatim
theorem ninePoint_top_three :
    HasTopThreeDistanceClasses ninePoint 855625 838525 811165 := by
  unfold HasTopThreeDistanceClasses
  decide +kernel


-- @@ L64-67 verbatim
theorem ninePoint_insertions_isolated :
    vertexDegree ninePoint 855625 838525 811165 1 = 0 ∧
      vertexDegree ninePoint 855625 838525 811165 2 = 0 := by
  decide +kernel


-- @@ L69-76 verbatim
/-- A second exact rational hexagon, in positive cyclic order. -/
def rationalHexagon : Fin 6 → Point ℚ :=
  ![(0, -20),
    (24171 / 50380, -(12571661 / 629750)),
    (48331 / 50380, -(12546661 / 629750)),
    (1208 / 229, -(4480 / 229)),
    (1, 0),
    (-1, 0)]


-- @@ L78-80 verbatim
theorem rationalHexagon_strict_convex : CyclicStrictConvex rationalHexagon := by
  unfold CyclicStrictConvex
  decide +kernel


-- @@ L82-86 verbatim
theorem rationalHexagon_top_three :
    HasTopThreeDistanceClasses rationalHexagon
      (96661 / 229) 401 (2776265163521 / 6927250000) := by
  unfold HasTopThreeDistanceClasses
  decide +kernel


-- @@ L88-95 verbatim
theorem rationalHexagon_key_edges :
    sqDist (rationalHexagon 3) (rationalHexagon 5) = 96661 / 229 ∧
    sqDist (rationalHexagon 0) (rationalHexagon 5) = 401 ∧
    sqDist (rationalHexagon 3) (rationalHexagon 4) = 401 ∧
    sqDist (rationalHexagon 0) (rationalHexagon 4) = 401 ∧
    sqDist (rationalHexagon 2) (rationalHexagon 5) =
      2776265163521 / 6927250000 := by
  decide +kernel


-- @@ L97-102 verbatim
theorem rationalHexagon_lower_degrees :
    vertexDegree rationalHexagon
        (96661 / 229) 401 (2776265163521 / 6927250000) 1 = 0 ∧
      vertexDegree rationalHexagon
        (96661 / 229) 401 (2776265163521 / 6927250000) 2 = 1 := by
  decide +kernel


-- @@ L104-104 verbatim
end LeanPool.Erdos132ConvexK3.Witnesses
