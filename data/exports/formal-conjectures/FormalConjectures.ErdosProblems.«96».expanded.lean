/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil


-- @@ L19-23 verbatim
/-!
# Erdős Problem 96

*Reference:* [erdosproblems.com/96](https://www.erdosproblems.com/96)
-/


-- @@ L25-25 verbatim
open Filter

-- @@ L26-26 verbatim
open EuclideanGeometry

-- @@ L27-27 verbatim
open scoped EuclideanGeometry


-- @@ L29-29 verbatim
namespace Erdos96

-- @@ L30-30 verbatim
open Finset


-- @@ L32-37 expanded
/-- The set of all possible numbers of unit distances determined by the vertices of a convex
$n$-gon.
-/
noncomputable def convexUnitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistNum points | (points : Finset (EuclideanSpace ℝ (Fin 2))) (_ : points.card = n) (_ :
    ConvexIndep points)}


-- @@ L39-48 verbatim
/--
This lemma confirms that the set of possible unit-distance counts is bounded above, which
ensures that taking the supremum (`sSup`) is a well-defined operation. The trivial upper bound is
the total number of pairs of points, $\binom{n}{2}$.
-/
@[category test, AMS 52]
theorem convexUnitDistanceCounts_bddAbove (n : ℕ) : BddAbove <| convexUnitDistanceCounts n := by
  use n.choose 2
  rintro _ ⟨points, rfl, _, rfl⟩
  exact unitDistNum_le_choose_two points


-- @@ L50-55 verbatim
/--
The **maximum number of unit distances** determined by the vertices of a convex $n$-gon.
This function is often denoted as $U_c(n)$ in combinatorics.
-/
noncomputable def maxConvexUnitDistances (n : ℕ) : ℕ :=
  sSup (convexUnitDistanceCounts n)


-- @@ L57-64 verbatim
/--
If $n$ points in $\mathbb{R}^2$ form a convex polygon then there are $O(n)$ many pairs which are
distance $1$ apart.
-/
@[category research open, AMS 52]
theorem erdos_96 :
    answer(sorry) ↔ (fun n => (maxConvexUnitDistances n : ℝ)) =O[atTop] fun n => (n : ℝ) := by
  sorry


-- @@ L66-66 verbatim
end Erdos96
