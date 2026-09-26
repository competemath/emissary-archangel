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
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.Lattice.Nat


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-28 verbatim
/-!
# Cycle lengths and circumference

The cycle lengths and the longest cycle length of a graph.
-/


-- @@ L30-30 verbatim
namespace SimpleGraph


-- @@ L32-34 verbatim
/-- `G.cycleLengths` is the set of lengths of the cycles in `G`. -/
def cycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m | ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m}


-- @@ L36-38 verbatim
/-- `G.oddCycleLengths` is the set of lengths of odd cycles in `G`. -/
def oddCycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m ∈ G.cycleLengths | Odd m}


-- @@ L40-40 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L42-45 verbatim
/-- `circumference G` is the length of the longest cycle in `G`.
    It is `0` when `G` is acyclic. -/
noncomputable def circumference (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup G.cycleLengths


-- @@ L47-47 verbatim
end SimpleGraph
