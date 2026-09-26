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

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace SimpleGraph


-- @@ L27-27 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L29-41 verbatim
/--
Given a simple graph `G` with adjacency matrix `A`, this is the number `n₀ + min n₊ n₋` where:
- `n₀` is the multiplicity of zero as an eigenvalue of `A`
- `n₊` is the number of positive eigenvalues of `A` (counting multiplicities)
- `n₋` is the number of negative eigenvalues of `A` (counting multiplicities)
-/
noncomputable def cvetkovic (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI A : Matrix α α ℝ := G.adjMatrix ℝ
  letI spectrum : Multiset ℝ := (Matrix.charpoly A).roots
  letI positive_count : ℕ := spectrum.countP (fun x => 0 < x)
  letI negative_count : ℕ := spectrum.countP (fun x => 0 > x)
  letI zero_count : ℕ := spectrum.countP (fun x => 0 = x)
  zero_count + min positive_count negative_count


-- @@ L43-43 verbatim
end SimpleGraph
