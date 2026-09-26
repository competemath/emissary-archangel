/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-35 verbatim
/-!
# Well totally dominated graphs

A *total dominating set* of `G` is a set `S` of vertices such that every vertex of `G`
(including vertices in `S`) has a neighbor in `S`. A total dominating set `S` is
*minimal* if no proper subset of `S` is also a total dominating set.

A graph `G` is *well totally dominated* if every minimal total dominating set has the
same cardinality; equivalently, the total domination number equals the maximum
cardinality of a minimal total dominating set.

The *pendant vertices* (also called *leaves*) of `G` are the vertices of degree 1.
-/


-- @@ L37-37 verbatim
namespace SimpleGraph


-- @@ L39-39 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L41-43 verbatim
/-- A set `S` is a total dominating set of `G` if every vertex has a neighbor in `S`. -/
def IsTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v : α, ∃ w ∈ S, G.Adj v w


-- @@ L45-49 verbatim
/-- A total dominating set `S` is minimal if no proper subset of `S` is also a
total dominating set. -/
def IsMinimalTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  IsTotalDominatingSet G S ∧
  ∀ T : Finset α, T ⊂ S → ¬IsTotalDominatingSet G T


-- @@ L51-57 verbatim
/-- A graph `G` is well totally dominated if every minimal total dominating set
has the same cardinality. -/
def IsWellTotallyDominated (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  ∀ S T : Finset α,
    IsMinimalTotalDominatingSet G S →
    IsMinimalTotalDominatingSet G T →
    S.card = T.card


-- @@ L59-61 verbatim
/-- The set of pendant vertices (leaves) of `G`: vertices of degree 1. -/
noncomputable def pendantVertices (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  Finset.univ.filter (fun v => G.degree v = 1)


-- @@ L63-63 verbatim
end SimpleGraph
