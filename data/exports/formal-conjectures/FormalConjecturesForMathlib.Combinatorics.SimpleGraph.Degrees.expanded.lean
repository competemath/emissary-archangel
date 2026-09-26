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

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.CompletePartialOrder


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
namespace SimpleGraph


-- @@ L31-31 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L33-35 verbatim
/-- The average degree of `G`. -/
noncomputable def averageDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ  :=
  (∑ v, (G.degree v : ℚ)) / (Fintype.card α : ℚ)


-- @@ L37-39 verbatim
/-- The multiset of degrees of a graph. -/
def degreeMultiset (G : SimpleGraph α) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun v => G.degree v


-- @@ L41-43 verbatim
/-- The degree sequence of a graph, sorted in nondecreasing order. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)


-- @@ L45-50 verbatim
/--
The maximum number of occurrences of any term of the degree sequence of `G`.
-/
noncomputable def degreeSequenceMultiplicity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI degs := degreeSequence G
  (List.max? (degs.map (fun d => degs.count d))).getD 0


-- @@ L52-57 verbatim
/-- Infinite graphs: definitions for max degree and clique number so that the maximum
degree of a graph with unbounded degree is
`∞` rather than 0.
-/
noncomputable
def edegree {V : Type*} (G : SimpleGraph V) (v : V) : ℕ∞ := (G.neighborSet v).encard


-- @@ L59-60 verbatim
noncomputable
def emaxDegree {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨆ v, G.edegree v


-- @@ L62-65 verbatim
/-- Cardinality of the union of the neighbourhoods of the ends of the non-edge `e`. -/
def non_edge_neighborhood_card (G : SimpleGraph α) [DecidableRel G.Adj] (e : Sym2 α) : ℕ :=
  Sym2.lift ⟨fun u v => (G.neighborFinset u ∪ G.neighborFinset v).card,
    fun u v => by simp [Finset.union_comm]⟩ e


-- @@ L67-74 verbatim
/-- Minimum size of the neighbourhood of a non-edge of `G`. -/
noncomputable def NG (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let non_edges := (compl G).edgeFinset
  if h : non_edges.Nonempty then
    let neighbor_sizes := non_edges.image (non_edge_neighborhood_card G)
    (neighbor_sizes.min' (Finset.Nonempty.image h _))
  else
    (Fintype.card α : ℝ)


-- @@ L76-82 verbatim
noncomputable def S (G : SimpleGraph α) : ℝ :=
  open scoped Classical in
  let card := Fintype.card α
  if card < 2 then 0 else
    let degrees := Multiset.ofList (List.map (fun v => G.degree v) Finset.univ.toList)
    let sorted_degrees := degrees.sort (· ≤ ·)
    ↑((sorted_degrees[card - 2]?).getD 0)


-- @@ L84-90 verbatim
/-- The **second-smallest degree** of `G`'s degree sequence — DeLaVina's `σ(G)`
per the WOWII definitions popup (defEntry 65): "order the degree sequence in
nondecreasing order `d₁ ≤ d₂ ≤ … ≤ dₙ`, the second smallest degree of the
sequence is the 2nd entry". For graphs with `n ≤ 1` we conventionally
return `0`. -/
noncomputable def secondSmallestDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (degreeSequence G).getD 1 0


-- @@ L92-95 verbatim
/-- The number of triangles (3-cliques) of `G` incident to vertex `v`:
the number of 3-element cliques containing `v`. -/
noncomputable def numTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card


-- @@ L97-99 verbatim
/-- The length of a graph: the square root of the sum of the squares of degrees. -/
noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)


-- @@ L101-103 verbatim
/-- The number of vertices of degree k in `G`. -/
def countDegreeK (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = k)).card


-- @@ L105-105 verbatim
end SimpleGraph
