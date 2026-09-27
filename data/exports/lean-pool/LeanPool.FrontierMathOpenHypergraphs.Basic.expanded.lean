/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.Order.Lattice.Nat


-- @@ L10-14 verbatim
/-!
# Basic definitions for the hypergraph lower bound

Basic definitions and the substitution theorem for the hypergraph lower bound.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Finset


-- @@ L20-20 verbatim
namespace HypergraphLowerBound


-- @@ L22-22 verbatim
/-! ## Hypergraph definitions -/


-- @@ L24-25 verbatim
/-- A finite hypergraph on `V`, encoded by its finite edge family. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)


-- @@ L27-28 verbatim
/-- A family of hypergraphs indexed by `ι`. -/
abbrev HypergraphFamily (ι : Type*) (V : Type*) := ι → Hypergraph V


-- @@ L30-33 verbatim
/-- The vertex set of a hypergraph given by its edge set: the union of all edges. -/
noncomputable def vertexSet {V : Type*} [DecidableEq V]
    (edges : Hypergraph V) : Finset V :=
  edges.biUnion id


-- @@ L35-38 verbatim
/-- The unique coverage count: the number of vertices belonging to exactly one edge in P. -/
noncomputable def uniqueCoverage {V : Type*} [DecidableEq V]
    (edges : Hypergraph V) (P : Hypergraph V) : ℕ :=
  (vertexSet edges).filter (fun v => (P.filter (fun e => v ∈ e)).card = 1) |>.card


-- @@ L40-43 verbatim
/-- A hypergraph contains no partition of size greater than n. -/
def NoLargePartition {V : Type*} [DecidableEq V]
    (edges : Hypergraph V) (n : ℕ) : Prop :=
  ∀ P : Hypergraph V, P ⊆ edges → uniqueCoverage edges P ≤ n


-- @@ L45-52 verbatim
/-- `H n` is the largest number of vertices of a finite hypergraph with no isolated
    vertices and no partition of size greater than `n`.

    In this development hypergraphs are encoded by their edge sets, so "no isolated
    vertices" is reflected by taking the vertex set to be the union of the edges. -/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (edges : Hypergraph ℕ),
    (vertexSet edges).card = k ∧ NoLargePartition edges n}


-- @@ L54-54 verbatim
/-! ## The benchmark sequence k_n -/


-- @@ L56-65 verbatim
/-- The benchmark sequence k(n) defined by k(1) = 1 and
    k(n) = ⌊n/2⌋ + k(⌊n/2⌋) + k(⌊(n+1)/2⌋) for n ≥ 2. -/
def k : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let half := (n + 2) / 2
    let halfUp := (n + 3) / 2
    half + k half + k halfUp
termination_by n => n


-- @@ L67-72 verbatim
/-- The partition problem is equivalent to bounding unique coverage. -/
theorem partition_iff_uniqueCoverage {V : Type*} [DecidableEq V]
    (edges : Hypergraph V) (n : ℕ) :
    NoLargePartition edges n ↔
    ∀ P : Hypergraph V, P ⊆ edges → uniqueCoverage edges P ≤ n :=
  Iff.rfl


-- @@ L74-74 verbatim
end HypergraphLowerBound
