/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Lattice.Nat


-- @@ L11-15 verbatim
/-!
# Definitions for the main theorem

The complete non-Mathlib vocabulary used in the public statement.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace SaxlCounterexamples.MainTheorems


-- @@ L23-34 verbatim
/-- A finite permutation group: a finite group acting faithfully on a finite
set. -/
structure FinitePermutationGroup where
  /-- The acting group. -/
  G : Type
  /-- The type of points on which the group acts. -/
  Point : Type
  [group : Group G]
  [action : MulAction G Point]
  [finiteGroup : Finite G]
  [finitePoint : Finite Point]
  [faithful : FaithfulSMul G Point]


-- @@ L36-38 verbatim
attribute [instance] FinitePermutationGroup.group
  FinitePermutationGroup.action FinitePermutationGroup.finiteGroup
  FinitePermutationGroup.finitePoint FinitePermutationGroup.faithful


-- @@ L40-40 verbatim
namespace FinitePermutationGroup


-- @@ L42-44 verbatim
/-- A set of points is a base if only the identity fixes every point in it. -/
def IsBase (P : FinitePermutationGroup) (B : Set P.Point) : Prop :=
  ∀ g : P.G, (∀ x ∈ B, g • x = x) → g = 1


-- @@ L46-50 verbatim
/-- The least size of a base. An injective map from `Fin n` represents an
`n`-element base; existential quantification makes its enumeration irrelevant. -/
noncomputable def baseSize (P : FinitePermutationGroup) : Nat :=
  sInf {n : Nat | ∃ b : Fin n → P.Point,
    Function.Injective b ∧ P.IsBase (Set.range b)}


-- @@ L52-67 verbatim
/-- The Saxl graph of a finite permutation group. Two distinct points are
adjacent exactly when they lie together in a base of minimum size. Thus this
is the ordinary Saxl graph at base size two and the generalized Saxl graph at
larger base sizes. -/
noncomputable def saxlGraph (P : FinitePermutationGroup) :
    SimpleGraph P.Point where
  Adj x y :=
    x ≠ y ∧ ∃ b : Fin P.baseSize → P.Point,
      Function.Injective b ∧ P.IsBase (Set.range b) ∧
        x ∈ Set.range b ∧ y ∈ Set.range b
  symm := ⟨by
    rintro x y ⟨hxy, b, hinj, hbase, hx, hy⟩
    exact ⟨hxy.symm, b, hinj, hbase, hy, hx⟩⟩
  loopless := ⟨by
    rintro x ⟨hxx, -⟩
    exact hxx rfl⟩


-- @@ L69-69 verbatim
end FinitePermutationGroup


-- @@ L71-71 verbatim
end SaxlCounterexamples.MainTheorems
