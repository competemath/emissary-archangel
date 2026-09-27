/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD

-- @@ L13-23 verbatim
/-!
# Definition of Graph Action

In this file we define group actions on simple graphs.

Let `G` be a group and `X` be a simple graph. Then an action of `G` on `X` is defined as an action
on the vertices of `X` that preserves the adjacency relation.

We show that a graph action induces an action on the edges.

-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open Module



-- @@ L30-30 verbatim
variable {V : Type*}


-- @@ L32-32 verbatim
open SimpleGraph

-- @@ L33-33 verbatim
section «Action»


-- @@ L35-37 verbatim
/-- A group `G` acts as a graph action on `X`, if the adjacency relation is preserved. -/
class GraphAction (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) where
  smul_adj_smul (g : G) (x y : V) (h : X.Adj x y) : X.Adj (g • x) (g • y)


-- @@ L39-39 verbatim
variable (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) [GraphAction G X]


-- @@ L41-41 verbatim
namespace GraphAction


-- @@ L43-48 verbatim
@[simp]
lemma adj_iff (g : G) (x y : V) : X.Adj (g • x) (g • y) ↔ X.Adj x y := by
  constructor
  · intro h
    simpa using smul_adj_smul g⁻¹ (g • x) (g • y) h
  · exact smul_adj_smul g x y


-- @@ L50-51 verbatim
instance : SMul G (Sym2 V) where
  smul g := Sym2.map (fun x ↦ g • x)


-- @@ L53-55 verbatim
@[simp]
lemma smul_sym2 (g : G) (x y : V) : g • s(x, y) = s(g • x, g • y) :=
  rfl


-- @@ L57-65 verbatim
instance : MulAction G (Sym2 V) where
  one_smul x := by
    refine Sym2.inductionOn x ?_
    intro x y
    simp
  mul_smul g h x := by
    refine Sym2.inductionOn x ?_
    intro x y
    simp [mul_smul]


-- @@ L67-74 verbatim
instance : SMul G X.edgeSet where
  smul g e := ⟨g • e.val, by
    have := e.property
    revert this
    generalize e.val = t
    refine Sym2.inductionOn t ?_
    intro x y
    simp⟩


-- @@ L76-77 verbatim
@[simp]
lemma smul_edgeSet_coe (g : G) (e : X.edgeSet) : (g • e).val = g • e.val := rfl


-- @@ L79-87 verbatim
/-- The action on edges induced by a graph action.
-/
instance : MulAction G X.edgeSet where
  one_smul x := by
    ext : 1
    simp
  mul_smul g x y := by
    ext : 1
    simp [mul_smul]


-- @@ L89-89 verbatim
variable {G} {X}


-- @@ L91-96 verbatim
lemma smul_mem_smul_of (g : G) (e : Sym2 V) (x : V) (h : x ∈ e) :
    g • x ∈ g • e := by
  revert h
  refine Sym2.inductionOn e ?_
  intro a b h
  simpa using h


-- @@ L98-104 verbatim
@[simp]
lemma smul_mem_smul_iff (g : G) (e : Sym2 V) (x : V) :
    g • x ∈ g • e ↔ x ∈ e := by
  constructor
  · intro h
    simpa using smul_mem_smul_of g⁻¹ (g • e) (g • x) h
  · exact smul_mem_smul_of g e x


-- @@ L106-111 verbatim
instance [MulAction.IsPretransitive G (Sym2 V)] : MulAction.IsPretransitive G X.edgeSet where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) x.val y.val
    use g
    ext : 1
    simpa


-- @@ L113-113 verbatim
end GraphAction


-- @@ L115-115 verbatim
end «Action»
