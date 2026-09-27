/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Mathlib.Topology.Path


-- @@ L10-12 verbatim
/-!
# LeanPool.DirectedTopologyLean4.DirectedSpace
-/


-- @@ L14-20 verbatim
@[expose] public section

/-
  # Definition of directed spaces
  This file defines the directed space, an extension of a topological space where
  some of its paths are considered directed paths.
-/


-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
open scoped unitInterval


-- @@ L26-42 verbatim
/-- Definition of a directed topological space.

Dipaths are closed under:
* Constant paths,
* Concatenation of paths,
* Monotone reparametrization of paths. -/
class DirectedSpace (α : Type u) extends TopologicalSpace α where
  /-- Predicate selecting the directed paths in the space. -/
  IsDipath : ∀ {x y : α}, Path x y → Prop
  /-- Every constant path is directed. -/
  isDipath_constant : ∀ (x : α), IsDipath (Path.refl x)
  /-- The concatenation of two directed paths is directed. -/
  isDipath_concat : ∀ {x y z : α} {γ₁ : Path x y}
      {γ₂ : Path y z}, IsDipath γ₁ → IsDipath γ₂ → IsDipath (Path.trans γ₁ γ₂)
  /-- Monotone reparametrization preserves directedness. -/
  isDipath_reparam : ∀ {x y : α} {γ : Path x y} {t₀ t₁ : I}
      {f : Path t₀ t₁}, Monotone f → IsDipath γ → IsDipath (f.map (γ.continuous_toFun))


-- @@ L44-44 verbatim
section DirectedSpace


-- @@ L46-47 verbatim
variable {α : Type u} {x y z : α} [DirectedSpace α] {γ : Path x y} {γ' : Path y z} {t₀ t₁ : I}
  {f : Path t₀ t₁}


-- @@ L49-51 verbatim
/-- A path in a directed space is a dipath if it satisfies the directed-space predicate. -/
def IsDipath : (Path x y) → Prop :=
  DirectedSpace.IsDipath


-- @@ L53-55 verbatim
/-- The constant path at any point of a directed space is directed. -/
lemma isDipath_constant (x : α) : IsDipath (Path.refl x) :=
  DirectedSpace.isDipath_constant _


-- @@ L57-59 verbatim
/-- The concatenation of two dipaths is again a dipath. -/
lemma isDipath_concat (hγ : IsDipath γ) (hγ' : IsDipath γ') : IsDipath (γ.trans γ') :=
  DirectedSpace.isDipath_concat hγ hγ'


-- @@ L61-64 verbatim
/-- Reparametrizing a dipath along a monotone path yields another dipath. -/
lemma isDipath_reparam (hfmono : Monotone f) (hγ : IsDipath γ) :
    IsDipath (f.map γ.continuous_toFun) :=
  DirectedSpace.isDipath_reparam hfmono hγ


-- @@ L66-70 verbatim
/-- Casting a path that is directed into another path gives another directed path -/
lemma isDipath_cast {x y x' y' : α} (γ : Path x y) (hx : x' = x) (hy : y' = y) (hγ : IsDipath γ) :
  IsDipath (γ.cast hx hy) := by
    subst_vars
    simp_all


-- @@ L72-72 verbatim
end DirectedSpace
