/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps
public import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Tactic.Measurability.Init


-- @@ L12-16 verbatim
/-!
# LeanPool.WhiteheadTheorem.Defs

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Defs`.
-/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
open CategoryTheory

-- @@ L22-22 verbatim
open scoped ContinuousMap


-- @@ L24-24 verbatim
universe u


-- @@ L26-30 verbatim
/-- `IsWeakHomotopyEquiv` -/
def IsWeakHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  Nonempty X ∧
    ∀ n x, Function.Bijective (HomotopyGroup.inducedMap n x f)


-- @@ L32-39 verbatim
lemma isIso_inducedPointedHom_of_isWeakHomotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (hf : IsWeakHomotopyEquiv f) :
    ∀ n x, IsIso (HomotopyGroup.inducedPointedHom n x f) := by
  intro n x
  apply (Pointed.isIso_iff_bijective _).mpr
  have := hf.right n x
  rwa [HomotopyGroup.inducedMap] at this


-- @@ L41-44 verbatim
/-- `IsHomotopyEquiv` -/
def IsHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  ∃ equiv : X ≃ₕ Y, equiv.toFun = f
