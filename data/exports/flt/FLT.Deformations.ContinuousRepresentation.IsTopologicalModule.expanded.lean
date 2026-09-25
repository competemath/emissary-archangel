/-
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Pi
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict


-- @@ L13-19 verbatim
/-!
# Topological modules

The typeclass `IsTopologicalModule R M` packages a topology on `M` for which
both scalar multiplication and addition are continuous, together with basic
constructions (subobjects, products) and inducing-map properties.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open Topology


-- @@ L25-26 verbatim
variable (R : Type*) [Ring R] [TopologicalSpace R]
  (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]


-- @@ L28-32 verbatim
/--
`IsTopologicalModule R M` states that the topology in `M` makes scalar multiplication and addition
into continuous maps.
-/
class IsTopologicalModule extends ContinuousSMul R M, ContinuousAdd M


-- @@ L34-34 verbatim
variable [IsTopologicalModule R M]


-- @@ L36-43 verbatim
protected theorem Topology.IsInducing.topologicalModule {F : Type*}
    (R : Type*) [Ring R] [TopologicalSpace R]
    {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalModule R M]
    {H : Type*} [AddCommGroup H] [Module R H] [TopologicalSpace H]
    [FunLike F H M] [LinearMapClass F R H M] (f : F) (hf : IsInducing ⇑f) :
    IsTopologicalModule R H where
  continuous_smul := (hf.continuousSMul (f := id) continuous_id (by simp)).continuous_smul
  continuous_add := (hf.continuousAdd ..).continuous_add


-- @@ L45-46 verbatim
instance Submodule.instIsTopologicalModuleSubtypeMem (S : Submodule R M) : IsTopologicalModule R S
    := IsInducing.subtypeVal.topologicalModule R S.subtypeL


-- @@ L48-53 verbatim
instance Pi.instTopologicalModule {ι : Type*} (R : Type*) [Ring R] [TopologicalSpace R]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsTopologicalModule R (M i)] :
    IsTopologicalModule R ((i : ι) → M i) where
  continuous_smul := by apply continuous_smul
  continuous_add := by apply continuous_add
