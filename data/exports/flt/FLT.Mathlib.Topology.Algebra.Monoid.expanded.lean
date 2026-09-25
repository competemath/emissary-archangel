/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard
-/
module

public import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Monoid


-- @@ L11-15 verbatim
/-!
# Monoid

Material destined for Mathlib.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-22 verbatim
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [ContinuousMul G]
-- TODO: `ContinuousMulConst` would be enough but it doesn't exist, and `ContinuousConstSMul Gᵐᵒᵖ G`
-- should work but doesn't


-- @@ L24-24 verbatim
section induced


-- @@ L26-26 verbatim
variable {R : Type*} [τR : TopologicalSpace R]

-- @@ L27-27 verbatim
variable {A : Type*} [SMul R A]

-- @@ L28-28 verbatim
variable {S : Type*} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)

-- @@ L29-29 verbatim
variable {B : Type*} [SMul S B]


-- @@ L31-33 verbatim
open Topology

-- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B

-- @@ L34-37 verbatim
@[to_additive]
theorem induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A)
    (hf : Continuous f) : @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert IsInducing.continuousSMul (IsInducing.induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)


-- @@ L39-43 verbatim
@[to_additive]
theorem induced_continuous_mul [CommMonoid A] [τA : TopologicalSpace A] [ContinuousMul A]
    [CommMonoid B] (h : B →* A) :
    @ContinuousMul B (TopologicalSpace.induced h τA) _ := by
  convert (IsInducing.induced h).continuousMul h


-- @@ L45-45 verbatim
end induced
