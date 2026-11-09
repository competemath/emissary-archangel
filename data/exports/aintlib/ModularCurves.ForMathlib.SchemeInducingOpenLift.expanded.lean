/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `SchemeInducingOpenLift.lean` in
Vilin97/Clawristotle.
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion


-- @@ L11-16 verbatim
/-!
# Lifting opens along inducing scheme morphisms

Every open in the source of an inducing scheme morphism is the inverse
image of a chosen target open.
-/


-- @@ L18-18 verbatim
open AlgebraicGeometry TopologicalSpace


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
namespace AlgebraicGeometry.Scheme.Hom


-- @@ L26-31 verbatim
/-- A chosen target open whose inverse image is the given source open. -/
noncomputable def targetOpenOfIsInducing
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (U : X.Opens) : Y.Opens :=
  ⟨Classical.choose (hf.isOpen_iff.mp U.2),
    (Classical.choose_spec (hf.isOpen_iff.mp U.2)).1⟩


-- @@ L33-40 verbatim
/-- The chosen target open pulls back to the given source open. -/
@[simp]
theorem preimage_targetOpenOfIsInducing
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (U : X.Opens) :
    f ⁻¹ᵁ f.targetOpenOfIsInducing hf U = U := by
  apply Opens.ext
  exact (Classical.choose_spec (hf.isOpen_iff.mp U.2)).2


-- @@ L42-50 verbatim
/-- Membership in the lifted open is preserved by the inducing map. -/
theorem mem_targetOpenOfIsInducing
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (U : X.Opens)
    (x : X) (hx : x ∈ U) :
    f x ∈ f.targetOpenOfIsInducing hf U := by
  have hx' : x ∈ f ⁻¹ᵁ f.targetOpenOfIsInducing hf U := by
    simpa using hx
  exact hx'


-- @@ L52-56 verbatim
/-- A chosen target open for a source open under a closed immersion. -/
noncomputable def closedImmersionTargetOpen
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (U : X.Opens) : Y.Opens :=
  i.targetOpenOfIsInducing i.isClosedEmbedding.isInducing U


-- @@ L58-65 verbatim
/-- A closed-immersion target open has the prescribed inverse image. -/
@[simp]
theorem preimage_closedImmersionTargetOpen
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (U : X.Opens) :
    i ⁻¹ᵁ i.closedImmersionTargetOpen U = U :=
  i.preimage_targetOpenOfIsInducing
    i.isClosedEmbedding.isInducing U


-- @@ L67-67 verbatim
end AlgebraicGeometry.Scheme.Hom
