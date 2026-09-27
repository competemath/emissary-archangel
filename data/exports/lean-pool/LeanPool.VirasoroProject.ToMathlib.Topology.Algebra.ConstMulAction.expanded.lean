/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction


-- @@ L10-12 verbatim
/-!
# LeanPool.VirasoroProject.ToMathlib.Topology.Algebra.ConstMulAction
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-19 verbatim
lemma continuousConstSMul_of_discreteTopology (𝕜 X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] [SMul 𝕜 X] :
    ContinuousConstSMul 𝕜 X :=
  ⟨fun c ↦ by continuity⟩
