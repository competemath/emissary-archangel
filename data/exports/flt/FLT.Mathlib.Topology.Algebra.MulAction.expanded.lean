/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard
-/
module

public import Mathlib.Topology.Algebra.MulAction


-- @@ L10-14 verbatim
/-!
# Mul Action

Material destined for Mathlib.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
variable {ι A : Type*}

-- @@ L19-19 verbatim
variable {R : ι → Type*} [Π i, Ring (R i)]

-- @@ L20-20 verbatim
variable {M : ι → Type*} [Π i, AddCommGroup (M i)] [Π i, Module (R i) (M i)]

-- @@ L21-21 verbatim
variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (M i)]

-- @@ L22-22 verbatim
variable [∀ i, ContinuousSMul (R i) (M i)]


-- @@ L24-27 verbatim
instance : ContinuousSMul ((i : ι) → R i) ((i : ι) → M i) :=
  ⟨continuous_pi fun i ↦
    (Continuous.smul ((continuous_apply i).comp (Continuous.fst continuous_id'))
      ((continuous_apply i).comp (Continuous.snd continuous_id')))⟩
