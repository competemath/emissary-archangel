/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun, Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import FLT.Mathlib.Topology.MetricSpace.ProperSpace.InfinitePlace


-- @@ L11-15 verbatim
/-!
# Infinite Place

Material destined for Mathlib.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open NumberField


-- @@ L21-21 verbatim
open InfinitePlace.Completion


-- @@ L23-23 verbatim
variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)


-- @@ L25-25 verbatim
noncomputable instance : MeasurableSpace (v.Completion) := borel _


-- @@ L27-27 verbatim
instance : BorelSpace (v.Completion) := ⟨rfl⟩


-- @@ L29-30 verbatim
noncomputable instance : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ _, _))


-- @@ L32-32 verbatim
instance : BorelSpace (InfiniteAdeleRing K) := inferInstanceAs (BorelSpace (∀ _, _))
