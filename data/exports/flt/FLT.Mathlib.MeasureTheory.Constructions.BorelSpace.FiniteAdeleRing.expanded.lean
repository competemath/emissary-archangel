/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun, Kevin Buzzard
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing


-- @@ L11-15 verbatim
/-!
# Finite Adele Ring

Material destined for Mathlib.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L21-21 verbatim
open NumberField


-- @@ L23-23 verbatim
open IsDedekindDomain


-- @@ L25-25 verbatim
noncomputable instance : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _


-- @@ L27-27 verbatim
instance : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
