/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun, Kevin Buzzard
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation


-- @@ L11-15 verbatim
/-!
# Adic Completion

Material destined for Mathlib.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open NumberField


-- @@ L21-21 verbatim
variable (K : Type*) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))


-- @@ L23-23 verbatim
noncomputable instance : MeasurableSpace (v.adicCompletion K) := borel _


-- @@ L25-25 verbatim
instance : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
