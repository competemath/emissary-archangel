/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun
-/
module

public import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.InfinitePlace
public import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing


-- @@ L13-17 verbatim
/-!
# Adele Ring

Material destined for Mathlib.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L23-23 verbatim
open NumberField


-- @@ L25-25 verbatim
instance : MeasurableSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (MeasurableSpace (_ × _))


-- @@ L27-27 verbatim
instance : BorelSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (BorelSpace (_ × _))
