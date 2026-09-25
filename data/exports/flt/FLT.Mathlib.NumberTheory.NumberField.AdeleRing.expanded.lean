/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

-- can't upstream until we've imported the below!
public import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing


-- @@ L13-19 verbatim
/-!

# Topological facts about adele rings

This should be enough to deduce that they're Polish.

-/


-- @@ L21-21 verbatim
@[expose] public section

-- @@ L22-22 verbatim
variable {K : Type*} [Field K]


-- @@ L24-24 verbatim
namespace NumberField.AdeleRing


-- @@ L26-27 verbatim
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (x y : AdeleRing R K)


-- @@ L29-29 verbatim
@[simp] lemma add_fst (x y : AdeleRing R K) : (x + y).1 = x.1 + y.1 := rfl

-- @@ L30-30 verbatim
@[simp] lemma add_snd (x y : AdeleRing R K) : (x + y).2 = x.2 + y.2 := rfl


-- @@ L32-32 verbatim
@[simp] lemma mul_fst (x y : AdeleRing R K) : (x * y).1 = x.1 * y.1 := rfl

-- @@ L33-33 verbatim
@[simp] lemma mul_snd (x y : AdeleRing R K) : (x * y).2 = x.2 * y.2 := rfl


-- @@ L35-35 verbatim
@[simp] lemma zero_fst : (0 : AdeleRing R K).1 = 0 := rfl

-- @@ L36-36 verbatim
@[simp] lemma zero_snd : (0 : AdeleRing R K).2 = 0 := rfl


-- @@ L38-38 verbatim
@[simp] lemma one_fst : (1 : AdeleRing R K).1 = 1 := rfl

-- @@ L39-39 verbatim
@[simp] lemma one_snd : (1 : AdeleRing R K).2 = 1 := rfl


-- @@ L41-41 verbatim
variable [NumberField K]


-- @@ L43-43 verbatim
section topology_stuff


-- @@ L45-47 verbatim
open IsDedekindDomain.HeightOneSpectrum in
instance locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| LocallyCompactSpace (_ × _)


-- @@ L49-50 verbatim
instance : T2Space (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| T2Space (_ × _)


-- @@ L52-53 verbatim
instance : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (_ × _)


-- @@ L55-55 verbatim
end topology_stuff


-- @@ L57-57 verbatim
end NumberField.AdeleRing
