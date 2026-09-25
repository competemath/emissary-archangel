/-
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras, Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic


-- @@ L12-16 verbatim
/-!
# Defs

Material destined for Mathlib.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]


-- @@ L22-22 verbatim
open IsLocalRing


-- @@ L24-24 verbatim
instance IsLocalRing.quot : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective


-- @@ L26-27 verbatim
instance IsLocalHom.quotient_mk : IsLocalHom (algebraMap R (R ⧸ I)) :=
  .of_surjective _ Ideal.Quotient.mk_surjective
