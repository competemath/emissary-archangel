/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import FLT.Mathlib.RepresentationTheory.Continuous.Basic


-- @@ L11-15 verbatim
/-!
# The internal hom of topological representations

Material destined for `Mathlib.RepresentationTheory.Continuous.TopRep`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
universe u v


-- @@ L21-21 verbatim
open ContinuousLinearMap.CompactOpen


-- @@ L23-23 verbatim
namespace TopRep


-- @@ L25-25 verbatim
variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]


-- @@ L27-29 verbatim
/-- The internal hom of two topological representations: the topological representation on the
space of continuous linear maps `A →L[k] B`, with `G` acting by conjugation. -/
abbrev iHom (A B : TopRep k G) : TopRep k G := TopRep.of (ContRepresentation.linHom A.ρ B.ρ)


-- @@ L31-31 verbatim
end TopRep
