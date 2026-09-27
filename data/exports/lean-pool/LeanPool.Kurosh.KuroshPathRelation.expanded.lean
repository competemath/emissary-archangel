/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.KuroshCoverLift


-- @@ L10-16 verbatim
/-!
# Kurosh Path Relation

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Set Function

-- @@ L21-21 verbatim
open CategoryTheory

-- @@ L22-22 verbatim
open scoped Pointwise

-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-26 verbatim
/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshPathRelationDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

-- @@ L27-27 verbatim
universe u v

-- @@ L28-28 verbatim
namespace GraphCoveringTheory.Kurosh


-- @@ L30-39 verbatim
/-- Recover the raw symmetrified Bass-Serre path from a path-category morphism. -/
def catPathToRaw {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)]
    {a b : Quiver.Symmetrify (RawBassSerreVertex G)}
    (p : (CategoryTheory.Paths.of
      (Quiver.Symmetrify (RawBassSerreVertex G))).obj a ⟶
        (CategoryTheory.Paths.of
          (Quiver.Symmetrify (RawBassSerreVertex G))).obj b) :
    @Quiver.Path (Quiver.Symmetrify (RawBassSerreVertex G))
      (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
        (rawBassSerreQuiver G)) a b := p


-- @@ L41-41 verbatim
end GraphCoveringTheory.Kurosh
