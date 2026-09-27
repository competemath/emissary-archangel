/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 138-157 and 252-285.
Modifications: extracted into a separate namespace and changed source-module
imports and namespace qualifications. See the upstream PORT_MAP.md.
-/
module

public import LeanPool.ConnesRigidity.Core


-- @@ L17-19 verbatim
/-!
The core transfer component of the Connes rigidity formalization.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Connes

-- @@ L24-24 verbatim
namespace OpenAIPort


-- @@ L26-26 verbatim
universe u v


-- @@ L28-32 verbatim
/-- Public OpenAI reindexing computation. Paper: §3. -/
@[simp] theorem l2Reindex_apply {α : Type u} {β : Type v} (e : α ≃ β)
    (f : GroupL2 α) (j : β) :
    l2Reindex e f j = f (e.symm j) :=
  rfl


-- @@ L34-38 verbatim
/-- Public OpenAI reindexing symmetry. Paper: §3. -/
@[simp] theorem l2Reindex_symm {α : Type u} {β : Type v} (e : α ≃ β) :
    (l2Reindex e).symm = l2Reindex e.symm := by
  ext f i
  rfl


-- @@ L40-44 verbatim
/-- Public OpenAI left-regular computation. Paper: §3. -/
@[simp] theorem leftRegularUnitary_apply {G : Type u} [Group G]
    (g : G) (f : GroupL2 G) (h : G) :
    (leftRegularUnitary g : GroupL2 G →L[ℂ] GroupL2 G) f h = f (g⁻¹ * h) := by
  rfl


-- @@ L46-59 verbatim
/-- Public OpenAI transfer of almost-invariant vectors. Paper: §4. -/
theorem hasAlmostInvariantUnitVectors_comp
    {G H : Type u} {K : Type v} [Group G] [Group H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation H K)
    (f : G →* H)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    UnitaryRepresentation.HasAlmostInvariantUnitVectors (π.comp f) := by
  classical
  intro S ε hε
  obtain ⟨ξ, hξ, hclose⟩ := hπ (S.image f) ε hε
  refine ⟨ξ, hξ, ?_⟩
  intro g hg
  exact hclose (f g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)


-- @@ L61-74 verbatim
/-- Public OpenAI property-(T) quotient transfer. Paper: §4. -/
theorem hasKazhdanPropertyT_of_surjective
    (G H : CountableDiscreteGroup.{u})
    (f : G →* H) (hf : Function.Surjective f)
    (hG : HasKazhdanPropertyT.{u, v} G) :
    HasKazhdanPropertyT.{u, v} H := by
  intro K _ _ _ π hπ
  obtain ⟨ξ, hξ, hinv⟩ :=
    hG K inferInstance inferInstance inferInstance (π.comp f)
      (hasAlmostInvariantUnitVectors_comp π f hπ)
  refine ⟨ξ, hξ, ?_⟩
  intro h
  obtain ⟨g, rfl⟩ := hf h
  exact hinv g


-- @@ L76-82 verbatim
/-- Public OpenAI property-(T) transport across a group equivalence. Paper: §4. -/
theorem hasKazhdanPropertyT_iff_of_mulEquiv
    (G H : CountableDiscreteGroup.{u}) (e : G ≃* H) :
    HasKazhdanPropertyT.{u, v} G ↔ HasKazhdanPropertyT.{u, v} H := by
  constructor
  · exact hasKazhdanPropertyT_of_surjective G H e.toMonoidHom e.surjective
  · exact hasKazhdanPropertyT_of_surjective H G e.symm.toMonoidHom e.symm.surjective


-- @@ L84-84 verbatim
end OpenAIPort

-- @@ L85-85 verbatim
end Connes
