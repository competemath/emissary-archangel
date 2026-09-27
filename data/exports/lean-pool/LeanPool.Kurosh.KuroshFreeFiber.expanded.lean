/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.KuroshRawPathValue


-- @@ L10-16 verbatim
/-!
# Kurosh Free Fiber

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


-- @@ L25-25 verbatim
universe u v


-- @@ L27-27 verbatim
namespace GraphCoveringTheory.Kurosh


-- @@ L29-44 verbatim
theorem Internal.coverFreeGroupoidPathHom_eq_quotient_map {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) :
    coverFreeGroupoidPathHom G H p =
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H))).map p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      simp only [coverFreeGroupoidPathHom]
      rw [ih]
      cases e using Sum.casesOn <;> rfl


-- @@ L46-62 verbatim
theorem Internal.coverFreePath_exists {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (z : @Quiver.Hom (Quiver.FreeGroupoid (RawBassSerreOrbitVertex G H)) _
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj a)
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj b)) :
    ∃ p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) a b,
      coverFreeGroupoidPathHom G H p = z := by
  obtain ⟨p, hp⟩ :=
    (CategoryTheory.Quotient.full_functor
      (@Quiver.FreeGroupoid.redStep (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))).map_surjective z
  refine ⟨p, ?_⟩
  rw [Internal.coverFreeGroupoidPathHom_eq_quotient_map]
  exact hp


-- @@ L64-64 verbatim
end GraphCoveringTheory.Kurosh
