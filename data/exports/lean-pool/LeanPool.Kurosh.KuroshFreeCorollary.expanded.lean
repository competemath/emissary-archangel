/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.KuroshFreePart


-- @@ L10-16 verbatim
/-!
# Kurosh Free Corollary

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


-- @@ L25-27 verbatim
/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshFreeCorollaryDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α


-- @@ L29-29 verbatim
universe u v w


-- @@ L31-31 verbatim
namespace GraphCoveringTheory.Kurosh


-- @@ L33-33 verbatim
open Monoid.CoprodI


-- @@ L35-54 verbatim
/-- Kill every stabilizer component and retain the free component. -/
noncomputable def treeKuroshComponentToFreePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (q : TreeKuroshComponentIndex G H) :
    TreeKuroshComponent G H q →* KuroshFreePart G H := by
  cases q using Sum.casesOn with
  | inl a =>
      change ULift.{max (u + 1) (v + 1)}
          (treeVertexStabilizer G H a) →* KuroshFreePart G H
      exact
        { toFun := fun _ => 1
          map_one' := by rfl
          map_mul' := by intro x y; simp }
  | inr q =>
      change ULift.{max (u + 1) (v + 1)}
          (KuroshFreePart G H) →* KuroshFreePart G H
      exact
        { toFun := fun x => x.down
          map_one' := by rfl
          map_mul' := by intro x y; rfl }


-- @@ L56-61 verbatim
/-- The projection of the tree Kurosh product onto its free component. -/
noncomputable def treeKuroshProductToFreePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    TreeKuroshProduct G H →* KuroshFreePart G H := by
  change FreeProduct (TreeKuroshComponent G H) →* KuroshFreePart G H
  exact Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H)


-- @@ L63-76 verbatim
theorem treeKuroshProductToFreePart_vertex {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (x : treeVertexStabilizer G H a) :
    treeKuroshProductToFreePart G H
      (treeKuroshVertexInclusion G H a x) = 1 := by
  change treeKuroshProductToFreePart G H
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)) = 1
  change (Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inl a) from ULift.up x)) = 1
  rw [Monoid.CoprodI.lift_of]
  rfl


-- @@ L78-90 verbatim
@[simp] theorem treeKuroshProductToFreePart_free {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H) :
    treeKuroshProductToFreePart G H
      (treeKuroshFreeInclusion G H x) = x := by
  change treeKuroshProductToFreePart G H
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)) = x
  change (Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
      (Monoid.CoprodI.of
        (show TreeKuroshComponent G H (Sum.inr PUnit.unit) from ULift.up x)) = x
  rw [Monoid.CoprodI.lift_of]
  rfl


-- @@ L92-134 verbatim
theorem treeKuroshProductToH_factor_through_freePart {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    treeKuroshProductToH G H =
      (kuroshFreePartHom G H).comp (treeKuroshProductToFreePart G H) := by
  apply Monoid.CoprodI.ext_hom
  intro q
  cases q using Sum.casesOn with
  | inl a =>
      apply MonoidHom.ext
      intro x
      have hx : x.down = (1 : treeVertexStabilizer G H a) := by
        let := htriv a
        exact Subsingleton.elim _ _
      change treeKuroshComponentHom G H (Sum.inl a) x =
        kuroshFreePartHom G H
          (treeKuroshProductToFreePart G H
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inl a) from x)))
      change x.down.1 =
        kuroshFreePartHom G H
          ((Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inl a) from x)))
      rw [Monoid.CoprodI.lift_of]
      change x.down.1 = 1
      exact congrArg Subtype.val hx
  | inr q =>
      apply MonoidHom.ext
      intro x
      change treeKuroshComponentHom G H (Sum.inr q) x =
        kuroshFreePartHom G H
          (treeKuroshProductToFreePart G H
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inr q) from x)))
      change kuroshFreePartHom G H x.down =
        kuroshFreePartHom G H
          ((Monoid.CoprodI.lift (treeKuroshComponentToFreePart G H))
            (Monoid.CoprodI.of
              (show TreeKuroshComponent G H (Sum.inr q) from x)))
      rw [Monoid.CoprodI.lift_of]
      rfl


-- @@ L136-149 verbatim
theorem kuroshFreePartHom_surjective_of_trivial_stabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    Function.Surjective (kuroshFreePartHom G H) := by
  intro h
  obtain ⟨p, hp⟩ :=
    Internal.treeKuroshProductToH_surjective_for_kernel G H h
  refine ⟨treeKuroshProductToFreePart G H p, ?_⟩
  have hfactor := congrArg
    (fun f : @TreeKuroshProduct.{u, v, 0} ι G _ H →* H => f p)
    (@treeKuroshProductToH_factor_through_freePart.{u, v, 0}
      ι G _ H htriv)
  simpa using hfactor.symm.trans hp


-- @@ L151-159 verbatim
/-- When all vertex stabilizers are trivial, free-part evaluation is an isomorphism onto `H`. -/
noncomputable def kuroshFreePartEquivOfTrivialStabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    KuroshFreePart G H ≃* H :=
  MulEquiv.ofBijective (kuroshFreePartHom G H)
    ⟨kuroshFreePartHom_injective G H,
      kuroshFreePartHom_surjective_of_trivial_stabilizers G H htriv⟩


-- @@ L161-167 verbatim
theorem kurosh_subgroup_is_free_of_trivial_stabilizers {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (htriv : ∀ a : RawBassSerreOrbitVertex G H,
      Subsingleton (treeVertexStabilizer G H a)) :
    IsFreeGroup H := by
  exact IsFreeGroup.ofMulEquiv
    (kuroshFreePartEquivOfTrivialStabilizers G H htriv)


-- @@ L169-169 verbatim
end GraphCoveringTheory.Kurosh
