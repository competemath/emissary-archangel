/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.SubgroupGroupObject
import ModularCurves.GroupScheme.StableCharts
import ModularCurves.GroupScheme.PatchKunneth
import ModularCurves.ForMathlib.SchemeAppLE
import ModularCurves.ForMathlib.BaseChangeAlongCompat


-- @@ L12-29 verbatim
/-!
# The Hopf algebra of a finite locally free subgroup over an affine patch

Construction support for `[CHARTER-HOPF]` Wave C, leaf `[HG-C1c-1]`
(`.mathlib-quality/decomposition-hopf-crux.md`): with the group-object structure of `G`
in hand (`SubgroupGroupObject.lean`), the section ring `A = Γ(G, G|_V)` over an affine
base patch `V` carries the dual structure — counit from the unit section, antipode from
inversion, comultiplication from the multiplication through the affine Künneth
identification (`PatchKunneth.lean`).

This file builds the *maps*; their coalgebra/bialgebra/Hopf axioms are the `Γ`-duals of
the group-object laws already proven (`mulOver_assoc`, `unitOver_mulOver_left`,
`invOver_mulOver_left`).

## Main definitions
* `groupPatchCounit` — `ε : A ⟶ R`, restriction along the unit section.
* `groupPatchAntipode` — `S : A ⟶ A`, restriction along inversion.
-/


-- @@ L31-31 verbatim
set_option backward.defeqAttrib.useBackward true

-- @@ L32-32 verbatim
set_option backward.isDefEq.respectTransparency false


-- @@ L34-34 verbatim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

-- @@ L35-35 verbatim
open scoped TensorProduct


-- @@ L37-38 verbatim
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory


-- @@ L40-40 verbatim
universe u


-- @@ L42-42 verbatim
namespace ModularCurves


-- @@ L44-44 verbatim
namespace EllipticCurve


-- @@ L46-46 verbatim
namespace FiniteLocallyFreeSubgroup


-- @@ L48-48 verbatim
variable {S : Scheme.{u}} {E : EllipticCurve S} (G : FiniteLocallyFreeSubgroup E)


-- @@ L50-50 verbatim
namespace AffineChartPatch


-- @@ L52-52 verbatim
variable (P : G.AffineChartPatch)


-- @@ L54-58 verbatim
/-- The base patch lies in the unit section's preimage of the group patch: the unit
section is a section of the structure morphism. -/
theorem le_preimage_groupOpen_unitHom : P.V ≤ G.unitHom ⁻¹ᵁ P.groupOpen := by
  rw [groupOpen, ← Scheme.Hom.comp_preimage, G.unitHom_π]
  exact le_of_eq (Scheme.Hom.id_preimage P.V).symm


-- @@ L60-62 verbatim
/-- The group patch is inversion-stable: `inv⁻¹(G|_V) = G|_V`. -/
theorem le_preimage_groupOpen_invHom : P.groupOpen ≤ G.invHom ⁻¹ᵁ P.groupOpen := by
  rw [groupOpen, ← Scheme.Hom.comp_preimage, G.invHom_π]


-- @@ L64-66 verbatim
/-- **The counit** `ε : A ⟶ R`: restriction of sections along the unit section. -/
noncomputable def groupPatchCounit : P.groupRing ⟶ P.baseRing :=
  G.unitHom.appLE P.groupOpen P.V P.le_preimage_groupOpen_unitHom


-- @@ L68-70 verbatim
/-- **The antipode** `S : A ⟶ A`: restriction of sections along inversion. -/
noncomputable def groupPatchAntipode : P.groupRing ⟶ P.groupRing :=
  G.invHom.appLE P.groupOpen P.groupOpen P.le_preimage_groupOpen_invHom


-- @@ L72-72 verbatim
/-! ### The comultiplication -/


-- @@ L74-76 verbatim
/-- The `V`-level square `G|_V ×_V G|_V`. -/
noncomputable abbrev groupSquare : Scheme.{u} :=
  pullback (G.π.resLE P.V P.groupOpen le_rfl) (G.π.resLE P.V P.groupOpen le_rfl)


-- @@ L78-82 verbatim
/-- The `V`-level square maps into the `S`-level square. -/
noncomputable def groupSquareToSquare :
    P.groupSquare ⟶ (Over.mk G.π ⊗ Over.mk G.π).left :=
  pullback.map _ _ G.π G.π P.groupOpen.ι P.groupOpen.ι P.V.ι
    (Scheme.Hom.resLE_comp_ι _ _) (Scheme.Hom.resLE_comp_ι _ _)


-- @@ L84-89 verbatim
@[reassoc (attr := simp)]
theorem groupSquareToSquare_snd :
    P.groupSquareToSquare ≫ (snd (Over.mk G.π) (Over.mk G.π)).left
      = pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
          (G.π.resLE P.V P.groupOpen le_rfl) ≫ P.groupOpen.ι :=
  pullback.lift_snd _ _ _


-- @@ L91-96 verbatim
@[reassoc (attr := simp)]
theorem groupSquareToSquare_fst :
    P.groupSquareToSquare ≫ (fst (Over.mk G.π) (Over.mk G.π)).left
      = pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
          (G.π.resLE P.V P.groupOpen le_rfl) ≫ P.groupOpen.ι :=
  pullback.lift_fst _ _ _


-- @@ L98-100 verbatim
/-- Multiplication, restricted to the `V`-level square. -/
noncomputable def squareMul : P.groupSquare ⟶ G.G :=
  P.groupSquareToSquare ≫ G.mulHom


-- @@ L102-112 verbatim
/-- **The restricted multiplication is a morphism over the base patch**: its composite
with the structure morphism is the square's projection to `V`. -/
@[reassoc]
theorem squareMul_π : P.squareMul ≫ G.π
    = pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      ≫ G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι := by
  rw [squareMul, Category.assoc, G.mulHom_π]
  rw [show ((Over.mk G.π ⊗ Over.mk G.π).hom)
      = (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.π from rfl]
  rw [P.groupSquareToSquare_fst_assoc, Scheme.Hom.resLE_comp_ι]


-- @@ L114-121 verbatim
/-- The restricted multiplication lands in the group patch. -/
theorem top_le_preimage_groupOpen_squareMul :
    (⊤ : P.groupSquare.Opens) ≤ P.squareMul ⁻¹ᵁ P.groupOpen := by
  have hπ := P.squareMul_π
  rw [groupOpen, ← Scheme.Hom.comp_preimage, hπ]
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Scheme.Opens.ι_preimage_self]
  exact le_top


-- @@ L123-131 verbatim
/-- **The comultiplication** `Δ : A ⟶ A ⊗[R] A`: sections restricted along the group
multiplication, transported along the affine Künneth identification of the `V`-level
square. -/
noncomputable def groupPatchComul :
    P.groupRing ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) :=
  P.squareMul.appLE P.groupOpen ⊤ P.top_le_preimage_groupOpen_squareMul
    ≫ (patchKunneth G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen
        rfl rfl).inv.appTop
    ≫ (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.groupRing))).hom


-- @@ L133-136 verbatim
/-! ### `R`-linearity of the structure maps

Each is the `Γ`-dual of the corresponding "is a morphism over `S`" fact, through
`Scheme.Hom.appLE_comp_appLE`. -/


-- @@ L138-144 verbatim
/-- **The counit is `R`-linear**: `ε ∘ (algebraMap R A) = 𝟙 R`, the `Γ`-dual of
`unitHom ≫ π = 𝟙 S`. -/
theorem algebraMap_comp_groupPatchCounit :
    G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupPatchCounit = 𝟙 P.baseRing := by
  rw [groupPatchCounit, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom G.unitHom_π P.V P.V]
  exact appLE_id _


-- @@ L146-151 verbatim
/-- **The antipode is `R`-linear**, the `Γ`-dual of `invHom ≫ π = π`. -/
theorem algebraMap_comp_groupPatchAntipode :
    G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupPatchAntipode
      = G.π.appLE P.V P.groupOpen le_rfl := by
  rw [groupPatchAntipode, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom G.invHom_π P.V P.groupOpen]


-- @@ L153-159 verbatim
/-- The comultiplication, expressed through the generic `Γ`-transport. -/
theorem groupPatchComul_eq :
    P.groupPatchComul
      = P.squareMul.appLE P.groupOpen ⊤ P.top_le_preimage_groupOpen_squareMul
        ≫ patchKunnethΓ G.π G.π P.hV P.isAffineOpen_groupOpen
            P.isAffineOpen_groupOpen rfl rfl :=
  rfl


-- @@ L161-216 verbatim
/-- **The comultiplication is `R`-linear**: `Δ ∘ algebraMap = algebraMap`, the `Γ`-dual of
`squareMul ≫ π = fst ≫ (structure map to V)`. -/
theorem algebraMap_comp_groupPatchComul :
    G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupPatchComul
      = CommRingCat.ofHom
          (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.groupRing)) := by
  have halg : CommRingCat.ofHom (algebraMap P.baseRing P.groupRing)
      = G.π.appLE P.V P.groupOpen le_rfl := rfl
  -- the target factors through the left inclusion
  rw [show CommRingCat.ofHom
        (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.groupRing))
      = G.π.appLE P.V P.groupOpen le_rfl
        ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)) from by
    rw [← halg, ← CommRingCat.ofHom_comp]
    rfl]
  -- the left inclusion is the transported first projection
  rw [← topIso_inv_fst_appTop_patchKunnethΓ G.π G.π P.hV P.isAffineOpen_groupOpen
    P.isAffineOpen_groupOpen rfl rfl]
  rw [groupPatchComul_eq, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  -- both sides restrict `π` along the two routes around the square
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom P.squareMul_π P.V ⊤]
  rw [show (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
          (G.π.resLE P.V P.groupOpen le_rfl)
        ≫ G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι).appLE P.V ⊤ _
      = G.π.appLE P.V P.groupOpen le_rfl
        ≫ P.groupOpen.topIso.inv
        ≫ (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
            (G.π.resLE P.V P.groupOpen le_rfl)).appTop from ?_]
  · exact (Category.assoc _ _ _).symm
  -- the appLE of the composite, unwound
  rw [appLE_congr_hom (Category.assoc
      (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl))
      (G.π.resLE P.V P.groupOpen le_rfl) P.V.ι).symm P.V ⊤,
    ← Scheme.Hom.appLE_comp_appLE
      (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl) ≫ G.π.resLE P.V P.groupOpen le_rfl)
      P.V.ι P.V ⊤ ⊤ P.V.ι_preimage_self.ge le_top,
    ι_appLE_top]
  rw [show (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      ≫ G.π.resLE P.V P.groupOpen le_rfl).appLE ⊤ ⊤ le_top
      = (G.π.resLE P.V P.groupOpen le_rfl).appTop
        ≫ (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
            (G.π.resLE P.V P.groupOpen le_rfl)).appTop from
    (Scheme.Hom.appLE_comp_appLE
      (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl))
      (G.π.resLE P.V P.groupOpen le_rfl) ⊤ ⊤ ⊤ le_top le_top).symm.trans
      (by rw [appLE_top_top, appLE_top_top])]
  rw [show (G.π.resLE P.V P.groupOpen le_rfl).appTop
      = P.V.topIso.hom ≫ G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupOpen.topIso.inv from
    Scheme.Hom.resLE_app_top (f := G.π) (U := P.V) (V := P.groupOpen) le_rfl]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]


-- @@ L218-218 verbatim
/-! ### Algebra-map packaging -/


-- @@ L220-228 verbatim
/-- The counit as an `R`-algebra map. -/
noncomputable def counitAlg : P.groupRing →ₐ[P.baseRing] P.baseRing where
  toRingHom := P.groupPatchCounit.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRing ⟶ P.baseRing => m.hom r)
      P.algebraMap_comp_groupPatchCounit
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at h
    exact h


-- @@ L230-237 verbatim
/-- The antipode as an `R`-algebra map. -/
noncomputable def antipodeAlg : P.groupRing →ₐ[P.baseRing] P.groupRing where
  toRingHom := P.groupPatchAntipode.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRing ⟶ P.groupRing => m.hom r)
      P.algebraMap_comp_groupPatchAntipode
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h


-- @@ L239-248 verbatim
/-- The comultiplication as an `R`-algebra map. -/
noncomputable def comulAlg :
    P.groupRing →ₐ[P.baseRing] (P.groupRing ⊗[P.baseRing] P.groupRing) where
  toRingHom := P.groupPatchComul.hom
  commutes' := fun r => by
    have h := congrArg
      (fun m : P.baseRing ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing)
        => m.hom r) P.algebraMap_comp_groupPatchComul
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h


-- @@ L250-250 verbatim
/-! ### The counit laws, scheme-side -/


-- @@ L252-254 verbatim
/-- The unit section, restricted to the patch. -/
noncomputable def unitSection : P.V.toScheme ⟶ P.groupOpen.toScheme :=
  G.unitHom.resLE P.groupOpen P.V P.le_preimage_groupOpen_unitHom


-- @@ L256-263 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- The restricted unit section is a section of the restricted structure map. -/
@[reassoc (attr := simp)]
theorem unitSection_comp_groupToBase :
    P.unitSection ≫ G.π.resLE P.V P.groupOpen le_rfl = 𝟙 P.V.toScheme := by
  rw [unitSection, Scheme.Hom.resLE_comp_resLE,
    appLE_congr_hom_resLE G.unitHom_π P.V P.V, Scheme.Hom.resLE_id,
    Scheme.homOfLE_rfl]


-- @@ L265-269 verbatim
/-- The unit section, composed into `G`, is the zero section over the patch. -/
@[reassoc]
theorem unitSection_comp_ι :
    P.unitSection ≫ P.groupOpen.ι = P.V.ι ≫ G.unitHom :=
  Scheme.Hom.resLE_comp_ι _ _


-- @@ L271-276 verbatim
/-- The section `⟨e ∘ structure, 𝟙⟩ : G|_V ⟶ G|_V ×_V G|_V` of the left counit law. -/
noncomputable def leftUnitSection : P.groupOpen.toScheme ⟶ P.groupSquare :=
  pullback.lift (G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection)
    (𝟙 P.groupOpen.toScheme)
    (by rw [Category.assoc, P.unitSection_comp_groupToBase, Category.comp_id,
      Category.id_comp])


-- @@ L278-283 verbatim
@[reassoc (attr := simp)]
theorem leftUnitSection_fst :
    P.leftUnitSection ≫ pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection :=
  pullback.lift_fst _ _ _


-- @@ L285-290 verbatim
@[reassoc (attr := simp)]
theorem leftUnitSection_snd :
    P.leftUnitSection ≫ pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      = 𝟙 P.groupOpen.toScheme :=
  pullback.lift_snd _ _ _


-- @@ L292-332 verbatim
/-- **The counit law, scheme side**: acting by the unit section on the left is the
identity — `⟨e ∘ structure, 𝟙⟩ ≫ μ = 𝟙` (as maps into `G`). Proved by `ι`-cancellation and
point-algebra: the first component restricts to the zero point. -/
theorem leftUnitSection_comp_squareMul :
    P.leftUnitSection ≫ P.squareMul = P.groupOpen.ι := by
  rw [← cancel_mono G.ι, squareMul]
  set k := P.leftUnitSection ≫ P.groupSquareToSquare with hk
  rw [show (P.leftUnitSection ≫ P.groupSquareToSquare ≫ G.mulHom) ≫ G.ι
      = k ≫ (G.mulHom ≫ G.ι) from by rw [hk]; simp only [Category.assoc]]
  rw [G.mulHom_ι]
  -- restrict the point sum along `k`
  have hsum : k ≫ ((G.sqFstPoint + G.sqSndPoint : E.Point _) : _ ⟶ E.E)
      = ((EllipticCurve.Point.restrict E k G.sqFstPoint +
            EllipticCurve.Point.restrict E k G.sqSndPoint : E.Point _) : _ ⟶ E.E) := by
    rw [← EllipticCurve.Point.restrict_add]
    rfl
  rw [hsum]
  -- the first restricted point is zero
  have hk1 : k ≫ (fst (Over.mk G.π) (Over.mk G.π)).left
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection ≫ P.groupOpen.ι := by
    rw [hk, Category.assoc, P.groupSquareToSquare_fst]
    exact leftUnitSection_fst_assoc G P P.groupOpen.ι
  have hk2 : k ≫ (snd (Over.mk G.π) (Over.mk G.π)).left = P.groupOpen.ι := by
    rw [hk, Category.assoc, P.groupSquareToSquare_snd]
    exact leftUnitSection_snd_assoc G P P.groupOpen.ι
  have hfst : EllipticCurve.Point.restrict E k G.sqFstPoint = 0 := by
    refine Subtype.ext ?_
    show k ≫ ((fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι) = _
    rw [E.point_zero_val,
      show ((Over.mk G.π ⊗ Over.mk G.π).hom)
        = (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.π from rfl,
      ← Category.assoc k, ← Category.assoc k, hk1]
    rw [P.unitSection_comp_ι]
    show ((G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι ≫ G.unitHom : _ ⟶ G.G) ≫ G.ι)
      = ((G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι ≫ G.unitHom : _ ⟶ G.G) ≫ G.π)
        ≫ E.zero
    simp only [Category.assoc, G.unitHom_ι, G.unitHom_π, Category.id_comp]
  rw [hfst, zero_add]
  -- the second restricted point is the inclusion
  show k ≫ ((snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι) = _
  rw [← Category.assoc k, hk2]


-- @@ L334-334 verbatim
/-! ### The counit law, `Γ`-side -/


-- @@ L336-341 verbatim
/-- `appTop` of the restricted unit section. -/
theorem unitSection_appTop :
    P.unitSection.appTop
      = P.groupOpen.topIso.hom ≫ P.groupPatchCounit ≫ P.V.topIso.inv :=
  Scheme.Hom.resLE_app_top (f := G.unitHom) (U := P.groupOpen) (V := P.V)
    P.le_preimage_groupOpen_unitHom


-- @@ L343-347 verbatim
/-- `appTop` of the restricted structure map. -/
theorem groupToBase_appTop :
    (G.π.resLE P.V P.groupOpen le_rfl).appTop
      = P.V.topIso.hom ≫ G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupOpen.topIso.inv :=
  Scheme.Hom.resLE_app_top (f := G.π) (U := P.V) (V := P.groupOpen) le_rfl


-- @@ L349-352 verbatim
/-- The Künneth transport for the group square. -/
noncomputable abbrev squareΓ :
    Γ(P.groupSquare, ⊤) ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) :=
  patchKunnethΓ G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl


-- @@ L354-357 verbatim
/-- The `Γ`-dual of the left unit section. -/
noncomputable def counitLiftΓ :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) ⟶ P.groupRing :=
  inv P.squareΓ ≫ P.leftUnitSection.appTop ≫ P.groupOpen.topIso.hom


-- @@ L359-371 verbatim
set_option backward.isDefEq.respectTransparency.types false in
/-- **The counit law, `Γ`-side, in transported form**: `Δ` followed by the dual of the
left unit section is the identity. -/
theorem groupPatchComul_comp_counitLiftΓ :
    P.groupPatchComul ≫ P.counitLiftΓ = 𝟙 P.groupRing := by
  rw [groupPatchComul_eq, counitLiftΓ, Category.assoc,
    ← Category.assoc P.squareΓ, IsIso.hom_inv_id, Category.id_comp]
  -- the `appLE`-composite of the scheme identity
  rw [show P.leftUnitSection.appTop
      = P.leftUnitSection.appLE ⊤ ⊤ le_top from (appLE_top_top _).symm]
  rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom P.leftUnitSection_comp_squareMul P.groupOpen ⊤,
    ι_appLE_top, Iso.inv_hom_id]


-- @@ L373-394 verbatim
/-- The right inclusion, composed with the dual of the left unit section, is the
identity. -/
theorem includeRight_comp_counitLiftΓ :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ P.counitLiftΓ = 𝟙 P.groupRing := by
  have hleg := topIso_inv_snd_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [counitLiftΓ, ← hleg]
  -- cancel the transport
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  -- the two `appTop`s compose to the scheme identity
  have hcomp : (pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.leftUnitSection.appTop
      = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, P.leftUnitSection_snd,
      AlgebraicGeometry.Scheme.Hom.id_appTop]
  rw [← Category.assoc ((pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp, Category.id_comp,
    Iso.inv_hom_id]
  rfl


-- @@ L396-420 verbatim
/-- The left inclusion, composed with the dual of the left unit section, is the counit
followed by the structure map. -/
theorem includeLeft_comp_counitLiftΓ :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing))
      ≫ P.counitLiftΓ
      = P.groupPatchCounit ≫ G.π.appLE P.V P.groupOpen le_rfl := by
  have hleg := topIso_inv_fst_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [counitLiftΓ, ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  -- the two `appTop`s compose to the dual of `leftUnitSection ≫ fst`
  have hcomp : (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.leftUnitSection.appTop
      = P.unitSection.appTop ≫ (G.π.resLE P.V P.groupOpen le_rfl).appTop := by
    rw [← Scheme.Hom.comp_appTop, P.leftUnitSection_fst, Scheme.Hom.comp_appTop]
  rw [← Category.assoc ((pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp]
  -- unwind the two restricted `appTop`s
  rw [P.unitSection_appTop, P.groupToBase_appTop]
  simp only [Category.assoc]
  rw [← Category.assoc P.V.topIso.inv, Iso.inv_hom_id, Category.id_comp]
  rw [← Category.assoc P.groupOpen.topIso.inv, Iso.inv_hom_id, Category.id_comp]
  rw [Category.comp_id]


-- @@ L422-426 verbatim
/-- The algebraic counit lift `A ⊗[R] A →ₐ[R] A`, `a ⊗ b ↦ ε(a) • b`. -/
noncomputable def counitLift :
    (P.groupRing ⊗[P.baseRing] P.groupRing) →ₐ[P.baseRing] P.groupRing :=
  Algebra.TensorProduct.lift ((Algebra.ofId P.baseRing P.groupRing).comp P.counitAlg)
    (AlgHom.id P.baseRing P.groupRing) (fun _ _ => Commute.all _ _)


-- @@ L428-441 verbatim
/-- **The counit lift is the `Γ`-dual of the left unit section.** -/
theorem counitLift_eq_counitLiftΓ :
    CommRingCat.ofHom P.counitLift.toRingHom = P.counitLiftΓ := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_counitLiftΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLift G P (a ⊗ₜ[P.baseRing] (1 : P.groupRing)) = _
    rw [counitLift, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
    rfl
  · rw [P.includeRight_comp_counitLiftΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLift G P ((1 : P.groupRing) ⊗ₜ[P.baseRing] a) = _
    rw [counitLift, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl


-- @@ L443-452 verbatim
/-- **The left counit law**: `(ε ⊗ id) ∘ Δ = id`, in `AlgHom` form. -/
theorem counitLift_comp_comulAlg :
    P.counitLift.comp P.comulAlg = AlgHom.id P.baseRing P.groupRing := by
  have h := P.groupPatchComul_comp_counitLiftΓ
  rw [← P.counitLift_eq_counitLiftΓ] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRing ⟶ P.groupRing => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    CommRingCat.hom_id, RingHom.id_apply] at h2
  exact h2


-- @@ L454-454 verbatim
/-! ### The right counit law -/


-- @@ L456-461 verbatim
/-- The section `⟨𝟙, e ∘ structure⟩ : G|_V ⟶ G|_V ×_V G|_V`. -/
noncomputable def rightUnitSection : P.groupOpen.toScheme ⟶ P.groupSquare :=
  pullback.lift (𝟙 P.groupOpen.toScheme)
    (G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection)
    (by rw [Category.assoc, P.unitSection_comp_groupToBase, Category.comp_id,
      Category.id_comp])


-- @@ L463-468 verbatim
@[reassoc (attr := simp)]
theorem rightUnitSection_fst :
    P.rightUnitSection ≫ pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      = 𝟙 P.groupOpen.toScheme :=
  pullback.lift_fst _ _ _


-- @@ L470-475 verbatim
@[reassoc (attr := simp)]
theorem rightUnitSection_snd :
    P.rightUnitSection ≫ pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection :=
  pullback.lift_snd _ _ _


-- @@ L477-512 verbatim
/-- **The right counit law, scheme side**. -/
theorem rightUnitSection_comp_squareMul :
    P.rightUnitSection ≫ P.squareMul = P.groupOpen.ι := by
  rw [← cancel_mono G.ι, squareMul]
  set k := P.rightUnitSection ≫ P.groupSquareToSquare with hk
  rw [show (P.rightUnitSection ≫ P.groupSquareToSquare ≫ G.mulHom) ≫ G.ι
      = k ≫ (G.mulHom ≫ G.ι) from by rw [hk]; simp only [Category.assoc]]
  rw [G.mulHom_ι]
  have hsum : k ≫ ((G.sqFstPoint + G.sqSndPoint : E.Point _) : _ ⟶ E.E)
      = ((EllipticCurve.Point.restrict E k G.sqFstPoint
          + EllipticCurve.Point.restrict E k G.sqSndPoint : E.Point _) : _ ⟶ E.E) := by
    rw [← EllipticCurve.Point.restrict_add]
    rfl
  rw [hsum]
  have hk1 : k ≫ (fst (Over.mk G.π) (Over.mk G.π)).left = P.groupOpen.ι := by
    rw [hk, Category.assoc, P.groupSquareToSquare_fst]
    exact rightUnitSection_fst_assoc G P P.groupOpen.ι
  have hk2 : k ≫ (snd (Over.mk G.π) (Over.mk G.π)).left
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.unitSection ≫ P.groupOpen.ι := by
    rw [hk, Category.assoc, P.groupSquareToSquare_snd]
    exact rightUnitSection_snd_assoc G P P.groupOpen.ι
  have hsnd : EllipticCurve.Point.restrict E k G.sqSndPoint = 0 := by
    refine Subtype.ext ?_
    show k ≫ ((snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι) = _
    rw [E.point_zero_val,
      show ((Over.mk G.π ⊗ Over.mk G.π).hom)
        = (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.π from rfl,
      ← Category.assoc k, ← Category.assoc k, hk1, hk2]
    rw [P.unitSection_comp_ι]
    show ((G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.ι ≫ G.unitHom : _ ⟶ G.G) ≫ G.ι)
      = (P.groupOpen.ι ≫ G.π) ≫ E.zero
    rw [← Scheme.Hom.resLE_comp_ι G.π (le_rfl : P.groupOpen ≤ G.π ⁻¹ᵁ P.V)]
    simp only [Category.assoc, G.unitHom_ι]
  rw [hsnd, add_zero]
  show k ≫ ((fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι) = _
  rw [← Category.assoc k, hk1]


-- @@ L514-517 verbatim
/-- The `Γ`-dual of the right unit section. -/
noncomputable def counitLiftΓ' :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) ⟶ P.groupRing :=
  inv P.squareΓ ≫ P.rightUnitSection.appTop ≫ P.groupOpen.topIso.hom


-- @@ L519-528 verbatim
set_option backward.isDefEq.respectTransparency.types false in
theorem groupPatchComul_comp_counitLiftΓ' :
    P.groupPatchComul ≫ P.counitLiftΓ' = 𝟙 P.groupRing := by
  rw [groupPatchComul_eq, counitLiftΓ', Category.assoc,
    ← Category.assoc P.squareΓ, IsIso.hom_inv_id, Category.id_comp]
  rw [show P.rightUnitSection.appTop
      = P.rightUnitSection.appLE ⊤ ⊤ le_top from (appLE_top_top _).symm]
  rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom P.rightUnitSection_comp_squareMul P.groupOpen ⊤,
    ι_appLE_top, Iso.inv_hom_id]


-- @@ L530-547 verbatim
theorem includeLeft_comp_counitLiftΓ' :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing))
      ≫ P.counitLiftΓ' = 𝟙 P.groupRing := by
  have hleg := topIso_inv_fst_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [counitLiftΓ', ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  have hcomp : (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.rightUnitSection.appTop
      = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, P.rightUnitSection_fst,
      AlgebraicGeometry.Scheme.Hom.id_appTop]
  rw [← Category.assoc ((pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp, Category.id_comp,
    Iso.inv_hom_id]
  rfl


-- @@ L549-569 verbatim
theorem includeRight_comp_counitLiftΓ' :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ P.counitLiftΓ'
      = P.groupPatchCounit ≫ G.π.appLE P.V P.groupOpen le_rfl := by
  have hleg := topIso_inv_snd_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [counitLiftΓ', ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  have hcomp : (pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.rightUnitSection.appTop
      = P.unitSection.appTop ≫ (G.π.resLE P.V P.groupOpen le_rfl).appTop := by
    rw [← Scheme.Hom.comp_appTop, P.rightUnitSection_snd, Scheme.Hom.comp_appTop]
  rw [← Category.assoc ((pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp]
  rw [P.unitSection_appTop, P.groupToBase_appTop]
  simp only [Category.assoc]
  rw [← Category.assoc P.V.topIso.inv, Iso.inv_hom_id, Category.id_comp]
  rw [← Category.assoc P.groupOpen.topIso.inv, Iso.inv_hom_id, Category.id_comp]
  rw [Category.comp_id]


-- @@ L571-576 verbatim
/-- The algebraic right counit lift `A ⊗[R] A →ₐ[R] A`, `a ⊗ b ↦ a • ε(b)`. -/
noncomputable def counitLift' :
    (P.groupRing ⊗[P.baseRing] P.groupRing) →ₐ[P.baseRing] P.groupRing :=
  Algebra.TensorProduct.lift (AlgHom.id P.baseRing P.groupRing)
    ((Algebra.ofId P.baseRing P.groupRing).comp P.counitAlg)
    (fun _ _ => Commute.all _ _)


-- @@ L578-590 verbatim
theorem counitLift'_eq_counitLiftΓ' :
    CommRingCat.ofHom P.counitLift'.toRingHom = P.counitLiftΓ' := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_counitLiftΓ']
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLift' G P (a ⊗ₜ[P.baseRing] (1 : P.groupRing)) = _
    rw [counitLift', Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
    rfl
  · rw [P.includeRight_comp_counitLiftΓ']
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLift' G P ((1 : P.groupRing) ⊗ₜ[P.baseRing] a) = _
    rw [counitLift', Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl


-- @@ L592-601 verbatim
/-- **The right counit law**: `(id ⊗ ε) ∘ Δ = id`, in `AlgHom` form. -/
theorem counitLift'_comp_comulAlg :
    P.counitLift'.comp P.comulAlg = AlgHom.id P.baseRing P.groupRing := by
  have h := P.groupPatchComul_comp_counitLiftΓ'
  rw [← P.counitLift'_eq_counitLiftΓ'] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRing ⟶ P.groupRing => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    CommRingCat.hom_id, RingHom.id_apply] at h2
  exact h2


-- @@ L603-607 verbatim
/-! ### Towards coassociativity: the `⊤`-level presentation

We restate the Hopf structure with `R' := Γ(V.toScheme, ⊤)` and `A' := Γ(G|_V, ⊤)`, where
the group structure maps dualise directly (as `appTop`, no `topIso` conjugation). The
opens-level maps are recovered by conjugating with `topIso`. -/


-- @@ L609-610 verbatim
/-- The `⊤`-level base ring `R' = Γ(V.toScheme, ⊤)`. -/
noncomputable abbrev baseRingTop : CommRingCat := Γ(P.V.toScheme, ⊤)


-- @@ L612-613 verbatim
/-- The `⊤`-level group ring `A' = Γ(G|_V.toScheme, ⊤)`. -/
noncomputable abbrev groupRingTop : CommRingCat := Γ(P.groupOpen.toScheme, ⊤)


-- @@ L615-617 verbatim
/-- The structure map of the group patch, in the spelling used by `groupSquare`. -/
noncomputable abbrev groupToBaseRes : P.groupOpen.toScheme ⟶ P.V.toScheme :=
  G.π.resLE P.V P.groupOpen le_rfl


-- @@ L619-621 verbatim
/-- `R'` is `R` transported by `topIso`. -/
noncomputable instance : Algebra P.baseRingTop P.groupRingTop :=
  P.groupToBaseRes.appTop.hom.toAlgebra


-- @@ L623-623 verbatim
instance : IsAffine P.V.toScheme := P.hV

-- @@ L624-624 verbatim
instance : IsAffine P.groupOpen.toScheme := P.isAffineOpen_groupOpen


-- @@ L626-626 verbatim
/-! #### The `⊤`-level structure maps -/


-- @@ L628-630 verbatim
/-- The `⊤`-level counit `ε' : A' ⟶ R'`. -/
noncomputable def counitTop : P.groupRingTop ⟶ P.baseRingTop :=
  P.unitSection.appTop


-- @@ L632-638 verbatim
/-- The group square is affine (it is the `Spec` of `A ⊗[R] A`). -/
theorem isAffine_groupSquare : IsAffine P.groupSquare := by
  haveI : IsIso (patchKunneth G.π G.π P.hV P.isAffineOpen_groupOpen
      P.isAffineOpen_groupOpen (e₁ := le_rfl) (e₂ := le_rfl) rfl rfl).hom :=
    inferInstance
  exact IsAffine.of_isIso (patchKunneth G.π G.π P.hV P.isAffineOpen_groupOpen
    P.isAffineOpen_groupOpen (e₁ := le_rfl) (e₂ := le_rfl) rfl rfl).hom


-- @@ L640-644 verbatim
/-- The restricted multiplication, corestricted to the group patch:
`G|_V ×_V G|_V ⟶ G|_V`. -/
noncomputable def squareMulRes : P.groupSquare ⟶ P.groupOpen.toScheme :=
  P.groupSquare.topIso.inv
    ≫ P.squareMul.resLE P.groupOpen ⊤ P.top_le_preimage_groupOpen_squareMul


-- @@ L646-651 verbatim
/-- The corestricted multiplication recovers `squareMul` after including the patch. -/
@[reassoc]
theorem squareMulRes_comp_ι : P.squareMulRes ≫ P.groupOpen.ι = P.squareMul := by
  rw [squareMulRes, Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [show (⊤ : P.groupSquare.Opens).ι = P.groupSquare.topIso.hom from rfl,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]


-- @@ L653-664 verbatim
/-- The corestricted multiplication over the base: `squareMulRes ≫ groupToBaseRes` is the
square's projection to the base, i.e. `fst ≫ groupToBaseRes`. -/
@[reassoc]
theorem squareMulRes_comp_groupToBaseRes :
    P.squareMulRes ≫ P.groupToBaseRes
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes := by
  rw [← cancel_mono P.V.ι, Category.assoc, Category.assoc]
  rw [show P.groupToBaseRes ≫ P.V.ι = P.groupOpen.ι ≫ G.π from
    Scheme.Hom.resLE_comp_ι _ _]
  rw [← Category.assoc P.squareMulRes, P.squareMulRes_comp_ι, P.squareMul_π]
  rw [show P.groupToBaseRes ≫ P.V.ι = P.groupOpen.ι ≫ G.π from
    Scheme.Hom.resLE_comp_ι _ _]


-- @@ L666-668 verbatim
/-- The structure map of the group square to the base patch. -/
noncomputable def squareToBase : P.groupSquare ⟶ P.V.toScheme :=
  pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes


-- @@ L670-672 verbatim
/-- `Γ(square)` is an `R'`-algebra via the structure map to the base. -/
noncomputable instance : Algebra P.baseRingTop (Γ(P.groupSquare, ⊤)) :=
  P.squareToBase.appTop.hom.toAlgebra


-- @@ L674-674 verbatim
instance : IsAffine P.groupSquare := P.isAffine_groupSquare


-- @@ L676-679 verbatim
/-- The affine Künneth transport for the group square, `⊤`-level. -/
noncomputable abbrev squareΓTop :
    Γ(P.groupSquare, ⊤) ⟶ CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) :=
  affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl


-- @@ L681-684 verbatim
/-- **The `⊤`-level comultiplication** `Δ' : A' ⟶ A' ⊗[R'] A'`. -/
noncomputable def comulTop :
    P.groupRingTop ⟶ CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) :=
  P.squareMulRes.appTop ≫ P.squareΓTop


-- @@ L686-691 verbatim
/-- The left unit section is a section of the corestricted multiplication. -/
@[reassoc]
theorem leftUnitSection_comp_squareMulRes :
    P.leftUnitSection ≫ P.squareMulRes = 𝟙 P.groupOpen.toScheme := by
  rw [← cancel_mono P.groupOpen.ι, Category.assoc, P.squareMulRes_comp_ι,
    P.leftUnitSection_comp_squareMul, Category.id_comp]


-- @@ L693-698 verbatim
/-- The right unit section is a section of the corestricted multiplication. -/
@[reassoc]
theorem rightUnitSection_comp_squareMulRes :
    P.rightUnitSection ≫ P.squareMulRes = 𝟙 P.groupOpen.toScheme := by
  rw [← cancel_mono P.groupOpen.ι, Category.assoc, P.squareMulRes_comp_ι,
    P.rightUnitSection_comp_squareMul, Category.id_comp]


-- @@ L700-700 verbatim
/-! #### The `⊤`-level counit laws -/


-- @@ L702-705 verbatim
/-- The `⊤`-level counit lift, dual of the left unit section. -/
noncomputable def counitLiftTop :
    CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) ⟶ P.groupRingTop :=
  inv P.squareΓTop ≫ P.leftUnitSection.appTop


-- @@ L707-711 verbatim
theorem comulTop_comp_counitLiftTop :
    P.comulTop ≫ P.counitLiftTop = 𝟙 P.groupRingTop := by
  rw [comulTop, counitLiftTop, Category.assoc, ← Category.assoc P.squareΓTop,
    IsIso.hom_inv_id, Category.id_comp, ← Scheme.Hom.comp_appTop,
    P.leftUnitSection_comp_squareMulRes, AlgebraicGeometry.Scheme.Hom.id_appTop]


-- @@ L713-725 verbatim
/-- **Left inclusion, `⊤`-level**: dualises to `ε'` followed by the base inclusion. -/
theorem includeLeft_comp_counitLiftTop :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop))
      ≫ P.counitLiftTop
      = P.counitTop ≫ P.groupToBaseRes.appTop := by
  have hleg := fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
  have hinv : affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
      ≫ inv P.squareΓTop = 𝟙 _ :=
    IsIso.hom_inv_id _
  rw [counitLiftTop, ← Category.assoc, ← hleg, Category.assoc, Category.assoc,
    reassoc_of% hinv, ← Scheme.Hom.comp_appTop,
    P.leftUnitSection_fst, Scheme.Hom.comp_appTop, counitTop]


-- @@ L727-738 verbatim
/-- **Right inclusion, `⊤`-level**: dualises to the identity. -/
theorem includeRight_comp_counitLiftTop :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom
      ≫ P.counitLiftTop = 𝟙 P.groupRingTop := by
  have hleg := snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
  have hinv : affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
      ≫ inv P.squareΓTop = 𝟙 _ :=
    IsIso.hom_inv_id _
  rw [counitLiftTop, ← Category.assoc, ← hleg, Category.assoc, Category.assoc,
    reassoc_of% hinv, ← Scheme.Hom.comp_appTop,
    P.leftUnitSection_snd, AlgebraicGeometry.Scheme.Hom.id_appTop]


-- @@ L740-740 verbatim
/-! #### `⊤`-level algebra-map packaging -/


-- @@ L742-744 verbatim
theorem algebraMapTop_eq :
    CommRingCat.ofHom (algebraMap P.baseRingTop P.groupRingTop)
      = P.groupToBaseRes.appTop := rfl


-- @@ L746-756 verbatim
/-- **`Δ'` is `R'`-linear.** -/
theorem algebraMap_comp_comulTop :
    P.groupToBaseRes.appTop ≫ P.comulTop
      = CommRingCat.ofHom
          (algebraMap P.baseRingTop (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)) := by
  rw [comulTop, ← Category.assoc]
  rw [show P.groupToBaseRes.appTop ≫ P.squareMulRes.appTop
      = (P.squareMulRes ≫ P.groupToBaseRes).appTop from
    (Scheme.Hom.comp_appTop _ _).symm]
  rw [P.squareMulRes_comp_groupToBaseRes, Scheme.Hom.comp_appTop, Category.assoc]
  exact base_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl


-- @@ L758-763 verbatim
/-- **`ε'` is `R'`-linear** (in fact the base-restriction of `𝟙 R'`): the unit section is
a section of the structure map, so `ε' ∘ algebraMap = 𝟙`. -/
theorem algebraMap_comp_counitTop :
    P.groupToBaseRes.appTop ≫ P.counitTop = 𝟙 P.baseRingTop := by
  rw [counitTop, ← Scheme.Hom.comp_appTop, P.unitSection_comp_groupToBase,
    AlgebraicGeometry.Scheme.Hom.id_appTop]


-- @@ L765-773 verbatim
/-- The `⊤`-level counit as an `R'`-algebra map. -/
noncomputable def counitAlgTop : P.groupRingTop →ₐ[P.baseRingTop] P.baseRingTop where
  toRingHom := P.counitTop.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRingTop ⟶ P.baseRingTop => m.hom r)
      (P.algebraMapTop_eq ▸ P.algebraMap_comp_counitTop)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply, CommRingCat.hom_ofHom] at h
    exact h


-- @@ L775-785 verbatim
/-- The `⊤`-level comultiplication as an `R'`-algebra map. -/
noncomputable def comulAlgTop :
    P.groupRingTop →ₐ[P.baseRingTop]
      (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) where
  toRingHom := P.comulTop.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRingTop ⟶ CommRingCat.of
      (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) => m.hom r)
      (P.algebraMapTop_eq ▸ P.algebraMap_comp_comulTop)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h


-- @@ L787-787 verbatim
/-! #### The `⊤`-level antipode -/


-- @@ L789-791 verbatim
/-- The corestricted inversion `G|_V ⟶ G|_V` (the group patch is inversion-stable). -/
noncomputable def invRes : P.groupOpen.toScheme ⟶ P.groupOpen.toScheme :=
  G.invHom.resLE P.groupOpen P.groupOpen P.le_preimage_groupOpen_invHom


-- @@ L793-797 verbatim
/-- The corestricted inversion is a morphism over the base patch. -/
@[reassoc]
theorem invRes_comp_groupToBaseRes : P.invRes ≫ P.groupToBaseRes = P.groupToBaseRes := by
  rw [invRes, groupToBaseRes]
  simp only [Scheme.Hom.resLE_comp_resLE, G.invHom_π]


-- @@ L799-802 verbatim
/-- The corestricted inversion recovers `invHom` after including the patch. -/
@[reassoc]
theorem invRes_comp_ι : P.invRes ≫ P.groupOpen.ι = P.groupOpen.ι ≫ G.invHom := by
  rw [invRes, Scheme.Hom.resLE_comp_ι]


-- @@ L804-806 verbatim
/-- The `⊤`-level antipode `S' : A' ⟶ A'`. -/
noncomputable def antipodeTop : P.groupRingTop ⟶ P.groupRingTop :=
  P.invRes.appTop


-- @@ L808-811 verbatim
theorem algebraMap_comp_antipodeTop :
    P.groupToBaseRes.appTop ≫ P.antipodeTop
      = CommRingCat.ofHom (algebraMap P.baseRingTop P.groupRingTop) := by
  rw [antipodeTop, ← Scheme.Hom.comp_appTop, P.invRes_comp_groupToBaseRes, algebraMapTop_eq]


-- @@ L813-820 verbatim
/-- The `⊤`-level antipode as an `R'`-algebra map. -/
noncomputable def antipodeAlgTop : P.groupRingTop →ₐ[P.baseRingTop] P.groupRingTop where
  toRingHom := P.antipodeTop.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRingTop ⟶ P.groupRingTop => m.hom r)
      (P.algebraMapTop_eq ▸ P.algebraMap_comp_antipodeTop)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h


-- @@ L822-825 verbatim
/-- The antipode pairing `⟨S, 𝟙⟩ : G|_V ⟶ G|_V ×_V G|_V`, `g ↦ (g⁻¹, g)`. -/
noncomputable def antipodePair : P.groupOpen.toScheme ⟶ P.groupSquare :=
  pullback.lift P.invRes (𝟙 P.groupOpen.toScheme)
    (by rw [Category.id_comp, P.invRes_comp_groupToBaseRes])


-- @@ L827-830 verbatim
@[reassoc (attr := simp)]
theorem antipodePair_fst :
    P.antipodePair ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes = P.invRes :=
  pullback.lift_fst _ _ _


-- @@ L832-835 verbatim
@[reassoc (attr := simp)]
theorem antipodePair_snd :
    P.antipodePair ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes = 𝟙 _ :=
  pullback.lift_snd _ _ _


-- @@ L837-840 verbatim
/-- The `⊤`-level dual of the antipode pairing: `A' ⊗ A' ⟶ A'`. -/
noncomputable def antipodeLiftTop :
    CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) ⟶ P.groupRingTop :=
  inv P.squareΓTop ≫ P.antipodePair.appTop


-- @@ L842-851 verbatim
/-- **Left inclusion, `⊤`-level**: dualises the `fst` leg to the antipode. -/
theorem includeLeft_comp_antipodeLiftTop :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop))
      ≫ P.antipodeLiftTop = P.antipodeTop := by
  have hleg := fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
  have hinv : affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
      ≫ inv P.squareΓTop = 𝟙 _ := IsIso.hom_inv_id _
  rw [antipodeLiftTop, ← Category.assoc, ← hleg, Category.assoc, Category.assoc,
    reassoc_of% hinv, ← Scheme.Hom.comp_appTop, antipodePair_fst, antipodeTop]


-- @@ L853-863 verbatim
/-- **Right inclusion, `⊤`-level**: dualises the `snd` leg to the identity. -/
theorem includeRight_comp_antipodeLiftTop :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom
      ≫ P.antipodeLiftTop = 𝟙 P.groupRingTop := by
  have hleg := snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
  have hinv : affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
      ≫ inv P.squareΓTop = 𝟙 _ := IsIso.hom_inv_id _
  rw [antipodeLiftTop, ← Category.assoc, ← hleg, Category.assoc, Category.assoc,
    reassoc_of% hinv, ← Scheme.Hom.comp_appTop, antipodePair_snd,
    AlgebraicGeometry.Scheme.Hom.id_appTop]


-- @@ L865-869 verbatim
/-- The algebraic antipode lift `A' ⊗[R'] A' →ₐ[R'] A'`, `a ⊗ b ↦ S'(a) · b`. -/
noncomputable def antipodeLiftAlgTop :
    (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) →ₐ[P.baseRingTop] P.groupRingTop :=
  Algebra.TensorProduct.lift P.antipodeAlgTop (AlgHom.id P.baseRingTop P.groupRingTop)
    (fun _ _ => Commute.all _ _)


-- @@ L871-884 verbatim
theorem antipodeLiftAlgTop_eq :
    CommRingCat.ofHom P.antipodeLiftAlgTop.toRingHom = P.antipodeLiftTop := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_antipodeLiftTop]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show antipodeLiftAlgTop G P (a ⊗ₜ[P.baseRingTop] (1 : P.groupRingTop)) = _
    rw [antipodeLiftAlgTop, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
    rfl
  · rw [P.includeRight_comp_antipodeLiftTop]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show antipodeLiftAlgTop G P ((1 : P.groupRingTop) ⊗ₜ[P.baseRingTop] a) = _
    rw [antipodeLiftAlgTop, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul,
      AlgHom.coe_id, id_eq]
    rfl


-- @@ L886-889 verbatim
/-- Base-congruence for points: transport across equal base morphisms preserves the
underlying scheme morphism. -/
theorem point_base_congr {T : Scheme.{u}} {g g' : T ⟶ S} (h : g = g')
    (pt : E.Point g) : (h ▸ pt : E.Point g').1 = pt.1 := by subst h; rfl


-- @@ L891-894 verbatim
/-- Base transport is additive. -/
theorem point_base_congr_add {T : Scheme.{u}} {g g' : T ⟶ S} (h : g = g')
    (pt q : E.Point g) : (h ▸ (pt + q) : E.Point g') = (h ▸ pt) + (h ▸ q) := by
  subst h; rfl


-- @@ L896-900 verbatim
/-- A transported restriction is pinned down by its underlying scheme morphism. -/
theorem point_restrictT_eq {T T' : Scheme.{u}} {g : T ⟶ S} {k : T' ⟶ T} {g' : T' ⟶ S}
    (h : k ≫ g = g') (pt : E.Point g) (q : E.Point g') (hpq : k ≫ pt.1 = q.1) :
    (h ▸ EllipticCurve.Point.restrict E k pt : E.Point g') = q :=
  Subtype.ext ((point_base_congr h (EllipticCurve.Point.restrict E k pt)).trans hpq)


-- @@ L902-908 verbatim
/-- Transported restriction of a sum splits as the sum of the identified points. -/
theorem point_restrictT_add_eq {T T' : Scheme.{u}} {g : T ⟶ S} {k : T' ⟶ T} {g' : T' ⟶ S}
    (h : k ≫ g = g') (a b : E.Point g) (pt q : E.Point g')
    (hp : k ≫ a.1 = pt.1) (hq : k ≫ b.1 = q.1) :
    (h ▸ EllipticCurve.Point.restrict E k (a + b) : E.Point g') = pt + q := by
  rw [EllipticCurve.Point.restrict_add, point_base_congr_add,
    point_restrictT_eq h a pt hp, point_restrictT_eq h b q hq]


-- @@ L910-967 verbatim
/-- **The left inverse law, chart form** `⟨S, 𝟙⟩ ≫ μ = e ∘ !`: the antipode pairing
followed by multiplication is the constant unit map `g ↦ g⁻¹·g = e`, i.e. the base
projection followed by the unit section. Dualises `invOver_mulOver_left`; proven by the
same `ι`-cancellation as `assocScheme_leftMulSchemeL`, the identity being `neg_add_cancel`
in `E.Point (groupOpen.ι ≫ G.π)`. -/
theorem antipodePair_comp_squareMulRes :
    P.antipodePair ≫ P.squareMulRes = P.groupToBaseRes ≫ P.unitSection := by
  rw [← cancel_mono (P.groupOpen.ι ≫ G.ι)]
  have hb : P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have hgsts : P.groupSquareToSquare ≫ (Over.mk G.π ⊗ Over.mk G.π).hom
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes ≫ P.V.ι := by
    rw [← G.mulHom_π, ← Category.assoc]; exact P.squareMul_π
  have hfstι : P.groupSquareToSquare ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_fst]; exact Category.assoc _ _ _
  have hsndι : P.groupSquareToSquare ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_snd]; exact Category.assoc _ _ _
  have hbaseP : (P.antipodePair ≫ P.groupSquareToSquare) ≫ (Over.mk G.π ⊗ Over.mk G.π).hom
      = P.groupOpen.ι ≫ G.π := by
    simp only [Category.assoc, hgsts, P.antipodePair_fst_assoc,
      P.invRes_comp_groupToBaseRes_assoc]
    rw [← hb]
  have Esplit : (hbaseP ▸ EllipticCurve.Point.restrict E
        (P.antipodePair ≫ P.groupSquareToSquare) (G.sqFstPoint + G.sqSndPoint)
        : E.Point (P.groupOpen.ι ≫ G.π))
      = EllipticCurve.Point.restrict E P.groupOpen.ι (-G.universalPoint)
        + EllipticCurve.Point.restrict E P.groupOpen.ι G.universalPoint :=
    point_restrictT_add_eq hbaseP G.sqFstPoint G.sqSndPoint
      (EllipticCurve.Point.restrict E P.groupOpen.ι (-G.universalPoint))
      (EllipticCurve.Point.restrict E P.groupOpen.ι G.universalPoint)
      (by
        show (P.antipodePair ≫ P.groupSquareToSquare)
            ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
          = P.groupOpen.ι ≫ (-G.universalPoint : E.Point G.π).1
        rw [← G.invHom_ι]
        simp only [Category.assoc, hfstι, P.antipodePair_fst_assoc, P.invRes_comp_ι_assoc])
      (by
        show (P.antipodePair ≫ P.groupSquareToSquare)
            ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
          = P.groupOpen.ι ≫ G.universalPoint.1
        simp only [Category.assoc, hsndι, P.antipodePair_snd_assoc]
        rfl)
  have hsum : EllipticCurve.Point.restrict E P.groupOpen.ι (-G.universalPoint)
        + EllipticCurve.Point.restrict E P.groupOpen.ι G.universalPoint = 0 := by
    rw [← EllipticCurve.Point.restrict_add, neg_add_cancel, EllipticCurve.Point.restrict_zero]
  have hLHS : (P.antipodePair ≫ P.squareMulRes) ≫ P.groupOpen.ι ≫ G.ι
      = (EllipticCurve.Point.restrict E P.groupOpen.ι (-G.universalPoint)
        + EllipticCurve.Point.restrict E P.groupOpen.ι G.universalPoint).1 := by
    rw [← Esplit, point_base_congr]
    simp only [EllipticCurve.Point.restrict, Category.assoc, P.squareMulRes_comp_ι_assoc,
      squareMul, G.mulHom_ι]
  have hRHS : (P.groupToBaseRes ≫ P.unitSection) ≫ P.groupOpen.ι ≫ G.ι
      = (0 : E.Point (P.groupOpen.ι ≫ G.π)).1 := by
    rw [E.point_zero_val, hb]
    simp only [Category.assoc, P.unitSection_comp_ι_assoc, G.unitHom_ι]
  rw [hLHS, hRHS, hsum]


-- @@ L969-974 verbatim
/-- **The antipode-multiplication law, `⊤`-level `CommRingCat` form.** -/
theorem comulTop_comp_antipodeLiftTop :
    P.comulTop ≫ P.antipodeLiftTop = P.counitTop ≫ P.groupToBaseRes.appTop := by
  rw [comulTop, antipodeLiftTop, Category.assoc, ← Category.assoc P.squareΓTop,
    IsIso.hom_inv_id, Category.id_comp, ← Scheme.Hom.comp_appTop,
    P.antipodePair_comp_squareMulRes, Scheme.Hom.comp_appTop, counitTop]


-- @@ L976-986 verbatim
/-- **The left antipode law, `AlgHom` form**: `(S' ⊗ id) ∘ Δ' = ofId ∘ ε'` (the convolution
inverse condition), in the shape `HopfAlgebra.ofAlgHom` consumes. -/
theorem antipodeLiftAlgTop_comp_comulAlgTop :
    P.antipodeLiftAlgTop.comp P.comulAlgTop
      = (Algebra.ofId P.baseRingTop P.groupRingTop).comp P.counitAlgTop := by
  have h := P.comulTop_comp_antipodeLiftTop
  rw [← P.antipodeLiftAlgTop_eq] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRingTop ⟶ P.groupRingTop => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2


-- @@ L988-991 verbatim
/-- The right antipode pairing `⟨𝟙, S⟩ : G|_V ⟶ G|_V ×_V G|_V`, `g ↦ (g, g⁻¹)`. -/
noncomputable def antipodePairR : P.groupOpen.toScheme ⟶ P.groupSquare :=
  pullback.lift (𝟙 P.groupOpen.toScheme) P.invRes
    (by rw [Category.id_comp, P.invRes_comp_groupToBaseRes])


-- @@ L993-996 verbatim
@[reassoc (attr := simp)]
theorem antipodePairR_fst :
    P.antipodePairR ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes = 𝟙 _ :=
  pullback.lift_fst _ _ _


-- @@ L998-1001 verbatim
@[reassoc (attr := simp)]
theorem antipodePairR_snd :
    P.antipodePairR ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes = P.invRes :=
  pullback.lift_snd _ _ _


-- @@ L1003-1006 verbatim
/-- The `⊤`-level dual of the right antipode pairing. -/
noncomputable def antipodeLiftTopR :
    CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) ⟶ P.groupRingTop :=
  inv P.squareΓTop ≫ P.antipodePairR.appTop


-- @@ L1008-1017 verbatim
theorem includeLeft_comp_antipodeLiftTopR :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop))
      ≫ P.antipodeLiftTopR = 𝟙 P.groupRingTop := by
  have hleg := fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
  have hinv : affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
      ≫ inv P.squareΓTop = 𝟙 _ := IsIso.hom_inv_id _
  rw [antipodeLiftTopR, ← Category.assoc, ← hleg, Category.assoc, Category.assoc,
    reassoc_of% hinv, ← Scheme.Hom.comp_appTop, antipodePairR_fst,
    AlgebraicGeometry.Scheme.Hom.id_appTop]


-- @@ L1019-1027 verbatim
theorem includeRight_comp_antipodeLiftTopR :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom
      ≫ P.antipodeLiftTopR = P.antipodeTop := by
  have hleg := snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
  have hinv : affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
      ≫ inv P.squareΓTop = 𝟙 _ := IsIso.hom_inv_id _
  rw [antipodeLiftTopR, ← Category.assoc, ← hleg, Category.assoc, Category.assoc,
    reassoc_of% hinv, ← Scheme.Hom.comp_appTop, antipodePairR_snd, antipodeTop]


-- @@ L1029-1033 verbatim
/-- The algebraic right antipode lift `A' ⊗[R'] A' →ₐ[R'] A'`, `a ⊗ b ↦ a · S'(b)`. -/
noncomputable def antipodeLiftAlgTopR :
    (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) →ₐ[P.baseRingTop] P.groupRingTop :=
  Algebra.TensorProduct.lift (AlgHom.id P.baseRingTop P.groupRingTop) P.antipodeAlgTop
    (fun _ _ => Commute.all _ _)


-- @@ L1035-1048 verbatim
theorem antipodeLiftAlgTopR_eq :
    CommRingCat.ofHom P.antipodeLiftAlgTopR.toRingHom = P.antipodeLiftTopR := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_antipodeLiftTopR]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show antipodeLiftAlgTopR G P (a ⊗ₜ[P.baseRingTop] (1 : P.groupRingTop)) = _
    rw [antipodeLiftAlgTopR, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one,
      AlgHom.coe_id, id_eq]
    rfl
  · rw [P.includeRight_comp_antipodeLiftTopR]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show antipodeLiftAlgTopR G P ((1 : P.groupRingTop) ⊗ₜ[P.baseRingTop] a) = _
    rw [antipodeLiftAlgTopR, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl


-- @@ L1050-1103 verbatim
/-- **The right inverse law, chart form** `⟨𝟙, S⟩ ≫ μ = e ∘ !` (`g ↦ g·g⁻¹ = e`).
Dualises `invOver_mulOver_right`. -/
theorem antipodePairR_comp_squareMulRes :
    P.antipodePairR ≫ P.squareMulRes = P.groupToBaseRes ≫ P.unitSection := by
  rw [← cancel_mono (P.groupOpen.ι ≫ G.ι)]
  have hb : P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have hgsts : P.groupSquareToSquare ≫ (Over.mk G.π ⊗ Over.mk G.π).hom
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes ≫ P.V.ι := by
    rw [← G.mulHom_π, ← Category.assoc]; exact P.squareMul_π
  have hfstι : P.groupSquareToSquare ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_fst]; exact Category.assoc _ _ _
  have hsndι : P.groupSquareToSquare ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_snd]; exact Category.assoc _ _ _
  have hbaseP : (P.antipodePairR ≫ P.groupSquareToSquare) ≫ (Over.mk G.π ⊗ Over.mk G.π).hom
      = P.groupOpen.ι ≫ G.π := by
    simp only [Category.assoc, hgsts, P.antipodePairR_fst_assoc]
    rw [← hb]
  have Esplit : (hbaseP ▸ EllipticCurve.Point.restrict E
        (P.antipodePairR ≫ P.groupSquareToSquare) (G.sqFstPoint + G.sqSndPoint)
        : E.Point (P.groupOpen.ι ≫ G.π))
      = EllipticCurve.Point.restrict E P.groupOpen.ι G.universalPoint
        + EllipticCurve.Point.restrict E P.groupOpen.ι (-G.universalPoint) :=
    point_restrictT_add_eq hbaseP G.sqFstPoint G.sqSndPoint
      (EllipticCurve.Point.restrict E P.groupOpen.ι G.universalPoint)
      (EllipticCurve.Point.restrict E P.groupOpen.ι (-G.universalPoint))
      (by
        show (P.antipodePairR ≫ P.groupSquareToSquare)
            ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
          = P.groupOpen.ι ≫ G.universalPoint.1
        simp only [Category.assoc, hfstι, P.antipodePairR_fst_assoc]
        rfl)
      (by
        show (P.antipodePairR ≫ P.groupSquareToSquare)
            ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
          = P.groupOpen.ι ≫ (-G.universalPoint : E.Point G.π).1
        rw [← G.invHom_ι]
        simp only [Category.assoc, hsndι, P.antipodePairR_snd_assoc, P.invRes_comp_ι_assoc])
  have hsum : EllipticCurve.Point.restrict E P.groupOpen.ι G.universalPoint
        + EllipticCurve.Point.restrict E P.groupOpen.ι (-G.universalPoint) = 0 := by
    rw [← EllipticCurve.Point.restrict_add, add_neg_cancel, EllipticCurve.Point.restrict_zero]
  have hLHS : (P.antipodePairR ≫ P.squareMulRes) ≫ P.groupOpen.ι ≫ G.ι
      = (EllipticCurve.Point.restrict E P.groupOpen.ι G.universalPoint
        + EllipticCurve.Point.restrict E P.groupOpen.ι (-G.universalPoint)).1 := by
    rw [← Esplit, point_base_congr]
    simp only [EllipticCurve.Point.restrict, Category.assoc, P.squareMulRes_comp_ι_assoc,
      squareMul, G.mulHom_ι]
  have hRHS : (P.groupToBaseRes ≫ P.unitSection) ≫ P.groupOpen.ι ≫ G.ι
      = (0 : E.Point (P.groupOpen.ι ≫ G.π)).1 := by
    rw [E.point_zero_val, hb]
    simp only [Category.assoc, P.unitSection_comp_ι_assoc, G.unitHom_ι]
  rw [hLHS, hRHS, hsum]


-- @@ L1105-1109 verbatim
theorem comulTop_comp_antipodeLiftTopR :
    P.comulTop ≫ P.antipodeLiftTopR = P.counitTop ≫ P.groupToBaseRes.appTop := by
  rw [comulTop, antipodeLiftTopR, Category.assoc, ← Category.assoc P.squareΓTop,
    IsIso.hom_inv_id, Category.id_comp, ← Scheme.Hom.comp_appTop,
    P.antipodePairR_comp_squareMulRes, Scheme.Hom.comp_appTop, counitTop]


-- @@ L1111-1120 verbatim
/-- **The right antipode law, `AlgHom` form**: `(id ⊗ S') ∘ Δ' = ofId ∘ ε'`. -/
theorem antipodeLiftAlgTopR_comp_comulAlgTop :
    P.antipodeLiftAlgTopR.comp P.comulAlgTop
      = (Algebra.ofId P.baseRingTop P.groupRingTop).comp P.counitAlgTop := by
  have h := P.comulTop_comp_antipodeLiftTopR
  rw [← P.antipodeLiftAlgTopR_eq] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRingTop ⟶ P.groupRingTop => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2


-- @@ L1122-1122 verbatim
/-! #### The `⊤`-level counit laws, `AlgHom` form -/


-- @@ L1124-1129 verbatim
/-- The algebraic left counit lift `A' ⊗[R'] A' →ₐ[R'] A'`, `a ⊗ b ↦ ε'(a) • b`. -/
noncomputable def counitLiftAlgTop :
    (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) →ₐ[P.baseRingTop] P.groupRingTop :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId P.baseRingTop P.groupRingTop).comp P.counitAlgTop)
    (AlgHom.id P.baseRingTop P.groupRingTop) (fun _ _ => Commute.all _ _)


-- @@ L1131-1143 verbatim
theorem counitLiftAlgTop_eq :
    CommRingCat.ofHom P.counitLiftAlgTop.toRingHom = P.counitLiftTop := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_counitLiftTop]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLiftAlgTop G P (a ⊗ₜ[P.baseRingTop] (1 : P.groupRingTop)) = _
    rw [counitLiftAlgTop, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
    rfl
  · rw [P.includeRight_comp_counitLiftTop]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLiftAlgTop G P ((1 : P.groupRingTop) ⊗ₜ[P.baseRingTop] a) = _
    rw [counitLiftAlgTop, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl


-- @@ L1145-1154 verbatim
/-- **The left counit law, `⊤`-level, `AlgHom` form**: `(ε' ⊗ id) ∘ Δ' = id`. -/
theorem counitLiftAlgTop_comp_comulAlgTop :
    P.counitLiftAlgTop.comp P.comulAlgTop = AlgHom.id P.baseRingTop P.groupRingTop := by
  have h := P.comulTop_comp_counitLiftTop
  rw [← P.counitLiftAlgTop_eq] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRingTop ⟶ P.groupRingTop => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    CommRingCat.hom_id, RingHom.id_apply] at h2
  exact h2


-- @@ L1156-1159 verbatim
/-- The right unit lift, `⊤`-level, dual of the right unit section. -/
noncomputable def counitLiftTop' :
    CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) ⟶ P.groupRingTop :=
  inv P.squareΓTop ≫ P.rightUnitSection.appTop


-- @@ L1161-1165 verbatim
theorem comulTop_comp_counitLiftTop' :
    P.comulTop ≫ P.counitLiftTop' = 𝟙 P.groupRingTop := by
  rw [comulTop, counitLiftTop', Category.assoc, ← Category.assoc P.squareΓTop,
    IsIso.hom_inv_id, Category.id_comp, ← Scheme.Hom.comp_appTop,
    P.rightUnitSection_comp_squareMulRes, AlgebraicGeometry.Scheme.Hom.id_appTop]


-- @@ L1167-1176 verbatim
theorem includeLeft_comp_counitLiftTop' :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop))
      ≫ P.counitLiftTop' = 𝟙 P.groupRingTop := by
  have hleg := fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
  have hinv : affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
      ≫ inv P.squareΓTop = 𝟙 _ := IsIso.hom_inv_id _
  rw [counitLiftTop', ← Category.assoc, ← hleg, Category.assoc, Category.assoc,
    reassoc_of% hinv, ← Scheme.Hom.comp_appTop, P.rightUnitSection_fst,
    AlgebraicGeometry.Scheme.Hom.id_appTop]


-- @@ L1178-1187 verbatim
theorem includeRight_comp_counitLiftTop' :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom
      ≫ P.counitLiftTop' = P.counitTop ≫ P.groupToBaseRes.appTop := by
  have hleg := snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
  have hinv : affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
      ≫ inv P.squareΓTop = 𝟙 _ := IsIso.hom_inv_id _
  rw [counitLiftTop', ← Category.assoc, ← hleg, Category.assoc, Category.assoc,
    reassoc_of% hinv, ← Scheme.Hom.comp_appTop, P.rightUnitSection_snd,
    Scheme.Hom.comp_appTop, counitTop]


-- @@ L1189-1194 verbatim
/-- The algebraic right counit lift `A' ⊗[R'] A' →ₐ[R'] A'`, `a ⊗ b ↦ a • ε'(b)`. -/
noncomputable def counitLiftAlgTop' :
    (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) →ₐ[P.baseRingTop] P.groupRingTop :=
  Algebra.TensorProduct.lift (AlgHom.id P.baseRingTop P.groupRingTop)
    ((Algebra.ofId P.baseRingTop P.groupRingTop).comp P.counitAlgTop)
    (fun _ _ => Commute.all _ _)


-- @@ L1196-1208 verbatim
theorem counitLiftAlgTop'_eq :
    CommRingCat.ofHom P.counitLiftAlgTop'.toRingHom = P.counitLiftTop' := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_counitLiftTop']
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLiftAlgTop' G P (a ⊗ₜ[P.baseRingTop] (1 : P.groupRingTop)) = _
    rw [counitLiftAlgTop', Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
    rfl
  · rw [P.includeRight_comp_counitLiftTop']
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show counitLiftAlgTop' G P ((1 : P.groupRingTop) ⊗ₜ[P.baseRingTop] a) = _
    rw [counitLiftAlgTop', Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl


-- @@ L1210-1219 verbatim
/-- **The right counit law, `⊤`-level, `AlgHom` form**: `(id ⊗ ε') ∘ Δ' = id`. -/
theorem counitLiftAlgTop'_comp_comulAlgTop :
    P.counitLiftAlgTop'.comp P.comulAlgTop = AlgHom.id P.baseRingTop P.groupRingTop := by
  have h := P.comulTop_comp_counitLiftTop'
  rw [← P.counitLiftAlgTop'_eq] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRingTop ⟶ P.groupRingTop => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    CommRingCat.hom_id, RingHom.id_apply] at h2
  exact h2


-- @@ L1221-1221 verbatim
/-! #### The triple product and coassociativity -/


-- @@ L1223-1225 verbatim
/-- The cube `G|_V ×_V (G|_V ×_V G|_V)`. -/
noncomputable abbrev cube : Scheme.{u} :=
  pullback P.groupToBaseRes P.squareToBase


-- @@ L1227-1231 verbatim
/-- The iterated (triple) Künneth transport:
`Γ(cube, ⊤) ≅ A' ⊗[R'] Γ(square, ⊤)`. -/
noncomputable abbrev cubeΓ :
    Γ(P.cube, ⊤) ⟶ CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] Γ(P.groupSquare, ⊤)) :=
  affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl


-- @@ L1233-1233 verbatim
instance : IsIso P.cubeΓ := isIso_affineKunnethΓ _ _ rfl rfl


-- @@ L1235-1244 verbatim
/-- The corestricted multiplication as an `R'`-algebra map `A' →ₐ Γ(square)`. -/
noncomputable def squareMulResAlg : P.groupRingTop →ₐ[P.baseRingTop] Γ(P.groupSquare, ⊤) where
  toRingHom := P.squareMulRes.appTop.hom
  commutes' := fun r => by
    have h : P.groupToBaseRes.appTop ≫ P.squareMulRes.appTop
        = P.squareToBase.appTop := by
      rw [← Scheme.Hom.comp_appTop, P.squareMulRes_comp_groupToBaseRes]
      rfl
    have h2 := congrArg (fun m : P.baseRingTop ⟶ Γ(P.groupSquare, ⊤) => m.hom r) h
    exact h2


-- @@ L1246-1251 verbatim
/-- The inner-multiplication `cube → square`: `(g₁,(g₂,g₃)) ↦ (g₁, g₂·g₃)`. -/
noncomputable def cubeInnerMul : P.cube ⟶ P.groupSquare :=
  pullback.map P.groupToBaseRes P.squareToBase P.groupToBaseRes P.groupToBaseRes
    (𝟙 P.groupOpen.toScheme) P.squareMulRes (𝟙 P.V.toScheme)
    (by rw [Category.id_comp, Category.comp_id])
    (by rw [Category.comp_id]; exact P.squareMulRes_comp_groupToBaseRes.symm)


-- @@ L1253-1257 verbatim
@[reassoc]
theorem cubeInnerMul_fst :
    P.cubeInnerMul ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes
      = pullback.fst P.groupToBaseRes P.squareToBase := by
  rw [cubeInnerMul, pullback.lift_fst, Category.comp_id]


-- @@ L1259-1263 verbatim
@[reassoc]
theorem cubeInnerMul_snd :
    P.cubeInnerMul ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes
      = pullback.snd P.groupToBaseRes P.squareToBase ≫ P.squareMulRes := by
  rw [cubeInnerMul, pullback.lift_snd]


-- @@ L1265-1303 verbatim
/-- **Künneth naturality (inner multiplication)**: transporting the inner-multiplication
across the two Künneth identifications is `id ⊗ (Γ-dual of squareMulRes)`. -/
theorem cubeInnerMul_appTop_cubeΓ :
    P.cubeInnerMul.appTop ≫ P.cubeΓ
      = P.squareΓTop ≫ CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
            P.squareMulResAlg).toRingHom := by
  -- both sides out of Γ(groupSquare); precompose with the iso squareΓTop⁻¹
  rw [← cancel_epi (inv P.squareΓTop), ← Category.assoc, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]
  have hLinv : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop))
      ≫ inv P.squareΓTop
      = (pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop := by
    rw [IsIso.comp_inv_eq]
    exact (fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl).symm
  have hRinv : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom
      ≫ inv P.squareΓTop
      = (pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop := by
    rw [IsIso.comp_inv_eq]
    exact (snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl).symm
  refine tensor_hom_ext ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, hLinv, ← Scheme.Hom.comp_appTop,
      P.cubeInnerMul_fst]
    rw [show P.cubeΓ = affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl from rfl,
      fst_appTop_affineKunnethΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show _ = Algebra.TensorProduct.map _ _ (a ⊗ₜ[P.baseRingTop] 1)
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  · rw [← Category.assoc, ← Category.assoc, hRinv, ← Scheme.Hom.comp_appTop,
      P.cubeInnerMul_snd, Scheme.Hom.comp_appTop, Category.assoc]
    rw [show P.cubeΓ = affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl from rfl,
      snd_appTop_affineKunnethΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show _ = Algebra.TensorProduct.map _ _ (1 ⊗ₜ[P.baseRingTop] a)
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl


-- @@ L1305-1318 verbatim
/-- The Künneth transport `Γ(square) ≅ A' ⊗ A'` as an `R'`-algebra map. -/
noncomputable def squareΓTopAlg :
    Γ(P.groupSquare, ⊤) →ₐ[P.baseRingTop] (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) where
  toRingHom := P.squareΓTop.hom
  commutes' := fun r => by
    have hbase : P.squareToBase.appTop ≫ P.squareΓTop
        = CommRingCat.ofHom
            (algebraMap P.baseRingTop (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)) := by
      rw [squareToBase, Scheme.Hom.comp_appTop, Category.assoc]
      exact base_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl
    have h2 := congrArg (fun m : P.baseRingTop ⟶ CommRingCat.of
      (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) => m.hom r) hbase
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    exact h2


-- @@ L1320-1323 verbatim
/-- `Δ'` factors as `squareMulResAlg` then `squareΓTopAlg`. -/
theorem comulAlgTop_eq :
    P.comulAlgTop = P.squareΓTopAlg.comp P.squareMulResAlg :=
  AlgHom.ext fun _ => rfl


-- @@ L1325-1331 verbatim
/-- The fixed triple identification `Γ(cube) ⟶ A' ⊗ (A' ⊗ A')`. -/
noncomputable def tripleΓ :
    Γ(P.cube, ⊤)
      ⟶ CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop]
          (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)) :=
  P.cubeΓ ≫ CommRingCat.ofHom (Algebra.TensorProduct.map
    (AlgHom.id P.baseRingTop P.groupRingTop) P.squareΓTopAlg).toRingHom


-- @@ L1333-1336 verbatim
/-- The right-associated triple multiplication `cube → G|_V`,
`(g₁,(g₂,g₃)) ↦ g₁·(g₂·g₃)`. -/
noncomputable def rightMulScheme : P.cube ⟶ P.groupOpen.toScheme :=
  P.cubeInnerMul ≫ P.squareMulRes


-- @@ L1338-1366 verbatim
/-- **`Δ₂R = (id ⊗ Δ') ∘ Δ'` is the `Γ`-dual of the right-associated triple
multiplication.** -/
theorem comulTop_comp_map_id_comulTop :
    P.comulTop ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
          P.comulAlgTop).toRingHom
      = P.rightMulScheme.appTop ≫ P.tripleΓ := by
  -- combine the two id⊗(-) using functoriality + comulAlgTop_eq
  have hmap : CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
          P.comulAlgTop).toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id P.baseRingTop P.groupRingTop) P.squareMulResAlg).toRingHom
        ≫ CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id P.baseRingTop P.groupRingTop) P.squareΓTopAlg).toRingHom := by
    have halg : Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
          P.comulAlgTop
        = (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
            P.squareΓTopAlg).comp
          (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
            P.squareMulResAlg) := by
      rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, comulAlgTop_eq]
    rw [halg]
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    rfl
  rw [comulTop, tripleΓ, rightMulScheme, Scheme.Hom.comp_appTop, hmap]
  simp only [Category.assoc]
  rw [← Category.assoc P.squareΓTop, ← P.cubeInnerMul_appTop_cubeΓ]
  simp only [Category.assoc]


-- @@ L1368-1368 verbatim
/-! #### The `Δ₂L` (left-associated) side -/


-- @@ L1370-1372 verbatim
/-- The left-square cube `(G|_V ×_V G|_V) ×_V G|_V`. -/
noncomputable abbrev cubeL : Scheme.{u} :=
  pullback P.squareToBase P.groupToBaseRes


-- @@ L1374-1377 verbatim
/-- The iterated Künneth for `cubeL`: `Γ(cubeL) ≅ Γ(square) ⊗ A'`. -/
noncomputable abbrev cubeLΓ :
    Γ(P.cubeL, ⊤) ⟶ CommRingCat.of (Γ(P.groupSquare, ⊤) ⊗[P.baseRingTop] P.groupRingTop) :=
  affineKunnethΓ P.squareToBase P.groupToBaseRes rfl rfl


-- @@ L1379-1379 verbatim
instance : IsIso P.cubeLΓ := isIso_affineKunnethΓ _ _ rfl rfl


-- @@ L1381-1386 verbatim
/-- The outer-multiplication `cubeL → square`: `((g₁,g₂),g₃) ↦ (g₁·g₂, g₃)`. -/
noncomputable def cubeOuterMul : P.cubeL ⟶ P.groupSquare :=
  pullback.map P.squareToBase P.groupToBaseRes P.groupToBaseRes P.groupToBaseRes
    P.squareMulRes (𝟙 P.groupOpen.toScheme) (𝟙 P.V.toScheme)
    (by rw [Category.comp_id]; exact P.squareMulRes_comp_groupToBaseRes.symm)
    (by rw [Category.id_comp, Category.comp_id])


-- @@ L1388-1392 verbatim
@[reassoc]
theorem cubeOuterMul_fst :
    P.cubeOuterMul ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes
      = pullback.fst P.squareToBase P.groupToBaseRes ≫ P.squareMulRes := by
  rw [cubeOuterMul, pullback.lift_fst]


-- @@ L1394-1398 verbatim
@[reassoc]
theorem cubeOuterMul_snd :
    P.cubeOuterMul ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes
      = pullback.snd P.squareToBase P.groupToBaseRes := by
  rw [cubeOuterMul, pullback.lift_snd, Category.comp_id]


-- @@ L1400-1436 verbatim
/-- **Künneth naturality (outer multiplication)**. -/
theorem cubeOuterMul_appTop_cubeLΓ :
    P.cubeOuterMul.appTop ≫ P.cubeLΓ
      = P.squareΓTop ≫ CommRingCat.ofHom
          (Algebra.TensorProduct.map P.squareMulResAlg
            (AlgHom.id P.baseRingTop P.groupRingTop)).toRingHom := by
  rw [← cancel_epi (inv P.squareΓTop), ← Category.assoc, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]
  have hLinv : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop))
      ≫ inv P.squareΓTop
      = (pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop := by
    rw [IsIso.comp_inv_eq]
    exact (fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl).symm
  have hRinv : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom
      ≫ inv P.squareΓTop
      = (pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop := by
    rw [IsIso.comp_inv_eq]
    exact (snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl).symm
  refine tensor_hom_ext ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, hLinv, ← Scheme.Hom.comp_appTop,
      P.cubeOuterMul_fst, Scheme.Hom.comp_appTop, Category.assoc]
    rw [show P.cubeLΓ = affineKunnethΓ P.squareToBase P.groupToBaseRes rfl rfl from rfl,
      fst_appTop_affineKunnethΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show _ = Algebra.TensorProduct.map _ _ (a ⊗ₜ[P.baseRingTop] 1)
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  · rw [← Category.assoc, ← Category.assoc, hRinv, ← Scheme.Hom.comp_appTop,
      P.cubeOuterMul_snd]
    rw [show P.cubeLΓ = affineKunnethΓ P.squareToBase P.groupToBaseRes rfl rfl from rfl,
      snd_appTop_affineKunnethΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show _ = Algebra.TensorProduct.map _ _ (1 ⊗ₜ[P.baseRingTop] a)
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl


-- @@ L1438-1444 verbatim
/-- The triple identification `Γ(cubeL) ⟶ (A' ⊗ A') ⊗ A'`. -/
noncomputable def tripleΓL :
    Γ(P.cubeL, ⊤)
      ⟶ CommRingCat.of ((P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)
          ⊗[P.baseRingTop] P.groupRingTop) :=
  P.cubeLΓ ≫ CommRingCat.ofHom (Algebra.TensorProduct.map P.squareΓTopAlg
    (AlgHom.id P.baseRingTop P.groupRingTop)).toRingHom


-- @@ L1446-1449 verbatim
/-- The left-associated triple multiplication `cubeL → G|_V`,
`((g₁,g₂),g₃) ↦ (g₁·g₂)·g₃`. -/
noncomputable def leftMulSchemeL : P.cubeL ⟶ P.groupOpen.toScheme :=
  P.cubeOuterMul ≫ P.squareMulRes


-- @@ L1451-1478 verbatim
/-- **`Δ₂L' = (Δ' ⊗ id) ∘ Δ'` is the `Γ`-dual of the left-associated triple
multiplication on `cubeL`.** -/
theorem comulTop_comp_map_comulTop_id :
    P.comulTop ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.map P.comulAlgTop
          (AlgHom.id P.baseRingTop P.groupRingTop)).toRingHom
      = P.leftMulSchemeL.appTop ≫ P.tripleΓL := by
  have hmap : CommRingCat.ofHom
        (Algebra.TensorProduct.map P.comulAlgTop
          (AlgHom.id P.baseRingTop P.groupRingTop)).toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.map P.squareMulResAlg
          (AlgHom.id P.baseRingTop P.groupRingTop)).toRingHom
        ≫ CommRingCat.ofHom (Algebra.TensorProduct.map P.squareΓTopAlg
          (AlgHom.id P.baseRingTop P.groupRingTop)).toRingHom := by
    have halg : Algebra.TensorProduct.map P.comulAlgTop
          (AlgHom.id P.baseRingTop P.groupRingTop)
        = (Algebra.TensorProduct.map P.squareΓTopAlg
            (AlgHom.id P.baseRingTop P.groupRingTop)).comp
          (Algebra.TensorProduct.map P.squareMulResAlg
            (AlgHom.id P.baseRingTop P.groupRingTop)) := by
      rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, comulAlgTop_eq]
    rw [halg]
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    rfl
  rw [comulTop, tripleΓL, leftMulSchemeL, Scheme.Hom.comp_appTop, hmap]
  simp only [Category.assoc]
  rw [← Category.assoc P.squareΓTop, ← P.cubeOuterMul_appTop_cubeLΓ]
  simp only [Category.assoc]


-- @@ L1480-1480 verbatim
/-! #### The associator and the final coassociativity -/


-- @@ L1482-1506 verbatim
/-- The associator `cube → cubeL`, `(g₁,(g₂,g₃)) ↦ ((g₁,g₂),g₃)`. -/
noncomputable def assocScheme : P.cube ⟶ P.cubeL := by
  refine pullback.lift
    (pullback.lift (pullback.fst P.groupToBaseRes P.squareToBase)
      (pullback.snd P.groupToBaseRes P.squareToBase
        ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes) ?_)
    (pullback.snd P.groupToBaseRes P.squareToBase
      ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes) ?_
  · -- inner: g₁ ≫ gtb = (g₂-proj) ≫ gtb
    show pullback.fst P.groupToBaseRes P.squareToBase ≫ P.groupToBaseRes
      = (pullback.snd P.groupToBaseRes P.squareToBase
          ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes) ≫ P.groupToBaseRes
    rw [pullback.condition, Category.assoc]
    rfl
  · -- outer: (inner lift) ≫ squareToBase = (g₃-proj) ≫ gtb
    show pullback.lift (pullback.fst P.groupToBaseRes P.squareToBase)
          (pullback.snd P.groupToBaseRes P.squareToBase
            ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes) _
        ≫ (pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes)
      = (pullback.snd P.groupToBaseRes P.squareToBase
          ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes) ≫ P.groupToBaseRes
    rw [← Category.assoc, pullback.lift_fst, pullback.condition, Category.assoc]
    congr 1
    rw [← pullback.condition]
    rfl


-- @@ L1508-1513 verbatim
@[reassoc]
theorem assocScheme_fst_fst :
    P.assocScheme ≫ pullback.fst P.squareToBase P.groupToBaseRes
        ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes
      = pullback.fst P.groupToBaseRes P.squareToBase := by
  rw [assocScheme, pullback.lift_fst_assoc, pullback.lift_fst]


-- @@ L1515-1521 verbatim
@[reassoc]
theorem assocScheme_fst_snd :
    P.assocScheme ≫ pullback.fst P.squareToBase P.groupToBaseRes
        ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes
      = pullback.snd P.groupToBaseRes P.squareToBase
        ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes := by
  rw [assocScheme, pullback.lift_fst_assoc, pullback.lift_snd]


-- @@ L1523-1528 verbatim
@[reassoc]
theorem assocScheme_snd :
    P.assocScheme ≫ pullback.snd P.squareToBase P.groupToBaseRes
      = pullback.snd P.groupToBaseRes P.squareToBase
        ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes := by
  rw [assocScheme, pullback.lift_snd]


-- @@ L1530-1672 verbatim
/-- **R1: the associator-Künneth compat.** `tripleΓL` followed by the tensor associator
equals `assocScheme` followed by `tripleΓ`. -/
theorem tripleΓL_comp_assoc :
    P.tripleΓL ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop P.baseRingTop
          P.groupRingTop P.groupRingTop P.groupRingTop).toAlgHom.toRingHom
      = P.assocScheme.appTop ≫ P.tripleΓ := by
  rw [← cancel_epi (inv P.cubeLΓ)]
  rw [tripleΓL]
  simp only [Category.assoc]
  rw [IsIso.inv_hom_id_assoc]
  -- reduced goal R1': `map(sqΓAlg,id) ≫ assoc = inv cubeLΓ ≫ assocScheme.appTop ≫ tripleΓ`
  refine tensor_hom_ext ?_ ?_
  · -- L-branch: the `Γ(square)` factor (coordinates g₁, g₂)
    have hLsq : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := P.baseRingTop) (A := Γ(P.groupSquare, ⊤)) (B := P.groupRingTop))
        ≫ inv P.cubeLΓ = (pullback.fst P.squareToBase P.groupToBaseRes).appTop := by
      rw [IsIso.comp_inv_eq]
      exact (fst_appTop_affineKunnethΓ P.squareToBase P.groupToBaseRes rfl rfl).symm
    have hfst_sq : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop))
        ≫ inv P.squareΓTop = (pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop := by
      rw [IsIso.comp_inv_eq]
      exact (fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl).symm
    have hsnd_sq : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom
        ≫ inv P.squareΓTop = (pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop := by
      rw [IsIso.comp_inv_eq]
      exact (snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl).symm
    rw [← cancel_epi (inv P.squareΓTop)]
    refine tensor_hom_ext ?_ ?_
    · -- g₁ leaf
      have hAff : (pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop
            ≫ (pullback.fst P.squareToBase P.groupToBaseRes).appTop ≫ P.assocScheme.appTop
          = (pullback.fst P.groupToBaseRes P.squareToBase).appTop := by
        rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, Category.assoc,
          assocScheme_fst_fst]
      rw [reassoc_of% hfst_sq, reassoc_of% hfst_sq, reassoc_of% hLsq,
        reassoc_of% hAff, tripleΓ,
        show P.cubeΓ = affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl from rfl,
        reassoc_of% (fst_appTop_affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl)]
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      have hsqfst : squareΓTopAlg G P
            ((pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop.hom a)
          = a ⊗ₜ[P.baseRingTop] (1 : P.groupRingTop) := by
        have h := congrArg (fun m : P.groupRingTop ⟶ _ => m.hom a)
          (fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      show (Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop P.baseRingTop
            P.groupRingTop P.groupRingTop P.groupRingTop)
          (Algebra.TensorProduct.map P.squareΓTopAlg (AlgHom.id P.baseRingTop P.groupRingTop)
            (Algebra.TensorProduct.includeLeftRingHom
              ((pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop.hom a)))
        = Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop) P.squareΓTopAlg
            (Algebra.TensorProduct.includeLeftRingHom a)
      rw [show Algebra.TensorProduct.includeLeftRingHom
            ((pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop.hom a)
          = (pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop.hom a ⊗ₜ[P.baseRingTop]
            (1 : P.groupRingTop) from rfl,
        Algebra.TensorProduct.map_tmul, map_one, hsqfst,
        Algebra.TensorProduct.assoc_tmul]
      rw [show Algebra.TensorProduct.includeLeftRingHom a
          = a ⊗ₜ[P.baseRingTop] (1 : Γ(P.groupSquare, ⊤)) from rfl,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one,
        Algebra.TensorProduct.one_def]
    · -- g₂ leaf
      have hAfs : (pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop
            ≫ (pullback.fst P.squareToBase P.groupToBaseRes).appTop ≫ P.assocScheme.appTop
          = (pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop
            ≫ (pullback.snd P.groupToBaseRes P.squareToBase).appTop := by
        rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, Category.assoc,
          assocScheme_fst_snd, Scheme.Hom.comp_appTop]
      rw [reassoc_of% hsnd_sq, reassoc_of% hsnd_sq, reassoc_of% hLsq,
        reassoc_of% hAfs, tripleΓ,
        show P.cubeΓ = affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl from rfl,
        reassoc_of% (snd_appTop_affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl)]
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      have hsqsnd : squareΓTopAlg G P
            ((pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop.hom b)
          = (1 : P.groupRingTop) ⊗ₜ[P.baseRingTop] b := by
        have h := congrArg (fun m : P.groupRingTop ⟶ _ => m.hom b)
          (snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h
      have hsqfst : squareΓTopAlg G P
            ((pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop.hom b)
          = b ⊗ₜ[P.baseRingTop] (1 : P.groupRingTop) := by
        have h := congrArg (fun m : P.groupRingTop ⟶ _ => m.hom b)
          (fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      show (Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop P.baseRingTop
            P.groupRingTop P.groupRingTop P.groupRingTop)
          (Algebra.TensorProduct.map P.squareΓTopAlg (AlgHom.id P.baseRingTop P.groupRingTop)
            (Algebra.TensorProduct.includeLeftRingHom
              ((pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop.hom b)))
        = Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop) P.squareΓTopAlg
            (Algebra.TensorProduct.includeRight
              ((pullback.fst P.groupToBaseRes P.groupToBaseRes).appTop.hom b))
      rw [show Algebra.TensorProduct.includeLeftRingHom
            ((pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop.hom b)
          = (pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop.hom b ⊗ₜ[P.baseRingTop]
            (1 : P.groupRingTop) from rfl,
        Algebra.TensorProduct.map_tmul, map_one, hsqsnd,
        Algebra.TensorProduct.assoc_tmul]
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
        map_one, hsqfst]
  · -- R-branch: the `A'` factor (coordinate g₃)
    have hg3 : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := P.baseRingTop) (A := Γ(P.groupSquare, ⊤)) (B := P.groupRingTop)).toRingHom
        ≫ inv P.cubeLΓ = (pullback.snd P.squareToBase P.groupToBaseRes).appTop := by
      rw [IsIso.comp_inv_eq]
      exact (snd_appTop_affineKunnethΓ P.squareToBase P.groupToBaseRes rfl rfl).symm
    have hRsnd : (pullback.snd P.squareToBase P.groupToBaseRes).appTop ≫ P.assocScheme.appTop
        = (pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop
          ≫ (pullback.snd P.groupToBaseRes P.squareToBase).appTop := by
      rw [← Scheme.Hom.comp_appTop, assocScheme_snd, Scheme.Hom.comp_appTop]
    rw [reassoc_of% hg3, reassoc_of% hRsnd, tripleΓ,
      show P.cubeΓ = affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl from rfl,
      reassoc_of% (snd_appTop_affineKunnethΓ P.groupToBaseRes P.squareToBase rfl rfl)]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    have hsqsnd : squareΓTopAlg G P
          ((pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop.hom a)
        = (1 : P.groupRingTop) ⊗ₜ[P.baseRingTop] a := by
      have h := congrArg (fun m : P.groupRingTop ⟶ _ => m.hom a)
        (snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
      exact h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    show (Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop P.baseRingTop
          P.groupRingTop P.groupRingTop P.groupRingTop)
        (Algebra.TensorProduct.map P.squareΓTopAlg (AlgHom.id P.baseRingTop P.groupRingTop)
          (Algebra.TensorProduct.includeRight a))
      = Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop) P.squareΓTopAlg
          (Algebra.TensorProduct.includeRight
            ((pullback.snd P.groupToBaseRes P.groupToBaseRes).appTop.hom a))
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one,
      AlgHom.coe_id, id_eq, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one, hsqsnd, Algebra.TensorProduct.one_def,
      Algebra.TensorProduct.assoc_tmul]


-- @@ L1674-1674 verbatim
/-! #### R3: chart-level associativity and the final coassociativity -/


-- @@ L1676-1678 verbatim
/-- The common base of the three coordinate points of the cube: the projection to `S`. -/
noncomputable abbrev cubeBase : P.cube ⟶ S :=
  pullback.fst P.groupToBaseRes P.squareToBase ≫ P.groupOpen.ι ≫ G.π


-- @@ L1680-1683 verbatim
/-- First coordinate point `g₁` of the cube, as an `E`-point over `cubeBase`. -/
noncomputable def cubePt₁ : E.Point (P.cubeBase) :=
  ⟨pullback.fst P.groupToBaseRes P.squareToBase ≫ P.groupOpen.ι ≫ G.ι, by
    simp only [cubeBase, Category.assoc, G.ι_π]⟩


-- @@ L1685-1696 verbatim
/-- Second coordinate point `g₂` of the cube. -/
noncomputable def cubePt₂ : E.Point (P.cubeBase) :=
  ⟨pullback.snd P.groupToBaseRes P.squareToBase ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes
      ≫ P.groupOpen.ι ≫ G.ι, by
    have hb : P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι :=
      (Scheme.Hom.resLE_comp_ι _ _).symm
    have hc₂ : pullback.snd P.groupToBaseRes P.squareToBase
          ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes
        = pullback.fst P.groupToBaseRes P.squareToBase ≫ P.groupToBaseRes :=
      pullback.condition.symm
    simp only [cubeBase, Category.assoc, G.ι_π, hb]
    rw [reassoc_of% hc₂]⟩


-- @@ L1698-1710 verbatim
/-- Third coordinate point `g₃` of the cube. -/
noncomputable def cubePt₃ : E.Point (P.cubeBase) :=
  ⟨pullback.snd P.groupToBaseRes P.squareToBase ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes
      ≫ P.groupOpen.ι ≫ G.ι, by
    have hb : P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι :=
      (Scheme.Hom.resLE_comp_ι _ _).symm
    have hc₃ : pullback.snd P.groupToBaseRes P.squareToBase
          ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes
        = pullback.fst P.groupToBaseRes P.squareToBase ≫ P.groupToBaseRes := by
      rw [← pullback.condition (f := P.groupToBaseRes) (g := P.groupToBaseRes)]
      exact pullback.condition.symm
    simp only [cubeBase, Category.assoc, G.ι_π, hb]
    rw [reassoc_of% hc₃]⟩


-- @@ L1712-1820 verbatim
/-- **R3-assoc: chart-level group associativity.** The associator carries the left-associated
triple multiplication `((g₁·g₂)·g₃)` to the right-associated one `(g₁·(g₂·g₃))`. The proof
cancels the two monos `groupOpen.ι` and `G.ι`, reducing to an equality of morphisms into `E`;
both sides are the coercion of a triple sum of the cube's three coordinate points, and the
identity is `add_assoc` in `E.Point cubeBase`. -/
theorem assocScheme_leftMulSchemeL :
    P.assocScheme ≫ P.leftMulSchemeL = P.rightMulScheme := by
  rw [← cancel_mono (P.groupOpen.ι ≫ G.ι)]
  have hb : P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have hU : (G.sqFstPoint + G.sqSndPoint : E.Point _).1 = G.mulHom ≫ G.ι := G.mulHom_ι.symm
  have hgsts : P.groupSquareToSquare ≫ (Over.mk G.π ⊗ Over.mk G.π).hom
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes ≫ P.V.ι := by
    rw [← G.mulHom_π, ← Category.assoc]; exact P.squareMul_π
  have hfstι : P.groupSquareToSquare ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_fst]; exact Category.assoc _ _ _
  have hsndι : P.groupSquareToSquare ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_snd]; exact Category.assoc _ _ _
  have hv : (P.cubeInnerMul ≫ P.groupSquareToSquare) ≫ (Over.mk G.π ⊗ Over.mk G.π).hom
      = P.cubeBase := by
    simp only [Category.assoc, hgsts, P.cubeInnerMul_fst_assoc, cubeBase, hb]
  have hv' : (P.assocScheme ≫ P.cubeOuterMul ≫ P.groupSquareToSquare)
        ≫ (Over.mk G.π ⊗ Over.mk G.π).hom = P.cubeBase := by
    simp only [Category.assoc, hgsts, P.cubeOuterMul_fst_assoc,
      P.squareMulRes_comp_groupToBaseRes_assoc, P.assocScheme_fst_fst_assoc, cubeBase, hb]
  have hs : (pullback.snd P.groupToBaseRes P.squareToBase ≫ P.groupSquareToSquare)
        ≫ (Over.mk G.π ⊗ Over.mk G.π).hom = P.cubeBase := by
    have hc₂ : pullback.snd P.groupToBaseRes P.squareToBase
          ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes
        = pullback.fst P.groupToBaseRes P.squareToBase ≫ P.groupToBaseRes :=
      pullback.condition.symm
    simp only [Category.assoc, hgsts, cubeBase, hb]
    rw [reassoc_of% hc₂]
  have hu : (P.assocScheme ≫ pullback.fst P.squareToBase P.groupToBaseRes ≫ P.groupSquareToSquare)
        ≫ (Over.mk G.π ⊗ Over.mk G.π).hom = P.cubeBase := by
    simp only [Category.assoc, hgsts, P.assocScheme_fst_fst_assoc, cubeBase, hb]
  have Es : (hs ▸ EllipticCurve.Point.restrict E
        (pullback.snd P.groupToBaseRes P.squareToBase ≫ P.groupSquareToSquare)
        (G.sqFstPoint + G.sqSndPoint) : E.Point P.cubeBase) = P.cubePt₂ + P.cubePt₃ :=
    point_restrictT_add_eq hs G.sqFstPoint G.sqSndPoint P.cubePt₂ P.cubePt₃
      (by
        show (pullback.snd P.groupToBaseRes P.squareToBase ≫ P.groupSquareToSquare)
            ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hfstι, cubePt₂])
      (by
        show (pullback.snd P.groupToBaseRes P.squareToBase ≫ P.groupSquareToSquare)
            ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hsndι, cubePt₃])
  have Eu : (hu ▸ EllipticCurve.Point.restrict E
        (P.assocScheme ≫ pullback.fst P.squareToBase P.groupToBaseRes ≫ P.groupSquareToSquare)
        (G.sqFstPoint + G.sqSndPoint) : E.Point P.cubeBase) = P.cubePt₁ + P.cubePt₂ :=
    point_restrictT_add_eq hu G.sqFstPoint G.sqSndPoint P.cubePt₁ P.cubePt₂
      (by
        show (P.assocScheme ≫ pullback.fst P.squareToBase P.groupToBaseRes ≫ P.groupSquareToSquare)
            ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hfstι, P.assocScheme_fst_fst_assoc, cubePt₁])
      (by
        show (P.assocScheme ≫ pullback.fst P.squareToBase P.groupToBaseRes ≫ P.groupSquareToSquare)
            ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hsndι, P.assocScheme_fst_snd_assoc, cubePt₂])
  have Ev : (hv ▸ EllipticCurve.Point.restrict E (P.cubeInnerMul ≫ P.groupSquareToSquare)
        (G.sqFstPoint + G.sqSndPoint) : E.Point P.cubeBase) = P.cubePt₁ + (P.cubePt₂ + P.cubePt₃) :=
    point_restrictT_add_eq hv G.sqFstPoint G.sqSndPoint P.cubePt₁ (P.cubePt₂ + P.cubePt₃)
      (by
        show (P.cubeInnerMul ≫ P.groupSquareToSquare)
            ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hfstι, P.cubeInnerMul_fst_assoc, cubePt₁])
      (by
        have hR : (P.cubePt₂ + P.cubePt₃).1
            = (pullback.snd P.groupToBaseRes P.squareToBase ≫ P.groupSquareToSquare)
              ≫ (G.sqFstPoint + G.sqSndPoint : E.Point _).1 := by
          rw [← Es]; exact point_base_congr hs _
        rw [hR]
        show (P.cubeInnerMul ≫ P.groupSquareToSquare)
            ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hsndι, P.cubeInnerMul_snd_assoc,
          P.squareMulRes_comp_ι_assoc, squareMul, hU])
  have Ev' : (hv' ▸ EllipticCurve.Point.restrict E
        (P.assocScheme ≫ P.cubeOuterMul ≫ P.groupSquareToSquare)
        (G.sqFstPoint + G.sqSndPoint) : E.Point P.cubeBase) = (P.cubePt₁ + P.cubePt₂) + P.cubePt₃ :=
    point_restrictT_add_eq hv' G.sqFstPoint G.sqSndPoint (P.cubePt₁ + P.cubePt₂) P.cubePt₃
      (by
        have hL : (P.cubePt₁ + P.cubePt₂).1
            = (P.assocScheme ≫ pullback.fst P.squareToBase P.groupToBaseRes ≫ P.groupSquareToSquare)
              ≫ (G.sqFstPoint + G.sqSndPoint : E.Point _).1 := by
          rw [← Eu]; exact point_base_congr hu _
        rw [hL]
        show (P.assocScheme ≫ P.cubeOuterMul ≫ P.groupSquareToSquare)
            ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hfstι, P.cubeOuterMul_fst_assoc,
          P.squareMulRes_comp_ι_assoc, squareMul, hU])
      (by
        show (P.assocScheme ≫ P.cubeOuterMul ≫ P.groupSquareToSquare)
            ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hsndι, P.cubeOuterMul_snd_assoc,
          P.assocScheme_snd_assoc, cubePt₃])
  have hLHS : (P.assocScheme ≫ P.leftMulSchemeL) ≫ P.groupOpen.ι ≫ G.ι
      = ((P.cubePt₁ + P.cubePt₂) + P.cubePt₃).1 := by
    rw [← Ev', point_base_congr]
    simp only [EllipticCurve.Point.restrict, leftMulSchemeL, Category.assoc,
      P.squareMulRes_comp_ι_assoc, squareMul, G.mulHom_ι]
  have hRHS : P.rightMulScheme ≫ P.groupOpen.ι ≫ G.ι
      = (P.cubePt₁ + (P.cubePt₂ + P.cubePt₃)).1 := by
    rw [← Ev, point_base_congr]
    simp only [EllipticCurve.Point.restrict, rightMulScheme, Category.assoc,
      P.squareMulRes_comp_ι_assoc, squareMul, G.mulHom_ι]
  rw [hLHS, hRHS, add_assoc]


-- @@ L1822-1836 verbatim
/-- **Coassociativity, `CommRingCat` form**: `assoc ∘ (Δ' ⊗ id) ∘ Δ' = (id ⊗ Δ') ∘ Δ'`,
combining `Δ₂L'` (`comulTop_comp_map_comulTop_id`), `R1` (`tripleΓL_comp_assoc`) and `R3-assoc`
(`assocScheme_leftMulSchemeL`) on the left, `Δ₂R` (`comulTop_comp_map_id_comulTop`) on the
right. -/
theorem comulTop_coassoc :
    P.comulTop ≫ CommRingCat.ofHom (Algebra.TensorProduct.map P.comulAlgTop
          (AlgHom.id P.baseRingTop P.groupRingTop)).toRingHom
        ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop
          P.baseRingTop P.groupRingTop P.groupRingTop P.groupRingTop).toAlgHom.toRingHom
      = P.comulTop ≫ CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id P.baseRingTop P.groupRingTop) P.comulAlgTop).toRingHom := by
  have hcomp : P.leftMulSchemeL.appTop ≫ P.assocScheme.appTop = P.rightMulScheme.appTop := by
    rw [← Scheme.Hom.comp_appTop, assocScheme_leftMulSchemeL]
  rw [reassoc_of% comulTop_comp_map_comulTop_id, tripleΓL_comp_assoc,
    reassoc_of% hcomp, comulTop_comp_map_id_comulTop]


-- @@ L1838-1847 verbatim
/-- **Coassociativity, `AlgHom` form** — exactly the `h_coassoc` field of `Bialgebra.ofAlgHom`. -/
theorem comulAlgTop_coassoc :
    (Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop P.baseRingTop
          P.groupRingTop P.groupRingTop P.groupRingTop).toAlgHom.comp
        ((Algebra.TensorProduct.map P.comulAlgTop
          (AlgHom.id P.baseRingTop P.groupRingTop)).comp P.comulAlgTop)
      = (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
          P.comulAlgTop).comp P.comulAlgTop := by
  refine AlgHom.ext fun x => ?_
  exact congrArg (fun m : P.groupRingTop ⟶ _ => m.hom x) P.comulTop_coassoc


-- @@ L1849-1849 verbatim
/-! #### The counit laws in `lid`/`rid` form (for `Bialgebra.ofAlgHom`) -/


-- @@ L1851-1866 verbatim
/-- `ε'`-collapse via `lid`: `lid ∘ (ε' ⊗ id) = counitLiftAlgTop`. -/
theorem lid_comp_map_counit :
    (Algebra.TensorProduct.lid P.baseRingTop P.groupRingTop).toAlgHom.comp
        (Algebra.TensorProduct.map P.counitAlgTop (AlgHom.id P.baseRingTop P.groupRingTop))
      = P.counitLiftAlgTop := by
  refine AlgHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    show (Algebra.TensorProduct.lid P.baseRingTop P.groupRingTop)
        (counitAlgTop G P a ⊗ₜ[P.baseRingTop] b)
      = counitLiftAlgTop G P (a ⊗ₜ[P.baseRingTop] b)
    rw [Algebra.TensorProduct.lid_tmul, counitLiftAlgTop, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.coe_id, id_eq, Algebra.smul_def]
  | add x y hx hy => rw [map_add, map_add, hx, hy]


-- @@ L1868-1882 verbatim
/-- **`h_rTensor`**: `(ε' ⊗ id) ∘ Δ' = lid.symm` — the left counit law in the shape
`Bialgebra.ofAlgHom` consumes. -/
theorem map_counit_id_comp_comul :
    (Algebra.TensorProduct.map P.counitAlgTop
          (AlgHom.id P.baseRingTop P.groupRingTop)).comp P.comulAlgTop
      = (Algebra.TensorProduct.lid P.baseRingTop P.groupRingTop).symm := by
  have key : (Algebra.TensorProduct.lid P.baseRingTop P.groupRingTop).toAlgHom.comp
      ((Algebra.TensorProduct.map P.counitAlgTop
        (AlgHom.id P.baseRingTop P.groupRingTop)).comp P.comulAlgTop)
      = AlgHom.id P.baseRingTop P.groupRingTop := by
    rw [← AlgHom.comp_assoc, lid_comp_map_counit, counitLiftAlgTop_comp_comulAlgTop]
  refine AlgHom.ext fun a => ?_
  have hkey := AlgHom.congr_fun key a
  rw [AlgHom.comp_apply, AlgHom.id_apply] at hkey
  simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.eq_symm_apply] using hkey


-- @@ L1884-1900 verbatim
/-- `ε'`-collapse via `rid`: `rid ∘ (id ⊗ ε') = counitLiftAlgTop'`. -/
theorem rid_comp_map_counit :
    (Algebra.TensorProduct.rid P.baseRingTop P.baseRingTop P.groupRingTop).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop) P.counitAlgTop)
      = P.counitLiftAlgTop' := by
  refine AlgHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    show (Algebra.TensorProduct.rid P.baseRingTop P.baseRingTop P.groupRingTop)
        (a ⊗ₜ[P.baseRingTop] counitAlgTop G P b)
      = counitLiftAlgTop' G P (a ⊗ₜ[P.baseRingTop] b)
    rw [Algebra.TensorProduct.rid_tmul, counitLiftAlgTop', Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.coe_id, id_eq, Algebra.smul_def,
      _root_.mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]


-- @@ L1902-1915 verbatim
/-- **`h_lTensor`**: `(id ⊗ ε') ∘ Δ' = rid.symm`. -/
theorem map_id_counit_comp_comul :
    (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
          P.counitAlgTop).comp P.comulAlgTop
      = (Algebra.TensorProduct.rid P.baseRingTop P.baseRingTop P.groupRingTop).symm := by
  have key : (Algebra.TensorProduct.rid P.baseRingTop P.baseRingTop P.groupRingTop).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop)
        P.counitAlgTop).comp P.comulAlgTop)
      = AlgHom.id P.baseRingTop P.groupRingTop := by
    rw [← AlgHom.comp_assoc, rid_comp_map_counit, counitLiftAlgTop'_comp_comulAlgTop]
  refine AlgHom.ext fun a => ?_
  have hkey := AlgHom.congr_fun key a
  rw [AlgHom.comp_apply, AlgHom.id_apply] at hkey
  simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.eq_symm_apply] using hkey


-- @@ L1917-1922 verbatim
/-- **The chart Hopf-algebra bialgebra structure** `[Bialgebra R' A']`, from the ⊤-level
comultiplication and counit, with coassociativity `comulAlgTop_coassoc` and the two counit
laws `map_counit_id_comp_comul` / `map_id_counit_comp_comul`. -/
noncomputable instance instBialgebra : Bialgebra P.baseRingTop P.groupRingTop :=
  Bialgebra.ofAlgHom P.comulAlgTop P.counitAlgTop
    P.comulAlgTop_coassoc P.map_counit_id_comp_comul P.map_id_counit_comp_comul


-- @@ L1924-1927 verbatim
/-- The canonical `comulAlgHom` of `instBialgebra` is our `comulAlgTop`. -/
theorem comulAlgHom_eq :
    Bialgebra.comulAlgHom P.baseRingTop P.groupRingTop = P.comulAlgTop :=
  AlgHom.ext fun _ => rfl


-- @@ L1929-1932 verbatim
/-- The canonical `counitAlgHom` of `instBialgebra` is our `counitAlgTop`. -/
theorem counitAlgHom_eq :
    Bialgebra.counitAlgHom P.baseRingTop P.groupRingTop = P.counitAlgTop :=
  AlgHom.ext fun _ => rfl


-- @@ L1934-1940 verbatim
/-- **`[HopfAlgebra R' A']`** — the chart Hopf-algebra structure, upgrading `instBialgebra`
with the ⊤-level antipode `antipodeAlgTop` and the two antipode laws
`antipodeLiftAlgTop_comp_comulAlgTop` / `antipodeLiftAlgTopR_comp_comulAlgTop`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra P.baseRingTop P.groupRingTop :=
  HopfAlgebra.ofAlgHom P.antipodeAlgTop
    (by rw [comulAlgHom_eq, counitAlgHom_eq]; exact P.antipodeLiftAlgTop_comp_comulAlgTop)
    (by rw [comulAlgHom_eq, counitAlgHom_eq]; exact P.antipodeLiftAlgTopR_comp_comulAlgTop)


-- @@ L1942-1953 verbatim
/-! ### The opens-level Hopf structure: transporting the `⊤`-level structure across `topIso`

The `⊤`-level Bialgebra/HopfAlgebra structures live over `R' = Γ(V.toScheme, ⊤)` and
`A' = Γ(G|_V.toScheme, ⊤)`. We assemble the opens-level `[Bialgebra R A]` and `[HopfAlgebra R A]`
(over `R = Γ(S, V)`, `A = Γ(G.G, G|_V)`) by:
* the **counit** laws: pure-algebra packaging of the already-proven collapsed forms
  `counitLift_comp_comulAlg` / `counitLift'_comp_comulAlg`;
* the **antipode** laws: dualising the (level-agnostic, already-proven) scheme identities
  `antipodePair_comp_squareMulRes` / `antipodePairR_comp_squareMulRes` through the *opens* Künneth
  `squareΓ`, exactly mirroring the opens counit development;
* **coassociativity**: transporting the `⊤`-level `comulTop_coassoc` across the `topIso` ring
  isomorphisms `A ≅ A'`, `A ⊗ A ≅ A' ⊗ A'`, `A ⊗ (A ⊗ A) ≅ A' ⊗ (A' ⊗ A')`. -/


-- @@ L1955-1963 verbatim
/-- **The `appLE`/`appTop` bridge for `squareMul`**: the `appLE` of the restricted multiplication
is the `topIso`-conjugate of the corestricted multiplication's `appTop`. -/
theorem squareMul_appLE_eq :
    P.squareMul.appLE P.groupOpen ⊤ P.top_le_preimage_groupOpen_squareMul
      = P.groupOpen.topIso.inv ≫ P.squareMulRes.appTop := by
  rw [appLE_congr_hom P.squareMulRes_comp_ι.symm P.groupOpen ⊤,
    ← Scheme.Hom.appLE_comp_appLE P.squareMulRes P.groupOpen.ι P.groupOpen ⊤ ⊤
      P.groupOpen.ι_preimage_self.ge le_top,
    ι_appLE_top, appLE_top_top]


-- @@ L1965-1975 verbatim
/-- **The `appLE`/`appTop` bridge for the antipode**: `topIso`-conjugating `invRes.appTop`
recovers the opens-level antipode `groupPatchAntipode`. -/
theorem groupPatchAntipode_eq :
    P.groupOpen.topIso.inv ≫ P.invRes.appTop ≫ P.groupOpen.topIso.hom
      = P.groupPatchAntipode := by
  rw [show P.invRes.appTop
      = P.groupOpen.topIso.hom ≫ P.groupPatchAntipode ≫ P.groupOpen.topIso.inv from
    Scheme.Hom.resLE_app_top (f := G.invHom) (U := P.groupOpen) (V := P.groupOpen)
      P.le_preimage_groupOpen_invHom]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]


-- @@ L1977-1977 verbatim
/-! #### The opens-level counit laws in `lid`/`rid` form -/


-- @@ L1979-1994 verbatim
/-- `ε`-collapse via `lid`: `lid ∘ (ε ⊗ id) = counitLift`. -/
theorem lid_comp_map_counitAlg :
    (Algebra.TensorProduct.lid P.baseRing P.groupRing).toAlgHom.comp
        (Algebra.TensorProduct.map P.counitAlg (AlgHom.id P.baseRing P.groupRing))
      = P.counitLift := by
  refine AlgHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    show (Algebra.TensorProduct.lid P.baseRing P.groupRing)
        (counitAlg G P a ⊗ₜ[P.baseRing] b)
      = counitLift G P (a ⊗ₜ[P.baseRing] b)
    rw [Algebra.TensorProduct.lid_tmul, counitLift, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.coe_id, id_eq, Algebra.smul_def]
  | add x y hx hy => rw [map_add, map_add, hx, hy]


-- @@ L1996-2008 verbatim
/-- **The left counit law, opens level**: `(ε ⊗ id) ∘ Δ = lid.symm`. -/
theorem map_counitAlg_id_comp_comulAlg :
    (Algebra.TensorProduct.map P.counitAlg (AlgHom.id P.baseRing P.groupRing)).comp P.comulAlg
      = (Algebra.TensorProduct.lid P.baseRing P.groupRing).symm := by
  have key : (Algebra.TensorProduct.lid P.baseRing P.groupRing).toAlgHom.comp
      ((Algebra.TensorProduct.map P.counitAlg
        (AlgHom.id P.baseRing P.groupRing)).comp P.comulAlg)
      = AlgHom.id P.baseRing P.groupRing := by
    rw [← AlgHom.comp_assoc, lid_comp_map_counitAlg, counitLift_comp_comulAlg]
  refine AlgHom.ext fun a => ?_
  have hkey := AlgHom.congr_fun key a
  rw [AlgHom.comp_apply, AlgHom.id_apply] at hkey
  simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.eq_symm_apply] using hkey


-- @@ L2010-2026 verbatim
/-- `ε`-collapse via `rid`: `rid ∘ (id ⊗ ε) = counitLift'`. -/
theorem rid_comp_map_counitAlg :
    (Algebra.TensorProduct.rid P.baseRing P.baseRing P.groupRing).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing) P.counitAlg)
      = P.counitLift' := by
  refine AlgHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    show (Algebra.TensorProduct.rid P.baseRing P.baseRing P.groupRing)
        (a ⊗ₜ[P.baseRing] counitAlg G P b)
      = counitLift' G P (a ⊗ₜ[P.baseRing] b)
    rw [Algebra.TensorProduct.rid_tmul, counitLift', Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.coe_id, id_eq, Algebra.smul_def,
      _root_.mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]


-- @@ L2028-2040 verbatim
/-- **The right counit law, opens level**: `(id ⊗ ε) ∘ Δ = rid.symm`. -/
theorem map_id_counitAlg_comp_comulAlg :
    (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing) P.counitAlg).comp P.comulAlg
      = (Algebra.TensorProduct.rid P.baseRing P.baseRing P.groupRing).symm := by
  have key : (Algebra.TensorProduct.rid P.baseRing P.baseRing P.groupRing).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing)
        P.counitAlg).comp P.comulAlg)
      = AlgHom.id P.baseRing P.groupRing := by
    rw [← AlgHom.comp_assoc, rid_comp_map_counitAlg, counitLift'_comp_comulAlg]
  refine AlgHom.ext fun a => ?_
  have hkey := AlgHom.congr_fun key a
  rw [AlgHom.comp_apply, AlgHom.id_apply] at hkey
  simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.eq_symm_apply] using hkey


-- @@ L2042-2046 verbatim
/-! #### The opens-level antipode laws

Dualising the (already-proven, level-agnostic) scheme identities
`antipodePair_comp_squareMulRes` / `antipodePairR_comp_squareMulRes` through the *opens* Künneth
`squareΓ`, mirroring the opens counit development. -/


-- @@ L2048-2051 verbatim
/-- The `Γ`-dual of the left antipode pairing, opens level: `A ⊗ A ⟶ A`. -/
noncomputable def antipodeLiftΓ :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) ⟶ P.groupRing :=
  inv P.squareΓ ≫ P.antipodePair.appTop ≫ P.groupOpen.topIso.hom


-- @@ L2053-2068 verbatim
theorem includeLeft_comp_antipodeLiftΓ :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing))
      ≫ P.antipodeLiftΓ = P.groupPatchAntipode := by
  have hleg := topIso_inv_fst_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [antipodeLiftΓ, ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  have hcomp : (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.antipodePair.appTop
      = P.invRes.appTop := by
    rw [← Scheme.Hom.comp_appTop, P.antipodePair_fst]
  rw [← Category.assoc ((pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp]
  exact P.groupPatchAntipode_eq


-- @@ L2070-2087 verbatim
theorem includeRight_comp_antipodeLiftΓ :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ P.antipodeLiftΓ = 𝟙 P.groupRing := by
  have hleg := topIso_inv_snd_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [antipodeLiftΓ, ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  have hcomp : (pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.antipodePair.appTop
      = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, P.antipodePair_snd,
      AlgebraicGeometry.Scheme.Hom.id_appTop]
  rw [← Category.assoc ((pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp, Category.id_comp,
    Iso.inv_hom_id]
  rfl


-- @@ L2089-2093 verbatim
/-- The algebraic left antipode lift `A ⊗[R] A →ₐ[R] A`, `a ⊗ b ↦ S(a) · b`. -/
noncomputable def antipodeLift :
    (P.groupRing ⊗[P.baseRing] P.groupRing) →ₐ[P.baseRing] P.groupRing :=
  Algebra.TensorProduct.lift P.antipodeAlg (AlgHom.id P.baseRing P.groupRing)
    (fun _ _ => Commute.all _ _)


-- @@ L2095-2108 verbatim
theorem antipodeLift_eq :
    CommRingCat.ofHom P.antipodeLift.toRingHom = P.antipodeLiftΓ := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_antipodeLiftΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show antipodeLift G P (a ⊗ₜ[P.baseRing] (1 : P.groupRing)) = _
    rw [antipodeLift, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
    rfl
  · rw [P.includeRight_comp_antipodeLiftΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show antipodeLift G P ((1 : P.groupRing) ⊗ₜ[P.baseRing] a) = _
    rw [antipodeLift, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul,
      AlgHom.coe_id, id_eq]
    rfl


-- @@ L2110-2120 verbatim
/-- **The left antipode law, opens `CommRingCat` form**. -/
theorem groupPatchComul_comp_antipodeLiftΓ :
    P.groupPatchComul ≫ P.antipodeLiftΓ
      = P.groupPatchCounit ≫ G.π.appLE P.V P.groupOpen le_rfl := by
  rw [groupPatchComul_eq, antipodeLiftΓ, Category.assoc,
    ← Category.assoc P.squareΓ, IsIso.hom_inv_id, Category.id_comp,
    P.squareMul_appLE_eq, Category.assoc, ← Category.assoc P.squareMulRes.appTop,
    ← Scheme.Hom.comp_appTop, P.antipodePair_comp_squareMulRes, Scheme.Hom.comp_appTop,
    P.unitSection_appTop, P.groupToBase_appTop]
  simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.id_comp,
    Category.comp_id]


-- @@ L2122-2131 verbatim
/-- **The left antipode law, opens `AlgHom` form**: `(S ⊗ id) ∘ Δ = ofId ∘ ε`. -/
theorem antipodeLift_comp_comulAlg :
    P.antipodeLift.comp P.comulAlg
      = (Algebra.ofId P.baseRing P.groupRing).comp P.counitAlg := by
  have h := P.groupPatchComul_comp_antipodeLiftΓ
  rw [← P.antipodeLift_eq] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRing ⟶ P.groupRing => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2


-- @@ L2133-2136 verbatim
/-- The `Γ`-dual of the right antipode pairing, opens level. -/
noncomputable def antipodeLiftΓR :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) ⟶ P.groupRing :=
  inv P.squareΓ ≫ P.antipodePairR.appTop ≫ P.groupOpen.topIso.hom


-- @@ L2138-2155 verbatim
theorem includeLeft_comp_antipodeLiftΓR :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing))
      ≫ P.antipodeLiftΓR = 𝟙 P.groupRing := by
  have hleg := topIso_inv_fst_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [antipodeLiftΓR, ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  have hcomp : (pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.antipodePairR.appTop
      = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, P.antipodePairR_fst,
      AlgebraicGeometry.Scheme.Hom.id_appTop]
  rw [← Category.assoc ((pullback.fst (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp, Category.id_comp,
    Iso.inv_hom_id]
  rfl


-- @@ L2157-2172 verbatim
theorem includeRight_comp_antipodeLiftΓR :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ P.antipodeLiftΓR = P.groupPatchAntipode := by
  have hleg := topIso_inv_snd_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [antipodeLiftΓR, ← hleg]
  rw [Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp]
  have hcomp : (pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
        (G.π.resLE P.V P.groupOpen le_rfl)).appTop ≫ P.antipodePairR.appTop
      = P.invRes.appTop := by
    rw [← Scheme.Hom.comp_appTop, P.antipodePairR_snd]
  rw [← Category.assoc ((pullback.snd (G.π.resLE P.V P.groupOpen le_rfl)
      (G.π.resLE P.V P.groupOpen le_rfl)).appTop), hcomp]
  exact P.groupPatchAntipode_eq


-- @@ L2174-2178 verbatim
/-- The algebraic right antipode lift `A ⊗[R] A →ₐ[R] A`, `a ⊗ b ↦ a · S(b)`. -/
noncomputable def antipodeLiftR :
    (P.groupRing ⊗[P.baseRing] P.groupRing) →ₐ[P.baseRing] P.groupRing :=
  Algebra.TensorProduct.lift (AlgHom.id P.baseRing P.groupRing) P.antipodeAlg
    (fun _ _ => Commute.all _ _)


-- @@ L2180-2193 verbatim
theorem antipodeLiftR_eq :
    CommRingCat.ofHom P.antipodeLiftR.toRingHom = P.antipodeLiftΓR := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_antipodeLiftΓR]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show antipodeLiftR G P (a ⊗ₜ[P.baseRing] (1 : P.groupRing)) = _
    rw [antipodeLiftR, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one,
      AlgHom.coe_id, id_eq]
    rfl
  · rw [P.includeRight_comp_antipodeLiftΓR]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show antipodeLiftR G P ((1 : P.groupRing) ⊗ₜ[P.baseRing] a) = _
    rw [antipodeLiftR, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl


-- @@ L2195-2205 verbatim
/-- **The right antipode law, opens `CommRingCat` form**. -/
theorem groupPatchComul_comp_antipodeLiftΓR :
    P.groupPatchComul ≫ P.antipodeLiftΓR
      = P.groupPatchCounit ≫ G.π.appLE P.V P.groupOpen le_rfl := by
  rw [groupPatchComul_eq, antipodeLiftΓR, Category.assoc,
    ← Category.assoc P.squareΓ, IsIso.hom_inv_id, Category.id_comp,
    P.squareMul_appLE_eq, Category.assoc, ← Category.assoc P.squareMulRes.appTop,
    ← Scheme.Hom.comp_appTop, P.antipodePairR_comp_squareMulRes, Scheme.Hom.comp_appTop,
    P.unitSection_appTop, P.groupToBase_appTop]
  simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.id_comp,
    Category.comp_id]


-- @@ L2207-2216 verbatim
/-- **The right antipode law, opens `AlgHom` form**: `(id ⊗ S) ∘ Δ = ofId ∘ ε`. -/
theorem antipodeLiftR_comp_comulAlg :
    P.antipodeLiftR.comp P.comulAlg
      = (Algebra.ofId P.baseRing P.groupRing).comp P.counitAlg := by
  have h := P.groupPatchComul_comp_antipodeLiftΓR
  rw [← P.antipodeLiftR_eq] at h
  refine AlgHom.ext fun a => ?_
  have h2 := congrArg (fun m : P.groupRing ⟶ P.groupRing => m.hom a) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2


-- @@ L2218-2223 verbatim
/-! #### Coassociativity, opens level: transporting `comulTop_coassoc` across `topIso`

`transDouble` (resp. `transTriple`, `transTripleL`) is the `topIso`-transport of the double
(resp. right- or left-nested triple) tensor product; each is characterised by its action on
the tensor inclusions. The `⊤`-level `comulTop_coassoc` transports to the opens-level
`groupPatchComul_coassoc`, hence `comulAlg_coassoc`. -/


-- @@ L2225-2229 verbatim
/-- The `topIso`-transport of the double tensor `A ⊗ A → A' ⊗ A'`, as `inv squareΓ ≫ squareΓTop`. -/
noncomputable def transDouble :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing)
      ⟶ CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) :=
  inv P.squareΓ ≫ P.squareΓTop


-- @@ L2231-2231 verbatim
instance : IsIso P.transDouble := by rw [transDouble]; infer_instance


-- @@ L2233-2237 verbatim
/-- **`Δ`-intertwining**: the opens comultiplication is the `⊤`-level one conjugated by `topIso`. -/
theorem groupPatchComul_comp_transDouble :
    P.groupPatchComul ≫ P.transDouble = P.groupOpen.topIso.inv ≫ P.comulTop := by
  rw [transDouble, groupPatchComul_eq, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp, P.squareMul_appLE_eq, comulTop, Category.assoc]


-- @@ L2239-2250 verbatim
/-- `transDouble` sends the left inclusion to `ψ`-conjugated left inclusion. -/
theorem includeLeft_comp_transDouble :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing))
      ≫ P.transDouble
      = P.groupOpen.topIso.inv ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)) := by
  have hleg := topIso_inv_fst_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [transDouble, ← hleg, Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp,
    fst_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl]


-- @@ L2252-2263 verbatim
/-- `transDouble` sends the right inclusion to `ψ`-conjugated right inclusion. -/
theorem includeRight_comp_transDouble :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ P.transDouble
      = P.groupOpen.topIso.inv ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom := by
  have hleg := topIso_inv_snd_appTop_patchKunnethΓ (e₁ := le_rfl) (e₂ := le_rfl)
    G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen rfl rfl
  rw [transDouble, ← hleg, Category.assoc, Category.assoc, ← Category.assoc P.squareΓ,
    IsIso.hom_inv_id, Category.id_comp,
    snd_appTop_affineKunnethΓ P.groupToBaseRes P.groupToBaseRes rfl rfl]


-- @@ L2265-2265 verbatim
section CoassocTransport


-- @@ L2267-2269 verbatim
/-- (local) base change `R → R'` along `topIso`. -/
noncomputable local instance : Algebra P.baseRing P.baseRingTop :=
  RingHom.toAlgebra P.V.topIso.inv.hom

-- @@ L2270-2272 verbatim
/-- (local) base change `R' → R` along `topIso`. -/
noncomputable local instance : Algebra P.baseRingTop P.baseRing :=
  RingHom.toAlgebra P.V.topIso.hom.hom

-- @@ L2273-2276 verbatim
/-- (local) `A'` as an `R`-algebra, through `R → R' → A'`. -/
noncomputable local instance : Algebra P.baseRing P.groupRingTop :=
  RingHom.toAlgebra ((algebraMap P.baseRingTop P.groupRingTop).comp
    (algebraMap P.baseRing P.baseRingTop))

-- @@ L2277-2278 verbatim
local instance : IsScalarTower P.baseRing P.baseRingTop P.groupRingTop :=
  .of_algebraMap_eq' rfl

-- @@ L2279-2282 verbatim
/-- (local) `A` as an `R'`-algebra, through `R' → R → A`. -/
noncomputable local instance : Algebra P.baseRingTop P.groupRing :=
  RingHom.toAlgebra ((algebraMap P.baseRing P.groupRing).comp
    (algebraMap P.baseRingTop P.baseRing))

-- @@ L2283-2284 verbatim
local instance : IsScalarTower P.baseRingTop P.baseRing P.groupRing :=
  .of_algebraMap_eq' rfl


-- @@ L2286-2290 verbatim
/-- The semilinearity of `ψ = topIso.inv`: `ψ ∘ algMap_R = algMap_{R'} ∘ (R → R')`. -/
theorem topIso_inv_algebraMap :
    G.π.appLE P.V P.groupOpen le_rfl ≫ P.groupOpen.topIso.inv
      = P.V.topIso.inv ≫ P.groupToBaseRes.appTop := by
  rw [groupToBase_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]


-- @@ L2292-2296 verbatim
/-- The reverse semilinearity of `ψ⁻¹ = topIso.hom`. -/
theorem topIso_hom_algebraMap :
    P.groupToBaseRes.appTop ≫ P.groupOpen.topIso.hom
      = P.V.topIso.hom ≫ G.π.appLE P.V P.groupOpen le_rfl := by
  rw [groupToBase_appTop, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]


-- @@ L2298-2304 verbatim
/-- `ψ = topIso.inv` as an `R`-algebra map `A →ₐ[R] A'`. -/
noncomputable def psiAlg : P.groupRing →ₐ[P.baseRing] P.groupRingTop where
  toRingHom := P.groupOpen.topIso.inv.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRing ⟶ P.groupRingTop => m.hom r) P.topIso_inv_algebraMap
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h


-- @@ L2306-2312 verbatim
/-- `ψ⁻¹ = topIso.hom` as an `R'`-algebra map `A' →ₐ[R'] A`. -/
noncomputable def psiAlgInv : P.groupRingTop →ₐ[P.baseRingTop] P.groupRing where
  toRingHom := P.groupOpen.topIso.hom.hom
  commutes' := fun r => by
    have h := congrArg (fun m : P.baseRingTop ⟶ P.groupRing => m.hom r) P.topIso_hom_algebraMap
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h


-- @@ L2314-2331 verbatim
/-- Elementwise action of `transDouble`: `a ⊗ b ↦ ψ a ⊗ ψ b`. -/
theorem transDouble_tmul (a b : P.groupRing) :
    P.transDouble.hom (a ⊗ₜ[P.baseRing] b)
      = P.groupOpen.topIso.inv.hom a ⊗ₜ[P.baseRingTop] P.groupOpen.topIso.inv.hom b := by
  have hL : P.transDouble.hom (a ⊗ₜ[P.baseRing] (1 : P.groupRing))
      = P.groupOpen.topIso.inv.hom a ⊗ₜ[P.baseRingTop] 1 := by
    have h := congrArg (fun m : P.groupRing ⟶ _ => m.hom a) P.includeLeft_comp_transDouble
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h
  have hR : P.transDouble.hom ((1 : P.groupRing) ⊗ₜ[P.baseRing] b)
      = 1 ⊗ₜ[P.baseRingTop] P.groupOpen.topIso.inv.hom b := by
    have h := congrArg (fun m : P.groupRing ⟶ _ => m.hom b) P.includeRight_comp_transDouble
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h
  rw [show (a ⊗ₜ[P.baseRing] b : P.groupRing ⊗[P.baseRing] P.groupRing)
      = (a ⊗ₜ[P.baseRing] (1 : P.groupRing)) * ((1 : P.groupRing) ⊗ₜ[P.baseRing] b) from by
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul],
    map_mul, hL, hR, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]


-- @@ L2333-2341 verbatim
/-- `inv transDouble` sends the left inclusion to the `ψ⁻¹`-conjugated left inclusion. -/
theorem includeLeft_comp_transDoubleInv :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop))
      ≫ inv P.transDouble
      = P.groupOpen.topIso.hom ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)) := by
  rw [IsIso.comp_inv_eq, Category.assoc, P.includeLeft_comp_transDouble]
  exact (P.groupOpen.topIso.hom_inv_id_assoc _).symm


-- @@ L2343-2351 verbatim
/-- `inv transDouble` sends the right inclusion to the `ψ⁻¹`-conjugated right inclusion. -/
theorem includeRight_comp_transDoubleInv :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRingTop) (A := P.groupRingTop) (B := P.groupRingTop)).toRingHom
      ≫ inv P.transDouble
      = P.groupOpen.topIso.hom ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := P.baseRing) (A := P.groupRing) (B := P.groupRing)).toRingHom := by
  rw [IsIso.comp_inv_eq, Category.assoc, P.includeRight_comp_transDouble]
  exact (P.groupOpen.topIso.hom_inv_id_assoc _).symm


-- @@ L2353-2370 verbatim
/-- Elementwise action of `inv transDouble`: `a ⊗ b ↦ ψ⁻¹ a ⊗ ψ⁻¹ b`. -/
theorem transDoubleInv_tmul (a b : P.groupRingTop) :
    (inv P.transDouble).hom (a ⊗ₜ[P.baseRingTop] b)
      = P.groupOpen.topIso.hom.hom a ⊗ₜ[P.baseRing] P.groupOpen.topIso.hom.hom b := by
  have hL : (inv P.transDouble).hom (a ⊗ₜ[P.baseRingTop] (1 : P.groupRingTop))
      = P.groupOpen.topIso.hom.hom a ⊗ₜ[P.baseRing] 1 := by
    have h := congrArg (fun m : P.groupRingTop ⟶ _ => m.hom a) P.includeLeft_comp_transDoubleInv
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h
  have hR : (inv P.transDouble).hom ((1 : P.groupRingTop) ⊗ₜ[P.baseRingTop] b)
      = 1 ⊗ₜ[P.baseRing] P.groupOpen.topIso.hom.hom b := by
    have h := congrArg (fun m : P.groupRingTop ⟶ _ => m.hom b) P.includeRight_comp_transDoubleInv
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h
  rw [show (a ⊗ₜ[P.baseRingTop] b : P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)
      = (a ⊗ₜ[P.baseRingTop] (1 : P.groupRingTop)) * ((1 : P.groupRingTop) ⊗ₜ[P.baseRingTop] b) from by
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul],
    map_mul, hL, hR, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]


-- @@ L2372-2385 verbatim
/-- `transDouble` as an `R`-algebra map (target restricted to `R`). -/
noncomputable def transDoubleAlg :
    (P.groupRing ⊗[P.baseRing] P.groupRing) →ₐ[P.baseRing]
      (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) where
  toRingHom := P.transDouble.hom
  commutes' := fun r => by
    have key : P.transDouble.hom
          (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.groupRing) r)
        = algebraMap P.baseRing (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) r := by
      rw [Algebra.TensorProduct.algebraMap_apply, P.transDouble_tmul, map_one,
        show P.groupOpen.topIso.inv.hom (algebraMap P.baseRing P.groupRing r)
          = algebraMap P.baseRing P.groupRingTop r from P.psiAlg.commutes r]
      rfl
    exact key


-- @@ L2387-2400 verbatim
/-- `inv transDouble` as an `R'`-algebra map. -/
noncomputable def transDoubleInvAlg :
    (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) →ₐ[P.baseRingTop]
      (P.groupRing ⊗[P.baseRing] P.groupRing) where
  toRingHom := (inv P.transDouble).hom
  commutes' := fun r => by
    have key : (inv P.transDouble).hom
          (algebraMap P.baseRingTop (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) r)
        = algebraMap P.baseRingTop (P.groupRing ⊗[P.baseRing] P.groupRing) r := by
      rw [Algebra.TensorProduct.algebraMap_apply, P.transDoubleInv_tmul, map_one,
        show P.groupOpen.topIso.hom.hom (algebraMap P.baseRingTop P.groupRingTop r)
          = algebraMap P.baseRingTop P.groupRing r from P.psiAlgInv.commutes r]
      rfl
    exact key


-- @@ L2402-2413 verbatim
/-- The `topIso`-transport of the right-nested triple tensor `A ⊗ (A ⊗ A) → A' ⊗ (A' ⊗ A')`. -/
noncomputable def transTripleAlg :
    (P.groupRing ⊗[P.baseRing] (P.groupRing ⊗[P.baseRing] P.groupRing)) →ₐ[P.baseRing]
      (P.groupRingTop ⊗[P.baseRingTop] (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft (R := P.baseRingTop) (S := P.baseRingTop)
        (A := P.groupRingTop) (B := P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)).restrictScalars
        P.baseRing).comp P.psiAlg)
    (((Algebra.TensorProduct.includeRight (R := P.baseRingTop) (A := P.groupRingTop)
        (B := P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)).restrictScalars
        P.baseRing).comp P.transDoubleAlg)
    (fun _ _ => Commute.all _ _)


-- @@ L2415-2420 verbatim
/-- The transport as a `CommRingCat` morphism. -/
noncomputable def transTriple :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] (P.groupRing ⊗[P.baseRing] P.groupRing))
      ⟶ CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop]
          (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop)) :=
  CommRingCat.ofHom P.transTripleAlg.toRingHom


-- @@ L2422-2433 verbatim
/-- The inverse triple transport. -/
noncomputable def transTripleInvAlg :
    (P.groupRingTop ⊗[P.baseRingTop] (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop))
      →ₐ[P.baseRingTop] (P.groupRing ⊗[P.baseRing] (P.groupRing ⊗[P.baseRing] P.groupRing)) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft (R := P.baseRing) (S := P.baseRing)
        (A := P.groupRing) (B := P.groupRing ⊗[P.baseRing] P.groupRing)).restrictScalars
        P.baseRingTop).comp P.psiAlgInv)
    (((Algebra.TensorProduct.includeRight (R := P.baseRing) (A := P.groupRing)
        (B := P.groupRing ⊗[P.baseRing] P.groupRing)).restrictScalars
        P.baseRingTop).comp P.transDoubleInvAlg)
    (fun _ _ => Commute.all _ _)


-- @@ L2435-2439 verbatim
noncomputable def transTripleInv :
    CommRingCat.of (P.groupRingTop ⊗[P.baseRingTop]
        (P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop))
      ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] (P.groupRing ⊗[P.baseRing] P.groupRing)) :=
  CommRingCat.ofHom P.transTripleInvAlg.toRingHom


-- @@ L2441-2450 verbatim
/-- Elementwise action of `transTriple`: `a ⊗ x ↦ ψ a ⊗ transDouble x`. -/
theorem transTriple_tmul (a : P.groupRing) (x : P.groupRing ⊗[P.baseRing] P.groupRing) :
    P.transTriple.hom (a ⊗ₜ[P.baseRing] x)
      = P.groupOpen.topIso.inv.hom a ⊗ₜ[P.baseRingTop] P.transDouble.hom x := by
  show transTripleAlg G P (a ⊗ₜ[P.baseRing] x) = _
  rw [transTripleAlg, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
  rfl


-- @@ L2452-2462 verbatim
/-- Elementwise action of `transTripleInv`: `a ⊗ x ↦ ψ⁻¹ a ⊗ inv transDouble x`. -/
theorem transTripleInv_tmul (a : P.groupRingTop)
    (x : P.groupRingTop ⊗[P.baseRingTop] P.groupRingTop) :
    P.transTripleInv.hom (a ⊗ₜ[P.baseRingTop] x)
      = P.groupOpen.topIso.hom.hom a ⊗ₜ[P.baseRing] (inv P.transDouble).hom x := by
  show transTripleInvAlg G P (a ⊗ₜ[P.baseRingTop] x) = _
  rw [transTripleInvAlg, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
  rfl


-- @@ L2464-2481 verbatim
/-- `transTripleInv` is a retraction of `transTriple`; hence `transTriple` is a split mono. -/
theorem transTriple_comp_transTripleInv :
    P.transTriple ≫ P.transTripleInv
      = 𝟙 (CommRingCat.of (P.groupRing ⊗[P.baseRing] (P.groupRing ⊗[P.baseRing] P.groupRing))) := by
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x =>
    rw [P.transTriple_tmul, P.transTripleInv_tmul]
    have h1 : P.groupOpen.topIso.hom.hom (P.groupOpen.topIso.inv.hom a) = a :=
      congrArg (fun m : P.groupRing ⟶ P.groupRing => m.hom a) P.groupOpen.topIso.inv_hom_id
    have h2 : (inv P.transDouble).hom (P.transDouble.hom x) = x :=
      congrArg (fun m : CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing)
          ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing) => m.hom x)
        (IsIso.hom_inv_id P.transDouble)
    rw [h1, h2]


-- @@ L2483-2484 verbatim
instance : IsSplitMono P.transTriple :=
  IsSplitMono.mk' ⟨P.transTripleInv, P.transTriple_comp_transTripleInv⟩


-- @@ L2486-2492 verbatim
/-- Elementwise comultiplication intertwining: `transDouble (Δ b) = Δ' (ψ b)`. -/
theorem transDouble_comulAlg (b : P.groupRing) :
    P.transDouble.hom (comulAlg G P b)
      = comulAlgTop G P (P.groupOpen.topIso.inv.hom b) := by
  have h := congrArg (fun m : P.groupRing ⟶ _ => m.hom b) P.groupPatchComul_comp_transDouble
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h


-- @@ L2494-2512 verbatim
/-- **Naturality of `id ⊗ Δ`** under the transports. -/
theorem map_id_comulAlg_comp_transTriple :
    CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing) P.comulAlg).toRingHom
      ≫ P.transTriple
      = P.transDouble ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop) P.comulAlgTop).toRingHom := by
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    AlgHom.coe_toRingHom]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    show P.transTriple.hom (a ⊗ₜ[P.baseRing] comulAlg G P b)
        = Algebra.TensorProduct.map (AlgHom.id P.baseRingTop P.groupRingTop) (comulAlgTop G P)
            (P.transDouble.hom (a ⊗ₜ[P.baseRing] b))
    rw [P.transTriple_tmul, P.transDouble_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, P.transDouble_comulAlg]


-- @@ L2514-2525 verbatim
/-- **Naturality of the associator** under the transports (general middle element). -/
theorem transTriple_assoc_tmul (y : P.groupRing ⊗[P.baseRing] P.groupRing) (b : P.groupRing) :
    P.transTriple.hom (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
        P.groupRing P.groupRing P.groupRing (y ⊗ₜ[P.baseRing] b))
      = Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop P.baseRingTop
          P.groupRingTop P.groupRingTop P.groupRingTop
          (P.transDouble.hom y ⊗ₜ[P.baseRingTop] P.groupOpen.topIso.inv.hom b) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
  | tmul p q =>
    simp only [Algebra.TensorProduct.assoc_tmul, P.transTriple_tmul, P.transDouble_tmul]


-- @@ L2527-2552 verbatim
/-- **Naturality of `(Δ ⊗ id)` followed by the associator** under the transports. -/
theorem map_comulAlg_id_assoc_comp_transTriple :
    CommRingCat.ofHom
        (Algebra.TensorProduct.map (comulAlg G P) (AlgHom.id P.baseRing P.groupRing)).toRingHom
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.groupRing).toAlgHom.toRingHom ≫ P.transTriple
      = P.transDouble ≫ CommRingCat.ofHom
          (Algebra.TensorProduct.map (comulAlgTop G P)
            (AlgHom.id P.baseRingTop P.groupRingTop)).toRingHom
        ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop P.baseRingTop
            P.groupRingTop P.groupRingTop P.groupRingTop).toAlgHom.toRingHom := by
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, AlgHom.coe_toRingHom]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    show P.transTriple.hom ((Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.groupRing).toAlgHom (comulAlg G P a ⊗ₜ[P.baseRing] b))
        = (Algebra.TensorProduct.assoc P.baseRingTop P.baseRingTop P.baseRingTop
            P.groupRingTop P.groupRingTop P.groupRingTop).toAlgHom
          (Algebra.TensorProduct.map (comulAlgTop G P) (AlgHom.id P.baseRingTop P.groupRingTop)
            (P.transDouble.hom (a ⊗ₜ[P.baseRing] b)))
    rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, P.transTriple_assoc_tmul,
      P.transDouble_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      P.transDouble_comulAlg]


-- @@ L2554-2568 verbatim
/-- **Coassociativity, opens `CommRingCat` form** — the transport of `comulTop_coassoc`. -/
theorem groupPatchComul_coassoc :
    P.groupPatchComul ≫ CommRingCat.ofHom (Algebra.TensorProduct.map (comulAlg G P)
          (AlgHom.id P.baseRing P.groupRing)).toRingHom
        ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.groupRing).toAlgHom.toRingHom
      = P.groupPatchComul ≫ CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id P.baseRing P.groupRing) (comulAlg G P)).toRingHom := by
  rw [← cancel_mono P.transTriple]
  simp only [Category.assoc]
  rw [P.map_comulAlg_id_assoc_comp_transTriple, P.map_id_comulAlg_comp_transTriple,
    ← Category.assoc P.groupPatchComul, P.groupPatchComul_comp_transDouble,
    ← Category.assoc P.groupPatchComul, P.groupPatchComul_comp_transDouble]
  simp only [Category.assoc]
  rw [P.comulTop_coassoc]


-- @@ L2570-2579 verbatim
/-- **Coassociativity, opens `AlgHom` form** — the `h_coassoc` field of `Bialgebra.ofAlgHom`. -/
theorem comulAlg_coassoc :
    (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.groupRing).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulAlg G P)
          (AlgHom.id P.baseRing P.groupRing)).comp (comulAlg G P))
      = (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing)
          (comulAlg G P)).comp (comulAlg G P) := by
  refine AlgHom.ext fun x => ?_
  exact congrArg (fun m : P.groupRing ⟶ _ => m.hom x) P.groupPatchComul_coassoc


-- @@ L2581-2581 verbatim
end CoassocTransport


-- @@ L2583-2583 verbatim
/-! ### The opens-level Bialgebra and HopfAlgebra instances -/


-- @@ L2585-2591 verbatim
/-- **The chart Hopf-algebra bialgebra structure** `[Bialgebra R A]` over `R = Γ(S, V)`,
`A = Γ(G.G, G|_V)`, assembled from the opens-level comultiplication `comulAlg` and counit
`counitAlg` with the transported coassociativity `comulAlg_coassoc` and the counit laws
`map_counitAlg_id_comp_comulAlg` / `map_id_counitAlg_comp_comulAlg`. -/
noncomputable instance instBialgebraOpens : Bialgebra P.baseRing P.groupRing :=
  Bialgebra.ofAlgHom (comulAlg G P) (counitAlg G P)
    P.comulAlg_coassoc P.map_counitAlg_id_comp_comulAlg P.map_id_counitAlg_comp_comulAlg


-- @@ L2593-2596 verbatim
/-- The canonical `comulAlgHom` of `instBialgebraOpens` is our `comulAlg`. -/
theorem comulAlgHom_eq_opens :
    Bialgebra.comulAlgHom P.baseRing P.groupRing = comulAlg G P :=
  AlgHom.ext fun _ => rfl


-- @@ L2598-2601 verbatim
/-- The canonical `counitAlgHom` of `instBialgebraOpens` is our `counitAlg`. -/
theorem counitAlgHom_eq_opens :
    Bialgebra.counitAlgHom P.baseRing P.groupRing = counitAlg G P :=
  AlgHom.ext fun _ => rfl


-- @@ L2603-2609 verbatim
/-- **The chart Hopf-algebra structure** `[HopfAlgebra R A]`, upgrading `instBialgebraOpens`
with the opens-level antipode `antipodeAlg` and the two antipode laws
`antipodeLift_comp_comulAlg` / `antipodeLiftR_comp_comulAlg`. -/
noncomputable instance instHopfAlgebraOpens : HopfAlgebra P.baseRing P.groupRing :=
  HopfAlgebra.ofAlgHom (antipodeAlg G P)
    (by rw [comulAlgHom_eq_opens, counitAlgHom_eq_opens]; exact P.antipodeLift_comp_comulAlg)
    (by rw [comulAlgHom_eq_opens, counitAlgHom_eq_opens]; exact P.antipodeLiftR_comp_comulAlg)


-- @@ L2611-2611 verbatim
end AffineChartPatch


-- @@ L2613-2613 verbatim
end FiniteLocallyFreeSubgroup


-- @@ L2615-2615 verbatim
end EllipticCurve


-- @@ L2617-2617 verbatim
end ModularCurves
