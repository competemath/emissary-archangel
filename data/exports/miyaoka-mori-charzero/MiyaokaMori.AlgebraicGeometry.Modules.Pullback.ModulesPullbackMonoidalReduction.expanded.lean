import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPreservesColimits
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal


-- @@ L6-31 verbatim
/-! # Reducing the monoidal structure of pullback to the presheaf level

Let `f : X ⟶ Y` be a morphism of schemes. If the pullback of presheaves of modules
`PresheafOfModules.pullback (f.toRingCatSheafHom).hom` is a strong monoidal functor, then so is
the pullback of sheaves of modules `AlgebraicGeometry.Scheme.Modules.pullback f`; in particular
one obtains the canonical isomorphism `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` of Stacks 01CD (the inverse of
the `μIso` of the monoidal functor) together with associators, unitors and naturality.

Proof:
1. The monoidal structure on `X.Modules` is defined as the monoidal localization
   `CategoryTheory.LocalizedMonoidal` of sheafification; the two types are definitionally equal
   (`localizedMonoidal_eq_modules` is `rfl`), and the sheafification functor is strong monoidal for
   this structure (Mathlib's `toMonoidalCategory` instance in `Localization/Monoidal/Basic.lean`).
2. Mathlib's `SheafOfModules.sheafificationCompPullback` gives the lifting isomorphism
   `L_Y ⋙ f^*_{sh} ≅ f^*_{pre} ⋙ L_X`, registered as a `Localization.Lifting` instance
   (`liftingPullback`).
3. Composites of strong monoidal functors are strong monoidal (`Functor.Monoidal.comp'`; Mathlib
   only has the lax and oplax composition instances, so this is obtained from the lax composite
   with `ε`, `μ` isomorphisms via `Functor.Monoidal.ofLaxMonoidal`).
4. Mathlib's `Localization.Monoidal.functorMonoidalOfComp`: a strong monoidal functor lifted along a
   monoidal localization passes its strong monoidal structure to the lifted functor, so
   `Scheme.Modules.pullback f` is strong monoidal.

References: Stacks 01CD; Mathlib `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`,
`CategoryTheory/Localization/Monoidal/Functor.lean`.
-/


-- @@ L33-33 verbatim
set_option autoImplicit false

-- @@ L34-34 verbatim
set_option maxHeartbeats 1000000

-- @@ L35-35 verbatim
set_option backward.isDefEq.respectTransparency.types false

-- @@ L36-36 verbatim
universe u

-- @@ L37-37 verbatim
open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

-- @@ L38-38 verbatim
open scoped AlgebraicGeometry


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-52 verbatim
/-- The composite of strong monoidal functors is strong monoidal (Mathlib only has the lax and oplax
composition instances). -/
noncomputable instance CategoryTheory.Functor.Monoidal.comp'
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] : (F ⋙ G).Monoidal := by
  have h1 : IsIso (Functor.LaxMonoidal.ε (F ⋙ G)) := by
    rw [Functor.LaxMonoidal.comp_ε]; infer_instance
  have h2 : ∀ Z W : C, IsIso (Functor.LaxMonoidal.μ (F ⋙ G) Z W) := fun Z W => by
    rw [Functor.LaxMonoidal.comp_μ]; infer_instance
  exact Functor.Monoidal.ofLaxMonoidal _


-- @@ L54-54 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L56-56 verbatim
variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)


-- @@ L58-67 verbatim
/-- The sheafification functor, with target written as `LocalizedMonoidal` (the one used for the
monoidal structure of `Y.Modules`). -/
abbrev LY (Y : AlgebraicGeometry.Scheme.{u}) :
    _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj ⥤
      CategoryTheory.LocalizedMonoidal
        (_root_.PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj))
        (sheafificationW Y) (sheafificationUnitIso Y) :=
  CategoryTheory.Localization.Monoidal.toMonoidalCategory
    (_root_.PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj))
    (sheafificationW Y) (sheafificationUnitIso Y)


-- @@ L69-76 verbatim
abbrev LX (X : AlgebraicGeometry.Scheme.{u}) :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      CategoryTheory.LocalizedMonoidal
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
        (sheafificationW X) (sheafificationUnitIso X) :=
  CategoryTheory.Localization.Monoidal.toMonoidalCategory
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (sheafificationW X) (sheafificationUnitIso X)


-- @@ L78-82 verbatim
/-- The type carrying the monoidal structure of `Y.Modules` is the monoidal localization of
sheafification (a definitional equality). -/
theorem localizedMonoidal_eq_modules : CategoryTheory.LocalizedMonoidal
        (_root_.PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj))
        (sheafificationW Y) (sheafificationUnitIso Y) = Y.Modules := rfl


-- @@ L84-90 verbatim
set_option maxSynthPendingDepth 3 in
/-- The pushforward of presheaves of modules is a right adjoint (a Mathlib instance; on the site of
a scheme it is found only with relaxed defeq transparency). -/
theorem presheaf_pushforward_isRightAdjoint :
    (_root_.PresheafOfModules.pushforward.{u} (f.toRingCatSheafHom).hom).IsRightAdjoint :=
  inferInstanceAs ((_root_.PresheafOfModules.pushforward.{u}
    (F := TopologicalSpace.Opens.map f.base) (f.toRingCatSheafHom).hom).IsRightAdjoint)


-- @@ L92-93 verbatim
/-- The lifting isomorphism through sheafification (Mathlib `SheafOfModules.sheafificationCompPullback`). -/
noncomputable def liftIso := SheafOfModules.sheafificationCompPullback.{u} f.toRingCatSheafHom


-- @@ L95-99 verbatim
/-- The sheafification functor with target written as `Z.Modules` (the same term as `LX` / `LY`; only
the spelling of the `MonoidalCategory` instance in the statement differs). -/
abbrev sheafify (Z : AlgebraicGeometry.Scheme.{u}) :
    _root_.PresheafOfModules.{u} Z.ringCatSheaf.obj ⥤ Z.Modules :=
  _root_.PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)


-- @@ L101-103 verbatim
noncomputable instance sheafify_monoidal (Z : AlgebraicGeometry.Scheme.{u}) :
    (sheafify Z).Monoidal :=
  inferInstanceAs ((LX Z).Monoidal)


-- @@ L105-108 verbatim
noncomputable instance sheafify_isLocalization (Z : AlgebraicGeometry.Scheme.{u}) :
    (sheafify Z).IsLocalization (sheafificationW Z) :=
  inferInstanceAs ((_root_.PresheafOfModules.sheafification
    (𝟙 Z.ringCatSheaf.obj)).IsLocalization (sheafificationW Z))


-- @@ L110-113 verbatim
/-- The pullback of presheaves of modules (with the target sheaf of rings spelled `X.ringCatSheaf.obj`). -/
noncomputable abbrev pullbackPre :
    _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj ⥤ _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  _root_.PresheafOfModules.pullback.{u} (R := X.ringCatSheaf.obj) (f.toRingCatSheafHom).hom


-- @@ L115-119 verbatim
/-- Sheafification lifts the pullback of presheaves of modules to the pullback of sheaves of modules. -/
noncomputable instance liftingPullback :
    CategoryTheory.Localization.Lifting (sheafify Y) (sheafificationW Y)
      (pullbackPre f ⋙ sheafify X) (AlgebraicGeometry.Scheme.Modules.pullback f) :=
  ⟨liftIso f⟩


-- @@ L121-129 verbatim
/-- **Reduction theorem**: if the pullback `PresheafOfModules.pullback` of presheaves of modules is
**strong** monoidal, then so is the pullback `Scheme.Modules.pullback f` of sheaves of modules;
hence `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` holds together with associators, unitors and naturality. -/
@[instance_reducible]
noncomputable def pullbackMonoidalOfPresheafMonoidal [(pullbackPre f).Monoidal] :
    (AlgebraicGeometry.Scheme.Modules.pullback f).Monoidal :=
  CategoryTheory.Localization.Monoidal.functorMonoidalOfComp
    (sheafify Y) (sheafificationW Y)
    (AlgebraicGeometry.Scheme.Modules.pullback f) (pullbackPre f ⋙ sheafify X)


-- @@ L131-141 verbatim
/-- Direct corollary of the reduction theorem: under the same hypothesis, the canonical isomorphism
`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` of Stacks 01CD (the inverse of the `μIso` of the monoidal functor). -/
noncomputable def pullbackTensorObjIsoOfPresheafMonoidal [(pullbackPre f).Monoidal]
    (M N : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (CategoryTheory.MonoidalCategoryStruct.tensorObj M N) ≅
      CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) :=
  letI := pullbackMonoidalOfPresheafMonoidal f
  (CategoryTheory.Functor.Monoidal.μIso (AlgebraicGeometry.Scheme.Modules.pullback f) M N).symm


-- @@ L143-143 verbatim
end AlgebraicGeometry.Scheme.Modules

-- @@ L144-144 verbatim
end
