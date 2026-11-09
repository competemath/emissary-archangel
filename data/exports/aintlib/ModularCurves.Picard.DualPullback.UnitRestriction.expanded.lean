import ModularCurves.Picard.DualPullback.UnitSquare


-- @@ L3-7 verbatim
/-!
# Restriction of the local structure-module pullback

The canonical local pullback of the structure module is compatible with shrinking opens.
-/


-- @@ L9-9 verbatim
universe u v


-- @@ L11-11 verbatim
open AlgebraicGeometry CategoryTheory




-- @@ L15-15 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L17-47 verbatim
theorem openPullbackRestrictIso_hom_app_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) (M : U.toScheme.Modules) :
    (openPullbackRestrictIso f i).hom.app M =
      (pullback (f ∣_ V)).map
          ((restrictFunctorIsoPullback
            (X.homOfLE (leOfHom i))).hom.app M) ≫
        (pullbackSquareIso (f ∣_ V) (X.homOfLE (leOfHom i))
          (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
          (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app M ≫
        (restrictFunctorIsoPullback
          (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
            ((pullback (f ∣_ U)).obj M) := by
  simp only [openPullbackRestrictIso, pullbackSquareIso, Iso.trans_hom,
    Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  let a := (pullback (f ∣_ V)).map
    ((restrictFunctorIsoPullback (X.homOfLE (leOfHom i))).hom.app M)
  let b := (pullbackComp (f ∣_ V)
    (X.homOfLE (leOfHom i))).hom.app M
  let c := (pullbackCongr
    (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app M
  let d := (pullbackComp
    (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)).inv.app M
  let e := (restrictFunctorIsoPullback
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
      ((pullback (f ∣_ U)).obj M)
  change a ≫ b ≫ c ≫ d ≫ e = a ≫ (b ≫ c ≫ d) ≫ e
  simp only [Category.assoc]


-- @@ L49-49 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L51-51 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L54-54 verbatim
namespace CategoryTheory


-- @@ L56-65 verbatim
theorem reassoc_three_tailG {C : Type u} [Category.{v} C]
    {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E}
    {d : E ⟶ F} {e : F ⟶ G} {z : A ⟶ G}
    (h : a ≫ b ≫ (c ≫ d ≫ e) = z) :
    (a ≫ b ≫ c) ≫ d ≫ e = z := by
  calc
    (a ≫ b ≫ c) ≫ d ≫ e = a ≫ b ≫ (c ≫ d ≫ e) := by
      simp only [Category.assoc]
    _ = z := h


-- @@ L67-67 verbatim
end CategoryTheory


-- @@ L69-69 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L71-71 verbatim
variable {X Y : Scheme.{u}}


-- @@ L73-77 verbatim
noncomputable def localPullbackUnitRestrictSourceG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) : (f ⁻¹ᵁ V : Scheme).Modules :=
  (pullback (f ∣_ V)).obj
    ((restrictFunctor (X.homOfLE (leOfHom i))).obj
      (unitObj U))


-- @@ L79-81 verbatim
noncomputable def localPullbackUnitRestrictTargetG (f : Y ⟶ X)
    {U V : X.Opens} (_i : V ⟶ U) : (f ⁻¹ᵁ V : Scheme).Modules :=
  unitObj (f ⁻¹ᵁ V)


-- @@ L83-93 verbatim
noncomputable def localPullbackUnitRestrictLeftG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictSourceG f i ⟶
      localPullbackUnitRestrictTargetG f i :=
  (openPullbackRestrictIso f i).hom.app
        (unitObj U) ≫
      (restrictFunctor
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
          (localPullbackUnitIso f U).hom ≫
      (overRestrictUnitIso
        ((TopologicalSpace.Opens.map f.base).map i)).hom


-- @@ L95-100 verbatim
noncomputable def localPullbackUnitRestrictRightG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictSourceG f i ⟶
      localPullbackUnitRestrictTargetG f i :=
  (pullback (f ∣_ V)).map (overRestrictUnitIso i).hom ≫
    (localPullbackUnitIso f V).hom


-- @@ L102-102 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L104-104 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L107-107 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L109-109 verbatim
variable {X Y : Scheme.{u}}


-- @@ L111-128 verbatim
noncomputable def localPullbackUnitRestrictExpandedLeftG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictSourceG f i ⟶
      localPullbackUnitRestrictTargetG f i :=
  (pullback (f ∣_ V)).map
        ((restrictFunctorIsoPullback
          (X.homOfLE (leOfHom i))).hom.app (unitObj U)) ≫
      (pullbackSquareIso (f ∣_ V) (X.homOfLE (leOfHom i))
        (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
        (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app (unitObj U) ≫
      (restrictFunctorIsoPullback
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
          ((pullback (f ∣_ U)).obj (unitObj U)) ≫
      (restrictFunctor
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
          (localPullbackUnitIso f U).hom ≫
      (overRestrictUnitIso
        ((TopologicalSpace.Opens.map f.base).map i)).hom


-- @@ L130-137 verbatim
theorem localPullbackUnitRestrictLeft_eq_expandedG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictLeftG f i =
      localPullbackUnitRestrictExpandedLeftG f i := by
  unfold localPullbackUnitRestrictLeftG
    localPullbackUnitRestrictExpandedLeftG
  rw [openPullbackRestrictIso_hom_app_eq]
  exact CategoryTheory.reassoc_three_tailG rfl


-- @@ L139-139 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L141-141 verbatim
open AlgebraicGeometry CategoryTheory Opposite



-- @@ L144-144 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L146-146 verbatim
variable {X Y : Scheme.{u}}


-- @@ L148-179 verbatim
theorem localPullbackUnitRestrictExpandedLeft_eq_rightG
    (f : Y ⟶ X) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictExpandedLeftG f i =
      localPullbackUnitRestrictRightG f i := by
  unfold localPullbackUnitRestrictExpandedLeftG
    localPullbackUnitRestrictRightG
  rw [localPullbackUnitIso_hom_eqP, localPullbackUnitIso_hom_eqP]
  rw [overRestrictUnitIso_eq_restrictUnitIsoP,
    overRestrictUnitIso_eq_restrictUnitIsoP]
  unfold localPullbackUnitRestrictSourceG
    localPullbackUnitRestrictTargetG
  let a := (pullback (f ∣_ V)).map
    ((restrictFunctorIsoPullback
      (X.homOfLE (leOfHom i))).hom.app (unitObj U))
  let b := (pullbackSquareIso (f ∣_ V) (X.homOfLE (leOfHom i))
    (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
    (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app (unitObj U)
  let c := (restrictFunctorIsoPullback
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
      ((pullback (f ∣_ U)).obj (unitObj U))
  let d := (restrictFunctor
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
      (pullbackUnitIso (f ∣_ U)).hom
  let e := (restrictUnitIso
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).hom
  let z := (pullback (f ∣_ V)).map
      (restrictUnitIso (X.homOfLE (leOfHom i))).hom ≫
    (pullbackUnitIso (f ∣_ V)).hom
  have hraw : a ≫ b ≫ (c ≫ d ≫ e) = z :=
    unitNat_rawStage0_eq_targetG f i
  change a ≫ b ≫ c ≫ d ≫ e = z
  exact hraw


-- @@ L181-181 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L183-183 verbatim
open AlgebraicGeometry CategoryTheory



-- @@ L186-186 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L188-188 verbatim
variable {X Y : Scheme.{u}}


-- @@ L190-195 verbatim
theorem localPullbackUnitIso_restrict_homG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictLeftG f i =
      localPullbackUnitRestrictRightG f i :=
  (localPullbackUnitRestrictLeft_eq_expandedG f i).trans
    (localPullbackUnitRestrictExpandedLeft_eq_rightG f i)


-- @@ L197-197 verbatim
end AlgebraicGeometry.Scheme.Modules
