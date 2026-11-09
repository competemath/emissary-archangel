import ModularCurves.ForMathlib.SheafCechSheafTerms
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech


-- @@ L4-10 verbatim
/-!
# Ordered sheaf-level Cech terms

This file restricts the sheaf-level Cech terms to strictly increasing tuples.
Sections of an ordered term are identified with ordered families of sections
on the corresponding intersections.
-/


-- @@ L12-12 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite


-- @@ L14-14 verbatim
universe u


-- @@ L16-16 verbatim
namespace TopCat.Sheaf


-- @@ L18-18 verbatim
open AlgebraicGeometry.Scheme.Modules


-- @@ L20-20 verbatim
variable {X : TopCat.{u}}

-- @@ L21-21 verbatim
variable (F : Sheaf AddCommGrpCat.{u} X) {ι : Type u}

-- @@ L22-22 verbatim
variable [LinearOrder ι]

-- @@ L23-23 verbatim
variable (U : ι → Opens X) (n : ℕ)


-- @@ L25-30 verbatim
/-- The restriction-pushforward factor indexed by a strictly increasing
tuple. -/
noncomputable abbrev orderedCechTermFactor
    (i : OrderedCechIndex ι n) :
    Sheaf AddCommGrpCat.{u} X :=
  cechTermFactor F U n i.1


-- @@ L32-34 verbatim
/-- Degree `n` of the ordered sheaf-level Cech resolution. -/
noncomputable def orderedCechTerm : Sheaf AddCommGrpCat.{u} X :=
  ∏ᶜ orderedCechTermFactor F U n


-- @@ L36-42 verbatim
private noncomputable def orderedCechTermFactorSectionsIso
    (V : Opens X) (i : OrderedCechIndex ι n) :
    (orderedCechTermFactor F U n i).obj.obj (op V) ≅
      F.obj.obj
        (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i.1 k))) :=
  eqToIso (by
    rw [toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])


-- @@ L44-49 verbatim
private noncomputable def orderedCechTermForgetDiagramIso :
    Discrete.functor (orderedCechTermFactor F U n) ⋙
        forget AddCommGrpCat X ≅
      Discrete.functor fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj :=
  Discrete.natIso (fun _ => Iso.refl _)


-- @@ L51-62 verbatim
private noncomputable def orderedCechTermForgetIso :
    (orderedCechTerm F U n).obj ≅
      ∏ᶜ fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj := by
  letI : HasLimit
      (Discrete.functor (orderedCechTermFactor F U n) ⋙
        forget AddCommGrpCat X) :=
    hasLimit_of_iso (orderedCechTermForgetDiagramIso F U n).symm
  exact
    preservesLimitIso (forget AddCommGrpCat X)
        (Discrete.functor (orderedCechTermFactor F U n)) ≪≫
      HasLimit.isoOfNatIso (orderedCechTermForgetDiagramIso F U n)


-- @@ L64-130 verbatim
private theorem orderedCechTermForgetIso_hom_π
    (i : OrderedCechIndex ι n) :
    (orderedCechTermForgetIso F U n).hom ≫
        Pi.π
          (fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj) i =
      (Pi.π (orderedCechTermFactor F U n) i).hom := by
  change
    (orderedCechTermForgetIso F U n).hom ≫
        limit.π
          (Discrete.functor fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj) ⟨i⟩ =
      (forget AddCommGrpCat X).map
        (limit.π
          (Discrete.functor (orderedCechTermFactor F U n)) ⟨i⟩)
  letI : HasLimit
      (Discrete.functor (orderedCechTermFactor F U n) ⋙
        forget AddCommGrpCat X) :=
    hasLimit_of_iso (orderedCechTermForgetDiagramIso F U n).symm
  have hnat :
      (HasLimit.isoOfNatIso
          (orderedCechTermForgetDiagramIso F U n)).hom ≫
          limit.π
            (Discrete.functor fun i : OrderedCechIndex ι n =>
              (orderedCechTermFactor F U n i).obj) ⟨i⟩ =
        limit.π
          (Discrete.functor (orderedCechTermFactor F U n) ⋙
            forget AddCommGrpCat X) ⟨i⟩ := by
    have hbase :
        (HasLimit.isoOfNatIso
            (orderedCechTermForgetDiagramIso F U n)).hom ≫
            limit.π
              (Discrete.functor fun i : OrderedCechIndex ι n =>
                (orderedCechTermFactor F U n i).obj) ⟨i⟩ =
          limit.π
              (Discrete.functor (orderedCechTermFactor F U n) ⋙
                forget AddCommGrpCat X) ⟨i⟩ ≫
            (orderedCechTermForgetDiagramIso F U n).hom.app ⟨i⟩ :=
      HasLimit.isoOfNatIso_hom_π
        (orderedCechTermForgetDiagramIso F U n) ⟨i⟩
    have hcomp :
        limit.π
              (Discrete.functor (orderedCechTermFactor F U n) ⋙
                forget AddCommGrpCat X) ⟨i⟩ ≫
            (orderedCechTermForgetDiagramIso F U n).hom.app ⟨i⟩ =
          limit.π
            (Discrete.functor (orderedCechTermFactor F U n) ⋙
              forget AddCommGrpCat X) ⟨i⟩ := by
      exact Category.comp_id _
    exact hbase.trans hcomp
  have hpreserves :=
    preservesLimitIso_hom_π
      (forget AddCommGrpCat X)
      (Discrete.functor (orderedCechTermFactor F U n)) ⟨i⟩
  change
    (preservesLimitIso (forget AddCommGrpCat X)
        (Discrete.functor (orderedCechTermFactor F U n))).hom ≫
        ((HasLimit.isoOfNatIso
          (orderedCechTermForgetDiagramIso F U n)).hom ≫
          limit.π
            (Discrete.functor fun i : OrderedCechIndex ι n =>
              (orderedCechTermFactor F U n i).obj) ⟨i⟩) =
      (forget AddCommGrpCat X).map
        (limit.π
          (Discrete.functor (orderedCechTermFactor F U n)) ⟨i⟩)
  rw [hnat]
  exact hpreserves


-- @@ L132-139 verbatim
private noncomputable def orderedCechTermForgetSectionsIso
    (V : Opens X) :
    (orderedCechTerm F U n).obj.obj (op V) ≅
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).obj
        (∏ᶜ fun i : OrderedCechIndex ι n =>
          (orderedCechTermFactor F U n i).obj) :=
  ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).mapIso
    (orderedCechTermForgetIso F U n)


-- @@ L141-148 verbatim
private noncomputable def orderedCechTermEvaluationDiagramIso
    (V : Opens X) :
    (Discrete.functor fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V) ≅
      Discrete.functor fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj.obj (op V) :=
  Discrete.natIso (fun _ => Iso.refl _)


-- @@ L150-169 verbatim
private noncomputable def orderedCechTermEvaluationIso
    (V : Opens X) :
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).obj
        (∏ᶜ fun i : OrderedCechIndex ι n =>
          (orderedCechTermFactor F U n i).obj) ≅
      ∏ᶜ fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj.obj (op V) := by
  letI : HasLimit
      ((Discrete.functor fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) :=
    hasLimit_of_iso
      (orderedCechTermEvaluationDiagramIso F U n V).symm
  exact
    preservesLimitIso
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
        (Discrete.functor fun i : OrderedCechIndex ι n =>
          (orderedCechTermFactor F U n i).obj) ≪≫
      HasLimit.isoOfNatIso
        (orderedCechTermEvaluationDiagramIso F U n V)


-- @@ L171-235 verbatim
private theorem orderedCechTermEvaluationIso_hom_π
    (V : Opens X) (i : OrderedCechIndex ι n) :
    (orderedCechTermEvaluationIso F U n V).hom ≫
        Pi.π
          (fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj.obj (op V)) i =
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
        (Pi.π
          (fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj) i) := by
  change
    (orderedCechTermEvaluationIso F U n V).hom ≫
        limit.π
          (Discrete.functor fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj.obj (op V)) ⟨i⟩ =
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
        (limit.π
          (Discrete.functor fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj) ⟨i⟩)
  letI : HasLimit
      ((Discrete.functor fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) :=
    hasLimit_of_iso
      (orderedCechTermEvaluationDiagramIso F U n V).symm
  have hnat :
      (HasLimit.isoOfNatIso
          (orderedCechTermEvaluationDiagramIso F U n V)).hom ≫
          limit.π
            (Discrete.functor fun i : OrderedCechIndex ι n =>
              (orderedCechTermFactor F U n i).obj.obj (op V)) ⟨i⟩ =
        limit.π
          ((Discrete.functor fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj) ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) ⟨i⟩ := by
    calc
      _ = limit.π
            ((Discrete.functor fun i : OrderedCechIndex ι n =>
              (orderedCechTermFactor F U n i).obj) ⋙
              (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) ⟨i⟩ ≫
          (orderedCechTermEvaluationDiagramIso F U n V).hom.app ⟨i⟩ :=
        HasLimit.isoOfNatIso_hom_π
          (orderedCechTermEvaluationDiagramIso F U n V) ⟨i⟩
      _ = _ := Category.comp_id _
  have hpreserves :=
    preservesLimitIso_hom_π
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
      (Discrete.functor fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj) ⟨i⟩
  change
    (preservesLimitIso
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
        (Discrete.functor fun i : OrderedCechIndex ι n =>
          (orderedCechTermFactor F U n i).obj)).hom ≫
        ((HasLimit.isoOfNatIso
          (orderedCechTermEvaluationDiagramIso F U n V)).hom ≫
          limit.π
            (Discrete.functor fun i : OrderedCechIndex ι n =>
              (orderedCechTermFactor F U n i).obj.obj (op V)) ⟨i⟩) =
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
        (limit.π
          (Discrete.functor fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj) ⟨i⟩)
  rw [hnat]
  exact hpreserves


-- @@ L237-243 verbatim
private noncomputable def orderedCechTermSectionsRawIso
    (V : Opens X) :
    (orderedCechTerm F U n).obj.obj (op V) ≅
      ∏ᶜ fun i : OrderedCechIndex ι n =>
        (orderedCechTermFactor F U n i).obj.obj (op V) :=
  orderedCechTermForgetSectionsIso F U n V ≪≫
    orderedCechTermEvaluationIso F U n V


-- @@ L245-255 verbatim
@[reassoc]
private theorem orderedCechTermSectionsRawIso_hom_π
    (V : Opens X) (i : OrderedCechIndex ι n) :
    (orderedCechTermSectionsRawIso F U n V).hom ≫
        Pi.π
          (fun i : OrderedCechIndex ι n =>
            (orderedCechTermFactor F U n i).obj.obj (op V)) i =
      (Pi.π (orderedCechTermFactor F U n) i).hom.app (op V) := by
  rw [orderedCechTermSectionsRawIso, Iso.trans_hom,
    Category.assoc, orderedCechTermEvaluationIso_hom_π]
  exact congr_app (orderedCechTermForgetIso_hom_π F U n i) (op V)


-- @@ L257-264 verbatim
private noncomputable def orderedCechTermSectionsProductIso
    (V : Opens X) :
    (orderedCechTerm F U n).obj.obj (op V) ≅
      ∏ᶜ fun i : OrderedCechIndex ι n =>
        F.obj.obj
          (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i.1 k))) :=
  orderedCechTermSectionsRawIso F U n V ≪≫
    Pi.mapIso (orderedCechTermFactorSectionsIso F U n V)


-- @@ L266-279 verbatim
private theorem orderedCechTermSectionsProductIso_hom_π
    (V : Opens X) (i : OrderedCechIndex ι n) :
    (orderedCechTermSectionsProductIso F U n V).hom ≫
        Pi.π
          (fun i : OrderedCechIndex ι n =>
            F.obj.obj
              (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i.1 k)))) i =
      (Pi.π (orderedCechTermFactor F U n) i).hom.app (op V) ≫
        (orderedCechTermFactorSectionsIso F U n V i).hom := by
  rw [orderedCechTermSectionsProductIso, Iso.trans_hom,
    Category.assoc, Pi.mapIso_hom_π]
  exact congrArg
    (fun k => k ≫ (orderedCechTermFactorSectionsIso F U n V i).hom)
    (orderedCechTermSectionsRawIso_hom_π F U n V i)


-- @@ L281-292 verbatim
/-- Sections of an ordered sheaf-level Cech term are ordered families
of sections on tuple intersections. -/
noncomputable def orderedCechTermSectionsAddEquiv
    (V : Opens X) :
    (orderedCechTerm F U n).obj.obj (op V) ≃+
      ∀ i : OrderedCechIndex ι n,
        F.obj.obj
          (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i.1 k))) :=
  ((orderedCechTermSectionsProductIso F U n V) ≪≫
    AddCommGrpCat.productIsoPi fun i : OrderedCechIndex ι n =>
      F.obj.obj
        (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i.1 k)))).addCommGroupIsoToAddEquiv


-- @@ L294-315 verbatim
/-- The component of `orderedCechTermSectionsAddEquiv` at an ordered
tuple is restriction to the corresponding intersection. -/
theorem orderedCechTermSectionsAddEquiv_apply
    (V : Opens X) (x : (orderedCechTerm F U n).obj.obj (op V))
    (i : OrderedCechIndex ι n) :
    orderedCechTermSectionsAddEquiv F U n V x i =
      ((eqToIso (by
          rw [toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
        (orderedCechTermFactor F U n i).obj.obj (op V) ≅
          F.obj.obj
            (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i.1 k)))).hom
        ((Pi.π (orderedCechTermFactor F U n) i).hom.app (op V) x) := by
  rw [show orderedCechTermSectionsAddEquiv F U n V x i =
      (AddCommGrpCat.productIsoPi
        (fun i : OrderedCechIndex ι n =>
          F.obj.obj
            (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i.1 k))))).hom
          ((orderedCechTermSectionsProductIso F U n V).hom x) i
      from rfl,
    AddCommGrpCat.productIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom
    (orderedCechTermSectionsProductIso_hom_π F U n V i) x


-- @@ L317-317 verbatim
end TopCat.Sheaf
