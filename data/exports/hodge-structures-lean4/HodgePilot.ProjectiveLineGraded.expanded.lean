import HodgePilot.TwoChartResidue
import HodgePilot.ProjectiveLineUnits


-- @@ L4-81 verbatim
/-! # The projective line: the graded edge class of `dz/z` in `H¹(ℙ¹, Ω¹-sheaf)`

Golden-path wave 3 (the G3-graded rung).  This module connects the ring-level
two-chart residue of `HodgePilot.TwoChartResidue` to the sheaf cohomology of
the actual projective line `p1 = Proj ℂ[X₀, X₁]` of
`HodgePilot.ProjectiveLine`, through Riou's Mayer–Vietoris long exact
sequence in sheaf cohomology.

**Part 1 (generic, any small site).**  Degree-0 sheaf cohomology at the
free-Yoneda anchor of Mathlib's `Sheaf.H'` is sections:
`h0SectionsEquiv : Ext (freeYonedaSheaf J U) F 0 ≃+ F.obj.obj (op U)`,
natural in `U` (`h0ToSections_natural`), and the anchor at a terminal object
is the constant-`ULift ℤ` anchor of Mathlib's `Sheaf.H`
(`freeYonedaTopSheafIso`, `hPrimeTopEquivH`).  This settles, for this
development, the two open ends recorded as CYC-G33: `H'`-degree-0-is-sections,
and the `H'(⊤)`-to-`Sheaf.H` anchor re-isomorphism (Mathlib's own `TODO` in
`CategoryTheory/Sites/SheafCohomology/Basic.lean`).

**Part 2 (the projective line).**  The degree-1 de Rham sheaf on the
underlying space of `p1` (`DeRhamSheaf.deRhamSheafSpace (cRingHom structMor) 1`
— sections on affine opens are the presented Kähler 1-forms of the section
rings, with no sheafification anywhere) is accessed through a single presheaf
morphism `secComparison` extending the dense-subsite equivalence unit along
`Functor.IsCoverDense.sheafHom`; its components at the two standard charts and
at their overlap are isomorphisms.  The chart section rings are polynomial
rings by wave 2 (`chartPolyEquiv`), and the overlap carries the two
`ℂ`-algebra maps `overlapAlgHom : ℂ[T;T⁻¹] →ₐ[ℂ] Γ(U₀ ⊓ U₁)` (the Laurent
coordinate, keyed at wave 1's literal overlap unit) and `overlapInvAlgHom`
(the evaluation `X₀ ↦ 1, X₁ ↦ T`), inverse to it on the relevant elements.

**Part 3 (the theorem).**  `edgeClassGraded`, the image of the ring-level
`dz/z` under the connecting map `δ` of the Mayer–Vietoris sequence for the
square `(U₀, U₁)`, is **nonzero** in `H¹` of the degree-1 de Rham sheaf in the
sense of Mathlib's `Sheaf.H'` (`edgeClassGraded_ne_zero`), and, transported
along the terminal-anchor re-isomorphism of Part 1, nonzero in the sense of
Mathlib's `Sheaf.H` (`edgeClassH_ne_zero`).  The proof needs **no acyclicity
anywhere**: exactness of the Mayer–Vietoris sequence (`ker δ = im fromBiprod`)
reduces nonvanishing to the ring-level statement that the residue functional
kills every form extending to a chart while taking the value `1` on `dz/z`
(`HodgePilot.TwoChartResidue`).

**Part 4 (falsifier suite and the honest walls).**  A negative control
(`edgeRoute_restriction_eq_zero`, `edgeRoute_dz_eq_zero`: a form extending to
a chart maps to zero under the same `δ`-route), `rfl`-receipts pinning the
module's subject to `TwoChartResidue`'s literal `chartEmbed`/`chartDifference`
and to wave 1's literal glue unit `overlapUnit`, and two **named unproved
`Prop`s** in registry style (stated, never proved, never assumed, never used):
`GradedTruncationDetection` (the `σ≥1`-truncation bridge between the degree-2
hypercohomology graded level and `H¹` of the degree-1 sheaf — the
`Λ²Ω¹`-vanishing sub-joint lives here and is deliberately not attempted) and
`InterferenceExclusion` (vanishing of the image of `H¹(O) → H¹(Ω¹)` under the
exterior differential — the honest wall of the recon; nothing here starts it).

## Claim discipline

The nonvanishing proved here is exactly: **the edge class of `dz/z` is a
nonzero element of `H¹` of the degree-1 de Rham sheaf of `p1` in the sense of
Mathlib's `Sheaf.H'` and `Sheaf.H`** (the latter along the anchor
re-isomorphism of Part 1).  No comparison with any other cohomology theory —
and no comparison between this `H¹` and the `σ≥1`-graded piece of the degree-2
de Rham hypercohomology — is stated, implied, or approached; the latter is
exactly the named unproved `Prop` `GradedTruncationDetection`.  No acyclicity,
no Čech-to-derived comparison, and no degeneration statement of any kind
appears here.  Nothing here makes the Hodge conjecture statable.

## Credits

The Mayer–Vietoris square and its long exact sequence in sheaf cohomology are
Joël Riou's (`Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`,
`Mathlib/Topology/Sheaves/MayerVietoris.lean`), as are `Sheaf.H`/`Sheaf.H'`
and the `Ext` infrastructure; the dense-subsite `sheafHom` extension is from
Mathlib's cover-dense machinery; `Proj`, its charts and `awayToSection` are
Andrew Yang's; homogeneous localizations are Jujian Zhang's and Eric Wieser's;
the ring-level residue input is `HodgePilot.TwoChartResidue` on
`HodgePilot.ContentAnchor`'s Euler-derivation residue; the object, divisor
datum, and chart isomorphisms are `HodgePilot.ProjectiveLine` (wave 1) and
`HodgePilot.ProjectiveLineUnits` (wave 2).
-/


-- @@ L83-83 verbatim
set_option maxHeartbeats 1000000

-- @@ L84-84 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L86-86 verbatim
noncomputable section


-- @@ L88-88 verbatim
namespace HodgePilot


-- @@ L90-90 verbatim
namespace ProjectiveLineGraded


-- @@ L92-92 verbatim
open CategoryTheory CategoryTheory.Limits Opposite Abelian


-- @@ L94-100 verbatim
/-! ## Part 1. Degree-0 sheaf cohomology at the free-Yoneda anchor is sections

Generic over any small site.  Mathlib's `Sheaf.H' F n U` is by definition the
`Ext`-group from the sheafification of the free abelian presheaf on
`yoneda.obj U`; in degree 0 this is the sections of `F` over `U`, naturally in
`U`.  This is the `H'`-degree-0-is-sections identification recorded as
unverified in CYC-G33 (and as a `TODO` in Mathlib itself). -/


-- @@ L102-102 verbatim
section SectionsLayer


-- @@ L104-104 verbatim
universe u


-- @@ L106-106 verbatim
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

-- @@ L107-107 verbatim
variable [HasSheafify J AddCommGrpCat.{u}]


-- @@ L109-112 verbatim
/-- The free abelian presheaf on the Yoneda presheaf of `U`, spelled exactly
as inside Mathlib's `Sheaf.cohomologyPresheafFunctor`. -/
@[reducible] def freeYonedaPresheaf (U : C) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda.obj U ⋙ AddCommGrpCat.free


-- @@ L114-118 verbatim
/-- The free abelian sheaf on `yoneda.obj U` — the per-object anchor of
Mathlib's `Sheaf.H'`. -/
@[reducible] def freeYonedaSheaf (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) : Sheaf J AddCommGrpCat.{u} :=
  (presheafToSheaf J AddCommGrpCat.{u}).obj (freeYonedaPresheaf U)


-- @@ L120-124 verbatim
/-- Functoriality of the free-Yoneda presheaf, spelled exactly as inside
`Sheaf.cohomologyPresheafFunctor`. -/
@[reducible] def freeYonedaPresheafMap {V U : C} (i : V ⟶ U) :
    freeYonedaPresheaf (C := C) V ⟶ freeYonedaPresheaf U :=
  Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free


-- @@ L126-129 verbatim
/-- Functoriality of the free-Yoneda sheaf. -/
@[reducible] def freeYonedaSheafMap {V U : C} (i : V ⟶ U) :
    freeYonedaSheaf J V ⟶ freeYonedaSheaf J U :=
  (presheafToSheaf J AddCommGrpCat.{u}).map (freeYonedaPresheafMap i)


-- @@ L131-131 verbatim
section OfF


-- @@ L133-133 verbatim
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

-- @@ L134-134 verbatim
variable (F : Sheaf J AddCommGrpCat.{u})


-- @@ L136-139 verbatim
/-- Definitional receipt: the carrier of Mathlib's `Sheaf.H'` is the
`Ext`-group from the free-Yoneda sheaf. -/
theorem hPrime_carrier (n : ℕ) (U : C) :
    (F.H' n U : Type u) = Ext (freeYonedaSheaf J U) F n := rfl


-- @@ L141-146 verbatim
/-- Definitional receipt: the restriction maps of Mathlib's
`Sheaf.cohomologyPresheaf` are `Ext`-precomposition with `Ext.mk₀` of the
free-Yoneda sheaf map. -/
theorem cohomologyPresheaf_map_eq {n : ℕ} {V U : C} (i : V ⟶ U) (x : F.H' n U) :
    (F.cohomologyPresheaf n).map i.op x =
      (Ext.mk₀ (freeYonedaSheafMap (J := J) i)).comp x (zero_add n) := rfl


-- @@ L148-148 verbatim
end OfF


-- @@ L150-150 verbatim
section HomOfSection


-- @@ L152-152 verbatim
variable {P : Cᵒᵖ ⥤ AddCommGrpCat.{u}}


-- @@ L154-185 verbatim
/-- The presheaf morphism out of the free-Yoneda presheaf attached to a
section `s` of `P` over `U`: on the `V`-component it sends the generator of
`g : V ⟶ U` to the restriction of `s` along `g`. -/
def freeYonedaHomOfSection {U : C} (s : P.obj (op U)) :
    freeYonedaPresheaf U ⟶ P where
  app V := AddCommGrpCat.ofHom
    (FreeAbelianGroup.lift (fun g : V.unop ⟶ U => P.map g.op s))
  naturality V W i := by
    apply AddCommGrpCat.hom_ext
    refine FreeAbelianGroup.lift_ext _ _ (fun g : V.unop ⟶ U => ?_)
    show ((freeYonedaPresheaf U).map i ≫ AddCommGrpCat.ofHom
        (FreeAbelianGroup.lift (fun g : W.unop ⟶ U => P.map g.op s)))
        (FreeAbelianGroup.of g) =
      (AddCommGrpCat.ofHom
        (FreeAbelianGroup.lift (fun g : V.unop ⟶ U => P.map g.op s)) ≫ P.map i)
        (FreeAbelianGroup.of g)
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
    have h1 : (freeYonedaPresheaf U).map i (FreeAbelianGroup.of g) =
        FreeAbelianGroup.of (i.unop ≫ g) := by
      show AddCommGrpCat.free.map ((yoneda.obj U).map i) (FreeAbelianGroup.of g) =
        FreeAbelianGroup.of (i.unop ≫ g)
      show FreeAbelianGroup.map ((yoneda.obj U).map i) (FreeAbelianGroup.of g) =
        FreeAbelianGroup.of (i.unop ≫ g)
      exact FreeAbelianGroup.map_of_apply g
    rw [h1]
    show FreeAbelianGroup.lift (fun g : W.unop ⟶ U => P.map g.op s)
        (FreeAbelianGroup.of (i.unop ≫ g)) =
      P.map i (FreeAbelianGroup.lift (fun g : V.unop ⟶ U => P.map g.op s)
        (FreeAbelianGroup.of g))
    rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      ← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl


-- @@ L187-190 verbatim
theorem freeYonedaHomOfSection_app_of {U : C} (s : P.obj (op U)) (V : Cᵒᵖ)
    (g : V.unop ⟶ U) :
    (freeYonedaHomOfSection s).app V (FreeAbelianGroup.of g) = P.map g.op s :=
  FreeAbelianGroup.lift_apply_of _ _


-- @@ L192-218 verbatim
/-- A morphism out of the free-Yoneda presheaf is determined by its value on
the tautological generator. -/
theorem freeYonedaHom_eq_ofSection {U : C} (φ : freeYonedaPresheaf U ⟶ P) :
    φ = freeYonedaHomOfSection (φ.app (op U) (FreeAbelianGroup.of (𝟙 U))) := by
  ext V : 2
  apply AddCommGrpCat.hom_ext
  refine FreeAbelianGroup.lift_ext _ _ (fun g : V.unop ⟶ U => ?_)
  have hn : φ.app V ((freeYonedaPresheaf U).map (Quiver.Hom.op (g : V.unop ⟶ U))
      (FreeAbelianGroup.of (𝟙 U))) =
      P.map (Quiver.Hom.op (g : V.unop ⟶ U))
        (φ.app (op U) (FreeAbelianGroup.of (𝟙 U))) :=
    congrArg
      (fun (h : (freeYonedaPresheaf U).obj (op U) ⟶ P.obj V) =>
        h (FreeAbelianGroup.of (𝟙 U)))
      (φ.naturality (Quiver.Hom.op (g : V.unop ⟶ U) : op U ⟶ V))
  have h1 : (freeYonedaPresheaf U).map (Quiver.Hom.op (g : V.unop ⟶ U))
      (FreeAbelianGroup.of (𝟙 U)) = FreeAbelianGroup.of g := by
    show FreeAbelianGroup.map ((yoneda.obj U).map (Quiver.Hom.op (g : V.unop ⟶ U)))
      (FreeAbelianGroup.of (𝟙 U)) = FreeAbelianGroup.of g
    rw [FreeAbelianGroup.map_of_apply]
    show FreeAbelianGroup.of (g ≫ 𝟙 U) = FreeAbelianGroup.of g
    rw [Category.comp_id]
  show φ.app V (FreeAbelianGroup.of g) =
    (freeYonedaHomOfSection (φ.app (op U) (FreeAbelianGroup.of (𝟙 U)))).app V
      (FreeAbelianGroup.of g)
  rw [freeYonedaHomOfSection_app_of]
  exact (congrArg (fun z => φ.app V z) h1).symm.trans hn


-- @@ L220-220 verbatim
end HomOfSection


-- @@ L222-222 verbatim
section EquivH0


-- @@ L224-224 verbatim
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

-- @@ L225-225 verbatim
variable (F : Sheaf J AddCommGrpCat.{u})


-- @@ L227-231 verbatim
/-- The sheaf morphism out of the free-Yoneda sheaf attached to a section,
along the sheafification adjunction. -/
def sheafHomOfSection (U : C) (s : F.obj.obj (op U)) : freeYonedaSheaf J U ⟶ F :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv (freeYonedaPresheaf U) F).symm
    (freeYonedaHomOfSection s)


-- @@ L233-237 verbatim
/-- **Degree-0 `Sheaf.H'` classes are sections** (forward direction): evaluate
the underlying presheaf morphism at the tautological generator. -/
def h0ToSections (U : C) (x : Ext (freeYonedaSheaf J U) F 0) : F.obj.obj (op U) :=
  (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv (freeYonedaPresheaf U) F)
    (Ext.addEquiv₀ x)).app (op U) (FreeAbelianGroup.of (𝟙 U))


-- @@ L239-243 verbatim
theorem h0ToSections_def (U : C) (x : Ext (freeYonedaSheaf J U) F 0) :
    h0ToSections F U x =
      (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
        (freeYonedaPresheaf U) F) (Ext.addEquiv₀ x)).app (op U)
        (FreeAbelianGroup.of (𝟙 U)) := rfl


-- @@ L245-247 verbatim
theorem addEquiv₀_mk₀ {X Y : Sheaf J AddCommGrpCat.{u}} (f : X ⟶ Y) :
    Ext.addEquiv₀ (Ext.mk₀ f) = f :=
  (Ext.mk₀_bijective _ _).injective (Ext.mk₀_addEquiv₀_apply _)


-- @@ L249-260 verbatim
theorem h0ToSections_sheafHomOfSection (U : C) (s : F.obj.obj (op U)) :
    h0ToSections F U (Ext.mk₀ (sheafHomOfSection F U s)) = s := by
  rw [h0ToSections_def, addEquiv₀_mk₀]
  show (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
      (freeYonedaPresheaf U) F)
      (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
        (freeYonedaPresheaf U) F).symm (freeYonedaHomOfSection s))).app (op U)
      (FreeAbelianGroup.of (𝟙 U)) = s
  rw [Equiv.apply_symm_apply, freeYonedaHomOfSection_app_of]
  show F.obj.map ((𝟙 U).op) s = s
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl


-- @@ L262-277 verbatim
theorem mk₀_sheafHomOfSection_h0ToSections (U : C)
    (x : Ext (freeYonedaSheaf J U) F 0) :
    Ext.mk₀ (sheafHomOfSection F U (h0ToSections F U x)) = x := by
  have h1 : sheafHomOfSection F U (h0ToSections F U x) = Ext.addEquiv₀ x := by
    apply ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
      (freeYonedaPresheaf U) F).injective
    show ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
        (freeYonedaPresheaf U) F)
        (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
          (freeYonedaPresheaf U) F).symm
          (freeYonedaHomOfSection (h0ToSections F U x))) =
      ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
        (freeYonedaPresheaf U) F) (Ext.addEquiv₀ x)
    rw [Equiv.apply_symm_apply]
    exact (freeYonedaHom_eq_ofSection _).symm
  rw [h1, Ext.mk₀_addEquiv₀_apply]


-- @@ L279-284 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem h0ToSections_add (U : C) (x y : Ext (freeYonedaSheaf J U) F 0) :
    h0ToSections F U (x + y) = h0ToSections F U x + h0ToSections F U y := by
  rw [h0ToSections_def, h0ToSections_def, h0ToSections_def, map_add,
    Adjunction.homAddEquiv_add]
  rfl


-- @@ L286-295 verbatim
/-- **Degree-0 `Sheaf.H'` is sections**: the additive equivalence between the
degree-0 `Ext` group at the free-Yoneda anchor and the sections of `F` over
`U`.  (This is the `H'`-degree-0-is-sections identification of CYC-G33 and of
Mathlib's own `TODO`.) -/
def h0SectionsEquiv (U : C) :
    Ext (freeYonedaSheaf J U) F 0 ≃+ F.obj.obj (op U) :=
  AddEquiv.mk'
    ⟨h0ToSections F U, fun s => Ext.mk₀ (sheafHomOfSection F U s),
      mk₀_sheafHomOfSection_h0ToSections F U, h0ToSections_sheafHomOfSection F U⟩
    (h0ToSections_add F U)


-- @@ L297-298 verbatim
theorem h0SectionsEquiv_apply (U : C) (x : Ext (freeYonedaSheaf J U) F 0) :
    h0SectionsEquiv F U x = h0ToSections F U x := rfl


-- @@ L300-301 verbatim
theorem h0SectionsEquiv_symm_apply (U : C) (s : F.obj.obj (op U)) :
    (h0SectionsEquiv F U).symm s = Ext.mk₀ (sheafHomOfSection F U s) := rfl


-- @@ L303-351 verbatim
/-- **Naturality of the degree-0 sections identification** in the open,
against the restriction maps of `Sheaf.cohomologyPresheaf` (spelled as
`Ext`-precomposition, per `cohomologyPresheaf_map_eq`). -/
theorem h0ToSections_natural {V U : C} (i : V ⟶ U)
    (x : Ext (freeYonedaSheaf J U) F 0) :
    F.obj.map i.op (h0ToSections F U x) =
      h0ToSections F V
        ((Ext.mk₀ (freeYonedaSheafMap (J := J) i)).comp x (zero_add 0)) := by
  have hEq : Ext.addEquiv₀
      ((Ext.mk₀ (freeYonedaSheafMap (J := J) i)).comp x (zero_add 0)) =
      freeYonedaSheafMap (J := J) i ≫ Ext.addEquiv₀ x := by
    apply (Ext.mk₀_bijective _ _).injective
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  rw [h0ToSections_def, h0ToSections_def, hEq]
  have hnatL : ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
        (freeYonedaPresheaf V) F) (freeYonedaSheafMap (J := J) i ≫ Ext.addEquiv₀ x) =
      freeYonedaPresheafMap i ≫
        ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
          (freeYonedaPresheaf U) F) (Ext.addEquiv₀ x) :=
    Adjunction.homEquiv_naturality_left _ _ _
  rw [hnatL]
  set ψ : freeYonedaPresheaf U ⟶ (sheafToPresheaf J AddCommGrpCat.{u}).obj F :=
    ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv
      (freeYonedaPresheaf U) F) (Ext.addEquiv₀ x)
  have hn : ψ.app (op V) ((freeYonedaPresheaf U).map (Quiver.Hom.op (i : V ⟶ U))
      (FreeAbelianGroup.of (𝟙 U))) =
      ((sheafToPresheaf J AddCommGrpCat.{u}).obj F).map (Quiver.Hom.op (i : V ⟶ U))
        (ψ.app (op U) (FreeAbelianGroup.of (𝟙 U))) :=
    congrArg
      (fun (h : (freeYonedaPresheaf U).obj (op U) ⟶
          ((sheafToPresheaf J AddCommGrpCat.{u}).obj F).obj (op V)) =>
        h (FreeAbelianGroup.of (𝟙 U)))
      (ψ.naturality (Quiver.Hom.op (i : V ⟶ U) : op U ⟶ op V))
  have h1 : (freeYonedaPresheaf U).map (Quiver.Hom.op (i : V ⟶ U))
      (FreeAbelianGroup.of (𝟙 U)) = FreeAbelianGroup.of i := by
    show FreeAbelianGroup.map ((yoneda.obj U).map (Quiver.Hom.op (i : V ⟶ U)))
      (FreeAbelianGroup.of (𝟙 U)) = FreeAbelianGroup.of i
    rw [FreeAbelianGroup.map_of_apply]
    show FreeAbelianGroup.of (i ≫ 𝟙 U) = FreeAbelianGroup.of i
    rw [Category.comp_id]
  have hgen : (freeYonedaPresheafMap (C := C) i).app (op V)
      (FreeAbelianGroup.of (𝟙 V)) = FreeAbelianGroup.of i := by
    show FreeAbelianGroup.map ((yoneda.map i).app (op V))
      (FreeAbelianGroup.of (𝟙 V)) = FreeAbelianGroup.of i
    rw [FreeAbelianGroup.map_of_apply]
    show FreeAbelianGroup.of (𝟙 V ≫ i) = FreeAbelianGroup.of i
    rw [Category.id_comp]
  exact (hn.symm.trans (congrArg (fun z => ψ.app (op V) z) h1)).trans
    (congrArg (fun z => ψ.app (op V) z) hgen).symm


-- @@ L353-362 verbatim
/-- Naturality of the inverse direction: the class of a restricted section is
the `Ext`-restriction of the class of the section. -/
theorem mk₀_sheafHomOfSection_natural {V U : C} (i : V ⟶ U) (s : F.obj.obj (op U)) :
    Ext.mk₀ (sheafHomOfSection F V (F.obj.map i.op s)) =
      (Ext.mk₀ (freeYonedaSheafMap (J := J) i)).comp
        (Ext.mk₀ (sheafHomOfSection F U s)) (zero_add 0) := by
  apply (h0SectionsEquiv F V).injective
  rw [h0SectionsEquiv_apply, h0SectionsEquiv_apply,
    h0ToSections_sheafHomOfSection, ← h0ToSections_natural,
    h0ToSections_sheafHomOfSection]


-- @@ L364-364 verbatim
end EquivH0


-- @@ L366-370 verbatim
/-! ### The terminal-object anchor: `H'(⊤)` re-anchors to `Sheaf.H`

At a terminal object the Yoneda presheaf is constant `PUnit`, so its free
abelian presheaf is constant `ℤ`; sheafifying identifies the free-Yoneda
anchor with the constant-`ULift ℤ` anchor of Mathlib's `Sheaf.H`. -/


-- @@ L372-372 verbatim
section TopAnchor


-- @@ L374-374 verbatim
variable (T : C) (hT : IsTerminal T)


-- @@ L376-378 verbatim
/-- Homs into a terminal object form a `Unique` type. -/
@[reducible] def uniqueHomToTerminal (V : C) : Unique (V ⟶ T) :=
  ⟨⟨hT.from V⟩, fun f => hT.hom_ext f _⟩


-- @@ L380-385 verbatim
/-- The component of the terminal-anchor identification at `V`: the free
abelian group on the (unique-element) hom-type `V ⟶ T` is `ULift ℤ`. -/
def freeYonedaTopComponent (V : C) :
    (freeYonedaPresheaf (C := C) T).obj (op V) ≅ AddCommGrpCat.of (ULift.{u} ℤ) :=
  letI := uniqueHomToTerminal T hT V
  ((FreeAbelianGroup.uniqueEquiv (V ⟶ T)).trans AddEquiv.ulift.symm).toAddCommGrpIso


-- @@ L387-394 verbatim
theorem freeYonedaTopComponent_hom_of (V : C) (g : V ⟶ T) :
    (freeYonedaTopComponent T hT V).hom (FreeAbelianGroup.of g) =
      ULift.up (1 : ℤ) := by
  letI := uniqueHomToTerminal T hT V
  show AddEquiv.ulift.symm (FreeAbelianGroup.lift (fun _ => (1 : ℤ))
    (FreeAbelianGroup.of g)) = ULift.up (1 : ℤ)
  rw [FreeAbelianGroup.lift_apply_of]
  rfl


-- @@ L396-420 verbatim
/-- The free-Yoneda presheaf at a terminal object is the constant presheaf at
`ULift ℤ`. -/
def freeYonedaTopIso :
    freeYonedaPresheaf (C := C) T ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents
    (fun V => freeYonedaTopComponent T hT V.unop)
    (fun {V W} i => by
      apply AddCommGrpCat.hom_ext
      refine FreeAbelianGroup.lift_ext _ _ (fun g : V.unop ⟶ T => ?_)
      show ((freeYonedaPresheaf T).map i ≫ (freeYonedaTopComponent T hT W.unop).hom)
          (FreeAbelianGroup.of g) =
        ((freeYonedaTopComponent T hT V.unop).hom ≫
          ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))).map i)
          (FreeAbelianGroup.of g)
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
      have h1 : (freeYonedaPresheaf T).map i (FreeAbelianGroup.of g) =
          FreeAbelianGroup.of (i.unop ≫ g) := by
        show FreeAbelianGroup.map ((yoneda.obj T).map i) (FreeAbelianGroup.of g) =
          FreeAbelianGroup.of (i.unop ≫ g)
        exact FreeAbelianGroup.map_of_apply g
      rw [h1, freeYonedaTopComponent_hom_of, freeYonedaTopComponent_hom_of]
      show ULift.up (1 : ℤ) =
        (𝟙 (AddCommGrpCat.of (ULift.{u} ℤ))) (ULift.up (1 : ℤ))
      rfl)


-- @@ L422-428 verbatim
/-- **The anchor re-isomorphism**: the free-Yoneda sheaf at a terminal object
is the constant sheaf at `ULift ℤ` — Mathlib's `Sheaf.H`-anchor.  (This is the
`H'(⊤)`-to-`Sheaf.H` anchor bridge of CYC-G33.) -/
def freeYonedaTopSheafIso :
    freeYonedaSheaf J T ≅
      (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{u}).mapIso (freeYonedaTopIso T hT)


-- @@ L430-430 verbatim
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]


-- @@ L432-436 verbatim
/-- **`H'` at a terminal object is `Sheaf.H`**, in every degree: the additive
equivalence obtained by re-anchoring along `freeYonedaTopSheafIso`. -/
def hPrimeTopEquivH (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    Ext (freeYonedaSheaf J T) F n ≃+ Sheaf.H F n :=
  CycCarrier.extReanchorLeft (freeYonedaTopSheafIso (J := J) T hT) n


-- @@ L438-438 verbatim
end TopAnchor


-- @@ L440-440 verbatim
end SectionsLayer


-- @@ L442-446 verbatim
/-! ## Part 2. The projective line: the constants joint, the chart algebra
maps, and the overlap coordinate

Everything below is at `p1 = Proj ℂ[X₀, X₁]` with the `ℂ`-algebra structure
on section rings induced by the structure morphism (`Sec φC U`). -/


-- @@ L448-448 verbatim
section ProjectiveLinePart


-- @@ L450-450 verbatim
open AlgebraicGeometry HomogeneousLocalization TopologicalSpace

-- @@ L451-451 verbatim
open HodgePilot.DeRhamPresheaf HodgePilot.ProjectiveLine HodgePilot.ProjectiveLineUnits

-- @@ L452-452 verbatim
open LaurentPolynomial

-- @@ L453-453 verbatim
open scoped Polynomial


-- @@ L455-455 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L457-458 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L460-462 verbatim
/-- The structure constants map of the projective line: the ring hom
`ℂ →+* Γ(p1, ⊤)` induced by wave 1's structure morphism. -/
def φC : ℂ →+* Γ(p1, ⊤) := cRingHom structMor


-- @@ L464-465 verbatim
/-! ### The constants joint (γ): restriction of a global constant to a basic
open is `awayToSection` of the grade-zero constant -/


-- @@ L467-521 verbatim
/-- The categorical constants joint: on any positive-degree basic open, the
global-sections leg of `toSpecZero` followed by restriction agrees with
`awayToSection ∘ fromZeroRingHom`.  (Assembled from the pin's
`awayι_toSpecZero`, `basicOpenToSpec_app_top`, and `ΓSpecIso` naturality.) -/
theorem toSpecZero_appTop_res {f : MvPolynomial (Fin 2) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₂ m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜₂ 0))).inv ≫ (Proj.toSpecZero 𝒜₂).appTop ≫
        p1.presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜₂ f ≤ ⊤)).op =
      CommRingCat.ofHom (fromZeroRingHom 𝒜₂ (Submonoid.powers f)) ≫
        Proj.awayToSection 𝒜₂ f := by
  have h1 : Proj.awayι 𝒜₂ f hf hm ≫ Proj.toSpecZero 𝒜₂ =
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜₂ (Submonoid.powers f))) :=
    Proj.awayι_toSpecZero 𝒜₂ f hf hm
  have h2 := congrArg Scheme.Hom.appTop h1
  rw [Scheme.Hom.comp_appTop] at h2
  have h3 : (Proj.awayι 𝒜₂ f hf hm).appTop =
      (Proj.basicOpen 𝒜₂ f).ι.appTop ≫
        ((Proj.basicOpenIsoSpec 𝒜₂ f hf hm).inv).appTop := by
    rw [← Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_inv_ι]
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of (𝒜₂ 0))).inv ≫
      (Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜₂ (Submonoid.powers f)))).appTop =
      CommRingCat.ofHom (fromZeroRingHom 𝒜₂ (Submonoid.powers f)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜₂ f))).inv :=
    (Scheme.ΓSpecIso_inv_naturality _).symm
  have h5 : (Scheme.ΓSpecIso (CommRingCat.of (𝒜₂ 0))).inv ≫
      (Proj.toSpecZero 𝒜₂).appTop ≫ (Proj.basicOpen 𝒜₂ f).ι.appTop ≫
        ((Proj.basicOpenIsoSpec 𝒜₂ f hf hm).inv).appTop =
      CommRingCat.ofHom (fromZeroRingHom 𝒜₂ (Submonoid.powers f)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜₂ f))).inv := by
    rw [← h3, h2]
    exact h4
  have h6 : ((Proj.basicOpenIsoSpec 𝒜₂ f hf hm).inv).appTop ≫
      ((Proj.basicOpenIsoSpec 𝒜₂ f hf hm).hom).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    rfl
  have h7 : ((Proj.basicOpenIsoSpec 𝒜₂ f hf hm).hom).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜₂ f))).hom ≫ Proj.awayToSection 𝒜₂ f ≫
        (Proj.basicOpen 𝒜₂ f).topIso.inv := by
    rw [Proj.basicOpenIsoSpec_hom]
    exact Proj.basicOpenToSpec_app_top 𝒜₂ f
  have h8 : (Proj.basicOpen 𝒜₂ f).ι.appTop ≫ (Proj.basicOpen 𝒜₂ f).topIso.hom =
      p1.presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜₂ f ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    exact ((p1.presheaf.map_comp _ _).symm).trans
      ((congrArg (fun t => p1.presheaf.map t) op_comp.symm).trans
        (congrArg (fun (h : Proj.basicOpen 𝒜₂ f ⟶ ⊤) => p1.presheaf.map h.op)
          (Subsingleton.elim _ _)))
  have h9 := congrArg
    (fun t => t ≫ ((Proj.basicOpenIsoSpec 𝒜₂ f hf hm).hom).appTop) h5
  simp only [Category.assoc] at h9
  rw [h6, Category.comp_id, h7, Iso.inv_hom_id_assoc] at h9
  have h10 := congrArg (fun t => t ≫ (Proj.basicOpen 𝒜₂ f).topIso.hom) h9
  simp only [Category.assoc] at h10
  rw [Iso.inv_hom_id, Category.comp_id, h8] at h10
  exact h10


-- @@ L523-550 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The constants joint (γ), element level, restriction form**: the
restriction of the global constant `φC c` to a positive-degree basic open is
the `awayToSection` image of the chart-ring constant of wave 2's
`instAlgebraAwayC`. -/
theorem res_top_cRingHom_eq_awayToSection {f : MvPolynomial (Fin 2) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₂ m) (hm : 0 < m) (c : ℂ) :
    p1.presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜₂ f ≤ ⊤)).op (φC c) =
      Proj.awayToSection 𝒜₂ f (algebraMap ℂ (Away 𝒜₂ f) c) := by
  have hnat' : (Scheme.ΓSpecIso (CommRingCat.of (𝒜₂ 0))).inv
      (gradeZeroEquiv.toCommRingCatIso.hom c) =
      (Spec.map (gradeZeroEquiv.toCommRingCatIso.hom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) :=
    congrArg
      (fun (t : CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of (𝒜₂ 0)), ⊤)) => t c)
      (Scheme.ΓSpecIso_inv_naturality (gradeZeroEquiv.toCommRingCatIso.hom))
  have hφ : φC c = (Proj.toSpecZero 𝒜₂).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒜₂ 0))).inv (algebraMap ℂ (𝒜₂ 0) c)) := by
    show (Proj.toSpecZero 𝒜₂).appTop
        ((Spec.map (gradeZeroEquiv.toCommRingCatIso.hom)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = _
    exact congrArg (fun z => (Proj.toSpecZero 𝒜₂).appTop z) hnat'.symm
  have hmain := congrArg
    (fun (t : CommRingCat.of (𝒜₂ 0) ⟶ Γ(p1, Proj.basicOpen 𝒜₂ f)) =>
      t (algebraMap ℂ (𝒜₂ 0) c))
    (toSpecZero_appTop_res hf hm)
  rw [hφ, ProjectiveLineUnits.algebraMap_away_apply]
  exact hmain


-- @@ L552-559 verbatim
/-- **The constants joint (γ), element level**: the `ℂ`-algebra constants of
the section ring of a positive-degree basic open are the `awayToSection`
images of the chart-ring constants of wave 2's `instAlgebraAwayC`. -/
theorem algebraMap_sec_eq_awayToSection {f : MvPolynomial (Fin 2) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₂ m) (hm : 0 < m) (c : ℂ) :
    algebraMap ℂ (Sec φC (Proj.basicOpen 𝒜₂ f)) c =
      Proj.awayToSection 𝒜₂ f (algebraMap ℂ (Away 𝒜₂ f) c) :=
  res_top_cRingHom_eq_awayToSection hf hm c


-- @@ L561-576 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The constants joint at the chart overlap `U0 ⊓ U1`, phrased at wave 1's
literal `overlapRingHom`. -/
theorem algebraMap_sec_U01 (c : ℂ) :
    algebraMap ℂ (Sec φC (U0 ⊓ U1)) c =
      overlapRingHom (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) c) := by
  have hsplit : p1.presheaf.map (homOfLE (le_top : U0 ⊓ U1 ≤ ⊤)).op (φC c) =
      p1.presheaf.map (homOfLE (le_of_eq U0_inf_U1)).op
        (p1.presheaf.map (homOfLE (le_top :
          Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) ≤ ⊤)).op (φC c)) := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact congrArg (fun (h : U0 ⊓ U1 ⟶ ⊤) => p1.presheaf.map h.op (φC c))
      (Subsingleton.elim _ _)
  show p1.presheaf.map (homOfLE (le_top : U0 ⊓ U1 ≤ ⊤)).op (φC c) = _
  rw [hsplit, res_top_cRingHom_eq_awayToSection hX01 two_pos c]
  rfl


-- @@ L578-578 verbatim
/-! ### The chart algebra maps `ℂ[X] →ₐ[ℂ] Γ(U_i)` -/


-- @@ L580-588 verbatim
theorem uniqueAlgEquiv_X :
    (MvPolynomial.uniqueAlgEquiv (R := ℂ) (Fin 1)) (MvPolynomial.X 0) =
      Polynomial.X := by
  show (MvPolynomial.uniqueAlgEquiv (R := ℂ) (Fin 1))
    (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 1) (1 : ℂ)) = Polynomial.X
  rw [MvPolynomial.uniqueAlgEquiv_monomial]
  rw [show ((Finsupp.single (0 : Fin 1) 1) default) = 1 from by
    rw [show (default : Fin 1) = 0 from rfl, Finsupp.single_eq_same]]
  exact Polynomial.monomial_one_one_eq_X


-- @@ L590-593 verbatim
theorem uniqueAlgEquiv_symm_X :
    (MvPolynomial.uniqueAlgEquiv (R := ℂ) (Fin 1)).symm Polynomial.X =
      MvPolynomial.X 0 := by
  rw [← uniqueAlgEquiv_X, AlgEquiv.symm_apply_apply]


-- @@ L595-602 verbatim
/-- `awayToSection` as a `ℂ`-algebra map onto the section ring, at the
`ℂ`-structures of wave 2 (`instAlgebraAwayC`) and of the tower (`Sec φC`) —
the constants agreement is the (γ) joint above. -/
def awaySectionAlgHom {f : MvPolynomial (Fin 2) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₂ m) (hm : 0 < m) :
    Away 𝒜₂ f →ₐ[ℂ] Sec φC (Proj.basicOpen 𝒜₂ f) :=
  { toRingHom := (Proj.awayToSection 𝒜₂ f).hom
    commutes' := fun c => (algebraMap_sec_eq_awayToSection hf hm c).symm }


-- @@ L604-606 verbatim
theorem awaySectionAlgHom_apply {f : MvPolynomial (Fin 2) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₂ m) (hm : 0 < m) (x : Away 𝒜₂ f) :
    awaySectionAlgHom hf hm x = Proj.awayToSection 𝒜₂ f x := rfl


-- @@ L608-614 verbatim
/-- **The chart algebra map** `ℂ[X] →ₐ[ℂ] Γ(D₊(Xᵢ))`, sending the variable to
the coordinate fraction `Xⱼ/Xᵢ` (through wave 2's `chartPolyHom` and the pin's
`awayToSection`). -/
def chartHomA (i j : Fin 2) :
    Polynomial ℂ →ₐ[ℂ] Sec φC (Proj.basicOpen 𝒜₂ (MvPolynomial.X i)) :=
  ((awaySectionAlgHom (X_mem_grade_one i) one_pos).comp (chartPolyHom i j)).comp
    ((MvPolynomial.uniqueAlgEquiv (R := ℂ) (Fin 1)).symm.toAlgHom)


-- @@ L616-622 verbatim
theorem chartHomA_X (i j : Fin 2) :
    chartHomA i j Polynomial.X =
      Proj.awayToSection 𝒜₂ (MvPolynomial.X i) (coordFrac i j) := by
  show awaySectionAlgHom (X_mem_grade_one i) one_pos (chartPolyHom i j
    ((MvPolynomial.uniqueAlgEquiv (R := ℂ) (Fin 1)).symm Polynomial.X)) = _
  rw [uniqueAlgEquiv_symm_X, chartPolyHom_X]
  rfl


-- @@ L624-633 verbatim
/-- The chart algebra map is surjective (wave 2's `chartPolyHom_surjective`
composed with the `awayToSection` isomorphism). -/
theorem chartHomA_surjective (i j : Fin 2) (hij : i ≠ j) :
    Function.Surjective (chartHomA i j) := by
  have h1 : Function.Surjective (awaySectionAlgHom (X_mem_grade_one i) one_pos) := by
    have := isIso_awayToSection (X_mem_grade_one i) one_pos
    exact (ConcreteCategory.bijective_of_isIso
      (Proj.awayToSection 𝒜₂ (MvPolynomial.X i))).surjective
  exact h1.comp ((chartPolyHom_surjective hij).comp
    (MvPolynomial.uniqueAlgEquiv (R := ℂ) (Fin 1)).symm.surjective)


-- @@ L635-635 verbatim
/-! ### The overlap coordinate: `ℂ[T;T⁻¹]` into and out of `Γ(U0 ⊓ U1)` -/


-- @@ L637-638 verbatim
/-- Wave 1's overlap unit, retyped at the `Sec φC`-carrier. -/
def overlapUnitSec : (Sec φC (U0 ⊓ U1))ˣ := overlapUnit


-- @@ L640-646 verbatim
/-- **The overlap coordinate map**: the `ℂ`-algebra map
`ℂ[T;T⁻¹] →ₐ[ℂ] Γ(U0 ⊓ U1)` sending `T` to wave 1's literal overlap unit
(the transition unit of the point-divisor glue datum). -/
def overlapAlgHom : ℂ[T;T⁻¹] →ₐ[ℂ] Sec φC (U0 ⊓ U1) :=
  AddMonoidAlgebra.lift _ _ _
    ((Units.coeHom (Sec φC (U0 ⊓ U1))).comp
      ((zpowersHom ((Sec φC (U0 ⊓ U1))ˣ)) overlapUnitSec))


-- @@ L648-650 verbatim
theorem T_one_eq_single : (T (1 : ℤ) : ℂ[T;T⁻¹]) =
    AddMonoidAlgebra.single (1 : ℤ) (1 : ℂ) := by
  rw [single_eq_C_mul_T, map_one, one_mul]


-- @@ L652-654 verbatim
theorem T_neg_one_eq_single : (T (-1 : ℤ) : ℂ[T;T⁻¹]) =
    AddMonoidAlgebra.single (-1 : ℤ) (1 : ℂ) := by
  rw [single_eq_C_mul_T, map_one, one_mul]


-- @@ L656-670 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Glue-datum receipt**: the overlap coordinate map sends `T` to wave 1's
literal `overlapUnit` — the transition unit of `dinf`'s Mayer–Vietoris glue
datum. -/
theorem overlapAlgHom_T :
    overlapAlgHom (T (1 : ℤ)) = (overlapUnit : Γ(p1, U0 ⊓ U1)) := by
  rw [T_one_eq_single, overlapAlgHom]
  rw [AddMonoidAlgebra.lift_single, one_smul]
  show (((zpowersHom ((Sec φC (U0 ⊓ U1))ˣ)) overlapUnitSec)
    (Multiplicative.ofAdd (1 : ℤ)) : Sec φC (U0 ⊓ U1)) = _
  rw [zpowersHom_apply]
  show ((overlapUnitSec ^ ((Multiplicative.ofAdd (1 : ℤ)).toAdd) :
    (Sec φC (U0 ⊓ U1))ˣ) : Sec φC (U0 ⊓ U1)) = _
  rw [show ((Multiplicative.ofAdd (1 : ℤ)).toAdd) = (1 : ℤ) from rfl, zpow_one]
  rfl


-- @@ L672-685 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem overlapAlgHom_T_neg :
    overlapAlgHom (T (-1 : ℤ)) =
      ((overlapUnit⁻¹ : (Γ(p1, U0 ⊓ U1))ˣ) : Γ(p1, U0 ⊓ U1)) := by
  rw [T_neg_one_eq_single, overlapAlgHom]
  rw [AddMonoidAlgebra.lift_single, one_smul]
  show (((zpowersHom ((Sec φC (U0 ⊓ U1))ˣ)) overlapUnitSec)
    (Multiplicative.ofAdd (-1 : ℤ)) : Sec φC (U0 ⊓ U1)) = _
  rw [zpowersHom_apply]
  show ((overlapUnitSec ^ ((Multiplicative.ofAdd (-1 : ℤ)).toAdd) :
    (Sec φC (U0 ⊓ U1))ˣ) : Sec φC (U0 ⊓ U1)) = _
  rw [show ((Multiplicative.ofAdd (-1 : ℤ)).toAdd) = (-1 : ℤ) from rfl,
    zpow_neg_one]
  rfl


-- @@ L687-690 verbatim
/-- Wave 1's `overlapUnit`, unfolded: its value is `overlapRingHom awayNum`
(definitional receipt). -/
theorem overlapUnit_coe :
    (overlapUnit : Γ(p1, U0 ⊓ U1)) = overlapRingHom awayNum := rfl


-- @@ L692-695 verbatim
/-- The inverse of wave 1's `overlapUnit`, unfolded (definitional receipt). -/
theorem overlapUnit_inv_coe :
    ((overlapUnit⁻¹ : (Γ(p1, U0 ⊓ U1))ˣ) : Γ(p1, U0 ⊓ U1)) =
      overlapRingHom awayNumInv := rfl


-- @@ L697-705 verbatim
/-- The overlap-section isomorphism: `awayToSection` at `X₀X₁` followed by the
transport along `U0 ⊓ U1 = D₊(X₀X₁)`. -/
def overlapSectionIso :
    CommRingCat.of (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) ≅
      Γ(p1, U0 ⊓ U1) :=
  letI : IsIso (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) :=
    isIso_awayToSection hX01 two_pos
  asIso (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) ≪≫
    p1.presheaf.mapIso (eqToIso U0_inf_U1).op


-- @@ L707-721 verbatim
theorem overlapSectionIso_inv_overlapRingHom
    (x : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) :
    overlapSectionIso.inv (overlapRingHom x) = x := by
  have h1 : overlapRingHom x = overlapSectionIso.hom x := by
    show p1.presheaf.map (homOfLE (le_of_eq U0_inf_U1)).op
        (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) x) =
      p1.presheaf.map ((eqToIso U0_inf_U1).hom.op)
        (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) x)
    exact congrArg
      (fun (h : U0 ⊓ U1 ⟶ Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) =>
        p1.presheaf.map h.op
          (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) x))
      (Subsingleton.elim _ _)
  rw [h1]
  exact overlapSectionIso.hom_inv_id_apply x


-- @@ L723-725 verbatim
/-- The Laurent evaluation of the overlap chart ring: `X₀ ↦ 1`, `X₁ ↦ T`
(the wave-2 `chartEval` pattern with target `ℂ[T;T⁻¹]`). -/
def overlapPt : Fin 2 → ℂ[T;T⁻¹] := ![1, T 1]


-- @@ L727-736 verbatim
theorem overlapPt_X01_isUnit :
    IsUnit ((MvPolynomial.aeval overlapPt : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ[T;T⁻¹]).toRingHom
      (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
  rw [map_mul]
  show IsUnit ((MvPolynomial.aeval overlapPt) (MvPolynomial.X 0) *
    (MvPolynomial.aeval overlapPt) (MvPolynomial.X 1))
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  show IsUnit ((1 : ℂ[T;T⁻¹]) * T 1)
  rw [one_mul]
  exact isUnit_T 1


-- @@ L738-744 verbatim
/-- The Laurent evaluation on the overlap chart ring. -/
def overlapEvalRing :
    Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) →+* ℂ[T;T⁻¹] :=
  (Localization.awayLift ((MvPolynomial.aeval overlapPt : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ[T;T⁻¹]).toRingHom)
    (MvPolynomial.X 0 * MvPolynomial.X 1) overlapPt_X01_isUnit).comp
    (algebraMap (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1))
      (Localization.Away (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ)))


-- @@ L746-760 verbatim
theorem overlapEvalRing_algebraMap (c : ℂ) :
    overlapEvalRing (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) c) =
      algebraMap ℂ ℂ[T;T⁻¹] c := by
  have hval : (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) c).val =
      algebraMap (MvPolynomial (Fin 2) ℂ)
        (Localization.Away (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ))
        (MvPolynomial.C c) := by
    rw [ProjectiveLineUnits.algebraMap_away_apply]
    show Localization.mk _ 1 = _
    rw [Localization.mk_one_eq_algebraMap, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq]
  rw [overlapEvalRing, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    hval, IsLocalization.Away.lift_eq]
  show (MvPolynomial.aeval overlapPt) (MvPolynomial.C c) = algebraMap ℂ ℂ[T;T⁻¹] c
  rw [MvPolynomial.aeval_C]


-- @@ L762-765 verbatim
theorem T_mul_T_neg : (T (1 : ℤ) : ℂ[T;T⁻¹]) * T (-1 : ℤ) = 1 := by
  rw [← T_add]
  show (T ((1 : ℤ) + (-1)) : ℂ[T;T⁻¹]) = 1
  rw [show (1 : ℤ) + (-1) = 0 by ring, T_zero]


-- @@ L767-786 verbatim
theorem overlapEvalRing_awayNum : overlapEvalRing awayNum = T (1 : ℤ) := by
  rw [overlapEvalRing, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  rw [show (awayNum).val = Localization.mk
      (MvPolynomial.X 1 * MvPolynomial.X 1)
      (⟨(MvPolynomial.X 0 * MvPolynomial.X 1) ^ 1, 1, rfl⟩ :
        Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ))
    from HomogeneousLocalization.Away.val_mk _ _ _ _ _]
  rw [Localization.awayLift_mk (v := T (-1 : ℤ)) (hv := by
    rw [map_mul]
    show (MvPolynomial.aeval overlapPt) (MvPolynomial.X 0) *
        (MvPolynomial.aeval overlapPt) (MvPolynomial.X 1) * T (-1 : ℤ) = 1
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    show (1 : ℂ[T;T⁻¹]) * T 1 * T (-1 : ℤ) = 1
    rw [one_mul, T_mul_T_neg])]
  rw [map_mul]
  show (MvPolynomial.aeval overlapPt) (MvPolynomial.X 1) *
      (MvPolynomial.aeval overlapPt) (MvPolynomial.X 1) * T (-1 : ℤ) ^ 1 = T 1
  rw [MvPolynomial.aeval_X]
  show (T 1 : ℂ[T;T⁻¹]) * T 1 * T (-1 : ℤ) ^ 1 = T 1
  rw [pow_one, mul_assoc, T_mul_T_neg, mul_one]


-- @@ L788-807 verbatim
theorem overlapEvalRing_awayNumInv : overlapEvalRing awayNumInv = T (-1 : ℤ) := by
  rw [overlapEvalRing, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  rw [show (awayNumInv).val = Localization.mk
      (MvPolynomial.X 0 * MvPolynomial.X 0)
      (⟨(MvPolynomial.X 0 * MvPolynomial.X 1) ^ 1, 1, rfl⟩ :
        Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ))
    from HomogeneousLocalization.Away.val_mk _ _ _ _ _]
  rw [Localization.awayLift_mk (v := T (-1 : ℤ)) (hv := by
    rw [map_mul]
    show (MvPolynomial.aeval overlapPt) (MvPolynomial.X 0) *
        (MvPolynomial.aeval overlapPt) (MvPolynomial.X 1) * T (-1 : ℤ) = 1
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    show (1 : ℂ[T;T⁻¹]) * T 1 * T (-1 : ℤ) = 1
    rw [one_mul, T_mul_T_neg])]
  rw [map_mul]
  show (MvPolynomial.aeval overlapPt) (MvPolynomial.X 0) *
      (MvPolynomial.aeval overlapPt) (MvPolynomial.X 0) * T (-1 : ℤ) ^ 1 = T (-1 : ℤ)
  rw [MvPolynomial.aeval_X]
  show (1 : ℂ[T;T⁻¹]) * 1 * T (-1 : ℤ) ^ 1 = T (-1 : ℤ)
  rw [one_mul, one_mul, pow_one]


-- @@ L809-818 verbatim
/-- **The overlap inverse coordinate**: the `ℂ`-algebra map
`Γ(U0 ⊓ U1) →ₐ[ℂ] ℂ[T;T⁻¹]` given by the Laurent evaluation `X₀ ↦ 1, X₁ ↦ T`
through the `awayToSection` isomorphism. -/
def overlapInvAlgHom : Sec φC (U0 ⊓ U1) →ₐ[ℂ] ℂ[T;T⁻¹] :=
  { toRingHom := overlapEvalRing.comp (overlapSectionIso.inv.hom)
    commutes' := fun c => by
      show overlapEvalRing (overlapSectionIso.inv
        (algebraMap ℂ (Sec φC (U0 ⊓ U1)) c)) = algebraMap ℂ ℂ[T;T⁻¹] c
      rw [algebraMap_sec_U01, overlapSectionIso_inv_overlapRingHom]
      exact overlapEvalRing_algebraMap c }


-- @@ L820-824 verbatim
theorem overlapInvAlgHom_overlapRingHom
    (x : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) :
    overlapInvAlgHom (overlapRingHom x) = overlapEvalRing x := by
  show overlapEvalRing (overlapSectionIso.inv (overlapRingHom x)) = overlapEvalRing x
  rw [overlapSectionIso_inv_overlapRingHom]


-- @@ L826-831 verbatim
/-- **The `dz/z`-pin**: the inverse coordinate undoes the coordinate on the
transition unit — `overlapInvAlgHom (overlapAlgHom T) = T`. -/
theorem overlapInvAlgHom_overlapAlgHom_T :
    overlapInvAlgHom (overlapAlgHom (T (1 : ℤ))) = T (1 : ℤ) := by
  rw [overlapAlgHom_T, overlapUnit_coe, overlapInvAlgHom_overlapRingHom,
    overlapEvalRing_awayNum]


-- @@ L833-833 verbatim
end ProjectiveLinePart


-- @@ L835-835 verbatim
/-! ## Part 3. The Mayer–Vietoris edge class of `dz/z` and THE THEOREM -/


-- @@ L837-837 verbatim
section EdgeClass


-- @@ L839-839 verbatim
open AlgebraicGeometry HomogeneousLocalization TopologicalSpace

-- @@ L840-840 verbatim
open HodgePilot.DeRhamPresheaf HodgePilot.DeRhamSheaf HodgePilot.DLog

-- @@ L841-841 verbatim
open HodgePilot.ProjectiveLine HodgePilot.ProjectiveLineUnits

-- @@ L842-842 verbatim
open LaurentPolynomial

-- @@ L843-843 verbatim
open scoped Polynomial


-- @@ L845-845 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L847-848 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L850-851 verbatim
/-- The small Zariski site of the underlying space of the projective line. -/
abbrev JP1 := Opens.grothendieckTopology (p1 : TopCat)


-- @@ L853-859 verbatim
/-- **The Ω¹-sheaf of the projective line on the underlying space**: the
degree-1 term of the space-level de Rham complex
(`DeRhamSheaf.deRhamSheafSpace` at the structure constants), whose sections
on affine opens are the presented Kähler 1-forms of the section rings — no
sheafification anywhere (`DeRhamSheaf.isSheaf_presheafSite`). -/
abbrev omegaSheaf : Sheaf JP1 AddCommGrpCat.{0} :=
  DeRhamSheaf.deRhamSheafSpace φC 1


-- @@ L861-866 verbatim
/-- Receipt: `omegaSheaf` is the degree-1 term of the transported de Rham
complex of sheaves (definitional). -/
theorem omegaSheaf_receipt :
    omegaSheaf = (((Scheme.AffineZariskiSite.sheafEquiv (X := p1)
      (A := AddCommGrpCat.{0})).functor.mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (DeRhamSheaf.deRhamSheafComplexN φC)).X 1 := rfl


-- @@ L868-869 verbatim
theorem isAffineOpen_U0 : IsAffineOpen U0 :=
  Proj.isAffineOpen_basicOpen 𝒜₂ (MvPolynomial.X 0) (X_mem_grade_one 0) one_pos


-- @@ L871-872 verbatim
theorem isAffineOpen_U1 : IsAffineOpen U1 :=
  Proj.isAffineOpen_basicOpen 𝒜₂ (MvPolynomial.X 1) (X_mem_grade_one 1) one_pos


-- @@ L874-876 verbatim
theorem isAffineOpen_U01 : IsAffineOpen (U0 ⊓ U1) := by
  rw [U0_inf_U1]
  exact Proj.isAffineOpen_basicOpen 𝒜₂ _ hX01 two_pos


-- @@ L878-879 verbatim
/-- The first chart as an object of the small affine Zariski site. -/
def aU0 : p1.AffineZariskiSite := ⟨U0, isAffineOpen_U0⟩


-- @@ L881-882 verbatim
/-- The second chart as an object of the small affine Zariski site. -/
def aU1 : p1.AffineZariskiSite := ⟨U1, isAffineOpen_U1⟩


-- @@ L884-885 verbatim
/-- The chart overlap as an object of the small affine Zariski site. -/
def aU01 : p1.AffineZariskiSite := ⟨U0 ⊓ U1, isAffineOpen_U01⟩


-- @@ L887-895 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The dense-subsite equivalence unit at the degree-1 de Rham sheaf, as an
isomorphism of presheaves restricted along the affine site inclusion. -/
def unitRestrictionIso :
    (Scheme.AffineZariskiSite.toOpensFunctor p1).op ⋙ DLog.drAbOpens φC 1 ≅
      (Scheme.AffineZariskiSite.toOpensFunctor p1).op ⋙ omegaSheaf.obj :=
  (sheafToPresheaf _ _).mapIso
    ((Scheme.AffineZariskiSite.sheafEquiv (X := p1)
      (A := AddCommGrpCat.{0})).unitIso.app (DeRhamSheaf.deRhamSheafAb φC 1))


-- @@ L897-903 verbatim
/-- **The sections comparison**: the presheaf morphism from the presheaf of
presented degree-1 Kähler forms on all opens (`DLog.drAbOpens`) to the
Ω¹-sheaf on the space, extending the dense-subsite equivalence unit along
Mathlib's cover-dense `sheafHom`.  Natural over ALL opens; an isomorphism on
the components at affine opens (`isIso_secComparison_app`). -/
def secComparison : DLog.drAbOpens φC 1 ⟶ omegaSheaf.obj :=
  Functor.IsCoverDense.sheafHom (ℱ' := omegaSheaf) unitRestrictionIso.hom


-- @@ L905-911 verbatim
theorem secComparison_app_site (W : p1.AffineZariskiSite) :
    secComparison.app (op W.toOpens) = unitRestrictionIso.hom.app (op W) :=
  congrArg
    (fun (t : (Scheme.AffineZariskiSite.toOpensFunctor p1).op ⋙ DLog.drAbOpens φC 1 ⟶
        (Scheme.AffineZariskiSite.toOpensFunctor p1).op ⋙ omegaSheaf.obj) =>
      t.app (op W))
    (Functor.IsCoverDense.sheafHom_restrict_eq unitRestrictionIso.hom)


-- @@ L913-916 verbatim
theorem isIso_secComparison_app (W : p1.AffineZariskiSite) :
    IsIso (secComparison.app (op W.toOpens)) := by
  rw [secComparison_app_site]
  exact inferInstanceAs (IsIso ((unitRestrictionIso.app (op W)).hom))


-- @@ L918-918 verbatim
/-! ### The edge input `dz/z` as a section of the Ω¹-sheaf -/


-- @@ L920-924 verbatim
/-- **The ring-level edge input**: the image of `TwoChartResidue`'s literal
`dz/z = dlog (tUnit)` under the overlap coordinate map, as a presented
degree-1 Kähler form of the overlap section ring. -/
def omegaRing : DeRham.DR ℂ (Sec φC (U0 ⊓ U1)) 1 :=
  DeRham.map overlapAlgHom 1 (DLog.dlog ℂ ℂ[T;T⁻¹] (ContentAnchor.tUnit ℂ))


-- @@ L926-931 verbatim
/-- Statement-drift guard (definitional receipt): `omegaRing` is the literal
`dlog` of `ContentAnchor`'s `tUnit` — the calibrated `dz/z` of
`TwoChartResidue` — pushed along the overlap coordinate. -/
theorem omegaRing_receipt :
    omegaRing = DeRham.map overlapAlgHom 1
      (DLog.dlog ℂ ℂ[T;T⁻¹] (ContentAnchor.tUnit ℂ)) := rfl


-- @@ L933-935 verbatim
/-- The edge input as a section of the Ω¹-sheaf over the chart overlap. -/
def omegaSec : omegaSheaf.obj.obj (op (U0 ⊓ U1)) :=
  secComparison.app (op (U0 ⊓ U1)) omegaRing


-- @@ L937-940 verbatim
/-- The edge input as a degree-0 `Sheaf.H'`-class over the chart overlap
(along the Part-1 sections identification). -/
def omegaH : Ext (freeYonedaSheaf JP1 (U0 ⊓ U1)) omegaSheaf 0 :=
  (h0SectionsEquiv omegaSheaf (U0 ⊓ U1)).symm omegaSec


-- @@ L942-947 verbatim
/-- **The graded edge class of `dz/z`**: the image of `omegaH` under the
connecting map `δ` of Riou's Mayer–Vietoris sequence for the two-chart square
of the projective line, a degree-1 class of the Ω¹-sheaf in the sense of
Mathlib's `Sheaf.H'` (at the object `U0 ⊔ U1` of the square). -/
def edgeClassGraded : Ext (freeYonedaSheaf JP1 (U0 ⊔ U1)) omegaSheaf 1 :=
  (Opens.mayerVietorisSquare U0 U1).δ omegaSheaf 0 1 rfl omegaH


-- @@ L949-952 verbatim
/-- Receipt: the square's fourth object is `U0 ⊔ U1`, definitionally (wave
1's receipt, restated here for self-containment). -/
theorem mvSquare_X₄_receipt :
    (Opens.mayerVietorisSquare U0 U1).toSquare.X₄ = U0 ⊔ U1 := rfl


-- @@ L954-954 verbatim
/-! ### The residue functional through the comparison -/


-- @@ L956-960 verbatim
/-- The inverse of the sections comparison at the overlap. -/
def kappaU01Inv : omegaSheaf.obj.obj (op (U0 ⊓ U1)) ⟶
    (DLog.drAbOpens φC 1).obj (op (U0 ⊓ U1)) :=
  letI : IsIso (secComparison.app (op (U0 ⊓ U1))) := isIso_secComparison_app aU01
  inv (secComparison.app (op (U0 ⊓ U1)))


-- @@ L962-965 verbatim
theorem kappaInv_kappa (t : (DLog.drAbOpens φC 1).obj (op (U0 ⊓ U1))) :
    kappaU01Inv (secComparison.app (op (U0 ⊓ U1)) t) = t := by
  letI : IsIso (secComparison.app (op (U0 ⊓ U1))) := isIso_secComparison_app aU01
  exact IsIso.hom_inv_id_apply _ t


-- @@ L967-971 verbatim
/-- **The residue functional on overlap sections of the Ω¹-sheaf**: pull back
along the comparison, evaluate the inverse overlap coordinate, take
`TwoChartResidue`'s residue. -/
def PhiSec (s : omegaSheaf.obj.obj (op (U0 ⊓ U1))) : ℂ :=
  TwoChartResidue.residueLin ℂ (DeRham.map overlapInvAlgHom 1 (kappaU01Inv s))


-- @@ L973-977 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem PhiSec_sub (s t : omegaSheaf.obj.obj (op (U0 ⊓ U1))) :
    PhiSec (s - t) = PhiSec s - PhiSec t := by
  unfold PhiSec
  rw [map_sub, map_sub, map_sub]


-- @@ L979-1004 verbatim
/-- `Φ` takes the value `1` on the edge input `dz/z` — the calibration key,
inherited from `TwoChartResidue.residueLin_dlog_tUnit`. -/
theorem PhiSec_omegaSec : PhiSec omegaSec = 1 := by
  show TwoChartResidue.residueLin ℂ (DeRham.map overlapInvAlgHom 1
    (kappaU01Inv (secComparison.app (op (U0 ⊓ U1)) omegaRing))) = 1
  rw [kappaInv_kappa]
  show TwoChartResidue.residueLin ℂ (DeRham.map overlapInvAlgHom 1
    (DeRham.map overlapAlgHom 1 (DLog.dlog ℂ ℂ[T;T⁻¹] (ContentAnchor.tUnit ℂ)))) = 1
  have hcomp : DeRham.map overlapInvAlgHom 1 (DeRham.map overlapAlgHom 1
      (DLog.dlog ℂ ℂ[T;T⁻¹] (ContentAnchor.tUnit ℂ))) =
      DeRham.map (overlapInvAlgHom.comp overlapAlgHom) 1
        (DLog.dlog ℂ ℂ[T;T⁻¹] (ContentAnchor.tUnit ℂ)) := by
    rw [DeRham.map_comp]
    rfl
  rw [hcomp, DLog.map_dlog]
  have hunit : Units.map ((overlapInvAlgHom.comp overlapAlgHom :
      ℂ[T;T⁻¹] →ₐ[ℂ] ℂ[T;T⁻¹]) : ℂ[T;T⁻¹] →* ℂ[T;T⁻¹]) (ContentAnchor.tUnit ℂ) =
      ContentAnchor.tUnit ℂ := by
    apply Units.ext
    show (overlapInvAlgHom.comp overlapAlgHom)
      ((ContentAnchor.tUnit ℂ : (ℂ[T;T⁻¹])ˣ) : ℂ[T;T⁻¹]) = _
    rw [ContentAnchor.tUnit_val]
    show overlapInvAlgHom (overlapAlgHom (T 1)) = T 1
    exact overlapInvAlgHom_overlapAlgHom_T
  rw [hunit]
  exact TwoChartResidue.residueLin_dlog_tUnit ℂ


-- @@ L1006-1007 verbatim
/-! ### The chart squares: restriction of the chart coordinate is the
overlap coordinate (`TwoChartResidue`'s literal `chartEmbed`) -/


-- @@ L1009-1020 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Restriction along a factored inclusion splits into two restrictions
(any witnesses; the arrows are unique). -/
theorem presheaf_map_arrowSplit {V W W' : p1.Opens} (h : V ≤ W)
    (h1 : V ≤ W') (h2 : W' ≤ W) (z : Γ(p1, W)) :
    p1.presheaf.map (homOfLE h).op z =
      p1.presheaf.map (homOfLE h1).op (p1.presheaf.map (homOfLE h2).op z) := by
  have harr : (homOfLE h).op = (homOfLE h2).op ≫ (homOfLE h1).op := by
    rw [← op_comp]
    exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)
  rw [harr]
  exact congrArg (fun (t : Γ(p1, W) ⟶ Γ(p1, V)) => t z) (p1.presheaf.map_comp _ _)


-- @@ L1022-1042 verbatim
theorem res_chartHomA_X_left :
    DeRhamPresheaf.res φC (inf_le_left : U0 ⊓ U1 ≤ U0) (chartHomA 0 1 Polynomial.X) =
      overlapRingHom awayNum := by
  rw [chartHomA_X]
  show p1.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op
    (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0) (coordFrac 0 1)) = overlapRingHom awayNum
  have hres := Proj.awayMap_awayToSection (𝒜 := 𝒜₂) (X_mem_grade_one 1)
    (rfl : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.X 0 * MvPolynomial.X 1)
  have hpt := congrArg
    (fun t : CommRingCat.of (Away 𝒜₂ (MvPolynomial.X 0)) ⟶
        Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) =>
      t (coordFrac 0 1)) hres
  simp only [CategoryTheory.comp_apply] at hpt
  rw [presheaf_map_arrowSplit (inf_le_left : U0 ⊓ U1 ≤ U0) (le_of_eq U0_inf_U1)
    (Proj.basicOpen_mono 𝒜₂ _ _ ⟨_, rfl⟩), ← hpt]
  exact congrArg
    (fun z : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) =>
      p1.presheaf.map (homOfLE (le_of_eq U0_inf_U1)).op
        (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) z))
    awayMap_coordFrac


-- @@ L1044-1073 verbatim
/-- The `awayMap` to the overlap carries the second chart's coordinate
fraction to `awayNumInv` (the swapped-index companion of wave 2's
`awayMap_coordFrac`). -/
theorem awayMap_coordFrac' :
    awayMap 𝒜₂ (X_mem_grade_one 0)
      (show (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
        MvPolynomial.X 1 * MvPolynomial.X 0 from mul_comm _ _)
      (coordFrac 1 0) = awayNumInv := by
  apply HomogeneousLocalization.val_injective
  have h1 : (awayMap 𝒜₂ (X_mem_grade_one 0)
      (show (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
        MvPolynomial.X 1 * MvPolynomial.X 0 from mul_comm _ _)
      (coordFrac 1 0)).val =
      Localization.mk (MvPolynomial.X 0 * MvPolynomial.X 0 ^ 1)
        (⟨(MvPolynomial.X 0 * MvPolynomial.X 1) ^ 1, 1, rfl⟩ :
          Submonoid.powers
            (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ)) := by
    rw [show coordFrac 1 0 = HomogeneousLocalization.Away.mk 𝒜₂ (X_mem_grade_one 1) 1
        (MvPolynomial.X 0) ((one_smul ℕ 1).symm ▸ X_mem_grade_one 0) from rfl,
      awayMap_mk]
    exact HomogeneousLocalization.Away.val_mk _ _ _ _ _
  have h2 : (awayNumInv).val =
      Localization.mk (MvPolynomial.X 0 * MvPolynomial.X 0)
        (⟨(MvPolynomial.X 0 * MvPolynomial.X 1) ^ 1, 1, rfl⟩ :
          Submonoid.powers
            (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ)) :=
    HomogeneousLocalization.Away.val_mk _ _ _ _ _
  rw [h1, h2, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  ring


-- @@ L1075-1096 verbatim
theorem res_chartHomA_X_right :
    DeRhamPresheaf.res φC (inf_le_right : U0 ⊓ U1 ≤ U1) (chartHomA 1 0 Polynomial.X) =
      overlapRingHom awayNumInv := by
  rw [chartHomA_X]
  show p1.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op
    (Proj.awayToSection 𝒜₂ (MvPolynomial.X 1) (coordFrac 1 0)) = overlapRingHom awayNumInv
  have hres := Proj.awayMap_awayToSection (𝒜 := 𝒜₂) (X_mem_grade_one 0)
    (show (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.X 1 * MvPolynomial.X 0 from mul_comm _ _)
  have hpt := congrArg
    (fun t : CommRingCat.of (Away 𝒜₂ (MvPolynomial.X 1)) ⟶
        Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) =>
      t (coordFrac 1 0)) hres
  simp only [CategoryTheory.comp_apply] at hpt
  rw [presheaf_map_arrowSplit (inf_le_right : U0 ⊓ U1 ≤ U1) (le_of_eq U0_inf_U1)
    (Proj.basicOpen_mono 𝒜₂ _ _
      ⟨_, mul_comm (MvPolynomial.X 0) (MvPolynomial.X 1)⟩), ← hpt]
  exact congrArg
    (fun z : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) =>
      p1.presheaf.map (homOfLE (le_of_eq U0_inf_U1)).op
        (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) z))
    awayMap_coordFrac'


-- @@ L1098-1109 verbatim
/-- **The left chart square** (receipt pinning to `TwoChartResidue`'s literal
`chartEmbed ℂ 1`): the inverse overlap coordinate carries the restriction of
the first chart's coordinate to the `z`-chart embedding. -/
theorem overlapInv_res_chartHomA_left :
    overlapInvAlgHom.comp
        ((DeRhamPresheaf.res φC (inf_le_left : U0 ⊓ U1 ≤ U0)).comp (chartHomA 0 1)) =
      TwoChartResidue.chartEmbed ℂ 1 := by
  apply Polynomial.algHom_ext
  show overlapInvAlgHom (DeRhamPresheaf.res φC inf_le_left
    (chartHomA 0 1 Polynomial.X)) = TwoChartResidue.chartEmbed ℂ 1 Polynomial.X
  rw [res_chartHomA_X_left, overlapInvAlgHom_overlapRingHom, overlapEvalRing_awayNum,
    TwoChartResidue.chartEmbed_X]


-- @@ L1111-1121 verbatim
/-- **The right chart square** (receipt pinning to `TwoChartResidue`'s
literal `chartEmbed ℂ (-1)`). -/
theorem overlapInv_res_chartHomA_right :
    overlapInvAlgHom.comp
        ((DeRhamPresheaf.res φC (inf_le_right : U0 ⊓ U1 ≤ U1)).comp (chartHomA 1 0)) =
      TwoChartResidue.chartEmbed ℂ (-1) := by
  apply Polynomial.algHom_ext
  show overlapInvAlgHom (DeRhamPresheaf.res φC inf_le_right
    (chartHomA 1 0 Polynomial.X)) = TwoChartResidue.chartEmbed ℂ (-1) Polynomial.X
  rw [res_chartHomA_X_right, overlapInvAlgHom_overlapRingHom, overlapEvalRing_awayNumInv,
    TwoChartResidue.chartEmbed_X]


-- @@ L1123-1134 verbatim
/-- **The forward left chart square** (receipt): the overlap coordinate
composed with `TwoChartResidue`'s literal `chartEmbed ℂ 1` is restriction of
the chart coordinate. -/
theorem overlapAlgHom_chartEmbed_left :
    overlapAlgHom.comp (TwoChartResidue.chartEmbed ℂ 1) =
      (DeRhamPresheaf.res φC (inf_le_left : U0 ⊓ U1 ≤ U0)).comp (chartHomA 0 1) := by
  apply Polynomial.algHom_ext
  show overlapAlgHom (TwoChartResidue.chartEmbed ℂ 1 Polynomial.X) = _
  rw [TwoChartResidue.chartEmbed_X, overlapAlgHom_T]
  show (overlapUnit : Γ(p1, U0 ⊓ U1)) =
    DeRhamPresheaf.res φC inf_le_left (chartHomA 0 1 Polynomial.X)
  rw [res_chartHomA_X_left, overlapUnit_coe]


-- @@ L1136-1145 verbatim
/-- **The forward right chart square** (receipt). -/
theorem overlapAlgHom_chartEmbed_right :
    overlapAlgHom.comp (TwoChartResidue.chartEmbed ℂ (-1)) =
      (DeRhamPresheaf.res φC (inf_le_right : U0 ⊓ U1 ≤ U1)).comp (chartHomA 1 0) := by
  apply Polynomial.algHom_ext
  show overlapAlgHom (TwoChartResidue.chartEmbed ℂ (-1) Polynomial.X) = _
  rw [TwoChartResidue.chartEmbed_X, overlapAlgHom_T_neg]
  show ((overlapUnit⁻¹ : (Γ(p1, U0 ⊓ U1))ˣ) : Γ(p1, U0 ⊓ U1)) =
    DeRhamPresheaf.res φC inf_le_right (chartHomA 1 0 Polynomial.X)
  rw [res_chartHomA_X_right, overlapUnit_inv_coe]


-- @@ L1147-1177 verbatim
/-- **`TwoChartResidue`'s literal difference-map receipt**: through the
overlap coordinate, the ring-level `chartDifference` of `TwoChartResidue`
becomes the difference of the two chart restrictions. -/
theorem chartDifference_receipt (a b : TwoChartResidue.chartOneForms ℂ) :
    DeRham.map overlapAlgHom 1 (TwoChartResidue.chartDifference ℂ (a, b)) =
      DeRham.map (DeRhamPresheaf.res φC (inf_le_left : U0 ⊓ U1 ≤ U0)) 1
        (DeRham.map (chartHomA 0 1) 1 a) -
      DeRham.map (DeRhamPresheaf.res φC (inf_le_right : U0 ⊓ U1 ≤ U1)) 1
        (DeRham.map (chartHomA 1 0) 1 b) := by
  rw [TwoChartResidue.chartDifference_apply, map_sub]
  have hL : DeRham.map overlapAlgHom 1 (TwoChartResidue.chartRes ℂ 1 a) =
      DeRham.map (DeRhamPresheaf.res φC (inf_le_left : U0 ⊓ U1 ≤ U0)) 1
        (DeRham.map (chartHomA 0 1) 1 a) := by
    show DeRham.map overlapAlgHom 1 (DeRham.map (TwoChartResidue.chartEmbed ℂ 1) 1 a) = _
    rw [show DeRham.map overlapAlgHom 1 (DeRham.map (TwoChartResidue.chartEmbed ℂ 1) 1 a) =
        DeRham.map (overlapAlgHom.comp (TwoChartResidue.chartEmbed ℂ 1)) 1 a from by
      rw [DeRham.map_comp]; rfl]
    rw [overlapAlgHom_chartEmbed_left]
    rw [DeRham.map_comp]
    rfl
  have hR : DeRham.map overlapAlgHom 1 (TwoChartResidue.chartRes ℂ (-1) b) =
      DeRham.map (DeRhamPresheaf.res φC (inf_le_right : U0 ⊓ U1 ≤ U1)) 1
        (DeRham.map (chartHomA 1 0) 1 b) := by
    show DeRham.map overlapAlgHom 1 (DeRham.map (TwoChartResidue.chartEmbed ℂ (-1)) 1 b) = _
    rw [show DeRham.map overlapAlgHom 1 (DeRham.map (TwoChartResidue.chartEmbed ℂ (-1)) 1 b) =
        DeRham.map (overlapAlgHom.comp (TwoChartResidue.chartEmbed ℂ (-1))) 1 b from by
      rw [DeRham.map_comp]; rfl]
    rw [overlapAlgHom_chartEmbed_right]
    rw [DeRham.map_comp]
    rfl
  rw [hL, hR]


-- @@ L1179-1179 verbatim
/-! ### Surjectivity of the de Rham map along a surjective algebra map -/


-- @@ L1181-1199 verbatim
theorem drMap_surjective {A B C' : Type} [CommRing A] [CommRing B] [CommRing C']
    [Algebra A B] [Algebra A C'] (ψ : B →ₐ[A] C') (hψ : Function.Surjective ψ)
    (n : ℕ) : Function.Surjective (DeRham.map ψ n) := by
  intro x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction w using Finsupp.induction_linear with
  | zero =>
      exact ⟨0, by rw [map_zero, Submodule.Quotient.mk_zero]⟩
  | add f g hf hg =>
      obtain ⟨yf, hyf⟩ := hf
      obtain ⟨yg, hyg⟩ := hg
      exact ⟨yf + yg, by rw [map_add, hyf, hyg, Submodule.Quotient.mk_add]⟩
  | single t s =>
      choose tb htb using fun k => hψ (t k)
      obtain ⟨sb, hsb⟩ := hψ s
      refine ⟨Submodule.Quotient.mk (Finsupp.single tb sb), ?_⟩
      rw [DeRham.map_mk_single]
      have h1 : (⇑ψ ∘ tb) = t := funext htb
      rw [h1, hsb]


-- @@ L1201-1201 verbatim
/-! ### The kill lemmas and THE THEOREM -/


-- @@ L1203-1238 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- `Φ` kills the restriction of any section over the first chart (the
polynomial-tail argument of `TwoChartResidue.residueLin_zChart`, routed
through the chart algebra map and the comparison). -/
theorem PhiSec_res_left (s : omegaSheaf.obj.obj (op U0)) :
    PhiSec (omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op s) = 0 := by
  letI : IsIso (secComparison.app (op U0)) := isIso_secComparison_app aU0
  obtain ⟨s', rfl⟩ : ∃ s', secComparison.app (op U0) s' = s :=
    ⟨inv (secComparison.app (op U0)) s, IsIso.inv_hom_id_apply _ _⟩
  have hnat : omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
      (secComparison.app (op U0) s') =
      secComparison.app (op (U0 ⊓ U1))
        ((DLog.drAbOpens φC 1).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op s') :=
    (congrArg
      (fun (t : (DLog.drAbOpens φC 1).obj (op U0) ⟶ omegaSheaf.obj.obj (op (U0 ⊓ U1))) =>
        t s')
      (secComparison.naturality ((Opens.mayerVietorisSquare U0 U1).f₁₂).op)).symm
  rw [hnat]
  show TwoChartResidue.residueLin ℂ (DeRham.map overlapInvAlgHom 1
    (kappaU01Inv (secComparison.app (op (U0 ⊓ U1))
      ((DLog.drAbOpens φC 1).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op s')))) = 0
  rw [kappaInv_kappa]
  obtain ⟨a, rfl⟩ := drMap_surjective (chartHomA 0 1)
    (chartHomA_surjective 0 1 (by decide)) 1 s'
  show TwoChartResidue.residueLin ℂ (DeRham.map overlapInvAlgHom 1
    (DeRham.map (DeRhamPresheaf.res φC (leOfHom (Opens.mayerVietorisSquare U0 U1).f₁₂)) 1
      (DeRham.map (chartHomA 0 1) 1 a))) = 0
  have hcomp : DeRham.map overlapInvAlgHom 1
      (DeRham.map (DeRhamPresheaf.res φC (leOfHom (Opens.mayerVietorisSquare U0 U1).f₁₂)) 1
        (DeRham.map (chartHomA 0 1) 1 a)) =
      DeRham.map (overlapInvAlgHom.comp
        ((DeRhamPresheaf.res φC (inf_le_left : U0 ⊓ U1 ≤ U0)).comp (chartHomA 0 1))) 1 a := by
    rw [DeRham.map_comp, DeRham.map_comp]
    rfl
  rw [hcomp, overlapInv_res_chartHomA_left]
  exact TwoChartResidue.residueLin_zChart ℂ a


-- @@ L1240-1274 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- `Φ` kills the restriction of any section over the second chart
(`TwoChartResidue.residueLin_wChart`). -/
theorem PhiSec_res_right (s : omegaSheaf.obj.obj (op U1)) :
    PhiSec (omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op s) = 0 := by
  letI : IsIso (secComparison.app (op U1)) := isIso_secComparison_app aU1
  obtain ⟨s', rfl⟩ : ∃ s', secComparison.app (op U1) s' = s :=
    ⟨inv (secComparison.app (op U1)) s, IsIso.inv_hom_id_apply _ _⟩
  have hnat : omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op
      (secComparison.app (op U1) s') =
      secComparison.app (op (U0 ⊓ U1))
        ((DLog.drAbOpens φC 1).map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op s') :=
    (congrArg
      (fun (t : (DLog.drAbOpens φC 1).obj (op U1) ⟶ omegaSheaf.obj.obj (op (U0 ⊓ U1))) =>
        t s')
      (secComparison.naturality ((Opens.mayerVietorisSquare U0 U1).f₁₃).op)).symm
  rw [hnat]
  show TwoChartResidue.residueLin ℂ (DeRham.map overlapInvAlgHom 1
    (kappaU01Inv (secComparison.app (op (U0 ⊓ U1))
      ((DLog.drAbOpens φC 1).map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op s')))) = 0
  rw [kappaInv_kappa]
  obtain ⟨a, rfl⟩ := drMap_surjective (chartHomA 1 0)
    (chartHomA_surjective 1 0 (by decide)) 1 s'
  show TwoChartResidue.residueLin ℂ (DeRham.map overlapInvAlgHom 1
    (DeRham.map (DeRhamPresheaf.res φC (leOfHom (Opens.mayerVietorisSquare U0 U1).f₁₃)) 1
      (DeRham.map (chartHomA 1 0) 1 a))) = 0
  have hcomp : DeRham.map overlapInvAlgHom 1
      (DeRham.map (DeRhamPresheaf.res φC (leOfHom (Opens.mayerVietorisSquare U0 U1).f₁₃)) 1
        (DeRham.map (chartHomA 1 0) 1 a)) =
      DeRham.map (overlapInvAlgHom.comp
        ((DeRhamPresheaf.res φC (inf_le_right : U0 ⊓ U1 ≤ U1)).comp (chartHomA 1 0))) 1 a := by
    rw [DeRham.map_comp, DeRham.map_comp]
    rfl
  rw [hcomp, overlapInv_res_chartHomA_right]
  exact TwoChartResidue.residueLin_wChart ℂ a


-- @@ L1276-1335 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **THE THEOREM (Step 2, the G3-graded rung)**: the edge class of `dz/z` is
**nonzero** in `H¹` of the degree-1 de Rham sheaf of the projective line, in
the sense of Mathlib's `Sheaf.H'` at the object `U0 ⊔ U1` of the two-chart
Mayer–Vietoris square.

By exactness of Riou's Mayer–Vietoris sequence (`ker δ = im fromBiprod` — no
acyclicity input of any kind), vanishing of the edge class would express the
overlap form `dz/z` as a difference of forms extending to the two charts;
the residue functional of `HodgePilot.TwoChartResidue` kills every such
difference while taking the value `1` on `dz/z`.  Nothing here makes the
Hodge conjecture statable. -/
theorem edgeClassGraded_ne_zero : edgeClassGraded ≠ 0 := by
  intro hzero
  have hex := ((Opens.mayerVietorisSquare U0 U1).sequence_exact omegaSheaf 0 1 rfl).exact 1
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp hex omegaH hzero
  have hb' : (Opens.mayerVietorisSquare U0 U1).fromBiprod omegaSheaf 0 b = omegaH := hb
  set p := (AddCommGrpCat.biprodIsoProd
    (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂)
    (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃)).hom b with hp
  have hbinv : (AddCommGrpCat.biprodIsoProd _ _).inv p = b := by
    rw [hp]
    exact Iso.hom_inv_id_apply _ b
  have homega : omegaH =
      (omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op p.1 -
      (omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op p.2 :=
    hb'.symm.trans
      ((congrArg (fun z => (Opens.mayerVietorisSquare U0 U1).fromBiprod omegaSheaf 0 z)
        hbinv.symm).trans
        ((Opens.mayerVietorisSquare U0 U1).fromBiprod_biprodIsoProd_inv_apply
          omegaSheaf p.1 p.2))
  have hsecL : h0ToSections omegaSheaf (U0 ⊓ U1)
      ((omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op p.1) =
      omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
        (h0ToSections omegaSheaf (Opens.mayerVietorisSquare U0 U1).toSquare.X₂ p.1) :=
    (h0ToSections_natural omegaSheaf (Opens.mayerVietorisSquare U0 U1).f₁₂ p.1).symm
  have hsecR : h0ToSections omegaSheaf (U0 ⊓ U1)
      ((omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op p.2) =
      omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op
        (h0ToSections omegaSheaf (Opens.mayerVietorisSquare U0 U1).toSquare.X₃ p.2) :=
    (h0ToSections_natural omegaSheaf (Opens.mayerVietorisSquare U0 U1).f₁₃ p.2).symm
  have hsec : omegaSec =
      omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
        (h0ToSections omegaSheaf (Opens.mayerVietorisSquare U0 U1).toSquare.X₂ p.1) -
      omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op
        (h0ToSections omegaSheaf (Opens.mayerVietorisSquare U0 U1).toSquare.X₃ p.2) := by
    have h1 : h0ToSections omegaSheaf (U0 ⊓ U1) omegaH = omegaSec :=
      (h0SectionsEquiv omegaSheaf (U0 ⊓ U1)).apply_symm_apply omegaSec
    rw [← h1, homega]
    rw [show h0ToSections omegaSheaf (U0 ⊓ U1)
        ((omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op p.1 -
         (omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op p.2) =
        h0SectionsEquiv omegaSheaf (U0 ⊓ U1)
          ((omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op p.1 -
           (omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op p.2)
      from rfl, map_sub]
    rw [h0SectionsEquiv_apply, h0SectionsEquiv_apply, hsecL, hsecR]
  have hval : PhiSec omegaSec = 1 := PhiSec_omegaSec
  rw [hsec, PhiSec_sub, PhiSec_res_left, PhiSec_res_right, sub_zero] at hval
  exact one_ne_zero hval.symm


-- @@ L1337-1337 verbatim
/-! ### Step 3(a): the class in Mathlib's `Sheaf.H` -/


-- @@ L1339-1343 verbatim
/-- The graded edge class re-anchored at `⊤` (the two charts cover the
projective line, `U0_sup_U1`). -/
def edgeClassTop : Ext (freeYonedaSheaf JP1 (⊤ : p1.Opens)) omegaSheaf 1 :=
  CycCarrier.extReanchorLeft
    (eqToIso (congrArg (freeYonedaSheaf JP1) U0_sup_U1)) 1 edgeClassGraded


-- @@ L1345-1354 verbatim
theorem edgeClassTop_ne_zero : edgeClassTop ≠ 0 := by
  intro h
  have h2 := congrArg
    (fun z => (CycCarrier.extReanchorLeft
      (eqToIso (congrArg (freeYonedaSheaf JP1) U0_sup_U1)) 1).symm z) h
  have h3 : (CycCarrier.extReanchorLeft
      (eqToIso (congrArg (freeYonedaSheaf JP1) U0_sup_U1)) 1).symm edgeClassTop =
      edgeClassGraded :=
    AddEquiv.symm_apply_apply _ _
  exact edgeClassGraded_ne_zero ((h3.symm.trans h2).trans (map_zero _))


-- @@ L1356-1362 verbatim
/-- **The edge class of `dz/z` in Mathlib's `Sheaf.H`**: the graded edge
class, re-anchored at `⊤` and transported along the Part-1 terminal-anchor
re-isomorphism to the constant-`ULift ℤ` anchor of `Sheaf.H`.  Nothing here
makes the Hodge conjecture statable. -/
def edgeClassH : Sheaf.H omegaSheaf 1 :=
  hPrimeTopEquivH (⊤ : p1.Opens) (CartierClass.opensTopIsTerminal p1)
    omegaSheaf 1 edgeClassTop


-- @@ L1364-1379 verbatim
/-- **THE THEOREM at the `Sheaf.H` anchor**: the edge class of `dz/z` is a
nonzero element of `H¹` of the degree-1 de Rham sheaf of the projective line
in the sense of Mathlib's `Sheaf.H`.  (`H¹(X, Ω¹)` is *classically* the home
of the first Chern class of a point; no comparison with any other cohomology
theory — nor with the degree-2 hypercohomology graded level, see
`GradedTruncationDetection` — is stated or claimed.  Nothing here makes the
Hodge conjecture statable.) -/
theorem edgeClassH_ne_zero : edgeClassH ≠ 0 := by
  intro h
  have h2 := congrArg
    (fun z => (hPrimeTopEquivH (⊤ : p1.Opens) (CartierClass.opensTopIsTerminal p1)
      omegaSheaf 1).symm z) h
  have h3 : (hPrimeTopEquivH (⊤ : p1.Opens) (CartierClass.opensTopIsTerminal p1)
      omegaSheaf 1).symm edgeClassH = edgeClassTop :=
    AddEquiv.symm_apply_apply _ _
  exact edgeClassTop_ne_zero ((h3.symm.trans h2).trans (map_zero _))


-- @@ L1381-1384 verbatim
/-- `H¹` of the Ω¹-sheaf of the projective line is a nontrivial group, in the
sense of Mathlib's `Sheaf.H`. -/
theorem nontrivial_omegaH1 : Nontrivial (Sheaf.H omegaSheaf 1) :=
  ⟨⟨edgeClassH, 0, edgeClassH_ne_zero⟩⟩


-- @@ L1386-1386 verbatim
/-! ### The falsifier suite: negative controls -/


-- @@ L1388-1420 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Negative control, general form**: any class restricted from the first
chart maps to zero under the same `δ`-route (`fromBiprod_δ` — a form that
extends to a chart has vanishing edge class). -/
theorem edgeRoute_restriction_eq_zero
    (y : Ext (freeYonedaSheaf JP1 U0) omegaSheaf 0) :
    (Opens.mayerVietorisSquare U0 U1).δ omegaSheaf 0 1 rfl
      ((omegaSheaf.cohomologyPresheaf 0).map
        ((Opens.mayerVietorisSquare U0 U1).f₁₂).op y) = 0 := by
  have h1 : (omegaSheaf.cohomologyPresheaf 0).map
      ((Opens.mayerVietorisSquare U0 U1).f₁₂).op y =
      (Opens.mayerVietorisSquare U0 U1).fromBiprod omegaSheaf 0
        ((AddCommGrpCat.biprodIsoProd _ _).inv
          ((y, 0) : (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂) ×
            (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃))) := by
    rw [(Opens.mayerVietorisSquare U0 U1).fromBiprod_biprodIsoProd_inv_apply
      omegaSheaf y 0, map_zero, sub_zero]
  rw [h1]
  have h2 := congrArg
    (fun (t : ((omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂) ⊞
        (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃) :
          AddCommGrpCat.{0}) ⟶
        omegaSheaf.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₄) =>
      t ((AddCommGrpCat.biprodIsoProd _ _).inv
          ((y, 0) : (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂) ×
            (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃))))
    ((Opens.mayerVietorisSquare U0 U1).fromBiprod_δ omegaSheaf 0 1 rfl)
  refine h2.trans ?_
  show ((0 : _ ⟶ omegaSheaf.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₄))
    ((AddCommGrpCat.biprodIsoProd _ _).inv
          ((y, 0) : (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂) ×
            (omegaSheaf.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃))) = 0
  rfl


-- @@ L1422-1426 verbatim
/-- The differential `dz` of the chart coordinate, as a ring-level presented
1-form of the first chart's coordinate ring (a form that extends to the
`z`-chart: its residue vanishes, unlike `dz/z`'s). -/
def dzChart : TwoChartResidue.chartOneForms ℂ :=
  Submodule.Quotient.mk (Finsupp.single (fun _ => Polynomial.X) (1 : Polynomial ℂ))


-- @@ L1428-1433 verbatim
/-- `dz` as a section of the Ω¹-sheaf over the overlap: the restriction of a
section defined over the whole first chart. -/
def dzSec : omegaSheaf.obj.obj (op (U0 ⊓ U1)) :=
  secComparison.app (op (U0 ⊓ U1))
    (DeRham.map (DeRhamPresheaf.res φC (inf_le_left : U0 ⊓ U1 ≤ U0)) 1
      (DeRham.map (chartHomA 0 1) 1 dzChart))


-- @@ L1435-1463 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Negative control, concrete instance**: the chart-extendable form `dz`
maps to zero under the same edge route that detects `dz/z`.  (A proof scheme
that secretly sent every overlap form to a nonzero class would collide with
this receipt.) -/
theorem edgeRoute_dz_eq_zero :
    (Opens.mayerVietorisSquare U0 U1).δ omegaSheaf 0 1 rfl
      ((h0SectionsEquiv omegaSheaf (U0 ⊓ U1)).symm dzSec) = 0 := by
  have hnat : dzSec = omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
      (secComparison.app (op U0) (DeRham.map (chartHomA 0 1) 1 dzChart)) := by
    show secComparison.app (op (U0 ⊓ U1))
        ((DLog.drAbOpens φC 1).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
          (DeRham.map (chartHomA 0 1) 1 dzChart)) = _
    exact congrArg
      (fun (t : (DLog.drAbOpens φC 1).obj (op U0) ⟶ omegaSheaf.obj.obj (op (U0 ⊓ U1))) =>
        t (DeRham.map (chartHomA 0 1) 1 dzChart))
      (secComparison.naturality ((Opens.mayerVietorisSquare U0 U1).f₁₂).op)
  rw [hnat]
  have hres : (h0SectionsEquiv omegaSheaf (U0 ⊓ U1)).symm
      (omegaSheaf.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
        (secComparison.app (op U0) (DeRham.map (chartHomA 0 1) 1 dzChart))) =
      (omegaSheaf.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
        ((h0SectionsEquiv omegaSheaf
          ((Opens.mayerVietorisSquare U0 U1).toSquare.X₂ : p1.Opens)).symm
          (secComparison.app (op U0) (DeRham.map (chartHomA 0 1) 1 dzChart))) := by
    rw [h0SectionsEquiv_symm_apply, h0SectionsEquiv_symm_apply]
    exact mk₀_sheafHomOfSection_natural omegaSheaf _ _
  rw [hres]
  exact edgeRoute_restriction_eq_zero _


-- @@ L1465-1466 verbatim
/-! ### The named unproved `Prop`s (registry style: stated, never proved,
never assumed, never used) -/


-- @@ L1468-1482 verbatim
/-- **Named unproved `Prop` — the truncation bridge (parked)**: the degree-2
hypercohomology of the `σ≥1`-truncated de Rham complex of the projective line
agrees with `H¹` of the degree-1 de Rham sheaf.  Classically this is the
degeneracy of the trivial truncation spectral sequence in the lowest window,
and for the projective line it holds because `Ω²` vanishes on every affine
open (the rank-1 Kähler exterior vanishing); **neither statement is proved,
assumed, or used anywhere in this development** — this `Prop` is a name for
that open end, in the registry style of `HyperHdRSpaceAgreement`.  Until it
carries a proof term, `edgeClassH_ne_zero` says nothing about the graded
piece `F¹ℍ²/F²ℍ²`.  Nothing here makes the Hodge conjecture statable. -/
def GradedTruncationDetection : Prop :=
  Nonempty (Hyper.sheafHyperH (Scheme.AffineZariskiSite.grothendieckTopology p1)
    (Hyper.zConstSheaf _)
    (Hyper.brutalTruncGE (DeRhamSheaf.deRhamSheafComplex φC) 1) 2 ≃+
      Sheaf.H omegaSheaf 1)


-- @@ L1484-1488 verbatim
/-- The exterior differential of the space-level de Rham sheaves in degree
zero, transported along the dense-subsite equivalence. -/
def dSpaceZeroOne : DeRhamSheaf.deRhamSheafSpace φC 0 ⟶ omegaSheaf :=
  (Scheme.AffineZariskiSite.sheafEquiv (X := p1)
    (A := AddCommGrpCat.{0})).functor.map (DeRhamSheaf.dSheafAb φC 0)


-- @@ L1490-1500 verbatim
/-- **Named unproved `Prop` — the interference exclusion (the honest wall)**:
the map `H¹(ℙ¹, O) → H¹(ℙ¹, Ω¹)` induced by the exterior differential kills
every class.  Classically this holds because `H¹(ℙ¹, O) = 0` (affine chart
acyclicity — Serre-type vanishing, which exists nowhere at this Mathlib);
**it is not proved, not assumed, and not used anywhere in this
development**.  Until it carries a proof term, no statement about the image
of `dz/z` in any de Rham hypercohomology group follows from this module.
Nothing here makes the Hodge conjecture statable. -/
def InterferenceExclusion : Prop :=
  ∀ x : Sheaf.H (DeRhamSheaf.deRhamSheafSpace φC 0) 1,
    Sheaf.H.map dSpaceZeroOne 1 x = 0


-- @@ L1502-1502 verbatim
end EdgeClass


-- @@ L1504-1504 verbatim
end ProjectiveLineGraded


-- @@ L1506-1506 verbatim
end HodgePilot


-- @@ L1508-1508 verbatim
end
