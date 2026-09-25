module

/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JHU Category Theory Seminar
-/
public import InfinityCosmos.ForMathlib.InfinityCosmos.Basic
public import Mathlib.CategoryTheory.Category.Basic


-- @@ L11-11 verbatim
@[expose] public section



-- @@ L14-33 verbatim
/-!
# Explicit isofibrations in an ∞-cosmos.

This file constructs a few explicit isofibrations in an ∞-cosmos as consequences of the axioms.

Simple examples include:

* `compIsofibration {A B C : K} (f : A ↠ B) (g : B ↠ C) : A ↠ C`
* `pullbackIsofibration {E B A : K} (p : E ↠ B) (f : A ⟶ B) : pullbackIsofibrationObj p f ↠ A`
* `toTerminalIsofibration (A : K) : A ↠ (⊤_ K)`

More elaborate examples include:

* `cotensorCovIsofibration (V : SSet.{v}) {A B : K} (f : A ↠ B) : V ⋔ A ↠ V ⋔ B`
* `cotensorContraIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] (A : K) : V ⋔ A ↠ U ⋔ A`
* `leibnizCotensorIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K} (f : A ↠ B) :`
    `V ⋔ A ↠ leibnizCotensorCod i f`

All but the first of these involve explicit choices of limits so are noncomputable.
-/


-- @@ L35-35 verbatim
namespace InfinityCosmos


-- @@ L37-37 verbatim
universe u v


-- @@ L39-39 verbatim
open CategoryTheory Category PreInfinityCosmos SimplicialCategory Enriched Limits InfinityCosmos

-- @@ L40-40 verbatim
open HasConicalTerminal


-- @@ L42-42 verbatim
variable {K : Type u} [Category.{v} K] [InfinityCosmos K]


-- @@ L44-46 expanded
/-- The composite of isofibrations. -/
def compIsofibration {A B C : K} (f : Isofibration A B) (g : Isofibration B C) : Isofibration A C :=
  ⟨(f.1 ≫ g.1), comp_isIsofibration f g⟩


-- @@ L48-50 expanded
@[simp]
lemma compIsofibration_map {A B C : K} (f : Isofibration A B) (g : Isofibration B C) :
    (compIsofibration f g).1 = f.1 ≫ g.1 :=
  rfl


-- @@ L52-54 expanded
/-- The object defined by pulling back an isofibration. -/
noncomputable def pullbackIsofibrationObj {E B A : K} (p : Isofibration E B) (f : A ⟶ B) : K :=
  pullback p.1 f


-- @@ L56-59 expanded
/-- The object defined by pulling back an isofibration. -/
noncomputable def pullbackIsofibration {E B A : K} (p : Isofibration E B) (f : A ⟶ B) :
    Isofibration (pullbackIsofibrationObj p f) A :=
  ⟨pullback.snd p.1 f, pullback_isIsofibration _ _ _ _ (IsPullback.of_hasPullback p.1 f)⟩


-- @@ L61-63 expanded
@[simp]
lemma pullbackIsofibration_map {E B A : K} (p : Isofibration E B) (f : A ⟶ B) :
    (pullbackIsofibration p f).1 = pullback.snd p.1 f :=
  rfl


-- @@ L65-66 verbatim
theorem toTerminal_fibrant (A : K) : IsIsofibration (terminal.from A) :=
  all_objects_fibrant terminalIsConicalTerminal _


-- @@ L68-70 expanded
/-- The explicit map `terminal.from A` is an isofibration in an ∞-cosmos. -/
noncomputable def toTerminalIsofibration (A : K) : Isofibration A (⊤_ K) :=
  ⟨terminal.from A, toTerminal_fibrant A⟩


-- @@ L72-73 verbatim
@[simp]
lemma toTerminalIsofibration_map (A : K) : (toTerminalIsofibration A).1 = terminal.from A := rfl


-- @@ L75-96 expanded
/-- Note: proven by Aristotle. -/
theorem binary_prod_map_fibrant {X Y X' Y' : K} {f : Isofibration X Y} {g : Isofibration X' Y'} :
    IsIsofibration (prod.map f.1 g.1) :=
  by
  rw [show prod.map f.1 g.1 = prod.map f.1 (𝟙 X') ≫ prod.map (𝟙 Y) g.1 from by
      rw [prod.map_map, comp_id, id_comp]]
  apply comp_isIsofibration ⟨_, ?_⟩ ⟨_, ?_⟩
  ·
    exact
      pullback_isIsofibration f prod.fst prod.fst (prod.map f.1 (𝟙 X'))
        (IsPullback.of_bot
          (by
            convert IsPullback.of_hasBinaryProduct' X X' using 1
            · simp [prod.map_snd]
            · simp [terminal.comp_from])
          (prod.map_fst _ _).symm (IsPullback.of_hasBinaryProduct' Y X'))
  ·
    exact
      pullback_isIsofibration g prod.snd prod.snd (prod.map (𝟙 Y) g.1)
        (IsPullback.of_bot
          (by
            convert (IsPullback.of_hasBinaryProduct' Y X').flip using 1
            · simp [prod.map_fst]
            · simp [terminal.comp_from])
          (prod.map_snd _ _).symm (IsPullback.of_hasBinaryProduct' Y Y').flip)
          -- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.


-- @@ L97-102 expanded
noncomputable def cotensorInitialIso (A : K) : cotensor.obj (⊥_ SSet.{v}) A ≅ ⊤_ K
    where
  hom := terminal.from (cotensor.obj (⊥_ SSet.{v}) A)
  inv := (cotensor.iso.underlying (⊥_ SSet.{v}) A (⊤_ K)).symm (initial.to (sHom (⊤_ K) A))
  hom_inv_id :=
    (cotensor.iso.underlying (⊥_ SSet.{v}) A (cotensor.obj (⊥_ SSet.{v}) A)).injective
      (initial.hom_ext _ _)
  inv_hom_id := terminal.hom_ext _ _


-- @@ L104-105 expanded
noncomputable def cotensorInitial_isTerminal (A : K) : IsTerminal (cotensor.obj (⊥_ SSet.{v}) A) :=
  terminalIsTerminal.ofIso (cotensorInitialIso A).symm


-- @@ L107-111 verbatim
lemma cotensorCovMapInitial_isIso {A B : K} (f : A ⟶ B) : IsIso (cotensorCovMap (⊥_ SSet.{v}) f) :=
  isIso_of_isTerminal (cotensorInitial_isTerminal A) (cotensorInitial_isTerminal B)
    (cotensorCovMap (⊥_ SSet.{v}) f)

-- TODO: replace `cotensor.iso.underlying` with something for general cotensor API.

-- @@ L112-123 expanded
noncomputable def cotensorToTerminalIso (U : SSet) {T : K} (hT : IsConicalTerminal SSet T) :
    cotensor.obj U T ≅ ⊤_ K where
  hom := terminal.from _
  inv := by
    refine (cotensor.iso.underlying U T (⊤_ K)).symm ?_
    exact (terminal.from U) ≫ (IsConicalTerminal.eHomIso SSet hT (⊤_ K)).inv
  hom_inv_id := by
    apply (cotensor.iso.underlying U T (cotensor.obj U T)).injective
    have : IsTerminal (sHom (cotensor.obj U T) T) :=
      terminalIsTerminal.ofIso (IsConicalTerminal.eHomIso SSet hT (cotensor.obj U T)).symm
    apply IsTerminal.hom_ext this
  inv_hom_id := terminal.hom_ext _ _


-- @@ L125-127 expanded
noncomputable def cotensorToConicalTerminal_isTerminal (U : SSet) {T : K}
    (hT : IsConicalTerminal SSet T) : IsTerminal (cotensor.obj U T) :=
  terminalIsTerminal.ofIso (cotensorToTerminalIso U hT).symm


-- @@ L129-132 verbatim
lemma cotensorContraMapToTerminal_isIso {U V : SSet} (i : U ⟶ V)
    {T : K} (hT : IsConicalTerminal SSet T) : IsIso (cotensorContraMap i T) :=
  isIso_of_isTerminal (cotensorToConicalTerminal_isTerminal V hT)
    (cotensorToConicalTerminal_isTerminal U hT) (cotensorContraMap i T)


-- @@ L134-140 expanded
lemma cotensorInitialSquare_isPullback (V : SSet.{v}) {A B : K} (f : Isofibration A B) :
    IsPullback (terminal.from (cotensor.obj V B) ≫ (cotensorInitialIso A).inv) (𝟙 _)
      (cotensorCovMap (⊥_ SSet.{v}) f.1) (cotensorContraMap (initial.to V) B) :=
  by
  have := cotensorCovMapInitial_isIso f.1
  refine IsPullback.of_vert_isIso ?_
  constructor
  apply IsTerminal.hom_ext (cotensorInitial_isTerminal _)


-- @@ L142-149 expanded
theorem cotensorCovMap_fibrant (V : SSet.{v}) {A B : K} (f : Isofibration A B) :
    IsIsofibration (cotensorCovMap V f.1) :=
  by
  have :=
    IsPullback.lift_snd (cotensorInitialSquare_isPullback V f) (cotensorContraMap (initial.to V) A)
      (cotensorCovMap V f.1) (cotensor_bifunctoriality (initial.to V) f.1)
  rw [← this, comp_id]
  exact
    (leibniz_cotensor_isIsofibration (initial.to V) f _ _ (cotensorInitialSquare_isPullback V f))


-- @@ L151-153 expanded
/-- An explicit isofibration obtained by cotensoring `V` with an isofibration `f`. -/
noncomputable def cotensorCovIsofibration (V : SSet.{v}) {A B : K} (f : Isofibration A B) :
    Isofibration (cotensor.obj V A) (cotensor.obj V B) :=
  ⟨cotensorCovMap V f.1, cotensorCovMap_fibrant V f⟩


-- @@ L155-157 expanded
@[simp]
lemma cotensorCovIsofibration_map (V : SSet.{v}) {A B : K} (f : Isofibration A B) :
    (cotensorCovIsofibration V f).1 = cotensorCovMap V f.1 :=
  rfl


-- @@ L159-166 expanded
lemma cotensorTerminalSquare_isPullback {U V : SSet.{v}} (i : U ⟶ V) (A : K) :
    IsPullback (𝟙 _)
      (terminal.from (cotensor.obj U A) ≫ (cotensorToTerminalIso V terminalIsConicalTerminal).inv)
      (cotensorCovMap U (terminal.from A)) (cotensorContraMap i (⊤_ K)) :=
  by
  have := cotensorContraMapToTerminal_isIso i (T := ⊤_ K) terminalIsConicalTerminal
  refine IsPullback.of_horiz_isIso ?_
  constructor
  apply IsTerminal.hom_ext (cotensorToConicalTerminal_isTerminal U terminalIsConicalTerminal)


-- @@ L168-175 verbatim
theorem cotensorContraMap_fibrant {U V : SSet} (i : U ⟶ V) [Mono i] (A : K) :
    IsIsofibration (cotensorContraMap i A) := by
  have := IsPullback.lift_fst
    (cotensorTerminalSquare_isPullback i A) (cotensorContraMap i A)
    (cotensorCovMap V (terminal.from A)) (cotensor_bifunctoriality i (terminal.from A))
  rw [← this, comp_id]
  exact (leibniz_cotensor_isIsofibration i (toTerminalIsofibration A) _ _
    (cotensorTerminalSquare_isPullback i A))


-- @@ L177-179 expanded
/-- An explicit isofibration obtained by cotensoring a monomorphism `i` with `A`. -/
noncomputable def cotensorContraIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] (A : K) :
    Isofibration (cotensor.obj V A) (cotensor.obj U A) :=
  ⟨cotensorContraMap i A, cotensorContraMap_fibrant i A⟩


-- @@ L181-183 verbatim
@[simp]
lemma cotensorContraIsofibration_map {U V : SSet.{v}} (i : U ⟶ V) [Mono i] (A : K) :
    (cotensorContraIsofibration i A).1 = cotensorContraMap i A := rfl


-- @@ L185-194 expanded
/-- An explicit choice of codomain for the Leibniz cotensor of a monomorphism and an
isofibration. -/
@[nolint unusedArguments]
noncomputable def leibnizCotensorCod {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) : K :=
  by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) :=
    by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback (cotensorCovMap U f.1) (cotensorContraMap i B)


-- @@ L196-203 expanded
/-- An explicit choice of the top map in the Leibniz pullback square. -/
noncomputable def leibnizCotensor.fst {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) : leibnizCotensorCod i f ⟶ cotensor.obj U A :=
  by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) :=
    by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.fst (cotensorCovMap U f.1) (cotensorContraMap i B)


-- @@ L205-212 expanded
/-- An explicit choice of the left map in the Leibniz pullback square. -/
noncomputable def leibnizCotensor.snd {U V : SSet} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) : leibnizCotensorCod i f ⟶ cotensor.obj V B :=
  by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) :=
    by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.snd (cotensorCovMap U f.1) (cotensorContraMap i B)


-- @@ L214-223 expanded
/-- An explicitly chosen Leibniz pullback square, as a commutative square . -/
lemma leibnizCotensor.commSq {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) :
    CommSq (leibnizCotensor.fst i f) (leibnizCotensor.snd i f) (cotensorCovMap U f.1)
      (cotensorContraMap i B) :=
  by
  constructor
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) :=
    by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.condition


-- @@ L225-235 expanded
/-- An explicitly chosen Leibniz pullback square. -/
lemma leibnizCotensor.isPullback {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) :
    IsPullback (leibnizCotensor.fst i f) (leibnizCotensor.snd i f) (cotensorCovMap U f.1)
      (cotensorContraMap i B) :=
  by
  refine ⟨leibnizCotensor.commSq i f, ?_⟩
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) :=
    by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  refine IsPullback.isLimit' ?_
  apply IsPullback.of_hasPullback


-- @@ L237-245 expanded
/-- An explicitly chosen Leibniz pullback square, as a pullback cone. -/
@[nolint unusedArguments]
noncomputable def leibnizCotensor.pullbackCone {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) : PullbackCone (cotensorCovMap U f.1) (cotensorContraMap i B) :=
  by
  have : HasPullback (cotensorCovMap U f.1) (cotensorContraMap i B) :=
    by
    have : HasConicalPullback _ (cotensorCovMap U f.1) (cotensorContraMap i B) :=
      has_isofibration_pullbacks (cotensorCovIsofibration U f) (cotensorContraMap i B)
    infer_instance
  exact pullback.cone (cotensorCovMap U f.1) (cotensorContraMap i B)


-- @@ L247-251 expanded
/-- An explicitly chosen Leibniz cotensor map of a monomorphism `i` with an isofibration `f`. -/
noncomputable def leibnizCotensorMap {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) : cotensor.obj V A ⟶ leibnizCotensorCod i f :=
  IsPullback.lift (leibnizCotensor.isPullback i f) (cotensorContraMap i A) (cotensorCovMap V f.1)
    (cotensor_bifunctoriality i f.1)


-- @@ L253-257 expanded
/-- An explicitly chosen Leibniz cotensor isofibration of a monomorphism `i` with an isofibration
`f`. -/
noncomputable def leibnizCotensorIsofibration {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) : Isofibration (cotensor.obj V A) (leibnizCotensorCod i f) :=
  ⟨leibnizCotensorMap i f, leibniz_cotensor_isIsofibration _ _ _ _ _⟩


-- @@ L259-260 expanded
lemma leibnizCotensorIsofibration_map {U V : SSet.{v}} (i : U ⟶ V) [Mono i] {A B : K}
    (f : Isofibration A B) : (leibnizCotensorIsofibration i f).1 = leibnizCotensorMap i f :=
  rfl


-- @@ L262-262 verbatim
end InfinityCosmos
