/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import Mathlib.Topology.Instances.AddCircle.Real


-- @@ L10-17 verbatim
/-!
# Coefficient-parametric transfinite character extension

This module contains the recursion shared by the integer and rational Wallace constructions.
The coefficient-specific input is an additive character on one coordinate whose value at one is
a prescribed circle element. The integer specialization uses scalar multiplication; the rational
specialization obtains the character from Baer's extension theorem.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open Filter Set Topology


-- @@ L23-23 verbatim
namespace Wallace

-- @@ L24-24 verbatim
namespace CoefficientTransfiniteExtension


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
universe u v w


-- @@ L30-34 verbatim
/-- A way to extend a prescribed circle value to a character on one coefficient coordinate. -/
structure CoordinateExtension (R : Type w) [AddCommMonoid R] [One R] where
  /-- Build a coordinate character with the prescribed value at one. -/
  ofValue : UnitAddCircle → (R →+ UnitAddCircle)
  ofValue_one : ∀ t, ofValue t 1 = t


-- @@ L36-46 verbatim
/-- The triangular data needed by the coefficient-parametric recursion. -/
structure Data (R : Type w) (I : Type u) [Zero R] [LT I] where
  /-- Codes for the prepared sequences. -/
  Code : Type v
  /-- The fresh coordinate assigned to a code. -/
  codeIndex : Code ↪ I
  /-- The sequence after finite block preprocessing. -/
  prepared : Code → ℕ → I →₀ R
  support_lt : ∀ c n i, i ∈ (prepared c n).support → i < codeIndex c
  /-- The ultrafilter along which the coded limit is imposed. -/
  p : Code → Ultrafilter ℕ


-- @@ L48-51 verbatim
/-- Closure under the prepared supports attached to code coordinates in `D`. -/
def ClosedUnderPreparedSupports {R : Type w} {I : Type u} [Zero R] [LT I]
    (E : Data R I) (D : Set I) : Prop :=
  ∀ c, E.codeIndex c ∈ D → ∀ n i, i ∈ (E.prepared c n).support → i ∈ D


-- @@ L53-58 verbatim
/-- The local character already realizes each limit whose code coordinate lies in `D`. -/
def LocallyAdmissible {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LT I]
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle) : Prop :=
  ∀ (c : E.Code) (hc : E.codeIndex c ∈ D),
    Tendsto (fun n ↦ character (Finsupp.subtypeDomain D (E.prepared c n))) (E.p c)
      (nhds (character (Finsupp.single ⟨E.codeIndex c, hc⟩ 1)))


-- @@ L60-63 verbatim
/-- The character on a direct sum induced by its coordinate characters. -/
def finsuppAddHom {R : Type w} {I : Type u} [AddCommMonoid R]
    (coordinates : I → (R →+ UnitAddCircle)) : (I →₀ R) →+ UnitAddCircle :=
  Finsupp.liftAddHom coordinates


-- @@ L65-69 verbatim
@[simp]
private theorem finsuppAddHom_single {R : Type w} {I : Type u} [AddCommMonoid R]
    (coordinates : I → (R →+ UnitAddCircle)) (i : I) (r : R) :
    finsuppAddHom coordinates (Finsupp.single i r) = coordinates i r := by
  simp [finsuppAddHom]


-- @@ L71-75 verbatim
/-- Totalize the coordinate characters available below a recursive stage. -/
def stageCoordinates {R : Type w} {I : Type u} [AddCommMonoid R] [LT I]
    [DecidableRel ((· < ·) : I → I → Prop)] (i : I)
    (previous : ∀ j, j < i → (R →+ UnitAddCircle)) : I → (R →+ UnitAddCircle) :=
  fun j ↦ if h : j < i then previous j h else 0


-- @@ L77-82 verbatim
/-- Evaluate a prepared term using only coordinates below the current stage. -/
def stageEvaluation {R : Type w} {I : Type u} [AddCommMonoid R] [LT I]
    [DecidableRel ((· < ·) : I → I → Prop)] (E : Data R I) (i : I)
    (previous : ∀ j, j < i → (R →+ UnitAddCircle))
    (c : E.Code) (n : ℕ) : UnitAddCircle :=
  finsuppAddHom (stageCoordinates i previous) (E.prepared c n)


-- @@ L84-89 verbatim
/-- The compact ultrafilter limit selected at a code coordinate. -/
def compactStageLimit {R : Type w} {I : Type u} [AddCommMonoid R] [LT I]
    [DecidableRel ((· < ·) : I → I → Prop)] (E : Data R I) (i : I)
    (previous : ∀ j, j < i → (R →+ UnitAddCircle))
    (c : E.Code) : UnitAddCircle :=
  (Ultrafilter.map (stageEvaluation E i previous c) (E.p c)).lim


-- @@ L91-99 verbatim
private theorem finsuppAddHom_eq_of_eq_on_support
    {R : Type w} {I : Type u} [AddCommMonoid R]
    {left right : I → (R →+ UnitAddCircle)} {x : I →₀ R}
    (h : ∀ i ∈ x.support, left i = right i) :
    finsuppAddHom left x = finsuppAddHom right x := by
  simp only [finsuppAddHom, Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro i hi
  rw [h i hi]


-- @@ L101-113 verbatim
/-- One step of the well-founded coordinate recursion. -/
def coordinateStep
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LinearOrder I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle) (i : I)
    (previous : ∀ j, j < i → (R →+ UnitAddCircle)) : R →+ UnitAddCircle := by
  classical
  exact if hi : i ∈ D then
      character.comp (Finsupp.singleAddHom ⟨i, hi⟩)
    else if hcode : ∃ c : E.Code, E.codeIndex c = i then
      extension.ofValue (compactStageLimit E i previous (Classical.choose hcode))
    else
      0


-- @@ L115-120 verbatim
/-- The coordinate characters constructed by well-founded recursion. -/
def globalCoordinate {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle) :
    I → (R →+ UnitAddCircle) :=
  WellFoundedLT.fix fun i previous ↦ coordinateStep extension E D character i previous


-- @@ L122-128 verbatim
private theorem globalCoordinate_eq {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle) (i : I) :
    globalCoordinate extension E D character i =
      coordinateStep extension E D character i
        (fun j _ ↦ globalCoordinate extension E D character j) := by
  rw [globalCoordinate, WellFoundedLT.fix_eq]


-- @@ L130-138 verbatim
private theorem globalCoordinate_of_mem
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle)
    {i : I} (hi : i ∈ D) :
    globalCoordinate extension E D character i =
      character.comp (Finsupp.singleAddHom ⟨i, hi⟩) := by
  rw [globalCoordinate_eq]
  simp [coordinateStep, hi]


-- @@ L140-156 verbatim
private theorem globalCoordinate_codeIndex_of_not_mem
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle)
    (c : E.Code) (hc : E.codeIndex c ∉ D) :
    globalCoordinate extension E D character (E.codeIndex c) =
      extension.ofValue
        (compactStageLimit E (E.codeIndex c)
          (fun j _ ↦ globalCoordinate extension E D character j) c) := by
  rw [globalCoordinate_eq]
  simp only [coordinateStep, hc, dite_false]
  let hex : ∃ d : E.Code, E.codeIndex d = E.codeIndex c := ⟨c, rfl⟩
  rw [dite_eq_left hex]
  have hchosen : Classical.choose hex = c := by
    apply E.codeIndex.injective
    exact Classical.choose_spec hex
  rw [hchosen]


-- @@ L158-163 verbatim
/-- The global character assembled from the recursively constructed coordinates. -/
def globalCharacter {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle) :
    (I →₀ R) →+ UnitAddCircle :=
  finsuppAddHom (globalCoordinate extension E D character)


-- @@ L165-172 verbatim
@[simp]
private theorem globalCharacter_single {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle)
    (i : I) (r : R) :
    globalCharacter extension E D character (Finsupp.single i r) =
      globalCoordinate extension E D character i r := by
  simp [globalCharacter]


-- @@ L174-193 verbatim
private theorem globalCharacter_extendDomain {R : Type w} {I : Type u}
    [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle) (x : D →₀ R) :
    globalCharacter extension E D character (Finsupp.embDomain (.subtype D) x) = character x := by
  let inclusion : (D →₀ R) →+ (I →₀ R) :=
    Finsupp.embDomain.addMonoidHom (.subtype (D : I → Prop))
  have hhom : (globalCharacter extension E D character).comp inclusion = character := by
    apply Finsupp.addHom_ext
    intro i r
    rcases i with ⟨i, hi⟩
    change globalCharacter extension E D character
      (Finsupp.embDomain (.subtype (D : I → Prop)) (Finsupp.single ⟨i, hi⟩ r)) =
        character (Finsupp.single ⟨i, hi⟩ r)
    rw [Finsupp.embDomain_single, globalCharacter_single]
    have hcoordinate := globalCoordinate_of_mem extension E D character (i := i) hi
    have happly := DFunLike.congr_fun hcoordinate r
    change globalCoordinate extension E D character i r = character (Finsupp.single ⟨i, hi⟩ r)
    simpa only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply] using happly
  exact DFunLike.congr_fun hhom x


-- @@ L195-209 verbatim
theorem globalCharacter_eq_local_restriction {R : Type w} {I : Type u}
    [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle)
    (x : I →₀ R) (hx : ∀ i ∈ x.support, i ∈ D) :
    globalCharacter extension E D character x = character (Finsupp.subtypeDomain D x) := by
  have hxrange : (↑x.support : Set I) ⊆ Set.range (Function.Embedding.subtype D) := by
    intro i hi
    exact ⟨⟨i, hx i hi⟩, rfl⟩
  obtain ⟨y, rfl⟩ :=
    (Finsupp.mem_range_embDomain_iff (Function.Embedding.subtype D) x).2 hxrange
  rw [globalCharacter_extendDomain extension E D character y]
  congr 1
  ext i
  exact (Finsupp.embDomain_apply_self (Function.Embedding.subtype D) y i).symm


-- @@ L211-220 verbatim
private theorem stageEvaluation_eq_globalCharacter
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle) (c : E.Code) (n : ℕ) :
    stageEvaluation E (E.codeIndex c)
        (fun j _ ↦ globalCoordinate extension E D character j) c n =
      globalCharacter extension E D character (E.prepared c n) := by
  apply finsuppAddHom_eq_of_eq_on_support
  intro i hi
  simp [stageCoordinates, E.support_lt c n i hi]


-- @@ L222-228 verbatim
private theorem tendsto_stageEvaluation_compactLimit
    {R : Type w} {I : Type u} [AddCommMonoid R] [LinearOrder I]
    (E : Data R I) (i : I) (previous : ∀ j, j < i → (R →+ UnitAddCircle))
    (c : E.Code) :
    Tendsto (stageEvaluation E i previous c) (E.p c)
      (nhds (compactStageLimit E i previous c)) := by
  exact (Ultrafilter.map (stageEvaluation E i previous c) (E.p c)).le_nhds_lim


-- @@ L230-266 verbatim
/-- The transfinite extension realizes every prescribed ultrafilter limit. -/
theorem globalCharacter_admissible
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle)
    (hclosed : ClosedUnderPreparedSupports E D)
    (hlocal : LocallyAdmissible E D character) :
    ∀ c : E.Code,
      Tendsto (fun n ↦ globalCharacter extension E D character (E.prepared c n)) (E.p c)
        (nhds (globalCharacter extension E D character (Finsupp.single (E.codeIndex c) 1))) := by
  intro c
  by_cases hc : E.codeIndex c ∈ D
  · have heval :
        (fun n ↦ globalCharacter extension E D character (E.prepared c n)) =
          (fun n ↦ character (Finsupp.subtypeDomain D (E.prepared c n))) := by
      funext n
      exact globalCharacter_eq_local_restriction extension E D character (E.prepared c n)
        (hclosed c hc n)
    have hbasis :
        globalCharacter extension E D character (Finsupp.single (E.codeIndex c) 1) =
          character (Finsupp.single ⟨E.codeIndex c, hc⟩ 1) := by
      rw [globalCharacter_single, globalCoordinate_of_mem extension E D character hc]
      rfl
    rw [heval, hbasis]
    exact hlocal c hc
  · have hlim := tendsto_stageEvaluation_compactLimit E (E.codeIndex c)
        (fun j _ ↦ globalCoordinate extension E D character j) c
    have heval :
        (fun n ↦ globalCharacter extension E D character (E.prepared c n)) =
          stageEvaluation E (E.codeIndex c)
            (fun j _ ↦ globalCoordinate extension E D character j) c := by
      funext n
      exact (stageEvaluation_eq_globalCharacter extension E D character c n).symm
    rw [heval, globalCharacter_single,
      globalCoordinate_codeIndex_of_not_mem extension E D character c hc,
      extension.ofValue_one]
    exact hlim


-- @@ L268-268 verbatim
end

-- @@ L269-269 verbatim
end CoefficientTransfiniteExtension

-- @@ L270-270 verbatim
end Wallace
