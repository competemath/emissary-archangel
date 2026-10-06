/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Iterate
import DescriptiveComplexity.FixedPoint
import DescriptiveComplexity.SecondOrderTransitiveClosure
import DescriptiveComplexity.SecondOrderTransitiveClosurePull


-- @@ L11-72 verbatim
/-!
# Simultaneous first-order inductions: one skeleton for IFP and PFP

The inflationary (FO(IFP)) and partial (FO(PFP)) fixed-point logics differ in
exactly one place – what one application of the step formulas does with the
previous stage. Everything else is shared: the data (a block of relation
variables, one first-order step formula per variable, an output sentence), the
notion of a stage, stabilization on finite structures, transport along
isomorphisms, and the pullback along a first-order interpretation. This file
provides that shared skeleton; the logics themselves are built on it in
`DescriptiveComplexity.FixedPointInflationary` and
`DescriptiveComplexity.FixedPointPartial`.

## The data

A `DescriptiveComplexity.StepDef` over `L` bundles a block `B` of relation
variables, one step *formula* per variable – a first-order formula over
`L.sum B.lang` whose free variables are the arguments of the variable – and an
output sentence over the same expanded vocabulary. This is one *simultaneous*
induction with a first-order output; nesting is treated by stratification, in
`DescriptiveComplexity.FixedPointInflationary`.

Unlike `DescriptiveComplexity.LFPDef`, whose rules are clausal *data* (the
library's Horn-program normal form), the step formulas here are unrestricted:
positivity is exactly what the inflationary and partial iterations dispense
with. `LFPDef` keeps its clausal form – the two are bridged in
`DescriptiveComplexity.FixedPointInflationary` (rules give a `StepDef`) and
`DescriptiveComplexity.FixedPointInflationaryLFP` (the converse translation).

## The two iterations

* `DescriptiveComplexity.StepDef.inflStage`: iterate
  `DescriptiveComplexity.StepDef.inflStep`, which *accumulates* the step
  formulas into the previous stage. The stages grow, so on a finite structure
  they reach a fixed point within the atom count
  (`DescriptiveComplexity.StepDef.isFixedPt_inflStep_card` – the height of the
  subset lattice, via
  `DescriptiveComplexity.exists_succ_eq_of_monotone_subset`), and their union
  `DescriptiveComplexity.StepDef.inflLimit` equals the stage at the atom count
  (`DescriptiveComplexity.StepDef.inflLimit_eq_stage_card`).
* `DescriptiveComplexity.StepDef.partStage`: iterate
  `DescriptiveComplexity.StepDef.next` itself, *replacing* the previous stage.
  Nothing grows, and the iteration may cycle forever; if some stage is a fixed
  point, all fixed stages are equal
  (`DescriptiveComplexity.StepDef.partStage_eq_of_isFixedPt`) and one is
  reached within `Nat.card` of the *assignment* type – the pigeonhole
  `DescriptiveComplexity.isFixedPt_iterate_card_iff`, exposed here as
  `DescriptiveComplexity.StepDef.exists_isFixedPt_partStage_iff`.

## Transport

Both iterations commute with transporting an assignment along an isomorphism
(`DescriptiveComplexity.StepDef.inflStage_map`,
`DescriptiveComplexity.StepDef.partStage_map`) and with the pullback of the
block through a first-order interpretation
(`DescriptiveComplexity.StepDef.inflStage_pull`,
`DescriptiveComplexity.StepDef.partStage_pull`, for the pulled definition
`DescriptiveComplexity.StepDef.pull`). Each is one commuting lemma about
`DescriptiveComplexity.StepDef.next` (`next_map`, `next_pull`) propagated along
the orbit; these are the lemmas isomorphism-invariance and closure under
reductions rest on, for every logic built on this skeleton.
-/


-- @@ L74-74 verbatim
namespace DescriptiveComplexity


-- @@ L76-76 verbatim
open FirstOrder


-- @@ L78-78 verbatim
open Language Structure


-- @@ L80-80 verbatim
open Function (IsFixedPt)


-- @@ L82-82 verbatim
variable {L : Language.{0, 0}}


-- @@ L84-84 verbatim
/-! ### Assignments form a finite type -/


-- @@ L86-89 verbatim
/-- The all-empty assignment of a block: the starting point of both
iterations. -/
def SOBlock.botAssign (B : SOBlock) (A : Type) : B.Assignment A :=
  fun _ _ => False


-- @@ L91-95 verbatim
/-- Transport along an equivalence maps the empty assignment to the empty
assignment. -/
theorem SOBlock.mapAssign_botAssign (B : SOBlock) {A A' : Type} (e : A ≃ A') :
    B.mapAssign e (B.botAssign A) = B.botAssign A' :=
  rfl


-- @@ L97-98 verbatim
instance {B : SOBlock} {A : Type} [Finite A] : Finite (B.Assignment A) :=
  inferInstanceAs (Finite (∀ i : B.ι, (Fin (B.arity i) → A) → Prop))


-- @@ L100-105 verbatim
/-! ### Realization transport with explicit structures

The structures a stage is read against are block expansions, which are not
instances; this is `FirstOrder.Language.StrongHomClass.realize_formula` with
the two structures passed explicitly, exactly as
`DescriptiveComplexity.realize_sentence_of_equiv` does at the sentence level. -/


-- @@ L107-114 verbatim
theorem realize_formula_of_equiv {L' : Language.{0, 0}} {M N : Type} {α : Type}
    {instM : L'.Structure M} {instN : L'.Structure N}
    (e : @Language.Equiv L' M N instM instN) (φ : L'.Formula α) (v : α → M) :
    @Formula.Realize L' N instN α φ (fun a => e (v a)) ↔
      @Formula.Realize L' M instM α φ v :=
  letI := instM
  letI := instN
  StrongHomClass.realize_formula φ (g := e)


-- @@ L116-116 verbatim
/-! ### The data of a simultaneous induction -/


-- @@ L118-132 verbatim
/-- A simultaneous first-order induction: a block of relation variables, one
first-order step formula per variable – over the base vocabulary expanded by
the block, its free variables the arguments of the variable – and an output
sentence over the same expanded vocabulary, read at the value of the
iteration. The step formulas are *unrestricted*; which iteration is applied to
them (inflationary or partial) is chosen by the logics built on this data. -/
structure StepDef (L : Language.{0, 0}) : Type 1 where
  /-- The relation variables computed by the iteration. -/
  B : SOBlock
  /-- The step formula of each variable; its free variables are the arguments
  of the variable. -/
  step : ∀ i : B.ι, (L.sum B.lang).Formula (Fin (B.arity i))
  /-- The first-order output, over the expanded vocabulary – unrestricted, in
  particular free to negate fixed-point atoms. -/
  out : (L.sum B.lang).Sentence


-- @@ L134-134 verbatim
namespace StepDef


-- @@ L136-136 verbatim
variable (d : StepDef L)


-- @@ L138-138 verbatim
section Semantics


-- @@ L140-140 verbatim
variable {A : Type} [L.Structure A]


-- @@ L142-144 verbatim
/-- One application of the step formulas to an assignment. -/
def next (ρ : d.B.Assignment A) : d.B.Assignment A :=
  fun i x => @Formula.Realize _ A (d.B.structure₁ (L := L) ρ) _ (d.step i) x


-- @@ L146-149 verbatim
/-- The inflationary step: accumulate the step formulas into the previous
stage. -/
def inflStep (ρ : d.B.Assignment A) : d.B.Assignment A :=
  fun i x => ρ i x ∨ d.next ρ i x


-- @@ L151-154 verbatim
variable (A) in
/-- The stages of the inflationary iteration. -/
def inflStage (n : ℕ) : d.B.Assignment A :=
  (d.inflStep)^[n] (d.B.botAssign A)


-- @@ L156-159 verbatim
variable (A) in
/-- The stages of the partial iteration. -/
def partStage (n : ℕ) : d.B.Assignment A :=
  (d.next)^[n] (d.B.botAssign A)


-- @@ L161-166 verbatim
variable (A) in
/-- The value of the inflationary iteration: the union of the stages. On a
finite structure this is the stage at the atom count
(`DescriptiveComplexity.StepDef.inflLimit_eq_stage_card`). -/
def inflLimit : d.B.Assignment A :=
  fun i x => ∃ n, d.inflStage A n i x


-- @@ L168-170 verbatim
theorem inflStage_succ (n : ℕ) :
    d.inflStage A (n + 1) = d.inflStep (d.inflStage A n) :=
  Function.iterate_succ_apply' d.inflStep n (d.B.botAssign A)


-- @@ L172-174 verbatim
theorem partStage_succ (n : ℕ) :
    d.partStage A (n + 1) = d.next (d.partStage A n) :=
  Function.iterate_succ_apply' d.next n (d.B.botAssign A)


-- @@ L176-180 verbatim
/-- The inflationary stages increase. -/
theorem inflStage_le_succ (n : ℕ) (i : d.B.ι) (x : Fin (d.B.arity i) → A)
    (h : d.inflStage A n i x) : d.inflStage A (n + 1) i x := by
  rw [d.inflStage_succ]
  exact Or.inl h


-- @@ L182-190 verbatim
/-- The inflationary stages increase, monotonically. -/
theorem inflStage_le_of_le {m n : ℕ} (hmn : m ≤ n) (i : d.B.ι)
    (x : Fin (d.B.arity i) → A) (h : d.inflStage A m i x) : d.inflStage A n i x := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact d.inflStage_le_succ n i x (ih (Nat.lt_succ_iff.mp hlt))
    · rwa [heq] at h


-- @@ L192-199 verbatim
/-- Two partial stages that are both fixed points of the step are equal: the
value of a converging partial iteration does not depend on which stable stage
witnesses the convergence. -/
theorem partStage_eq_of_isFixedPt {m n : ℕ} (hm : IsFixedPt d.next (d.partStage A m))
    (hn : IsFixedPt d.next (d.partStage A n)) : d.partStage A m = d.partStage A n := by
  rcases le_total m n with h | h
  · exact (iterate_eq_of_isFixedPt hm h).symm
  · exact iterate_eq_of_isFixedPt hn h


-- @@ L201-201 verbatim
end Semantics


-- @@ L203-203 verbatim
/-! ### Stabilization on finite structures -/


-- @@ L205-205 verbatim
section Stab


-- @@ L207-207 verbatim
variable {A : Type} [L.Structure A] [Finite A]


-- @@ L209-219 verbatim
variable (A) in
/-- The inflationary stages plateau within the atom count. -/
theorem exists_inflStage_succ_eq :
    ∃ N ≤ Nat.card (BAtom d.B A), d.inflStage A (N + 1) = d.inflStage A N := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_monotone_subset
    (c := fun n => {q : BAtom d.B A | d.inflStage A n q.1 q.2})
    (fun n q hq => d.inflStage_le_succ n q.1 q.2 hq)
  refine ⟨N, hN, ?_⟩
  funext i x
  exact propext ⟨fun h => (Set.ext_iff.mp heq ⟨i, x⟩).mp h,
    fun h => (Set.ext_iff.mp heq ⟨i, x⟩).mpr h⟩


-- @@ L221-233 verbatim
variable (A) in
/-- **The inflationary iteration reaches a fixed point within the atom
count** – the height of the subset lattice of the block's atoms, not the
number of assignments. -/
theorem isFixedPt_inflStep_card :
    IsFixedPt d.inflStep (d.inflStage A (Nat.card (BAtom d.B A))) := by
  obtain ⟨N, hN, heq⟩ := d.exists_inflStage_succ_eq A
  have hfix : IsFixedPt d.inflStep (d.inflStage A N) :=
    (Function.iterate_succ_apply' d.inflStep N (d.B.botAssign A)).symm.trans heq
  have hc : d.inflStage A (Nat.card (BAtom d.B A)) = d.inflStage A N :=
    iterate_eq_of_isFixedPt hfix hN
  rw [hc]
  exact hfix


-- @@ L235-238 verbatim
/-- The inflationary stages are constant from the atom count on. -/
theorem inflStage_eq_of_card_le {n : ℕ} (hn : Nat.card (BAtom d.B A) ≤ n) :
    d.inflStage A n = d.inflStage A (Nat.card (BAtom d.B A)) :=
  iterate_eq_of_isFixedPt (d.isFixedPt_inflStep_card A) hn


-- @@ L240-251 verbatim
variable (A) in
/-- On a finite structure, the value of the inflationary iteration is the
stage at the atom count. -/
theorem inflLimit_eq_stage_card :
    d.inflLimit A = d.inflStage A (Nat.card (BAtom d.B A)) := by
  funext i x
  refine propext ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨n, hn⟩
  rcases le_or_gt n (Nat.card (BAtom d.B A)) with hle | hlt
  · exact d.inflStage_le_of_le hle i x hn
  · rw [← d.inflStage_eq_of_card_le hlt.le]
    exact hn


-- @@ L253-258 verbatim
variable (A) in
/-- The value of the inflationary iteration is a fixed point of the
inflationary step. -/
theorem isFixedPt_inflStep_inflLimit : IsFixedPt d.inflStep (d.inflLimit A) := by
  rw [d.inflLimit_eq_stage_card A]
  exact d.isFixedPt_inflStep_card A


-- @@ L260-267 verbatim
variable (A) in
/-- **If the partial iteration converges at all, it converges within the
number of assignments of the block** – the pigeonhole
`DescriptiveComplexity.isFixedPt_iterate_card_iff` read on the stages. -/
theorem exists_isFixedPt_partStage_iff :
    (∃ n, IsFixedPt d.next (d.partStage A n)) ↔
      IsFixedPt d.next (d.partStage A (Nat.card (d.B.Assignment A))) :=
  (isFixedPt_iterate_card_iff d.next (d.B.botAssign A)).symm


-- @@ L269-269 verbatim
end Stab


-- @@ L271-271 verbatim
/-! ### Transport along isomorphisms -/


-- @@ L273-273 verbatim
section Map


-- @@ L275-275 verbatim
variable {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N)


-- @@ L277-287 verbatim
/-- One application of the step formulas commutes with transporting the
assignment along an isomorphism: the step formulas cannot tell isomorphic
expanded structures apart. -/
theorem next_map (ρ : d.B.Assignment M) :
    d.next (d.B.mapAssign e.toEquiv ρ) = d.B.mapAssign e.toEquiv (d.next ρ) := by
  funext i x
  refine propext ?_
  have h := realize_formula_of_equiv (d.B.extendEquiv' (L' := L) e ρ) (d.step i)
    (fun j => e.toEquiv.symm (x j))
  refine Iff.trans (iff_of_eq (congrArg _ ?_)) h
  exact funext fun j => (e.toEquiv.apply_symm_apply (x j)).symm


-- @@ L289-294 verbatim
/-- The inflationary step commutes with transport along an isomorphism. -/
theorem inflStep_map (ρ : d.B.Assignment M) :
    d.inflStep (d.B.mapAssign e.toEquiv ρ) = d.B.mapAssign e.toEquiv (d.inflStep ρ) := by
  funext i x
  have h := congrFun (congrFun (d.next_map e ρ) i) x
  exact congrArg (fun p => d.B.mapAssign e.toEquiv ρ i x ∨ p) h


-- @@ L296-301 verbatim
/-- The inflationary stages transport along an isomorphism. -/
theorem inflStage_map (n : ℕ) :
    d.inflStage N n = d.B.mapAssign e.toEquiv (d.inflStage M n) := by
  induction n with
  | zero => exact (d.B.mapAssign_botAssign e.toEquiv).symm
  | succ n ih => rw [d.inflStage_succ, d.inflStage_succ, ih, d.inflStep_map]


-- @@ L303-308 verbatim
/-- The partial stages transport along an isomorphism. -/
theorem partStage_map (n : ℕ) :
    d.partStage N n = d.B.mapAssign e.toEquiv (d.partStage M n) := by
  induction n with
  | zero => exact (d.B.mapAssign_botAssign e.toEquiv).symm
  | succ n ih => rw [d.partStage_succ, d.partStage_succ, ih, d.next_map]


-- @@ L310-317 verbatim
/-- The value of the inflationary iteration transports along an
isomorphism. -/
theorem inflLimit_map : d.inflLimit N = d.B.mapAssign e.toEquiv (d.inflLimit M) := by
  funext i x
  refine propext ?_
  change (∃ n, d.inflStage N n i x) ↔ ∃ n, d.inflStage M n i fun j => e.toEquiv.symm (x j)
  refine exists_congr fun n => iff_of_eq ?_
  exact congrFun (congrFun (d.inflStage_map e n) i) x


-- @@ L319-326 verbatim
/-- Being a fixed point of the step is insensitive to transporting the
assignment along an isomorphism. -/
theorem isFixedPt_next_map_iff (ρ : d.B.Assignment M) :
    IsFixedPt d.next (d.B.mapAssign e.toEquiv ρ) ↔ IsFixedPt d.next ρ := by
  have hinj : Function.Injective (d.B.mapAssign (A := M) (A' := N) e.toEquiv) :=
    (d.B.assignEquiv e.toEquiv).injective
  exact ⟨fun h => hinj ((d.next_map e ρ).symm.trans h),
    fun h => (d.next_map e ρ).trans (congrArg _ h)⟩


-- @@ L328-328 verbatim
end Map


-- @@ L330-330 verbatim
end StepDef


-- @@ L332-332 verbatim
/-! ### Pullback through an interpretation -/


-- @@ L334-338 verbatim
/-- Pulling back the empty assignment gives the empty assignment. -/
theorem SOBlock.pullAssign_botAssign (B : SOBlock) {Tag : Type} [Finite Tag]
    {dm : ℕ} {A : Type} :
    B.pullAssign (B.botAssign (Tag × (Fin dm → A))) = (B.pull Tag dm).botAssign A :=
  rfl


-- @@ L340-340 verbatim
namespace StepDef


-- @@ L342-342 verbatim
section Pull


-- @@ L344-344 verbatim
variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dm : ℕ}


-- @@ L346-357 verbatim
/-- The pullback of a simultaneous induction through a tagged interpretation:
the block is pulled back variable by variable
(`DescriptiveComplexity.SOBlock.pull`), the step formula of a pulled variable
is the pullback of the original variable's step formula at the pulled
variable's tag tuple (`DescriptiveComplexity.guardPull`, through the extended
interpretation `DescriptiveComplexity.FOInterpretation.extendSO`), and the
output sentence is pulled through the extended interpretation. -/
noncomputable def pull (dd : StepDef L₂) (I : FOInterpretation L₁ L₂ Tag dm) :
    StepDef L₁ where
  B := dd.B.pull Tag dm
  step := fun p => guardPull (I.extendSO dd.B) (dd.step p.1) p.2
  out := (I.extendSO dd.B).pullSentence dd.out


-- @@ L359-359 verbatim
variable (I : FOInterpretation L₁ L₂ Tag dm) (dd : StepDef L₂)

-- @@ L360-360 verbatim
variable {A : Type} [L₁.Structure A]


-- @@ L362-373 verbatim
/-- **One application of the pulled step formulas is the pullback of one
application of the original ones**: the single commuting square from which
every transport of the iterations along a reduction follows. -/
theorem next_pull (ρ : dd.B.Assignment (I.Map A)) :
    (dd.pull I).next (dd.B.pullAssign ρ) = dd.B.pullAssign (dd.next (A := I.Map A) ρ) := by
  funext p x
  refine propext ?_
  let := (dd.B.pull Tag dm).structure₁ (L := L₁) (dd.B.pullAssign ρ)
  have h1 := realize_guardPull (I.extendSO dd.B) (dd.step p.1) p.2 x
  have h2 := realize_formula_of_equiv (I.extendSOEquiv dd.B A ρ) (dd.step p.1)
    (tagVal (I.extendSO dd.B) p.2 x)
  exact h1.trans h2.symm


-- @@ L375-380 verbatim
/-- The inflationary step commutes with the pullback. -/
theorem inflStep_pull (ρ : dd.B.Assignment (I.Map A)) :
    (dd.pull I).inflStep (dd.B.pullAssign ρ) = dd.B.pullAssign (dd.inflStep (A := I.Map A) ρ) := by
  funext p x
  have h := congrFun (congrFun (next_pull I dd ρ) p) x
  exact congrArg (fun t => dd.B.pullAssign ρ p x ∨ t) h


-- @@ L382-390 verbatim
variable (A) in
/-- The inflationary stages of the pulled induction are the pullbacks of the
original stages. -/
theorem inflStage_pull (n : ℕ) :
    (dd.pull I).inflStage A n = dd.B.pullAssign (dd.inflStage (I.Map A) n) := by
  induction n with
  | zero => exact (dd.B.pullAssign_botAssign).symm
  | succ n ih =>
    rw [(dd.pull I).inflStage_succ, dd.inflStage_succ, ih, inflStep_pull]


-- @@ L392-400 verbatim
variable (A) in
/-- The partial stages of the pulled induction are the pullbacks of the
original stages. -/
theorem partStage_pull (n : ℕ) :
    (dd.pull I).partStage A n = dd.B.pullAssign (dd.partStage (I.Map A) n) := by
  induction n with
  | zero => exact (dd.B.pullAssign_botAssign).symm
  | succ n ih =>
    rw [(dd.pull I).partStage_succ, dd.partStage_succ, ih, next_pull]


-- @@ L402-411 verbatim
variable (A) in
/-- The value of the pulled inflationary iteration is the pullback of the
original value. -/
theorem inflLimit_pull :
    (dd.pull I).inflLimit A = dd.B.pullAssign (dd.inflLimit (I.Map A)) := by
  funext p x
  refine propext ?_
  change (∃ n, (dd.pull I).inflStage A n p x) ↔ ∃ n, dd.inflStage (I.Map A) n p.1 _
  refine exists_congr fun n => iff_of_eq ?_
  exact congrFun (congrFun (inflStage_pull I dd A n) p) x


-- @@ L413-424 verbatim
/-- Being a fixed point of the step is insensitive to pulling the assignment
back: the pullback of assignments is a bijection
(`DescriptiveComplexity.SOBlock.mergeAssign_pullAssign`) intertwining the two
steps. -/
theorem isFixedPt_next_pull_iff (ρ : dd.B.Assignment (I.Map A)) :
    IsFixedPt (dd.pull I).next (dd.B.pullAssign ρ) ↔ IsFixedPt dd.next ρ := by
  have hinj : Function.Injective
      (dd.B.pullAssign (Tag := Tag) (d := dm) (A := A)) :=
    Function.LeftInverse.injective (g := dd.B.mergeAssign)
      fun σ => dd.B.mergeAssign_pullAssign σ
  exact ⟨fun h => hinj ((next_pull I dd ρ).symm.trans h),
    fun h => (next_pull I dd ρ).trans (congrArg _ h)⟩


-- @@ L426-426 verbatim
end Pull


-- @@ L428-428 verbatim
end StepDef


-- @@ L430-430 verbatim
end DescriptiveComplexity
