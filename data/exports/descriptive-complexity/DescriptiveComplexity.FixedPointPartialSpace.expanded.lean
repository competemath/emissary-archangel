/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointPartial
import DescriptiveComplexity.PSpace


-- @@ L9-49 verbatim
/-!
# FO(≤, PFP) is contained in SO(TC)

The easy half of the capture theorem FO(≤, PFP) = PSPACE ([Abiteboul–Vianu
1989][abiteboul1989fixpoint]; [Ebbinghaus–Flum 1995][ebbinghaus1995finite],
ch. 7): a partial fixed-point iteration *is* a deterministic walk on the
state space SO(TC) walks on – the assignments of the block – so a
`DescriptiveComplexity.StepDef` read partially translates into a
`DescriptiveComplexity.SOTCSpec` verbatim
(`DescriptiveComplexity.StepDef.toSOTCSpec`):

* the walk's states are the assignments of the same block;
* its transition sentence says «the second copy is one application of the
  step formulas to the first» (`DescriptiveComplexity.StepDef.nextSentence`);
* its source is the empty assignment
  (`DescriptiveComplexity.StepDef.botSentence`);
* its target says «the state is a fixed point of the step, and the output
  holds» (`DescriptiveComplexity.StepDef.isFixedPtF`, conjoined with the
  output).

The states reachable from the source along the deterministic transition are
exactly the partial stages, so acceptance is
`DescriptiveComplexity.StepDef.PFPHolds`
(`DescriptiveComplexity.StepDef.accepts_toSOTCSpec`) – with **no divergence
detection**: under the convergence-requiring semantics of
`DescriptiveComplexity.FixedPointPartial`, a diverging iteration simply
reaches no target state. This is what the divergence convention buys; the
textbook convention would need a step counter to make divergence positively
detectable, and a counter is the one thing this translation would otherwise
need the order for.

Whence FO(≤, PFP) ⊆ PSPACE: `DescriptiveComplexity.PFPDefinable.sotcDefinable`
and `DescriptiveComplexity.mem_PSPACE_of_pfpDefinable`. The converse
inclusion – PSPACE ⊆ FO(≤, PFP), completing the capture – iterates the
PSPACE-complete deterministic machine problem and is built in
`DescriptiveComplexity.FixedPointPartialMachine`.

`DescriptiveComplexity.StepDef.isFixedPtF` is also the guard that reads a
definition of this library in the textbook divergence convention – see the
divergence discussion in `DescriptiveComplexity.FixedPointPartial`.
-/


-- @@ L51-51 verbatim
namespace DescriptiveComplexity


-- @@ L53-53 verbatim
open FirstOrder


-- @@ L55-55 verbatim
open Language Structure


-- @@ L57-57 verbatim
open Function (IsFixedPt)


-- @@ L59-59 verbatim
variable {L : Language.{0, 0}}


-- @@ L61-61 verbatim
/-! ### Enumerating the variables of a block -/


-- @@ L63-68 verbatim
open Classical in
/-- The relation variables of a block, as a list: the sentences below conjoin
one clause per variable. -/
noncomputable def SOBlock.idxList (B : SOBlock) : List B.ι :=
  letI : Fintype B.ι := Fintype.ofFinite B.ι
  (Finset.univ : Finset B.ι).toList


-- @@ L70-73 verbatim
open Classical in
theorem SOBlock.mem_idxList (B : SOBlock) (i : B.ι) : i ∈ B.idxList := by
  let : Fintype B.ι := Fintype.ofFinite B.ι
  exact Finset.mem_toList.mpr (Finset.mem_univ i)


-- @@ L75-75 verbatim
namespace StepDef


-- @@ L77-77 verbatim
variable (d : StepDef L)


-- @@ L79-79 verbatim
/-! ### The three sentences of the walk -/


-- @@ L81-85 verbatim
/-- The atom of a block variable in the *second* copy of the block, over two
copies. -/
abbrev newVarSym (L : Language.{0, 0}) (B : SOBlock) (i : B.ι) :
    ((L.sum B.lang).sum B.lang).Relations (B.arity i) :=
  Sum.inr (varSym B i)


-- @@ L87-94 verbatim
/-- «The second copy of the block is one application of the step formulas to
the first»: the transition sentence of the walk. -/
noncomputable def nextSentence : ((L.sum d.B.lang).sum d.B.lang).Sentence :=
  listInf (d.B.idxList.map fun i =>
    Formula.iAlls (Fin (d.B.arity i))
      (((Relations.formula (newVarSym L d.B i) fun j => Term.var (Sum.inr j)).iff
          ((LHom.sumInl.onFormula (d.step i)).relabel Sum.inr) :
        ((L.sum d.B.lang).sum d.B.lang).Formula (Empty ⊕ Fin (d.B.arity i)))))


-- @@ L96-102 verbatim
/-- «Every relation of the block is empty»: the source sentence of the
walk. -/
noncomputable def botSentence : (L.sum d.B.lang).Sentence :=
  listInf (d.B.idxList.map fun i =>
    Formula.iAlls (Fin (d.B.arity i))
      ((∼(Relations.formula (varInSym L d.B i) fun j => Term.var (Sum.inr j)) :
        (L.sum d.B.lang).Formula (Empty ⊕ Fin (d.B.arity i)))))


-- @@ L104-112 verbatim
/-- «The state is a fixed point of the step formulas», as a sentence over one
copy of the block. Also the guard that transfers a definition between the two
divergence conventions – see `DescriptiveComplexity.FixedPointPartial`. -/
noncomputable def isFixedPtF : (L.sum d.B.lang).Sentence :=
  listInf (d.B.idxList.map fun i =>
    Formula.iAlls (Fin (d.B.arity i))
      (((Relations.formula (varInSym L d.B i) fun j => Term.var (Sum.inr j)).iff
          ((d.step i).relabel Sum.inr) :
        (L.sum d.B.lang).Formula (Empty ⊕ Fin (d.B.arity i)))))


-- @@ L114-114 verbatim
/-! ### Their semantics -/


-- @@ L116-116 verbatim
section Realize


-- @@ L118-118 verbatim
variable {A : Type} [L.Structure A]


-- @@ L120-142 verbatim
theorem realize_nextSentence (ρ σ : d.B.Assignment A) :
    (@Sentence.Realize _ A (d.B.structure₂ (L := L) ρ σ) d.nextSentence) ↔
      σ = d.next ρ := by
  let := d.B.structure σ
  let := d.B.structure₁ (L := L) ρ
  rw [nextSentence]
  simp only [Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i x
    have hi := h _ (List.mem_map_of_mem (d.B.mem_idxList i))
    rw [Formula.realize_iAlls] at hi
    have hx := hi x
    rw [Formula.realize_iff, Formula.realize_rel, Formula.realize_relabel,
      LHom.realize_onFormula] at hx
    exact propext hx
  · rintro rfl ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_iAlls]
    intro x
    rw [Formula.realize_iff, Formula.realize_rel, Formula.realize_relabel,
      LHom.realize_onFormula]
    exact Iff.rfl


-- @@ L144-163 verbatim
theorem realize_botSentence (ρ : d.B.Assignment A) :
    (@Sentence.Realize _ A (d.B.structure₁ (L := L) ρ) d.botSentence) ↔
      ρ = d.B.botAssign A := by
  let := d.B.structure ρ
  rw [botSentence]
  simp only [Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i x
    have hi := h _ (List.mem_map_of_mem (d.B.mem_idxList i))
    rw [Formula.realize_iAlls] at hi
    have hx := hi x
    rw [Formula.realize_not, Formula.realize_rel] at hx
    exact propext (iff_false_intro hx)
  · rintro rfl ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_iAlls]
    intro x
    rw [Formula.realize_not, Formula.realize_rel]
    exact fun h => h


-- @@ L165-184 verbatim
theorem realize_isFixedPtF (ρ : d.B.Assignment A) :
    (@Sentence.Realize _ A (d.B.structure₁ (L := L) ρ) d.isFixedPtF) ↔
      IsFixedPt d.next ρ := by
  let := d.B.structure ρ
  rw [isFixedPtF]
  simp only [Sentence.Realize, realize_listInf]
  constructor
  · intro h
    funext i x
    have hi := h _ (List.mem_map_of_mem (d.B.mem_idxList i))
    rw [Formula.realize_iAlls] at hi
    have hx := hi x
    rw [Formula.realize_iff, Formula.realize_rel, Formula.realize_relabel] at hx
    exact propext hx.symm
  · rintro hfix ψ hψ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hψ
    rw [Formula.realize_iAlls]
    intro x
    rw [Formula.realize_iff, Formula.realize_rel, Formula.realize_relabel]
    exact (iff_of_eq (congrFun (congrFun hfix i) x)).symm


-- @@ L186-186 verbatim
end Realize


-- @@ L188-188 verbatim
end StepDef


-- @@ L190-190 verbatim
/-! ### The walk of a partial iteration -/


-- @@ L192-192 verbatim
section ToSOTC


-- @@ L194-194 verbatim
variable (d : StepDef (L.sum Language.order))


-- @@ L196-203 verbatim
/-- The SO(TC) specification of a partial fixed-point definition: walk the
deterministic iteration of the step formulas from the empty assignment, and
accept at a stable stage satisfying the output. -/
noncomputable def StepDef.toSOTCSpec : SOTCSpec L where
  B := d.B
  step := d.nextSentence
  src := d.botSentence
  tgt := d.isFixedPtF ⊓ d.out


-- @@ L205-205 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A]


-- @@ L207-209 verbatim
theorem StepDef.toSOTCSpec_step_iff (ρ σ : d.B.Assignment A) :
    d.toSOTCSpec.Step ρ σ ↔ σ = d.next ρ :=
  d.realize_nextSentence ρ σ


-- @@ L211-213 verbatim
theorem StepDef.toSOTCSpec_isSrc_iff (ρ : d.B.Assignment A) :
    d.toSOTCSpec.IsSrc ρ ↔ ρ = d.B.botAssign A :=
  d.realize_botSentence ρ


-- @@ L215-225 verbatim
theorem StepDef.toSOTCSpec_isTgt_iff (ρ : d.B.Assignment A) :
    d.toSOTCSpec.IsTgt ρ ↔ IsFixedPt d.next ρ ∧
      @Sentence.Realize _ A (d.B.structure₁ (L := L.sum Language.order) ρ) d.out := by
  let := d.B.structure ρ
  have h : (@Sentence.Realize _ A (d.B.structure₁ (L := L.sum Language.order) ρ)
        (d.isFixedPtF ⊓ d.out)) ↔
      (@Sentence.Realize _ A (d.B.structure₁ (L := L.sum Language.order) ρ)
          d.isFixedPtF ∧
        @Sentence.Realize _ A (d.B.structure₁ (L := L.sum Language.order) ρ) d.out) :=
    BoundedFormula.realize_inf
  exact h.trans (and_congr (d.realize_isFixedPtF ρ) Iff.rfl)


-- @@ L227-245 verbatim
/-- The states reachable from the empty assignment are exactly the partial
stages. -/
theorem StepDef.reach_toSOTCSpec (σ : d.B.Assignment A) :
    d.toSOTCSpec.Reach (d.B.botAssign A) σ ↔ ∃ n, σ = d.partStage A n := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail τ υ _ hstep ih =>
      obtain ⟨n, rfl⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [d.partStage_succ]
      exact ((d.toSOTCSpec_step_iff _ _).mp hstep : υ = _)
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
      refine ih.tail ((d.toSOTCSpec_step_iff _ _).mpr ?_)
      exact d.partStage_succ n


-- @@ L247-261 verbatim
/-- **Acceptance of the walk is the value of the partial definition**: a
stable stage satisfying the output is reachable from the empty assignment
exactly when the iteration converges to a limit satisfying the output. -/
theorem StepDef.accepts_toSOTCSpec :
    d.toSOTCSpec.Accepts A ↔ d.PFPHolds A := by
  constructor
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    have hρ : ρ = d.B.botAssign A := (d.toSOTCSpec_isSrc_iff ρ).mp hsrc
    subst hρ
    obtain ⟨n, rfl⟩ := (d.reach_toSOTCSpec σ).mp hreach
    obtain ⟨hfix, hout⟩ := (d.toSOTCSpec_isTgt_iff _).mp htgt
    exact ⟨n, hfix, hout⟩
  · rintro ⟨n, hfix, hout⟩
    refine ⟨d.B.botAssign A, d.partStage A n, (d.toSOTCSpec_isSrc_iff _).mpr rfl,
      (d.toSOTCSpec_isTgt_iff _).mpr ⟨hfix, hout⟩, (d.reach_toSOTCSpec _).mpr ⟨n, rfl⟩⟩


-- @@ L263-263 verbatim
end ToSOTC


-- @@ L265-265 verbatim
/-! ### FO(≤, PFP) is contained in PSPACE -/


-- @@ L267-276 verbatim
/-- **Every FO(≤, PFP) definable problem is SO(TC) definable**: the partial
iteration is a deterministic walk on the assignments of its own block.
Registered in the Lax archive as
[`Lax134656.PartialFixedPointCapture.pfpDefinable_sotcDefinable`](https://laxarchive.org/lax-134656/Lax134656.PartialFixedPointCapture.html#s-Lax134656.PartialFixedPointCapture.pfpDefinable_sotcDefinable). -/
theorem PFPDefinable.sotcDefinable [L.IsRelational] {P : DecisionProblem L} (h : PFPDefinable P) :
    SOTCDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.toSOTCSpec, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (d.accepts_toSOTCSpec (A := A)).symm


-- @@ L278-281 verbatim
/-- **FO(≤, PFP) is contained in PSPACE.** -/
theorem mem_PSPACE_of_pfpDefinable [L.IsRelational] {P : DecisionProblem L} (h : PFPDefinable P) :
    P ∈ PSPACE :=
  (mem_PSPACE_iff P).mpr h.sotcDefinable


-- @@ L283-283 verbatim
end DescriptiveComplexity
