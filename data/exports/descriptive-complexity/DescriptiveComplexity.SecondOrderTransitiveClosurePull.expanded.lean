/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderTransitiveClosure
import DescriptiveComplexity.SecondOrderPull
import DescriptiveComplexity.OrderedComposition


-- @@ L10-64 verbatim
/-!
# Pulling SO(TC) definability back through an interpretation

SO(TC) definability is closed under (ordered) first-order reductions
(`DescriptiveComplexity.SOTCDefinable.of_orderedReduction`). This is what makes
`DescriptiveComplexity.PSPACE` a `DescriptiveComplexity.ComplexityClass` rather than a
mere definability predicate.

## The walk on the interpreted structure, read on the base structure

A state of an SO(TC) walk is an assignment of a second-order block, so pulling
a specification back is *entirely* a matter of pulling its block back – there
are no tuples of elements and no modes to rearrange, unlike
`DescriptiveComplexity.TCSpec.comap`. The block pullback of
`DescriptiveComplexity.SecondOrderPull` already supplies everything:

* the pulled block is `DescriptiveComplexity.SOBlock.pull`, one `(n·d)`-ary relation
  variable on the base universe per `n`-tuple of tags;
* its assignments are in bijection with the assignments of the original block
  on the interpreted universe (`DescriptiveComplexity.SOBlock.pullAssignEquiv`,
  the two transfers `pullAssign`/`mergeAssign` being mutually inverse);
* the three sentences are pulled back by
  `DescriptiveComplexity.FOInterpretation.pullSentence` through the interpretation
  extended along the block – twice for the transition sentence, which sees two
  copies of the block.

The order enters as it does for the clausal fragments and for FO(TC): the
sentences live over the *ordered* expansion of the target vocabulary, so the
pullback goes through `DescriptiveComplexity.FOInterpretation.ordExtend`, which
interprets the target's order as the lexicographic order on tagged tuples, and
the interpreted structure is equipped with that same order
(`DescriptiveComplexity.FOInterpretation.mapLinearOrder`). Since SO(TC)
definability is required *for every* linear order, the lexicographic one is
available.

## The chain of transports

Each of the three correctness lemmas is the same three-step chain, read from
the interpreted side:

1. `DescriptiveComplexity.FOInterpretation.realize_pullSentence` – the pulled
   sentence on the base structure is the original on the interpreted one;
2. `DescriptiveComplexity.FOInterpretation.extendSOEquiv` – interpreting and then
   expanding by a block is expanding by the pulled block and then interpreting
   (once per copy of the block);
3. `DescriptiveComplexity.FOInterpretation.ordExtendLEquiv` – the order-extended
   interpretation produces the interpreted structure with the lexicographic
   order.

Steps 2 and 3 need the expansion of an isomorphism along a block that is
interpreted by the *same* assignment on both sides, which is
`DescriptiveComplexity.SOBlock.extendEquiv` at an identity map (its transport
`DescriptiveComplexity.SOBlock.mapAssign` along `Equiv.refl` is the identity, by
definitional eta).
-/


-- @@ L66-66 verbatim
namespace DescriptiveComplexity


-- @@ L68-68 verbatim
open FirstOrder


-- @@ L70-70 verbatim
open Language Structure


-- @@ L72-72 verbatim
/-! ### The pullback of a specification -/


-- @@ L74-74 verbatim
section Comap


-- @@ L76-77 verbatim
variable {L L' : Language.{0, 0}} [L'.IsRelational] {Tag : Type} [Finite Tag]
  [LinearOrder Tag] {d : ℕ}


-- @@ L79-85 verbatim
/-- The interpretation extended with the order and along one copy of a block:
the layer through which the source and target sentences are pulled back. -/
noncomputable def FOInterpretation.ordExtendSO
    (I : FOInterpretation (L.sum Language.order) L' Tag d) (B : SOBlock) :
    FOInterpretation ((L.sum Language.order).sum (B.pull Tag d).lang)
      ((L'.sum Language.order).sum B.lang) Tag d :=
  I.ordExtend.extendSO B


-- @@ L87-97 verbatim
/-- **The pullback of a specification through an interpretation**: the walk of
`spec` on the interpreted structure, written on the base structure. Its states
are the assignments of the pulled block; its three sentences are pulled back
through the order-extended interpretation, expanded along one copy of the block
for the endpoints and along two for the transition. -/
noncomputable def SOTCSpec.comap (spec : SOTCSpec L')
    (I : FOInterpretation (L.sum Language.order) L' Tag d) : SOTCSpec L where
  B := spec.B.pull Tag d
  step := ((I.ordExtendSO spec.B).extendSO spec.B).pullSentence spec.step
  src := (I.ordExtendSO spec.B).pullSentence spec.src
  tgt := (I.ordExtendSO spec.B).pullSentence spec.tgt


-- @@ L99-99 verbatim
variable (spec : SOTCSpec L') (I : FOInterpretation (L.sum Language.order) L' Tag d)

-- @@ L100-100 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A]


-- @@ L102-110 verbatim
/-- **Starting states correspond.** -/
theorem SOTCSpec.comap_isSrc_iff (ρ : spec.B.Assignment (I.Map A)) :
    letI := I.mapLinearOrder A
    spec.IsSrc ρ ↔ (spec.comap I).IsSrc (spec.B.pullAssign ρ) := by
  let := I.mapLinearOrder A
  let := (spec.B.pull Tag d).structure₁ (L := L.sum Language.order) (spec.B.pullAssign ρ)
  exact Iff.symm (((I.ordExtendSO spec.B).realize_pullSentence spec.src A).trans
    ((realize_sentence_of_equiv (I.ordExtend.extendSOEquiv spec.B A ρ) spec.src).trans
      (realize_sentence_of_equiv (spec.B.extendEquiv (I.ordExtendLEquiv A) ρ) spec.src)))


-- @@ L112-120 verbatim
/-- **Accepting states correspond.** -/
theorem SOTCSpec.comap_isTgt_iff (ρ : spec.B.Assignment (I.Map A)) :
    letI := I.mapLinearOrder A
    spec.IsTgt ρ ↔ (spec.comap I).IsTgt (spec.B.pullAssign ρ) := by
  let := I.mapLinearOrder A
  let := (spec.B.pull Tag d).structure₁ (L := L.sum Language.order) (spec.B.pullAssign ρ)
  exact Iff.symm (((I.ordExtendSO spec.B).realize_pullSentence spec.tgt A).trans
    ((realize_sentence_of_equiv (I.ordExtend.extendSOEquiv spec.B A ρ) spec.tgt).trans
      (realize_sentence_of_equiv (spec.B.extendEquiv (I.ordExtendLEquiv A) ρ) spec.tgt)))


-- @@ L122-138 verbatim
/-- **Steps correspond**: a step of the specification on the interpreted
structure is a step of the pullback on the base structure. -/
theorem SOTCSpec.comap_step_iff (ρ σ : spec.B.Assignment (I.Map A)) :
    letI := I.mapLinearOrder A
    spec.Step ρ σ ↔ (spec.comap I).Step (spec.B.pullAssign ρ) (spec.B.pullAssign σ) := by
  let := I.mapLinearOrder A
  let := (spec.B.pull Tag d).structure₁ (L := L.sum Language.order) (spec.B.pullAssign ρ)
  let := (spec.B.pull Tag d).structure₂ (L := L.sum Language.order) (spec.B.pullAssign ρ)
    (spec.B.pullAssign σ)
  exact Iff.symm ((((I.ordExtendSO spec.B).extendSO spec.B).realize_pullSentence
      spec.step A).trans
    ((realize_sentence_of_equiv
        ((I.ordExtendSO spec.B).extendSOEquiv spec.B A σ) spec.step).trans
      ((realize_sentence_of_equiv
          (spec.B.extendEquiv' (I.ordExtend.extendSOEquiv spec.B A ρ) σ) spec.step).trans
        (realize_sentence_of_equiv
          (spec.B.extendEquiv₂ (I.ordExtendLEquiv A) ρ σ) spec.step))))


-- @@ L140-147 verbatim
/-- **The pullback is correct**: it accepts the base structure exactly when the
specification accepts the interpreted one. -/
theorem SOTCSpec.comap_accepts_iff :
    letI := I.mapLinearOrder A
    spec.Accepts (I.Map A) ↔ (spec.comap I).Accepts A := by
  let := I.mapLinearOrder A
  exact SOTCSpec.accepts_congr (spec.B.pullAssignEquiv Tag d A) (spec.comap_step_iff I)
    (spec.comap_isSrc_iff I) (spec.comap_isTgt_iff I)


-- @@ L149-149 verbatim
end Comap


-- @@ L151-151 verbatim
/-! ### Closure under reductions -/


-- @@ L153-153 verbatim
section Closure


-- @@ L155-156 verbatim
variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L}
  {Q : DecisionProblem L'}


-- @@ L158-175 verbatim
/-- **SO(TC) definability is closed under ordered first-order reductions.** The
walk of the specification on the interpreted structure is a walk on the base
structure, its states the assignments of the pulled block.
Registered in the Lax archive as
[`Lax134656.PSPACEClosure.PSPACE_mem_of_orderedReduction`](https://laxarchive.org/lax-134656/Lax134656.PSPACEClosure.html#s-Lax134656.PSPACEClosure.PSPACE_mem_of_orderedReduction). -/
theorem SOTCDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : SOTCDefinable Q) :
    SOTCDefinable P := by
  obtain ⟨spec, hspec⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨spec.comap f.toInterpretation, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans ((hspec (f.toInterpretation.Map A)).trans
    (spec.comap_accepts_iff f.toInterpretation))


-- @@ L177-182 verbatim
/-- SO(TC) definability is closed under first-order reductions.
Registered in the Lax archive as
[`Lax134656.PSPACEClosure.PSPACE_mem_of_foReduction`](https://laxarchive.org/lax-134656/Lax134656.PSPACEClosure.html#s-Lax134656.PSPACEClosure.PSPACE_mem_of_foReduction). -/
theorem SOTCDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : SOTCDefinable Q) :
    SOTCDefinable P :=
  h.of_orderedReduction f.toOrdered


-- @@ L184-184 verbatim
end Closure


-- @@ L186-186 verbatim
end DescriptiveComplexity
