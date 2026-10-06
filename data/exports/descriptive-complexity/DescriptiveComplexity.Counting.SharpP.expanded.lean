/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting
import DescriptiveComplexity.SecondOrderOrdered
import Mathlib.SetTheory.Cardinal.Finite


-- @@ L10-41 verbatim
/-!
# Counting the witnesses of a second-order block: `#P`-definability

Fagin's theorem reads NP as the problems defined by a sentence `∃X̄. φ` with `φ`
first-order. The counting analog, due to Saluja, Subrahmanyam and Thakur
([1995][saluja1995descriptive]), reads `#P` as the functions *counting the
witnesses* of such a sentence, over ordered structures: the number of
assignments of the block `X̄` under which the first-order kernel `φ` holds.
This is also the prenex normal form `ΣX̄. φ` of the logic ΣQSO(FO) of Arenas,
Muñoz and Riveros ([2020][arenas2020descriptive]), who show that every formula
of that logic can be brought to it.

This file sets up that notion:

* `DescriptiveComplexity.witnessCount B φ A` is the number of assignments of the block
  `B` on `A` satisfying the kernel `φ`;
* `DescriptiveComplexity.SharpPDefinable C` states that the counting problem `C` is
  the witness count of some kernel *over the ordered expansion*, whatever the
  linear order of the instance. The order is a parameter here and not a guessed
  relation as in `DescriptiveComplexity.SigmaSODefinable`: guessing it would multiply
  every count by the number of linear orders;
* `DescriptiveComplexity.CountingProblem.ofKernel B φ` is the witness-counting problem
  of an order-free kernel, the counting version of the decision problem the
  kernel defines.

The closure theorem, `DescriptiveComplexity.SharpPDefinable.of_orderedParsimonious`,
pulls a kernel back through a parsimonious reduction. The decision-side
pullback of `DescriptiveComplexity.SecondOrderPull` only needs each assignment of the
pulled block to come from one of the original block; counting needs the
correspondence to be a bijection (`DescriptiveComplexity.SOBlock.pullAssignEquiv`),
which it is because the interpreted universe is all of `Tag × A^d`.
-/


-- @@ L43-43 verbatim
namespace DescriptiveComplexity


-- @@ L45-45 verbatim
open FirstOrder


-- @@ L47-47 verbatim
open Language Structure


-- @@ L49-49 verbatim
/-! ### Counting witnesses -/


-- @@ L51-51 verbatim
section Witness


-- @@ L53-53 verbatim
variable {L : Language.{0, 0}}


-- @@ L55-60 verbatim
/-- The number of assignments of the block `B` on the structure `A` under which
the first-order kernel `φ` holds. -/
noncomputable def witnessCount (B : SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [inst : L.Structure A] : ℕ :=
  Nat.card {ρ : B.Assignment A //
    @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ)) φ}


-- @@ L62-72 verbatim
/-- Transport of block assignments along an equivalence, as an equivalence. -/
def SOBlock.mapAssignEquiv (B : SOBlock) {A A' : Type} (e : A ≃ A') :
    B.Assignment A ≃ B.Assignment A' where
  toFun := B.mapAssign e
  invFun := B.mapAssign e.symm
  left_inv ρ := by
    funext i x
    simp [SOBlock.mapAssign]
  right_inv ρ := by
    funext i x
    simp [SOBlock.mapAssign]


-- @@ L74-82 verbatim
/-- The witness count is isomorphism-invariant. -/
theorem witnessCount_iso (B : SOBlock) (φ : (L.sum B.lang).Sentence) {A A' : Type}
    [L.Structure A] [L.Structure A'] (e : A ≃[L] A') :
    witnessCount B φ A = witnessCount B φ A' :=
  Nat.card_congr (Equiv.subtypeEquiv (B.mapAssignEquiv e.toEquiv) fun ρ =>
    @StrongHomClass.realize_sentence (L.sum B.lang) A A'
      (@sumStructure L B.lang A _ (B.structure ρ))
      (@sumStructure L B.lang A' _ (B.structure (B.mapAssign e.toEquiv ρ))) _ _ _
      (B.extendEquiv e ρ) φ)


-- @@ L84-87 verbatim
/-- Block assignments on a finite universe are finitely many. -/
instance SOBlock.finite_assignment (B : SOBlock) (A : Type) [Finite A] :
    Finite (B.Assignment A) :=
  inferInstanceAs (Finite (∀ i : B.ι, (Fin (B.arity i) → A) → Prop))


-- @@ L89-96 verbatim
/-- On a finite structure, the witness count is positive exactly when there is
a witness. -/
theorem witnessCount_pos_iff (B : SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [inst : L.Structure A] [Finite A] :
    0 < witnessCount B φ A ↔ ∃ ρ : B.Assignment A,
      @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A inst (B.structure ρ)) φ := by
  rw [witnessCount, Nat.card_pos_iff]
  exact ⟨fun ⟨⟨ρ, hρ⟩, _⟩ => ⟨ρ, hρ⟩, fun ⟨ρ, hρ⟩ => ⟨⟨⟨ρ, hρ⟩⟩, inferInstance⟩⟩


-- @@ L98-98 verbatim
end Witness


-- @@ L100-100 verbatim
/-! ### Pulling a witness count back through an interpretation -/


-- @@ L102-102 verbatim
section Pull


-- @@ L104-104 verbatim
variable {L₁ L₂ : Language.{0, 0}} {Tag : Type} [Finite Tag] {d : ℕ} {A : Type}


-- @@ L106-119 verbatim
/-- **Pulling a witness count back through an interpretation**: the witnesses
of a kernel in the interpreted structure are, bijectively, the witnesses of the
pulled kernel, over the pulled block, in the base structure. -/
theorem witnessCount_map [L₂.IsRelational] (I : FOInterpretation L₁ L₂ Tag d) (B : SOBlock)
    (φ : (L₂.sum B.lang).Sentence) (A : Type) [instA : L₁.Structure A] :
    witnessCount B φ (I.Map A) =
      witnessCount (B.pull Tag d) ((I.extendSO B).pullSentence φ) A := by
  refine Nat.card_congr (Equiv.subtypeEquiv (B.pullAssignEquiv Tag d A) fun ρ => ?_)
  let := (B.pull Tag d).structure (B.pullAssign ρ)
  exact (@StrongHomClass.realize_sentence (L₂.sum B.lang) ((I.extendSO B).Map A) (I.Map A)
      (FOInterpretation.mapStructure (I.extendSO B) A)
      (@sumStructure L₂ B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) _ _ _
      (I.extendSOEquiv B A ρ) φ).symm.trans
    ((I.extendSO B).realize_pullSentence φ A).symm


-- @@ L121-121 verbatim
end Pull


-- @@ L123-123 verbatim
/-! ### `#P`-definability -/


-- @@ L125-125 verbatim
section Definable


-- @@ L127-127 verbatim
variable {L : Language.{0, 0}} [L.IsRelational]


-- @@ L129-137 verbatim
/-- A counting problem is **`#P`-definable** if, on nonempty finite structures,
it counts the witnesses of an existential second-order sentence over the
ordered expansion: for some block `B` and first-order kernel `φ`, its value is
the number of assignments of `B` satisfying `φ`, whatever the linear order of
the instance. -/
def SharpPDefinable (C : CountingProblem L) : Prop :=
  ∃ (B : SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = witnessCount B φ A


-- @@ L139-143 verbatim
theorem sharpPDefinable_congr {C C' : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = C' A) (hC : SharpPDefinable C) :
    SharpPDefinable C' := by
  obtain ⟨B, φ, hφ⟩ := hC
  exact ⟨B, φ, fun A _ _ _ _ => (h A).symm.trans (hφ A)⟩


-- @@ L145-146 verbatim
variable {L' : Language.{0, 0}} [L'.IsRelational] {C : CountingProblem L}
  {D : CountingProblem L'}


-- @@ L148-164 verbatim
/-- **`#P`-definability is closed under ordered parsimonious reductions.**
Registered in the Lax archive as
[`Lax366625.SharpPClosure.SharpP_mem_of_orderedParsimonious`](https://laxarchive.org/lax-366625/Lax366625.SharpPClosure.html#s-Lax366625.SharpPClosure.SharpP_mem_of_orderedParsimonious). -/
theorem SharpPDefinable.of_orderedParsimonious (f : C ≤ᵖ[≤] D) (h : SharpPDefinable D) :
    SharpPDefinable C := by
  obtain ⟨B, φ, hφ⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨B.pull f.Tag f.dim, (f.toInterpretation.ordExtend.extendSO B).pullSentence φ, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have : Finite (f.toInterpretation.Map A) := f.toInterpretation.map_finite A
  have : Nonempty (f.toInterpretation.Map A) := f.toInterpretation.map_nonempty A
  rw [f.correct A, hφ (f.toInterpretation.Map A),
    ← witnessCount_map f.toInterpretation.ordExtend B φ A]
  exact (witnessCount_iso B φ (f.toInterpretation.ordExtendLEquiv A)).symm


-- @@ L166-169 verbatim
/-- `#P`-definability is closed under parsimonious reductions. -/
theorem SharpPDefinable.of_parsimonious (f : C ≤ᵖ D) (h : SharpPDefinable D) :
    SharpPDefinable C :=
  h.of_orderedParsimonious f.toOrdered


-- @@ L171-171 verbatim
end Definable


-- @@ L173-173 verbatim
/-! ### The witness-counting problem of an order-free kernel -/


-- @@ L175-175 verbatim
section OfKernel


-- @@ L177-177 verbatim
variable {L : Language.{0, 0}} [L.IsRelational]


-- @@ L179-186 verbatim
/-- The counting problem of an existential second-order sentence: the number of
witnesses of the block `B` for the first-order kernel `φ`. It is the counting
version of the decision problem `∃B. φ`, which is its support
(`DescriptiveComplexity.CountingProblem.ofKernel_support_iff`). -/
noncomputable def CountingProblem.ofKernel (B : SOBlock) (φ : (L.sum B.lang).Sentence) :
    CountingProblem L where
  Count := fun A inst => @witnessCount L B φ A inst
  iso_invariant := fun e => witnessCount_iso B φ e


-- @@ L188-190 verbatim
theorem CountingProblem.ofKernel_apply (B : SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [L.Structure A] : CountingProblem.ofKernel B φ A = witnessCount B φ A :=
  rfl


-- @@ L192-197 verbatim
/-- The support of a witness-counting problem is the problem its sentence
defines. -/
theorem CountingProblem.ofKernel_support_iff (B : SOBlock) (φ : (L.sum B.lang).Sentence)
    (A : Type) [L.Structure A] [Finite A] :
    (CountingProblem.ofKernel B φ).support A ↔ SORealize L A [B] φ true :=
  witnessCount_pos_iff B φ A


-- @@ L199-202 verbatim
/-- The lift of an order-free kernel to the ordered expansion. -/
def orderFreeKernel (B : SOBlock) (φ : (L.sum B.lang).Sentence) :
    ((L.sum Language.order).sum B.lang).Sentence :=
  (LHom.sumMap LHom.sumInl (LHom.id B.lang)).onSentence φ


-- @@ L204-215 verbatim
/-- The witness-counting problem of an order-free kernel is `#P`-definable: its
kernel simply ignores the order. -/
theorem sharpPDefinable_ofKernel (B : SOBlock) (φ : (L.sum B.lang).Sentence) :
    SharpPDefinable (CountingProblem.ofKernel B φ) := by
  refine ⟨B, orderFreeKernel B φ, fun A instA _ _ _ => ?_⟩
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun ρ => ?_)
  let := B.structure ρ
  have : (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
      (LHom.id B.lang)).IsExpansionOn A :=
    ⟨fun f _ => by cases f <;> rfl, fun r _ => by cases r <;> rfl⟩
  exact (LHom.realize_onSentence A (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
    (LHom.id B.lang)) φ).symm


-- @@ L217-217 verbatim
end OfKernel


-- @@ L219-219 verbatim
end DescriptiveComplexity
