/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Matrix


-- @@ L8-31 verbatim
/-!
# Peeling a quantifier into a block

The semantic core of the translation lemma. Two facts, both independent of any
syntax.

**A guarded block is a point.** A second-order quantifier ranges over *all*
assignments of `DescriptiveComplexity.ExpExpansion.pointBlock`; the quantifier
being translated ranges over the *points* of the expanded universe, which are
the assignments the point guard admits. The two match up
(`DescriptiveComplexity.ExpExpansion.exists_point_iff`,
`DescriptiveComplexity.ExpExpansion.forall_point_iff`): a guarded block *is* a
point, existentially with the guard as a conjunct and universally with the guard
as a hypothesis, which is the usual shape of relativized quantification.

**A guard can be pulled through the rest of the prefix.** The guard of round `i`
sits at nesting depth `i` in the kernel, so peeling round `i` first has to move
it out past the quantifiers that remain
(`DescriptiveComplexity.altBlockQuant_and_const`,
`DescriptiveComplexity.altBlockQuant_const_imp`). Both directions need the block
assignments to be inhabited, which they are –
`DescriptiveComplexity.SOBlock.botAssign` – and the existential case of the
implication needs excluded middle, as relativized quantification always does.
-/


-- @@ L33-33 verbatim
namespace DescriptiveComplexity


-- @@ L35-35 verbatim
open FirstOrder


-- @@ L37-37 verbatim
open Language Structure


-- @@ L39-39 verbatim
/-! ### Moving a constant through the prefix -/


-- @@ L41-41 verbatim
section Const


-- @@ L43-43 verbatim
variable {B : SOBlock} {A : Type}


-- @@ L45-68 verbatim
/-- A conjunct not depending on the rounds moves out of the prefix. -/
theorem altBlockQuant_and_const (g : Prop) :
    ∀ (k : ℕ) (P : (Fin k → B.Assignment A) → Prop) (pol : Bool),
      altBlockQuant A B k (fun ρs => g ∧ P ρs) pol ↔ g ∧ altBlockQuant A B k P pol := by
  intro k
  induction k with
  | zero => intro P pol; exact Iff.rfl
  | succ k ih =>
    intro P pol
    cases pol with
    | true =>
      constructor
      · rintro ⟨ρ, h⟩
        obtain ⟨hg, h'⟩ := (ih _ false).mp h
        exact ⟨hg, ρ, h'⟩
      · rintro ⟨hg, ρ, h⟩
        exact ⟨ρ, (ih _ false).mpr ⟨hg, h⟩⟩
    | false =>
      constructor
      · intro h
        exact ⟨((ih _ true).mp (h (B.botAssign A))).1,
          fun ρ => ((ih _ true).mp (h ρ)).2⟩
      · rintro ⟨hg, h⟩ ρ
        exact (ih _ true).mpr ⟨hg, h ρ⟩


-- @@ L70-97 verbatim
/-- A hypothesis not depending on the rounds moves out of the prefix. The
existential case is where excluded middle enters: with the hypothesis false, any
round will do, and there is one. -/
theorem altBlockQuant_const_imp (g : Prop) :
    ∀ (k : ℕ) (P : (Fin k → B.Assignment A) → Prop) (pol : Bool),
      altBlockQuant A B k (fun ρs => g → P ρs) pol ↔ (g → altBlockQuant A B k P pol) := by
  classical
  intro k
  induction k with
  | zero => intro P pol; exact Iff.rfl
  | succ k ih =>
    intro P pol
    cases pol with
    | true =>
      constructor
      · rintro ⟨ρ, h⟩ hg
        exact ⟨ρ, (ih _ false).mp h hg⟩
      · intro h
        by_cases hg : g
        · obtain ⟨ρ, hρ⟩ := h hg
          exact ⟨ρ, (ih _ false).mpr fun _ => hρ⟩
        · exact ⟨B.botAssign A, (ih _ false).mpr fun hg' => absurd hg' hg⟩
    | false =>
      constructor
      · intro h hg ρ
        exact (ih _ true).mp (h ρ) hg
      · intro h ρ
        exact (ih _ true).mpr fun hg => h hg ρ


-- @@ L99-99 verbatim
end Const


-- @@ L101-101 verbatim
/-! ### A guarded block is a point -/


-- @@ L103-103 verbatim
namespace ExpExpansion


-- @@ L105-105 verbatim
variable {L : Language.{0, 0}} {X : ExpExpansion L} {m : ℕ}

-- @@ L106-106 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A]


-- @@ L108-110 verbatim
/-- The block assignment carrying a point. -/
def pointAssign (p : X.Map A) : X.pointBlock.Assignment A :=
  SOBlock.tagAssign p.1.1 p.1.2


-- @@ L112-115 verbatim
@[simp]
theorem roundAssign_apply [Finite A] [Nonempty A] (pts : Fin m → X.Map A) (i : Fin m) :
    roundAssign pts i = pointAssign (pts i) :=
  rfl


-- @@ L117-119 verbatim
/-- The condition the point guard expresses, semantically. -/
def IsPointAssign (σ : X.pointBlock.Assignment A) : Prop :=
  ∃ (t : X.Tag) (ρ : X.B.Assignment A), σ = SOBlock.tagAssign t ρ ∧ DomHolds (X := X) (t, ρ)


-- @@ L121-122 verbatim
theorem isPointAssign_pointAssign (p : X.Map A) : IsPointAssign (pointAssign p) :=
  ⟨p.1.1, p.1.2, rfl, p.2⟩


-- @@ L124-132 verbatim
/-- **A guarded block is a point, existentially.** -/
theorem exists_point_iff (P : X.pointBlock.Assignment A → Prop) :
    (∃ σ : X.pointBlock.Assignment A, IsPointAssign (X := X) σ ∧ P σ) ↔
      ∃ p : X.Map A, P (pointAssign p) := by
  constructor
  · rintro ⟨σ, ⟨t, ρ, rfl, hd⟩, hP⟩
    exact ⟨pt t ρ hd, hP⟩
  · rintro ⟨p, hP⟩
    exact ⟨pointAssign p, isPointAssign_pointAssign p, hP⟩


-- @@ L134-142 verbatim
/-- **A guarded block is a point, universally.** -/
theorem forall_point_iff (P : X.pointBlock.Assignment A → Prop) :
    (∀ σ : X.pointBlock.Assignment A, IsPointAssign (X := X) σ → P σ) ↔
      ∀ p : X.Map A, P (pointAssign p) := by
  constructor
  · intro h p
    exact h _ (isPointAssign_pointAssign p)
  · rintro h σ ⟨t, ρ, rfl, hd⟩
    exact h (pt t ρ hd)


-- @@ L144-150 verbatim
/-! ### The peel steps

Peeling the outermost quantifier of the prefix: the guard of the leading round
moves out past the rounds that remain
(`DescriptiveComplexity.altBlockQuant_and_const`,
`DescriptiveComplexity.altBlockQuant_const_imp`), and what is left of it turns
the round into a point (`exists_point_iff`, `forall_point_iff`). -/


-- @@ L152-161 verbatim
/-- **Peeling an existential quantifier.** -/
theorem altBlockQuant_peel_ex {k : ℕ}
    (R : X.pointBlock.Assignment A → (Fin k → X.pointBlock.Assignment A) → Prop) :
    altBlockQuant A X.pointBlock (k + 1)
        (fun ρs => IsPointAssign (X := X) (ρs 0) ∧ R (ρs 0) (Fin.tail ρs)) true ↔
      ∃ p : X.Map A, altBlockQuant A X.pointBlock k (R (pointAssign p)) false := by
  change (∃ ρ, altBlockQuant A X.pointBlock k
    (fun ρs => IsPointAssign (X := X) ρ ∧ R ρ ρs) false) ↔ _
  refine Iff.trans (exists_congr fun ρ => altBlockQuant_and_const _ k (R ρ) false) ?_
  exact exists_point_iff fun σ => altBlockQuant A X.pointBlock k (R σ) false


-- @@ L163-172 verbatim
/-- **Peeling a universal quantifier.** -/
theorem altBlockQuant_peel_all {k : ℕ}
    (R : X.pointBlock.Assignment A → (Fin k → X.pointBlock.Assignment A) → Prop) :
    altBlockQuant A X.pointBlock (k + 1)
        (fun ρs => IsPointAssign (X := X) (ρs 0) → R (ρs 0) (Fin.tail ρs)) false ↔
      ∀ p : X.Map A, altBlockQuant A X.pointBlock k (R (pointAssign p)) true := by
  change (∀ ρ, altBlockQuant A X.pointBlock k
    (fun ρs => IsPointAssign (X := X) ρ → R ρ ρs) true) ↔ _
  refine Iff.trans (forall_congr' fun ρ => altBlockQuant_const_imp _ k (R ρ) true) ?_
  exact forall_point_iff fun σ => altBlockQuant A X.pointBlock k (R σ) true


-- @@ L174-174 verbatim
end ExpExpansion


-- @@ L176-176 verbatim
end DescriptiveComplexity
