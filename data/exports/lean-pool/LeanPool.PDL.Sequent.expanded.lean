/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finset.Sort
-- note: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Can.27t.20.23eval.20a.20Finset.20Nat.3F/near/577761910

public import LeanPool.PDL.Discon


-- @@ L15-15 verbatim
/-! # Sequents -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace PDL


-- @@ L21-21 verbatim
/-! ## Optional loaded formulas (Olfs) -/


-- @@ L23-24 verbatim
/-- In nodes we optionally have a negated loaded formula on the left or right. -/
abbrev Olf := Option (NegLoadFormula ⊕ NegLoadFormula)


-- @@ L26-33 verbatim
/-- The vocabulary of the optional loaded formula, ignoring its side. -/
@[simp]
def Olf.voc : Olf → Vocab
| none => {}
| some (Sum.inl nlf) => nlf.voc
| some (Sum.inr nlf) => nlf.voc

-- mathlib this?

-- @@ L34-41 verbatim
instance Option.instHasSubsetOption : HasSubset (Option α) := HasSubset.mk
  fun o1 o2 =>
  match o1, o2 with
  | none, _ => True
  | some _, none => False
  | some f, some g => f = g

-- mathlib this?

-- @@ L42-47 verbatim
@[simp]
theorem Option.some_subseteq {O : Option α} : (some x ⊆ O) ↔ some x = O := by
  cases O
  all_goals simp [HasSubset.Subset]

-- mathlib this?

-- @@ L48-51 verbatim
@[simp]
theorem Option.none_subseteq {O : Option α} : none ⊆ O := trivial

-- mathlib this?

-- @@ L52-61 verbatim
/-- The subset relation on `Option α` from `Option.instHasSubsetOption` is decidable. -/
instance Option.instDecidableSubset [DecidableEq α] (o1 o2 : Option α) :
    Decidable (o1 ⊆ o2) := by
  rcases o1 with _ | a
  · exact isTrue trivial
  · rcases o2 with _ | b
    · exact isFalse id
    · exact decidable_of_iff (a = b) (by simp)

-- mathlib this?

-- @@ L62-68 verbatim
/-- Instance that is used to say `(O : Olf) \ (O' : Olf)`. -/
instance Option.insHasSdiff [DecidableEq α] : SDiff (Option α) := SDiff.mk
  fun o1 del =>
  match o1, del with
  | none, _ => none
  | some f, none => some f
  | some f, some g => if f = g then none else some f


-- @@ L70-74 verbatim
@[simp]
lemma Option.insHasSdiff_none [DecidableEq α] :
    (none : Option α) \ o = none := by
  unfold Option.insHasSdiff
  grind


-- @@ L76-80 verbatim
@[simp]
lemma Option.insHasSdiff_remove_none_cancel [DecidableEq α] :
    o \ (none : Option α) = o := by
  unfold Option.insHasSdiff
  grind


-- @@ L82-86 verbatim
@[simp]
lemma Option.insHasSdiff_remove_sem_eq_none [DecidableEq α] :
    (some x) \ (some x : Option α) = none := by
  unfold Option.insHasSdiff
  grind


-- @@ L88-92 verbatim
/-- The unloaded left formula contributed by an optional loading. -/
def Olf.L : Olf → Finset Formula
| none => {}
| some (Sum.inl ⟨lf⟩) => {~ lf.unload}
| some (Sum.inr _) =>{}


-- @@ L94-95 verbatim
@[simp]
lemma Olf.L_none : Olf.L none = {} := by rfl

-- @@ L96-97 verbatim
@[simp]
lemma Olf.L_inr {lf} : Olf.L (some (Sum.inr lf)) = {} := by rfl

-- @@ L98-99 verbatim
@[simp]
lemma Olf.L_map_inr {olf} : Olf.L (Option.map Sum.inr olf) = {} := by cases olf <;> rfl

-- @@ L100-101 verbatim
@[simp]
lemma Olf.L_inl {lf} : Olf.L (some (Sum.inl lf)) = {~lf.1.unload} := by simp only [L]


-- @@ L103-104 verbatim
lemma Olf.L_subset_of_subset {O1 O2 : Olf} (h : O1 ⊆ O2) : O1.L ⊆ O2.L := by
  rcases O1 with _|χ <;> rcases O2 with _|χ' <;> simp_all [Olf.L]


-- @@ L106-111 verbatim
lemma Olf.L_sdiff_subset {O Ocond : Olf} : (O \ Ocond).L ⊆ O.L := by
  rcases O with _|χ
  · simp
  rcases Ocond with _|χ'
  · simp
  by_cases h : χ = χ' <;> simp_all [SDiff.sdiff, Olf.L]


-- @@ L113-117 verbatim
/-- The unloaded right formula contributed by an optional loading. -/
def Olf.R : Olf → Finset Formula
| none => {}
| some (Sum.inl _) => {}
| some (Sum.inr ⟨lf⟩) => {~ lf.unload}


-- @@ L119-120 verbatim
@[simp]
lemma Olf.R_none : Olf.R none = {} := by rfl

-- @@ L121-122 verbatim
@[simp]
lemma Olf.R_inl {lf} : Olf.R (some (Sum.inl lf)) = {} := by rfl

-- @@ L123-124 verbatim
@[simp]
lemma Olf.R_map_inl {olf} : Olf.R (Option.map Sum.inl olf) = {} := by cases olf <;> rfl

-- @@ L125-126 verbatim
@[simp]
lemma Olf.R_inr {lf} : Olf.R (some (Sum.inr lf)) = {~lf.1.unload} := by simp only [R]


-- @@ L128-129 verbatim
lemma Olf.R_subset_of_subset {O1 O2 : Olf} (h : O1 ⊆ O2) : O1.R ⊆ O2.R := by
  rcases O1 with _|χ <;> rcases O2 with _|χ' <;> simp_all [Olf.R]


-- @@ L131-136 verbatim
lemma Olf.R_sdiff_subset {O Ocond : Olf} : (O \ Ocond).R ⊆ O.R := by
  rcases O with _|χ
  · simp
  rcases Ocond with _|χ'
  · simp
  by_cases h : χ = χ' <;> simp_all [SDiff.sdiff, Olf.R]


-- @@ L138-142 verbatim
/-- Use the new optional value when present, otherwise retain the old value. -/
@[simp]
def _root_.Option.pdlOverwrite : Option α → Option α → Option α
| old, none   => old
| _  , some x => some x


-- @@ L144-145 verbatim
/-- Remove the rule's required loading and install its new loading when present. -/
def Olf.change (oldO : Olf) (Ocond : Olf) (newO : Olf) : Olf := (oldO \ Ocond).pdlOverwrite newO


-- @@ L147-149 verbatim
@[simp]
theorem Olf.change_old_none_none {oldO} : Olf.change oldO none none = oldO := by
  cases oldO <;> simp [Olf.change, Option.pdlOverwrite, SDiff.sdiff]


-- @@ L151-153 verbatim
@[simp]
theorem Olf.change_none_none_new {newO} : Olf.change none none newO = newO := by
  cases newO <;> simp [Olf.change, Option.pdlOverwrite, SDiff.sdiff]


-- @@ L155-158 verbatim
@[simp]
theorem Olf.change_some {oldO whatever wnlf} :
    Olf.change oldO whatever (some wnlf) = some wnlf := by
  cases oldO <;> simp [Olf.change, Option.pdlOverwrite]


-- @@ L160-162 verbatim
@[simp]
theorem Olf.change_some_some_eq {Onew nχ} : Olf.change (some nχ) (some nχ) Onew = Onew := by
  cases Onew <;> simp [Olf.change, Option.pdlOverwrite]


-- @@ L164-169 verbatim
/-- Whether the optional loading is absent. -/
@[simp]
def Olf.isNone : Olf → Prop
 | .none => True
 | .some (Sum.inl _) => False
 | .some (Sum.inr _) => False


-- @@ L171-176 verbatim
/-- Whether the optional loading belongs to the left component. -/
@[simp]
def Olf.isLeft : Olf → Prop
 | .none => False
 | .some (Sum.inl _) => True
 | .some (Sum.inr _) => False


-- @@ L178-183 verbatim
/-- Whether the optional loading belongs to the right component. -/
@[simp]
def Olf.isRight : Olf → Prop
 | .none => False
 | .some (Sum.inl _) => False
 | .some (Sum.inr _) => True


-- @@ L185-189 verbatim
instance instDecidableOlfisNone (o : Olf) : Decidable o.isNone := by
  rcases o with _|(_|_)
  · apply isTrue; simp_all
  · apply isFalse; simp_all
  · apply isFalse; simp_all


-- @@ L191-195 verbatim
instance instDecidableOlfisLeft (o : Olf) : Decidable o.isLeft := by
  rcases o with _|(_|_)
  · apply isFalse; simp_all
  · apply isTrue; simp_all
  · apply isFalse; simp_all


-- @@ L197-201 verbatim
instance instDecidableOlfisRight (o : Olf) : Decidable o.isRight := by
  rcases o with _|(_|_)
  · apply isFalse; simp_all
  · apply isFalse; simp_all
  · apply isTrue; simp_all


-- @@ L203-203 verbatim
/-! ## Sequents and their (multi)set quality -/


-- @@ L205-209 verbatim
/-- A tableau node is labelled with two finite sets of formulas and an `Olf`.
Each formula is placed on the left or right and up to one formula may be loaded. -/
@[implicit_reducible]
def Sequent := Finset Formula × Finset Formula × Olf -- ⟨L, R, o⟩
  deriving DecidableEq, Repr


-- @@ L211-213 verbatim
/-- All ordinary formulas of a sequent, including its loading after unloading. -/
def Sequent.toFinset : Sequent → Finset Formula
| (L,R,O) => (L ∪ R) ∪ (O.map (Sum.elim negUnload negUnload)).toFinset


-- @@ L215-215 verbatim
/-! ## Components and sides of sequents -/


-- @@ L217-219 verbatim
/-- The ordinary formulas in the left component. -/
@[grind .]
def Sequent.L : Sequent → Finset Formula | ⟨L,_,_⟩ => L

-- @@ L220-222 verbatim
/-- The ordinary formulas in the right component. -/
@[grind .]
def Sequent.R : Sequent → Finset Formula | ⟨_,R,_⟩ => R

-- @@ L223-225 verbatim
/-- The optional loaded formula and its side. -/
@[grind .]
def Sequent.O : Sequent → Olf | ⟨_,_,O⟩ => O


-- @@ L227-228 verbatim
@[simp]
lemma Sequent.L_eq {L R O} : Sequent.L ⟨L,R,O⟩ = L := by simp [Sequent.L]

-- @@ L229-230 verbatim
@[simp]
lemma Sequent.R_eq {L R O} : Sequent.R ⟨L,R,O⟩ = R := by simp [Sequent.R]

-- @@ L231-232 verbatim
@[simp]
lemma Sequent.O_eq {L R O} : Sequent.O ⟨L,R,O⟩ = O := by simp [Sequent.O]


-- @@ L234-235 verbatim
/-- The left component including any left loading after unloading. -/
def Sequent.left (X : Sequent) : Finset Formula := X.L ∪ X.O.L

-- @@ L236-237 verbatim
/-- The right component including any right loading after unloading. -/
def Sequent.right (X : Sequent) : Finset Formula := X.R ∪ X.O.R


-- @@ L239-240 verbatim
@[simp]
lemma Sequent.left_eq {L R O} : Sequent.left ⟨L,R,O⟩ = L ∪ O.L := by simp [Sequent.left]

-- @@ L241-242 verbatim
@[simp]
lemma Sequent.right_eq {L R O} : Sequent.right ⟨L,R,O⟩ = R ∪ O.R := by simp [Sequent.right]



-- @@ L245-245 verbatim
/-! ## (Joint) vocabulary of sequents -/


-- @@ L247-250 verbatim
/-- Like `Olf.voc` but without the ⊕ inside. -/
def onlfvoc : Option NegLoadFormula → Vocab
| none => ∅
| some nlf => nlf.voc


-- @@ L252-254 verbatim
/-- The combined vocabulary of formula lists and optional loaded formulas. -/
def lfovoc (L : List (List Formula × Option NegLoadFormula)) : Vocab :=
  L.toFinset.sup (fun ⟨fs,o⟩ => fs.pdlFvoc ∪ (onlfvoc o))


-- @@ L256-258 verbatim
/-- `Finset` version of `lfovoc`. -/
def lfovocFin (L : Finset (Finset Formula × Option NegLoadFormula)) : Vocab :=
  L.sup (fun ⟨fs,o⟩ => fs.pdlFvoc ∪ (onlfvoc o))


-- @@ L260-262 verbatim
/-- The joint vocabulary occurring on both the left and the right side. -/
@[simp]
def jvoc (X : Sequent) : Vocab := (X.left).pdlFvoc ∩ (X.right).pdlFvoc


-- @@ L264-273 verbatim
lemma jvoc_sub_of_voc_sub {Y X : Sequent}
    (hl : Y.left.pdlFvoc ⊆ X.left.pdlFvoc)
    (hr : Y.right.pdlFvoc ⊆ X.right.pdlFvoc)
    : jvoc Y ⊆ jvoc X := by
  intro x x_in_jY
  simp only [jvoc, Finset.mem_inter] at x_in_jY
  specialize @hl x x_in_jY.1
  specialize @hr x x_in_jY.2
  simp only [jvoc, Finset.mem_inter]
  tauto


-- @@ L275-275 verbatim
/-! ## Formulas as elements of sequents -/


-- @@ L277-279 verbatim
@[simp]
instance (priority := high) instMembershipFormulaSequent : Membership Formula Sequent := ⟨fun X φ
  => φ ∈ X.L ∨ φ ∈ X.R⟩


-- @@ L281-282 verbatim
@[simp]
lemma Sequent.mem_def {φ : Formula} {X : Sequent} : φ ∈ X ↔ φ ∈ X.L ∨ φ ∈ X.R := Iff.rfl


-- @@ L284-287 verbatim
instance instDecidableMemFormulaSequent {φ : Formula} {X : Sequent} : Decidable (φ ∈ X) := by
  rcases X with ⟨L,R,o⟩
  unfold Membership.mem instMembershipFormulaSequent
  infer_instance


-- @@ L289-294 verbatim
instance instFintypeSubtypeMemSequent {X : Sequent} : Fintype (Subtype (fun x => x ∈ X)) := by
  rcases X with ⟨L,R,o⟩
  unfold Membership.mem instMembershipFormulaSequent
  simp only [Sequent.L, Sequent.R]
  apply Fintype.subtype (L ∪ R)
  aesop


-- @@ L296-299 verbatim
/-- Whether the specified loaded formula is the loading on either side of a sequent. -/
@[simp]
def NegLoadFormula.memSequent (X : Sequent) (nlf : NegLoadFormula) : Prop :=
  X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)


-- @@ L301-305 verbatim
instance {nlf} : Decidable (NegLoadFormula.memSequent ⟨L,R,O⟩ nlf) := by
  refine
    if h : O = some (Sum.inl nlf) then isTrue ?_
    else if h2 : O = some (Sum.inr nlf) then isTrue ?_ else isFalse ?_
  all_goals simp; tauto


-- @@ L307-309 verbatim
@[simp]
instance instMembershipNegLoadFormulaSequent :
    Membership NegLoadFormula Sequent := ⟨NegLoadFormula.memSequent⟩


-- @@ L311-315 verbatim
/-- Membership of a negated ordinary or loaded formula in a sequent. -/
def AnyNegFormula.memSequent : (X : Sequent) → (anf : AnyNegFormula) → Prop
| X, ⟨.normal φ⟩ => (~φ) ∈ X
| X, ⟨.loaded χ⟩ => instMembershipNegLoadFormulaSequent.mem X (~'χ)
  -- Note: writing `∈` does not work because the first argument of `Membership` is `outParam`.


-- @@ L317-318 verbatim
@[simp]
instance : Membership AnyNegFormula Sequent := ⟨AnyNegFormula.memSequent⟩


-- @@ L320-320 verbatim
/-! ## Closed, basic, loaded and free sequents -/


-- @@ L322-324 verbatim
/-- A sequent is *closed* iff it contains `⊥` or contains a formula and its negation. -/
def Sequent.closed (X : Sequent) : Prop :=
  ⊥ ∈ X ∨ ∃ f ∈ X, (~f) ∈ X


-- @@ L326-328 verbatim
/-- A sequent is *basic* iff it only contains basic formulas and is not closed. -/
def Sequent.basic : Sequent → Prop
  | X => (∀ f ∈ X.toFinset, f.basic) ∧ ¬ X.closed


-- @@ L330-336 verbatim
/-- A variant of `Fintype.decidableExistsFintype`, used by `instDecidableClosed`. -/
instance Fintype.decidableExistsConjFintype {α : Type u_1} {p q : α → Prop}
    [DecidablePred q] [Fintype (Subtype p)]
    : Decidable (∃ (a : α), p a ∧ q a) := by
  by_cases ∃ x : Subtype p, q x -- This uses the Fintype instance.
  · apply isTrue; aesop
  · apply isFalse; aesop


-- @@ L338-344 verbatim
instance Sequent.instDecidableClosed {X : Sequent} : Decidable (X.closed) := by
  unfold Sequent.closed
  by_cases ⊥ ∈ X
  · apply isTrue; tauto
  · by_cases ∃ f, f ∈ X ∧ (~f) ∈ X
    · apply isTrue; aesop
    · apply isFalse; aesop


-- @@ L346-361 verbatim
instance instDecidableBasic {X : Sequent} : Decidable (X.basic) := by
  by_cases X.closed
  · apply isFalse
    rcases X with ⟨L,R,o⟩
    unfold Sequent.basic
    aesop
  case neg h =>
    unfold Sequent.basic
    simp only [h, not_false_eq_true, and_true]
    by_cases ∃ f ∈ X.toFinset, f.basic ≠ true
    · apply isFalse
      push Not
      assumption
    · apply isTrue
      push Not at *
      assumption


-- @@ L363-366 verbatim
/-- Whether a sequent carries a loaded formula. -/
def Sequent.isLoaded : Sequent → Prop
| ⟨_, _, none  ⟩ => False
| ⟨_, _, some _⟩ => True


-- @@ L368-371 verbatim
/-- A loaded sequent that is not loaded on the left is loaded on the right. -/
lemma Sequent.isRight_of_not_isLeft_isLoaded {X : Sequent} (h1 : ¬ X.2.2.isLeft) (h2 : X.isLoaded) :
    X.2.2.isRight := by
  rcases X with ⟨L, R, _|(o|o)⟩ <;> simp_all [Sequent.isLoaded]


-- @@ L373-376 verbatim
instance instDecidableSequentisLoaded (X : Sequent) : Decidable (X.isLoaded) := by
  rcases X with ⟨_, _, _|_⟩
  · apply isFalse; simp_all [Sequent.isLoaded]
  · apply isTrue; simp_all [Sequent.isLoaded]


-- @@ L378-379 verbatim
/-- Whether a sequent has no loaded formula. -/
def Sequent.isFree (Γ : Sequent) : Prop := ¬ Γ.isLoaded


-- @@ L381-384 verbatim
instance instDecidableSequentisFree (X : Sequent) : Decidable (X.isFree) := by
  rcases X with ⟨_, _, _|_⟩
  · apply isTrue; simp_all [Sequent.isFree, Sequent.isLoaded]
  · apply isFalse; simp_all [Sequent.isFree, Sequent.isLoaded]


-- @@ L386-388 verbatim
@[simp]
theorem Sequent.none_isFree L R : Sequent.isFree (L, R, none) := by
  simp [Sequent.isFree, Sequent.isLoaded]


-- @@ L390-392 verbatim
@[simp]
theorem Sequent.some_not_isFree L R olf : ¬ Sequent.isFree (L, R, some olf) := by
  simp [Sequent.isFree, Sequent.isLoaded]


-- @@ L394-394 verbatim
/-! ## Semantics of sequents -/


-- @@ L396-397 verbatim
instance modelCanSemImplySequent : vDash (KripkeModel W × W) Sequent :=
  vDash.mk (fun ⟨M,w⟩ X => ∀ f ∈ X.toFinset, evaluate M w f)


-- @@ L399-400 verbatim
instance instSequentHasSat : HasSat Sequent :=
  HasSat.mk fun Δ => ∃ (W : Type) (M : KripkeModel W) (w : W), (M,w) ⊨ Δ


-- @@ L402-402 verbatim
open HasSat


-- @@ L404-408 verbatim
theorem tautImp_iff_SequentUnsat {φ ψ} {X : Sequent} :
    X = ({φ}, {~ψ}, none) → (tautology (φ ↣ ψ) ↔ ¬ satisfiable X) := by
  intro defX
  subst defX
  simp_all [Sequent.toFinset, tautology, satisfiable, vDash.SemImplies]


-- @@ L410-416 verbatim
theorem vDash_setEqTo_iff {X Y : Sequent} (h : X = Y) (M : KripkeModel W) (w : W) :
    (M,w) ⊨ X ↔ (M,w) ⊨ Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L',R',O'⟩
  simp only [vDash.SemImplies]
  cases h
  simp_all


-- @@ L418-436 verbatim
lemma Sequent.satisfiable_top_cons_right {X : Sequent} (h_left_nil : X.left = {})
    (X_unsat : ¬satisfiable X) : ¬satisfiable ({⊤} ∪ X.right) := by
  rintro ⟨W,M,w,w_⟩
  absurd X_unsat; clear X_unsat
  use W, M, w
  intro φ φ_in
  rcases X with ⟨L,R,O⟩
  simp only [left_eq, Finset.union_eq_empty] at h_left_nil
  rcases h_left_nil with ⟨L_nil, OL_nil⟩
  subst L_nil
  simp only [toFinset, Finset.empty_union, Finset.mem_union, Option.mem_toFinset, Option.mem_def,
    Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload, Sum.elim_inr] at φ_in
  rcases φ_in with _|_|⟨⟨χ⟩, ⟨O_def, def_φ⟩⟩
  · aesop
  · aesop
  · subst O_def def_φ
    unfold right at w_
    simp only [Top.top, R_eq, O_eq, Olf.R_inr] at w_
    grind


-- @@ L438-438 verbatim
/-! ## Removing loaded formulas from sequents -/


-- @@ L440-443 verbatim
/-- Remove a negated formula from the ordinary components or from the optional loading. -/
def Sequent.without : (LRO : Sequent) → (naf : AnyNegFormula) → Sequent
| ⟨L,R,O⟩, ⟨.normal f⟩  => ⟨L \ {~f}, R \ {~f}, O⟩
| ⟨L,R,O⟩, ⟨.loaded lf⟩ => if ((~'lf).memSequent ⟨L,R,O⟩) then ⟨L, R, none⟩ else ⟨L,R,O⟩


-- @@ L445-450 verbatim
@[simp]
theorem Sequent.without_normal_isFree_iff_isFree (LRO : Sequent) :
    (LRO.without (~''(.normal φ))).isFree ↔ LRO.isFree := by
  rcases LRO with ⟨L, R, O⟩
  simp [Sequent.without, isFree, isLoaded]
  aesop


-- @@ L452-459 verbatim
@[simp]
theorem Sequent.isFree_then_without_isFree (LRO : Sequent) :
    LRO.isFree → ∀ anf, (LRO.without anf).isFree := by
  intro LRO_isFree anf
  rcases LRO with ⟨L, R, _|_⟩
  · rcases anf with ⟨_|_⟩ <;> simp [without, isFree, isLoaded]
  · exfalso
    simp [isFree, isLoaded] at *


-- @@ L461-470 verbatim
lemma Sequent.without_loadBoxes_isFree_of_eq_inl {αs} {L R δs} {χ : LoadFormula} {φ : Formula}
    (h : χ = AnyFormula.loadBoxes αs φ)
    : (Sequent.without (L, R, some (Sum.inl (~'⌊⌊d :: δs⌋⌋χ)))
      (~''(AnyFormula.loadBoxes (d :: (δs ++ αs)) (AnyFormula.normal φ)))).isFree := by
  unfold Sequent.without
  simp only [AnyFormula.loadBoxes_cons, NegLoadFormula.memSequent, O_eq, Option.some.injEq,
    Sum.inl.injEq, NegLoadFormula.neg.injEq, reduceCtorEq, or_false]
  suffices (⌊⌊d :: δs⌋⌋χ) = ⌊d⌋AnyFormula.loadBoxes (δs ++ αs) (AnyFormula.normal φ) by simp_all
  rw [box_loadBoxes_append_eq_of_loaded_eq_loadBoxes]
  exact h


-- @@ L472-481 verbatim
lemma Sequent.without_loadBoxes_isFree_of_eq_inr {αs} {L R δs} {χ : LoadFormula} {φ : Formula}
    (h : χ = AnyFormula.loadBoxes αs φ)
    : (Sequent.without (L, R, some (Sum.inr (~'⌊⌊d :: δs⌋⌋χ)))
      (~''(AnyFormula.loadBoxes (d :: (δs ++ αs)) (AnyFormula.normal φ)))).isFree := by
  unfold Sequent.without
  simp only [AnyFormula.loadBoxes_cons, NegLoadFormula.memSequent, O_eq, Option.some.injEq,
    reduceCtorEq, Sum.inr.injEq, NegLoadFormula.neg.injEq, false_or]
  suffices (⌊⌊d :: δs⌋⌋χ) = ⌊d⌋AnyFormula.loadBoxes (δs ++ αs) (AnyFormula.normal φ) by simp_all
  rw [box_loadBoxes_append_eq_of_loaded_eq_loadBoxes]
  exact h


-- @@ L483-488 verbatim
lemma Sequent.without_loadMulti_isFree_of_splitLast_cons_inl {δ_β} {L R δs} {φ : Formula}
    (h : splitLast (d :: δs) = some δ_β)
    : (Sequent.without (L, R, some (Sum.inl (~'loadMulti δ_β.1 δ_β.2 φ)))
      (~''(AnyFormula.loadBoxes (d :: δs) (AnyFormula.normal φ)))).isFree := by
  rw [@loadMulti_of_splitLast_cons _ _ _ _ φ h]
  simp [Sequent.without]


-- @@ L490-495 verbatim
lemma Sequent.without_loadMulti_isFree_of_splitLast_cons_inr {δ_β} {L R δs} {φ : Formula}
    (h : splitLast (d :: δs) = some δ_β)
    : (Sequent.without (L, R, some (Sum.inr (~'loadMulti δ_β.1 δ_β.2 φ)))
      (~''(AnyFormula.loadBoxes (d :: δs) (AnyFormula.normal φ)))).isFree := by
  rw [@loadMulti_of_splitLast_cons _ _ _ _ φ h]
  simp [Sequent.without]


-- @@ L497-500 verbatim
/-- The left and right components of a sequent. -/
inductive Side
| LL : Side
| RR : Side


-- @@ L502-506 verbatim
/-- The component indicated by a sum constructor. -/
@[simp]
def sideOf : Sum α α → Side
| Sum.inl _ => .LL
| Sum.inr _ => .RR


-- @@ L508-513 verbatim
/-- Membership of a negated formula in the specified sequent component. -/
def AnyNegFormula.inSide : (anf : AnyNegFormula) → Side → (X : Sequent) → Prop
| ⟨.normal φ⟩, .LL, ⟨L, _, _⟩ => (~φ) ∈ L
| ⟨.normal φ⟩, .RR, ⟨_, R, _⟩ => (~φ) ∈ R
| ⟨.loaded χ⟩, .LL, ⟨_, _, O⟩ => O = some (Sum.inl (~'χ))
| ⟨.loaded χ⟩, .RR, ⟨_, _, O⟩ => O = some (Sum.inr (~'χ))


-- @@ L515-519 verbatim
lemma LoadFormula.in_side_of_lf_inl {X} (lf : LoadFormula)
    (O_def : X.2.2 = some (Sum.inl (~'lf))) :
    (~''(AnyFormula.loaded lf)).inSide Side.LL X := by
  rcases X with ⟨L,R,O⟩
  simp_all [AnyNegFormula.inSide]


-- @@ L521-525 verbatim
lemma LoadFormula.in_side_of_lf_inr {X} (lf : LoadFormula)
    (O_def : X.2.2 = some (Sum.inr (~'lf))) :
    (~''(AnyFormula.loaded lf)).inSide Side.RR X := by
  rcases X with ⟨L,R,O⟩
  simp_all [AnyNegFormula.inSide]


-- @@ L527-540 verbatim
lemma Sequent.isLoaded_of_negAnyFormula_loaded {α ξ side} {X : Sequent}
    (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋ξ))).inSide side X)
    : X.isLoaded := by
  unfold AnyNegFormula.inSide at negLoad_in
  rcases X with ⟨L,R,O⟩
  rcases O with _|⟨lf|lf⟩
  · cases side <;> simp_all
  all_goals
    cases side <;> simp only [Option.some.injEq, Sum.inl.injEq, reduceCtorEq,
      Sum.inr.injEq] at negLoad_in
    subst negLoad_in
    cases ξ
    all_goals
      simp_all [isLoaded]


-- @@ L542-547 verbatim
theorem Sequent.without_loaded_in_side_isFree (LRO : Sequent) ξ side :
    (~''(.loaded ξ)).inSide side LRO → (LRO.without (~''(.loaded ξ))).isFree := by
  rcases LRO with ⟨L, R, _|(OL|OR)⟩ <;> cases side
  all_goals
    simp [Sequent.without, isFree, isLoaded, AnyNegFormula.inSide]
    try aesop


-- @@ L549-552 verbatim
/-! ## Whatever formulas

A type to describe all formulas that can occur in a sequent, without losing information
about whether they are loaded or not. -/


-- @@ L554-559 verbatim
/-- Unfortunately our `AnyFormula` type does not include *negated* loaded formulas, so this is yet
another type to describe "whatever formula" can be in a sequent, without losing information. -/
inductive WhateverFormula : Type
  | any : AnyFormula → WhateverFormula
  | negLoad : NegLoadFormula → WhateverFormula
  deriving Repr, DecidableEq


-- @@ L561-561 verbatim
instance : Coe Formula WhateverFormula := ⟨.any ∘ .normal⟩

-- @@ L562-562 verbatim
instance : Coe LoadFormula WhateverFormula := ⟨.any ∘ .loaded⟩

-- @@ L563-563 verbatim
instance : Coe NegLoadFormula WhateverFormula := ⟨WhateverFormula.negLoad⟩


-- @@ L565-569 verbatim
/-- The optional loading viewed as a finset of tagged formulas. -/
def Olf.wForms : Olf → Finset WhateverFormula
  | none => {}
  | some (.inl (nφ)) => {.negLoad nφ}
  | some (.inr (nφ)) => {.negLoad nφ}


-- @@ L571-573 verbatim
/-- All ordinary and loaded formulas of a sequent, retaining their tags. -/
def Sequent.wForms : Sequent → Finset WhateverFormula
  | ⟨L,R,O⟩ => L.image Coe.coe ∪ R.image Coe.coe ∪ O.wForms


-- @@ L575-582 verbatim
lemma Sequent.mem_toFinset_iff (φ : Formula) (X : Sequent) :
    φ ∈ X.toFinset ↔
      ((.any (.normal φ) : WhateverFormula) ∈ X.wForms
      ∨ (∃ χ, χ.unload = φ ∧ (.any (.loaded χ) ∈ X.wForms))
      ∨ (∃ ψ, negUnload ψ = φ ∧ (.negLoad ψ ∈ X.wForms))) := by
  rcases X with ⟨L, R, O⟩
  rcases O with _ | (ψ | ψ) <;>
    simp [Sequent.toFinset, Sequent.wForms, Olf.wForms, Coe.coe] <;> tauto


-- @@ L584-588 verbatim
/-- A normal formula is in `X.wForms` iff it is on the left or on the right of `X`.
(Note that the `Olf` part of `X` only contributes negated *loaded* formulas.) -/
lemma Sequent.mem_wForms_normal_iff {ψ : Formula} {L R : Finset Formula} {O : Olf} :
    ((ψ : WhateverFormula) ∈ Sequent.wForms ⟨L,R,O⟩) ↔ (ψ ∈ L ∨ ψ ∈ R) := by
  rcases O with _|(nl|nl) <;> simp [Sequent.wForms, Olf.wForms, Coe.coe]


-- @@ L590-596 verbatim
/-- In a basic sequent all free diamonds are atomic. -/
lemma Sequent.isAtomic_of_basic_of_negBox_mem_wForms {X : Sequent} {α φ} (bas : X.basic)
    (h : (~⌈α⌉φ : WhateverFormula) ∈ X.wForms) : α.isAtomic := by
  rcases X with ⟨L, R, O⟩
  rw [Sequent.mem_wForms_normal_iff] at h
  have := bas.1 (~⌈α⌉φ) (by simp [Sequent.toFinset]; tauto)
  cases α <;> simp_all [Formula.basic, Program.isAtomic]


-- @@ L598-603 verbatim
/-- A negated loaded formula is in `X.wForms` iff it is the loaded formula of `X`. -/
lemma Sequent.mem_wForms_negLoad_iff {nlf : NegLoadFormula} {L R : Finset Formula} {O : Olf} :
    ((WhateverFormula.negLoad nlf) ∈ Sequent.wForms ⟨L,R,O⟩)
    ↔ (O = some (.inl nlf) ∨ O = some (.inr nlf)) := by
  rcases O with _|(nl|nl) <;>
    simp [Sequent.wForms, Olf.wForms, Coe.coe] <;> tauto


-- @@ L605-613 verbatim
/-- In a basic sequent all loaded diamonds are atomic. -/
lemma Sequent.isAtomic_of_basic_of_negLoad_mem_wForms {X : Sequent} {α} {ξ : AnyFormula}
    (bas : X.basic) (h : (WhateverFormula.negLoad (~'⌊α⌋ξ)) ∈ X.wForms) : α.isAtomic := by
  rcases X with ⟨L, R, O⟩
  rw [Sequent.mem_wForms_negLoad_iff] at h
  have h_mem : (~ (⌊α⌋ξ).unload) ∈ Sequent.toFinset ⟨L, R, O⟩ := by
    rcases h with rfl | rfl <;> simp [Sequent.toFinset]
  have := bas.1 _ h_mem
  cases ξ <;> cases α <;> simp_all [Formula.basic, Program.isAtomic, LoadFormula.unload]


-- @@ L615-615 verbatim
/-! ## Sorting Finsets of Sequents -/


-- @@ L617-621 verbatim
/-! ### Lexicographic orders on lists and pairs

NOTE: The following two definitions and their properties are general, i.e. not about PDL at all.
These could be moved to a separate file (or even might be in newer versions of Mathlib?).
-/


-- @@ L623-628 verbatim
/-- Lexicographic extension of a relation `le` to lists: shorter lists come first,
and lists of the same shape are compared element-wise from left to right. -/
def listLex {α : Type} (le : α → α → Prop) : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => le a b ∧ (a = b → listLex le as bs)


-- @@ L630-636 verbatim
instance listLex.instDecidableRel {α : Type} [DecidableEq α] (le : α → α → Prop)
    [DecidableRel le] : DecidableRel (listLex le)
  | [], _ => isTrue trivial
  | _ :: _, [] => isFalse not_false
  | a :: as, b :: bs => by
      have := listLex.instDecidableRel le as bs
      exact (inferInstance : Decidable (le a b ∧ (a = b → listLex le as bs)))


-- @@ L638-641 verbatim
lemma listLex_refl {α : Type} {le : α → α → Prop} (hrefl : ∀ a, le a a) :
    ∀ as, listLex le as as
  | [] => trivial
  | a :: as => ⟨hrefl a, fun _ => listLex_refl hrefl as⟩


-- @@ L643-652 verbatim
lemma listLex_antisymm {α : Type} {le : α → α → Prop}
    (hanti : ∀ a b, le a b → le b a → a = b) :
    ∀ as bs, listLex le as bs → listLex le bs as → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h2 => absurd h2 not_false
  | _ :: _, [], h1, _ => absurd h1 not_false
  | a :: as, b :: bs, h1, h2 => by
      have hab : a = b := hanti a b h1.1 h2.1
      subst hab
      rw [listLex_antisymm hanti as bs (h1.2 rfl) (h2.2 rfl)]


-- @@ L654-665 verbatim
lemma listLex_trans {α : Type} {le : α → α → Prop}
    (hanti : ∀ a b, le a b → le b a → a = b) (htrans : ∀ a b c, le a b → le b c → le a c) :
    ∀ as bs cs, listLex le as bs → listLex le bs cs → listLex le as cs
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, h1, _ => absurd h1 not_false
  | _ :: _, _ :: _, [], _, h2 => absurd h2 not_false
  | a :: as, b :: bs, c :: cs, h1, h2 => by
      refine ⟨htrans a b c h1.1 h2.1, fun hac => ?_⟩
      subst hac
      have hab : a = b := hanti a b h1.1 h2.1
      subst hab
      exact listLex_trans hanti htrans as bs cs (h1.2 rfl) (h2.2 rfl)


-- @@ L667-680 verbatim
lemma listLex_total {α : Type} {le : α → α → Prop} (hrefl : ∀ a, le a a)
    (htotal : ∀ a b, le a b ∨ le b a) :
    ∀ as bs, listLex le as bs ∨ listLex le bs as
  | [], _ => Or.inl trivial
  | _ :: _, [] => Or.inr trivial
  | a :: as, b :: bs => by
      by_cases hab : a = b
      · subst hab
        rcases listLex_total hrefl htotal as bs with h | h
        · exact Or.inl ⟨hrefl a, fun _ => h⟩
        · exact Or.inr ⟨hrefl a, fun _ => h⟩
      · rcases htotal a b with h | h
        · exact Or.inl ⟨h, fun he => absurd he hab⟩
        · exact Or.inr ⟨h, fun he => absurd he.symm hab⟩


-- @@ L682-684 verbatim
/-- Lexicographic combination of two relations on a product type. -/
def prodLex {α β : Type} (le1 : α → α → Prop) (le2 : β → β → Prop) : α × β → α × β → Prop
  | (a, b), (a', b') => le1 a a' ∧ (a = a' → le2 b b')


-- @@ L686-688 verbatim
instance prodLex.instDecidableRel {α β : Type} [DecidableEq α] (le1 : α → α → Prop)
    (le2 : β → β → Prop) [DecidableRel le1] [DecidableRel le2] : DecidableRel (prodLex le1 le2)
  | (a, b), (a', b') => (inferInstance : Decidable (le1 a a' ∧ (a = a' → le2 b b')))


-- @@ L690-692 verbatim
lemma prodLex_refl {α β : Type} {le1 : α → α → Prop} {le2 : β → β → Prop}
    (h1 : ∀ a, le1 a a) (h2 : ∀ b, le2 b b) : ∀ x, prodLex le1 le2 x x
  | (a, b) => ⟨h1 a, fun _ => h2 b⟩


-- @@ L694-700 verbatim
lemma prodLex_antisymm {α β : Type} {le1 : α → α → Prop} {le2 : β → β → Prop}
    (h1 : ∀ a a', le1 a a' → le1 a' a → a = a') (h2 : ∀ b b', le2 b b' → le2 b' b → b = b') :
    ∀ x y, prodLex le1 le2 x y → prodLex le1 le2 y x → x = y
  | (a, b), (a', b'), hxy, hyx => by
      have haa : a = a' := h1 a a' hxy.1 hyx.1
      subst haa
      rw [h2 b b' (hxy.2 rfl) (hyx.2 rfl)]


-- @@ L702-712 verbatim
lemma prodLex_trans {α β : Type} {le1 : α → α → Prop} {le2 : β → β → Prop}
    (hanti1 : ∀ a a', le1 a a' → le1 a' a → a = a')
    (htrans1 : ∀ a a' a'', le1 a a' → le1 a' a'' → le1 a a'')
    (htrans2 : ∀ b b' b'', le2 b b' → le2 b' b'' → le2 b b'') :
    ∀ x y z, prodLex le1 le2 x y → prodLex le1 le2 y z → prodLex le1 le2 x z
  | (a, b), (a', b'), (a'', b''), hxy, hyz => by
      refine ⟨htrans1 a a' a'' hxy.1 hyz.1, fun he => ?_⟩
      subst he
      have haa : a = a' := hanti1 a a' hxy.1 hyz.1
      subst haa
      exact htrans2 b b' b'' (hxy.2 rfl) (hyz.2 rfl)


-- @@ L714-726 verbatim
lemma prodLex_total {α β : Type} {le1 : α → α → Prop} {le2 : β → β → Prop}
    (hrefl1 : ∀ a, le1 a a) (htotal1 : ∀ a a', le1 a a' ∨ le1 a' a)
    (htotal2 : ∀ b b', le2 b b' ∨ le2 b' b) :
    ∀ x y, prodLex le1 le2 x y ∨ prodLex le1 le2 y x
  | (a, b), (a', b') => by
      by_cases haa : a = a'
      · subst haa
        rcases htotal2 b b' with h | h
        · exact Or.inl ⟨hrefl1 a, fun _ => h⟩
        · exact Or.inr ⟨hrefl1 a, fun _ => h⟩
      · rcases htotal1 a a' with h | h
        · exact Or.inl ⟨h, fun he => absurd he haa⟩
        · exact Or.inr ⟨h, fun he => absurd he.symm haa⟩


-- @@ L728-728 verbatim
/-! ### An order on loaded formulas, via a key -/


-- @@ L730-735 verbatim
/-- Every loaded formula is a non-empty sequence of loading boxes followed by a normal formula.
The `key` of a loaded formula records exactly this data, and hence determines it uniquely.
NOTE: This could be moved to `Pdl/Syntax.lean`. -/
def LoadFormula.key : LoadFormula → List Program × Formula
  | .box α (.normal φ) => ([α], φ)
  | .box α (.loaded χ) => (α :: χ.key.1, χ.key.2)


-- @@ L737-743 verbatim
/-- Inverse of `LoadFormula.key`, see `LoadFormula.ofKey_key`.
(The value for the empty list of programs is arbitrary.)
NOTE: This could be moved to `Pdl/Syntax.lean`. -/
def loadFormulaOfKey : List Program → Formula → LoadFormula
  | [], φ => LoadFormula.box (Program.test φ) (AnyFormula.normal φ)
  | [α], φ => LoadFormula.box α (AnyFormula.normal φ)
  | α :: β :: δ, φ => LoadFormula.box α (AnyFormula.loaded (loadFormulaOfKey (β :: δ) φ))


-- @@ L745-751 verbatim
/-- The key of a loaded formula determines it. -/
theorem LoadFormula.ofKey_key : ∀ χ : LoadFormula, loadFormulaOfKey χ.key.1 χ.key.2 = χ
  | .box _ (.normal _) => rfl
  | .box _ (.loaded χ) => by
      have ih := LoadFormula.ofKey_key χ
      rcases χ with ⟨β, ξ⟩
      cases ξ <;> simp_all [LoadFormula.key, loadFormulaOfKey]


-- @@ L753-754 verbatim
theorem LoadFormula.key_injective {χ χ' : LoadFormula} (h : χ.key = χ'.key) : χ = χ' := by
  rw [← LoadFormula.ofKey_key χ, ← LoadFormula.ofKey_key χ', h]


-- @@ L756-756 verbatim
/-! ### An order on sequents, via a key -/


-- @@ L758-762 verbatim
/-- Key of an `Olf`: which side (if any) is loaded, together with the key of the loaded formula. -/
def Olf.key : Olf → ℕ × (List Program × Formula)
  | none => (0, ([], Formula.bottom))
  | some (Sum.inl (~'χ)) => (1, χ.key)
  | some (Sum.inr (~'χ)) => (2, χ.key)


-- @@ L764-777 verbatim
lemma Olf.key_injective : ∀ {O O' : Olf}, O.key = O'.key → O = O'
  | none, none, _ => rfl
  | none, some (.inl (~'_)), h => by simp [Olf.key] at h
  | none, some (.inr (~'_)), h => by simp [Olf.key] at h
  | some (.inl (~'_)), none, h => by simp [Olf.key] at h
  | some (.inr (~'_)), none, h => by simp [Olf.key] at h
  | some (.inl (~'_)), some (.inr (~'_)), h => by simp [Olf.key] at h
  | some (.inr (~'_)), some (.inl (~'_)), h => by simp [Olf.key] at h
  | some (.inl (~'_)), some (.inl (~'_)), h => by
      simp only [Olf.key, Prod.mk.injEq] at h
      rw [LoadFormula.key_injective h.2]
  | some (.inr (~'_)), some (.inr (~'_)), h => by
      simp only [Olf.key, Prod.mk.injEq] at h
      rw [LoadFormula.key_injective h.2]


-- @@ L779-781 verbatim
/-- Key of a sequent: the sorted lists of the left and right side, and the key of the `Olf`. -/
def Sequent.key (X : Sequent) : List Formula × (List Formula × (ℕ × (List Program × Formula))) :=
  (X.L.pdlSort, (X.R.pdlSort, X.O.key))


-- @@ L783-787 verbatim
/-- Finsets of formulas with the same `pdlSort` are equal.
NOTE: This could be moved to `Pdl/Syntax.lean`. -/
lemma Finset.pdlSort_injective {X Y : Finset Formula} (h : X.pdlSort = Y.pdlSort) : X = Y := by
  ext φ
  rw [← Formula.mem_pdlSort, ← Formula.mem_pdlSort, h]


-- @@ L789-794 verbatim
lemma Sequent.key_injective {X Y : Sequent} (h : X.key = Y.key) : X = Y := by
  rcases X with ⟨L, R, O⟩
  rcases Y with ⟨L', R', O'⟩
  simp only [Sequent.key, Prod.mk.injEq, Sequent.L_eq, Sequent.R_eq, Sequent.O_eq] at h
  exact Prod.ext (Finset.pdlSort_injective h.1)
    (Prod.ext (Finset.pdlSort_injective h.2.1) (Olf.key_injective h.2.2))


-- @@ L796-798 verbatim
/-- Order used to compare the keys of `Olf`s. -/
def olfKeyLe : (ℕ × (List Program × Formula)) → (ℕ × (List Program × Formula)) → Prop :=
  prodLex (fun (n m : ℕ) => n ≤ m) (prodLex (listLex Program.le) Formula.le)


-- @@ L800-800 verbatim
instance : DecidableRel olfKeyLe := by unfold olfKeyLe; infer_instance


-- @@ L802-804 verbatim
lemma olfKeyLe_refl (x) : olfKeyLe x x :=
  prodLex_refl (fun _ => Nat.le_refl _)
    (prodLex_refl (listLex_refl Program.le_rfl) Formula.le_rfl) x


-- @@ L806-808 verbatim
lemma olfKeyLe_antisymm (x y) (h1 : olfKeyLe x y) (h2 : olfKeyLe y x) : x = y :=
  prodLex_antisymm (fun _ _ => Nat.le_antisymm)
    (prodLex_antisymm (listLex_antisymm Program.le_antisymm) Formula.le_antisymm) x y h1 h2


-- @@ L810-813 verbatim
lemma olfKeyLe_trans (x y z) (h1 : olfKeyLe x y) (h2 : olfKeyLe y z) : olfKeyLe x z :=
  prodLex_trans (fun _ _ => Nat.le_antisymm) (fun _ _ _ => Nat.le_trans)
    (prodLex_trans (listLex_antisymm Program.le_antisymm)
      (listLex_trans Program.le_antisymm Program.le_trans_aux) Formula.le_trans) x y z h1 h2


-- @@ L815-818 verbatim
lemma olfKeyLe_total (x y) : olfKeyLe x y ∨ olfKeyLe y x :=
  prodLex_total (fun _ => Nat.le_refl _) (fun n m => Nat.le_total n m)
    (prodLex_total (listLex_refl Program.le_rfl)
      (listLex_total Program.le_rfl Program.le_total) Formula.le_total) x y


-- @@ L820-823 verbatim
/-- Order used to compare the keys of sequents. -/
def seqKeyLe : (List Formula × (List Formula × (ℕ × (List Program × Formula)))) →
    (List Formula × (List Formula × (ℕ × (List Program × Formula)))) → Prop :=
  prodLex (listLex Formula.le) (prodLex (listLex Formula.le) olfKeyLe)


-- @@ L825-825 verbatim
instance : DecidableRel seqKeyLe := by unfold seqKeyLe; infer_instance


-- @@ L827-828 verbatim
/-- A linear order on sequents, used to define `Finset.pdlSeqSort`. -/
def Sequent.le (X Y : Sequent) : Prop := seqKeyLe X.key Y.key


-- @@ L830-831 verbatim
instance Sequent.instDecidableRelLe : DecidableRel Sequent.le :=
  fun X Y => by unfold Sequent.le; infer_instance


-- @@ L833-839 verbatim
instance Sequent.instIsTransLe : IsTrans Sequent Sequent.le :=
  ⟨fun X Y Z h1 h2 =>
    prodLex_trans (listLex_antisymm Formula.le_antisymm)
      (listLex_trans Formula.le_antisymm Formula.le_trans)
      (prodLex_trans (listLex_antisymm Formula.le_antisymm)
        (listLex_trans Formula.le_antisymm Formula.le_trans) olfKeyLe_trans)
      X.key Y.key Z.key h1 h2⟩


-- @@ L841-845 verbatim
instance Sequent.instAntisymmLe : Std.Antisymm Sequent.le :=
  ⟨fun X Y h1 h2 => Sequent.key_injective <|
    prodLex_antisymm (listLex_antisymm Formula.le_antisymm)
      (prodLex_antisymm (listLex_antisymm Formula.le_antisymm) olfKeyLe_antisymm)
      X.key Y.key h1 h2⟩


-- @@ L847-852 verbatim
instance Sequent.instTotalLe : Std.Total Sequent.le :=
  ⟨fun X Y =>
    prodLex_total (listLex_refl Formula.le_rfl) (listLex_total Formula.le_rfl Formula.le_total)
      (prodLex_total (listLex_refl Formula.le_rfl)
        (listLex_total Formula.le_rfl Formula.le_total) olfKeyLe_total)
      X.key Y.key⟩


-- @@ L854-856 verbatim
/-- Sort a finite set of sequents into a list, using `Sequent.le`. -/
def _root_.Finset.pdlSeqSort : Finset Sequent → List Sequent :=
  fun A => A.sort Sequent.le


-- @@ L858-860 verbatim
@[simp]
lemma Finset.mem_seqSort (A : Finset Sequent) : X ∈ A.pdlSeqSort ↔ X ∈ A :=
  Finset.mem_sort Sequent.le


-- @@ L862-863 verbatim
lemma Finset.seqSort_nodup (A : Finset Sequent) : A.pdlSeqSort.Nodup :=
  Finset.sort_nodup A Sequent.le


-- @@ L865-867 verbatim
@[simp]
lemma Finset.length_seqSort (A : Finset Sequent) : A.pdlSeqSort.length = A.card :=
  Finset.length_sort Sequent.le


-- @@ L869-871 verbatim
@[simp]
lemma Finset.seqSort_eq_nil_iff {A : Finset Sequent} : A.pdlSeqSort = [] ↔ A = ∅ := by
  rw [← List.length_eq_zero_iff, Finset.length_seqSort, Finset.card_eq_zero]


-- @@ L873-873 verbatim
end PDL
