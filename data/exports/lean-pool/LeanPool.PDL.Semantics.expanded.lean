/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Logic.Relation
public import Mathlib.Order.CompleteLattice.Basic

public import LeanPool.PDL.Syntax
public import LeanPool.PDL.General.ListFinset


-- @@ L22-22 verbatim
/-! # Semantics (Section 2.2) -/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace PDL


-- @@ L28-28 verbatim
/-! ## Models and Truth -/


-- @@ L30-35 verbatim
/-- Kripke Models, also known as Labelled Transition Systems -/
structure KripkeModel (W : Type) : Type where
  /-- The truth assignment for atomic propositions at each world. -/
  val : W → Nat → Prop
  /-- The accessibility relation for each atomic program. -/
  Rel : Nat → W → W → Prop


-- @@ L37-43 verbatim
/-- The syntactic measure used to define formula evaluation and program relations mutually. -/
@[simp]
def complexityOfQuery {W : Type} :
    PSum (Σ' (_ : KripkeModel W) (_ : W), Formula)
         (Σ' (_ : KripkeModel W) (_ : Program) (_ : W), W) → ℕ
  | PSum.inl val => lengthOfFormula val.snd.snd
  | PSum.inr val => lengthOfProgram val.snd.fst


-- @@ L45-64 verbatim
mutual
  /-- Truth of a PDL formula at a world in a Kripke model. -/
  @[simp]
  def evaluate {W : Type} : KripkeModel W → W → Formula → Prop
    | _, _, ⊥ => False
    | M, w, ·c => M.val w c
    | M, w, ~φ => Not (evaluate M w φ)
    | M, w, φ⋀ψ => evaluate M w φ ∧ evaluate M w ψ
    | M, w, ⌈α⌉ φ => ∀ v : W, relate M α w v → evaluate M v φ
  /-- The binary relation denoted by a PDL program in a Kripke model. -/
  @[simp]
  def relate {W : Type} : KripkeModel W → Program → W → W → Prop
    | M, ·c, w, v => M.Rel c w v
    | M, α;'β, w, v => ∃ y, relate M α w y ∧ relate M β y v
    | M, α⋓β, w, v => relate M α w v ∨ relate M β w v
    | M, ∗α, w, v => Relation.ReflTransGen (relate M α) w v
    | M, ?'φ, w, v => w = v ∧ evaluate M w φ
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.

-- @@ L65-65 verbatim
end PDL


-- @@ L67-67 verbatim
namespace PDL


-- @@ L69-72 verbatim
theorem evalDis {W M f g} {w : W} : evaluate M w (f⋁g) ↔ evaluate M w f ∨ evaluate M w g :=
  by
  simp
  tauto


-- @@ L74-77 verbatim
/-- Evaluate a formula at a pointed Kripke model. -/
@[simp]
def evaluatePoint {W : Type} : KripkeModel W × W → Formula → Prop
  | (M, w), ϕ => evaluate M w ϕ


-- @@ L79-81 verbatim
/-- Validity of a formula at every world of every Kripke model. -/
def tautology (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, evaluate M w φ


-- @@ L83-85 verbatim
/-- Falsity of a formula at every world of every Kripke model. -/
def contradiction (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, ¬evaluate M w φ


-- @@ L87-89 verbatim
/-! ## Satisfiability -/

-- MB: Definition 5, page 9

-- @@ L90-93 verbatim
/-- Types equipped with a notion of semantic satisfiability. -/
class HasSat (α : Type) where
  /-- Existence of a semantic model for an object. -/
  satisfiable : α → Prop

-- @@ L94-94 verbatim
open HasSat

-- @@ L95-97 verbatim
@[simp]
instance formHasSat : HasSat Formula :=
  HasSat.mk fun ϕ => ∃ (W : _) (M : KripkeModel W) (w : _), evaluate M w ϕ

-- @@ L98-100 verbatim
@[simp]
instance setHasSat : HasSat (Finset Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, evaluate M w φ

-- @@ L101-103 verbatim
@[simp]
instance listHasSat : HasSat (List Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, evaluate M w φ


-- @@ L105-108 verbatim
/-- Satisfiability of a list only depends on which formulas are in it. -/
lemma sat_congr_of_mem_iff {L L' : List Formula} (h : ∀ f, f ∈ L ↔ f ∈ L') :
    satisfiable L ↔ satisfiable L' := by
  constructor <;> rintro ⟨W, M, w, hw⟩ <;> exact ⟨W, M, w, fun f hf => hw f (by simp_all)⟩


-- @@ L110-110 verbatim
/-! ## Semantic implication and vDash notation -/


-- @@ L112-115 verbatim
/-- Semantic consequence between finite sets of formulas. -/
def semImpliesSets (X : Finset Formula) (Y : Finset Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluate M w φ) → ∀ ψ ∈ Y, evaluate M w ψ


-- @@ L117-120 verbatim
/-- Semantic consequence between lists of formulas. -/
def semImpliesLists (X : List Formula) (Y : List Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluate M w φ) → ∀ ψ ∈ Y, evaluate M w ψ


-- @@ L122-124 verbatim
/-- Agreement of two formulas at every pointed Kripke model. -/
def semEquiv (φ ψ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, evaluate M w φ ↔ evaluate M w ψ


-- @@ L126-128 verbatim
/-- Agreement of two program relations in every Kripke model. -/
def relEquiv (α β : Program) :=
  ∀ (W : Type) (M : KripkeModel W) v w, relate M α v w ↔ relate M β v w


-- @@ L130-135 verbatim
theorem notsatisfnotThenTaut : ∀ φ, ¬ satisfiable (~φ) → tautology φ :=
  by
  intro phi
  unfold satisfiable
  unfold tautology
  simp


-- @@ L137-139 verbatim
theorem subsetSat {M : KripkeModel W} {w : W} {X Y : List Formula} :
    (∀ φ ∈ X, evaluate M w φ) → Y ⊆ X → ∀ φ ∈ Y, evaluate M w φ :=
  by aesop


-- @@ L141-143 verbatim
theorem semEquiv.refl : Std.Refl semEquiv := by
  constructor
  tauto


-- @@ L145-149 verbatim
theorem semEquiv.symm : Std.Symm semEquiv := by
  constructor
  intro φ1 φ2 hyp W M w
  specialize hyp W M w
  tauto


-- @@ L151-156 verbatim
theorem semEquiv.trans : IsTrans Formula semEquiv := by
  constructor
  intro _ _ _ hyp1 hyp2 W M w
  specialize hyp1 W M w
  specialize hyp2 W M w
  tauto


-- @@ L158-160 verbatim
theorem relEquiv.refl : Std.Refl relEquiv := by
  constructor
  tauto


-- @@ L162-166 verbatim
theorem relEquiv.symm : Std.Symm relEquiv := by
  constructor
  intro α1 α2 hyp W M w v
  specialize hyp W M w v
  tauto


-- @@ L168-173 verbatim
theorem relEquiv.trans : IsTrans Program relEquiv := by
  constructor
  intro _ _ _ hyp1 hyp2 W M w v
  specialize hyp1 W M w v
  specialize hyp2 W M w v
  tauto


-- @@ L175-178 verbatim
/-- An overloaded semantic satisfaction or consequence relation. -/
class vDash (α : Type) (β : Type) where
  /-- The semantic relation for the two specified types. -/
  SemImplies : α → β → Prop


-- @@ L180-180 verbatim
open vDash


-- @@ L182-183 verbatim
instance modelCanSemImplyForm {W : Type} : vDash (KripkeModel W × W) Formula :=
  vDash.mk (@evaluatePoint W)

-- @@ L184-186 verbatim
@[simp]
instance modelCanSemImplyList {W : Type} : vDash (KripkeModel W × W) (List Formula) :=
  vDash.mk (fun ⟨M,w⟩ fs => ∀ f ∈ fs, @evaluate W M w f)

-- @@ L187-190 verbatim
instance modelCanSemImplyAnyFormula {W : Type} : vDash (KripkeModel W × W) AnyFormula :=
  ⟨fun (M,w) ξ => match ξ with
    | (AnyFormula.normal φ) => evaluate M w φ
    | .loaded χ => evaluate M w χ.unload⟩

-- @@ L191-192 verbatim
instance modelCanSemImplyAnyNegFormula {W : Type} : vDash (KripkeModel W × W) AnyNegFormula :=
  vDash.mk (fun ⟨M,w⟩ ⟨ξ⟩ => ¬ SemImplies (M, w) ξ)

-- @@ L193-193 verbatim
instance setCanSemImplySet : vDash (List Formula) (List Formula) := vDash.mk semImpliesLists

-- @@ L194-195 verbatim
instance setCanSemImplyForm : vDash (List Formula) Formula :=
  vDash.mk fun X ψ => semImpliesLists X [ψ]

-- @@ L196-197 verbatim
instance formCanSemImplySet : vDash Formula (List Formula) :=
  vDash.mk fun φ X => semImpliesLists [φ] X

-- @@ L198-199 verbatim
instance formCanSemImplyForm : vDash Formula Formula :=
  vDash.mk fun φ ψ => semImpliesLists [φ] [ψ]


-- @@ L201-202 verbatim
/-- Semantic satisfaction or consequence. -/
scoped infixl:40 " ⊨ " => SemImplies


-- @@ L204-205 verbatim
/-- Semantic equivalence of formulas. -/
scoped infixl:40 " ≡ " => semEquiv


-- @@ L207-208 verbatim
/-- Semantic equivalence of program relations. -/
scoped infixl:40 " ≡ᵣ " => relEquiv


-- @@ L210-211 verbatim
/-- Failure of semantic satisfaction or consequence. -/
scoped infixl:40 " ⊭ " => fun a b => ¬a⊨b


-- @@ L213-217 verbatim
@[simp]
theorem singletonSat_iff_sat : ∀ φ, satisfiable ({φ} : Finset Formula) ↔ satisfiable φ :=
  by
  intro phi
  simp [satisfiable]


-- @@ L219-226 verbatim
@[simp]
theorem vDashSingleton_iff_vDash_formula {M : KripkeModel W} {w : W} :
    ∀ φ, (M, w) ⊨ ([φ] : List Formula) ↔ evaluate M w φ :=
  by
  intro phi
  simp [SemImplies]

-- useful lemmas to connect different ⊨ cases

-- @@ L227-237 verbatim
theorem forms_to_lists {φ ψ : Formula} : φ⊨ψ → ([φ] : List Formula)⊨([ψ] : List Formula) :=
  by
  intro impTaut W M w lhs ψ psi_in_psi
  specialize impTaut W M w
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at psi_in_psi lhs
  rw [psi_in_psi]
  -- needed even though no ψ_1 in goal here?!
  apply impTaut
  · rw [←vDashSingleton_iff_vDash_formula φ] at lhs
    tauto
  · aesop


-- @@ L239-247 verbatim
/-- The Local Deduction Theorem. -/
theorem deduction (X : List Formula) (ψ φ : Formula) :
    X ++ [ψ] ⊨ φ ↔ (X ⊨ ψ ↣ φ) := by
  constructor
  · intro Xφ_then_ψ W M w w_X
    aesop
  · intro X_ W M w w_X
    specialize X_ W M w
    aesop


-- @@ L249-266 verbatim
theorem notSat_iff_semImplies (X : List Formula) (φ : Formula) :
    ¬ satisfiable (X ∪ [~φ]) ↔ X ⊨ ([φ] : List Formula) := by
  constructor
  · simp only [satisfiable, not_exists, not_forall, exists_prop]
    intro nSat W M w satX
    specialize nSat W M w
    rcases nSat with ⟨φ, phi_in, not_phi⟩
    aesop
  · intro X_φ
    by_contra hyp
    simp only [satisfiable] at hyp
    rcases hyp with ⟨W, M, w, w_⟩
    specialize X_φ W M w
    cases X
    · simp_all
    · have := w_ (~φ)
      simp at *
      simp_all


-- @@ L268-274 verbatim
theorem equivSat (φ ψ : Formula) {M : KripkeModel W} {w : W} :
    φ ≡ ψ → (M, w) ⊨ φ → (M, w) ⊨ ψ :=
  by
    intro φ_eq_ψ evalφ
    have : evaluate M w φ := by tauto
    rw [φ_eq_ψ] at this
    tauto


-- @@ L276-289 verbatim
theorem equiv_iff (φ ψ : Formula) (φ_eq_ψ : φ ≡ ψ) :
    ∀ {W} {M : KripkeModel W} {w : W},
    (M, w) ⊨ φ ↔ (M, w) ⊨ ψ :=
  by
    intro W M w
    constructor
    · intro
      have : evaluate M w φ := by tauto
      rw [φ_eq_ψ] at this
      tauto
    · intro
      have : evaluate M w ψ := by tauto
      rw [← φ_eq_ψ] at this
      tauto


-- @@ L291-294 verbatim
theorem tautImp_iff_comboNotUnsat {φ ψ : Formula} :
    tautology (φ ↣ ψ) ↔ ¬ satisfiable ([φ, ~ψ]) :=
  by
  simp [tautology, satisfiable, evaluate]


-- @@ L296-318 verbatim
theorem relate_steps_append {as bs} : ∀ x z, relate M (Program.steps (as ++ bs)) x z  ↔
  ∃ y, relate M (Program.steps as) x y ∧ relate M (Program.steps bs) y z :=
  by
  induction as
  · simp
  case cons a as IH =>
    intro x z
    constructor
    · intro lhs
      simp only [List.cons_append, Program.steps.eq_2, relate, Program.steps] at *
      rcases lhs with ⟨y, x_a_y, y_asbs_z⟩
      rw [IH] at y_asbs_z
      rcases y_asbs_z with ⟨y', y_as_ys', ys'_bs_z⟩
      use y'
      constructor
      · use y
      · exact ys'_bs_z
    · intro rhs
      simp only [Program.steps, relate, List.cons_append] at *
      rcases rhs with ⟨y, ⟨y', x_a_y', y'_as_y⟩, bla⟩
      use y'
      rw [IH y' z]
      tauto


-- @@ L320-339 verbatim
theorem rel_steps_last {as} : ∀ v w,
  relate M (Program.steps (as ++ [a])) v w ↔
    ∃ mid, relate M (Program.steps as) v mid ∧ relate M a mid w :=
  by
  induction as
  case nil =>
    simp at *
  case cons a2 as IH =>
    intro s t
    simp only [List.cons_append, Program.steps.eq_2, relate, Program.steps] at *
    constructor
    · intro lhs
      rcases lhs with ⟨next, s_a2_next, next_asa_t⟩
      rw [IH] at next_asa_t
      tauto
    · intro rhs
      rcases rhs with ⟨m,⟨y,yP,yP2⟩,mP⟩
      use y
      rw [IH]
      tauto


-- @@ L341-345 verbatim
/-- Relational composition of a list of programs, with equality for the empty list. -/
def relateSeq {W} (M : KripkeModel W) (δ : List Program) (w v : W) : Prop :=
  match δ with
  | [] => w = v
  | (α::as) => ∃ u, relate M α w u ∧ relateSeq M as u v


-- @@ L347-350 verbatim
@[simp]
theorem relateSeq_nil {M : KripkeModel W} {w v : W} :
    relateSeq M [] w v ↔ w = v := by
  simp [relateSeq]


-- @@ L352-355 verbatim
@[simp]
theorem relateSeq_singleton {M : KripkeModel W} {α : Program} {w v : W} :
    relateSeq M [α] w v ↔ relate M α w v := by
  simp [relateSeq]


-- @@ L357-358 verbatim
theorem relateSeq_cons {M : KripkeModel W} {d : Program} {δ : List Program} {w v : W} :
    relateSeq M (d :: δ) w v ↔ ∃ u, relate M d w u ∧ relateSeq M δ u v := iff_of_eq rfl


-- @@ L360-366 verbatim
theorem relateSeq_append {M : KripkeModel W} {l1 l2 : List Program} {w v : W} :
    relateSeq M (l1 ++ l2) w v ↔ ∃ u, relateSeq M l1 w u ∧ relateSeq M l2 u v := by
  induction l1 generalizing w v
  · simp [relateSeq]
  case cons l l1 IH =>
    simp [relateSeq]
    aesop


-- @@ L368-370 verbatim
lemma relate_steps_iff_relateSeq (M : KripkeModel W) (δ : List Program) (w v : W) :
    relate M (Program.steps δ) w v ↔ relateSeq M δ w v := by
  induction δ generalizing w v <;> simp_all [relateSeq]


-- @@ L372-443 verbatim
theorem relateSeq_iff_exists_Vector (M : KripkeModel W) (δ : List Program) (w v : W) :
  relateSeq M δ w v ↔
   ∃ (ws : List.Vector W (δ.length).succ),
      w = ws.head ∧ v = ws.last ∧ ∀ i, relate M (δ.get i) (ws.get i.castSucc) (ws.get i.succ)
    := by
  induction δ generalizing w
  · simp only [relateSeq_nil, List.length_nil, Nat.succ_eq_add_one, Nat.reduceAdd,
    List.get_eq_getElem, IsEmpty.forall_iff, and_true]
    constructor <;> intro h
    · use ⟨[w], by simp⟩
      aesop
    · rcases h with ⟨⟨ws, ws_len_eq_1⟩ , w_def, v_def⟩
      rw [List.length_eq_one_iff] at ws_len_eq_1
      rcases ws_len_eq_1 with ⟨x, ws_def⟩
      aesop
  case cons d δ IH =>
    simp only [relateSeq_cons, List.length_cons, Nat.succ_eq_add_one, List.get_eq_getElem]
    constructor <;> intro h
    · rcases h with ⟨u, w_u, u_v⟩
      rw [IH] at u_v
      clear IH
      rcases u_v with ⟨ws, u_def, v_def, claim⟩
      refine ⟨w ::ᵥ ws, ?_, ?_, ?_⟩
      · simp
      · rw [v_def]
        have := @List.Vector.tail_last_eq_last _ _ (w ::ᵥ ws)
        grind
      · apply Fin.cases
        · simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
            Fin.castSucc_zero, Fin.succ_zero_eq_one]
          convert w_u
          · subst u_def
            simp [List.Vector.get]
          · rcases ws with ⟨ws, ws_len⟩
            have := List.exists_of_length_succ _ ws_len
            aesop
        · aesop
    · rcases h with ⟨wws, w_def, v_def, claim⟩
      let u := wws[1]
      use wws[1]
      constructor
      · have := claim 0
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero, Fin.castSucc_zero,
          List.Vector.get_zero, Fin.succ_zero_eq_one] at this
        convert this
        rfl
      · specialize IH u
        rw [IH]
        clear IH
        refine ⟨wws.tail, ?_ , ?_ , ?_ ⟩
        · unfold u
          rcases wws with ⟨wws, wws_len⟩
          rcases List.exists_of_length_succ _ wws_len with ⟨x, t, wws_def⟩
          subst wws_def
          have := List.exists_of_length_succ t
            (by simp at wws_len; assumption : t.length = δ.length + 1)
          rcases this with ⟨y, tt, t_def⟩
          subst t_def
          aesop
        · rw [v_def]
          -- copied from previous case
          rcases wws with ⟨wws, wws_len⟩
          rcases List.exists_of_length_succ _ wws_len with ⟨x, t, wws_def⟩
          subst wws_def
          have := List.exists_of_length_succ t
            (by simp at wws_len; assumption : t.length = δ.length + 1)
          rcases this with ⟨y, tt, t_def⟩
          subst t_def
          aesop
        · intro i
          specialize claim i.succ
          aesop


-- @@ L445-458 verbatim
/-- Relating along `Program.unions L` means relating along one of the programs in `L`. -/
lemma relate_unions {W} {M : KripkeModel W} : ∀ (L : List Program) (v u : W),
    relate M (Program.unions L) v u ↔ ∃ a ∈ L, relate M a v u
  | [], v, u => by simp [Program.unions, relate, evaluate]
  | [a], v, u => by simp [Program.unions]
  | a :: b :: L, v, u => by
      simp only [Program.unions, relate, relate_unions (b :: L) v u, List.mem_cons]
      constructor
      · rintro (h | ⟨c, hc, h⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨c, Or.inr hc, h⟩
      · rintro ⟨c, rfl | hc, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, hc, h⟩


-- @@ L460-478 verbatim
theorem evalBoxes (δ : List Program) φ :
    evaluate M w (⌈⌈δ⌉⌉φ) ↔ (∀ v, relateSeq M δ w v → evaluate M v φ) := by
  induction δ generalizing w
  · simp [relateSeq]
  case cons α δ IH =>
    simp only [Formula.boxes_cons]
    constructor
    · intro lhs v v_αδ_w
      simp only [evaluate, relateSeq] at *
      rcases v_αδ_w with ⟨u, w_α_u, u_δ_v⟩
      specialize @IH u
      refine IH.1 ?_ v u_δ_v
      simp_all only [true_iff]
    · intro rhs u w_α_u
      apply IH.2
      intro v u_δ_v
      apply rhs
      simp only [relateSeq]
      use u


-- @@ L480-483 verbatim
@[simp]
theorem evaluate_unload_box {af} :
    evaluate M w (⌊α⌋af).unload ↔ ∀ v, relate M α w v → (M,v) ⊨ af := by
  cases af <;> simp_all [SemImplies]


-- @@ L485-490 verbatim
theorem truthImply_then_satImply (X Y : List Formula) : X ⊨ Y → satisfiable X → satisfiable Y :=
  by
  intro X_Y satX
  rcases satX with ⟨W,M,w,v_X⟩
  specialize X_Y W M w v_X
  use W, M, w


-- @@ L492-504 verbatim
/-- Semantic induction rule for the Kleene star operator. -/
theorem stepToStar : φ ⊨ (⌈α⌉φ) ⋀ ψ  →  φ ⊨ (⌈∗α⌉ψ) := by
  intro hyp W M w w_φ
  specialize hyp W M
  have : ∀ v, relate M (∗α) w v → evaluate M v φ := by
    intro v w_sta_v
    simp_all only [List.mem_singleton, forall_eq, evaluate, relate]
    induction w_sta_v
    case refl =>
      simp_all
    case tail s t _ s_α_t s_φ =>
      exact (hyp s s_φ).1 t s_α_t
  simp_all


-- @@ L506-530 verbatim
theorem SemImplyAnyNegFormula_loadBoxes_iff {M : KripkeModel W} {ξ : AnyFormula} :
    (M, w) ⊨ ~''(ξ.loadBoxes δ) ↔ ∃ v, relateSeq M δ w v ∧ (M, v) ⊨ ~''ξ := by
  induction δ generalizing w
  · simp
  case cons d δ IH =>
    unfold modelCanSemImplyAnyNegFormula at IH
    simp only at IH
    unfold SemImplies modelCanSemImplyAnyNegFormula modelCanSemImplyAnyFormula
    simp only [AnyFormula.loadBoxes_cons, evaluate_unload_box, not_forall]
    constructor
    · rintro ⟨u, w_u, u_⟩
      rw [IH] at u_
      rcases u_ with ⟨z, u_z, z_⟩
      use z
      simp only [relateSeq_cons]
      constructor
      · use u
      · exact z_
    · rintro ⟨v, w_v, v_⟩
      simp only [relateSeq_cons] at w_v
      rcases w_v with ⟨u, w_u, u_v⟩
      refine ⟨u, w_u, ?_⟩
      rw [IH]
      use v
      tauto


-- @@ L532-532 verbatim
end PDL
