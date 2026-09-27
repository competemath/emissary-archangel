/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.Calculus
public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Syntax.Rew
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental


-- @@ L12-12 verbatim
/-! # Calculus -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace LO


-- @@ L18-18 verbatim
namespace FirstOrder


-- @@ L20-21 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Sequent (L : Language) := List (SyntacticFormula L)


-- @@ L23-23 verbatim
open Semiformula

-- @@ L24-24 verbatim
variable {L : Language} {T : Theory L}


-- @@ L26-36 expanded
/-- Imported declaration from the Incompleteness formalization. -/
inductive _root_.LO.FirstOrder.Derivation (T : Theory L) : Sequent L → Type _
  | axL (Γ) {k} (r : L.Rel k) (v) : Derivation T (rel r v :: nrel r v :: Γ)
  | verum (Γ) : Derivation T (⊤ :: Γ)
  | or {Γ φ ψ} : Derivation T (φ :: ψ :: Γ) → Derivation T (Vee.vee φ ψ :: Γ)
  |
  and {Γ φ ψ} : Derivation T (φ :: Γ) → Derivation T (ψ :: Γ) → Derivation T (Wedge.wedge φ ψ :: Γ)
  | all {Γ φ} : Derivation T (Rewriting.free φ :: Γ⁺) → Derivation T ((UnivQuantifier.univ φ) :: Γ)
  |
  ex {Γ φ} (t) :
    Derivation T (LO.FirstOrder.Rewriting.substitute φ ![t] :: Γ) →
      Derivation T ((ExQuantifier.ex φ) :: Γ)
  | wk {Γ Δ} : Derivation T Δ → Δ ⊆ Γ → Derivation T Γ
  | cut {Γ φ} : Derivation T (φ :: Γ) → Derivation T (Tilde.tilde φ :: Γ) → Derivation T Γ
  | root {φ} : φ ∈ T → Derivation T [φ]


-- @@ L38-38 verbatim
instance : OneSided (SyntacticFormula L) (Theory L) := ⟨Derivation⟩


-- @@ L40-41 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Derivation₀ (Γ : Sequent L) : Type _ :=
  OneSided.Derivation (∅ : Theory L) Γ


-- @@ L43-44 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Derivable₀ (Γ : Sequent L) : Prop :=
  OneSided.Derivable (∅ : Theory L) Γ


-- @@ L46-47 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:45 "⊢ᵀ " => Derivation₀


-- @@ L49-50 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:45 "⊢ᵀ! " => Derivable₀


-- @@ L52-52 verbatim
namespace Derivation


-- @@ L54-54 verbatim
variable {T U : Theory L} {Δ Δ₁ Δ₂ Γ : Sequent L} {φ ψ r : SyntacticFormula L}


-- @@ L56-56 verbatim
open Rewriting LawfulSyntacticRewriting


-- @@ L58-68 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.length {Δ : Sequent L} : OneSided.Derivation T Δ → ℕ
  | axL _ _ _ => 0
  | verum _ => 0
  | or d => d.length.succ
  | and dp dq => (max (length dp) (length dq)).succ
  | all d => d.length.succ
  | ex _ d => d.length.succ
  | wk d _ => d.length.succ
  | cut dp dn => (max (length dp) (length dn)).succ
  | root _ => 0


-- @@ L70-70 verbatim
section «lp_section_1»


-- @@ L72-73 verbatim
@[simp] lemma _root_.LO.FirstOrder.Derivation.length_axL {k} {r : L.Rel k} {v} :
  length (axL (T := T) Δ r v) = 0 := rfl


-- @@ L75-75 verbatim
@[simp] lemma _root_.LO.FirstOrder.Derivation.length_verum : length (verum (T := T) Δ) = 0 := rfl


-- @@ L77-78 expanded
@[simp]
lemma _root_.LO.FirstOrder.Derivation.length_and {φ ψ} (dp : OneSided.Derivation T (φ :: Δ))
    (dq : OneSided.Derivation T (ψ :: Δ)) :
    length (and dp dq) = (max (length dp) (length dq)).succ :=
  rfl


-- @@ L80-81 expanded
@[simp]
lemma _root_.LO.FirstOrder.Derivation.length_or {φ ψ} (d : OneSided.Derivation T (φ :: ψ :: Δ)) :
    length (or d) = d.length.succ :=
  rfl


-- @@ L83-84 expanded
@[simp]
lemma _root_.LO.FirstOrder.Derivation.length_all {φ}
    (d : OneSided.Derivation T (Rewriting.free φ :: Δ⁺)) : length (all d) = d.length.succ :=
  rfl


-- @@ L86-87 expanded
@[simp]
lemma _root_.LO.FirstOrder.Derivation.length_ex {t} {φ}
    (d : OneSided.Derivation T (LO.FirstOrder.Rewriting.substitute φ ![t] :: Δ)) :
    length (ex t d) = d.length.succ :=
  rfl


-- @@ L89-90 expanded
@[simp]
lemma _root_.LO.FirstOrder.Derivation.length_wk (d : OneSided.Derivation T Δ) (h : Δ ⊆ Γ) :
    length (wk d h) = d.length.succ :=
  rfl


-- @@ L92-93 expanded
@[simp]
lemma _root_.LO.FirstOrder.Derivation.length_cut {φ} (dp : OneSided.Derivation T (φ :: Δ))
    (dn : OneSided.Derivation T ((Tilde.tilde φ) :: Δ)) :
    length (cut dp dn) = (max (length dp) (length dn)).succ :=
  rfl


-- @@ L95-95 verbatim
end «lp_section_1»


-- @@ L97-97 verbatim
section «lp_section_2»

-- @@ L98-98 verbatim
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)]


-- @@ L100-139 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def _root_.LO.FirstOrder.Derivation.repr {Δ : Sequent L} :
    OneSided.Derivation T Δ → String
  | axL Δ _ _ =>
    "\\AxiomC{}\n" ++ "\\RightLabel{\\scriptsize(axL)}\n" ++ "\\UnaryInfC{$" ++ reprStr Δ ++
      "$}\n\n"
  | verum Δ =>
    "\\AxiomC{}\n" ++ "\\RightLabel{\\scriptsize($\\top$)}\n" ++ "\\UnaryInfC{$" ++ reprStr Δ ++
      "$}\n\n"
  | @or _ _ Δ φ ψ d =>
    Derivation.repr d ++ "\\RightLabel{\\scriptsize($\\lor$)}\n" ++ "\\UnaryInfC{$" ++
        reprStr ((Vee.vee φ ψ) :: Δ) ++
      "$}\n\n"
  | @and _ _ Δ φ ψ dp dq =>
    Derivation.repr dp ++ Derivation.repr dq ++ "\\RightLabel{\\scriptsize($\\land$)}\n" ++
          "\\BinaryInfC{$" ++
        reprStr ((Wedge.wedge φ ψ) :: Δ) ++
      "$}\n\n"
  | @all _ _ Δ φ d =>
    Derivation.repr d ++ "\\RightLabel{\\scriptsize($\\forall$)}\n" ++ "\\UnaryInfC{$" ++
        reprStr ((UnivQuantifier.univ φ) :: Δ) ++
      "$}\n\n"
  | @ex _ _ Δ φ _ d =>
    Derivation.repr d ++ "\\RightLabel{\\scriptsize($\\exists$)}\n" ++ "\\UnaryInfC{$" ++
        reprStr ((ExQuantifier.ex φ) :: Δ) ++
      "$}\n\n"
  | @wk _ _ _ Γ d _ =>
    Derivation.repr d ++ "\\RightLabel{\\scriptsize(wk)}\n" ++ "\\UnaryInfC{$" ++ reprStr Γ ++
      "$}\n\n"
  | @cut _ _ Δ _ dp dn =>
    Derivation.repr dp ++ Derivation.repr dn ++ "\\RightLabel{\\scriptsize(Cut)}\n" ++
          "\\BinaryInfC{$" ++
        reprStr Δ ++
      "$}\n\n"
  | root (φ := φ) _ =>
    "\\AxiomC{}\n" ++ "\\RightLabel{\\scriptsize(ROOT)}\n" ++ "\\UnaryInfC{$" ++ reprStr φ ++
          ", " ++
        reprStr (Tilde.tilde φ) ++
      "$}\n\n"


-- @@ L141-141 expanded
instance : Repr (OneSided.Derivation T Δ) where reprPrec d _ := Derivation.repr d


-- @@ L143-143 verbatim
end «lp_section_2»


-- @@ L145-146 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.FirstOrder.Derivation.cast (d : OneSided.Derivation T Δ) (e : Δ = Γ) :
    OneSided.Derivation T Γ :=
  e ▸ d


-- @@ L148-149 expanded
lemma _root_.LO.FirstOrder.Derivation.cast_eq (d : OneSided.Derivation T Δ) (e : Δ = Δ) :
    Derivation.cast d e = d :=
  rfl


-- @@ L151-152 expanded
@[simp 1100]
lemma _root_.LO.FirstOrder.Derivation.length_cast (d : OneSided.Derivation T Δ) (e : Δ = Γ) :
    length (Derivation.cast d e) = length d := by rcases e with rfl; simp [Derivation.cast]


-- @@ L154-155 expanded
lemma _root_.LO.FirstOrder.Derivation.length_cast' (d : OneSided.Derivation T Δ) (e : Δ = Γ) :
    length (e ▸ d) = length d := by rcases e with rfl; simp []


-- @@ L157-157 verbatim
alias weakening := wk


-- @@ L159-160 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.verum' (h : ⊤ ∈ Δ) : OneSided.Derivation T Δ :=
  (verum Δ).wk (by simp [h])


-- @@ L162-165 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.axL' {k} (r : L.Rel k) (v) (h : Semiformula.rel r v ∈ Δ)
    (hn : Semiformula.nrel r v ∈ Δ) : OneSided.Derivation T Δ :=
  (axL Δ r v).wk (by simp [h, hn])


-- @@ L167-169 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.all' {φ} (h : UnivQuantifier.univ φ ∈ Δ)
    (d : OneSided.Derivation T (Rewriting.free φ :: Δ⁺)) : OneSided.Derivation T Δ :=
  d.all.wk (by simp [h])


-- @@ L171-173 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.ex' {φ} (h : ExQuantifier.ex φ ∈ Δ) (t)
    (d : OneSided.Derivation T (LO.FirstOrder.Rewriting.substitute φ ![t] :: Δ)) :
    OneSided.Derivation T Δ :=
  (d.ex t).wk (by simp [h])


-- @@ L175-176 verbatim
lemma _root_.LO.FirstOrder.Derivation.ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt <| Nat.lt_succ_of_le <| by simp


-- @@ L178-179 verbatim
@[simp 1100] lemma _root_.LO.FirstOrder.Derivation.ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt <| Nat.lt_succ_of_le <| by simp


-- @@ L181-218 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.em {Δ : Sequent L} :
    {φ : SyntacticFormula L} → (hpos : φ ∈ Δ) → (hneg : Tilde.tilde φ ∈ Δ) → OneSided.Derivation T Δ
  | ⊤, hpos, hneg => verum' hpos
  | ⊥, hpos, hneg => verum' hneg
  | .rel R v, hpos, hneg => axL' R v hpos hneg
  | .nrel R v, hpos, hneg => axL' R v hneg hpos
  | Wedge.wedge φ ψ, hpos, hneg =>
    have ihp : OneSided.Derivation T (φ :: Tilde.tilde φ :: Tilde.tilde ψ :: Δ) :=
      em (φ := φ) (by simp) (by simp)
    have ihq : OneSided.Derivation T (ψ :: Tilde.tilde φ :: Tilde.tilde ψ :: Δ) :=
      em (φ := ψ) (by simp) (by simp)
    have : OneSided.Derivation T (Tilde.tilde φ :: Tilde.tilde ψ :: Δ) :=
      (ihp.and ihq).wk (by simp [hpos])
    this.or.wk (by simpa using hneg)
  | Vee.vee φ ψ, hpos, hneg =>
    have ihp : OneSided.Derivation T (Tilde.tilde φ :: φ :: ψ :: Δ) :=
      em (φ := φ) (by simp) (by simp)
    have ihq : OneSided.Derivation T (Tilde.tilde ψ :: φ :: ψ :: Δ) :=
      em (φ := ψ) (by simp) (by simp)
    have : OneSided.Derivation T (φ :: ψ :: Δ) := (ihp.and ihq).wk (by simp [by simpa using hneg])
    this.or.wk (by simp [hpos])
  | UnivQuantifier.univ φ, hpos, hneg =>
    have : OneSided.Derivation T (Tilde.tilde (Rewriting.free φ) :: Rewriting.free φ :: Δ⁺) :=
      em (φ := Rewriting.free φ) (by simp) (by simp)
    have :
      OneSided.Derivation T
        (LO.FirstOrder.Rewriting.substitute (Tilde.tilde (Rewriting.shift φ)) ![&0] ::
          Rewriting.free φ :: Δ⁺) :=
      Derivation.cast this (by simp [← TransitiveRewriting.comp_app])
    have : OneSided.Derivation T (Rewriting.free φ :: Δ⁺) :=
      (ex (&0) this).wk
        (List.cons_subset_of_subset_of_mem
          (List.mem_cons_of_mem (free φ) <| by simpa using mem_shifts_iff.mpr hneg) (by rfl))
    this.all.wk (by simp [hpos])
  | ExQuantifier.ex φ, hpos, hneg =>
    have : OneSided.Derivation T (Rewriting.free φ :: Tilde.tilde (Rewriting.free φ) :: Δ⁺) :=
      em (φ := Rewriting.free φ) (by simp) (by simp)
    have :
      OneSided.Derivation T
        (LO.FirstOrder.Rewriting.substitute (Rewriting.shift φ) ![&0] ::
          Tilde.tilde (Rewriting.free φ) :: Δ⁺) :=
      Derivation.cast this (by simp [← TransitiveRewriting.comp_app])
    have : OneSided.Derivation T (Rewriting.free (Tilde.tilde φ) :: Δ⁺) :=
      (ex (&0) this).wk
        (List.cons_subset_of_subset_of_mem
          (List.mem_cons_of_mem (free (Tilde.tilde φ)) <| by simpa using mem_shifts_iff.mpr hpos)
          (by simp))
    this.all.wk (by simpa using hneg)
termination_by φ => φ.complexity


-- @@ L220-225 verbatim
instance : Tait (SyntacticFormula L) (Theory L) where
  verum := fun _ Δ => verum Δ
  and := fun dp dq => dp.and dq
  or := fun d => d.or
  wk := fun d ss => d.wk ss
  em := fun hp hn => em hp hn


-- @@ L227-228 verbatim
instance : Tait.Cut (SyntacticFormula L) (Theory L) where
  cut {_ _ _ dp dn} := cut dp dn


-- @@ L230-231 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.provableOfDerivable {φ} (b : OneSided.Derivation₁ T φ) :
    Entailment.Prf T φ :=
  b


-- @@ L233-241 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.specialize {φ : SyntacticSemiformula L 1}
    (t : SyntacticTerm L) :
    OneSided.Derivation T ((UnivQuantifier.univ φ) :: Γ) →
      OneSided.Derivation T (LO.FirstOrder.Rewriting.substitute φ ![t] :: Γ) :=
  fun d ↦
  have :
    OneSided.Derivation T
      (Tilde.tilde (LO.FirstOrder.Rewriting.substitute φ ![t]) ::
        LO.FirstOrder.Rewriting.substitute φ ![t] :: Γ) :=
    Tait.em (φ := LO.FirstOrder.Rewriting.substitute φ ![t]) (by simp) (by simp)
  have dn :
    OneSided.Derivation T
      (Tilde.tilde (UnivQuantifier.univ φ) :: LO.FirstOrder.Rewriting.substitute φ ![t] :: Γ) :=
    by
    simp only [neg_all, Nat.reduceAdd]
    exact Derivation.ex t (by simp only [LogicalConnective.HomClass.map_neg]; exact this)
  have dp :
    OneSided.Derivation T
      ((UnivQuantifier.univ φ) :: LO.FirstOrder.Rewriting.substitute φ ![t] :: Γ) :=
    Derivation.wk d (List.cons_subset_cons _ <| by simp)
  Derivation.cut dp dn


-- @@ L243-254 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.specializes :
    {k : ℕ} →
      {φ : SyntacticSemiformula L k} →
        {Γ : Sequent L} →
          (v : Fin k → SyntacticTerm L) →
            OneSided.Derivation T ((univClosure φ) :: Γ) →
              OneSided.Derivation T ((LO.FirstOrder.Rewriting.substitute φ v) :: Γ)
  | 0, φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : OneSided.Derivation T ((UnivQuantifier.univ (app (Rew.substs (v ·.succ)).q φ)) :: Γ) :=
      by simpa using specializes (φ := UnivQuantifier.univ φ) (v ·.succ) b
    Derivation.cast (specialize (v 0) this)
      (by
        simp only [Nat.reduceAdd, ← TransitiveRewriting.comp_app, List.cons.injEq, and_true];
        congr 2
        ext x <;> simp [Rew.comp_app]
        cases x using Fin.cases <;> simp)


-- @@ L256-267 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.instances :
    {k : ℕ} →
      {φ : SyntacticSemiformula L k} →
        {Γ : Sequent L} →
          {v : Fin k → SyntacticTerm L} →
            OneSided.Derivation T ((LO.FirstOrder.Rewriting.substitute φ v) :: Γ) →
              OneSided.Derivation T ((exClosure φ) :: Γ)
  | 0, φ, Γ, _, b => Derivation.cast b (by simp)
  | k + 1, φ, Γ, v, b =>
    have : OneSided.Derivation T ((ExQuantifier.ex (app (Rew.substs (v ·.succ)).q φ)) :: Γ) :=
      ex (v 0) <|
        Derivation.cast b <| by
          unfold Rewriting.substitute; rw [← TransitiveRewriting.comp_app]; congr 3
          ext x <;> simp [Rew.comp_app]
          cases x using Fin.cases <;> simp
    instances (k := k) (v := (v ·.succ)) (Derivation.cast this (by simp))


-- @@ L269-275 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.allClosureFixitr {φ : SyntacticFormula L}
    (dp : Entailment.Prf T φ) : (m : ℕ) → Entailment.Prf T (univClosure (app (Rew.fixitr 0 m) φ))
  | 0 => by simpa
  | m + 1 => by
    simp only [allClosure_fixitr, Nat.reduceAdd]
    apply all; simp only [free_fix, Rewriting.shifts, List.map_nil]; exact allClosureFixitr dp m


-- @@ L277-278 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.toClose (b : Entailment.Prf T φ) : Entailment.Prf T ∀∀φ :=
  allClosureFixitr b φ.fvSup


-- @@ L280-281 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma toClose! (b : Provable T φ) : Provable T ∀∀φ :=
  ⟨toClose b.get⟩


-- @@ L283-286 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.rewrite₁ (b : Entailment.Prf T φ) (f : ℕ → SyntacticTerm L) :
    Entailment.Prf T (app (Rew.rewrite f) φ) :=
  Derivation.cast (specializes (fun x ↦ f x) (allClosureFixitr b φ.fvSup)) (by simp)


-- @@ L288-325 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.rewrite {Δ} :
    OneSided.Derivation T Δ →
      ∀ (f : ℕ → SyntacticTerm L), OneSided.Derivation T (Δ.map fun φ ↦ app (Rew.rewrite f) φ)
  | axL Δ r v, f =>
    Derivation.cast (axL (Δ.map fun φ ↦ app (Rew.rewrite f) φ) r (fun i ↦ Rew.rewrite f (v i)))
      (by simp [rew_rel, rew_nrel])
  | verum Δ, f => Derivation.cast (verum (Δ.map fun φ ↦ app (Rew.rewrite f) φ)) (by simp)
  | @or _ _ Δ φ ψ d, f =>
    have :
      OneSided.Derivation T
        (Vee.vee (app (Rew.rewrite f) φ) (app (Rew.rewrite f) ψ) ::
          Δ.map fun φ ↦ app (Rew.rewrite f) φ) :=
      or (Derivation.cast (rewrite d f) (by simp))
    Derivation.cast this (by simp)
  | @and _ _ Δ φ ψ dp dq, f =>
    have :
      OneSided.Derivation T
        (Wedge.wedge (app (Rew.rewrite f) φ) (app (Rew.rewrite f) ψ) ::
          Δ.map fun φ ↦ app (Rew.rewrite f) φ) :=
      and (Derivation.cast (rewrite dp f) (by simp)) (Derivation.cast (rewrite dq f) (by simp))
    Derivation.cast this (by simp)
  | @all _ _ Δ φ d, f =>
    have :
      OneSided.Derivation T
        (((Rewriting.free φ) :: Δ⁺).map fun φ ↦
          app (Rew.rewrite (cases &0 fun x => Rew.shift (f x))) φ) :=
      rewrite d (cases &0 fun x => Rew.shift (f x))
    have :
      OneSided.Derivation T
        ((UnivQuantifier.univ (app (Rew.rewrite (Rew.bShift ∘ f)) φ)) ::
          Δ.map fun φ ↦ app (Rew.rewrite f) φ) :=
      all
        (Derivation.cast this
          (by simp [free_rewrite_eq, Rewriting.shifts, shift_rewrite_eq, Function.comp_def]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | @ex _ _ Δ φ t d, f =>
    have :
      OneSided.Derivation T
        ((LO.FirstOrder.Rewriting.substitute φ ![t] :: Δ).map fun φ ↦ app (Rew.rewrite f) φ) :=
      rewrite d f
    have :
      OneSided.Derivation T
        ((ExQuantifier.ex (app (Rew.rewrite (Rew.bShift ∘ f)) φ)) ::
          Δ.map fun φ ↦ app (Rew.rewrite f) φ) :=
      ex (Rew.rewrite f t) (Derivation.cast this (by simp [rewrite_subst_eq]))
    Derivation.cast this (by simp [Rew.q_rewrite])
  | @wk _ _ Δ Γ d ss, f => (rewrite d f).wk (List.map_subset _ ss)
  | @cut _ _ Δ φ d dn, f =>
    have dΔ :
      OneSided.Derivation T ((app (Rew.rewrite f) φ) :: Δ.map fun φ ↦ app (Rew.rewrite f) φ) :=
      Derivation.cast (rewrite d f) (by simp)
    have dΓ :
      OneSided.Derivation T
        (Tilde.tilde (app (Rew.rewrite f) φ) :: Δ.map fun φ ↦ app (Rew.rewrite f) φ) :=
      Derivation.cast (rewrite dn f) (by simp)
    Derivation.cast (cut dΔ dΓ) (by simp)
  | root h, f => rewrite₁ (root h) f


-- @@ L327-329 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def _root_.LO.FirstOrder.Derivation.map {Δ : Sequent L} (d : OneSided.Derivation T Δ)
    (f : ℕ → ℕ) : OneSided.Derivation T (Δ.map fun φ ↦ app (@Rew.rewriteMap L ℕ ℕ 0 f) φ) :=
  rewrite d (fun x ↦ &(f x))


-- @@ L331-336 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def _root_.LO.FirstOrder.Derivation.shift {Δ : Sequent L} (d : OneSided.Derivation T Δ) :
    OneSided.Derivation T Δ⁺ :=
  Derivation.cast (Derivation.map d Nat.succ)
    (by
      simp only [Rewriting.shifts, List.map_inj_left]
      intro _ _
      rfl)


-- @@ L338-348 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.trans (F : PrfSet U T) {Γ : Sequent L} :
    OneSided.Derivation T Γ → OneSided.Derivation U Γ
  | axL Γ R v => axL Γ R v
  | verum Γ => verum Γ
  | and d₁ d₂ => and (trans F d₁) (trans F d₂)
  | or d => or (trans F d)
  | all d => all (trans F d)
  | ex t d => ex t (trans F d)
  | wk d ss => wk (trans F d) ss
  | cut d₁ d₂ => cut (trans F d₁) (trans F d₂)
  | root h => F h


-- @@ L350-352 verbatim
instance : Tait.Axiomatized (SyntacticFormula L) (Theory L) where
  root {_ _ h} := root h
  trans {_ _ _ F d} := trans (fun h ↦ F _ h) d


-- @@ L354-354 verbatim
variable [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]


-- @@ L356-361 expanded
/-- Derive a formula from the negation of its universal closure in the sequent calculus. -/
def notClose' (φ) : OneSided.Derivation T [Tilde.tilde (∀∀φ), φ] :=
  have : OneSided.Derivation T [exClosure (Tilde.tilde (app (@Rew.fixitr L 0 (fvSup φ)) φ)), φ] :=
    instances (v := fun x ↦ &x) (em (φ := φ) (by simp) (by simp))
  Derivation.cast this (by simp [close])


-- @@ L363-365 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.invClose (b : Entailment.Prf T ∀∀φ) : Entailment.Prf T φ :=
  cut (wk b (by simp)) (notClose' φ)


-- @@ L367-369 expanded
omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma invClose! (b : Provable T ∀∀φ) : Provable T φ :=
  ⟨invClose b.get⟩


-- @@ L371-385 expanded
/-- Transform a derivation by removing one theory axiom and adding its negated closure. -/
def deductionAux {Γ : Sequent L} :
    OneSided.Derivation T Γ → OneSided.Derivation (T \ { φ }) (Tilde.tilde (∀∀φ) :: Γ)
  | axL Γ R v => Tait.wkTail <| axL Γ R v
  | verum Γ => Tait.wkTail <| verum Γ
  | and d₁ d₂ =>
    Tait.rotate₁ <| and (Tait.rotate₁ (deductionAux d₁)) (Tait.rotate₁ (deductionAux d₂))
  | or d => Tait.rotate₁ <| or (Tait.rotate₂ (deductionAux d))
  | all d => Tait.rotate₁ <| all (Derivation.cast (Tait.rotate₁ (deductionAux d)) (by simp))
  | ex t d => Tait.rotate₁ <| ex t <| Tait.rotate₁ (deductionAux d)
  | wk d ss => wk (deductionAux d) (by simp [List.subset_cons_of_subset _ ss])
  | cut d₁ d₂ => (Tait.rotate₁ <| deductionAux d₁).cut (Tait.rotate₁ <| deductionAux d₂)
  | root (φ := ψ) h =>
    if hq : φ = ψ then Derivation.cast (notClose' φ) (by simp [hq])
    else
      have : OneSided.Derivation₁ (T \ { φ }) ψ := root (by simp [h, Ne.symm hq])
      wk this (by simp)


-- @@ L387-389 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.deduction (d : OneSided.Derivation (insert φ T) Γ) :
    OneSided.Derivation T (Tilde.tilde (∀∀φ) :: Γ) :=
  Tait.ofAxiomSubset (by intro x; simp; tauto) (deductionAux d (φ := φ))


-- @@ L391-405 expanded
omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.FirstOrder.Derivation.provable_iff_inconsistent :
    Provable T φ ↔ Entailment.Inconsistent (insert (Tilde.tilde ∀∀φ) T) := by
  classical
  constructor
  · rintro b
    exact
      Entailment.inconsistent_of_provable_of_unprovable
        (Entailment.wk! (fun _ hψ ↦ Set.mem_insert_of_mem _ hψ) (Derivation.toClose! b))
        (Entailment.by_axm _ (Set.mem_insert _ _))
  · intro h
    rcases Tait.inconsistent_iff_provable.mp h with ⟨d⟩
    have : Entailment.Prf T ∀∀φ :=
      Derivation.cast (deduction d) (by rw [close_eq_self_of (Tilde.tilde ∀∀φ) (by simp)]; simp)
    exact ⟨invClose this⟩


-- @@ L407-411 expanded
omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma _root_.LO.FirstOrder.Derivation.unprovable_iff_consistent :
    Unprovable T φ ↔ Entailment.Consistent (insert (Tilde.tilde ∀∀φ) T) := by
  simp [← Entailment.not_inconsistent_iff_consistent, ← provable_iff_inconsistent]


-- @@ L413-413 verbatim
section «lp_section_3»


-- @@ L415-415 verbatim
variable {L₁ : Language} {L₂ : Language} {T₁ : Theory L₁} {Δ₁ : Sequent L₁}


-- @@ L417-419 verbatim
lemma _root_.LO.FirstOrder.Derivation.shifts_image (Φ : L₁ →ᵥ L₂) {Δ : List (SyntacticFormula L₁)} :
     (Δ.map <| Semiformula.lMap Φ)⁺ = (Δ⁺.map <| Semiformula.lMap Φ) := by
  simp [Rewriting.shifts, Function.comp_def, Semiformula.lMap_shift]


-- @@ L421-449 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.lMap (Φ : L₁ →ᵥ L₂) {Δ} :
    OneSided.Derivation T₁ Δ → OneSided.Derivation (T₁.lMap Φ) (Δ.map (.lMap Φ))
  | axL Δ r v =>
    .cast (axL (Δ.map (.lMap Φ)) (Φ.rel r) (fun i ↦ .lMap Φ (v i)))
      (by simp [Semiformula.lMap_rel, Semiformula.lMap_nrel])
  | verum Δ => verum _
  | @or _ _ Δ φ ψ d =>
    by
    have :
      OneSided.Derivation (T₁.lMap Φ)
        (Vee.vee (.lMap Φ φ) (.lMap Φ ψ) :: Δ.map (.lMap Φ) : Sequent L₂) :=
      or (lMap Φ d)
    exact Derivation.cast this (by simp)
  | @and _ _ Δ φ ψ dp dq =>
    have :
      OneSided.Derivation (T₁.lMap Φ)
        (Wedge.wedge (.lMap Φ φ) (.lMap Φ ψ) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      and (Derivation.cast (lMap Φ dp) (by simp)) (Derivation.cast (lMap Φ dq) (by simp))
    Derivation.cast this (by simp)
  | @all _ _ Δ φ d =>
    have :
      OneSided.Derivation (T₁.lMap Φ)
        ((UnivQuantifier.univ (.lMap Φ φ)) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      all (Derivation.cast (lMap Φ d) (by simp [← Semiformula.lMap_free, shifts_image]))
    Derivation.cast this (by simp)
  | @ex _ _ Δ φ t d =>
    have :
      OneSided.Derivation (T₁.lMap Φ)
        ((ExQuantifier.ex (.lMap Φ φ)) :: (Δ.map (.lMap Φ)) : Sequent L₂) :=
      ex (Semiterm.lMap Φ t) (Derivation.cast (lMap Φ d) (by simp [Semiformula.lMap_substs]))
    Derivation.cast this (by simp)
  | @wk _ _ Δ Γ d ss => (lMap Φ d).wk (List.map_subset _ ss)
  | @cut _ _ Δ φ d dn =>
    have : OneSided.Derivation (T₁.lMap Φ) (Δ.map (.lMap Φ) : Sequent L₂) :=
      cut (φ := .lMap Φ φ) (Derivation.cast (lMap Φ d) (by simp))
        (Derivation.cast (lMap Φ dn) (by simp))
    Derivation.cast this (by simp [])
  | root h => root (Set.mem_image_of_mem _ h)


-- @@ L451-453 verbatim
lemma _root_.LO.FirstOrder.Derivation.inconsistent_lMap (Φ : L₁ →ᵥ L₂) :
    Entailment.Inconsistent T₁ → Entailment.Inconsistent (T₁.lMap Φ) := by
  simp only [Entailment.inconsistent_iff_provable_bot]; intro ⟨b⟩; exact ⟨lMap Φ b⟩


-- @@ L455-455 verbatim
end «lp_section_3»


-- @@ L457-457 verbatim
omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]


-- @@ L459-464 expanded
private lemma map_subst_eq_free (φ : SyntacticSemiformula L 1) (h : ¬φ.FVar? m) :
    app (@Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1))
        (LO.FirstOrder.Rewriting.substitute φ ![&m] : SyntacticFormula L) =
      Rewriting.free φ :=
  by
  simp only [← TransitiveRewriting.comp_app]
  exact
    Semiformula.rew_eq_of_funEqOn (by simp [Rew.comp_app, Fin.eq_zero])
      (fun x hx => by simp [Rew.comp_app, ne_of_mem_of_not_mem hx h])


-- @@ L466-470 expanded
private lemma map_rewriteMap_eq_shifts (Δ : Sequent L) (h : ∀ φ ∈ Δ, ¬φ.FVar? m) :
    Δ.map (fun φ ↦ app (@Rew.rewriteMap L ℕ ℕ 0 (fun x ↦ if x = m then 0 else x + 1)) φ) = Δ⁺ :=
  by
  apply List.map_congr_left
  intro φ hp; exact rew_eq_of_funEqOn₀ (by intro x hx; simp [ne_of_mem_of_not_mem hx (h φ hp)])


-- @@ L472-479 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.genelalizeByNewver {φ : SyntacticSemiformula L 1}
    (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : OneSided.Derivation T (LO.FirstOrder.Rewriting.substitute φ ![&m] :: Δ)) :
    OneSided.Derivation T ((UnivQuantifier.univ φ) :: Δ) :=
  by
  have : OneSided.Derivation T ((Rewriting.free φ) :: Δ⁺) :=
    Derivation.cast (Derivation.map d (fun x => if x = m then 0 else x + 1))
      (by simp [map_subst_eq_free φ hp, map_rewriteMap_eq_shifts Δ hΔ])
  exact all this


-- @@ L481-487 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.exOfInstances (v : List (SyntacticTerm L))
    (φ : SyntacticSemiformula L 1)
    (h : OneSided.Derivation T (v.map (LO.FirstOrder.Rewriting.substitute φ ![·]) ++ Γ)) :
    OneSided.Derivation T ((ExQuantifier.ex φ) :: Γ) := by
  induction v generalizing Γ with
  | nil => exact weakening h (List.subset_cons_self _ _)
  | cons t v ih => exact (ih (Γ := (ExQuantifier.ex φ) :: Γ) ((ex t h).wk (by simp))).wk (by simp)


-- @@ L489-493 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.exOfInstances' (v : List (SyntacticTerm L))
    (φ : SyntacticSemiformula L 1)
    (h :
      OneSided.Derivation T
        ((ExQuantifier.ex φ) :: v.map (LO.FirstOrder.Rewriting.substitute φ ![·]) ++ Γ)) :
    OneSided.Derivation T ((ExQuantifier.ex φ) :: Γ) :=
  (exOfInstances (Γ := (ExQuantifier.ex φ) :: Γ) v φ (h.wk <| by simp)).wk (by simp)


-- @@ L495-495 verbatim
end Derivation


-- @@ L497-498 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.newVar (Γ : Sequent L) : ℕ := (Γ.map Semiformula.fvSup).foldr max 0


-- @@ L500-503 verbatim
lemma «not_fvar?_newVar» {φ : SyntacticFormula L} {Γ : Sequent L} (h : φ ∈ Γ) :
    ¬FVar? φ (newVar Γ) :=
  not_fvar?_of_lt_fvSup φ (by
    simpa [newVar] using List.le_max_of_le' 0 (List.mem_map_of_mem h) (by simp))


-- @@ L505-505 verbatim
namespace Derivation


-- @@ L507-507 verbatim
open Semiformula

-- @@ L508-508 verbatim
variable {P : SyntacticFormula L → Prop} {T : Theory L} {Δ : Sequent L}


-- @@ L510-515 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Derivation.allNvar {φ} (h : UnivQuantifier.univ φ ∈ Δ) :
    OneSided.Derivation T (LO.FirstOrder.Rewriting.substitute φ ![&(newVar Δ)] :: Δ) →
      OneSided.Derivation T Δ :=
  fun b ↦
  let b : OneSided.Derivation T ((UnivQuantifier.univ φ) :: Δ) :=
    genelalizeByNewver (by simpa [FVar?] using not_fvar?_newVar h) (fun _ ↦ not_fvar?_newVar) b
  Tait.wk b (by simp [h])


-- @@ L517-519 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def _root_.LO.FirstOrder.Derivation.id {φ} (hp : φ ∈ T) :
    OneSided.Derivation T (Tilde.tilde ∀∀φ :: Δ) → OneSided.Derivation T Δ := fun b ↦
  Tait.cut (Tait.wk (toClose (root hp)) (by simp)) b


-- @@ L521-521 verbatim
end Derivation


-- @@ L523-523 verbatim
namespace Theory


-- @@ L525-526 expanded
instance {T U : Theory L} : WeakerThan T (T + U) :=
  Entailment.Axiomatized.weakerThanOfSubset Set.subset_union_left


-- @@ L528-529 expanded
instance {T U : Theory L} : WeakerThan U (T + U) :=
  Entailment.Axiomatized.weakerThanOfSubset Set.subset_union_right


-- @@ L531-531 verbatim
end Theory


-- @@ L533-533 verbatim
variable (L)


-- @@ L535-538 verbatim
/-- An auxiliary structure to provide systems of provability of sentence. -/
structure _root_.LO.FirstOrder.Theory.Alt where
  /-- Imported declaration from the Incompleteness formalization. -/
  thy : Theory L


-- @@ L540-540 verbatim
variable {L}


-- @@ L542-542 verbatim
alias Theory.alt := Theory.Alt.mk


-- @@ L544-544 expanded
instance : Entailment (Sentence L) (Theory.Alt L) :=
  ⟨fun T σ ↦ Entailment.Prf T.thy ↑σ⟩


-- @@ L546-546 verbatim
@[simp] lemma _root_.LO.FirstOrder.Theory.alt_thy (T : Theory L) : T.alt.thy = T := rfl


-- @@ L548-548 verbatim
section «lp_section_4»


-- @@ L550-551 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Provable₀ (T : Theory L) (σ : Sentence L) : Prop :=
  Provable T.alt σ


-- @@ L553-554 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊢!. " => Provable₀


-- @@ L556-557 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Unprovable₀ (T : Theory L) (σ : Sentence L) : Prop :=
  Unprovable T.alt σ


-- @@ L559-560 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊬. " => Unprovable₀


-- @@ L562-563 verbatim
instance (T : Theory.Alt L) : Entailment.Classical T :=
  Entailment.Classical.ofEquiv T.thy T (Rewriting.app Rew.emb) (fun _ ↦ .refl _)


-- @@ L565-565 verbatim
variable {T : Theory L} {σ : Sentence L}


-- @@ L567-567 expanded
lemma _root_.LO.FirstOrder.provable₀_iff : Provable₀ T σ ↔ Provable T ↑σ :=
  iff_of_eq rfl


-- @@ L569-569 expanded
lemma _root_.LO.FirstOrder.unprovable₀_iff : Unprovable₀ T σ ↔ Unprovable T ↑σ :=
  iff_of_eq rfl


-- @@ L571-571 verbatim
end «lp_section_4»


-- @@ L573-573 verbatim
end FirstOrder


-- @@ L575-575 verbatim
end LO
