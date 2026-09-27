/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Syntax.Rew
public import LeanPool.Incompleteness.Foundation.Logic.Semantics
import Mathlib.Tactic.Bound.Init


-- @@ L12-18 verbatim
/-!
# Semantics of first-order logic

This file defines the structure and the evaluation of terms and formulas by Tarski's truth
definition.

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace LO


-- @@ L24-24 verbatim
namespace FirstOrder


-- @@ L26-26 verbatim
variable {L : Language.{u}}


-- @@ L28-33 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[ext] class Structure (L : Language.{u}) (M : Type w) where
  /-- Imported declaration from the Incompleteness formalization. -/
  func : ⦃k : ℕ⦄ → L.Func k → (Fin k → M) → M
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : ⦃k : ℕ⦄ → L.Rel k → (Fin k → M) → Prop


-- @@ L35-41 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Struc (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Dom : Type*
  nonempty : Nonempty Dom
  /-- Imported declaration from the Incompleteness formalization. -/
  struc : Structure L Dom


-- @@ L43-44 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev SmallStruc (L : Language.{u}) := Struc.{u, u} L


-- @@ L46-46 verbatim
instance : CoeSort (Struc L) (Type _) := ⟨Struc.Dom⟩


-- @@ L48-48 verbatim
namespace Structure


-- @@ L50-52 verbatim
instance [n : Nonempty M] : Nonempty (Structure L M) := by
  rcases n with ⟨x⟩
  exact ⟨{ func := fun _ _ _ => x, rel := fun _ _ _ => True }⟩


-- @@ L54-58 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
protected def lMap (φ : L₁ →ᵥ L₂) {M : Type w} (S : Structure L₂ M) : Structure L₁ M where
  func := fun _ f => S.func (φ.func f)
  rel := fun _ r => S.rel (φ.rel r)


-- @@ L60-60 verbatim
variable (φ : L₁ →ᵥ L₂) {M : Type w} (s₂ : Structure L₂ M)


-- @@ L62-64 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[simp] lemma lMap_func {k} {f : L₁.Func k} {v : Fin k → M} :
    (s₂.lMap φ).func f v = s₂.func (φ.func f) v := rfl


-- @@ L66-67 verbatim
@[simp] lemma lMap_rel
    {k} {r : L₁.Rel k} {v : Fin k → M} : (s₂.lMap φ).rel r v ↔ s₂.rel (φ.rel r) v := of_eq rfl


-- @@ L69-73 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def ofEquiv {M : Type w} [Structure L M] {N : Type w'} (Θ : M ≃ N) : Structure L N where
  func := fun _ f v => Θ (func f (Θ.symm ∘ v))
  rel  := fun _ r v => rel r (Θ.symm ∘ v)


-- @@ L75-77 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Decidable (L : Language.{u}) (M : Type w) [s : Structure L M] :=
  {k : ℕ} → (r : L.Rel k) → (v : Fin k → M) → Decidable (s.rel r v)


-- @@ L79-80 verbatim
noncomputable instance [Structure L M] :
    Structure.Decidable L M := fun r v => Classical.dec (rel r v)


-- @@ L82-83 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible] def toStruc [i : Nonempty M] (s : Structure L M) : Struc L := ⟨M, i, s⟩


-- @@ L85-85 verbatim
end Structure


-- @@ L87-87 verbatim
namespace Struc


-- @@ L89-89 verbatim
instance (s : Struc L) : Nonempty s.Dom := s.nonempty


-- @@ L91-91 verbatim
instance (s : Struc L) : Structure L s.Dom := s.struc


-- @@ L93-93 verbatim
end Struc


-- @@ L95-95 verbatim
namespace Semiterm


-- @@ L97-100 verbatim
variable
  {M : Type w} {s : Structure L M}
  {e : Fin n → M} {e₁ : Fin n₁ → M} {e₂ : Fin n₂ → M}
  {ε : ξ → M} {ε₁ : μ₁ → M} {ε₂ : μ₂ → M}


-- @@ L102-106 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def val (s : Structure L M) (e : Fin n → M) (ε : ξ → M) : Semiterm L ξ n → M
  | #x       => e x
  | &x       => ε x
  | func f v => s.func f (fun i => (v i).val s e ε)


-- @@ L108-109 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev valb (s : Structure L M) (e : Fin n → M) (t : Semiterm L Empty n) : M := t.val s e Empty.elim


-- @@ L111-113 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev valm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : ξ → M) : Semiterm L ξ n → M :=
  val s e ε


-- @@ L115-117 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev valbm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) : Semiterm L Empty n → M :=
  valb s e


-- @@ L119-120 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev realize (s : Structure L M) (t : Term L M) : M := t.val s ![] id


-- @@ L122-122 verbatim
@[simp] lemma val_bvar (x) : val s e ε (#x : Semiterm L ξ n) = e x := rfl


-- @@ L124-124 verbatim
@[simp] lemma val_fvar (x) : val s e ε (&x : Semiterm L ξ n) = ε x := rfl


-- @@ L126-127 verbatim
lemma val_func {k} (f : L.Func k) (v) :
    val s e ε (func f v) = s.func f (fun i => (v i).val s e ε) := rfl


-- @@ L129-130 verbatim
@[simp] lemma val_func₀ (f : L.Func 0) (v) :
    val s e ε (func f v) = s.func f ![] := by simp [val_func, Matrix.empty_eq]


-- @@ L132-139 verbatim
@[simp] lemma val_func₁ (f : L.Func 1) (t) :
    val s e ε (func f ![t]) = s.func f ![t.val s e ε] := by
  simp only [val_func]
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact Fin.elim0 i


-- @@ L141-143 verbatim
@[simp] lemma val_func₂ (f : L.Func 2) (t u) :
    val s e ε (func f ![t, u]) = s.func f ![t.val s e ε, u.val s e ε] :=
  by simp only [val_func]; congr; funext i; cases i using Fin.cases <;> simp


-- @@ L145-147 verbatim
lemma val_rew (ω : Rew L μ₁ n₁ μ₂ n₂) (t : Semiterm L μ₁ n₁) :
    (ω t).val s e₂ ε₂ = t.val s (val s e₂ ε₂ ∘ ω ∘ bvar) (val s e₂ ε₂ ∘ ω ∘ fvar) :=
  by induction t <;> simp [*, Rew.func, val_func]


-- @@ L149-151 verbatim
lemma val_rewrite (f : μ₁ → Semiterm L μ₂ n) (t : Semiterm L μ₁ n) :
    (Rew.rewrite f t).val s e ε₂ = t.val s e (fun x => (f x).val s e ε₂) :=
  by simp [val_rew]; congr


-- @@ L153-155 verbatim
lemma val_rewriteMap (f : μ₁ → μ₂) (t : Semiterm L μ₁ n) :
    (Rew.rewriteMap f t).val s e ε₂ = t.val s e (fun x => ε₂ (f x)) :=
  by simp [val_rew]; congr


-- @@ L157-159 verbatim
lemma val_substs (w : Fin n₁ → Semiterm L ξ n₂) (t : Semiterm L ξ n₁) :
    (Rew.substs w t).val s e₂ ε = t.val s (fun x => (w x).val s e₂ ε) ε :=
  by simp [val_rew]; congr


-- @@ L161-162 expanded
@[simp]
lemma val_bShift (a : M) (t : Semiterm L ξ n) :
    (Rew.bShift t).val s (vecCons a e) ε = t.val s e ε := by simp [val_rew, Function.comp_def]


-- @@ L164-165 verbatim
lemma val_bShift' (e : Fin (n + 1) → M) (t : Semiterm L ξ n) :
    (Rew.bShift t).val s e ε = t.val s (e ·.succ) ε := by simp [val_rew, Function.comp_def]


-- @@ L167-169 verbatim
@[simp] lemma val_emb {o : Type v'} [i : IsEmpty o] (t : Semiterm L o n) :
    (Rew.emb t : Semiterm L ξ n).val s e ε = t.val s e i.elim := by
  simp only [val_rew]; congr; { funext x; exact i.elim' x }


-- @@ L171-173 verbatim
@[simp] lemma val_castLE (h : n₁ ≤ n₂) (t : Semiterm L ξ n₁) :
    (Rew.castLE h t).val s e₂ ε = t.val s (fun x => e₂ (x.castLE h)) ε  := by
  simp [val_rew]; congr


-- @@ L175-177 verbatim
lemma val_embSubsts (w : Fin k → Semiterm L ξ n) (t : Semiterm L Empty k) :
    (Rew.embSubsts w t).val s e ε = t.valb s (fun x ↦ (w x).val s e ε) := by
  simp [val_rew, Empty.eq_elim]; congr


-- @@ L179-181 verbatim
@[simp] lemma val_toS {e : Fin n → M} (t : Semiterm L (Fin n) 0) :
    valb s e (Rew.toS t) = val s ![] e t := by
  simp [val_rew, Matrix.empty_eq]; congr


-- @@ L183-186 verbatim
@[simp] lemma val_toF {e : Fin n → M} (t : Semiterm L Empty n) :
    val s ![] e (Rew.toF t) = valb s e t := by
  simp only [val_rew]; congr
  funext i; simp only [Function.comp_apply]; contradiction


-- @@ L188-188 verbatim
section «lp_section_1»


-- @@ L190-190 verbatim
variable (φ : L₁ →ᵥ L₂) (e : Fin n → M) (ε : ξ → M)


-- @@ L192-195 verbatim
lemma val_lMap (φ : L₁ →ᵥ L₂) (s₂ : Structure L₂ M) (e : Fin n → M) (ε : ξ → M) {t :
    Semiterm L₁ ξ n} :
    (t.lMap φ).val s₂ e ε = t.val (s₂.lMap φ) e ε :=
  by induction t <;> simp [*, val_func, Semiterm.lMap_func]


-- @@ L197-197 verbatim
end «lp_section_1»


-- @@ L199-199 verbatim
section «lp_section_2»


-- @@ L201-201 verbatim
variable (ε : ℕ → M)


-- @@ L203-204 verbatim
lemma val_shift (t : SyntacticSemiterm L n) :
    (Rew.shift t).val s e ε = t.val s e (ε ∘ Nat.succ) := by simp [val_rew]; congr


-- @@ L206-217 expanded
lemma val_free (a : M) (t : SyntacticSemiterm L (n + 1)) :
    (Rew.free t).val s e (cases a ε) = t.val s (vecConsLast e a) ε :=
  by
  simp only [val_rew, Nat.succ_eq_add_one]
  congr
  funext i
  cases i using Fin.lastCases with
  | last =>
    simp only [Function.comp_apply, Rew.free_bvar_last, val_fvar, Nat.cases_zero,
      Matrix.rightConcat_last]
  | cast i =>
    simp only [Function.comp_apply, Rew.free_bvar_castSucc, val_bvar, Matrix.rightConcat_castSucc]


-- @@ L219-231 expanded
lemma val_fix (a : M) (t : SyntacticSemiterm L n) :
    (Rew.fix t).val s (vecConsLast e a) ε = t.val s e (cases a ε) :=
  by
  simp only [val_rew, Nat.succ_eq_add_one]
  congr
  · funext i
    simp only [Function.comp_apply, Rew.fix_bvar, val_bvar, Matrix.rightConcat_castSucc]
  · funext i
    cases i with
    | zero =>
      simp only [Function.comp_apply, Rew.fix_fvar_zero, val_bvar, Nat.cases_zero,
        Matrix.rightConcat_last]
    | succ i => simp only [Function.comp_apply, Rew.fix_fvar_succ, val_fvar, Nat.cases_succ]


-- @@ L233-233 verbatim
end «lp_section_2»


-- @@ L235-243 verbatim
lemma val_eq_of_funEqOn [DecidableEq ξ] (t : Semiterm L ξ n) (h : Function.funEqOn t.FVar? ε ε') :
    val s e ε t = val s e ε' t := by
  induction t
  case bvar x => rfl
  case fvar x => exact h x (by simp [FVar?])
  case func k f v ih =>
    simp only [val_func]
    congr; funext i
    exact ih i (by intro x hx; exact h x (by simp only [fvar?_func]; exact ⟨i, hx⟩))


-- @@ L245-255 verbatim
lemma val_toEmpty [DecidableEq ξ] (t : Semiterm L ξ n) (h : t.freeVariables = ∅) :
    val s e ε t = valb s e (t.toEmpty h) := by
  induction t
  case bvar => rfl
  case fvar => simp at h
  case func k f v ih =>
    simp only [val_func, Semiterm.toEmpty]
    have : ∀ i, (v i).freeVariables = ∅ := by
      simpa [Semiterm.freeVariables_func, Finset.biUnion_eq_empty] using h
    congr 1; funext i
    exact ih i (this i)


-- @@ L257-257 verbatim
end Semiterm


-- @@ L259-259 verbatim
namespace Structure


-- @@ L261-261 verbatim
section «lp_section_3»


-- @@ L263-263 verbatim
variable [s : Structure L M] (Θ : M ≃ N)


-- @@ L265-266 verbatim
lemma ofEquiv_func (f : L.Func k) (v : Fin k → N) :
    (ofEquiv Θ).func f v = Θ (func f (Θ.symm ∘ v)) := rfl


-- @@ L268-270 verbatim
lemma ofEquiv_val (e : Fin n → N) (ε : ξ → N) (t : Semiterm L ξ n) :
    t.val (ofEquiv Θ) e ε = Θ (t.val s (Θ.symm ∘ e) (Θ.symm ∘ ε)) := by
  induction t <;> simp [*, Semiterm.val_func, ofEquiv_func Θ, Function.comp_def]


-- @@ L272-272 verbatim
end «lp_section_3»


-- @@ L274-274 verbatim
end Structure


-- @@ L276-276 verbatim
namespace Semiformula


-- @@ L278-278 verbatim
variable {M : Type w} {s : Structure L M}

-- @@ L279-279 verbatim
variable {n : ℕ} {e : Fin n → M} {e₂ : Fin n₂ → M} {ε : ξ → M} {ε₂ : μ₂ → M}


-- @@ L281-290 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def EvalAux (s : Structure L M) (ε : ξ → M) : ∀ {n}, (Fin n → M) → Semiformula L ξ n → Prop
  | _, _, ⊤ => True
  | _, _, ⊥ => False
  | _, e, rel φ v => s.rel φ (fun i => Semiterm.val s e ε (v i))
  | _, e, nrel φ v => ¬s.rel φ (fun i => Semiterm.val s e ε (v i))
  | _, e, Wedge.wedge φ ψ => φ.EvalAux s ε e ∧ ψ.EvalAux s ε e
  | _, e, Vee.vee φ ψ => φ.EvalAux s ε e ∨ ψ.EvalAux s ε e
  | _, e, UnivQuantifier.univ φ => ∀ x : M, (φ.EvalAux s ε (vecCons x e))
  | _, e, ExQuantifier.ex φ => ∃ x : M, (φ.EvalAux s ε (vecCons x e))


-- @@ L292-294 expanded
@[simp]
lemma EvalAux_neg (φ : Semiformula L ξ n) : EvalAux s ε e (Tilde.tilde φ) = ¬EvalAux s ε e φ := by
  induction φ using rec' <;> simp [*, EvalAux, or_iff_not_imp_left]


-- @@ L296-304 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Eval (s : Structure L M) (e : Fin n → M) (ε : ξ → M) : Hom (Semiformula L ξ n) Prop
    where
  toTr := EvalAux s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp [EvalAux]
  map_or' := by simp [EvalAux]
  map_neg' := by simp [EvalAux_neg]
  map_imply' := by simp [EvalAux_neg, ← neg_eq, EvalAux, imp_iff_not_or]


-- @@ L306-308 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Evalm (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : ξ → M) :
    Hom (Semiformula L ξ n) Prop :=
  Eval s e ε


-- @@ L310-311 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Evalf (s : Structure L M) (ε : ξ → M) : Hom (Formula L ξ) Prop :=
  Eval s ![] ε


-- @@ L313-314 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Evalb (s : Structure L M) (e : Fin n → M) : Hom (Semisentence L n) Prop :=
  Eval s e Empty.elim


-- @@ L316-318 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Evalfm (M : Type w) [s : Structure L M] (ε : ξ → M) : Hom (Formula L ξ) Prop :=
  Evalf s ε


-- @@ L320-322 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Evalbm (M : Type w) [s : Structure L M] (e : Fin n → M) : Hom (Semiformula L Empty n) Prop :=
  Evalb s e


-- @@ L324-325 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:max M:90 " ⊧/" e:max => Evalbm M e


-- @@ L327-328 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Realize (s : Structure L M) : Hom (Formula L M) Prop :=
  Eval s ![] id


-- @@ L330-331 verbatim
lemma eval_rel {k} {r : L.Rel k} {v} :
    Eval s e ε (rel r v) ↔ s.rel r (fun i => Semiterm.val s e ε (v i)) := of_eq rfl


-- @@ L333-335 verbatim
lemma _root_.LO.FirstOrder.Semiformula.Eval.of_eq
    {e e' : Fin n → M} {ε ε' : ξ → M} {φ} (h : Eval s e ε φ) (he : e = e') (hε : ε = ε') :
    Eval s e' ε' φ := he ▸ hε ▸ h


-- @@ L337-338 verbatim
@[simp] lemma eval_rel₀ {r : L.Rel 0} :
    Eval s e ε (rel r ![]) ↔ s.rel r ![] := by simp [eval_rel, Matrix.empty_eq]


-- @@ L340-346 verbatim
@[simp] lemma eval_rel₁ {r : L.Rel 1} (t : Semiterm L ξ n) :
    Eval s e ε (rel r ![t]) ↔ s.rel r ![t.val s e ε] := by
  simp only [eval_rel]; apply of_eq; congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact Fin.elim0 i


-- @@ L348-351 verbatim
@[simp] lemma eval_rel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L ξ n) :
    Eval s e ε (rel r ![t₁, t₂]) ↔ s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp only [eval_rel]; apply of_eq; congr
  funext i; cases i using Fin.cases <;> simp


-- @@ L353-354 verbatim
lemma eval_nrel {k} {r : L.Rel k} {v} :
    Eval s e ε (nrel r v) ↔ ¬s.rel r (fun i => Semiterm.val s e ε (v i)) := of_eq rfl


-- @@ L356-357 verbatim
@[simp] lemma eval_nrel₀ {r : L.Rel 0} :
    Eval s e ε (nrel r ![]) ↔ ¬s.rel r ![] := by simp [eval_nrel, Matrix.empty_eq]


-- @@ L359-365 verbatim
@[simp] lemma eval_nrel₁ {r : L.Rel 1} (t : Semiterm L ξ n) :
    Eval s e ε (nrel r ![t]) ↔ ¬s.rel r ![t.val s e ε] := by
  simp only [eval_nrel]; apply of_eq; congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact Fin.elim0 i


-- @@ L367-370 verbatim
@[simp] lemma eval_nrel₂ {r : L.Rel 2} (t₁ t₂ : Semiterm L ξ n) :
    Eval s e ε (nrel r ![t₁, t₂]) ↔ ¬s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp only [eval_nrel]; apply of_eq; congr
  funext i; cases i using Fin.cases <;> simp


-- @@ L372-373 expanded
@[simp]
lemma eval_all {φ : Semiformula L ξ (n + 1)} :
    Eval s e ε (UnivQuantifier.univ φ) ↔ ∀ x : M, Eval s (vecCons x e) ε φ :=
  of_eq rfl


-- @@ L375-376 expanded
@[simp]
lemma eval_ex {φ : Semiformula L ξ (n + 1)} :
    Eval s e ε (ExQuantifier.ex φ) ↔ ∃ x : M, Eval s (vecCons x e) ε φ :=
  of_eq rfl


-- @@ L378-379 expanded
@[simp]
lemma eval_ball {φ ψ : Semiformula L ξ (n + 1)} :
    Eval s e ε (ball φ ψ) ↔ ∀ x : M, Eval s (vecCons x e) ε φ → Eval s (vecCons x e) ε ψ := by
  simp [ball]


-- @@ L381-382 expanded
@[simp]
lemma eval_bex {φ ψ : Semiformula L ξ (n + 1)} :
    Eval s e ε (bex φ ψ) ↔
      ∃ x : M, Wedge.wedge (Eval s (vecCons x e) ε φ) (Eval s (vecCons x e) ε ψ) :=
  by simp [bex]


-- @@ L384-392 expanded
@[simp]
lemma eval_univClosure {e'} {φ : Semiformula L ξ n'} :
    Eval s e' ε (univClosure φ) ↔ ∀ e, Eval s e ε φ := by
  induction n' generalizing e' with
  | zero => simp [eq_finZeroElim]
  | succ n' ih =>
    simp only [univClosure_succ, eval_all, ih, Nat.succ_eq_add_one]
    constructor
    · intro h e; simpa using h (Matrix.vecTail e) (Matrix.vecHead e)
    · intro h e x; exact h (vecCons x e)


-- @@ L394-402 expanded
@[simp]
lemma eval_exClosure {e'} {φ : Semiformula L ξ n'} :
    Eval s e' ε (exClosure φ) ↔ ∃ e, Eval s e ε φ := by
  induction n' generalizing e' with
  | zero => simp [eq_finZeroElim]
  | succ n' ih =>
    simp only [exClosure_succ, eval_ex, ih]
    constructor
    · rintro ⟨e, x, h⟩; exact ⟨vecCons x e, h⟩
    · rintro ⟨e, h⟩; exact ⟨Matrix.vecTail e, Matrix.vecHead e, by simpa using h⟩


-- @@ L404-414 expanded
@[simp]
lemma eval_univItr {k} {e} {φ : Semiformula L ξ (n + k)} :
    Eval s e ε (univItr k φ) ↔ ∀ e', Eval s (Matrix.appendr e' e) ε φ := by
  induction k generalizing e with
  | zero => simp [Matrix.empty_eq]
  | succ k ih =>
    simp only [univItr_succ, eval_all, ih]
    constructor
    · intro h e'
      exact
        Eval.of_eq (h (Matrix.vecTail e') (Matrix.vecHead e'))
          (by rw [← Matrix.appendr_cons, Matrix.cons_head_tail]) rfl
    · intro h e' x; simpa using h (vecCons x e')


-- @@ L416-427 expanded
@[simp]
lemma eval_exItr {k} {e} {φ : Semiformula L ξ (n + k)} :
    Eval s e ε (exItr k φ) ↔ ∃ e', Eval s (Matrix.appendr e' e) ε φ := by
  induction k generalizing e with
  | zero => simp [Matrix.empty_eq]
  | succ k ih =>
    simp only [exItr_succ, eval_ex, ih]
    constructor
    · rintro ⟨e', x, h⟩
      exact ⟨vecCons x e', by simpa using h⟩
    · rintro ⟨e, h⟩
      exact
        ⟨Matrix.vecTail e, Matrix.vecHead e, by rw [← Matrix.appendr_cons, Matrix.cons_head_tail];
          exact h⟩


-- @@ L429-429 verbatim
section «lp_section_4»


-- @@ L431-431 verbatim
variable {ε : ξ → M} {ε₂ : ξ₂ → M}


-- @@ L433-449 expanded
lemma eval_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    Eval s e₂ ε₂ (app ω φ) ↔
      Eval s (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.bvar) (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.fvar)
        φ :=
  by
  induction φ using rec' generalizing n₂ <;>
    simp only [*, Semiterm.val_rew, eval_rel, eval_nrel, rew_rel, rew_nrel,
      LogicalConnective.HomClass.map_top, LogicalConnective.HomClass.map_bot,
      LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or, Rewriting.app_all,
      eval_all, Nat.succ_eq_add_one, Rewriting.app_ex, eval_ex]
  case hall =>
    simp only [Function.comp_def, Rew.q_fvar, Semiterm.val_bShift]
    exact iff_of_eq <| forall_congr fun x ↦ by congr; funext i; cases i using Fin.cases <;> simp
  case hex =>
    simp only [Function.comp_def, Rew.q_fvar, Semiterm.val_bShift]
    exact exists_congr fun x ↦ iff_of_eq <| by congr; funext i; cases i using Fin.cases <;> simp


-- @@ L451-460 expanded
lemma eval_rew_q {ε₂ : ξ₂ → M} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ (n₁ + 1)) :
    Eval s (vecCons x e₂) ε₂ (app ω.q φ) ↔
      Eval s (vecCons x (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.bvar))
        (Semiterm.val s e₂ ε₂ ∘ ω ∘ Semiterm.fvar) φ :=
  by
  simp only [eval_rew, Function.comp_def, Nat.succ_eq_add_one, Rew.q_fvar, Semiterm.val_bShift]
  apply iff_of_eq; congr 2
  · funext x
    cases x using Fin.cases <;> simp


-- @@ L462-465 expanded
lemma eval_map (b : Fin n₁ → Fin n₂) (f : ξ₁ → ξ₂) (e : Fin n₂ → M) (ε : ξ₂ → M)
    (φ : Semiformula L ξ₁ n₁) :
    Eval s e ε (app (Rew.map (L := L) b f) φ) ↔ Eval s (e ∘ b) (ε ∘ f) φ := by
  simp [eval_rew, Function.comp_def]


-- @@ L467-469 expanded
lemma eval_rewrite (f : ξ₁ → Semiterm L ξ₂ n) (φ : Semiformula L ξ₁ n) :
    Eval s e ε₂ (app (Rew.rewrite f) φ) ↔ Eval s e (fun x ↦ (f x).val s e ε₂) φ := by
  simp [eval_rew, Function.comp_def]


-- @@ L471-473 expanded
lemma eval_rewriteMap (f : ξ₁ → ξ₂) (φ : Semiformula L ξ₁ n) :
    Eval s e ε₂ (app (Rew.rewriteMap (L := L) (n := n) f) φ) ↔ Eval s e (fun x ↦ ε₂ (f x)) φ := by
  simp [eval_rew, Function.comp_def]


-- @@ L475-477 expanded
@[simp]
lemma eval_castLE (h : n₁ ≤ n₂) (φ : Semiformula L ξ n₁) :
    Eval s e₂ ε (app (@Rew.castLE L ξ _ _ h) φ) ↔ Eval s (fun x ↦ e₂ (x.castLE h)) ε φ := by
  simp [eval_rew, Function.comp_def]


-- @@ L479-481 expanded
@[simp]
lemma eval_bShift (φ : Semiformula L ξ n) :
    Eval s (vecCons x e) ε (app (@Rew.bShift L ξ n) φ) ↔ Eval s e ε φ := by
  simp [eval_rew, Function.comp_def]


-- @@ L483-485 expanded
lemma eval_bShift' (φ : Semiformula L ξ n) :
    Eval s e' ε (app (@Rew.bShift L ξ n) φ) ↔ Eval s (e' ·.succ) ε φ := by
  simp [eval_rew, Function.comp_def]


-- @@ L487-489 expanded
lemma eval_substs {k} (w : Fin k → Semiterm L ξ n) (φ : Semiformula L ξ k) :
    Eval s e ε (LO.FirstOrder.Rewriting.substitute φ w) ↔ Eval s (fun i ↦ (w i).val s e ε) ε φ := by
  simp [eval_rew, Function.comp_def]


-- @@ L491-493 verbatim
@[simp] lemma eval_emb {ε : ξ → M} (φ : Semiformula L Empty n) :
    Eval s e ε (Rewriting.embedding (ξ := ξ) φ : Semiformula L ξ n) ↔ Eval s e Empty.elim φ := by
  simp only [eval_rew]; apply iff_of_eq; congr; funext x; contradiction


-- @@ L495-498 expanded
@[simp]
lemma eval_empty [h : IsEmpty o] (φ : Formula L o) :
    Eval s e ε (app (@Rew.empty L o _ ξ n) φ) ↔ Eval s ![] h.elim φ :=
  by
  simp only [eval_rew, Matrix.empty_eq]
  apply iff_of_eq; congr; funext x; exact h.elim' x


-- @@ L500-502 expanded
@[simp]
lemma eval_toS {e : Fin n → M} {ε} (φ : Formula L (Fin n)) :
    Eval s e ε (app (@Rew.toS L n) φ) ↔ Eval s ![] e φ := by
  simp [Rew.toS, eval_rew, Function.comp_def, Matrix.empty_eq]


-- @@ L504-506 expanded
lemma eval_embSubsts {ξ} {ε : ξ → M} {k} (w : Fin k → Semiterm L ξ n) (σ : Semisentence L k) :
    Eval s e ε (app (@Rew.embSubsts L ξ n k w) σ) ↔ Evalb s (fun x ↦ (w x).val s e ε) σ := by
  simp [eval_rew, Function.comp_def, Empty.eq_elim]


-- @@ L508-508 verbatim
section «lp_section_5»


-- @@ L510-510 verbatim
variable (ε : ℕ → M)


-- @@ L512-518 expanded
@[simp]
lemma eval_free (φ : SyntacticSemiformula L (n + 1)) :
    Eval s e (cases a ε) (app (@Rew.free L n) φ) ↔ Eval s (vecConsLast e a) ε φ :=
  by
  simp only [eval_rew, Function.comp_def, Nat.succ_eq_add_one]
  apply iff_of_eq
  congr
  funext x
  cases x using Fin.lastCases <;> simp


-- @@ L520-521 expanded
@[simp]
lemma eval_shift (φ : SyntacticSemiformula L n) :
    Eval s e (cases a ε) (app (@Rew.shift L n) φ) ↔ Eval s e ε φ := by
  simp [eval_rew, Function.comp_def]


-- @@ L523-523 verbatim
end «lp_section_5»


-- @@ L525-552 verbatim
lemma eval_iff_of_funEqOn [DecidableEq ξ] (φ : Semiformula L ξ n) (h :
    Function.funEqOn φ.FVar? ε ε') :
    Eval s e ε φ ↔ Eval s e ε' φ := by
  induction φ using Semiformula.rec'
  case hverum => simp
  case hfalsum => simp
  case hrel k r v =>
    simp only [eval_rel]; apply iff_of_eq; congr
    funext i
    exact Semiterm.val_eq_of_funEqOn (v i) (fun x hx ↦ h x (fvar?_rel.mpr ⟨i, hx⟩))
  case hnrel k r v =>
    simp only [eval_nrel]; apply iff_of_eq; congr
    funext i
    exact Semiterm.val_eq_of_funEqOn (v i) (fun x hx ↦ h x (fvar?_nrel.mpr ⟨i, hx⟩))
  case hand φ ψ ihp ihq =>
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]; apply and_congr
    · exact ihp fun x hx ↦ h x (by simp [hx])
    · exact ihq fun x hx ↦ h x (by simp [hx])
  case hor φ ψ ihp ihq =>
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]; apply or_congr
    · exact ihp fun x hx ↦ h x (by simp [hx])
    · exact ihq fun x hx ↦ h x (by simp [hx])
  case hall φ ih =>
    simp only [eval_all, Nat.succ_eq_add_one]; apply forall_congr'; intro x
    exact ih (fun x hx ↦ h _ <| by simp only [fvar?_all]; exact hx)
  case hex φ ih =>
    simp only [eval_ex, Nat.succ_eq_add_one]; apply exists_congr; intro x
    exact ih (fun x hx ↦ h _ <| by simp only [fvar?_ex]; exact hx)


-- @@ L554-574 expanded
lemma eval_toEmpty [DecidableEq ξ] {φ : Semiformula L ξ n} (hp : φ.freeVariables = ∅) :
    Eval s e f φ ↔ Evalb s e (φ.toEmpty hp) :=
  by
  induction φ using Semiformula.rec'
  case hrel k R v =>
    simp only [eval_rel, Semiformula.toEmpty]
    apply iff_of_eq; congr; funext i
    rw [Semiterm.val_toEmpty]
  case hnrel k R v =>
    simp only [eval_nrel, Semiformula.toEmpty]
    apply iff_of_eq; congr; funext i
    rw [Semiterm.val_toEmpty]
  case hverum => simp
  case hfalsum => simp
  case hand φ ψ ihp ihq =>
    simp [ihp (e := e) (by simp [by simpa [Finset.union_eq_empty] using hp]),
      ihq (e := e) (by simp [by simpa [Finset.union_eq_empty] using hp])]
  case hor φ ψ ihp ihq =>
    simp [ihp (e := e) (by simp [by simpa [Finset.union_eq_empty] using hp]),
      ihq (e := e) (by simp [by simpa [Finset.union_eq_empty] using hp])]
  case hall φ ih => simp [fun x ↦ ih (e := (vecCons x e)) (by simpa using hp)]
  case hex φ ih => simp [fun x ↦ ih (e := (vecCons x e)) (by simpa using hp)]


-- @@ L576-586 verbatim
lemma eval_close {ε} (φ : SyntacticFormula L) :
    Evalf s ε (∀∀φ) ↔ ∀ f, Evalf s f φ := by
  simp only [close, eval_univClosure, eval_rew, Function.comp_def, Matrix.empty_eq]
  constructor
  · intro h f
    refine (eval_iff_of_funEqOn φ ?_).mp (h (fun x ↦ f x))
    intro x hx; simp [Rew.fixitr_fvar, lt_fvSup_of_fvar? hx]
  · intro h f
    refine (eval_iff_of_funEqOn φ ?_).mp (h (fun x ↦ if hx :
        x < φ.fvSup then f ⟨x, by simp [hx]⟩ else ε 0))
    intro x hx; simp [Rew.fixitr_fvar, lt_fvSup_of_fvar? hx]


-- @@ L588-591 verbatim
lemma eval_close₀ [Nonempty M] (φ : SyntacticFormula L) :
    Evalb s ![] (∀∀₀φ) ↔ ∀ f, Evalf s f φ := by
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  simp [Semiformula.close₀, ←eval_toEmpty (f := default), eval_close]


-- @@ L593-593 verbatim
end «lp_section_4»


-- @@ L595-595 verbatim
end Semiformula


-- @@ L597-597 verbatim
namespace Structure


-- @@ L599-599 verbatim
section «lp_section_6»


-- @@ L601-601 verbatim
open Semiformula

-- @@ L602-602 verbatim
variable [s : Structure L M] (Θ : M ≃ N)


-- @@ L604-605 verbatim
lemma ofEquiv_rel (r : L.Rel k) (v : Fin k → N) :
    (Structure.ofEquiv Θ).rel r v ↔ Structure.rel r (Θ.symm ∘ v) := iff_of_eq rfl


-- @@ L607-624 expanded
lemma eval_ofEquiv_iff :
    ∀ {n} {e : Fin n → N} {ε : ξ → N} {φ : Semiformula L ξ n},
      Eval (ofEquiv Θ) e ε φ ↔ Eval s (Θ.symm ∘ e) (Θ.symm ∘ ε) φ
  | _, e, ε, ⊤ => by simp
  | _, e, ε, ⊥ => by simp
  | _, e, ε, .rel r v => by
    simp [Function.comp_def, eval_rel, ofEquiv_rel Θ, Structure.ofEquiv_val Θ]
  | _, e, ε, .nrel r v => by
    simp [Function.comp_def, eval_nrel, ofEquiv_rel Θ, Structure.ofEquiv_val Θ]
  | _, e, ε, Wedge.wedge φ ψ => by simp [eval_ofEquiv_iff (φ := φ), eval_ofEquiv_iff (φ := ψ)]
  | _, e, ε, Vee.vee φ ψ => by simp [eval_ofEquiv_iff (φ := φ), eval_ofEquiv_iff (φ := ψ)]
  | _, e, ε, UnivQuantifier.univ φ => by simp only [eval_all, Nat.succ_eq_add_one];
    exact
      ⟨fun h x => by simpa [Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp (h (Θ x)), fun h x =>
        eval_ofEquiv_iff.mpr (by simpa [Matrix.comp_vecCons''] using h (Θ.symm x))⟩
  | _, e, ε, ExQuantifier.ex φ => by simp only [eval_ex, Nat.succ_eq_add_one];
    exact
      ⟨by rintro ⟨x, h⟩; exists Θ.symm x; simpa [Matrix.comp_vecCons''] using eval_ofEquiv_iff.mp h,
        by rintro ⟨x, h⟩; exists Θ x; apply eval_ofEquiv_iff.mpr;
        simpa [Matrix.comp_vecCons''] using h⟩


-- @@ L626-629 verbatim
lemma evalf_ofEquiv_iff {ε : ξ → N} {φ : Formula L ξ} :
    Evalf (ofEquiv Θ) ε φ ↔
        Evalf s (Θ.symm ∘ ε) φ := by
  simpa using eval_ofEquiv_iff (Θ := Θ) (ε := ε) (φ := φ) (e := ![])


-- @@ L631-631 verbatim
end «lp_section_6»


-- @@ L633-633 verbatim
end Structure


-- @@ L635-636 verbatim
instance : Semantics (SyntacticFormula L) (Struc L) where
  Realize := fun str φ ↦ ∀ f, Semiformula.Evalf str.struc f φ


-- @@ L638-638 verbatim
instance : Semantics.Top (Struc L) := ⟨by simp [Semantics.Realize]⟩


-- @@ L640-640 verbatim
instance : Semantics.Bot (Struc L) := ⟨by simp [Semantics.Realize]⟩


-- @@ L642-646 verbatim
instance : Semantics.And (Struc L) := ⟨by
  intro 𝓜 φ ψ
  constructor
  · intro h; exact ⟨fun f ↦ (h f).left, fun f ↦ (h f).right⟩
  · rintro ⟨hp, hq⟩ f; exact ⟨hp f, hq f⟩ ⟩


-- @@ L648-648 verbatim
section «lp_section_7»


-- @@ L650-650 verbatim
variable (M : Type*) [Nonempty M] [s : Structure L M] {T U : Theory L}


-- @@ L652-653 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Models : SyntacticFormula L → Prop := Semantics.Realize s.toStruc


-- @@ L655-656 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊧ₘ " => Models


-- @@ L658-659 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Models₀ (σ : Sentence L) : Prop :=
  Models M (↑σ : SyntacticFormula L)


-- @@ L661-662 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊧ₘ₀ " => Models₀


-- @@ L664-665 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ModelsTheory (T : Theory L) : Prop := Semantics.RealizeSet s.toStruc T


-- @@ L667-668 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊧ₘ* " => ModelsTheory


-- @@ L670-671 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Realize (M : Type*) [s : Structure L M] : Formula L M → Prop := Semiformula.Evalf s id


-- @@ L673-674 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊧ₘᵣ " => Realize


-- @@ L676-677 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Consequence (T : Theory L) (φ : SyntacticFormula L) : Prop :=
  Consequence (SmallStruc L) T φ


-- @@ L679-680 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:45 " ⊨ " => Consequence


-- @@ L682-683 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Satisfiable (T : Theory L) : Prop := Semantics.Satisfiable (SmallStruc L) T


-- @@ L685-685 verbatim
variable {M}


-- @@ L687-688 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma modelsTheory_iff_modelsTheory_s : ModelsTheory M T ↔ RealizeSet s.toStruc T := by rfl


-- @@ L690-690 expanded
lemma models_def {φ} : (Models M φ) = ∀ f, Semiformula.Evalf s f φ :=
  rfl


-- @@ L692-692 expanded
lemma models_iff {φ} : Models M φ ↔ ∀ f, Semiformula.Evalf s f φ := by simp [models_def]


-- @@ L694-694 expanded
lemma models₀_iff {σ : Sentence L} : Models₀ M σ ↔ Semiformula.Evalb s ![] σ := by simp [models_iff]


-- @@ L696-698 expanded
lemma models_iff₀ {φ} : Models M φ ↔ Semiformula.Evalb s ![] ∀∀₀φ :=
  by
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  simp [models_def, Semiformula.eval_close₀]


-- @@ L700-700 expanded
lemma modelsTheory_iff : ModelsTheory M T ↔ (∀ {φ}, φ ∈ T → Models M φ) :=
  Semantics.realizeSet_iff


-- @@ L702-702 verbatim
variable (M T)


-- @@ L704-705 expanded
lemma _root_.LO.FirstOrder.Theory.models [ModelsTheory M T] {φ} (hp : φ ∈ T) : Models M φ :=
  Semantics.realizeSet_iff.mp inferInstance hp


-- @@ L707-707 verbatim
variable {M T}


-- @@ L709-710 expanded
lemma models_iff_models {φ} : Models M φ ↔ Realize s.toStruc φ :=
  of_eq rfl


-- @@ L712-714 expanded
lemma consequence_iff {φ} :
    Consequence (Struc.{v, u} L) T φ ↔
      (∀ (M : Type v) [Nonempty M] [Structure L M], ModelsTheory M T → Models M φ) :=
  ⟨fun h _ _ _ hT ↦ h hT, fun h s hT ↦ h s.Dom hT⟩


-- @@ L716-719 expanded
lemma consequence_iff' {φ} :
    Consequence (Struc.{v, u} L) T φ ↔
      (∀ (M : Type v) [Nonempty M] [Structure L M] [ModelsTheory M T], Models M φ) :=
  ⟨fun h _ _ s _ => Semantics.consequence_iff'.mp h s.toStruc, fun h s hs =>
    @h s.Dom s.nonempty s.struc hs⟩


-- @@ L721-723 expanded
lemma valid_iff {φ} :
    Semantics.Valid (Struc.{v, u} L) φ ↔ ∀ (M : Type v) [Nonempty M] [Structure L M], Models M φ :=
  ⟨fun hσ _ _ s ↦ @hσ s.toStruc, fun h s ↦ h s.Dom⟩


-- @@ L725-733 expanded
lemma satisfiable_iff :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔
      ∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M), ModelsTheory M T :=
  ⟨by
    rintro ⟨s, hs⟩
    exact ⟨s.Dom, s.nonempty, s.struc, hs⟩,
    by
    rintro ⟨M, i, s, hT⟩
    exact ⟨s.toStruc, hT⟩⟩


-- @@ L735-738 expanded
lemma unsatisfiable_iff :
    ¬Semantics.Satisfiable (Struc.{v, u} L) T ↔
      ∀ (M : Type v) (_ : Nonempty M) (_ : Structure L M), ¬ModelsTheory M T :=
  by simpa using satisfiable_iff.not


-- @@ L740-741 expanded
lemma satisfiable_intro (M : Type v) [Nonempty M] [s : Structure L M] (h : ModelsTheory M T) :
    Semantics.Satisfiable (Struc.{v, u} L) T :=
  ⟨s.toStruc, h⟩


-- @@ L743-745 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def ModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) : Type v :=
  Classical.choose (satisfiable_iff.mp h)


-- @@ L747-749 verbatim
noncomputable instance nonemptyModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    Nonempty (ModelOfSat h) := by
  choose i _ _ using Classical.choose_spec (satisfiable_iff.mp h); exact i


-- @@ L751-755 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def StructureModelOfSatAux (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    { _s : Structure L (ModelOfSat h) // ModelsTheory (ModelOfSat h) T } :=
  by
  choose _ s h using Classical.choose_spec (satisfiable_iff.mp h)
  exact ⟨s, h⟩


-- @@ L757-758 verbatim
noncomputable instance StructureModelOfSat (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    Structure L (ModelOfSat h) := StructureModelOfSatAux h


-- @@ L760-761 expanded
lemma _root_.LO.FirstOrder.ModelOfSat.models (h : Semantics.Satisfiable (Struc.{v, u} L) T) :
    ModelsTheory (ModelOfSat h) T :=
  (StructureModelOfSatAux h).prop


-- @@ L763-780 expanded
lemma consequence_iff_unsatisfiable {φ : SyntacticFormula L} :
    Consequence (Struc.{v, u} L) T φ ↔
      ¬Semantics.Satisfiable (Struc.{v, u} L) (insert (Tilde.tilde ∀∀φ) T) :=
  by
  let σ := Tilde.tilde ∀∀₀φ
  have : Tilde.tilde ∀∀φ = Rewriting.embedding σ := by simp [Semiformula.close₀, σ]
  rw [this]
  constructor
  · intro h
    apply unsatisfiable_iff.mpr
    intro M _ s; simp only [Semantics.RealizeSet.insert_iff, models₀_iff, not_and']
    intro hT; simpa [σ] using models_iff₀.mp (h hT)
  · intro h; apply consequence_iff.mpr
    intro M _ s hT
    have : ¬(Semiformula.Evalb s ![]) σ :=
      by
      have := by
        simpa only [Semantics.RealizeSet.insert_iff, not_and', models₀_iff] using
          unsatisfiable_iff.mp h M inferInstance s
      exact this hT
    apply models_iff₀.mpr (by simpa [σ] using this)


-- @@ L782-782 verbatim
end «lp_section_7»


-- @@ L784-784 verbatim
namespace Semiformula


-- @@ L786-786 verbatim
variable {L₁ L₂ : Language} {Φ : L₁ →ᵥ L₂}


-- @@ L788-788 verbatim
section «lp_section_8»

-- @@ L789-789 verbatim
variable {M : Type u} {s₂ : Structure L₂ M} {n} {e : Fin n → M} {ε : ξ → M}


-- @@ L791-794 verbatim
lemma eval_lMap {φ : Semiformula L₁ ξ n} :
    Eval s₂ e ε (lMap Φ φ) ↔ Eval (s₂.lMap Φ) e ε φ :=
  by induction φ using rec' <;>
    simp [*, Semiterm.val_lMap, lMap_rel, lMap_nrel, eval_rel, eval_nrel]


-- @@ L796-798 expanded
lemma models_lMap [Nonempty M] {φ : SyntacticFormula L₁} :
    Realize s₂.toStruc (lMap Φ φ) ↔ Realize (s₂.lMap Φ).toStruc φ := by
  simp [Semantics.Realize, Evalf, eval_lMap]


-- @@ L800-800 verbatim
end «lp_section_8»


-- @@ L802-802 verbatim
end Semiformula


-- @@ L804-811 expanded
lemma lMap_models_lMap {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂} {T : Theory L₁}
    {φ : SyntacticFormula L₁} (h : Consequence (Struc.{v, u} L₁) T φ) :
    Consequence (Struc.{v, u} L₂) (T.lMap Φ) (Semiformula.lMap Φ φ) :=
  by
  intro s hM
  have : Realize (s.struc.lMap Φ).toStruc φ :=
    h ⟨fun _ hq => Semiformula.models_lMap.mp <| hM.realize _ (Set.mem_image_of_mem _ hq)⟩
  exact Semiformula.models_lMap.mpr this


-- @@ L813-813 verbatim
namespace ModelsTheory


-- @@ L815-815 verbatim
variable (M) [Nonempty M] [Structure L M]


-- @@ L817-817 expanded
lemma models {T : Theory L} [ModelsTheory M T] {φ} (h : φ ∈ T) : Models M φ :=
  Semantics.RealizeSet.realize _ h


-- @@ L819-819 verbatim
variable {M}


-- @@ L821-822 expanded
lemma of_ss {T U : Theory L} (h : ModelsTheory M U) (ss : T ⊆ U) : ModelsTheory M T :=
  Semantics.RealizeSet.of_subset h ss


-- @@ L824-825 expanded
@[simp]
lemma add_iff {T U : Theory L} : ModelsTheory M (T + U) ↔ ModelsTheory M T ∧ ModelsTheory M U := by
  simp [Theory.add_def]


-- @@ L827-828 expanded
instance add (T U : Theory L) [ModelsTheory M T] [ModelsTheory M U] : ModelsTheory M (T + U) :=
  ModelsTheory.add_iff.mpr ⟨inferInstance, inferInstance⟩


-- @@ L830-830 verbatim
end ModelsTheory


-- @@ L832-832 verbatim
namespace Theory


-- @@ L834-834 verbatim
variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂}


-- @@ L836-836 verbatim
variable {M : Type u} [Nonempty M] [s₂ : Structure L₂ M]


-- @@ L838-840 verbatim
lemma modelsTheory_onTheory₁ {T₁ : Theory L₁} :
    ModelsTheory (s := s₂) M (T₁.lMap Φ) ↔ ModelsTheory (s := s₂.lMap Φ) M T₁ :=
  by simp [Semiformula.models_lMap, Theory.lMap, @modelsTheory_iff (T := T₁)]


-- @@ L842-842 verbatim
end Theory


-- @@ L844-844 verbatim
namespace Structure


-- @@ L846-846 verbatim
variable (L)


-- @@ L848-849 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev theory (M : Type u) [Nonempty M] [s : Structure L M] : Theory L := Semantics.theory s.toStruc


-- @@ L851-851 verbatim
variable {L} {M : Type u} [Nonempty M] [Structure L M]


-- @@ L853-853 expanded
@[simp]
lemma mem_theory_iff {σ} : σ ∈ theory L M ↔ Models M σ := by rfl


-- @@ L855-856 expanded
lemma subset_of_models : T ⊆ theory L M ↔ ModelsTheory M T :=
  ⟨fun h ↦ ⟨fun _ hσ ↦ h hσ⟩, fun h _ hσ ↦ h.all_realize hσ⟩


-- @@ L858-858 verbatim
end Structure


-- @@ L860-860 verbatim
end FirstOrder


-- @@ L862-862 verbatim
end LO
