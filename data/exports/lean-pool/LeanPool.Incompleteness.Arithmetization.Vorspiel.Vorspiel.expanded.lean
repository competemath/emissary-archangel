/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.Model
import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.CobhamR0
import LeanPool.Incompleteness.Foundation.FirstOrder.Arith.PeanoMinus
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Soundness
import Mathlib.Order.ConditionallyCompleteLattice.Basic


-- @@ L14-14 verbatim
/-! # Vorspiel -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
instance [Zero α] : Nonempty α := ⟨0⟩


-- @@ L21-22 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "exp " x:90 => Exp.exp x


-- @@ L24-24 verbatim
namespace Matrix


-- @@ L26-28 expanded
lemma _root_.Matrix.forall_vecCons_iff {n : ℕ} (φ : (Fin (n + 1) → α) → Prop) :
    (∀ v, φ v) ↔ (∀ a, ∀ v, φ (vecCons a v)) :=
  ⟨fun h a v ↦ h (vecCons a v), fun h v ↦ by simpa [← eq_vecCons v] using h (v 0) (v ∘ Fin.succ)⟩


-- @@ L30-33 expanded
lemma comp_vecCons₂' (g : β → γ) (f : α → β) (a : α) (s : Fin n → α) :
    (fun x ↦ g <| f <| (vecCons a s) x) = (vecCons (g (f a)) fun i ↦ g <| f <| s i) :=
  by
  funext x
  cases x using Fin.cases <;> simp


-- @@ L35-35 verbatim
end Matrix


-- @@ L37-37 verbatim
namespace Set


-- @@ L39-40 verbatim
@[simp 1100] lemma subset_union_three₁ (s t u : Set α) : s ⊆ s ∪ t ∪ u :=
  Set.subset_union_of_subset_left (by simp) _


-- @@ L42-43 verbatim
@[simp] lemma subset_union_three₂ (s t u : Set α) : t ⊆ s ∪ t ∪ u :=
  Set.subset_union_of_subset_left (by simp) _


-- @@ L45-46 verbatim
@[simp 1100] lemma subset_union_three₃ (s t u : Set α) : u ⊆ s ∪ t ∪ u :=
  Set.subset_union_of_subset_right (by rfl) _


-- @@ L48-48 verbatim
end Set


-- @@ L50-50 verbatim
namespace Matrix


-- @@ L52-61 verbatim
lemma fun_eq_vec₃ {v : Fin 3 → α} : v = ![v 0, v 1, v 2] := by
  funext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
    cases x using Fin.cases with
    | zero => rfl
    | succ x =>
      rw [Fin.eq_zero x]
      rfl


-- @@ L63-75 verbatim
lemma fun_eq_vec₄ {v : Fin 4 → α} : v = ![v 0, v 1, v 2, v 3] := by
  funext x
  cases x using Fin.cases with
  | zero => rfl
  | succ x =>
    cases x using Fin.cases with
    | zero => rfl
    | succ x =>
      cases x using Fin.cases with
      | zero => rfl
      | succ x =>
        rw [Fin.eq_zero x]
        rfl


-- @@ L77-79 expanded
@[simp]
lemma cons_app_four {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ → α) : (vecCons a s) 4 = s 3 :=
  rfl


-- @@ L81-83 expanded
@[simp]
lemma cons_app_five {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ → α) :
    (vecCons a s) 5 = s 4 :=
  rfl


-- @@ L85-87 expanded
@[simp]
lemma cons_app_six {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ → α) :
    (vecCons a s) 6 = s 5 :=
  rfl


-- @@ L89-91 expanded
@[simp]
lemma cons_app_seven {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ → α) :
    (vecCons a s) 7 = s 6 :=
  rfl


-- @@ L93-96 expanded
@[simp]
lemma cons_app_eight {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ.succ.succ → α) :
    (vecCons a s) 8 = s 7 :=
  rfl


-- @@ L98-99 expanded
lemma eq_vecCons' (s : Fin (n + 1) → C) : vecCons (s 0) (s ·.succ) = s :=
  funext <| Fin.cases (by simp) (by simp)


-- @@ L101-101 verbatim
end Matrix


-- @@ L103-109 verbatim
lemma forall_fin_iff_zero_and_forall_succ {P : Fin (k + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i :
    Fin k, P i.succ :=
  ⟨fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩, by
    rintro ⟨hz, hs⟩ i
    cases i using Fin.cases with
    | zero => exact hz
    | succ i => exact hs i⟩


-- @@ L111-119 verbatim
lemma exists_fin_iff_zero_or_exists_succ {P : Fin (k + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i :
    Fin k, P i.succ :=
  ⟨by rintro ⟨i, hi⟩
      cases i using Fin.cases
      · left; exact hi
      · right; exact ⟨_, hi⟩,
   by rintro (hz | ⟨i, h⟩)
      · exact ⟨0, hz⟩
      · exact ⟨_, h⟩⟩


-- @@ L121-125 expanded
lemma forall_vec_iff_forall_forall_vec {P : (Fin (k + 1) → α) → Prop} :
    (∀ v : Fin (k + 1) → α, P v) ↔ ∀ x, ∀ v : Fin k → α, P (vecCons x v) :=
  by
  constructor
  · intro h x v; exact h _
  · intro h v; simpa using h (v 0) (v ·.succ)


-- @@ L127-131 expanded
lemma exists_vec_iff_exists_exists_vec {P : (Fin (k + 1) → α) → Prop} :
    (∃ v : Fin (k + 1) → α, P v) ↔ ∃ x, ∃ v : Fin k → α, P (vecCons x v) :=
  by
  constructor
  · rintro ⟨v, h⟩; exact ⟨v 0, (v ·.succ), by simpa using h⟩
  · rintro ⟨x, v, h⟩; exact ⟨_, h⟩


-- @@ L133-144 expanded
lemma exists_le_vec_iff_exists_le_exists_vec [LE α] {P : (Fin (k + 1) → α) → Prop}
    {f : Fin (k + 1) → α} : (∃ v ≤ f, P v) ↔ ∃ x ≤ f 0, ∃ v ≤ (f ·.succ), P (vecCons x v) :=
  by
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w 0, hw 0, (w ·.succ), fun i ↦ hw i.succ, by simpa using h⟩
  · rintro ⟨x, hx, v, hv, h⟩
    refine ⟨vecCons x v, ?_, h⟩
    intro i
    cases i using Fin.cases with
    | zero => exact hx
    | succ i => exact hv i


-- @@ L146-157 expanded
lemma forall_le_vec_iff_forall_le_forall_vec [LE α] {P : (Fin (k + 1) → α) → Prop}
    {f : Fin (k + 1) → α} : (∀ v ≤ f, P v) ↔ ∀ x ≤ f 0, ∀ v ≤ (f ·.succ), P (vecCons x v) :=
  by
  constructor
  · intro h x hx v hv
    refine h (vecCons x v) ?_
    intro i
    cases i using Fin.cases with
    | zero => exact hx
    | succ i => exact hv i
  · intro h v hv
    simpa using h (v 0) (hv 0) (v ·.succ) (hv ·.succ)


-- @@ L159-159 verbatim
instance instToStringEmptyOfVorspiel : ToString Empty := ⟨Empty.elim⟩


-- @@ L161-164 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Hash (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  hash : α → α → α


-- @@ L166-167 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:80 " # " => Hash.hash


-- @@ L169-172 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Length (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  length : α → α


-- @@ L174-174 verbatim
namespace Length


-- @@ L176-177 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped notation "‖" x "‖" => Length.length x


-- @@ L179-179 verbatim
end Length


-- @@ L181-181 verbatim
namespace LO


-- @@ L183-183 verbatim
namespace Polarity


-- @@ L185-185 verbatim
variable {α : Type*} [SigmaSymbol α] [PiSymbol α]


-- @@ L187-190 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def coe : Polarity → α
  | SigmaSymbol.sigma => SigmaSymbol.sigma
  | PiSymbol.pi => PiSymbol.pi


-- @@ L192-192 verbatim
instance : Coe Polarity α := ⟨Polarity.coe⟩


-- @@ L194-194 expanded
@[simp]
lemma coe_sigma : ((SigmaSymbol.sigma : Polarity) : α) = SigmaSymbol.sigma :=
  rfl


-- @@ L196-196 expanded
@[simp]
lemma coe_pi : ((PiSymbol.pi : Polarity) : α) = PiSymbol.pi :=
  rfl


-- @@ L198-198 verbatim
end Polarity


-- @@ L200-200 verbatim
namespace SigmaPiDelta


-- @@ L202-203 verbatim
@[simp] lemma alt_coe (Γ : Polarity) : SigmaPiDelta.alt Γ = (Γ.alt : SigmaPiDelta) := by
  rcases Γ <;> rfl


-- @@ L205-205 verbatim
end SigmaPiDelta


-- @@ L207-207 verbatim
namespace FirstOrder


-- @@ L209-209 verbatim
namespace Semiterm


-- @@ L211-215 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fvarList : Semiterm L ξ n → List ξ
  | #_       => []
  | &x       => [x]
  | func _ v => List.flatten <| Matrix.toList fun i ↦ fvarList (v i)


-- @@ L217-218 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fvarEnum [DecidableEq ξ] (t : Semiterm L ξ n) : ξ → ℕ := t.fvarList.idxOf


-- @@ L220-222 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fvarEnumInv [Inhabited ξ] (t : Semiterm L ξ n) : ℕ → ξ :=
  fun i ↦ if hi : i < t.fvarList.length then t.fvarList.get ⟨i, hi⟩ else default


-- @@ L224-227 verbatim
lemma fvarEnumInv_fvarEnum [DecidableEq ξ] [Inhabited ξ] {t : Semiterm L ξ n} {x : ξ} (hx :
    x ∈ t.fvarList) :
    fvarEnumInv t (fvarEnum t x) = x := by
  simp [fvarEnumInv, fvarEnum, List.idxOf_lt_length_of_mem hx, List.getElem_idxOf]


-- @@ L229-238 verbatim
lemma «mem_fvarList_iff_fvar?» [DecidableEq ξ] {t : Semiterm L ξ n} :
    x ∈ t.fvarList ↔ t.FVar? x:= by
  induction t with
  | bvar _ =>
    simp only [fvarList, List.not_mem_nil, fvar?_bvar]
  | fvar y =>
    simp only [fvarList, List.mem_singleton, fvar?_fvar, eq_comm]
  | func _ v ih =>
    simp only [fvarList, List.mem_flatten, Matrix.mem_toList_iff, fvar?_func]
    simp_all


-- @@ L240-240 verbatim
end Semiterm


-- @@ L242-242 verbatim
namespace Semiformula


-- @@ L244-253 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def fvarList {n : ℕ} : Semiformula L ξ n → List ξ
  | ⊤ => []
  | ⊥ => []
  | rel _ v => List.flatten <| Matrix.toList fun i ↦ (v i).fvarList
  | nrel _ v => List.flatten <| Matrix.toList fun i ↦ (v i).fvarList
  | Wedge.wedge p q => p.fvarList ++ q.fvarList
  | Vee.vee p q => p.fvarList ++ q.fvarList
  | UnivQuantifier.univ p => p.fvarList
  | ExQuantifier.ex p => p.fvarList


-- @@ L255-256 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fvarEnum [DecidableEq ξ] (φ : Semiformula L ξ n) : ξ → ℕ := φ.fvarList.idxOf


-- @@ L258-260 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fvarEnumInv [Inhabited ξ] (φ : Semiformula L ξ n) : ℕ → ξ :=
  fun i ↦ if hi : i < φ.fvarList.length then φ.fvarList.get ⟨i, hi⟩ else default


-- @@ L262-265 verbatim
lemma fvarEnumInv_fvarEnum [DecidableEq ξ] [Inhabited ξ] {φ : Semiformula L ξ n} {x : ξ} (hx :
    x ∈ φ.fvarList) :
    fvarEnumInv φ (fvarEnum φ x) = x := by
  simp [fvarEnumInv, fvarEnum, List.idxOf_lt_length_of_mem hx, List.getElem_idxOf]


-- @@ L267-269 verbatim
lemma «mem_fvarList_iff_fvar?» [DecidableEq ξ] {φ : Semiformula L ξ n} :
    x ∈ φ.fvarList ↔ φ.FVar? x := by
  induction φ using rec' <;> simp [fvarList, Semiterm.mem_fvarList_iff_fvar?, *]


-- @@ L271-271 verbatim
end Semiformula


-- @@ L273-273 verbatim
namespace Arith


-- @@ L275-276 verbatim
attribute [simp] Semiformula.eval_substs Semiformula.eval_embSubsts
  Matrix.vecHead Matrix.vecTail


-- @@ L278-278 verbatim
section «lp_section_1»


-- @@ L280-280 verbatim
variable [ToString μ]


-- @@ L282-282 verbatim
open Semiterm Semiformula


-- @@ L284-291 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def termToStr : Semiterm oRing μ n → String
  | #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  | func Language.One.one _ => "1"
  | func Language.Add.add v => "(" ++ termToStr (v 0) ++ " + " ++ termToStr (v 1) ++ ")"
  | func Language.Mul.mul v => "(" ++ termToStr (v 0) ++ " \\cdot " ++ termToStr (v 1) ++ ")"


-- @@ L293-293 expanded
instance : Repr (Semiterm oRing μ n) :=
  ⟨fun t _ => termToStr t⟩


-- @@ L295-295 expanded
instance : ToString (Semiterm oRing μ n) :=
  ⟨termToStr⟩


-- @@ L297-318 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def formulaToStr : ∀ {n}, Semiformula oRing μ n → String
  | _, ⊤ => "\\top"
  | _, ⊥ => "\\bot"
  | _, rel Language.Eq.eq v => termToStr (v 0) ++ " = " ++ termToStr (v 1)
  | _, rel Language.LT.lt v => termToStr (v 0) ++ " < " ++ termToStr (v 1)
  | _, nrel Language.Eq.eq v => termToStr (v 0) ++ " \\not = " ++ termToStr (v 1)
  | _, nrel Language.LT.lt v => termToStr (v 0) ++ " \\not < " ++ termToStr (v 1)
  | _, Wedge.wedge φ ψ => "[" ++ formulaToStr φ ++ "]" ++ " \\land " ++ "[" ++ formulaToStr ψ ++ "]"
  | _, Vee.vee φ ψ => "[" ++ formulaToStr φ ++ "]" ++ " \\lor " ++ "[" ++ formulaToStr ψ ++ "]"
  | n, UnivQuantifier.univ (Arrow.arrow (rel Language.LT.lt v) φ) =>
    "(\\forall x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr φ ++
      "]"
  | n, ExQuantifier.ex (Wedge.wedge (rel Language.LT.lt v) φ) =>
    "(\\exists x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr φ ++
      "]"
  | n, UnivQuantifier.univ φ =>
    "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr φ ++ "]"
  | n, ExQuantifier.ex φ => "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr φ ++ "]"


-- @@ L320-320 expanded
instance : Repr (Semiformula oRing μ n) :=
  ⟨fun t _ => formulaToStr t⟩


-- @@ L322-322 expanded
instance : ToString (Semiformula oRing μ n) :=
  ⟨formulaToStr⟩


-- @@ L324-324 verbatim
end «lp_section_1»


-- @@ L326-326 verbatim
section «lp_section_2»


-- @@ L328-328 expanded
variable {T : Theory oRing} [WeakerThan eqAxiom T]


-- @@ L330-330 expanded
variable (M : Type*) [ORingStruc M] [ModelsTheory M T]


-- @@ L332-333 expanded
instance indScheme_of_indH (Γ n) [ModelsTheory M ((indH Γ) n)] :
    ModelsTheory M (Theory.indScheme oRing (Arith.Hierarchy Γ n)) :=
  models_indScheme_of_models_indH Γ n


-- @@ L335-335 verbatim
end «lp_section_2»


-- @@ L337-337 verbatim
end Arith


-- @@ L339-339 verbatim
section «lp_section_3»


-- @@ L341-341 verbatim
variable {L : Language}


-- @@ L343-343 verbatim
namespace Semiformula


-- @@ L345-345 verbatim
variable {M : Type*} {s : Structure L M}


-- @@ L347-347 verbatim
variable {n : ℕ} {ε : ξ → M}


-- @@ L349-351 verbatim
@[simp] lemma eval_operator₃ {o : Operator L 3} {t₁ t₂ t₃ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂, t₃]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε, t₃.val s e ε] := by
  simp [eval_operator, Matrix.comp_vecCons', Matrix.constant_eq_singleton]


-- @@ L353-356 verbatim
@[simp] lemma eval_operator₄ {o : Operator L 4} {t₁ t₂ t₃ t₄ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂, t₃, t₄]) ↔
        o.val ![t₁.val s e ε, t₂.val s e ε, t₃.val s e ε, t₄.val s e ε] := by
  simp [eval_operator, Matrix.comp_vecCons', Matrix.constant_eq_singleton]


-- @@ L358-358 verbatim
end Semiformula


-- @@ L360-360 verbatim
end «lp_section_3»


-- @@ L362-362 verbatim
section «lp_section_4»


-- @@ L364-364 verbatim
variable {M : Type*} [Nonempty M] [Structure L M]


-- @@ L366-367 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Semiterm.Rlz (t : Semiterm L M n) (e : Fin n → M) : M := t.valm M e id


-- @@ L369-371 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Semiformula.Rlz (φ : Semiformula L M n) (e : Fin n → M) : Prop :=
  Semiformula.Evalm M e id φ


-- @@ L373-373 expanded
@[simp]
lemma models₀_not_iff (σ : Sentence L) : Models₀ M (Tilde.tilde σ) ↔ ¬Models₀ M σ := by
  simp [models₀_iff]


-- @@ L375-376 expanded
@[simp]
lemma models₀_or_iff (σ π : Sentence L) : Models₀ M (Vee.vee σ π) ↔ Models₀ M σ ∨ Models₀ M π := by
  simp [models₀_iff]


-- @@ L378-379 expanded
@[simp]
lemma models₀_imply_iff (σ π : Sentence L) :
    Models₀ M (Arrow.arrow σ π) ↔ Models₀ M σ → Models₀ M π := by simp [models₀_iff]


-- @@ L381-381 verbatim
end «lp_section_4»


-- @@ L383-383 verbatim
namespace Arith


-- @@ L385-385 verbatim
namespace Hierarchy


-- @@ L387-387 verbatim
section «lp_section_5»

-- @@ L388-388 verbatim
variable {L : FirstOrder.Language} [L.LT] {μ : Type v}


-- @@ L390-394 expanded
@[simp]
lemma exItr {n} :
    {k : ℕ} →
      {φ : Semiformula L μ (n + k)} →
        Hierarchy SigmaSymbol.sigma (s + 1) (exItr k φ) ↔ Hierarchy SigmaSymbol.sigma (s + 1) φ
  | 0, φ => by simp
  | k + 1, φ => by simp [LO.exItr_succ, exItr]


-- @@ L396-400 expanded
@[simp]
lemma univItr {n} :
    {k : ℕ} →
      {φ : Semiformula L μ (n + k)} →
        Hierarchy PiSymbol.pi (s + 1) (univItr k φ) ↔ Hierarchy PiSymbol.pi (s + 1) φ
  | 0, φ => by simp
  | k + 1, φ => by simp [LO.univItr_succ, univItr]


-- @@ L402-402 verbatim
end «lp_section_5»


-- @@ L404-404 verbatim
end Hierarchy


-- @@ L406-406 expanded
variable (M : Type*) [ORingStruc M] [ModelsTheory M PeanoMinus]


-- @@ L408-408 expanded
instance : ModelsTheory M CobhamR0 := by refine models_of_subtheory (T := PeanoMinus) inferInstance


-- @@ L410-412 expanded
lemma nat_extention_sigmaOne {σ : Sentence oRing} (hσ : Hierarchy SigmaSymbol.sigma 1 σ) :
    Models₀ ℕ σ → Models₀ M σ := fun h ↦ by
  simpa [Matrix.empty_eq] using LO.Arith.sigma_one_completeness (M := M) hσ h


-- @@ L414-417 expanded
lemma nat_extention_piOne {σ : Sentence oRing} (hσ : Hierarchy PiSymbol.pi 1 σ) :
    Models₀ M σ → Models₀ ℕ σ := by
  contrapose
  simpa using nat_extention_sigmaOne M (σ := Tilde.tilde σ) (by simpa using hσ)


-- @@ L419-419 verbatim
end Arith


-- @@ L421-421 verbatim
end FirstOrder


-- @@ L423-423 verbatim
end LO


-- @@ L425-425 verbatim
namespace LO

-- @@ L426-426 verbatim
namespace Arith


-- @@ L428-428 verbatim
open FirstOrder FirstOrder.Arith ORingStruc


-- @@ L430-430 expanded
variable {M : Type*} [ORingStruc M] [ModelsTheory M CobhamR0]


-- @@ L432-435 expanded
lemma bold_sigma_one_completeness' {n} {σ : Semisentence oRing n}
    (hσ : Hierarchy SigmaSymbol.sigma 1 σ) {e} :
    Semiformula.Evalbm ℕ e σ → Semiformula.Evalbm M (fun x ↦ numeral (e x)) σ := fun h ↦ by
  simpa [Empty.eq_elim] using
    bold_sigma_one_completeness (M := M) (φ := σ) hσ (f := Empty.elim) (e := e) h


-- @@ L437-437 verbatim
end Arith

-- @@ L438-438 verbatim
end LO


-- @@ L440-440 verbatim
namespace List

-- @@ L441-441 verbatim
namespace Vector


-- @@ L443-443 verbatim
variable {α : Type*}


-- @@ L445-445 verbatim
@[simp] lemma nil_get (v : Vector α 0) : v.get = ![] := by ext i; exact i.elim0


-- @@ L447-447 verbatim
end Vector

-- @@ L448-448 verbatim
end List
