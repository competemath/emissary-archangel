/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Mathlib.Algebra.CharZero.Defs

public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.PFun
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.List
public import Mathlib.Order.Preorder.Chain
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToDual
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.List.GetD
import Mathlib.Order.ConditionallyCompleteLattice.Basic


-- @@ L25-25 verbatim
/-! # Vorspiel -/


-- @@ L27-27 verbatim
@[expose] public section



-- @@ L30-30 verbatim
namespace Nat

-- @@ L31-31 verbatim
variable {α : ℕ → Sort u}


-- @@ L33-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def cases (hzero : α 0) (hsucc : ∀ n, α (n + 1)) : ∀ n, α n
  | 0     => hzero
  | n + 1 => hsucc n


-- @@ L38-39 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:70 " :>ₙ " => cases


-- @@ L41-42 expanded
@[simp]
lemma cases_zero (hzero : α 0) (hsucc : ∀ n, α (n + 1)) : (cases hzero hsucc) 0 = hzero :=
  rfl


-- @@ L44-45 expanded
@[simp]
lemma cases_succ (hzero : α 0) (hsucc : ∀ n, α (n + 1)) (n : ℕ) :
    (cases hzero hsucc) (n + 1) = hsucc n :=
  rfl


-- @@ L47-48 verbatim
@[simp 1100] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt <| Nat.lt_succ_of_le <| by simp


-- @@ L50-51 verbatim
lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt <| Nat.lt_succ_of_le <| by simp


-- @@ L53-59 verbatim
lemma rec_eq {α : Sort*} (a : α) (f₁ f₂ : ℕ → α → α) (n : ℕ) (H : ∀ m < n, ∀ a, f₁ m a = f₂ m a) :
    (n.rec a f₁ : α) = n.rec a f₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (n.rec a f₁ : α) = n.rec a f₂ := ih (fun m hm a => H m (Nat.lt_succ_of_lt hm) a)
    simpa [this] using H n (Nat.lt_add_one n) (n.rec a f₂)


-- @@ L61-63 verbatim
lemma least_number (P : ℕ → Prop) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ z < x, ¬P z := by
  classical
  exact ⟨Nat.find hP, Nat.find_spec hP, fun z hz => Nat.find_min hP hz⟩


-- @@ L65-66 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def toFin (n : ℕ) : ℕ → Option (Fin n) := fun x => if hx : x < n then some ⟨x, hx⟩ else none


-- @@ L68-68 verbatim
end Nat


-- @@ L70-71 verbatim
lemma eq_finZeroElim {α : Sort u} (x : Fin 0 → α) : x = finZeroElim :=
  funext (by rintro ⟨_, _⟩; contradiction)


-- @@ L73-73 verbatim
namespace Matrix

-- @@ L74-74 verbatim
open _root_.Matrix.Fin

-- @@ L75-75 verbatim
section «lp_section_1»

-- @@ L76-76 verbatim
variable {n : ℕ} {α : Type u}


-- @@ L78-79 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:70 " :> " => vecCons


-- @@ L81-82 expanded
@[simp 1100]
lemma vecCons_zero : (vecCons a s) 0 = a := by simp


-- @@ L84-85 expanded
@[simp 1100]
lemma vecCons_succ (i : Fin n) : (vecCons a s) (Fin.succ i) = s i := by simp


-- @@ L87-88 expanded
@[simp]
lemma vecCons_last (a : C) (s : Fin (n + 1) → C) :
    (vecCons a s) (Fin.last (n + 1)) = s (Fin.last n) :=
  vecCons_succ (Fin.last n)


-- @@ L90-92 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def vecConsLast {n : ℕ} (t : Fin n → α) (h : α) : Fin n.succ → α :=
  Fin.lastCases h t


-- @@ L94-94 expanded
@[simp]
lemma cons_app_one {n : ℕ} (a : α) (s : Fin n.succ → α) : (vecCons a s) 1 = s 0 :=
  rfl


-- @@ L96-96 expanded
@[simp]
lemma cons_app_two {n : ℕ} (a : α) (s : Fin n.succ.succ → α) : (vecCons a s) 2 = s 1 :=
  rfl


-- @@ L98-99 expanded
@[simp]
lemma cons_app_three {n : ℕ} (a : α) (s : Fin n.succ.succ.succ → α) : (vecCons a s) 3 = s 2 :=
  rfl


-- @@ L101-101 verbatim
section «lp_section_2»

-- @@ L102-102 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L104-107 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Matrix.vecEmpty]
meta def unexpandVecEmpty : Unexpander
  | `($(_)) => `(![])


-- @@ L109-114 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Matrix.vecCons]
meta def unexpandVecCons : Unexpander
  | `($(_) $a ![])      => `(![$a])
  | `($(_) $a ![$as,*]) => `(![$a, $as,*])
  | _                   => throw ()


-- @@ L116-116 verbatim
end «lp_section_2»


-- @@ L118-119 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixl:70 " <: " => vecConsLast


-- @@ L121-122 expanded
@[simp]
lemma rightConcat_last : (vecConsLast s a) (Fin.last n) = a := by simp [vecConsLast]


-- @@ L124-125 expanded
@[simp]
lemma rightConcat_castSucc (i : Fin n) : (vecConsLast s a) (Fin.castSucc i) = s i := by
  simp [vecConsLast]


-- @@ L127-128 expanded
@[simp]
lemma rightConcat_zero (a : α) (s : Fin n.succ → α) : (vecConsLast s a) 0 = s 0 :=
  rightConcat_castSucc 0


-- @@ L130-131 expanded
@[simp]
lemma zero_succ_eq_id {n} : vecCons (0 : Fin (n + 1)) Fin.succ = id :=
  funext <| Fin.cases (by simp) (by simp)


-- @@ L133-135 expanded
@[simp]
lemma zero_cons_succ_eq_self (f : Fin (n + 1) → α) :
    (vecCons (f 0) (f ·.succ) : Fin (n + 1) → α) = f := by funext x;
  cases x using Fin.cases <;> simp


-- @@ L137-138 expanded
lemma eq_vecCons (s : Fin (n + 1) → C) : s = vecCons (s 0) (s ∘ Fin.succ) :=
  funext <| Fin.cases (by simp) (by simp)


-- @@ L140-143 expanded
@[simp 1100]
lemma vecCons_ext (a₁ a₂ : α) (s₁ s₂ : Fin n → α) :
    vecCons a₁ s₁ = vecCons a₂ s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by simp_all, by intros h; simp [h]⟩


-- @@ L145-157 expanded
lemma vecCons_assoc (a b : α) (s : Fin n → α) :
    vecCons a (vecConsLast s b) = vecConsLast (vecCons a s) b :=
  by
  funext x
  cases x using Fin.cases with
  | zero => simp
  | succ x =>
    cases x using Fin.lastCases
    · simp
    · rename_i i
      simp only [Nat.succ_eq_add_one, vecCons_succ, rightConcat_castSucc]
      rw [Fin.succ_castSucc]
      exact ((rightConcat_castSucc (a := b) (s := vecCons a s) i.succ).trans (vecCons_succ i)).symm


-- @@ L159-166 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def decVec {α : Type _} : {n : ℕ} → (v w :
    Fin n → α) → (∀ i, Decidable (v i = w i)) → Decidable (v = w)
  | 0,     _, _, _ => by simpa [Matrix.empty_eq] using isTrue trivial
  | n + 1, v, w, d => by
      rw [eq_vecCons v, eq_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simpa using d _)
      refine instDecidableAnd


-- @@ L168-170 expanded
lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) :
    (fun x => f <| (vecCons a s) x) = vecCons (f a) (f ∘ s) :=
  funext (fun i => Fin.cases (by simp) (by simp) i)


-- @@ L172-174 expanded
lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) :
    (fun x => f <| (vecCons a s) x) = vecCons (f a) fun i => f (s i) :=
  comp_vecCons f a s


-- @@ L176-177 expanded
lemma comp_vecCons'' (f : α → β) (a : α) (s : Fin n → α) :
    f ∘ (vecCons a s) = vecCons (f a) (f ∘ s) :=
  comp_vecCons f a s


-- @@ L179-179 verbatim
@[simp] lemma comp₀ : f ∘ (![] : Fin 0 → α) = ![] := by simp [Matrix.empty_eq]


-- @@ L181-181 verbatim
@[simp] lemma comp₁ (a : α) : f ∘ ![a] = ![f a] := by simp [comp_vecCons'']


-- @@ L183-183 verbatim
@[simp] lemma comp₂ (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] := by simp [comp_vecCons'']


-- @@ L185-187 verbatim
@[simp] lemma comp₃ (a₁ a₂ a₃ : α) :
    f ∘ ![a₁, a₂, a₃] = ![f a₁, f a₂, f a₃] := by
  simp [comp_vecCons'']


-- @@ L189-191 expanded
lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) :
    (fun x => f <| (vecConsLast s a) x) = vecConsLast (f ∘ s) (f a) :=
  funext (fun i => Fin.lastCases (by simp) (by simp) i)


-- @@ L193-195 verbatim
@[simp 1100] lemma vecHead_comp (f : α → β) (v : Fin (n + 1) → α) :
    vecHead (f ∘ v) = f (vecHead v) :=
  by simp [vecHead]


-- @@ L197-198 verbatim
lemma vecTail_comp (f : α → β) (v : Fin (n + 1) → α) : vecTail (f ∘ v) = f ∘ (vecTail v) := by
  simp [vecTail, Function.comp_assoc]


-- @@ L200-204 expanded
lemma vecConsLast_vecEmpty {s : Fin 0 → α} (a : α) : vecConsLast s a = ![a] :=
  funext
    (fun x => by
      cases x using Fin.cases with
      | zero => rw [show (0 : Fin 1) = Fin.last 0 from rfl, rightConcat_last, cons_val_fin_one]
      | succ i => exact absurd i.isLt (by simp))


-- @@ L206-206 verbatim
lemma constant_eq_singleton {a : α} : (fun _ => a) = ![a] := by funext x; simp


-- @@ L208-208 verbatim
lemma constant_eq_singleton' {v : Fin 1 → α} : v = ![v 0] := by funext x; simp [Fin.eq_zero]


-- @@ L210-211 verbatim
lemma constant_eq_vec₂ {a : α} : (fun _ => a) = ![a, a] := by
  funext x; cases x using Fin.cases <;> simp [Fin.eq_zero]


-- @@ L213-214 verbatim
lemma fun_eq_vec₂ {v : Fin 2 → α} : v = ![v 0, v 1] := by
  funext x; cases x using Fin.cases <;> simp [Fin.eq_zero]


-- @@ L216-223 expanded
lemma injective_vecCons {f : Fin n → α} (h : Function.Injective f) {a} (ha : ∀ i, a ≠ f i) :
    Function.Injective (vecCons a f) :=
  by
  have : ∀ i, f i ≠ a := fun i => (ha i).symm
  intro i j; cases i using Fin.cases <;> cases j using Fin.cases
  · simp
  · simp [*]
  · simp [*]
  · simpa using @h _ _


-- @@ L225-225 verbatim
end «lp_section_1»


-- @@ L227-227 verbatim
variable {α : Type _}


-- @@ L229-232 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def toList : {n : ℕ} → (Fin n → α) → List α
  | 0,     _ => []
  | _ + 1, v => v 0 :: toList (v ∘ Fin.succ)


-- @@ L234-234 verbatim
@[simp] lemma toList_zero (v : Fin 0 → α) : toList v = [] := rfl


-- @@ L236-236 verbatim
@[simp] lemma toList_succ (v : Fin (n + 1) → α) : toList v = v 0 :: toList (v ∘ Fin.succ) := rfl


-- @@ L238-239 verbatim
@[simp] lemma toList_length (v : Fin n → α) : (toList v).length = n :=
  by induction n <;> simp [*]


-- @@ L241-247 verbatim
@[simp] lemma mem_toList_iff {v : Fin n → α} {a} : a ∈ toList v ↔ ∃ i, v i = a := by
  induction n
  · simp [*]
  · suffices (a = v 0 ∨ ∃ i : Fin _, v i.succ = a) ↔ ∃ i, v i = a by simp [*]
    constructor
    · rintro (rfl | ⟨i, rfl⟩) <;> simp
    · rintro ⟨i, rfl⟩; cases i using Fin.cases <;> simp


-- @@ L249-249 verbatim
variable {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}


-- @@ L251-254 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def getM : {n : ℕ} → {β : Fin n → Type u} → ((i : Fin n) → m (β i)) → m ((i : Fin n) → β i)
  | 0,     _, _ => pure finZeroElim
  | _ + 1, _, f => Fin.cases <$> f 0 <*> getM (f ·.succ)


-- @@ L256-263 verbatim
lemma getM_pure [LawfulMonad m] {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (pure (v i) : m (β i))) = pure v := by
  induction n with
  | zero =>
    unfold getM; congr; funext x; exact x.elim0
  | succ n ih =>
    simp only [getM, map_pure, ih, seq_pure]
    exact congr_arg _ (funext <| Fin.cases rfl fun i ↦ rfl)


-- @@ L265-266 verbatim
@[simp] lemma getM_some {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (some (v i) : Option (β i))) = some v := getM_pure v


-- @@ L268-270 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def appendr {n m} (v : Fin n → α) (w : Fin m → α) : Fin (m + n) → α :=
  Matrix.vecAppend (add_comm m n) v w


-- @@ L272-272 verbatim
@[simp] lemma appendr_nil {m} (w : Fin m → α) : appendr ![] w = w := by funext i; simp [appendr]


-- @@ L274-276 expanded
@[simp]
lemma appendr_cons {m n} (x : α) (v : Fin n → α) (w : Fin m → α) :
    appendr (vecCons x v) w = vecCons x (appendr v w) := by funext i; simp [appendr]


-- @@ L278-278 verbatim
section «lp_section_3»


-- @@ L280-283 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def vecToNat : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0,     _ => 0
  | _ + 1, v => Nat.pair (v 0) (vecToNat <| v ∘ Fin.succ) + 1


-- @@ L285-285 verbatim
open Encodable


-- @@ L287-287 verbatim
@[simp] lemma vecToNat_empty (v : Fin 0 → ℕ) : vecToNat v = 0 := rfl


-- @@ L289-291 expanded
@[simp]
lemma encode_succ {n} (x : ℕ) (v : Fin n → ℕ) :
    vecToNat (vecCons x v) = Nat.pair x (vecToNat v) + 1 := by simp [vecToNat, Function.comp_def]


-- @@ L293-293 verbatim
end «lp_section_3»


-- @@ L295-295 verbatim
end Matrix


-- @@ L297-297 verbatim
namespace DMatrix


-- @@ L299-301 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def vecEmpty : Fin 0 → α :=
  Fin.elim0


-- @@ L303-303 verbatim
variable {n} {α : Fin (n + 1) → Type*}


-- @@ L305-307 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def vecCons (h : α 0) (t : (i : Fin n) → α i.succ) : (i : Fin n.succ) → α i :=
  Fin.cons h t


-- @@ L309-310 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:70 " ::> " => vecCons


-- @@ L312-312 expanded
@[simp]
lemma vecCons_zero (h : α 0) (t : (i : Fin n) → α i.succ) : (vecCons h t) 0 = h :=
  rfl


-- @@ L314-316 expanded
@[simp]
lemma vecCons_succ (h : α 0) (t : (i : Fin n) → α i.succ) (i : Fin n) :
    (vecCons h t) i.succ = t i :=
  rfl


-- @@ L318-319 expanded
lemma eq_vecCons (s : (i : Fin (n + 1)) → α i) : s = vecCons (s 0) fun i => s i.succ :=
  funext <| Fin.cases (by simp) (by simp)


-- @@ L321-327 expanded
@[simp]
lemma vecCons_ext (a₁ a₂ : α 0) (s₁ s₂ : (i : Fin n) → α i.succ) :
    vecCons a₁ s₁ = vecCons a₂ s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by
    intros h
    constructor
    · exact congrFun h 0
    · exact funext (fun i => by simpa using congrFun h i.succ), by intros h; simp [h]⟩


-- @@ L329-337 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def decVec {n : ℕ} {α : Fin n → Type _}
  (v w : (i : Fin n) → α i) (h : ∀ i, Decidable (v i = w i)) : Decidable (v = w) := by
    induction n with
    | zero => exact isTrue (by funext x; exact finZeroElim (α := fun x => v x = w x) x)
    | succ n ih =>
      rw [eq_vecCons v, eq_vecCons w, vecCons_ext]
      haveI := ih (fun i => v i.succ) (fun i => w i.succ) (fun i => h i.succ)
      refine instDecidableAnd


-- @@ L339-339 verbatim
end DMatrix


-- @@ L341-341 verbatim
namespace Option


-- @@ L343-343 verbatim
lemma pure_eq_some (a : α) : pure a = some a := rfl


-- @@ L345-346 verbatim
@[simp 1100] lemma toList_eq_iff {o : Option α} {a} :
    o.toList = [a] ↔ o = some a := by rcases o <;> simp


-- @@ L348-348 verbatim
end Option


-- @@ L350-354 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def Nat.natToVec : ℕ → (n : ℕ) → Option (Fin n → ℕ)
  | 0, 0 => some Matrix.vecEmpty
  | e + 1, n + 1 => Nat.natToVec e.unpair.2 n |>.map (vecCons e.unpair.1 ·)
  | _, _ => none


-- @@ L356-356 verbatim
namespace Nat

-- @@ L357-357 verbatim
open Matrix

-- @@ L358-358 verbatim
variable {n : ℕ}


-- @@ L360-364 expanded
@[simp]
lemma natToVec_vecToNat (v : Fin n → ℕ) : (vecToNat v).natToVec n = some v :=
  by
  induction n
  · simp [*, Nat.natToVec, vecToNat, Matrix.empty_eq]
  · suffices vecCons (v 0) (v ∘ Fin.succ) = v by simp [*, Nat.natToVec, vecToNat]
    exact funext (fun i ↦ i.cases (by simp []) (by simp))


-- @@ L366-380 verbatim
lemma lt_of_eq_natToVec {e : ℕ} {v : Fin n → ℕ} (h : e.natToVec n = some v) (i : Fin n) :
    v i < e := by
  induction n generalizing e with
  | zero => exact i.elim0
  | succ n ih =>
    cases e with
    | zero => simp [natToVec] at h
    | succ e =>
      simp only [natToVec, Option.map_eq_some_iff] at h
      rcases h with ⟨v, hnv, rfl⟩
      cases i using Fin.cases with
      | zero => simp [Nat.lt_succ_iff, unpair_left_le]
      | succ i =>
        simp only [cons_val_succ]
        exact lt_trans (ih hnv i) (Nat.lt_succ_iff.mpr <| unpair_right_le e)


-- @@ L382-383 verbatim
lemma one_le_of_bodd {n : ℕ} (h : n.bodd = true) : 1 ≤ n :=
by induction n <;> simp  at h ⊢


-- @@ L385-391 verbatim
lemma pair_le_pair_of_le {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁.pair b₁ ≤ a₂.pair b₂ := by
  rcases lt_or_eq_of_le ha with (ha | rfl) <;> rcases lt_or_eq_of_le hb with (hb | rfl)
  { exact le_of_lt (lt_trans (Nat.pair_lt_pair_left b₁ ha) (Nat.pair_lt_pair_right a₂ hb)) }
  { exact le_of_lt (Nat.pair_lt_pair_left b₁ ha) }
  { exact le_of_lt (Nat.pair_lt_pair_right a₁ hb) }
  { rfl }


-- @@ L393-393 verbatim
end Nat


-- @@ L395-395 verbatim
namespace Fin


-- @@ L397-398 verbatim
lemma pos_of_coe_ne_zero {i : Fin (n + 1)} (h : (i : ℕ) ≠ 0) :
    0 < i := Nat.pos_of_ne_zero h


-- @@ L400-400 verbatim
@[simp 1100] lemma one_pos'' : (0 : Fin (n + 2)) < 1 := pos_of_coe_ne_zero (Nat.succ_ne_zero 0)


-- @@ L402-402 verbatim
@[simp] lemma two_pos : (0 : Fin (n + 3)) < 2 := pos_of_coe_ne_zero (Nat.succ_ne_zero 1)


-- @@ L404-404 verbatim
@[simp] lemma three_pos : (0 : Fin (n + 4)) < 3 := pos_of_coe_ne_zero (Nat.succ_ne_zero 2)


-- @@ L406-406 verbatim
@[simp] lemma four_pos : (0 : Fin (n + 5)) < 4 := pos_of_coe_ne_zero (Nat.succ_ne_zero 3)


-- @@ L408-408 verbatim
@[simp] lemma five_pos : (0 : Fin (n + 6)) < 5 := pos_of_coe_ne_zero (Nat.succ_ne_zero 4)


-- @@ L410-410 verbatim
end Fin


-- @@ L412-412 verbatim
namespace Fintype

-- @@ L413-413 verbatim
variable {ι : Type _} [Fintype ι]


-- @@ L415-415 verbatim
section «lp_section_4»


-- @@ L417-417 verbatim
variable {α : Type _} [SemilatticeSup α] [OrderBot α]


-- @@ L419-420 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def sup (f : ι → α) : α := (Finset.univ : Finset ι).sup f


-- @@ L422-422 verbatim
@[simp] lemma elem_le_sup (f : ι → α) (i : ι) : f i ≤ sup f := Finset.le_sup (by simp)


-- @@ L424-424 verbatim
lemma le_sup {a : α} {f : ι → α} (i : ι) (le : a ≤ f i) : a ≤ sup f := le_trans le (elem_le_sup _ _)


-- @@ L426-427 verbatim
@[simp] lemma sup_le_iff {f : ι → α} {a : α} :
    sup f ≤ a ↔ (∀ i, f i ≤ a) := by simp [sup]


-- @@ L429-429 verbatim
@[simp] lemma finsup_eq_0_of_empty [IsEmpty ι] (f : ι → α) : sup f = ⊥ := by simp [sup]


-- @@ L431-431 verbatim
end «lp_section_4»


-- @@ L433-436 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def decideEqPi {β : ι → Type*} (a b : (i : ι) → β i) (_ : (i : ι) → Decidable (a i = b i)) :
    Decidable (a = b) :=
  decidable_of_iff (∀ i, a i = b i) funext_iff.symm


-- @@ L438-438 verbatim
end Fintype


-- @@ L440-440 verbatim
namespace String


-- @@ L442-445 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))


-- @@ L447-447 verbatim
end String


-- @@ L449-449 verbatim
namespace Empty


-- @@ L451-451 verbatim
lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim := funext (by rintro ⟨⟩)


-- @@ L453-453 verbatim
end Empty


-- @@ L455-455 verbatim
namespace IsEmpty

-- @@ L456-456 verbatim
variable {o : Sort u} (h : IsEmpty o)


-- @@ L458-458 verbatim
lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim' := funext h.elim


-- @@ L460-460 verbatim
end IsEmpty


-- @@ L462-462 verbatim
namespace Function


-- @@ L464-464 verbatim
variable {α : Type u} {β : Type v}


-- @@ L466-467 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def funEqOn (φ : α → Prop) (f g : α → β) : Prop := ∀ a, φ a → f a = g a


-- @@ L469-472 verbatim
lemma _root_.Function.funEqOn.of_subset {φ ψ : α → Prop} {f g : α → β} (e : funEqOn φ f g) (h :
    ∀ a, ψ a → φ a) :
    funEqOn ψ f g :=
  by intro a ha; exact e a (h a ha)


-- @@ L474-474 verbatim
end Function


-- @@ L476-476 verbatim
namespace Quotient

-- @@ L477-477 verbatim
open Matrix

-- @@ L478-478 verbatim
variable {α : Type u} [s : Setoid α] {β : Sort v}


-- @@ L480-483 verbatim
@[elab_as_elim]
lemma inductionOnVec {φ : (Fin n → Quotient s) → Prop} (v : Fin n → Quotient s)
  (h : ∀ v : Fin n → α, φ (fun i => Quotient.mk s (v i))) : φ v :=
  Quotient.induction_on_pi v h


-- @@ L485-497 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def liftVec :
    ∀ {n} (f : (Fin n → α) → β),
      (∀ v₁ v₂ : Fin n → α, (∀ n, v₁ n ≈ v₂ n) → f v₁ = f v₂) → (Fin n → Quotient s) → β
  | 0, f, _, _ => f ![]
  | n + 1, f, h, v =>
    let ih : α → (Fin n → Quotient s) → β := fun a v =>
      liftVec (n := n) (fun v => f (vecCons a v))
        (fun v₁ v₂ hv => h (vecCons a v₁) (vecCons a v₂) (Fin.cases (by simpa using refl a) hv)) v
    Quot.liftOn (vecHead v) (ih · (vecTail v))
      (fun a b hab =>
        by
        have : ∀ v, f (vecCons a v) = f (vecCons b v) := fun v ↦
          h _ _ (Fin.cases hab (by simpa using fun x ↦ refl _))
        simp [this, ih])


-- @@ L499-501 verbatim
@[simp] lemma liftVec_zero (f : (Fin 0 → α) → β) (h) (v : Fin 0 → Quotient s) :
    liftVec f h v = f ![] :=
  rfl


-- @@ L503-511 expanded
lemma liftVec_mk {n} (f : (Fin n → α) → β) (h) (v : Fin n → α) :
    liftVec f h (Quotient.mk s ∘ v) = f v := by
  induction n with
  | zero => simp [liftVec, empty_eq]
  | succ n ih =>
    simp [liftVec]
    simpa [Function.comp_def, Matrix.vecHead, Matrix.vecTail, Quotient.liftOn_mk] using
      ih (fun v' => f (vecCons (vecHead v) v'))
        (fun v₁ v₂ hv =>
          h (vecCons (vecHead v) v₁) (vecCons (vecHead v) v₂) (Fin.cases (refl _) hv))
        (vecTail v)


-- @@ L513-514 verbatim
@[simp] lemma liftVec_mk₁ (f : (Fin 1 → α) → β) (h) (a : α) :
    liftVec f h ![Quotient.mk s a] = f ![a] := liftVec_mk f h ![a]


-- @@ L516-517 verbatim
@[simp] lemma liftVec_mk₂ (f : (Fin 2 → α) → β) (h) (a₁ a₂ : α) :
    liftVec f h ![Quotient.mk s a₁, Quotient.mk s a₂] = f ![a₁, a₂] := liftVec_mk f h ![a₁, a₂]


-- @@ L519-519 verbatim
end Quotient


-- @@ L521-521 verbatim
namespace List


-- @@ L523-523 verbatim
variable {α : Type u} {β : Type v}


-- @@ L525-527 verbatim
lemma getI_map_range [Inhabited α] (f : ℕ → α) (h : i < n) :
    ((List.range n).map f).getI i = f i := by
  simpa [h] using List.getI_eq_getElem ((List.range n).map f) (n := i) (by simpa using h)


-- @@ L529-531 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def subsetSet (l : List α) (s : Set α) [DecidablePred s] : Bool :=
  l.foldr (fun a ih => s a && ih) true


-- @@ L533-536 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def upper : List ℕ → ℕ
  | []      => 0
  | n :: ns => max (n + 1) ns.upper


-- @@ L538-538 verbatim
@[simp] lemma upper_nil : upper [] = 0 := rfl


-- @@ L540-540 verbatim
@[simp] lemma upper_cons (n : ℕ) (ns : List ℕ) : upper (n :: ns) = max (n + 1) ns.upper := rfl


-- @@ L542-549 verbatim
lemma lt_upper (l : List ℕ) {n} (h : n ∈ l) : n < l.upper := by
  induction l with
  | nil => simp at h
  | cons m ns ih =>
    suffices n < m + 1 ∨ n < ns.upper by simpa
    rcases show n = m ∨ n ∈ ns by simpa using h with (rfl | h)
    · exact Or.inl (Nat.lt_succ_self _)
    · exact Or.inr (ih h)


-- @@ L551-551 verbatim
section «lp_section_5»


-- @@ L553-553 verbatim
variable [DecidableEq α] [DecidableEq β]


-- @@ L555-556 verbatim
lemma toFinset_map {f : α → β} (l : List α) : (l.map f).toFinset = Finset.image f l.toFinset := by
  induction l <;> simp [*]


-- @@ L558-559 verbatim
lemma toFinset_mono {l l' : List α} (h : l ⊆ l') : l.toFinset ⊆ l'.toFinset :=
  fun _ ha => mem_toFinset.mpr (h (mem_toFinset.mp ha))


-- @@ L561-561 verbatim
end «lp_section_5»


-- @@ L563-563 verbatim
section «lp_section_6»


-- @@ L565-565 verbatim
variable [SemilatticeSup α] [OrderBot α]


-- @@ L567-570 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def sup : List α → α
  |      [] => ⊥
  | a :: as => a ⊔ as.sup


-- @@ L572-572 verbatim
@[simp] lemma sup_nil : ([] : List α).sup = ⊥ := rfl


-- @@ L574-574 verbatim
@[simp] lemma sup_cons (a : α) (as : List α) : (a :: as).sup = a ⊔ as.sup := rfl


-- @@ L576-583 verbatim
lemma le_sup {a} {l : List α} : a ∈ l → a ≤ l.sup := by
  induction l with
  | nil => simp
  | cons b l ih =>
    intro h
    rcases show a = b ∨ a ∈ l by simpa using h with (rfl | h)
    · simp
    · exact le_sup_of_le_right (ih h)


-- @@ L585-599 verbatim
lemma sup_ofFn (f : Fin n → α) : (ofFn f).sup = Finset.sup Finset.univ f := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 ((Finset.univ : Finset (Fin n)).image Fin.succ) := by
      ext i; simp
    have h₂ : Finset.sup Finset.univ (fun i ↦ f (Fin.succ i)) = Finset.sup {0}ᶜ f := by
      simpa [Function.comp_def] using Eq.symm <|
          Finset.sup_image (Finset.univ : Finset (Fin n)) Fin.succ f
    calc
      (ofFn f).sup = (f 0 ⊔ Finset.univ.sup fun i : Fin _ ↦ f i.succ) := by simp [ih]
      _            = f 0 ⊔ Finset.sup {0}ᶜ f                          := by rw [h₂]
      _            = Finset.univ.sup f                                := by
        rw [h₁, Finset.sup_insert]; simp


-- @@ L601-601 verbatim
end «lp_section_6»


-- @@ L603-605 verbatim
lemma ofFn_get_eq_map_cast {n} (g : α → β) (as : List α) {h} :
    ofFn (fun i => g (as.get (i.cast h)) : Fin n → β) = as.map g := by
  simp_all


-- @@ L607-607 verbatim
variable {m : Type _ → Type _} {α : Type _} {β : Type _} [Monad m]


-- @@ L609-610 verbatim
lemma append_subset_append {l₁ l₂ l : List α} (h : l₁ ⊆ l₂) : l₁ ++ l ⊆ l₂ ++ l :=
  List.append_subset.mpr ⟨List.subset_append_of_subset_left _ h, subset_append_right l₂ l⟩


-- @@ L612-612 verbatim
lemma subset_of_eq {l₁ l₂ : List α} (e : l₁ = l₂) : l₁ ⊆ l₂ := by simp [e]


-- @@ L614-614 verbatim
section «lp_section_7»


-- @@ L616-617 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def remove [DecidableEq α] (a : α) : List α → List α := List.filter (· ≠ a)


-- @@ L619-619 verbatim
variable [DecidableEq α]


-- @@ L621-622 verbatim
@[simp]
lemma remove_nil (a : α) : [].remove a = [] := by simp [List.remove]


-- @@ L624-627 verbatim
@[simp 1100]
lemma eq_remove_cons {l : List α} :
    (ψ :: l).remove ψ = l.remove ψ := by
  induction l <;> simp_all [List.remove];


-- @@ L629-631 verbatim
@[simp]
lemma remove_singleton_of_ne {φ ψ : α} (h : φ ≠ ψ) :
    [φ].remove ψ = [φ] := by simp_all [List.remove]


-- @@ L633-633 verbatim
lemma mem_remove_iff {l : List α} : b ∈ l.remove a ↔ b ∈ l ∧ b ≠ a := by simp [List.remove]


-- @@ L635-636 verbatim
lemma mem_of_mem_remove {a b : α} {l : List α} (h : b ∈ l.remove a) : b ∈ l :=
  (mem_remove_iff.mp h).1


-- @@ L638-639 verbatim
lemma remove_cons_self (l : List α) (a) :
  (a :: l).remove a = l.remove a := by simp [remove]


-- @@ L641-642 verbatim
lemma remove_cons_of_ne (l : List α) {a b} (ne : a ≠ b) :
  (a :: l).remove b = a :: l.remove b := by simp_all [remove];


-- @@ L644-645 verbatim
lemma remove_subset (a) (l : List α) :
    l.remove a ⊆ l := fun _ h => (mem_remove_iff.mp h).1


-- @@ L647-651 verbatim
lemma remove_subset_remove (a) {l₁ l₂ : List α} (h : l₁ ⊆ l₂) :
    l₁.remove a ⊆ l₂.remove a := by
  simp only [subset_def, mem_remove_iff, ne_eq, and_imp]
  intros
  simpa [*] using h (by assumption)


-- @@ L653-657 verbatim
lemma remove_cons_subset_cons_remove (a b) (l : List α) :
    (a :: l).remove b ⊆ a :: l.remove b := by
  intro x
  simp only [mem_remove_iff, mem_cons, ne_eq, and_imp]
  rintro (rfl | hx) nex <;> simp [*]


-- @@ L659-664 verbatim
lemma remove_map_substet_map_remove [DecidableEq β] (f : α → β) (l : List α) (a) :
    (l.map f).remove (f a) ⊆ (l.remove a).map f := by
  simp only [subset_def, mem_remove_iff, mem_map, ne_eq, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂]
  intro b hb neb;
  exact ⟨b, ⟨hb, by rintro rfl; exact neb rfl⟩, rfl⟩


-- @@ L666-666 verbatim
end «lp_section_7»


-- @@ L668-679 verbatim
@[elab_as_elim]
lemma induction_with_singleton
  {motive : List F → Prop}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a as, as ≠ [] → motive as → motive (a :: as)) : ∀ as, motive as := by
  intro as;
  induction as with
  | nil => exact hnil;
  | cons a as ih => cases as with
    | nil => exact hsingle a;
    | cons b bs => exact hcons a (b :: bs) (by simp) ih;




-- @@ L683-683 verbatim
end List


-- @@ L685-685 verbatim
namespace List

-- @@ L686-686 verbatim
namespace Vector


-- @@ L688-688 verbatim
variable {α : Type*}


-- @@ L690-692 verbatim
lemma get_mk_eq_get {n} (l : List α) (h : l.length = n) (i : Fin n) : List.Vector.get (⟨l, h⟩ :
    List.Vector α n) i = l.get (i.cast h.symm) :=
  rfl


-- @@ L694-695 verbatim
lemma get_one {α : Type*} {n} (v : Vector α (n + 2)) : v.get 1 = v.tail.head := by
  simpa [Vector.get_zero] using (Vector.get_tail_succ v 0).symm


-- @@ L697-699 expanded
lemma ofFn_vecCons (a : α) (v : Fin n → α) : ofFn (vecCons a v) = a ::ᵥ ofFn v := by ext i;
  cases i using Fin.cases <;> simp


-- @@ L701-701 verbatim
end Vector

-- @@ L702-702 verbatim
end List


-- @@ L704-704 verbatim
namespace Finset


-- @@ L706-706 verbatim
variable {α : Type u} {β : Type v} {γ : Type w}


-- @@ L708-710 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def rangeOfFinite {ι : Sort v} [Finite ι] (f : ι → α) : Finset α :=
  Set.Finite.toFinset (s := Set.range f) (Set.finite_range f)


-- @@ L712-713 verbatim
lemma mem_rangeOfFinite_iff {ι : Sort v} [Finite ι] {f : ι → α} {a : α} :
    a ∈ rangeOfFinite f ↔ ∃ i : ι, f i = a := by simp [rangeOfFinite]


-- @@ L715-718 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def imageOfFinset [DecidableEq β] (s : Finset α) (f : (a : α) → a ∈ s → β) :
    Finset β :=
  Finset.biUnion s (rangeOfFinite <| f ·)


-- @@ L720-722 verbatim
lemma mem_imageOfFinset_iff [DecidableEq β] {s : Finset α} {f : (a : α) → a ∈ s → β} {b : β} :
    b ∈ imageOfFinset s f ↔ ∃ (a : α) (ha : a ∈ s), f a ha = b := by
  simp [imageOfFinset, mem_rangeOfFinite_iff]


-- @@ L724-727 verbatim
@[simp] lemma mem_imageOfFinset [DecidableEq β] {s : Finset α} (f : (a : α) → a ∈ s → β) (a :
    α) (ha :
    a ∈ s) :
    f a ha ∈ imageOfFinset s f := by simpa [mem_imageOfFinset_iff] using ⟨a, ha, rfl⟩


-- @@ L729-730 verbatim
lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} :
  (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp [and_or_left]


-- @@ L732-733 verbatim
@[simp 1100] lemma equiv_univ {α α'} [Fintype α] [Fintype α'] [DecidableEq α'] (e : α ≃ α') :
    (Finset.univ : Finset α).image e = Finset.univ := by ext x; simp


-- @@ L735-741 verbatim
@[simp] lemma sup_univ_equiv
    {α α'} [Fintype α] [Fintype α'] [SemilatticeSup β] [OrderBot β] (f :
    α → β) (e :
    α' ≃ α) :
    Finset.sup Finset.univ (fun i => f (e i)) = Finset.sup Finset.univ f := by
  classical
  simpa [Function.comp_def] using Eq.symm <| Finset.sup_image Finset.univ e f


-- @@ L743-746 verbatim
lemma sup_univ_cast {α : Type _} [SemilatticeSup α] [OrderBot α] {n} (f : Fin n → α) (n') {h :
    n' = n} :
    Finset.sup Finset.univ (fun (i : Fin n') =>
      f (i.cast h)) = Finset.sup Finset.univ f := by rcases h with rfl; simp


-- @@ L748-748 verbatim
end Finset


-- @@ L750-750 verbatim
namespace Denumerable


-- @@ L752-761 verbatim
lemma lt_of_mem_list : ∀ n i, i ∈ Denumerable.ofNat (List ℕ) n → i < n
  |     0 => by simp
  | n + 1 => by
    have : n.unpair.2 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    suffices (Nat.unpair n).1 < n + 1 ∧ ∀ a ∈ ofNat (List ℕ) (Nat.unpair n).2, a < n + 1 by simpa
    constructor
    · exact Nat.lt_succ_of_le (Nat.unpair_left_le n)
    · intro i hi
      have : i < n.unpair.2 := lt_of_mem_list n.unpair.2 i hi
      exact lt_trans this (Nat.lt_succ_of_le <| Nat.unpair_right_le n)


-- @@ L763-763 verbatim
end Denumerable


-- @@ L765-765 verbatim
namespace Part


-- @@ L767-783 verbatim
@[simp] lemma mem_vector_mOfFn : ∀ {n : ℕ} {w : List.Vector α n} {v : Fin n →. α},
    w ∈ List.Vector.mOfFn v ↔ ∀ i, w.get i ∈ v i
  |     0, _, _ => by simp [List.Vector.mOfFn, List.Vector.eq_nil]
  | n + 1, w, v => by
    suffices (∃ a ∈ v 0, ∃ u, (∀ (i : Fin n), u.get i ∈ v i.succ) ∧ w = a ::ᵥ u) ↔
      ∀ (i : Fin (n + 1)), w.get i ∈ v i by
      simpa [List.Vector.mOfFn, mem_vector_mOfFn (n := n) (v := fun i => v i.succ)]
    constructor
    · rintro ⟨a, ha, v, hv, rfl⟩ i; cases i using Fin.cases <;> simp [ha, hv]
    · intro h
      have hhead : w.head ∈ v 0 := by
        rw [←List.Vector.get_zero w]
        exact h 0
      refine ⟨w.head, hhead, w.tail, ?_, (List.Vector.cons_head_tail w).symm⟩
      intro i
      have htail : w.tail.get i = w.get i.succ := List.Vector.get_tail_succ w i
      exact htail.symm ▸ h i.succ


-- @@ L785-785 verbatim
end Part


-- @@ L787-787 verbatim
namespace Set


-- @@ L789-789 verbatim
variable {α : Type*}


-- @@ L791-805 verbatim
lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c) (hchain :
    IsChain (· ⊆ ·) c)
    {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on s hfin
    (by rcases hc with ⟨t, ht⟩; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h
        have : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h)
        rcases this with ⟨t, htc, ht⟩
        have : ∃ u ∈ c, a ∈ u := by
          have : (∃ t ∈ c, a ∈ t) ∧ s ⊆ ⋃₀ c := by simpa [Set.insert_subset_iff] using h
          exact this.1
        rcases this with ⟨u, huc, hu⟩
        have : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := IsChain.directedOn hchain t htc u huc
        rcases this with ⟨z, hzc, htz, huz⟩
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)


-- @@ L807-807 verbatim
end Set


-- @@ L809-812 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Exp (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  exp : α → α

-- @@ L813-813 verbatim
export Exp (exp)


-- @@ L815-817 verbatim
/-- Class for `α` has at least `n` elements -/
class Atleast (n : ℕ+) (α) where
  mapping : ∃ f : Fin n → α, Function.HasLeftInverse f
