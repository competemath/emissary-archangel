/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel
import Mathlib.Algebra.Order.Ring.Nat


-- @@ L11-24 verbatim
/-!
# Logic Symbols

This file defines structure that has logical connectives $\top, \bot, \land, \lor, \to, \lnot$
and their homomorphisms.

## Main Definitions
* `LO.LogicalConnective` is defined so that `LO.LogicalConnective F` is a type that has logical
* connectives $\top, \bot, \land, \lor, \to, \lnot$.
* `LO.LogicalConnective.Hom` is defined so that `f : F →ˡᶜ G` is a homomorphism from `F` to `G`,
* i.e.,
a function that preserves logical connectives.

-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
namespace LO


-- @@ L30-30 verbatim
section «lp_section_1»


-- @@ L32-35 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class Tilde (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  tilde : α → α


-- @@ L37-40 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class Arrow (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  arrow : α → α → α


-- @@ L42-45 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class Wedge (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  wedge : α → α → α


-- @@ L47-50 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class] class Vee (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  vee : α → α → α


-- @@ L52-54 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class LogicalConnective (α : Type*)
  extends Top α, Bot α, Tilde α, Arrow α, Wedge α, Vee α


-- @@ L56-57 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:75 "∼" => Tilde.tilde


-- @@ L59-60 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:60 " ==> " => Arrow.arrow


-- @@ L62-63 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:69 " ⋏ " => Wedge.wedge


-- @@ L65-66 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infixr:68 " ⋎ " => Vee.vee


-- @@ L68-72 verbatim
attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee


-- @@ L74-74 verbatim
end «lp_section_1»


-- @@ L76-83 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class DeMorgan (F : Type*) [LogicalConnective F] where
  verum : Tilde.tilde (⊤ : F) = ⊥
  falsum : Tilde.tilde (⊥ : F) = ⊤
  imply (φ ψ : F) : (Arrow.arrow φ ψ) = Vee.vee (Tilde.tilde φ) ψ
  and (φ ψ : F) : Tilde.tilde (Wedge.wedge φ ψ) = Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ)
  or (φ ψ : F) : Tilde.tilde (Vee.vee φ ψ) = Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ)
  neg (φ : F) : Tilde.tilde (Tilde.tilde φ) = φ


-- @@ L85-85 verbatim
attribute [simp] DeMorgan.verum DeMorgan.falsum DeMorgan.and DeMorgan.or DeMorgan.neg


-- @@ L87-89 expanded
/-- Introducing `∼φ` as an abbreviation of `φ ==> ⊥`. -/
class NegAbbrev (F : Type*) [Tilde F] [Arrow F] [Bot F] where
  neg {φ : F} : Tilde.tilde φ = Arrow.arrow φ ⊥


-- @@ L91-91 verbatim
namespace LogicalConnective


-- @@ L93-93 verbatim
section «lp_section_2»

-- @@ L94-94 verbatim
variable {α : Type*} [LogicalConnective α]


-- @@ L96-97 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern]
def iff (a b : α) :=
  Wedge.wedge (Arrow.arrow a b) (Arrow.arrow b a)


-- @@ L99-100 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:61 " <=> " => LogicalConnective.iff


-- @@ L102-102 verbatim
end «lp_section_2»


-- @@ L104-111 verbatim
@[reducible]
instance PropLogicSymbols : LogicalConnective Prop where
  top := True
  bot := False
  tilde := Not
  arrow := fun P Q => (P → Q)
  wedge := And
  vee := Or


-- @@ L113-113 verbatim
@[simp] lemma _root_.LO.LogicalConnective.Prop.top_eq : ⊤ = True := rfl


-- @@ L115-115 verbatim
@[simp] lemma _root_.LO.LogicalConnective.Prop.bot_eq : ⊥ = False := rfl


-- @@ L117-117 expanded
@[simp]
lemma _root_.LO.LogicalConnective.Prop.neg_eq (φ : Prop) : Tilde.tilde φ = ¬φ :=
  rfl


-- @@ L119-120 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[simp]
lemma _root_.LO.LogicalConnective.Prop.arrow_eq (φ ψ : Prop) : (Arrow.arrow φ ψ) = (φ → ψ) :=
  rfl


-- @@ L122-122 expanded
@[simp]
lemma _root_.LO.LogicalConnective.Prop.and_eq (φ ψ : Prop) : (Wedge.wedge φ ψ) = (φ ∧ ψ) :=
  rfl


-- @@ L124-124 expanded
@[simp]
lemma _root_.LO.LogicalConnective.Prop.or_eq (φ ψ : Prop) : (Vee.vee φ ψ) = (φ ∨ ψ) :=
  rfl


-- @@ L126-128 expanded
@[simp]
lemma _root_.LO.LogicalConnective.Prop.iff_eq (φ ψ : Prop) :
    (LogicalConnective.iff φ ψ) = (φ ↔ ψ) := by
  simp [LogicalConnective.iff, iff_iff_implies_and_implies]


-- @@ L130-136 verbatim
instance : DeMorgan Prop where
  verum := by simp
  falsum := by simp
  imply := fun _ _ => by simp[imp_iff_not_or]
  and := fun _ _ => by simp[-not_and, not_and_or]
  or := fun _ _ => by simp[not_or]
  neg := fun _ => by simp


-- @@ L138-146 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HomClass (F : Type*) (α β : outParam Type*) [LogicalConnective α] [LogicalConnective β]
    [FunLike F α β] where
  map_top : ∀ (f : F), f ⊤ = ⊤
  map_bot : ∀ (f : F), f ⊥ = ⊥
  map_neg : ∀ (f : F) (φ : α), f (Tilde.tilde φ) = Tilde.tilde (f φ)
  map_imply : ∀ (f : F) (φ ψ : α), f (Arrow.arrow φ ψ) = Arrow.arrow (f φ) (f ψ)
  map_and : ∀ (f : F) (φ ψ : α), f (Wedge.wedge φ ψ) = Wedge.wedge (f φ) (f ψ)
  map_or : ∀ (f : F) (φ ψ : α), f (Vee.vee φ ψ) = Vee.vee (f φ) (f ψ)


-- @@ L148-149 verbatim
attribute [simp] HomClass.map_top HomClass.map_bot HomClass.map_neg HomClass.map_imply
  HomClass.map_and HomClass.map_or


-- @@ L151-151 verbatim
namespace HomClass


-- @@ L153-153 verbatim
variable (F : Type*) (α β : outParam Type*) [LogicalConnective α] [LogicalConnective β]

-- @@ L154-154 verbatim
variable [FunLike F α β]

-- @@ L155-155 verbatim
variable [HomClass F α β]

-- @@ L156-156 verbatim
variable (f : F) (a b : α)


-- @@ L158-158 verbatim
instance : CoeFun F (fun _ => α → β) := ⟨DFunLike.coe⟩


-- @@ L160-160 expanded
@[simp]
lemma map_iff : f (LogicalConnective.iff a b) = LogicalConnective.iff (f a) (f b) := by
  simp [LogicalConnective.iff]


-- @@ L162-162 verbatim
end HomClass


-- @@ L164-164 verbatim
variable (α β γ : Type*) [LogicalConnective α] [LogicalConnective β] [LogicalConnective γ]


-- @@ L166-175 expanded
/-- Imported declaration from the Incompleteness formalization. -/
structure Hom where
  /-- Imported declaration from the Incompleteness formalization. -/
  toTr : α → β
  map_top' : toTr ⊤ = ⊤
  map_bot' : toTr ⊥ = ⊥
  map_neg' : ∀ φ, toTr (Tilde.tilde φ) = Tilde.tilde (toTr φ)
  map_imply' : ∀ φ ψ, toTr (Arrow.arrow φ ψ) = Arrow.arrow (toTr φ) (toTr ψ)
  map_and' : ∀ φ ψ, toTr (Wedge.wedge φ ψ) = Wedge.wedge (toTr φ) (toTr ψ)
  map_or' : ∀ φ ψ, toTr (Vee.vee φ ψ) = Vee.vee (toTr φ) (toTr ψ)


-- @@ L177-178 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
infix:25 " →ˡᶜ " => Hom


-- @@ L180-180 verbatim
namespace Hom

-- @@ L181-181 verbatim
variable {α β γ}


-- @@ L183-187 expanded
instance : FunLike (Hom α β) α β where
  coe := toTr
  coe_injective := by
    rintro ⟨_⟩ ⟨_⟩ h
    simpa only [mk.injEq] using h


-- @@ L189-189 expanded
@[ext]
lemma ext (f g : Hom α β) (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h


-- @@ L191-197 expanded
instance : HomClass (Hom α β) α β where
  map_top := map_top'
  map_bot := map_bot'
  map_neg := map_neg'
  map_imply := map_imply'
  map_and := map_and'
  map_or := map_or'


-- @@ L199-199 expanded
variable (f : Hom α β) (a b : α)


-- @@ L201-209 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def id : Hom α α where
  toTr := id
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp


-- @@ L211-211 verbatim
@[simp] lemma app_id (a : α) : LogicalConnective.Hom.id a = a := rfl


-- @@ L213-221 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def comp (g : Hom β γ) (f : Hom α β) : Hom α γ
    where
  toTr := g ∘ f
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp


-- @@ L223-224 expanded
@[simp]
lemma app_comp (g : Hom β γ) (f : Hom α β) (a : α) : g.comp f a = g (f a) :=
  rfl


-- @@ L226-226 verbatim
end Hom


-- @@ L228-233 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class AndOrClosed {F} [LogicalConnective F] (C : F → Prop) where
  verum : C ⊤
  falsum : C ⊥
  and {f g : F} : C f → C g → C (Wedge.wedge f g)
  or {f g : F} : C f → C g → C (Vee.vee f g)


-- @@ L235-238 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Closed {F} [LogicalConnective F] (C : F → Prop) extends AndOrClosed C where
  not {f : F} : C f → C (Tilde.tilde f)
  imply {f g : F} : C f → C g → C (Arrow.arrow f g)


-- @@ L240-240 verbatim
end LogicalConnective


-- @@ L242-242 verbatim
section «lp_section_3»


-- @@ L244-246 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Tilde.Subclosed [Tilde F] (C : F → Prop) where
  tilde_closed : C (Tilde.tilde φ) → C φ


-- @@ L248-250 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Arrow.Subclosed [Arrow F] (C : F → Prop) where
  arrow_closed : C (Arrow.arrow φ ψ) → C φ ∧ C ψ


-- @@ L252-254 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Wedge.Subclosed [Wedge F] (C : F → Prop) where
  wedge_closed : C (Wedge.wedge φ ψ) → C φ ∧ C ψ


-- @@ L256-258 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.Vee.Subclosed [Vee F] (C : F → Prop) where
  vee_closed : C (Vee.vee φ ψ) → C φ ∧ C ψ


-- @@ L260-264 verbatim
attribute [aesop safe 5 forward]
  Tilde.Subclosed.tilde_closed
  Arrow.Subclosed.arrow_closed
  Wedge.Subclosed.wedge_closed
  Vee.Subclosed.vee_closed


-- @@ L266-271 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.LogicalConnective.Subclosed [LogicalConnective F] (C : F → Prop) extends
  toTildeSubclosed : Tilde.Subclosed C,
  toArrowSubclosed : Arrow.Subclosed C,
  toWedgeSubclosed : Wedge.Subclosed C,
  toVeeSubclosed : Vee.Subclosed C


-- @@ L273-273 verbatim
end «lp_section_3»


-- @@ L275-275 verbatim
section «lp_section_4»


-- @@ L277-277 verbatim
variable {α β : Type*} [LogicalConnective α] [LogicalConnective β]


-- @@ L279-282 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conjLt (φ : ℕ → α) : ℕ → α
  | 0 => ⊤
  | k + 1 => Wedge.wedge (φ k) (conjLt φ k)


-- @@ L284-284 verbatim
@[simp] lemma conjLt_zero (φ : ℕ → α) : conjLt φ 0 = ⊤ := rfl


-- @@ L286-286 expanded
@[simp]
lemma conjLt_succ (φ : ℕ → α) (k) : conjLt φ (k + 1) = Wedge.wedge (φ k) (conjLt φ k) :=
  rfl


-- @@ L288-303 verbatim
@[simp] lemma hom_conj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (φ :
    ℕ → α) :
    f (conjLt φ k) ↔ ∀ i < k, f (φ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [conjLt_succ, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
      ih]
    constructor
    · rintro ⟨hk, h⟩
      intro i hi
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with (rfl | hi)
      · exact hk
      · exact h i hi
    · rintro h
      exact ⟨h k (by simp), fun i hi ↦ h i (Nat.lt_add_right 1 hi)⟩


-- @@ L305-308 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def disjLt (φ : ℕ → α) : ℕ → α
  | 0 => ⊥
  | k + 1 => Vee.vee (φ k) (disjLt φ k)


-- @@ L310-310 verbatim
@[simp] lemma disjLt_zero (φ : ℕ → α) : disjLt φ 0 = ⊥ := rfl


-- @@ L312-312 expanded
@[simp]
lemma disjLt_succ (φ : ℕ → α) (k) : disjLt φ (k + 1) = Vee.vee (φ k) (disjLt φ k) :=
  rfl


-- @@ L314-328 verbatim
@[simp] lemma hom_disj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (φ :
    ℕ → α) :
    f (disjLt φ k) ↔ ∃ i < k, f (φ i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [disjLt_succ, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨k, by simp, h⟩
      · exact ⟨i, Nat.lt_add_right 1 hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with (rfl | hi)
      · left; exact h
      · right; exact ⟨i, hi, h⟩


-- @@ L330-330 verbatim
end «lp_section_4»


-- @@ L332-332 verbatim
end LO


-- @@ L334-334 verbatim
open LO


-- @@ L336-336 verbatim
namespace Matrix


-- @@ L338-338 verbatim
section «lp_section_5»


-- @@ L340-340 verbatim
variable {α : Type*}

-- @@ L341-341 verbatim
variable [LogicalConnective α] [LogicalConnective β]


-- @@ L343-346 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conjVec : {n : ℕ} → (Fin n → α) → α
  | 0, _ => ⊤
  | _ + 1, v => Wedge.wedge (v 0) (conjVec (vecTail v))


-- @@ L348-348 verbatim
@[simp] lemma conj_nil (v : Fin 0 → α) : conjVec v = ⊤ := rfl


-- @@ L350-350 expanded
@[simp]
lemma conj_cons {a : α} {v : Fin n → α} : conjVec (vecCons a v) = Wedge.wedge a (conjVec v) :=
  rfl


-- @@ L352-362 verbatim
@[simp] lemma conj_hom_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
  (f : F) (v : Fin n → α) : f (conjVec v) = ∀ i, f (v i) := by
  induction n with
  | zero => simp [conjVec]
  | succ n ih =>
    simp only [conjVec, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
      eq_iff_iff]
    rw [ih]
    constructor
    · intro ⟨hz, hs⟩ i; cases i using Fin.cases; { exact hz }; { exact hs _ }
    · intro h; exact ⟨h 0, fun i => h _⟩


-- @@ L364-368 verbatim
lemma hom_conj [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) :
    f (conjVec v) = conjVec (f ∘ v) := by
  induction n with
  | zero => simp only [conjVec, LogicalConnective.HomClass.map_top]
  | succ n ih => simp [ih, conjVec, Matrix.vecTail_comp]


-- @@ L370-372 verbatim
lemma hom_conj₂ [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) :
    f (conjVec v) = conjVec fun i => f (v i) :=
  hom_conj f v


-- @@ L374-377 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def disj : {n : ℕ} → (Fin n → α) → α
  | 0, _ => ⊥
  | _ + 1, v => Vee.vee (v 0) (disj (vecTail v))


-- @@ L379-379 verbatim
@[simp] lemma disj_nil (v : Fin 0 → α) : disj v = ⊥ := rfl


-- @@ L381-381 expanded
@[simp]
lemma disj_cons {a : α} {v : Fin n → α} : disj (vecCons a v) = Vee.vee a (disj v) :=
  rfl


-- @@ L383-394 verbatim
@[simp] lemma disj_hom_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
  (f : F) (v : Fin n → α) : f (disj v) = ∃ i, f (v i) := by
  induction n with
  | zero => simp [disj]
  | succ n ih =>
    simp only [disj, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
      eq_iff_iff]
    rw [ih]
    constructor
    · rintro (H | ⟨i, H⟩); { exact ⟨0, H⟩ }; { exact ⟨i.succ, H⟩ }
    · rintro ⟨i, h⟩
      cases i using Fin.cases; { left; exact h }; { right; exact ⟨_, h⟩ }


-- @@ L396-400 verbatim
lemma hom_disj [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) :
    f (disj v) = disj (f ∘ v) := by
  induction n with
  | zero => simp only [disj, LogicalConnective.HomClass.map_bot]
  | succ n ih => simp [ih, disj, Matrix.vecTail_comp]


-- @@ L402-404 verbatim
lemma hom_disj' [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) :
    f (disj v) = disj fun i => f (v i) :=
  hom_disj f v


-- @@ L406-406 verbatim
end «lp_section_5»


-- @@ L408-408 verbatim
end Matrix


-- @@ L410-410 verbatim
namespace List


-- @@ L412-412 verbatim
section «lp_section_6»


-- @@ L414-414 verbatim
variable {α : Type*} [LogicalConnective α]


-- @@ L416-419 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conj : List α → α
  | [] => ⊤
  | a :: as => Wedge.wedge a as.conj


-- @@ L421-421 verbatim
@[simp] lemma conj_nil : conj (α := α) [] = ⊤ := rfl


-- @@ L423-423 expanded
@[simp]
lemma conj_cons {a : α} {as : List α} : conj (a :: as) = Wedge.wedge a as.conj :=
  rfl


-- @@ L425-427 verbatim
lemma map_conj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l : List α) :
    f l.conj ↔ ∀ a ∈ l, f a := by
  induction l <;> simp[*]


-- @@ L429-432 expanded
lemma map_conj_append [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F)
    (l₁ l₂ : List α) : f (l₁ ++ l₂).conj ↔ f (Wedge.wedge l₁.conj l₂.conj) := by
  induction l₁ <;> induction l₂ <;> aesop;


-- @@ L434-437 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def disj : List α → α
  | [] => ⊥
  | a :: as => Vee.vee a as.disj


-- @@ L439-439 verbatim
@[simp] lemma disj_nil : disj (α := α) [] = ⊥ := rfl


-- @@ L441-441 expanded
@[simp]
lemma disj_cons {a : α} {as : List α} : disj (a :: as) = Vee.vee a as.disj :=
  rfl


-- @@ L443-445 verbatim
lemma map_disj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (l : List α) :
    f l.disj ↔ ∃ a ∈ l, f a := by
  induction l <;> simp[*]


-- @@ L447-450 expanded
lemma map_disj_append [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F)
    (l₁ l₂ : List α) : f (l₁ ++ l₂).disj ↔ f (Vee.vee l₁.disj l₂.disj) := by
  induction l₁ <;> induction l₂ <;> aesop;


-- @@ L452-452 verbatim
end «lp_section_6»


-- @@ L454-454 verbatim
section «lp_section_7»


-- @@ L456-456 verbatim
variable {F : Type u} [LogicalConnective F]

-- @@ L457-457 verbatim
variable {φ ψ : F}


-- @@ L459-463 expanded
/-- Remark: `[φ].conj₂ = φ ≠ φ ⋏ ⊤ = [φ].conj` -/
def conj₂ : List F → F
  | [] => ⊤
  | [φ] => φ
  | φ :: ψ :: rs => Wedge.wedge φ (ψ :: rs).conj₂


-- @@ L465-466 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "⋀" => List.conj₂


-- @@ L468-468 expanded
@[simp]
lemma conj₂_nil : List.conj₂ [] = (⊤ : F) :=
  rfl


-- @@ L470-470 expanded
@[simp]
lemma conj₂_singleton : List.conj₂ [φ] = φ :=
  rfl


-- @@ L472-472 expanded
@[simp]
lemma conj₂_doubleton : List.conj₂ [φ, ψ] = Wedge.wedge φ ψ :=
  rfl


-- @@ L474-478 expanded
@[simp]
lemma conj₂_cons_nonempty {a : F} {as : List F} (h : as ≠ [] := by assumption) :
    List.conj₂ (a :: as) = Wedge.wedge a (List.conj₂ as) := by
  cases as with
  | nil => contradiction;
  | cons ψ rs => simp [List.conj₂]


-- @@ L480-484 expanded
/-- Remark: `[φ].disj = φ ≠ φ ⋎ ⊥ = [φ].disj` -/
def disj₂ : List F → F
  | [] => ⊥
  | [φ] => φ
  | φ :: ψ :: rs => Vee.vee φ (ψ :: rs).disj₂


-- @@ L486-487 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "⋁" => disj₂


-- @@ L489-489 expanded
@[simp]
lemma disj₂_nil : disj₂ [] = (⊥ : F) :=
  rfl


-- @@ L491-491 expanded
@[simp]
lemma disj₂_singleton : disj₂ [φ] = φ :=
  rfl


-- @@ L493-493 expanded
@[simp]
lemma disj₂_doubleton : disj₂ [φ, ψ] = Vee.vee φ ψ :=
  rfl


-- @@ L495-499 expanded
@[simp]
lemma disj₂_cons_nonempty {a : F} {as : List F} (h : as ≠ [] := by assumption) :
    disj₂ (a :: as) = Vee.vee a (disj₂ as) := by
  cases as with
  | nil => contradiction;
  | cons ψ rs => simp [disj₂]


-- @@ L501-501 verbatim
end «lp_section_7»


-- @@ L503-503 verbatim
end List


-- @@ L505-505 verbatim
namespace Finset


-- @@ L507-507 verbatim
section «lp_section_8»


-- @@ L509-509 verbatim
variable [LogicalConnective α]


-- @@ L511-512 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def conj (s : Finset α) : α := s.toList.conj


-- @@ L514-516 verbatim
lemma map_conj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s : Finset α) :
    f s.conj ↔ ∀ a ∈ s, f a := by
  simpa [conj] using List.map_conj f s.toList


-- @@ L518-522 expanded
lemma map_conj_union [DecidableEq α] [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
    (f : F) (s₁ s₂ : Finset α) : f (s₁ ∪ s₂).conj ↔ f (Wedge.wedge s₁.conj s₂.conj) :=
  by
  simp only [Finset.mem_union, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    map_conj]
  aesop


-- @@ L524-525 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def disj (s : Finset α) : α := s.toList.disj


-- @@ L527-529 verbatim
lemma map_disj [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s : Finset α) :
    f s.disj ↔ ∃ a ∈ s, f a := by
  simpa [disj] using List.map_disj f s.toList


-- @@ L531-535 expanded
lemma map_disj_union [DecidableEq α] [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
    (f : F) (s₁ s₂ : Finset α) : f (s₁ ∪ s₂).disj ↔ f (Vee.vee s₁.disj s₂.disj) :=
  by
  simp only [Finset.mem_union, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
    map_disj]
  aesop


-- @@ L537-537 verbatim
end «lp_section_8»


-- @@ L539-539 verbatim
end Finset
