module

public import Foundation.Vorspiel.List.Basic
public import Foundation.Vorspiel.Multiset
public import Foundation.Vorspiel.NotationClass


-- @@ L7-7 verbatim
@[expose] public section


-- @@ L9-20 verbatim
/-!
# Logic Symbols

This file defines structure that has logical connectives $\top, \bot, \land, \lor, \to, \lnot$
and their homomorphisms.

## Main Definitions
* `FFL.LogicalConnective` is defined so that `FFL.LogicalConnective F` is a type that has logical connectives $\top, \bot, \land, \lor, \to, \lnot$.
* `FFL.LogicalConnective.Hom` is defined so that `f : F →ˡᶜ G` is a homomorphism from `F` to `G`, i.e.,
a function that preserves logical connectives.

-/


-- @@ L22-22 verbatim
namespace FFL


-- @@ L24-27 verbatim
/--
A class for types with logical connectives $\top, \bot, \land, \lor, \to, \lnot$.
-/
class LogicalConnective (α : Type*) extends Tilde α, Arrow α, Wedge α, Vee α


-- @@ L29-29 verbatim
class LogicalNeutral (α : Type*) extends Top α, Bot α


-- @@ L31-32 verbatim
class TildeInvolutive (F : Type*) [Tilde F] where
  tilde_involutive (φ : F) : ∼∼φ = φ


-- @@ L34-37 verbatim
class LogicalConnective.DeMorgan (F : Type*) [LogicalConnective F] where
  imply (φ ψ : F) : φ 🡒 ψ = ∼φ ⋎ ψ
  and (φ ψ : F) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ
  or (φ ψ : F) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ


-- @@ L39-43 verbatim
class LogicalNeutral.DeMorgan (F : Type*) [LogicalNeutral F] [Tilde F] where
  verum : ∼(⊤ : F) = ⊥
  falsum : ∼(⊥ : F) = ⊤

alias LogicalNeutral.DeMorgan.neg := TildeInvolutive.tilde_involutive


-- @@ L45-45 verbatim
attribute [simp, grind =] TildeInvolutive.tilde_involutive

-- @@ L46-46 verbatim
attribute [simp, grind =] LogicalNeutral.DeMorgan.verum LogicalNeutral.DeMorgan.falsum LogicalConnective.DeMorgan.and LogicalConnective.DeMorgan.or


-- @@ L48-49 verbatim
/-- Introducing `∼φ` as an abbreviation of `φ 🡒 ⊥`. -/
class NegAbbrev (F : Type*) [Tilde F] [Arrow F] [Bot F] where
  
-- @@ L50-50 verbatim
protected neg {φ : F} : ∼φ = φ 🡒 ⊥


-- @@ L52-52 verbatim
attribute [grind =] NegAbbrev.neg


-- @@ L54-55 verbatim
/-- Introducing `∼φ`, `φ ⋎ ψ`, `φ ⋏ ψ`, `⊤` as abbreviation. -/
class ŁukasiewiczAbbrev (F : Type*) [LogicalNeutral F] [LogicalConnective F] extends NegAbbrev F where
  
-- @@ L56-56 verbatim
protected top : ⊤ = ∼(⊥ : F)
  
-- @@ L57-57 verbatim
protected or {φ ψ : F} : φ ⋎ ψ = ∼φ 🡒 ψ
  
-- @@ L58-58 verbatim
protected and {φ ψ : F} : φ ⋏ ψ = ∼(φ 🡒 ∼ψ)


-- @@ L60-60 verbatim
attribute [grind =] ŁukasiewiczAbbrev.and ŁukasiewiczAbbrev.or ŁukasiewiczAbbrev.top


-- @@ L62-62 verbatim
section tilde


-- @@ L64-64 verbatim
variable {α : Type*} [Tilde α] [TildeInvolutive α]


-- @@ L66-68 verbatim
@[simp] lemma TildeInvolutive.tilde_injective : Function.Injective (∼· : α → α) := by
  intro φ ψ h
  simpa using congr_arg (∼·) h


-- @@ L70-71 verbatim
@[simp] lemma TildeInvolutive.tilde_eq_tilde_iff_eq {φ ψ : α} : ∼φ = ∼ψ ↔ φ = ψ :=
  Function.Injective.eq_iff TildeInvolutive.tilde_injective


-- @@ L73-73 verbatim
def Tilde.invol : α ↪ α := ⟨(∼·), TildeInvolutive.tilde_injective⟩


-- @@ L75-75 verbatim
@[simp] lemma Tilde.invol_app (φ : α) : Tilde.invol φ = ∼φ := rfl


-- @@ L77-77 verbatim
end tilde


-- @@ L79-79 verbatim
namespace LogicalConnective


-- @@ L81-81 verbatim
section

-- @@ L82-82 verbatim
variable {α : Type*} [LogicalConnective α]


-- @@ L84-84 verbatim
@[match_pattern] def iff (a b : α) := (a 🡒 b) ⋏ (b 🡒 a)


-- @@ L86-89 verbatim
/--
A defined logical connective for "iff", defined from the logical connectives `🡒` and `⋏`.
-/
infix:61 " 🡘 " => LogicalConnective.iff


-- @@ L91-91 verbatim
end


-- @@ L93-98 verbatim
@[reducible]
instance PropLogicSymbols : LogicalConnective Prop where
  arrow := fun P Q => (P → Q)
  wedge := And
  vee := Or
  tilde := Not


-- @@ L100-102 verbatim
instance PropLogicalNeutral : LogicalNeutral Prop where
  top := True
  bot := False


-- @@ L104-104 verbatim
@[simp] lemma Prop.top_eq : ⊤ = True := rfl


-- @@ L106-106 verbatim
@[simp] lemma Prop.bot_eq : ⊥ = False := rfl


-- @@ L108-108 verbatim
@[simp] lemma Prop.neg_eq (φ : Prop) : ∼φ = ¬φ := rfl


-- @@ L110-110 verbatim
@[simp] lemma Prop.arrow_eq (φ ψ : Prop) : (φ 🡒 ψ) = (φ → ψ) := rfl


-- @@ L112-112 verbatim
@[simp] lemma Prop.and_eq (φ ψ : Prop) : (φ ⋏ ψ) = (φ ∧ ψ) := rfl


-- @@ L114-114 verbatim
@[simp] lemma Prop.or_eq (φ ψ : Prop) : (φ ⋎ ψ) = (φ ∨ ψ) := rfl


-- @@ L116-116 verbatim
@[simp] lemma Prop.iff_eq (φ ψ : Prop) : (φ 🡘 ψ) = (φ ↔ ψ) := by simp [LogicalConnective.iff, iff_iff_implies_and_implies]


-- @@ L118-119 verbatim
instance : TildeInvolutive Prop where
  tilde_involutive := fun _ => by simp


-- @@ L121-124 verbatim
instance : LogicalConnective.DeMorgan Prop where
  imply := fun _ _ => by simp [imp_iff_not_or]
  and := fun _ _ => by simp [-not_and, not_and_or]
  or := fun _ _ => by simp [not_or]


-- @@ L126-128 verbatim
instance : LogicalNeutral.DeMorgan Prop where
  verum := by simp
  falsum := by simp


-- @@ L130-140 verbatim
/--
A class for a type `F` which contains homomorphisms (for logical connectives) from `α` to `β`.
-/
class HomClass (F : Type*) (α β : outParam Type*)
    [LogicalConnective α] [LogicalNeutral α] [LogicalConnective β] [LogicalNeutral β] [FunLike F α β] where
  map_top : ∀ (f : F), f ⊤ = ⊤
  map_bot : ∀ (f : F), f ⊥ = ⊥
  map_neg : ∀ (f : F) (φ : α), f (∼φ) = ∼f φ
  map_imply : ∀ (f : F) (φ ψ : α), f (φ 🡒 ψ) = f φ 🡒 f ψ
  map_and : ∀ (f : F) (φ ψ : α), f (φ ⋏ ψ) = f φ ⋏ f ψ
  map_or  : ∀ (f : F) (φ ψ : α), f (φ ⋎ ψ) = f φ ⋎ f ψ


-- @@ L142-142 verbatim
attribute [simp, grind =] HomClass.map_top HomClass.map_bot HomClass.map_neg HomClass.map_imply HomClass.map_and HomClass.map_or


-- @@ L144-144 verbatim
namespace HomClass


-- @@ L146-146 verbatim
variable (F : Type*) (α β : outParam Type*) [LogicalConnective α] [LogicalNeutral α] [LogicalConnective β] [LogicalNeutral β] [FunLike F α β]

-- @@ L147-147 verbatim
variable [HomClass F α β]

-- @@ L148-148 verbatim
variable (f : F) (a b : α)


-- @@ L150-150 verbatim
instance : CoeFun F (fun _ => α → β) := ⟨DFunLike.coe⟩


-- @@ L152-152 verbatim
@[simp] lemma map_iff : f (a 🡘 b) = f a 🡘 f b := by simp [LogicalConnective.iff]


-- @@ L154-154 verbatim
end HomClass


-- @@ L156-158 verbatim
variable (α β γ : Type*)
  [LogicalConnective α] [LogicalConnective β] [LogicalConnective γ]
  [LogicalNeutral α] [LogicalNeutral β] [LogicalNeutral γ]


-- @@ L160-167 verbatim
structure Hom where
  toTr : α → β
  map_top' : toTr ⊤ = ⊤
  map_bot' : toTr ⊥ = ⊥
  map_neg' : ∀ φ, toTr (∼φ) = ∼toTr φ
  map_imply' : ∀ φ ψ, toTr (φ 🡒 ψ) = toTr φ 🡒 toTr ψ
  map_and' : ∀ φ ψ, toTr (φ ⋏ ψ) = toTr φ ⋏ toTr ψ
  map_or'  : ∀ φ ψ, toTr (φ ⋎ ψ) = toTr φ ⋎ toTr ψ


-- @@ L169-172 verbatim
/--
A structure for homomorphisms (for logical connectives) from `α` to `β`.
-/
infix:25 " →ˡᶜ " => Hom


-- @@ L174-174 verbatim
namespace Hom

-- @@ L175-175 verbatim
variable {α β γ}


-- @@ L177-180 verbatim
instance : FunLike (α →ˡᶜ β) α β where
  coe := toTr
  coe_injective := by
    intro f g h; rcases f; rcases g; simpa using h


-- @@ L182-182 verbatim
instance : CoeFun (α →ˡᶜ β) (fun _ => α → β) := DFunLike.toCoeFun


-- @@ L184-184 verbatim
@[ext] lemma ext (f g : α →ˡᶜ β) (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h


-- @@ L186-192 verbatim
instance : HomClass (α →ˡᶜ β) α β where
  map_top := map_top'
  map_bot := map_bot'
  map_neg := map_neg'
  map_imply := map_imply'
  map_and := map_and'
  map_or := map_or'


-- @@ L194-194 verbatim
variable (f : α →ˡᶜ β) (a b : α)


-- @@ L196-203 verbatim
protected def id : α →ˡᶜ α where
  toTr := id
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp


-- @@ L205-205 verbatim
@[simp] lemma app_id (a : α) : LogicalConnective.Hom.id a = a := rfl


-- @@ L207-214 verbatim
def comp (g : β →ˡᶜ γ) (f : α →ˡᶜ β) : α →ˡᶜ γ where
  toTr := g ∘ f
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp


-- @@ L216-217 verbatim
@[simp] lemma app_comp (g : β →ˡᶜ γ) (f : α →ˡᶜ β) (a : α) :
     g.comp f a = g (f a) := rfl


-- @@ L219-219 verbatim
end Hom


-- @@ L221-225 verbatim
class AndOrClosed {F} [LogicalConnective F] [LogicalNeutral F] (C : F → Prop) where
  verum  : C ⊤
  falsum : C ⊥
  and {f g : F} : C f → C g → C (f ⋏ g)
  or  {f g : F} : C f → C g → C (f ⋎ g)


-- @@ L227-234 verbatim
class Closed {F} [LogicalConnective F] [LogicalNeutral F] (C : F → Prop) extends AndOrClosed C where
  not {f : F} : C f → C (∼f)
  imply {f g : F} : C f → C g → C (f 🡒 g)

-- `AndOrClosed.verum`/`AndOrClosed.falsum` have `C` (a variable) as the simp LHS head symbol,
-- since `C` is the predicate being closed under `⊤`/`⊥`. They are intentionally kept as global
-- simp lemmas (`⊤`/`⊥` are always in any `AndOrClosed` predicate); scoping them would break
-- implicit uses elsewhere.

-- @@ L235-236 verbatim
set_option warning.simp.varHead false in
attribute [simp] AndOrClosed.verum AndOrClosed.falsum


-- @@ L238-268 verbatim
end LogicalConnective

/-
section Subclosed

class Tilde.Subclosed [Tilde F] (C : F → Prop) where
  tilde_closed : C (∼φ) → C φ

class Arrow.Subclosed [Arrow F] (C : F → Prop) where
  arrow_closed : C (φ 🡒 ψ) → C φ ∧ C ψ

class Wedge.Subclosed [Wedge F] (C : F → Prop) where
  wedge_closed : C (φ ⋏ ψ) → C φ ∧ C ψ

class Vee.Subclosed [Vee F] (C : F → Prop) where
  vee_closed : C (φ ⋎ ψ) → C φ ∧ C ψ

attribute [aesop safe 5 forward]
  Tilde.Subclosed.tilde_closed
  Arrow.Subclosed.arrow_closed
  Wedge.Subclosed.wedge_closed
  Vee.Subclosed.vee_closed

class LogicalConnective.Subclosed [LogicalConnective F] (C : F → Prop) extends
  Tilde.Subclosed C,
  Arrow.Subclosed C,
  Wedge.Subclosed C,
  Vee.Subclosed C

end Subclosed
-/


-- @@ L270-270 verbatim
section conjdisj


-- @@ L272-274 verbatim
variable {α β : Type*}
  [LogicalConnective α] [LogicalConnective β]
  [LogicalNeutral α] [LogicalNeutral β]


-- @@ L276-278 verbatim
def conjLt (φ : ℕ → α) : ℕ → α
  | 0     => ⊤
  | k + 1 => φ k ⋏ conjLt φ k


-- @@ L280-280 verbatim
@[simp] lemma conjLt_zero (φ : ℕ → α) : conjLt φ 0 = ⊤ := rfl


-- @@ L282-282 verbatim
@[simp] lemma conjLt_succ (φ : ℕ → α) (k) : conjLt φ (k + 1) = φ k ⋏ conjLt φ k := rfl


-- @@ L284-298 verbatim
/--
Homomorphisms commute with `k`-ary conjunctions.
-/
@[simp] lemma hom_conj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (φ : ℕ → α) :
    f (conjLt φ k) ↔ ∀ i < k, f (φ i) := by
  induction' k with k ih
  · simp [*]
  · suffices (f (φ k) ∧ ∀ i < k, f (φ i)) ↔ ∀ i < k + 1, f (φ i) by simp [*]
    constructor
    · rintro ⟨hk, h⟩
      intro i hi
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with (rfl | hi)
      · exact hk
      · exact h i hi
    · grind


-- @@ L300-302 verbatim
def disjLt (φ : ℕ → α) : ℕ → α
  | 0     => ⊥
  | k + 1 => φ k ⋎ disjLt φ k


-- @@ L304-304 verbatim
@[simp] lemma disjLt_zero (φ : ℕ → α) : disjLt φ 0 = ⊥ := rfl


-- @@ L306-306 verbatim
@[simp] lemma disjLt_succ (φ : ℕ → α) (k) : disjLt φ (k + 1) = φ k ⋎ disjLt φ k := rfl


-- @@ L308-316 verbatim
/--
Homomorphisms commute with `k`-ary disjunctions.
-/
@[simp] lemma hom_disj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (φ : ℕ → α) :
    f (disjLt φ k) ↔ ∃ i < k, f (φ i) := by
  induction' k with k ih
  · simp [*]
  · suffices (f (φ k) ∨ ∃ i < k, f (φ i)) ↔ ∃ i < k + 1, f (φ i) by simp [*]
    grind


-- @@ L318-318 verbatim
end conjdisj


-- @@ L320-320 verbatim
end FFL


-- @@ L322-322 verbatim
open FFL


-- @@ L324-324 verbatim
namespace Matrix


-- @@ L326-326 verbatim
variable {α : Type*}


-- @@ L328-328 verbatim
section conjunction


-- @@ L330-330 verbatim
variable [Top α] [Wedge α]


-- @@ L332-335 verbatim
/-- The conjunction of a vector of elements of type `α`, where `α` is a type with `Wedge α`. -/
def conj : {n : ℕ} → (Fin n → α) → α
  |     0, _ => ⊤
  | _ + 1, v => v 0 ⋏ conj (vecTail v)


-- @@ L337-337 verbatim
@[simp] lemma conj_nil (v : Fin 0 → α) : conj v = ⊤ := rfl


-- @@ L339-339 verbatim
@[simp] lemma conj_cons {a : α} {v : Fin n → α} : conj (a :> v) = a ⋏ conj v := rfl


-- @@ L341-341 verbatim
end conjunction


-- @@ L343-343 verbatim
section disjunction


-- @@ L345-345 verbatim
variable [Bot α] [Vee α]


-- @@ L347-350 verbatim
/-- The disjunction of a vector of elements of type `α`, where `α` is a type with `Vee α`. -/
def disj : {n : ℕ} → (Fin n → α) → α
  |     0, _ => ⊥
  | _ + 1, v => v 0 ⋎ disj (vecTail v)


-- @@ L352-352 verbatim
@[simp] lemma disj_nil (v : Fin 0 → α) : disj v = ⊥ := rfl


-- @@ L354-354 verbatim
@[simp] lemma disj_cons {a : α} {v : Fin n → α} : disj (a :> v) = a ⋎ disj v := rfl


-- @@ L356-356 verbatim
end disjunction


-- @@ L358-360 verbatim
variable
  [LogicalConnective α] [LogicalConnective β]
  [LogicalNeutral α] [LogicalNeutral β]


-- @@ L362-372 verbatim
/--
Homomorphisms commute with `k`-ary conjunctions (vector version).
-/
@[simp] lemma conj_hom_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
  (f : F) (v : Fin n → α) : f (conj v) = ∀ i, f (v i) := by
  induction' n with n ih
  · simp [conj]
  · suffices (f (v 0) ∧ ∀ (i : Fin n), f (vecTail v i)) ↔ ∀ (i : Fin (n + 1)), f (v i) by simpa [conj, ih]
    constructor
    · intro ⟨hz, hs⟩ i; cases i using Fin.cases; { exact hz }; { exact hs _ }
    · intro h; exact ⟨h 0, fun i => h _⟩


-- @@ L374-385 verbatim
/--
Homomorphisms commute with `k`-ary disjunctions (vector version).
-/
@[simp] lemma disj_hom_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
  (f : F) (v : Fin n → α) : f (disj v) = ∃ i, f (v i) := by
  induction' n with n ih
  · simp [disj]
  · suffices (f (v 0) ∨ ∃ i, f (vecTail v i)) ↔ ∃ i, f (v i) by simpa [disj, ih]
    constructor
    · rintro (H | ⟨i, H⟩); { exact ⟨0, H⟩ }; { exact ⟨i.succ, H⟩ }
    · rintro ⟨i, h⟩
      cases i using Fin.cases; { left; exact h }; { right; exact ⟨_, h⟩ }


-- @@ L387-390 verbatim
@[simp] lemma hom_conj [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) : f (conj v) = conj (f ∘ v) := by
  induction' n with n ih <;> simp [*, conj]

lemma hom_conj₂ [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) : f (conj v) = conj fun i => f (v i) := hom_conj f v


-- @@ L392-395 verbatim
@[simp] lemma hom_disj [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) : f (disj v) = disj (f ∘ v) := by
  induction' n with n ih <;> simp [*, disj]

lemma hom_disj' [FunLike F α β] [LogicalConnective.HomClass F α β] (f : F) (v : Fin n → α) : f (disj v) = disj fun i => f (v i) := hom_disj f v


-- @@ L397-397 verbatim
end Matrix


-- @@ L399-399 verbatim
namespace List


-- @@ L401-401 verbatim
variable {α : Type*}


-- @@ L403-403 verbatim
variable {φ ψ : α}


-- @@ L405-405 verbatim
section tilde


-- @@ L407-407 verbatim
variable [Tilde α]


-- @@ L409-411 verbatim
instance : Tilde (List α) := ⟨fun l ↦ l.map (∼·)⟩

lemma tilde_def (l : List α) : ∼l = l.map (∼·) := rfl


-- @@ L413-413 verbatim
@[simp] lemma tilde_nil : ∼([] : List α) = [] := rfl


-- @@ L415-415 verbatim
@[simp] lemma tilde_cons (a : α) (l : List α) : ∼(a :: l) = ∼a :: ∼l := rfl


-- @@ L417-420 verbatim
@[simp] lemma tilde_append (l k : List α) : ∼(l ++ k) = ∼l ++ ∼k := by
  induction l with
  |          nil => simp [*]
  | cons a as ih => simp [*, List.cons_append]


-- @@ L422-428 verbatim
@[simp] lemma mem_tilde_iff [TildeInvolutive α] {a : α} {l : List α} : a ∈ ∼l ↔ ∼a ∈ l := by
  induction l with
  |          nil => simp [*]
  | cons b bs ih =>
    suffices a = ∼b ↔ ∼a = b by
      simp [ih, this]
    constructor <;> {rintro rfl; simp}


-- @@ L430-435 verbatim
instance [TildeInvolutive α] : TildeInvolutive (List α) where
  tilde_involutive l := by
    induction l with
    |          nil => simp [*]
    | cons a as ih =>
      simp [ih, TildeInvolutive.tilde_involutive a]


-- @@ L437-437 verbatim
end tilde


-- @@ L439-439 verbatim
section conjunction


-- @@ L441-441 verbatim
variable [Top α] [Wedge α]


-- @@ L443-445 verbatim
def conj : List α → α
  |      [] => ⊤
  | a :: as => a ⋏ as.conj


-- @@ L447-447 verbatim
@[simp] lemma conj_nil : conj (α := α) [] = ⊤ := rfl


-- @@ L449-449 verbatim
@[simp] lemma conj_cons {a : α} {as : List α} : conj (a :: as) = a ⋏ as.conj := rfl


-- @@ L451-455 verbatim
/-- Remark: `[φ].conj₂ = φ ≠ φ ⋏ ⊤ = [φ].conj`. -/
def conj₂ : List α → α
|           [] => ⊤
|          [φ] => φ
| φ :: ψ :: rs => φ ⋏ (ψ :: rs).conj₂


-- @@ L457-460 verbatim
/--
The conjunction of a list of members of type `α`.
-/
prefix:80 "⋀" => List.conj₂


-- @@ L462-462 verbatim
@[simp] lemma conj₂_nil : ⋀[] = (⊤ : α) := rfl


-- @@ L464-464 verbatim
@[simp] lemma conj₂_singleton : ⋀[φ] = φ := rfl


-- @@ L466-466 verbatim
@[simp] lemma conj₂_doubleton : ⋀[φ, ψ] = φ ⋏ ψ := rfl


-- @@ L468-471 verbatim
@[simp] lemma conj₂_cons_nonempty {a : α} {as : List α} (h : as ≠ [] := by assumption) : ⋀(a :: as) = a ⋏ ⋀as := by
  cases as with
  | nil => contradiction;
  | cons ψ rs => simp [List.conj₂]


-- @@ L473-473 verbatim
def conj' (f : ι → α) (l : List ι) : α := (l.map f).conj₂


-- @@ L475-475 verbatim
@[simp] lemma conj'_nil (f : ι → α) : conj' f [] = ⊤ := rfl


-- @@ L477-477 verbatim
@[simp] lemma conj'_singleton (f : ι → α) (i : ι) : conj' f [i] = f i := rfl


-- @@ L479-479 verbatim
@[simp] lemma conj'_cons (f : ι → α) (i j : ι) (is : List ι) : conj' f (i :: j :: is) = f i ⋏ conj' f (j :: is) := rfl


-- @@ L481-481 verbatim
end conjunction


-- @@ L483-483 verbatim
section disjunction


-- @@ L485-485 verbatim
variable [Bot α] [Vee α]


-- @@ L487-489 verbatim
def disj : List α → α
  |      [] => ⊥
  | a :: as => a ⋎ as.disj


-- @@ L491-491 verbatim
@[simp] lemma disj_nil : disj (α := α) [] = ⊥ := rfl


-- @@ L493-493 verbatim
@[simp] lemma disj_cons {a : α} {as : List α} : disj (a :: as) = a ⋎ as.disj := rfl


-- @@ L495-499 verbatim
/-- Remark: `[φ].disj₂ = φ ≠ φ ⋎ ⊥ = [φ].disj`. -/
def disj₂ : List α → α
|           [] => ⊥
|          [φ] => φ
| φ :: ψ :: rs => φ ⋎ (ψ :: rs).disj₂


-- @@ L501-504 verbatim
/--
The disjunction of a list of members of type `α`.
-/
prefix:80 "⋁" => disj₂


-- @@ L506-506 verbatim
@[simp] lemma disj₂_nil : ⋁[] = (⊥ : α) := rfl


-- @@ L508-508 verbatim
@[simp] lemma disj₂_singleton : ⋁[φ] = φ := rfl


-- @@ L510-510 verbatim
@[simp] lemma disj₂_doubleton : ⋁[φ, ψ] = φ ⋎ ψ := rfl


-- @@ L512-515 verbatim
@[simp] lemma disj₂_cons_nonempty {a : α} {as : List α} (h : as ≠ [] := by assumption) : ⋁(a :: as) = a ⋎ ⋁as := by
  cases as with
  | nil => contradiction;
  | cons ψ rs => simp [disj₂]


-- @@ L517-517 verbatim
def disj' (f : ι → α) (l : List ι) : α := (l.map f).disj₂


-- @@ L519-519 verbatim
@[simp] lemma disj'_nil (f : ι → α) : disj' f [] = ⊥ := rfl


-- @@ L521-521 verbatim
@[simp] lemma disj'_singleton (f : ι → α) (i : ι) : disj' f [i] = f i := rfl


-- @@ L523-523 verbatim
@[simp] lemma disj'_cons (f : ι → α) (i j : ι) (is : List ι) : disj' f (i :: j :: is) = f i ⋎ disj' f (j :: is) := rfl


-- @@ L525-525 verbatim
end disjunction


-- @@ L527-527 verbatim
section tilde


-- @@ L529-529 verbatim
variable [LogicalConnective α] [LogicalNeutral α] [LogicalNeutral.DeMorgan α] [LogicalConnective.DeMorgan α]


-- @@ L531-537 verbatim
/--
Variadic de Morgan's law for lists of elements of type `α`.
-/
@[simp] lemma tilde_conj (l : List α) : ∼l.disj = (∼l).conj := by
  match l with
  |     [] => simp
  | a :: l => simp [tilde_conj l]


-- @@ L539-545 verbatim
/--
Variadic de Morgan's law for lists of elements of type `α`.
-/
@[simp] lemma tilde_disj (l : List α) : ∼l.conj = (∼l).disj := by
  match l with
  |     [] => simp
  | a :: l => simp [tilde_disj l]


-- @@ L547-554 verbatim
/--
Variadic de Morgan's law for lists of elements of type `α`.
-/
@[simp] lemma tilde_conj₂ (l : List α) : ∼⋁l = ⋀(∼l) := by
  match l with
  |          [] => simp
  |         [a] => simp
  | a :: b :: l => simp [tilde_conj₂ (b :: l)]


-- @@ L556-563 verbatim
/--
Variadic de Morgan's law for lists of elements of type `α`.
-/
@[simp] lemma tilde_disj₂ (l : List α) : ∼⋀l = ⋁(∼l) := by
  match l with
  |          [] => simp
  |         [a] => simp
  | a :: b :: l => simp [tilde_disj₂ (b :: l)]


-- @@ L565-565 verbatim
end tilde


-- @@ L567-567 verbatim
section


-- @@ L569-593 verbatim
variable
  [LogicalConnective α] [LogicalNeutral α]
  [LogicalConnective β] [LogicalNeutral β]
  [FunLike G α β] [LogicalConnective.HomClass G α β]

lemma map_tilde (f : G) (l : List α) : (∼l : List α).map f = ∼(l.map f) := by
  induction l <;> simp [*]

lemma map_conj (f : G) (l : List α) : f l.conj = (l.map f).conj := by
  induction l <;> simp [*]

lemma map_conj₂ (f : G) (l : List α) : f l.conj₂ = (l.map f).conj₂ := by
  induction l using List.induction_with_singleton' <;> simp [*]

lemma map_conj' (F : G) (l : List ι) (f : ι → α) : F (l.conj' f) = l.conj' (F ∘ f) := by
  induction l using List.induction_with_singleton' <;> simp [*]

lemma map_disj (f : G) (l : List α) : f l.disj = (l.map f).disj := by
  induction l <;> simp [*]

lemma map_disj₂ (f : G) (l : List α) : f l.disj₂ = (l.map f).disj₂ := by
  induction l using List.induction_with_singleton' <;> simp [*]

lemma map_disj' (F : G) (l : List ι) (f : ι → α) : F (l.disj' f) = l.disj' (F ∘ f) := by
  induction l using List.induction_with_singleton' <;> simp [*]


-- @@ L595-595 verbatim
end


-- @@ L597-597 verbatim
section


-- @@ L599-599 verbatim
variable [LogicalConnective α] [LogicalNeutral α] [FunLike G α Prop] [LogicalConnective.HomClass G α Prop]


-- @@ L601-602 verbatim
@[simp] lemma map_conj_prop {f : G} {l : List α} : f l.conj ↔ ∀ a ∈ l, f a := by
  induction l <;> simp [*]


-- @@ L604-609 verbatim
@[simp] lemma map_conj₂_prop {f : G} {l : List α} : f l.conj₂ ↔ ∀ a ∈ l, f a := by
  induction l using List.induction_with_singleton' <;> simp [*]

lemma map_conj_append_prop
    (f : G) (l₁ l₂ : List α) : f (l₁ ++ l₂).conj ↔ f (l₁.conj ⋏ l₂.conj) := by
  induction l₁ <;> induction l₂ <;> aesop;


-- @@ L611-613 verbatim
@[simp] lemma map_conj'_prop
    {F : G} {l : List ι} {f : ι → α} : F (l.conj' f) ↔ ∀ i ∈ l, F (f i) := by
  induction l using List.induction_with_singleton' <;> simp [*]


-- @@ L615-617 verbatim
@[simp] lemma map_disj_prop
    {f : G} {l : List α} : f l.disj ↔ ∃ a ∈ l, f a := by
  induction l <;> simp [*]


-- @@ L619-623 verbatim
@[simp] lemma map_disj₂_prop {f : G} {l : List α} : f l.disj₂ ↔ ∃ a ∈ l, f a := by
  induction l using List.induction_with_singleton' <;> simp [*]

lemma map_disj_append_prop (f : G) (l₁ l₂ : List α) : f (l₁ ++ l₂).disj ↔ f (l₁.disj ⋎ l₂.disj) := by
  induction l₁ <;> induction l₂ <;> aesop;


-- @@ L625-627 verbatim
@[simp] lemma map_disj'_prop
    {F : G} {l : List ι} {f : ι → α} : F (l.disj' f) ↔ ∃ i ∈ l, F (f i) := by
  induction l using List.induction_with_singleton' <;> simp [*]


-- @@ L629-629 verbatim
end


-- @@ L631-631 verbatim
end List


-- @@ L633-633 verbatim
namespace Multiset


-- @@ L635-635 verbatim
variable {α : Type*} [Tilde α]


-- @@ L637-639 verbatim
instance : Tilde (Multiset α) := ⟨fun Γ ↦ Γ.map (∼·)⟩

lemma tilde_def (Γ : Multiset α) : ∼Γ = Γ.map (∼·) := rfl


-- @@ L641-641 verbatim
@[simp] lemma tilde_zero : ∼(0 : Multiset α) = 0 := rfl


-- @@ L643-644 verbatim
@[simp] lemma tilde_add (Γ Δ : Multiset α) : ∼(Γ + Δ) = ∼Γ + ∼Δ := by
  simp [tilde_def]


-- @@ L646-647 verbatim
@[simp] lemma tilde_atom (φ : α) : ∼(⦃φ⦄ : Multiset α) = ⦃∼φ⦄ := by
  simp [tilde_def]


-- @@ L649-657 verbatim
@[simp] lemma mem_tilde_iff [TildeInvolutive α] {φ : α} {Γ : Multiset α} :
    φ ∈ ∼Γ ↔ ∼φ ∈ Γ := by
  rw [tilde_def]
  constructor
  · intro h
    rcases Multiset.mem_map.mp h with ⟨ψ, hψ, rfl⟩
    simpa using hψ
  · intro hφ
    simpa using Multiset.mem_map_of_mem (fun ψ ↦ ∼ψ) hφ


-- @@ L659-660 verbatim
instance [TildeInvolutive α] : TildeInvolutive (Multiset α) where
  tilde_involutive Γ := by simp [tilde_def, Multiset.map_map]


-- @@ L662-662 verbatim
end Multiset


-- @@ L664-664 verbatim
namespace Finset


-- @@ L666-666 verbatim
open Classical


-- @@ L668-668 verbatim
variable {α : Type*}


-- @@ L670-670 verbatim
section tilde


-- @@ L672-672 verbatim
variable [Tilde α] [TildeInvolutive α]


-- @@ L674-676 verbatim
instance : Tilde (Finset α) := ⟨fun l ↦ l.map Tilde.invol⟩

lemma tilde_def (s : Finset α) : ∼s = s.map Tilde.invol := rfl


-- @@ L678-679 verbatim
@[simp] lemma mem_tilde_iff {a : α} {s : Finset α} : a ∈ ∼s ↔ ∼a ∈ s := by
  simp [tilde_def]; grind


-- @@ L681-682 verbatim
instance : TildeInvolutive (Finset α) where
  tilde_involutive s := by ext a; simp


-- @@ L684-684 verbatim
@[simp] lemma tilde_empty : ∼(∅ : Finset α) = ∅ := rfl


-- @@ L686-687 verbatim
@[simp] lemma tilde_insert (a : α) (s : Finset α) : ∼(insert a s) = insert (∼a) (∼s) := by
  simp [tilde_def]


-- @@ L689-690 verbatim
@[simp] lemma tilde_union (s t : Finset α) : ∼(s ∪ t) = ∼s ∪ ∼t := by
  simp [tilde_def, Finset.map_union]


-- @@ L692-692 verbatim
end tilde


-- @@ L694-694 verbatim
noncomputable def conj [Top α] [Wedge α] (s : Finset α) : α := s.toList.conj₂


-- @@ L696-696 verbatim
noncomputable def conj' [Top α] [Wedge α] (s : Finset ι) (f : ι → α) : α := s.toList.conj' f


-- @@ L698-698 verbatim
noncomputable def uconj [Top α] [Wedge α] [Fintype ι] (f : ι → α) : α := (Finset.univ : Finset ι).conj' f


-- @@ L700-700 verbatim
noncomputable def disj [Bot α] [Vee α] (s : Finset α) : α := s.toList.disj₂


-- @@ L702-702 verbatim
noncomputable def disj' [Bot α] [Vee α] (s : Finset ι) (f : ι → α) : α := s.toList.disj' f


-- @@ L704-704 verbatim
noncomputable def udisj [Bot α] [Vee α] [Fintype ι] (f : ι → α) : α := (Finset.univ : Finset ι).disj' f


-- @@ L706-706 verbatim
section


-- @@ L708-708 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L710-714 verbatim
/--
- `⩕ i ∈ s, φ i` is notation for `s.conj' fun i ↦ φ i`
- `⩕ i, φ i` is notation for `uconj fun i ↦ φ i`
-/
syntax (name := biguconj) "⩕ " Parser.Term.funBinder (" : " term)? (" ∈ " term)? ", " term:0 : term


-- @@ L716-720 verbatim
macro_rules (kind := biguconj)
  |           `(⩕ $i:ident : $ι, $v) => `(uconj fun $i : $ι ↦ $v)
  |                `(⩕ $i:ident, $v) => `(uconj fun $i ↦ $v)
  | `(⩕ $i:ident : $ι ∈ $s:term, $v) => `(Finset.conj' $s fun $i : $ι ↦ $v)
  |      `(⩕ $i:ident ∈ $s:term, $v) => `(Finset.conj' $s fun $i ↦ $v)


-- @@ L722-725 verbatim
@[app_unexpander uconj]
meta def uconjUnexpsnder : Unexpander
  | `($_ fun $i ↦ $v) => `(⩕ $i, $v)
  |                 _ => throw ()


-- @@ L727-730 verbatim
@[app_unexpander Finset.conj']
meta def conj'Unexpsnder : Unexpander
  | `($_ $s fun $i ↦ $v) => `(⩕ $i ∈ $s, $v)
  |                    _ => throw ()


-- @@ L732-736 verbatim
/--
- `⩖ i ∈ s, φ i` is notation for `s.disj' fun i ↦ φ i`
- `⩖ i, φ i` is notation for `udisj fun i ↦ φ i`
-/
syntax (name := bigudisj) "⩖ " Parser.Term.funBinder (" : " term)? (" ∈ " term)? ", " term:0 : term


-- @@ L738-742 verbatim
macro_rules (kind := bigudisj)
  |           `(⩖ $i:ident : $ι, $v) => `(udisj fun $i : $ι ↦ $v)
  |                `(⩖ $i:ident, $v) => `(udisj fun $i ↦ $v)
  | `(⩖ $i:ident : $ι ∈ $s:term, $v) => `(Finset.disj' $s fun $i : $ι ↦ $v)
  |      `(⩖ $i:ident ∈ $s:term, $v) => `(Finset.disj' $s fun $i ↦ $v)


-- @@ L744-747 verbatim
@[app_unexpander udisj]
meta def udisjUnexpsnder : Unexpander
  | `($_ fun $i ↦ $v) => `(⩖ $i, $v)
  |                 _ => throw ()


-- @@ L749-752 verbatim
@[app_unexpander Finset.disj']
meta def disj'Unexpsnder : Unexpander
  | `($_ $s fun $i ↦ $v) => `(⩖ $i ∈ $s, $v)
  |                    _ => throw ()


-- @@ L754-754 verbatim
end


-- @@ L756-756 verbatim
section conjunction


-- @@ L758-758 verbatim
variable [Top α] [Wedge α]


-- @@ L760-760 verbatim
@[simp] lemma conj_empty : conj (∅ : Finset α) = ⊤ := by simp [conj]


-- @@ L762-762 verbatim
@[simp] lemma conj_singleton (a : α) : conj {a} = a := by simp [conj]


-- @@ L764-764 verbatim
@[simp] lemma conj'_empty (f : ι → α) : (∅ : Finset ι).conj' f = ⊤ := by simp [conj']


-- @@ L766-766 verbatim
@[simp] lemma conj'_singleton (f : ι → α) {i : ι} : ({i} : Finset ι).conj' f = f i := by simp [conj']


-- @@ L768-768 verbatim
@[simp] lemma uconj_empty [Fintype ι] [IsEmpty ι] (f : ι → α) : uconj f = ⊤ := by simp [uconj]


-- @@ L770-770 verbatim
@[simp] lemma uconj_singleton [Fintype ι] [Unique ι] (f : ι → α) : uconj f = f default := by simp [uconj]


-- @@ L772-772 verbatim
end conjunction


-- @@ L774-774 verbatim
section disjunction


-- @@ L776-776 verbatim
variable [Bot α] [Vee α]


-- @@ L778-778 verbatim
@[simp] lemma disj_empty : (∅ : Finset α).disj = ⊥ := by simp [disj]


-- @@ L780-780 verbatim
@[simp] lemma disj_singleton (a : α) : ({a} : Finset α).disj = a := by simp [disj]


-- @@ L782-782 verbatim
@[simp] lemma disj'_empty (f : ι → α) : (∅ : Finset ι).disj' f = ⊥ := by simp [disj']


-- @@ L784-784 verbatim
@[simp] lemma disj'_singleton (f : ι → α) (i : ι) : ({i} : Finset ι).disj' f = f i := by simp [disj']


-- @@ L786-786 verbatim
@[simp] lemma udisj_empty [Fintype ι] [IsEmpty ι] (f : ι → α) : udisj f = ⊥ := by simp [udisj]


-- @@ L788-788 verbatim
@[simp] lemma udisj_singleton [Fintype ι] [Unique ι] (f : ι → α) : udisj f = f default := by simp [udisj]


-- @@ L790-790 verbatim
end disjunction


-- @@ L792-794 verbatim
variable
  [LogicalConnective α] [LogicalNeutral α]
  [LogicalConnective β] [LogicalNeutral β]


-- @@ L796-807 verbatim
@[simp] lemma map_conj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
    {f : F} {s : Finset α} : f s.conj ↔ ∀ a ∈ s, f a := by
  simp [conj]

lemma map_conj_union [DecidableEq α] [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
    (f : F) (s₁ s₂ : Finset α) : f (s₁ ∪ s₂).conj ↔ f (s₁.conj ⋏ s₂.conj) := by
  suffices (∀ (a : α), a ∈ s₁ ∨ a ∈ s₂ → f a) ↔ (∀ a ∈ s₁, f a) ∧ ∀ a ∈ s₂, f a by simpa
  grind

lemma map_conj' [FunLike F α β] [LogicalConnective.HomClass F α β]
    (Φ : F) (s : Finset ι) (f : ι → α) : Φ (⩕ i ∈ s, f i) = ⩕ i ∈ s, Φ (f i) := by
  simp [conj', Function.comp_def, List.map_conj']


-- @@ L809-814 verbatim
@[simp] lemma map_conj'_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] {f : F} {s : Finset ι} {p : ι → α} :
    f (s.conj' p) ↔ ∀ i ∈ s, f (p i) := by simp [conj']

lemma map_uconj [FunLike F α β] [LogicalConnective.HomClass F α β]
    (Φ : F) [Fintype ι] (f : ι → α) : Φ (⩕ i, f i) = ⩕ i, Φ (f i) := by
  simp [uconj, map_conj']


-- @@ L816-817 verbatim
@[simp] lemma map_uconj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] {Φ : F} [Fintype ι] {f : ι → α} :
    Φ (uconj f) ↔ ∀ i, Φ (f i) := by simp [uconj]


-- @@ L819-829 verbatim
@[simp] lemma map_disj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] (f : F) (s : Finset α) : f s.disj ↔ ∃ a ∈ s, f a := by
  simp [disj]

lemma map_disj_union [DecidableEq α] [FunLike F α Prop] [LogicalConnective.HomClass F α Prop]
    (f : F) (s₁ s₂ : Finset α) : f (s₁ ∪ s₂).disj ↔ f (s₁.disj ⋎ s₂.disj) := by
  suffices (∃ a, (a ∈ s₁ ∨ a ∈ s₂) ∧ f a) ↔ (∃ a ∈ s₁, f a) ∨ ∃ a ∈ s₂, f a by simpa [map_disj_prop]
  grind

lemma map_disj' [FunLike F α β] [LogicalConnective.HomClass F α β]
    (Φ : F) (s : Finset ι) (f : ι → α) : Φ (⩖ i ∈ s, f i) = ⩖ i ∈ s, Φ (f i) := by
  simp [disj', List.map_disj', Function.comp_def]


-- @@ L831-836 verbatim
@[simp] lemma map_disj'_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] {f : F} {s : Finset ι} {p : ι → α} :
    f (s.disj' p) ↔ ∃ i ∈ s, f (p i) := by simp [disj']

lemma map_udisj [FunLike F α β] [LogicalConnective.HomClass F α β]
    (Φ : F) [Fintype ι] (f : ι → α) : Φ (⩖ i, f i) = ⩖ i, Φ (f i) := by
  simp [udisj, map_disj']


-- @@ L838-839 verbatim
@[simp] lemma map_udisj_prop [FunLike F α Prop] [LogicalConnective.HomClass F α Prop] {Φ : F} [Fintype ι] {f : ι → α} :
    Φ (udisj f) ↔ ∃ i, Φ (f i) := by simp [udisj]


-- @@ L841-841 verbatim
end Finset


-- @@ L843-843 verbatim
end
