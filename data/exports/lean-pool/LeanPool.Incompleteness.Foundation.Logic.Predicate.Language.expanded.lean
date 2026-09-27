/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Encodable.Basic
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToDual
import Mathlib.Algebra.Order.Ring.Nat


-- @@ L14-22 verbatim
/-!
# Language of first-order logic

This file defines the language of first-order logic.

- `LO.FirstOrder.Language.empty` is the empty language.
- `LO.FirstOrder.Language.constant C` is a language with only constants of the element `C`.
- `LO.FirstOrder.Language.oRing`, `ℒₒᵣ` is the language of ordered ring.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace LO


-- @@ L28-28 verbatim
namespace FirstOrder


-- @@ L30-35 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Language where
  /-- Imported declaration from the Incompleteness formalization. -/
  Func : Nat → Type u
  /-- Imported declaration from the Incompleteness formalization. -/
  Rel  : Nat → Type u


-- @@ L37-37 verbatim
namespace Language


-- @@ L39-41 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class IsRelational (L : Language) where
  func_empty : ∀ k, IsEmpty (L.Func (k + 1))


-- @@ L43-45 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class IsConstant (L : Language) extends IsRelational L where
  rel_empty : ∀ k, IsEmpty (L.Rel k)


-- @@ L47-48 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class ConstantInhabited (L : Language) extends Inhabited (L.Func 0)


-- @@ L50-50 verbatim
instance {L : Language} [L.ConstantInhabited] : Inhabited (L.Func 0) := inferInstance


-- @@ L52-55 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected def empty : Language where
  Func := fun _ => PEmpty
  Rel  := fun _ => PEmpty


-- @@ L57-57 verbatim
instance : Inhabited Language := ⟨Language.empty⟩


-- @@ L59-62 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive GraphFunc : ℕ → Type
  | start : GraphFunc 0
  | terminal : GraphFunc 0


-- @@ L64-67 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive GraphRel : ℕ → Type
  | equal : GraphRel 2
  | le : GraphRel 2


-- @@ L69-72 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def graph : Language where
  Func := GraphFunc
  Rel := GraphRel


-- @@ L74-78 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive BinaryRel : ℕ → Type
  | isone : BinaryRel 1
  | equal : BinaryRel 2
  | le : BinaryRel 2


-- @@ L80-83 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def binary : Language where
  Func := fun _ => Empty
  Rel := BinaryRel


-- @@ L85-87 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive EqRel : ℕ → Type
  | equal : EqRel 2


-- @@ L89-93 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def equal : Language where
  Func := fun _ => Empty
  Rel := EqRel


-- @@ L95-95 verbatim
instance (k) : ToString (equal.Func k) := ⟨fun _ => ""⟩


-- @@ L97-97 verbatim
instance (k) : ToString (equal.Rel k) := ⟨fun _ => "\\mathrm{Eq}"⟩


-- @@ L99-99 verbatim
instance (k) : DecidableEq (equal.Func k) := fun a b => by rcases a


-- @@ L101-101 verbatim
instance (k) : DecidableEq (equal.Rel k) := fun a b => by rcases a; rcases b; exact isTrue (by simp)


-- @@ L103-103 verbatim
instance (k) : Encodable (equal.Func k) := IsEmpty.toEncodable


-- @@ L105-111 verbatim
instance (k) : Encodable (equal.Rel k) where
  encode := fun _ => 0
  decode := fun _ =>
    match k with
    | 2 => some EqRel.equal
    | _ => none
  encodek := fun x => by rcases x; simp


-- @@ L113-113 verbatim
namespace ORing


-- @@ L115-120 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | add : Func 2
  | mul : Func 2


-- @@ L122-125 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive Rel : ℕ → Type
  | eq : Rel 2
  | lt : Rel 2


-- @@ L127-127 verbatim
end ORing


-- @@ L129-133 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[reducible]
def oRing : Language where
  Func := ORing.Func
  Rel := ORing.Rel


-- @@ L135-136 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "ℒₒᵣ" => oRing


-- @@ L138-138 verbatim
namespace ORing


-- @@ L140-146 verbatim
instance (k) : ToString (oRing.Func k) :=
⟨ fun s =>
  match s with
  | Func.zero => "0"
  | Func.one  => "1"
  | Func.add  => "(+)"
  | Func.mul  => "(\\cdot)"⟩


-- @@ L148-152 verbatim
instance (k) : ToString (oRing.Rel k) :=
⟨ fun s =>
  match s with
  | Rel.eq => "\\mathrm{Eq}"
  | Rel.lt    => "\\mathrm{LT}"⟩


-- @@ L154-158 verbatim
instance (k) : DecidableEq (oRing.Func k) := fun a b =>
  by
    rcases a <;> rcases b <;> simp only [reduceCtorEq] <;>
      try {exact instDecidableTrue} <;>
      try {exact instDecidableFalse}


-- @@ L160-164 verbatim
instance (k) : DecidableEq (oRing.Rel k) := fun a b =>
  by
    rcases a <;> rcases b <;> simp only [reduceCtorEq] <;>
      try {exact instDecidableTrue} <;>
      try {exact instDecidableFalse}


-- @@ L166-180 verbatim
instance (k) : Encodable (oRing.Func k) where
  encode := fun x =>
    match x with
    | Func.zero => 0
    | Func.one  => 1
    | Func.add  => 0
    | Func.mul  => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some Func.zero
    | 0, 1 => some Func.one
    | 2, 0 => some Func.add
    | 2, 1 => some Func.mul
    | _, _ => none
  encodek := fun x => by rcases x <;> simp


-- @@ L182-182 verbatim
instance Func1IsEmpty : IsEmpty (oRing.Func 1) := ⟨by rintro ⟨⟩⟩


-- @@ L184-189 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
theorem FuncGe3IsEmpty : ∀ k ≥ 3, IsEmpty (oRing.Func k)
  | 0       => by simp
  | 1       => by simp [show ¬3 ≤ 1 from of_decide_eq_false rfl]
  | 2       => by simp [show ¬3 ≤ 2 from of_decide_eq_false rfl]
  | (n + 3) => fun _ => ⟨by rintro ⟨⟩⟩


-- @@ L191-201 verbatim
instance (k) : Encodable (oRing.Rel k) where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.lt => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.lt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp


-- @@ L203-228 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def funcEquivFinFour : (k : ℕ) × oRing.Func k ≃ Fin 4 where
  toFun f :=
    match f with
    | ⟨0, Func.zero⟩ => 0
    | ⟨0,  Func.one⟩ => 1
    | ⟨2,  Func.add⟩ => 2
    | ⟨2,  Func.mul⟩ => 3
  invFun x :=
    match x with
    | 0 => ⟨0, Func.zero⟩
    | 1 => ⟨0,  Func.one⟩
    | 2 => ⟨2,  Func.add⟩
    | 3 => ⟨2,  Func.mul⟩
  left_inv f :=
    match f with
    | ⟨0, Func.zero⟩ => rfl
    | ⟨0,  Func.one⟩ => rfl
    | ⟨2,  Func.add⟩ => rfl
    | ⟨2,  Func.mul⟩ => rfl
  right_inv x :=
    match x with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl


-- @@ L230-247 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def relEquivFinTwo : (k : ℕ) × oRing.Rel k ≃ Fin 2 where
  toFun f :=
    match f with
    | ⟨2, Rel.eq⟩ => 0
    | ⟨2, Rel.lt⟩ => 1
  invFun x :=
    match x with
    | 0 => ⟨2, Rel.eq⟩
    | 1 => ⟨2, Rel.lt⟩
  left_inv f :=
    match f with
    | ⟨2, Rel.eq⟩ => rfl
    | ⟨2, Rel.lt⟩ => rfl
  right_inv x :=
    match x with
    | 0 => rfl
    | 1 => rfl


-- @@ L249-249 verbatim
end ORing


-- @@ L251-251 verbatim
namespace Constant


-- @@ L253-253 verbatim
variable (C : Type*)


-- @@ L255-257 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive Func : ℕ → Type _
  | const (c : C) : Func 0


-- @@ L259-259 verbatim
end Constant


-- @@ L261-261 verbatim
section «lp_section_1»


-- @@ L263-263 verbatim
variable (C : Type*)


-- @@ L265-268 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Language.constLang : Language := ⟨Constant.Func C, fun _ => PEmpty⟩

--instance : Coe (Type*) Language := ⟨constLang⟩


-- @@ L270-270 verbatim
instance : Coe C ((constLang C).Func 0) := ⟨Constant.Func.const⟩


-- @@ L272-274 verbatim
instance : IsConstant (constLang C) where
  func_empty := fun k => ⟨by rintro ⟨⟩⟩
  rel_empty  := fun k => ⟨by rintro ⟨⟩⟩


-- @@ L276-277 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev unit : Language := constLang PUnit


-- @@ L279-279 verbatim
end «lp_section_1»


-- @@ L281-282 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def ofFunc (F : ℕ → Type v) : Language := ⟨F, fun _ => PEmpty⟩


-- @@ L284-286 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def add (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) : Language :=
  ⟨fun k => L₁.Func k ⊕ L₂.Func k, fun k => L₁.Rel k ⊕ L₂.Rel k⟩


-- @@ L288-288 verbatim
instance : _root_.Add Language := ⟨add⟩


-- @@ L290-291 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def sigma (L : ι → Language) : Language := ⟨fun k => Σ i, (L i).Func k, fun k => Σ i, (L i).Rel k⟩


-- @@ L293-296 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Eq (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  eq : L.Rel 2


-- @@ L298-301 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class LT (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  lt : L.Rel 2


-- @@ L303-306 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Zero (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  zero : L.Func 0


-- @@ L308-311 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class One (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  one : L.Func 0


-- @@ L313-316 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Add (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  add : L.Func 2


-- @@ L318-321 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Mul (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  mul : L.Func 2


-- @@ L323-326 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Pow (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  pow : L.Func 2


-- @@ L328-331 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Exp (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  exp : L.Func 1


-- @@ L333-336 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Pairing (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  pair : L.Func 2


-- @@ L338-341 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class Star (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  star : L.Func 0


-- @@ L343-343 verbatim
attribute [match_pattern] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt Star.star


-- @@ L345-346 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class ORing (L : Language) extends L.Eq, L.LT, L.Zero, L.One, L.Add, L.Mul


-- @@ L348-354 verbatim
instance : ORing oRing where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul


-- @@ L356-357 expanded
instance : ConstantInhabited oRing where default := Language.Zero.zero


-- @@ L359-360 verbatim
instance : Star unit where
  star := ()


-- @@ L362-363 verbatim
instance (L : Language) (S : Language) [Star S] : Star (L.add S) where
  star := Sum.inr Star.star


-- @@ L365-366 verbatim
instance (L : Language) (S : Language) [L.Zero] : (L.add S).Zero where
  zero := Sum.inl Zero.zero


-- @@ L368-369 verbatim
instance (L : Language) (S : Language) [L.One] : (L.add S).One where
  one := Sum.inl One.one


-- @@ L371-372 verbatim
instance (L : Language) (S : Language) [L.Add] : (L.add S).Add where
  add := Sum.inl Add.add


-- @@ L374-375 verbatim
instance (L : Language) (S : Language) [L.Mul] : (L.add S).Mul where
  mul := Sum.inl Mul.mul


-- @@ L377-378 verbatim
instance (L : Language) (S : Language) [L.Eq] : (L.add S).Eq where
  eq := Sum.inl Eq.eq


-- @@ L380-381 verbatim
instance (L : Language) (S : Language) [L.LT] : (L.add S).LT where
  lt := Sum.inl LT.lt


-- @@ L383-388 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure Hom (L₁ L₂ : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  func : {k : ℕ} → L₁.Func k → L₂.Func k
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : {k : ℕ} → L₁.Rel k → L₂.Rel k


-- @@ L390-391 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped[LO.FirstOrder] infix:25 " →ᵥ " => LO.FirstOrder.Language.Hom


-- @@ L393-393 verbatim
namespace Hom

-- @@ L394-394 verbatim
variable (L L₁ L₂ L₃ : Language) (Φ : Hom L₁ L₂)


-- @@ L396-399 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected def id : L →ᵥ L where
  func := id
  rel := id


-- @@ L401-401 verbatim
variable {L L₁ L₂ L₃}


-- @@ L403-406 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def comp (Ψ : L₂ →ᵥ L₃) (Φ : L₁ →ᵥ L₂) : L₁ →ᵥ L₃ where
  func := Ψ.func ∘ Φ.func
  rel  := Ψ.rel ∘ Φ.rel


-- @@ L408-409 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def add₁ (L₁ : Language) (L₂ : Language) : L₁ →ᵥ L₁.add L₂ := ⟨Sum.inl, Sum.inl⟩


-- @@ L411-412 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def add₂ (L₁ : Language) (L₂ : Language) : L₂ →ᵥ L₁.add L₂ := ⟨Sum.inr, Sum.inr⟩


-- @@ L414-416 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
lemma func_add₁ (L₁ : Language) (L₂ : Language) (f : L₁.Func k) :
    (add₁ L₁ L₂).func f = Sum.inl f := rfl


-- @@ L418-419 verbatim
lemma rel_add₁ (L₁ : Language) (L₂ : Language) (r : L₁.Rel k) :
    (add₁ L₁ L₂).rel r = Sum.inl r := rfl


-- @@ L421-422 verbatim
lemma func_add₂ (L₁ : Language) (L₂ : Language) (f : L₂.Func k) :
    (add₂ L₁ L₂).func f = Sum.inr f := rfl


-- @@ L424-425 verbatim
lemma rel_add₂ (L₁ : Language) (L₂ : Language) (r : L₂.Rel k) :
    (add₂ L₁ L₂).rel r = Sum.inr r := rfl


-- @@ L427-428 verbatim
@[simp] lemma add₂_star (L₁ : Language) (L₂ : Language) [Star L₂] :
    (add₂ L₁ L₂).func Star.star = Star.star := rfl


-- @@ L430-431 verbatim
@[simp] lemma add₁_zero (L₁ : Language) (L₂ : Language) [L₁.Zero] :
    (add₁ L₁ L₂).func Zero.zero = Zero.zero := rfl


-- @@ L433-434 verbatim
@[simp] lemma add₁_one (L₁ : Language) (L₂ : Language) [L₁.One] :
    (add₁ L₁ L₂).func One.one = One.one := rfl


-- @@ L436-437 verbatim
@[simp] lemma add₁_add (L₁ : Language) (L₂ : Language) [L₁.Add] :
    (add₁ L₁ L₂).func Add.add = Add.add := rfl


-- @@ L439-440 verbatim
@[simp] lemma add₁_mul (L₁ : Language) (L₂ : Language) [L₁.Mul] :
    (add₁ L₁ L₂).func Mul.mul = Mul.mul := rfl


-- @@ L442-443 verbatim
@[simp] lemma add₁_eq (L₁ : Language) (L₂ : Language) [L₁.Eq] :
    (add₁ L₁ L₂).rel Eq.eq = Eq.eq := rfl


-- @@ L445-446 verbatim
@[simp] lemma add₁_lt (L₁ : Language) (L₂ : Language) [L₁.LT] :
    (add₁ L₁ L₂).rel LT.lt = LT.lt := rfl


-- @@ L448-449 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def sigma (L : ι → Language) (i : ι) : L i →ᵥ Language.sigma L := ⟨fun f => ⟨i, f⟩, fun r => ⟨i, r⟩⟩


-- @@ L451-451 verbatim
lemma func_sigma (L : ι → Language) (i : ι) (f : (L i).Func k) : (sigma L i).func f = ⟨i, f⟩ := rfl


-- @@ L453-453 verbatim
lemma rel_sigma (L : ι → Language) (i : ι) (r : (L i).Rel k) : (sigma L i).rel r = ⟨i, r⟩ := rfl


-- @@ L455-455 verbatim
end Hom


-- @@ L457-468 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Language.ORing.embedding (L : Language) [ORing L] : oRing →ᵥ L
    where
  func := fun {n} f ↦
    match n, f with
    | 0, Zero.zero => Zero.zero
    | 0, One.one => One.one
    | 2, Add.add => Add.add
    | 2, Mul.mul => Mul.mul
  rel := fun {n} r ↦
    match n, r with
    | 2, Eq.eq => Eq.eq
    | 2, LT.lt => LT.lt


-- @@ L469-469 verbatim
end Language


-- @@ L471-476 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class _root_.LO.FirstOrder.Language.DecidableEq (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  func : (k : ℕ) → DecidableEq (L.Func k)
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : (k : ℕ) → DecidableEq (L.Rel k)


-- @@ L478-480 verbatim
instance (L : Language) [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] :
    L.DecidableEq :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩


-- @@ L482-483 verbatim
instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Func k) :=
  Language.DecidableEq.func k


-- @@ L485-486 verbatim
instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Rel k) :=
  Language.DecidableEq.rel k


-- @@ L488-489 verbatim
instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Rel k) :=
  Language.DecidableEq.rel k


-- @@ L491-496 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.FirstOrder.Language.Finite (L : Language) where
  /-- Imported declaration from the Incompleteness formalization. -/
  func : Fintype ((k : ℕ) × L.Func k)
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : Fintype ((k : ℕ) × L.Rel k)


-- @@ L498-500 expanded
instance : Language.Finite oRing
    where
  func := Fintype.ofEquiv (Fin 4) Language.ORing.funcEquivFinFour.symm
  rel := Fintype.ofEquiv (Fin 2) Language.ORing.relEquivFinTwo.symm


-- @@ L502-502 verbatim
end FirstOrder


-- @@ L504-504 verbatim
end LO
