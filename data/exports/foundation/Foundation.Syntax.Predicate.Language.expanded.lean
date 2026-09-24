module

public import Foundation.Logic.Entailment
public import Mathlib.Logic.Encodable.Basic


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-16 verbatim
/-!
# Language of first-order logic

This file defines the language of first-order logic.

- `FFL.FirstOrder.Language.empty` is the empty language.
- `FFL.FirstOrder.Language.constant C` is a language with only constants of the element `C`.
- `FFL.FirstOrder.Language.oRing`, `ℒₒᵣ` is the language of ordered ring.
-/


-- @@ L18-18 verbatim
namespace FFL


-- @@ L20-20 verbatim
namespace FirstOrder


-- @@ L22-24 verbatim
structure Language where
  Func : Nat → Type u
  Rel  : Nat → Type u


-- @@ L26-26 verbatim
namespace Language


-- @@ L28-29 verbatim
class Relational (L : Language) where
  func_empty : ∀ k, IsEmpty (L.Func k)


-- @@ L31-31 verbatim
instance {L : Language} [L.Relational] : IsEmpty (L.Func k) := Relational.func_empty k


-- @@ L33-35 verbatim
class IsConstant (L : Language) where
  func_empty : ∀ k, IsEmpty (L.Func (k + 1))
  rel_empty  : ∀ k, IsEmpty (L.Rel k)


-- @@ L37-37 verbatim
class ConstantInhabited (L : Language) extends Inhabited (L.Func 0)


-- @@ L39-39 verbatim
instance {L : Language} [L.ConstantInhabited] : Inhabited (L.Func 0) := inferInstance


-- @@ L41-43 verbatim
protected def empty : Language where
  Func := fun _ => PEmpty
  Rel  := fun _ => PEmpty


-- @@ L45-45 verbatim
instance : Inhabited Language := ⟨Language.empty⟩


-- @@ L47-49 verbatim
inductive GraphFunc : ℕ → Type
  | start : GraphFunc 0
  | terminal : GraphFunc 0


-- @@ L51-53 verbatim
inductive GraphRel : ℕ → Type
  | equal : GraphRel 2
  | le : GraphRel 2


-- @@ L55-57 verbatim
def graph : Language where
  Func := GraphFunc
  Rel := GraphRel


-- @@ L59-62 verbatim
inductive BinaryRel : ℕ → Type
  | isone : BinaryRel 1
  | equal : BinaryRel 2
  | le : BinaryRel 2


-- @@ L64-66 verbatim
def binary : Language where
  Func := fun _ => Empty
  Rel := BinaryRel


-- @@ L68-69 verbatim
inductive EqRel : ℕ → Type
  | equal : EqRel 2


-- @@ L71-74 verbatim
@[reducible]
def equal : Language where
  Func := fun _ => Empty
  Rel := EqRel


-- @@ L76-76 verbatim
instance (k) : ToString (equal.Func k) := ⟨fun _ => ""⟩


-- @@ L78-78 verbatim
instance (k) : ToString (equal.Rel k) := ⟨fun _ => "\\mathrm{Eq}"⟩


-- @@ L80-80 verbatim
instance (k) : DecidableEq (equal.Func k) := fun a b => by rcases a


-- @@ L82-82 verbatim
instance (k) : DecidableEq (equal.Rel k) := fun a b => by rcases a; rcases b; exact isTrue (by simp)


-- @@ L84-84 verbatim
instance (k) : Encodable (equal.Func k) := IsEmpty.toEncodable


-- @@ L86-92 verbatim
instance (k) : Encodable (equal.Rel k) where
  encode := fun _ => 0
  decode := fun _ =>
    match k with
    | 2 => some EqRel.equal
    | _ => none
  encodek := fun x => by rcases x; simp


-- @@ L94-94 verbatim
namespace ORing


-- @@ L96-100 verbatim
inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | add : Func 2
  | mul : Func 2


-- @@ L102-104 verbatim
inductive Rel : ℕ → Type
  | eq : Rel 2
  | lt : Rel 2


-- @@ L106-106 verbatim
end ORing


-- @@ L108-111 verbatim
@[reducible]
def oRing : Language where
  Func := ORing.Func
  Rel := ORing.Rel


-- @@ L113-113 verbatim
notation "ℒₒᵣ" => oRing


-- @@ L115-115 verbatim
namespace ORing


-- @@ L117-123 verbatim
instance (k) : ToString (oRing.Func k) :=
⟨ fun s =>
  match s with
  | Func.zero => "0"
  | Func.one  => "1"
  | Func.add  => "(+)"
  | Func.mul  => "(\\cdot)"⟩


-- @@ L125-129 verbatim
instance (k) : ToString (oRing.Rel k) :=
⟨ fun s =>
  match s with
  | Rel.eq => "\\mathrm{Eq}"
  | Rel.lt    => "\\mathrm{LT}"⟩


-- @@ L131-133 verbatim
instance (k) : DecidableEq (oRing.Func k) := fun a b => by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}


-- @@ L135-137 verbatim
instance (k) : DecidableEq (oRing.Rel k) := fun a b => by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> try {exact instDecidableFalse}


-- @@ L139-153 verbatim
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


-- @@ L155-155 verbatim
instance Func1IsEmpty : IsEmpty (oRing.Func 1) := ⟨by rintro ⟨⟩⟩


-- @@ L157-161 verbatim
lemma FuncGe3IsEmpty : ∀ k ≥ 3, IsEmpty (oRing.Func k)
  | 0       => by simp
  | 1       => by simp [show ¬3 ≤ 1 from of_decide_eq_false rfl]
  | 2       => by simp [show ¬3 ≤ 2 from of_decide_eq_false rfl]
  | (n + 3) => fun _ => ⟨by rintro ⟨⟩⟩


-- @@ L163-173 verbatim
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


-- @@ L175-199 verbatim
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


-- @@ L201-217 verbatim
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


-- @@ L219-219 verbatim
end ORing


-- @@ L221-221 verbatim
namespace Constant


-- @@ L223-223 verbatim
variable (C : Type*)


-- @@ L225-226 verbatim
inductive Func : ℕ → Type _
  | const (c : C) : Func 0


-- @@ L228-228 verbatim
end Constant


-- @@ L230-230 verbatim
section Constant


-- @@ L232-232 verbatim
variable (C : Type*)


-- @@ L234-236 verbatim
def constant : Language := ⟨Constant.Func C, fun _ => PEmpty⟩

--instance : Coe (Type*) Language := ⟨constant⟩


-- @@ L238-238 verbatim
instance : Coe C ((constant C).Func 0) := ⟨Constant.Func.const⟩


-- @@ L240-242 verbatim
instance : IsConstant (constant C) where
  func_empty := fun k => ⟨by rintro ⟨⟩⟩
  rel_empty  := fun k => ⟨by rintro ⟨⟩⟩


-- @@ L244-244 verbatim
abbrev unit : Language := constant PUnit


-- @@ L246-246 verbatim
end Constant


-- @@ L248-248 verbatim
def ofFunc (F : ℕ → Type v) : Language := ⟨F, fun _ => PEmpty⟩


-- @@ L250-251 verbatim
def add (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) : Language :=
  ⟨fun k => L₁.Func k ⊕ L₂.Func k, fun k => L₁.Rel k ⊕ L₂.Rel k⟩


-- @@ L253-253 verbatim
instance : _root_.Add Language := ⟨add⟩


-- @@ L255-255 verbatim
def sigma (L : ι → Language) : Language := ⟨fun k => Σ i, (L i).Func k, fun k => Σ i, (L i).Rel k⟩


-- @@ L257-258 verbatim
protected class Eq (L : Language) where
  eq : L.Rel 2


-- @@ L260-261 verbatim
protected class LT (L : Language) where
  lt : L.Rel 2


-- @@ L263-264 verbatim
protected class Mem (L : Language) where
  mem : L.Rel 2


-- @@ L266-267 verbatim
protected class Zero (L : Language) where
  zero : L.Func 0


-- @@ L269-270 verbatim
protected class One (L : Language) where
  one : L.Func 0


-- @@ L272-273 verbatim
protected class Add (L : Language) where
  add : L.Func 2


-- @@ L275-276 verbatim
protected class Mul (L : Language) where
  mul : L.Func 2


-- @@ L278-279 verbatim
protected class Pow (L : Language) where
  pow : L.Func 2


-- @@ L281-282 verbatim
protected class Exp (L : Language) where
  exp : L.Func 1


-- @@ L284-285 verbatim
class Pairing (L : Language) where
  pair : L.Func 2


-- @@ L287-288 verbatim
class Star (L : Language) where
  star : L.Func 0


-- @@ L290-290 verbatim
attribute [match_pattern] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt Mem.mem Star.star


-- @@ L292-292 verbatim
class ORing (L : Language) extends L.Eq, L.LT, L.Zero, L.One, L.Add, L.Mul


-- @@ L294-300 verbatim
instance : ORing oRing where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul


-- @@ L302-303 expanded
instance : ConstantInhabited oRing where default := Language.Zero.zero


-- @@ L305-306 verbatim
instance : Star unit where
  star := ()


-- @@ L308-309 verbatim
instance (L : Language) (S : Language) [Star S] : Star (L.add S) where
  star := Sum.inr Star.star


-- @@ L311-312 verbatim
instance (L : Language) (S : Language) [L.Zero] : (L.add S).Zero where
  zero := Sum.inl Zero.zero


-- @@ L314-315 verbatim
instance (L : Language) (S : Language) [L.One] : (L.add S).One where
  one := Sum.inl One.one


-- @@ L317-318 verbatim
instance (L : Language) (S : Language) [L.Add] : (L.add S).Add where
  add := Sum.inl Add.add


-- @@ L320-321 verbatim
instance (L : Language) (S : Language) [L.Mul] : (L.add S).Mul where
  mul := Sum.inl Mul.mul


-- @@ L323-324 verbatim
instance (L : Language) (S : Language) [L.Eq] : (L.add S).Eq where
  eq := Sum.inl Eq.eq


-- @@ L326-327 verbatim
instance (L : Language) (S : Language) [L.LT] : (L.add S).LT where
  lt := Sum.inl LT.lt


-- @@ L329-331 verbatim
@[ext] structure Hom (L₁ L₂ : Language) where
  func : {k : ℕ} → L₁.Func k → L₂.Func k
  rel : {k : ℕ} → L₁.Rel k → L₂.Rel k


-- @@ L333-336 verbatim
/--
A structure for the homomorphisms (respecting function and relation symbols) between first-order languages.
-/
scoped[FFL.FirstOrder] infix:25 " →ᵥ " => FFL.FirstOrder.Language.Hom


-- @@ L338-338 verbatim
namespace Hom

-- @@ L339-339 verbatim
variable (L L₁ L₂ L₃ : Language) (Φ : Hom L₁ L₂)


-- @@ L341-343 verbatim
protected def id : L →ᵥ L where
  func := id
  rel := id


-- @@ L345-345 verbatim
variable {L L₁ L₂ L₃}


-- @@ L347-349 verbatim
def comp (Ψ : L₂ →ᵥ L₃) (Φ : L₁ →ᵥ L₂) : L₁ →ᵥ L₃ where
  func := Ψ.func ∘ Φ.func
  rel  := Ψ.rel ∘ Φ.rel


-- @@ L351-351 verbatim
def add₁ (L₁ : Language) (L₂ : Language) : L₁ →ᵥ L₁.add L₂ := ⟨Sum.inl, Sum.inl⟩


-- @@ L353-353 verbatim
def add₂ (L₁ : Language) (L₂ : Language) : L₂ →ᵥ L₁.add L₂ := ⟨Sum.inr, Sum.inr⟩


-- @@ L355-356 verbatim
lemma func_add₁ (L₁ : Language) (L₂ : Language) (f : L₁.Func k) :
    (add₁ L₁ L₂).func f = Sum.inl f := rfl


-- @@ L358-359 verbatim
lemma rel_add₁ (L₁ : Language) (L₂ : Language) (r : L₁.Rel k) :
    (add₁ L₁ L₂).rel r = Sum.inl r := rfl


-- @@ L361-362 verbatim
lemma func_add₂ (L₁ : Language) (L₂ : Language) (f : L₂.Func k) :
    (add₂ L₁ L₂).func f = Sum.inr f := rfl


-- @@ L364-365 verbatim
lemma rel_add₂ (L₁ : Language) (L₂ : Language) (r : L₂.Rel k) :
    (add₂ L₁ L₂).rel r = Sum.inr r := rfl


-- @@ L367-368 verbatim
@[simp] lemma add₂_star (L₁ : Language) (L₂ : Language) [Star L₂] :
    (add₂ L₁ L₂).func Star.star = Star.star := rfl


-- @@ L370-371 verbatim
@[simp] lemma add₁_zero (L₁ : Language) (L₂ : Language) [L₁.Zero] :
    (add₁ L₁ L₂).func Zero.zero = Zero.zero := rfl


-- @@ L373-374 verbatim
@[simp] lemma add₁_one (L₁ : Language) (L₂ : Language) [L₁.One] :
    (add₁ L₁ L₂).func One.one = One.one := rfl


-- @@ L376-377 verbatim
@[simp] lemma add₁_add (L₁ : Language) (L₂ : Language) [L₁.Add] :
    (add₁ L₁ L₂).func Add.add = Add.add := rfl


-- @@ L379-380 verbatim
@[simp] lemma add₁_mul (L₁ : Language) (L₂ : Language) [L₁.Mul] :
    (add₁ L₁ L₂).func Mul.mul = Mul.mul := rfl


-- @@ L382-383 verbatim
@[simp] lemma add₁_eq (L₁ : Language) (L₂ : Language) [L₁.Eq] :
    (add₁ L₁ L₂).rel Eq.eq = Eq.eq := rfl


-- @@ L385-386 verbatim
@[simp] lemma add₁_lt (L₁ : Language) (L₂ : Language) [L₁.LT] :
    (add₁ L₁ L₂).rel LT.lt = LT.lt := rfl


-- @@ L388-388 verbatim
def sigma (L : ι → Language) (i : ι) : L i →ᵥ Language.sigma L := ⟨fun f => ⟨i, f⟩, fun r => ⟨i, r⟩⟩


-- @@ L390-390 verbatim
lemma func_sigma (L : ι → Language) (i : ι) (f : (L i).Func k) : (sigma L i).func f = ⟨i, f⟩ := rfl


-- @@ L392-392 verbatim
lemma rel_sigma (L : ι → Language) (i : ι) (r : (L i).Rel k) : (sigma L i).rel r = ⟨i, r⟩ := rfl


-- @@ L394-394 verbatim
end Hom


-- @@ L396-406 expanded
def ORing.embedding (L : Language) [ORing L] : oRing →ᵥ L
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


-- @@ L407-407 verbatim
end Language


-- @@ L409-411 verbatim
protected class Language.DecidableEq (L : Language) where
  func : (k : ℕ) → DecidableEq (L.Func k)
  rel : (k : ℕ) → DecidableEq (L.Rel k)


-- @@ L413-414 verbatim
instance (L : Language) [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] : L.DecidableEq :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩


-- @@ L416-416 verbatim
instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Func k) := Language.DecidableEq.func k


-- @@ L418-418 verbatim
instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Rel k) := Language.DecidableEq.rel k


-- @@ L420-420 verbatim
instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Rel k) := Language.DecidableEq.rel k


-- @@ L422-424 verbatim
protected class Language.Encodable (L : Language) where
  func : (k : ℕ) → Encodable (L.Func k)
  rel : (k : ℕ) → Encodable (L.Rel k)


-- @@ L426-426 verbatim
instance (L : Language) [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] : L.Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩


-- @@ L428-428 verbatim
instance (L : Language) [L.Encodable] (k : ℕ) : Encodable (L.Func k) := Language.Encodable.func k


-- @@ L430-430 verbatim
instance (L : Language) [L.Encodable] (k : ℕ) : Encodable (L.Rel k) := Language.Encodable.rel k


-- @@ L432-432 verbatim
instance (L : Language) [L.Encodable] (k : ℕ) : Encodable (L.Rel k) := Language.Encodable.rel k


-- @@ L434-436 verbatim
class Language.Finite (L : Language) where
  func : Fintype ((k : ℕ) × L.Func k)
  rel : Fintype ((k : ℕ) × L.Rel k)


-- @@ L438-440 expanded
instance : Language.Finite oRing
    where
  func := Fintype.ofEquiv (Fin 4) Language.ORing.funcEquivFinFour.symm
  rel := Fintype.ofEquiv (Fin 2) Language.ORing.relEquivFinTwo.symm


-- @@ L442-442 verbatim
end FirstOrder


-- @@ L444-444 verbatim
end FFL

-- @@ L445-445 verbatim
end
