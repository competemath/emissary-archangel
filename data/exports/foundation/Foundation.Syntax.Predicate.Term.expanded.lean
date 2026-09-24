module

public import Foundation.Syntax.Predicate.Language
public import Foundation.Vorspiel.String


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-16 verbatim
/-!
# Terms of first-order logic

This file defines the terms of first-order logic.

The bounded variables are denoted by `#x` for `x : Fin n`, and free variables are denoted by `&x` for `x : ξ`.
`t : Semiterm L ξ n` is a (semi-)term of language `L` with bounded variables of `Fin n` and free variables of `ξ`.

-/


-- @@ L18-18 verbatim
namespace FFL


-- @@ L20-20 verbatim
namespace FirstOrder


-- @@ L22-28 verbatim
/--
A semiterm of language `L`, with bound variables indexed by `Fin n` and free variables indexed by `ξ`. In `FFL.FirstOrder.Semiformula`, bound variables are de Bruijn indices with a separate type from free variables.
-/
inductive Semiterm (L : Language) (ξ : Type*) (n : ℕ)
  | bvar : Fin n → Semiterm L ξ n
  | fvar : ξ → Semiterm L ξ n
  | func : ∀ {arity}, L.Func arity → (Fin arity → Semiterm L ξ n) → Semiterm L ξ n


-- @@ L30-31 verbatim
/-- `&x` is the free variable indexed by the element `x : ξ`. -/
scoped prefix:max "&" => Semiterm.fvar


-- @@ L33-34 verbatim
/-- `#x` is the bound variable with de Bruijn index `x`. -/
scoped prefix:max "#" => Semiterm.bvar


-- @@ L36-36 verbatim
abbrev Term (L : Language) (ξ : Type*) := Semiterm L ξ 0


-- @@ L38-38 verbatim
abbrev ClosedSemiterm (L : Language) (n : ℕ) := Semiterm L Empty n


-- @@ L40-40 verbatim
abbrev ClosedTerm (L : Language) := Semiterm L Empty 0


-- @@ L42-42 verbatim
abbrev SyntacticSemiterm (L : Language) (n : ℕ) := Semiterm L ℕ n


-- @@ L44-44 verbatim
abbrev SyntacticTerm (L : Language) := SyntacticSemiterm L 0


-- @@ L46-46 verbatim
namespace Semiterm


-- @@ L48-48 verbatim
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}


-- @@ L50-50 verbatim
instance [Inhabited ξ] : Inhabited (Semiterm L ξ n) := ⟨&default⟩


-- @@ L52-52 verbatim
section ToString


-- @@ L54-54 verbatim
variable [∀ k, ToString (L.Func k)] [ToString ξ]


-- @@ L56-60 verbatim
def toStr : Semiterm L ξ n → String
  |                        #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  |                        &x => "z_{" ++ toString x ++ "}"
  |     func (arity := 0) c _ => toString c
  | func (arity := _ + 1) f v => "{" ++ toString f ++ "} \\left(" ++ String.vecToStr (fun i => toStr (v i)) ++ "\\right)"


-- @@ L62-62 verbatim
instance : Repr (Semiterm L ξ n) := ⟨fun t _ => toStr t⟩


-- @@ L64-64 verbatim
instance : ToString (Semiterm L ξ n) := ⟨toStr⟩


-- @@ L66-66 verbatim
end ToString


-- @@ L68-68 verbatim
section Decidable


-- @@ L70-70 verbatim
variable [∀ k, DecidableEq (L.Func k)] [DecidableEq ξ]


-- @@ L72-87 verbatim
def hasDecEq : (t u : Semiterm L ξ n) → Decidable (Eq t u)
  |                   #x,                   #y => by simpa using decEq x y
  |                   #_,                   &_ => isFalse (by simp)
  |                   #_,             func _ _ => isFalse (by simp)
  |                   &_,                   #_ => isFalse (by simp)
  |                   &x,                   &y => by simpa using decEq x y
  |                   &_,             func _ _ => isFalse (by simp)
  |             func _ _,                   #_ => isFalse (by simp)
  |             func _ _,                   &_ => isFalse (by simp)
  | @func L ξ _ k₁ r₁ v₁, @func L ξ _ k₂ r₂ v₂ => by
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact match decEq r₁ r₂ with
        |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ hasDecEq (v₁ i) (v₂ i)
        | isFalse h => isFalse (by simp [h])
      · exact isFalse (by simp [e])


-- @@ L89-89 verbatim
instance : DecidableEq (Semiterm L ξ n) := hasDecEq


-- @@ L91-91 verbatim
end Decidable


-- @@ L93-99 verbatim
/--
The complexity of a semiterm, taking suprema at function symbols.
-/
def complexity : Semiterm L ξ n → ℕ
  |       #_ => 0
  |       &_ => 0
  | func _ v => Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1


-- @@ L101-101 verbatim
@[simp] lemma complexity_bvar (x : Fin n) : (#x : Semiterm L ξ n).complexity = 0 := rfl


-- @@ L103-105 verbatim
@[simp] lemma complexity_fvar (x : ξ) : (&x : Semiterm L ξ n).complexity = 0 := rfl

lemma complexity_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) : (func f v).complexity = Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1 := rfl


-- @@ L107-109 verbatim
@[simp] lemma complexity_func_lt {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).complexity < (func f v).complexity := by
  simpa [complexity_func, Nat.lt_add_one_iff] using Finset.le_sup (f := fun i ↦ complexity (v i)) (by simp)


-- @@ L111-111 verbatim
abbrev func! (k) (f : L.Func k) (v : Fin k → Semiterm L ξ n) := func f v


-- @@ L113-119 verbatim
/--
The set of bound variables occurring in a semiterm.
-/
def bv : Semiterm L ξ n → Finset (Fin n)
  |       #x => {x}
  |       &_ => ∅
  | func _ v => .biUnion .univ fun i ↦ bv (v i)


-- @@ L121-121 verbatim
@[simp] lemma bv_bvar : (#x : Semiterm L ξ n).bv = {x} := rfl


-- @@ L123-125 verbatim
@[simp] lemma bv_fvar : (&x : Semiterm L ξ n).bv = ∅ := rfl

lemma bv_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) : (func f v).bv = .biUnion .univ fun i ↦ bv (v i) := rfl


-- @@ L127-127 verbatim
@[simp] lemma bv_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) : (func f v).bv = ∅ := rfl


-- @@ L129-129 verbatim
def Positive (t : Semiterm L ξ (n + 1)) : Prop := ∀ x ∈ t.bv, 0 < x


-- @@ L131-131 verbatim
namespace Positive


-- @@ L133-133 verbatim
@[simp] protected lemma bvar : Positive (#x : Semiterm L ξ (n + 1)) ↔ 0 < x := by simp [Positive]


-- @@ L135-135 verbatim
@[simp] protected lemma fvar : Positive (&x : Semiterm L ξ (n + 1)) := by simp [Positive]


-- @@ L137-139 verbatim
@[simp] protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ (n + 1)) :
    Positive (func f v) ↔ ∀ i, Positive (v i) := by
  simpa [Positive, bv] using forall_comm


-- @@ L141-144 verbatim
end Positive

lemma bv_eq_empty_of_positive {t : Semiterm L ξ 1} (ht : t.Positive) : t.bv = ∅ :=
  Finset.eq_empty_of_forall_notMem <| by simp_all [Positive]


-- @@ L146-146 verbatim
section freeVariables


-- @@ L148-148 verbatim
variable [DecidableEq ξ]


-- @@ L150-156 verbatim
/--
The set of free variables occuring in a semiterm.
-/
def freeVariables : Semiterm L ξ n → Finset ξ
  |       #_ => ∅
  |       &x => {x}
  | func _ v => .biUnion .univ fun i ↦ freeVariables (v i)


-- @@ L158-158 verbatim
@[simp] lemma freeVariables_bvar : (#x : Semiterm L ξ n).freeVariables = ∅ := rfl


-- @@ L160-163 verbatim
@[simp] lemma freeVariables_fvar : (&x : Semiterm L ξ n).freeVariables = {x} := rfl

lemma freeVariables_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl


-- @@ L165-165 verbatim
@[simp] lemma freeVariables_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) : (func f v).freeVariables = ∅ := rfl


-- @@ L167-168 verbatim
@[simp] lemma freeVariables_empty {ο : Type*} [IsEmpty ο] {t : Semiterm L ο n} : t.freeVariables = ∅ := by
  ext x; exact IsEmpty.elim inferInstance x


-- @@ L170-170 verbatim
abbrev FVar? (t : Semiterm L ξ n) (x : ξ) : Prop := x ∈ t.freeVariables


-- @@ L172-172 verbatim
@[simp] lemma fvar?_bvar (x z) : ¬(#x : Semiterm L ξ n).FVar? z := by simp [FVar?]


-- @@ L174-174 verbatim
@[simp] lemma fvar?_fvar (x z) : (&x : Semiterm L ξ n).FVar? z ↔ x = z := by simp [FVar?, Eq.comm]


-- @@ L176-177 verbatim
@[simp] lemma fvar?_func (x) {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_func]


-- @@ L179-179 verbatim
end freeVariables


-- @@ L181-181 verbatim
section lMap


-- @@ L183-183 verbatim
variable (Φ : L₁ →ᵥ L₂)


-- @@ L185-191 verbatim
/--
The map on terms induced from a homomorphism between languages.
-/
def lMap (Φ : L₁ →ᵥ L₂) : Semiterm L₁ ξ n → Semiterm L₂ ξ n
  |       #x => #x
  |       &x => &x
  | func f v => func (Φ.func f) fun i ↦ lMap Φ (v i)


-- @@ L193-193 verbatim
@[simp] lemma lMap_bvar (x : Fin n) : (#x : Semiterm L₁ ξ n).lMap Φ = #x := rfl


-- @@ L195-195 verbatim
@[simp] lemma lMap_fvar (x : ξ) : (&x : Semiterm L₁ ξ n).lMap Φ = &x := rfl


-- @@ L197-201 verbatim
@[simp] lemma lMap_func {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) (lMap Φ ∘ v) := rfl

lemma lMap_func' {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) fun i ↦ lMap Φ (v i) := rfl


-- @@ L203-204 verbatim
@[simp] lemma lMap_positive (t : Semiterm L₁ ξ (n + 1)) : (t.lMap Φ).Positive ↔ t.Positive := by
  induction t <;> simp [lMap_func, *]


-- @@ L206-212 verbatim
@[simp] lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (t : Semiterm L₁ ξ n) :
    (Semiterm.lMap Φ t).freeVariables = t.freeVariables := by
  induction t
  case bvar => simp
  case fvar => simp
  case func k f v ih =>
    ext x; simp [lMap_func, freeVariables_func, ih]


-- @@ L214-214 verbatim
end lMap


-- @@ L216-216 verbatim
section


-- @@ L218-218 verbatim
variable [L.ConstantInhabited]


-- @@ L220-222 verbatim
instance : Inhabited (Semiterm L ξ n) := ⟨func default ![]⟩

lemma default_def : (default : Semiterm L ξ n) = func default ![] := rfl


-- @@ L224-224 verbatim
end


-- @@ L226-226 verbatim
section idxOfFVar


-- @@ L228-231 verbatim
def fvarList : Semiterm L ξ n → List ξ
  |       #_ => []
  |       &x => [x]
  | func _ v => List.flatten <| Matrix.toList fun i ↦ fvarList (v i)


-- @@ L233-233 verbatim
def idxOfFVar [DecidableEq ξ] (t : Semiterm L ξ n) : ξ → ℕ := t.fvarList.idxOf


-- @@ L235-244 verbatim
def enumerateFVar [Inhabited ξ] (t : Semiterm L ξ n) : ℕ → ξ :=
  fun i ↦ if hi : i < t.fvarList.length then t.fvarList.get ⟨i, hi⟩ else default

lemma enumerateFVar_idxOfFVar [DecidableEq ξ] [Inhabited ξ] {t : Semiterm L ξ n} {x : ξ} (hx : x ∈ t.fvarList) :
    enumerateFVar t (idxOfFVar t x) = x := by
  simpa [enumerateFVar, idxOfFVar]
  using fun h ↦ False.elim <| not_le.mpr (List.idxOf_lt_length_iff.mpr $ hx) h

lemma mem_fvarList_iff_fvar? [DecidableEq ξ] {t : Semiterm L ξ n} : x ∈ t.fvarList ↔ t.FVar? x:= by
  induction t <;> { simp [fvarList, *]; try tauto }


-- @@ L246-246 verbatim
end idxOfFVar


-- @@ L248-248 verbatim
end Semiterm


-- @@ L250-250 verbatim
end FirstOrder


-- @@ L252-252 verbatim
end FFL

-- @@ L253-253 verbatim
end
