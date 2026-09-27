/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.Predicate.Language
public import LeanPool.Incompleteness.Foundation.Vorspiel.Collection
public import LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel
import Mathlib.Tactic.Bound.Init


-- @@ L13-23 verbatim
/-!
# Terms of first-order logic

This file defines the terms of first-order logic.

The bounded variables are denoted by `#x` for `x : Fin n`, and free variables are denoted by `&x`
for `x : ξ`.
`t : Semiterm L ξ n` is a (semi-)term of language `L` with bounded variables of `Fin n` and free
variables of `ξ`.

-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace LO


-- @@ L29-29 verbatim
namespace FirstOrder


-- @@ L31-35 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive Semiterm (L : Language) (ξ : Type*) (n : ℕ)
  | bvar : Fin n → Semiterm L ξ n
  | fvar : ξ → Semiterm L ξ n
  | func : ∀ {arity}, L.Func arity → (Fin arity → Semiterm L ξ n) → Semiterm L ξ n


-- @@ L37-38 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:max "&" => Semiterm.fvar

-- @@ L39-40 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:max "#" => Semiterm.bvar


-- @@ L42-43 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Term (L : Language) (ξ : Type*) := Semiterm L ξ 0


-- @@ L45-46 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticSemiterm (L : Language) (n : ℕ) := Semiterm L ℕ n


-- @@ L48-49 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticTerm (L : Language) := SyntacticSemiterm L 0


-- @@ L51-51 verbatim
namespace Semiterm


-- @@ L53-53 verbatim
variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}


-- @@ L55-55 verbatim
instance [Inhabited ξ] : Inhabited (Semiterm L ξ n) := ⟨&default⟩


-- @@ L57-57 verbatim
section «lp_section_1»


-- @@ L59-59 verbatim
variable [∀ k, ToString (L.Func k)] [ToString ξ]


-- @@ L61-67 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def toStr : Semiterm L ξ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "z_{" ++ toString x ++ "}"
  | func (arity := 0) c _     => toString c
  | func (arity := _ + 1) f v =>
    "{" ++ toString f ++ "} \\left(" ++ String.vecToStr (fun i => toStr (v i)) ++ "\\right)"


-- @@ L69-69 verbatim
instance : Repr (Semiterm L ξ n) := ⟨fun t _ => toStr t⟩


-- @@ L71-71 verbatim
instance : ToString (Semiterm L ξ n) := ⟨toStr⟩


-- @@ L73-73 verbatim
end «lp_section_1»


-- @@ L75-75 verbatim
section «lp_section_2»


-- @@ L77-77 verbatim
variable [∀ k, DecidableEq (L.Func k)] [DecidableEq ξ]


-- @@ L79-98 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : (t u : Semiterm L ξ n) → Decidable (Eq t u)
  | #x,                   #y                   => by simp only [bvar.injEq]; exact decEq x y
  | #_,                   &_                   => isFalse (by intro h; cases h)
  | #_,                   func _ _             => isFalse (by intro h; cases h)
  | &_,                   #_                   => isFalse (by intro h; cases h)
  | &x,                   &y                   => by simp only [fvar.injEq]; exact decEq x y
  | &_,                   func _ _             => isFalse (by intro h; cases h)
  | func _ _,             #_                   => isFalse (by intro h; cases h)
  | func _ _,             &_                   => isFalse (by intro h; cases h)
  | @func L ξ _ k₁ r₁ v₁, @func L ξ _ k₂ r₂ v₂ => by
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact match decEq r₁ r₂ with
        | isTrue h => by
          subst r₂
          simp only [func.injEq, heq_eq_eq, true_and]
          exact Matrix.decVec _ _ (fun i => hasDecEq (v₁ i) (v₂ i))
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])


-- @@ L100-100 verbatim
instance : DecidableEq (Semiterm L ξ n) := hasDecEq


-- @@ L102-102 verbatim
end «lp_section_2»


-- @@ L104-108 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def complexity : Semiterm L ξ n → ℕ
  | #_       => 0
  | &_       => 0
  | func _ v => Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1


-- @@ L110-110 verbatim
@[simp] lemma complexity_bvar (x : Fin n) : (#x : Semiterm L ξ n).complexity = 0 := rfl


-- @@ L112-112 verbatim
@[simp] lemma complexity_fvar (x : ξ) : (&x : Semiterm L ξ n).complexity = 0 := rfl


-- @@ L114-116 verbatim
lemma complexity_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).complexity = Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1 :=
  rfl


-- @@ L118-121 verbatim
@[simp] lemma complexity_func_lt {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).complexity < (func f v).complexity := by
  rw [complexity_func]
  exact Nat.lt_succ_of_le <| Finset.le_sup (f := fun i ↦ complexity (v i)) (by simp)


-- @@ L123-124 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev «func!» (k) (f : L.Func k) (v : Fin k → Semiterm L ξ n) := func f v


-- @@ L126-130 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def bv : Semiterm L ξ n → Finset (Fin n)
  | #x       => {x}
  | &_       => ∅
  | func _ v => .biUnion .univ fun i ↦ bv (v i)


-- @@ L132-132 verbatim
@[simp] lemma bv_bvar : (#x : Semiterm L ξ n).bv = {x} := rfl


-- @@ L134-134 verbatim
@[simp] lemma bv_fvar : (&x : Semiterm L ξ n).bv = ∅ := rfl


-- @@ L136-138 verbatim
lemma bv_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).bv = .biUnion .univ fun i ↦ bv (v i) :=
  rfl


-- @@ L140-140 verbatim
@[simp] lemma bv_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) : (func f v).bv = ∅ := rfl


-- @@ L142-143 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Positive (t : Semiterm L ξ (n + 1)) : Prop := ∀ x ∈ t.bv, 0 < x


-- @@ L145-145 verbatim
namespace Positive


-- @@ L147-147 verbatim
@[simp] protected lemma bvar : Positive (#x : Semiterm L ξ (n + 1)) ↔ 0 < x := by simp[Positive]


-- @@ L149-149 verbatim
@[simp] protected lemma fvar : Positive (&x : Semiterm L ξ (n + 1)) := by simp[Positive]


-- @@ L151-161 verbatim
@[simp] protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ (n + 1)) :
    Positive (func f v) ↔ ∀ i, Positive (v i) := by
  constructor
  · intro h i x hx
    exact h x (by
      rw [bv_func]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  · intro h x hx
    rw [bv_func] at hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, _, hi⟩
    exact h i x hi


-- @@ L163-163 verbatim
end Positive


-- @@ L165-169 verbatim
lemma bv_eq_empty_of_positive {t : Semiterm L ξ 1} (ht : t.Positive) : t.bv = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr <| by
    intro x hx
    rw [Fin.eq_zero x] at hx
    exact (Nat.lt_irrefl 0) (ht 0 hx)


-- @@ L171-171 verbatim
section «lp_section_3»


-- @@ L173-173 verbatim
variable [DecidableEq ξ]


-- @@ L175-179 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def freeVariables : Semiterm L ξ n → Finset ξ
  | #_       => ∅
  | &x       => {x}
  | func _ v => .biUnion .univ fun i ↦ freeVariables (v i)


-- @@ L181-181 verbatim
@[simp] lemma freeVariables_bvar : (#x : Semiterm L ξ n).freeVariables = ∅ := rfl


-- @@ L183-183 verbatim
@[simp] lemma freeVariables_fvar : (&x : Semiterm L ξ n).freeVariables = {x} := rfl


-- @@ L185-186 verbatim
lemma freeVariables_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl


-- @@ L188-190 verbatim
@[simp] lemma freeVariables_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) :
    (func f v).freeVariables = ∅ :=
  rfl


-- @@ L192-193 verbatim
@[simp] lemma freeVariables_empty {ο : Type*} [IsEmpty ο] {t : Semiterm L ο n} :
    t.freeVariables = ∅ := by ext x; exact IsEmpty.elim inferInstance x


-- @@ L195-196 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev «FVar?» (t : Semiterm L ξ n) (x : ξ) : Prop := x ∈ t.freeVariables


-- @@ L198-198 verbatim
@[simp] lemma «fvar?_bvar» (x z) : ¬(#x : Semiterm L ξ n).FVar? z := by simp [FVar?]


-- @@ L200-200 verbatim
@[simp] lemma «fvar?_fvar» (x z) : (&x : Semiterm L ξ n).FVar? z ↔ x = z := by simp [FVar?, Eq.comm]


-- @@ L202-203 verbatim
@[simp] lemma «fvar?_func» (x) {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_func]


-- @@ L205-205 verbatim
end «lp_section_3»


-- @@ L207-207 verbatim
section «lp_section_4»


-- @@ L209-209 verbatim
variable (Φ : L₁ →ᵥ L₂)


-- @@ L211-215 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def lMap (Φ : L₁ →ᵥ L₂) : Semiterm L₁ ξ n → Semiterm L₂ ξ n
  | #x       => #x
  | &x       => &x
  | func f v => func (Φ.func f) (fun i => lMap Φ (v i))


-- @@ L217-217 verbatim
@[simp] lemma lMap_bvar (x : Fin n) : (#x : Semiterm L₁ ξ n).lMap Φ = #x := rfl


-- @@ L219-219 verbatim
@[simp] lemma lMap_fvar (x : ξ) : (&x : Semiterm L₁ ξ n).lMap Φ = &x := rfl


-- @@ L221-222 verbatim
lemma lMap_func {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) (fun i ↦ lMap Φ (v i)) := rfl


-- @@ L224-225 verbatim
@[simp] lemma lMap_positive (t : Semiterm L₁ ξ (n + 1)) : (t.lMap Φ).Positive ↔ t.Positive := by
  induction t <;> simp [lMap_func, *]


-- @@ L227-233 verbatim
@[simp] lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (t : Semiterm L₁ ξ n) :
    (Semiterm.lMap Φ t).freeVariables = t.freeVariables := by
  induction t
  case bvar => simp
  case fvar => simp
  case func k f v ih =>
    ext x; simp [lMap_func, freeVariables_func, ih]


-- @@ L235-235 verbatim
end «lp_section_4»


-- @@ L237-237 verbatim
section «lp_section_5»


-- @@ L239-239 verbatim
variable [L.ConstantInhabited]


-- @@ L241-241 verbatim
instance : Inhabited (Semiterm L ξ n) := ⟨func default ![]⟩


-- @@ L243-243 verbatim
lemma default_def : (default : Semiterm L ξ n) = func default ![] := rfl


-- @@ L245-245 verbatim
end «lp_section_5»


-- @@ L247-247 verbatim
end Semiterm


-- @@ L249-249 verbatim
end FirstOrder


-- @@ L251-251 verbatim
end LO
