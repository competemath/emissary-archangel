module

public import Foundation.Syntax.Predicate.Term
public import Foundation.Syntax.Predicate.Quantifier
public import Mathlib.Data.Nat.Cast.Order.Basic


-- @@ L7-7 verbatim
@[expose] public section


-- @@ L9-17 verbatim
/-!
# Formulas of first-order logic

This file defines the formulas of first-order logic.

`φ : Semiformula L ξ n` is a (semi-)formula of language `L` with bounded variables of `Fin n` and free variables of `ξ`.
The quantification is represented by de Bruijn index.

-/


-- @@ L19-19 verbatim
namespace FFL.FirstOrder


-- @@ L21-32 verbatim
/--
A semiformula of language `L`. Free variables are of type `ξ`, and bound variables are implemented as de Bruijn indices, of a type `Fin n` separate from free variables.
-/
inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  |  verum : Semiformula L ξ n
  | falsum : Semiformula L ξ n
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |    and : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |     or : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    all : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |    exs : Semiformula L ξ (n + 1) → Semiformula L ξ n


-- @@ L34-34 verbatim
abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0


-- @@ L36-36 verbatim
abbrev Sentence (L : Language) := Formula L Empty


-- @@ L38-38 verbatim
abbrev Semisentence (L : Language) (n : ℕ) := Semiformula L Empty n


-- @@ L40-40 verbatim
abbrev Semiproposition (L : Language) (n : ℕ) := Semiformula L ℕ n


-- @@ L42-42 verbatim
abbrev Proposition (L : Language) := Semiproposition L 0


-- @@ L44-44 verbatim
namespace Semiformula


-- @@ L46-49 verbatim
variable
  {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language}
  {ξ ξ₁ ξ₂ ξ₃ : Type*}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}


-- @@ L51-62 verbatim
def neg {n} : Semiformula L ξ n → Semiformula L ξ n
  |    verum => falsum
  |   falsum => verum
  |  rel r v => nrel r v
  | nrel r v => rel r v
  |  and φ ψ => or (neg φ) (neg ψ)
  |   or φ ψ => and (neg φ) (neg ψ)
  |    all φ => exs (neg φ)
  |    exs φ => all (neg φ)

lemma neg_neg (φ : Semiformula L ξ n) : neg (neg φ) = φ :=
  by induction φ <;> simp [*, neg]


-- @@ L64-68 verbatim
instance : LogicalConnective (Semiformula L ξ n) where
  arrow := fun φ ψ => or (neg φ) ψ
  wedge := and
  vee := or
  tilde := neg


-- @@ L70-72 verbatim
instance : LogicalNeutral (Semiformula L ξ n) where
  top := verum
  bot := falsum


-- @@ L74-75 verbatim
instance : TildeInvolutive (Semiformula L ξ n) where
  tilde_involutive := neg_neg


-- @@ L77-80 verbatim
instance : LogicalConnective.DeMorgan (Semiformula L ξ n) where
  imply := fun _ _ => rfl
  and := fun _ _ => rfl
  or := fun _ _ => rfl


-- @@ L82-84 verbatim
instance : LogicalNeutral.DeMorgan (Semiformula L ξ n) where
  verum := rfl
  falsum := rfl


-- @@ L86-88 verbatim
instance : Quantifier (Semiformula L ξ) where
  all := all
  exs := exs


-- @@ L90-90 verbatim
section ToString


-- @@ L92-92 verbatim
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]


-- @@ L94-104 verbatim
def toStr {n} : Semiformula L ξ n → String
  |                         ⊤ => "\\top"
  |                         ⊥ => "\\bot"
  |      rel (arity := 0) r _ => "{" ++ toString r ++ "}"
  |  rel (arity := _ + 1) r v => "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  |     nrel (arity := 0) r _ => "\\lnot {" ++ toString r ++ "}"
  | nrel (arity := _ + 1) r v => "\\lnot {" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  |                     φ ⋏ ψ => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  |                     φ ⋎ ψ => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  |                      ∀¹ φ => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr φ
  |                      ∃¹ φ => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr φ


-- @@ L106-106 verbatim
instance : Repr (Semiformula L ξ n) := ⟨fun t _ ↦ toStr t⟩


-- @@ L108-108 verbatim
instance : ToString (Semiformula L ξ n) := ⟨toStr⟩


-- @@ L110-110 verbatim
end ToString


-- @@ L112-112 verbatim
@[simp] lemma neg_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ∼(rel r v) = nrel r v := rfl


-- @@ L114-114 verbatim
@[simp] lemma neg_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ∼(nrel r v) = rel r v := rfl


-- @@ L116-116 verbatim
@[simp] lemma neg_all (φ : Semiformula L ξ (n + 1)) : ∼(∀¹ φ) = ∃¹ ∼φ := rfl


-- @@ L118-118 verbatim
@[simp] lemma neg_ex (φ : Semiformula L ξ (n + 1)) : ∼(∃¹ φ) = ∀¹ ∼φ := rfl


-- @@ L120-122 verbatim
/-- `φ.toPrenex Γ s` prefixes `φ` with `s` alternating quantifiers, the outermost one being `Γ`. -/
abbrev toPrenex (Γ : Polarity) (s : ℕ) (φ : Semiformula L ξ (n + s)) : Semiformula L ξ n :=
  Polarity.quantItr Γ s φ


-- @@ L124-126 verbatim
@[simp] lemma neg_quant (Γ : Polarity) (φ : Semiformula L ξ (n + 1)) :
    ∼(Γ.quant φ) = Γ.alt.quant (∼φ) := by
  rcases Γ <;> rfl


-- @@ L128-135 verbatim
@[simp] lemma neg_toPrenex (Γ : Polarity) (s : ℕ) (φ : Semiformula L ξ (n + s)) :
    ∼(φ.toPrenex Γ s) = (∼φ).toPrenex Γ.alt s := by
  induction s generalizing n with
  | zero => rfl
  | succ s ih =>
    show ∼(Polarity.quantItr Γ (s + 1) φ) = Polarity.quantItr Γ.alt (s + 1) (∼φ)
    rw [Polarity.quantItr_succ', ih, neg_quant, Polarity.quantItr_succ']
    rw [← Polarity.altItr_succ, Polarity.altItr_succ']


-- @@ L137-140 verbatim
@[simp] lemma neg_inj (φ ψ : Semiformula L ξ n) : ∼φ = ∼ψ ↔ φ = ψ := by
  constructor
  · intro h; simpa using congr_arg (∼·) h
  · exact congr_arg _


-- @@ L142-143 verbatim
@[simp] lemma neg_allClosure (φ : Semiformula L ξ n) : ∼(∀¹* φ) = ∃¹* ∼φ := by
  induction n <;> simp [allClosure, exsClosure, *]


-- @@ L145-156 verbatim
@[simp] lemma neg_exsClosure (φ : Semiformula L ξ n) : ∼(∃¹* φ) = ∀¹* ∼φ := by
  induction n <;> simp [allClosure, exsClosure, *]

lemma neg_eq (φ : Semiformula L ξ n) : ∼φ = neg φ := rfl

lemma imp_eq (φ ψ : Semiformula L ξ n) : φ 🡒 ψ = ∼φ ⋎ ψ := rfl

lemma iff_eq (φ ψ : Semiformula L ξ n) : φ 🡘 ψ = (∼φ ⋎ ψ) ⋏ (∼ψ ⋎ φ) := rfl

lemma ball_eq (φ ψ : Semiformula L ξ (n + 1)) : (∀¹[φ] ψ) = ∀¹ (φ 🡒 ψ) := rfl

lemma bexs_eq (φ ψ : Semiformula L ξ (n + 1)) : (∃¹[φ] ψ) = ∃¹ (φ ⋏ ψ) := rfl


-- @@ L158-159 verbatim
@[simp] lemma neg_ball (φ ψ : Semiformula L ξ (n + 1)) : ∼(∀¹[φ] ψ) = ∃¹[φ] ∼ψ := by
  simp [ball, bexs, imp_eq]


-- @@ L161-162 verbatim
@[simp] lemma neg_bexs (φ ψ : Semiformula L ξ (n + 1)) : ∼(∃¹[φ] ψ) = ∀¹[φ] ∼ψ := by
  simp [ball, bexs, imp_eq]


-- @@ L164-164 verbatim
@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := Iff.of_eq <| and.injEq _ _ _ _


-- @@ L166-166 verbatim
@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := Iff.of_eq <| or.injEq _ _ _ _


-- @@ L168-168 verbatim
@[simp] lemma all_inj (φ ψ : Semiformula L ξ (n + 1)) : ∀¹ φ = ∀¹ ψ ↔ φ = ψ := Iff.of_eq <| all.injEq _ _


-- @@ L170-170 verbatim
@[simp] lemma exs_inj (φ ψ : Semiformula L ξ (n + 1)) : ∃¹ φ = ∃¹ ψ ↔ φ = ψ := Iff.of_eq <| exs.injEq _ _


-- @@ L172-173 verbatim
@[simp] lemma allClosure_inj (φ ψ : Semiformula L ξ n) : ∀¹* φ = ∀¹* ψ ↔ φ = ψ := by
  induction n <;> simp [*, allClosure_succ]


-- @@ L175-176 verbatim
@[simp] lemma exsClosure_inj (φ ψ : Semiformula L ξ n) : ∃¹* φ = ∃¹* ψ ↔ φ = ψ := by
  induction n <;> simp [*, exsClosure_succ]


-- @@ L178-179 verbatim
@[simp] lemma allItr_inj {k} (φ ψ : Semiformula L ξ (n + k)) : ∀¹^[k] φ = ∀¹^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, allItr_succ]


-- @@ L181-182 verbatim
@[simp] lemma exsItr_inj {k} (φ ψ : Semiformula L ξ (n + k)) : ∃¹^[k] φ = ∃¹^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, exsItr_succ]


-- @@ L184-185 verbatim
@[simp] lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L ξ n} :
    φ₁ 🡒 φ₂ = ψ₁ 🡒 ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [imp_eq]


-- @@ L187-187 verbatim
abbrev rel! (L : Language) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := rel r v


-- @@ L189-189 verbatim
abbrev nrel! (L : Language) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := nrel r v


-- @@ L191-202 verbatim
/--
The complexity of a semiformula, taking max at logical connectives.
-/
def complexity {n : ℕ} : Semiformula L ξ n → ℕ
|        ⊤ => 0
|        ⊥ => 0
|  rel _ _ => 0
| nrel _ _ => 0
|    φ ⋏ ψ => max φ.complexity ψ.complexity + 1
|    φ ⋎ ψ => max φ.complexity ψ.complexity + 1
|     ∀¹ φ => φ.complexity + 1
|     ∃¹ φ => φ.complexity + 1


-- @@ L204-204 verbatim
@[simp] lemma complexity_top : complexity (⊤ : Semiformula L ξ n) = 0 := rfl


-- @@ L206-206 verbatim
@[simp] lemma complexity_bot : complexity (⊥ : Semiformula L ξ n) = 0 := rfl


-- @@ L208-208 verbatim
@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (rel r v) = 0 := rfl


-- @@ L210-210 verbatim
@[simp] lemma complexity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (nrel r v) = 0 := rfl


-- @@ L212-212 verbatim
@[simp] lemma complexity_and (φ ψ : Semiformula L ξ n) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L213-213 verbatim
@[simp] lemma complexity_and' (φ ψ : Semiformula L ξ n) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L215-215 verbatim
@[simp] lemma complexity_or (φ ψ : Semiformula L ξ n) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L216-216 verbatim
@[simp] lemma complexity_or' (φ ψ : Semiformula L ξ n) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L218-218 verbatim
@[simp] lemma complexity_all (φ : Semiformula L ξ (n + 1)) : complexity (∀¹ φ) = φ.complexity + 1 := rfl

-- @@ L219-219 verbatim
@[simp] lemma complexity_all' (φ : Semiformula L ξ (n + 1)) : complexity (all φ) = φ.complexity + 1 := rfl


-- @@ L221-221 verbatim
@[simp] lemma complexity_exs (φ : Semiformula L ξ (n + 1)) : complexity (∃¹ φ) = φ.complexity + 1 := rfl

-- @@ L222-222 verbatim
@[simp] lemma complexity_exs' (φ : Semiformula L ξ (n + 1)) : complexity (exs φ) = φ.complexity + 1 := rfl


-- @@ L224-242 verbatim
@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L ξ n → Sort w}
    (hverum  : ∀ {n : ℕ}, C n ⊤)
    (hfalsum : ∀ {n : ℕ}, C n ⊥)
    (hrel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hnrel   : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hand    : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⋏ ψ))
    (hor     : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⋎ ψ))
    (hall    : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∀¹ φ))
    (hexs     : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∃¹ φ)) {n : ℕ} :
    (φ : Semiformula L ξ n) → C n φ
  |    verum => hverum
  |   falsum => hfalsum
  |  rel r v => hrel r v
  | nrel r v => hnrel r v
  |  and φ ψ => hand φ ψ
  |   or φ ψ => hor φ ψ
  |     ∀¹ φ => hall φ
  |     ∃¹ φ => hexs φ


-- @@ L244-262 verbatim
@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L ξ n → Sort w}
    (hverum  : ∀ {n : ℕ}, C n ⊤)
    (hfalsum : ∀ {n : ℕ}, C n ⊥)
    (hrel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hnrel   : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hand    : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⋏ ψ))
    (hor     : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⋎ ψ))
    (hall    : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∀¹ φ))
    (hexs     : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∃¹ φ)) {n : ℕ} :
    (φ : Semiformula L ξ n) → C n φ
  |    verum => hverum
  |   falsum => hfalsum
  |  rel r v => hrel r v
  | nrel r v => hnrel r v
  |  and φ ψ => hand φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hexs φ) (rec' hverum hfalsum hrel hnrel hand hor hall hexs ψ)
  |   or φ ψ => hor φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hexs φ) (rec' hverum hfalsum hrel hnrel hand hor hall hexs ψ)
  |     ∀¹ φ => hall φ (rec' hverum hfalsum hrel hnrel hand hor hall hexs φ)
  |     ∃¹ φ => hexs φ (rec' hverum hfalsum hrel hnrel hand hor hall hexs φ)


-- @@ L264-265 verbatim
@[simp] lemma complexity_neg (φ : Semiformula L ξ n) : complexity (∼φ) = complexity φ :=
  by induction φ using rec' <;> simp [*]


-- @@ L267-267 verbatim
section Decidable


-- @@ L269-269 verbatim
variable [L.DecidableEq] [DecidableEq ξ]


-- @@ L271-317 verbatim
def hasDecEq {n : ℕ} : (φ ψ : Semiformula L ξ n) → Decidable (φ = ψ)
  |        ⊤, ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; infer_instance }
  |        ⊥, ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; infer_instance }
  |  rel r v, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ decEq (v i) (v₂ i)
          | isFalse h => isFalse (by simp [h])
        · exact isFalse (by simp [e])
  | nrel r v, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ decEq (v i) (v₂ i)
          | isFalse h => isFalse (by simp [h])
        · exact isFalse (by simp [e])
  |    φ ⋏ ψ, r => by
      cases r using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hand φ' ψ' =>
        exact match hasDecEq φ φ' with
        |  isTrue hp =>
          match hasDecEq ψ ψ' with
          |  isTrue hq => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  |    φ ⋎ ψ, r => by
      cases r using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hor φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          |  isTrue hq => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  |     ∀¹ φ, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hall φ' => simpa using hasDecEq φ φ'
  |     ∃¹ φ, ψ => by
      cases ψ using cases' <;> try { simp only [reduceCtorEq]; infer_instance }
      case hexs φ' => simpa using hasDecEq φ φ'


-- @@ L319-319 verbatim
instance : DecidableEq (Semiformula L ξ n) := hasDecEq


-- @@ L321-321 verbatim
end Decidable


-- @@ L323-323 verbatim
/-! Quantifier rank -/


-- @@ L325-325 verbatim
section qr


-- @@ L327-335 verbatim
def qr {n} : Semiformula L ξ n → ℕ
  |        ⊤ => 0
  |        ⊥ => 0
  |  rel _ _ => 0
  | nrel _ _ => 0
  |    φ ⋏ ψ => max φ.qr ψ.qr
  |    φ ⋎ ψ => max φ.qr ψ.qr
  |     ∀¹ φ => φ.qr + 1
  |     ∃¹ φ => φ.qr + 1


-- @@ L337-337 verbatim
@[simp] lemma qr_top : (⊤ : Semiformula L ξ n).qr = 0 := rfl


-- @@ L339-339 verbatim
@[simp] lemma qr_bot : (⊥ : Semiformula L ξ n).qr = 0 := rfl


-- @@ L341-341 verbatim
@[simp] lemma qr_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).qr = 0 := rfl


-- @@ L343-343 verbatim
@[simp] lemma qr_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).qr = 0 := rfl


-- @@ L345-345 verbatim
@[simp] lemma qr_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).qr = max φ.qr ψ.qr := rfl


-- @@ L347-347 verbatim
@[simp] lemma qr_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).qr = max φ.qr ψ.qr := rfl


-- @@ L349-349 verbatim
@[simp] lemma qr_all (φ : Semiformula L ξ (n + 1)) : (∀¹ φ).qr = φ.qr + 1 := rfl


-- @@ L351-351 verbatim
@[simp] lemma qr_exs (φ : Semiformula L ξ (n + 1)) : (∃¹ φ).qr = φ.qr + 1 := rfl


-- @@ L353-354 verbatim
@[simp] lemma qr_neg (φ : Semiformula L ξ n) : (∼φ).qr = φ.qr := by
  induction' φ using rec' <;> simp [*]


-- @@ L356-357 verbatim
@[simp] lemma qr_imply (φ ψ : Semiformula L ξ n) : (φ 🡒 ψ).qr = max φ.qr ψ.qr :=
  by simp [imp_eq]


-- @@ L359-360 verbatim
@[simp] lemma qr_iff (φ ψ : Semiformula L ξ n) : (φ 🡘 ψ).qr = max φ.qr ψ.qr :=
  by simp [iff_eq, total_of]


-- @@ L362-362 verbatim
end qr


-- @@ L364-364 verbatim
/-! Open (Semi-)Formula -/


-- @@ L366-366 verbatim
section Open


-- @@ L368-368 verbatim
def Open (φ : Semiformula L ξ n) : Prop := φ.qr = 0


-- @@ L370-370 verbatim
@[simp] lemma open_top : (⊤ : Semiformula L ξ n).Open := rfl


-- @@ L372-372 verbatim
@[simp] lemma open_bot : (⊥ : Semiformula L ξ n).Open := rfl


-- @@ L374-374 verbatim
@[simp] lemma open_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).Open := rfl


-- @@ L376-376 verbatim
@[simp] lemma open_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).Open := rfl


-- @@ L378-378 verbatim
@[simp] lemma open_and {φ ψ : Semiformula L ξ n} : (φ ⋏ ψ).Open ↔ φ.Open ∧ ψ.Open := by simp [Open]


-- @@ L380-380 verbatim
@[simp] lemma open_or {φ ψ : Semiformula L ξ n} : (φ ⋎ ψ).Open ↔ φ.Open ∧ ψ.Open := by simp [Open]


-- @@ L382-382 verbatim
@[simp] lemma not_open_all {φ : Semiformula L ξ (n + 1)} : ¬(∀¹ φ).Open := by simp [Open]


-- @@ L384-384 verbatim
@[simp] lemma not_open_exs {φ : Semiformula L ξ (n + 1)} : ¬(∃¹ φ).Open := by simp [Open]


-- @@ L386-387 verbatim
@[simp] lemma open_neg {φ : Semiformula L ξ n} : (∼φ).Open ↔ φ.Open := by
  simp [Open]


-- @@ L389-390 verbatim
@[simp] lemma open_imply {φ ψ : Semiformula L ξ n} : (φ 🡒 ψ).Open ↔ φ.Open ∧ ψ.Open :=
  by simp [Open]


-- @@ L392-393 verbatim
@[simp] lemma open_iff {φ ψ : Semiformula L ξ n} : (φ 🡘 ψ).Open ↔ φ.Open ∧ ψ.Open :=
  by simp [Open]


-- @@ L395-395 verbatim
end Open


-- @@ L397-397 verbatim
/-! Free Variables -/


-- @@ L399-399 verbatim
section FreeVariables


-- @@ L401-401 verbatim
variable [DecidableEq ξ]


-- @@ L403-415 verbatim
def freeVariables {n} : Semiformula L ξ n → Finset ξ
  |  rel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  | nrel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  |        ⊤ => ∅
  |        ⊥ => ∅
  |    φ ⋏ ψ => freeVariables φ ∪ freeVariables ψ
  |    φ ⋎ ψ => freeVariables φ ∪ freeVariables ψ
  |     ∀¹ φ => freeVariables φ
  |     ∃¹ φ => freeVariables φ

lemma freeVariables_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

lemma freeVariables_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl


-- @@ L417-417 verbatim
@[simp] lemma freeVariables_verum : (⊤ : Semiformula L ξ n).freeVariables = ∅ := rfl


-- @@ L419-419 verbatim
@[simp] lemma freeVariables_falsum : (⊥ : Semiformula L ξ n).freeVariables = ∅ := rfl


-- @@ L421-421 verbatim
@[simp] lemma freeVariables_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := rfl


-- @@ L423-423 verbatim
@[simp] lemma freeVariables_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := rfl


-- @@ L425-425 verbatim
@[simp] lemma freeVariables_all (φ : Semiformula L ξ (n + 1)) : (∀¹ φ).freeVariables = φ.freeVariables := rfl


-- @@ L427-427 verbatim
@[simp] lemma freeVariables_exs (φ : Semiformula L ξ (n + 1)) : (∃¹ φ).freeVariables = φ.freeVariables := rfl


-- @@ L429-430 verbatim
@[simp] lemma freeVariables_not (φ : Semiformula L ξ n) : (∼φ).freeVariables = φ.freeVariables := by
  induction φ using rec' <;> simp [*, freeVariables_rel, freeVariables_nrel]


-- @@ L432-432 verbatim
@[simp] lemma freeVariables_imp (φ ψ : Semiformula L ξ n) : (φ 🡒 ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := by simp [imp_eq]


-- @@ L434-435 verbatim
@[simp] lemma freeVariables_allClosure (φ : Semiformula L ξ n) : (∀¹* φ).freeVariables = φ.freeVariables := by
  induction n <;> simp [allClosure, *]


-- @@ L437-438 verbatim
@[simp] lemma freeVariables_sentence {ο : Type*} [IsEmpty ο] (φ : Semiformula L ο n) : φ.freeVariables = ∅ := by
  ext x; exact IsEmpty.elim inferInstance x


-- @@ L440-440 verbatim
abbrev FVar? (φ : Semiformula L ξ n) (x : ξ) : Prop := x ∈ φ.freeVariables


-- @@ L442-443 verbatim
@[simp] lemma fvar?_rel {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (rel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_rel]


-- @@ L445-446 verbatim
@[simp] lemma fvar?_nrel {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (nrel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_nrel]


-- @@ L448-448 verbatim
@[simp] lemma fvar?_top (x) : ¬(⊤ : Semiformula L ξ n).FVar? x := by simp [FVar?]


-- @@ L450-450 verbatim
@[simp] lemma fvar?_falsum (x) : ¬(⊥ : Semiformula L ξ n).FVar? x := by simp [FVar?]


-- @@ L452-452 verbatim
@[simp] lemma fvar?_and (x) (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by simp [FVar?]


-- @@ L454-454 verbatim
@[simp] lemma fvar?_or (x) (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by simp [FVar?]


-- @@ L456-456 verbatim
@[simp] lemma fvar?_all (x) (φ : Semiformula L ξ (n + 1)) : (∀¹ φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]


-- @@ L458-458 verbatim
@[simp] lemma fvar?_exs (x) (φ : Semiformula L ξ (n + 1)) : (∃¹ φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]


-- @@ L460-460 verbatim
@[simp] lemma fvar?_allClosure (x) (φ : Semiformula L ξ n) : (∀¹* φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]


-- @@ L462-475 verbatim
def fvSup (φ : Semiproposition L n) : ℕ := (φ.freeVariables.max).recBotCoe 0 .succ

lemma lt_fvSup_of_fvar? {φ : Semiproposition L n} : φ.FVar? m → m < φ.fvSup := by
  unfold fvSup FVar?
  intro hm
  have : ∃ s : ℕ, φ.freeVariables.max = s := Finset.max_of_mem hm
  rcases this with ⟨s, hs⟩
  have : m ≤ s := by
    have : (m : WithBot ℕ) ≤ ↑s := by simpa [hs, -Nat.cast_le] using Finset.le_max hm
    exact WithBot.coe_le_coe.mp this
  simpa [hs, WithBot.recBotCoe] using Nat.lt_add_one_of_le this

lemma not_fvar?_of_lt_fvSup (φ : Semiproposition L n) (h : φ.fvSup ≤ m) : ¬φ.FVar? m :=
  fun hm ↦ (lt_self_iff_false _).mp (lt_of_le_of_lt h <| lt_fvSup_of_fvar? hm)


-- @@ L477-478 verbatim
@[simp] lemma not_fvar?_fvSup (φ : Semiproposition L n) : ¬φ.FVar? φ.fvSup :=
  not_fvar?_of_lt_fvSup φ (by simp)


-- @@ L480-480 verbatim
end FreeVariables


-- @@ L482-482 verbatim
section


-- @@ L484-492 verbatim
variable {α : Type*} [LinearOrder α]

lemma List.maximam?_some_of_not_nil {l : List α} (h : l ≠ []) : l.max?.isSome := by
  cases l
  case nil => simp at h
  case cons l => simp [List.max?_cons]

lemma List.maximam?_eq_some [Std.LawfulOrderSup α] {l : List α} {a} (h : l.max? = some a) : ∀ x ∈ l, x ≤ a :=
  List.max?_le_iff h (x := a) |>.mp (by rfl)


-- @@ L494-497 verbatim
end

lemma ne_of_ne_complexity {φ ψ : Semiformula L ξ n} (h : φ.complexity ≠ ψ.complexity) : φ ≠ ψ :=
  by rintro rfl; contradiction


-- @@ L499-499 verbatim
@[simp] lemma ne_or_left (φ ψ : Semiformula L ξ n) : φ ≠ φ ⋎ ψ := ne_of_ne_complexity (by simp)


-- @@ L501-501 verbatim
@[simp] lemma ne_or_right (φ ψ : Semiformula L ξ n) : ψ ≠ φ ⋎ ψ := ne_of_ne_complexity (by simp)


-- @@ L503-503 verbatim
variable {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language} {ξ : Type*} {Φ : L₁ →ᵥ L₂}


-- @@ L505-517 verbatim
def lMapAux (Φ : L₁ →ᵥ L₂) {n} : Semiformula L₁ ξ n → Semiformula L₂ ξ n
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |  rel r v => rel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | nrel r v => nrel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  |    φ ⋏ ψ => lMapAux Φ φ ⋏ lMapAux Φ ψ
  |    φ ⋎ ψ => lMapAux Φ φ ⋎ lMapAux Φ ψ
  |     ∀¹ φ => ∀¹ lMapAux Φ φ
  |     ∃¹ φ => ∃¹ lMapAux Φ φ

lemma lMapAux_neg {n} (φ : Semiformula L₁ ξ n) :
    (∼φ).lMapAux Φ = ∼φ.lMapAux Φ := by
  induction φ using Semiformula.rec' <;> simp [*, lMapAux]


-- @@ L519-529 verbatim
/--
The map on semiformulas induced by a homomorphism between languages.
-/
def lMap (Φ : L₁ →ᵥ L₂) {n} : Semiformula L₁ ξ n →ˡᶜ Semiformula L₂ ξ n where
  toTr := lMapAux Φ
  map_top' := by simp [lMapAux]
  map_bot' := by simp [lMapAux]
  map_and' := by simp [lMapAux]
  map_or'  := by simp [lMapAux]
  map_neg' := by simp [lMapAux_neg]
  map_imply' := by simp [Semiformula.imp_eq, lMapAux_neg, ←Semiformula.neg_eq, lMapAux]


-- @@ L531-532 verbatim
@[simp] lemma lMap_rel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) (Semiterm.lMap Φ ∘ v) := rfl


-- @@ L534-535 verbatim
@[simp] lemma lMap_nrel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) (Semiterm.lMap Φ ∘ v) := rfl


-- @@ L537-538 verbatim
@[simp] lemma lMap_all (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∀¹ φ) = ∀¹ lMap Φ φ := rfl


-- @@ L540-541 verbatim
@[simp] lemma lMap_exs (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∃¹ φ) = ∃¹ lMap Φ φ := rfl


-- @@ L543-544 verbatim
@[simp] lemma lMap_ball (φ ψ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∀¹[φ] ψ) = ∀¹[lMap Φ φ] lMap Φ ψ := by simp [ball]


-- @@ L546-547 verbatim
@[simp] lemma lMap_bexs (φ ψ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∃¹[φ] ψ) = ∃¹[lMap Φ φ] lMap Φ ψ := by simp [bexs]


-- @@ L549-550 verbatim
@[simp] lemma lMap_allClosure (φ : Semiformula L₁ ξ n) :
    lMap Φ (∀¹* φ) = ∀¹* lMap Φ φ := by induction n <;> simp [*, allClosure_succ]


-- @@ L552-553 verbatim
@[simp] lemma lMap_exsClosure (φ : Semiformula L₁ ξ n) :
    lMap Φ (∃¹* φ) = ∃¹* lMap Φ φ := by induction n <;> simp [*, exsClosure_succ]


-- @@ L555-556 verbatim
@[simp] lemma lMap_allItr {k} (φ : Semiformula L₁ ξ (n + k)) :
    lMap Φ (∀¹^[k] φ) = ∀¹^[k] lMap Φ φ := by induction k <;> simp [*, allItr_succ];


-- @@ L558-559 verbatim
@[simp] lemma lMap_exsItr {k} (φ : Semiformula L₁ ξ (n + k)) :
    lMap Φ (∃¹^[k] φ) = ∃¹^[k] lMap Φ φ := by induction k <;> simp [*, exsItr_succ];


-- @@ L561-563 verbatim
@[simp] lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (φ : Semiformula L₁ ξ n) :
    (Semiformula.lMap Φ φ).freeVariables = φ.freeVariables := by
  induction φ using Semiformula.rec' <;> try simp [lMap_rel, lMap_nrel, freeVariables_rel, freeVariables_nrel, *]


-- @@ L565-565 verbatim
section enumerateFVar


-- @@ L567-575 verbatim
def fvarList {n : ℕ} : Semiformula L ξ n → List ξ
  |        ⊤ => []
  |        ⊥ => []
  |  rel _ v => List.flatten <| Matrix.toList fun i ↦ (v i).fvarList
  | nrel _ v => List.flatten <| Matrix.toList fun i ↦ (v i).fvarList
  |    p ⋏ q => p.fvarList ++ q.fvarList
  |    p ⋎ q => p.fvarList ++ q.fvarList
  |     ∀¹ p => p.fvarList
  |     ∃¹ p => p.fvarList


-- @@ L577-577 verbatim
def idxOfFVar [DecidableEq ξ] (φ : Semiformula L ξ n) : ξ → ℕ := φ.fvarList.idxOf


-- @@ L579-588 verbatim
def enumerateFVar [Inhabited ξ] (φ : Semiformula L ξ n) : ℕ → ξ :=
  fun i ↦ if hi : i < φ.fvarList.length then φ.fvarList.get ⟨i, hi⟩ else default

lemma enumerateFVar_idxOfFVar [DecidableEq ξ] [Inhabited ξ] {φ : Semiformula L ξ n} {x : ξ} (hx : x ∈ φ.fvarList) :
    enumerateFVar φ (idxOfFVar φ x) = x := by
  simpa [enumerateFVar, idxOfFVar]
  using fun h ↦ False.elim <| not_le.mpr (List.idxOf_lt_length_iff.mpr hx) h

lemma mem_fvarList_iff_fvar? [DecidableEq ξ] {φ : Semiformula L ξ n} : x ∈ φ.fvarList ↔ φ.FVar? x := by
  induction φ using rec' <;> simp [fvarList, Semiterm.mem_fvarList_iff_fvar?, *]


-- @@ L590-590 verbatim
end enumerateFVar


-- @@ L592-592 verbatim
end Semiformula


-- @@ L594-594 verbatim
abbrev Theory (L : Language) := Set (Sentence L)


-- @@ L596-596 verbatim
namespace Theory


-- @@ L598-598 verbatim
def lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) : Theory L₂ := Semiformula.lMap Φ '' T


-- @@ L600-600 verbatim
end Theory


-- @@ L602-602 verbatim
end FFL.FirstOrder


-- @@ L604-604 verbatim
end
