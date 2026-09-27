/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.Predicate.Term
public import LeanPool.Incompleteness.Foundation.Logic.Predicate.Quantifier
public import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Ring.Nat


-- @@ L13-22 verbatim
/-!
# Formulas of first-order logic

This file defines the formulas of first-order logic.

`φ : Semiformula L ξ n` is a (semi-)formula of language `L` with bounded variables of `Fin n` and
free variables of `ξ`.
The quantification is represented by de Bruijn index.

-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace LO


-- @@ L28-28 verbatim
namespace FirstOrder


-- @@ L30-39 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  | verum  {n} : Semiformula L ξ n
  | falsum {n} : Semiformula L ξ n
  | rel    {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | nrel   {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | and    {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | or     {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | all    {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n
  | ex     {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n


-- @@ L41-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0


-- @@ L44-45 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Sentence (L : Language) := Formula L Empty


-- @@ L47-48 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Semisentence (L : Language) (n : ℕ) := Semiformula L Empty n


-- @@ L50-51 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticSemiformula (L : Language) (n : ℕ) := Semiformula L ℕ n


-- @@ L53-54 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticFormula (L : Language) := SyntacticSemiformula L 0


-- @@ L56-56 verbatim
namespace Semiformula


-- @@ L58-61 verbatim
variable
  {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language}
  {ξ ξ₁ ξ₂ ξ₃ : Type*}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}


-- @@ L63-72 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def neg {n} : Semiformula L ξ n → Semiformula L ξ n
  | verum    => falsum
  | falsum   => verum
  | rel r v  => nrel r v
  | nrel r v => rel r v
  | and φ ψ  => or (neg φ) (neg ψ)
  | or φ ψ   => and (neg φ) (neg ψ)
  | all φ    => ex (neg φ)
  | ex φ     => all (neg φ)


-- @@ L74-75 verbatim
lemma neg_neg (φ : Semiformula L ξ n) : neg (neg φ) = φ :=
  by induction φ <;> simp[*, neg]


-- @@ L77-83 verbatim
instance : LogicalConnective (Semiformula L ξ n) where
  tilde := neg
  arrow := fun φ ψ => or (neg φ) ψ
  wedge := and
  vee := or
  top := verum
  bot := falsum


-- @@ L85-91 verbatim
instance : DeMorgan (Semiformula L ξ n) where
  verum := rfl
  falsum := rfl
  imply := fun _ _ => rfl
  and := fun _ _ => rfl
  or := fun _ _ => rfl
  neg := neg_neg


-- @@ L93-95 verbatim
instance : Quantifier (Semiformula L ξ) where
  univ := all
  ex := ex


-- @@ L97-97 verbatim
section «lp_section_1»


-- @@ L99-99 verbatim
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]


-- @@ L101-115 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def toStr {n} : Semiformula L ξ n → String
  | ⊤ => "\\top"
  | ⊥ => "\\bot"
  | rel (arity := 0) r _ => "{" ++ toString r ++ "}"
  | rel (arity := _ + 1) r v =>
    "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | nrel (arity := 0) r _ => "\\lnot {" ++ toString r ++ "}"
  | nrel (arity := _ + 1) r v =>
    "\\lnot {" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++
      "\\right)"
  | Wedge.wedge φ ψ => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | Vee.vee φ ψ => "\\left(" ++ toStr φ ++ " \\lor " ++ toStr ψ ++ "\\right)"
  | all φ => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr φ
  | ex φ => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr φ


-- @@ L117-117 verbatim
instance : Repr (Semiformula L ξ n) := ⟨fun t _ => toStr t⟩


-- @@ L119-119 verbatim
instance : ToString (Semiformula L ξ n) := ⟨toStr⟩


-- @@ L121-121 verbatim
end «lp_section_1»


-- @@ L123-123 expanded
@[simp]
lemma neg_top : Tilde.tilde (⊤ : Semiformula L ξ n) = ⊥ :=
  rfl


-- @@ L125-125 expanded
@[simp]
lemma neg_bot : Tilde.tilde (⊥ : Semiformula L ξ n) = ⊤ :=
  rfl


-- @@ L127-127 expanded
@[simp]
lemma neg_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Tilde.tilde (rel r v) = nrel r v :=
  rfl


-- @@ L129-129 expanded
@[simp]
lemma neg_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Tilde.tilde (nrel r v) = rel r v :=
  rfl


-- @@ L131-131 expanded
@[simp]
lemma neg_and (φ ψ : Semiformula L ξ n) :
    Tilde.tilde (Wedge.wedge φ ψ) = Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ) :=
  rfl


-- @@ L133-133 expanded
@[simp]
lemma neg_or (φ ψ : Semiformula L ξ n) :
    Tilde.tilde (Vee.vee φ ψ) = Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ) :=
  rfl


-- @@ L135-135 expanded
@[simp 1100]
lemma neg_all (φ : Semiformula L ξ (n + 1)) :
    Tilde.tilde (UnivQuantifier.univ φ) = ExQuantifier.ex (Tilde.tilde φ) :=
  rfl


-- @@ L137-137 expanded
@[simp]
lemma neg_ex (φ : Semiformula L ξ (n + 1)) :
    Tilde.tilde (ExQuantifier.ex φ) = UnivQuantifier.univ (Tilde.tilde φ) :=
  rfl


-- @@ L139-139 expanded
@[simp 1100]
lemma neg_neg' (φ : Semiformula L ξ n) : Tilde.tilde (Tilde.tilde φ) = φ :=
  neg_neg φ


-- @@ L141-144 expanded
@[simp]
lemma neg_inj (φ ψ : Semiformula L ξ n) : Tilde.tilde φ = Tilde.tilde ψ ↔ φ = ψ :=
  by
  constructor
  · intro h; simpa using congr_arg (Tilde.tilde ·) h
  · exact congr_arg _


-- @@ L146-147 expanded
@[simp]
lemma neg_univClosure (φ : Semiformula L ξ n) :
    Tilde.tilde (univClosure φ) = exClosure (Tilde.tilde φ) := by
  induction n <;> simp [univClosure, exClosure, *]


-- @@ L149-150 expanded
@[simp]
lemma neg_exClosure (φ : Semiformula L ξ n) :
    Tilde.tilde (exClosure φ) = univClosure (Tilde.tilde φ) := by
  induction n <;> simp [univClosure, exClosure, *]


-- @@ L152-152 expanded
lemma neg_eq (φ : Semiformula L ξ n) : Tilde.tilde φ = neg φ :=
  rfl


-- @@ L154-154 expanded
lemma imp_eq (φ ψ : Semiformula L ξ n) : Arrow.arrow φ ψ = Vee.vee (Tilde.tilde φ) ψ :=
  rfl


-- @@ L156-156 expanded
lemma iff_eq (φ ψ : Semiformula L ξ n) :
    LogicalConnective.iff φ ψ =
      Wedge.wedge (Vee.vee (Tilde.tilde φ) ψ) (Vee.vee (Tilde.tilde ψ) φ) :=
  rfl


-- @@ L158-158 expanded
lemma ball_eq (φ ψ : Semiformula L ξ (n + 1)) :
    (ball φ ψ) = UnivQuantifier.univ (Arrow.arrow φ ψ) :=
  rfl


-- @@ L160-160 expanded
lemma bex_eq (φ ψ : Semiformula L ξ (n + 1)) : (bex φ ψ) = ExQuantifier.ex (Wedge.wedge φ ψ) :=
  rfl


-- @@ L162-163 expanded
@[simp]
lemma neg_ball (φ ψ : Semiformula L ξ (n + 1)) : Tilde.tilde (ball φ ψ) = bex φ (Tilde.tilde ψ) :=
  by simp [ball, bex, imp_eq]


-- @@ L165-166 expanded
@[simp]
lemma neg_bex (φ ψ : Semiformula L ξ (n + 1)) : Tilde.tilde (bex φ ψ) = ball φ (Tilde.tilde ψ) := by
  simp [ball, bex, imp_eq]


-- @@ L168-169 expanded
@[simp]
lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) :
    Wedge.wedge φ₁ φ₂ = Wedge.wedge ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Wedge.wedge]


-- @@ L171-172 expanded
@[simp]
lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) :
    Vee.vee φ₁ φ₂ = Vee.vee ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Vee.vee]


-- @@ L174-175 expanded
@[simp]
lemma all_inj (φ ψ : Semiformula L ξ (n + 1)) :
    UnivQuantifier.univ φ = UnivQuantifier.univ ψ ↔ φ = ψ := by simp [UnivQuantifier.univ]


-- @@ L177-178 expanded
@[simp]
lemma ex_inj (φ ψ : Semiformula L ξ (n + 1)) : ExQuantifier.ex φ = ExQuantifier.ex ψ ↔ φ = ψ := by
  simp [ExQuantifier.ex]


-- @@ L180-181 expanded
@[simp]
lemma univClosure_inj (φ ψ : Semiformula L ξ n) : univClosure φ = univClosure ψ ↔ φ = ψ := by
  induction n <;> simp [*, univClosure_succ]


-- @@ L183-184 expanded
@[simp]
lemma exClosure_inj (φ ψ : Semiformula L ξ n) : exClosure φ = exClosure ψ ↔ φ = ψ := by
  induction n <;> simp [*, exClosure_succ]


-- @@ L186-187 expanded
@[simp]
lemma univItr_inj {k} (φ ψ : Semiformula L ξ (n + k)) : univItr k φ = univItr k ψ ↔ φ = ψ := by
  induction k <;> simp [*, univItr_succ]


-- @@ L189-190 expanded
@[simp]
lemma exItr_inj {k} (φ ψ : Semiformula L ξ (n + k)) : exItr k φ = exItr k ψ ↔ φ = ψ := by
  induction k <;> simp [*, exItr_succ]


-- @@ L192-193 expanded
@[simp]
lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L ξ n} :
    Arrow.arrow φ₁ φ₂ = Arrow.arrow ψ₁ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [imp_eq]


-- @@ L195-196 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev «rel!» (L : Language) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := rel r v


-- @@ L198-199 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev «nrel!» (L : Language) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := nrel r v


-- @@ L201-210 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def complexity {n : ℕ} : Semiformula L ξ n → ℕ
  | ⊤ => 0
  | ⊥ => 0
  | rel _ _ => 0
  | nrel _ _ => 0
  | Wedge.wedge φ ψ => max φ.complexity ψ.complexity + 1
  | Vee.vee φ ψ => max φ.complexity ψ.complexity + 1
  | UnivQuantifier.univ φ => φ.complexity + 1
  | ExQuantifier.ex φ => φ.complexity + 1


-- @@ L212-212 verbatim
@[simp] lemma complexity_top : complexity (⊤ : Semiformula L ξ n) = 0 := rfl


-- @@ L214-214 verbatim
@[simp] lemma complexity_bot : complexity (⊥ : Semiformula L ξ n) = 0 := rfl


-- @@ L216-217 verbatim
@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    complexity (rel r v) = 0 := rfl


-- @@ L219-220 verbatim
@[simp] lemma complexity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    complexity (nrel r v) = 0 := rfl


-- @@ L222-223 expanded
@[simp]
lemma complexity_and (φ ψ : Semiformula L ξ n) :
    complexity (Wedge.wedge φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl


-- @@ L224-225 verbatim
@[simp] lemma complexity_and' (φ ψ : Semiformula L ξ n) :
    complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L227-228 expanded
@[simp]
lemma complexity_or (φ ψ : Semiformula L ξ n) :
    complexity (Vee.vee φ ψ) = max φ.complexity ψ.complexity + 1 :=
  rfl


-- @@ L229-230 verbatim
@[simp] lemma complexity_or' (φ ψ : Semiformula L ξ n) :
    complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L232-233 expanded
@[simp]
lemma complexity_all (φ : Semiformula L ξ (n + 1)) :
    complexity (UnivQuantifier.univ φ) = φ.complexity + 1 :=
  rfl


-- @@ L234-235 verbatim
@[simp] lemma complexity_all' (φ : Semiformula L ξ (n + 1)) :
    complexity (all φ) = φ.complexity + 1 := rfl


-- @@ L237-238 expanded
@[simp]
lemma complexity_ex (φ : Semiformula L ξ (n + 1)) :
    complexity (ExQuantifier.ex φ) = φ.complexity + 1 :=
  rfl


-- @@ L239-240 verbatim
@[simp] lemma complexity_ex' (φ : Semiformula L ξ (n + 1)) :
    complexity (ex φ) = φ.complexity + 1 := rfl


-- @@ L242-261 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L ξ n → Sort w} (hverum : ∀ {n : ℕ}, C n ⊤)
    (hfalsum : ∀ {n : ℕ}, C n ⊥)
    (hrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hnrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hand : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (Wedge.wedge φ ψ))
    (hor : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (Vee.vee φ ψ))
    (hall : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (UnivQuantifier.univ φ))
    (hex : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (ExQuantifier.ex φ)) :
    ∀ {n : ℕ} (φ : Semiformula L ξ n), C n φ
  | _, verum => hverum
  | _, falsum => hfalsum
  | _, rel r v => hrel r v
  | _, nrel r v => hnrel r v
  | _, and φ ψ => hand φ ψ
  | _, or φ ψ => hor φ ψ
  | _, all φ => hall φ
  | _, ex φ => hex φ


-- @@ L263-286 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L ξ n → Sort w} (hverum : ∀ {n : ℕ}, C n ⊤)
    (hfalsum : ∀ {n : ℕ}, C n ⊥)
    (hrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hnrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hand : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (Wedge.wedge φ ψ))
    (hor : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (Vee.vee φ ψ))
    (hall : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (UnivQuantifier.univ φ))
    (hex : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (ExQuantifier.ex φ)) :
    ∀ {n : ℕ} (φ : Semiformula L ξ n), C n φ
  | _, verum => hverum
  | _, falsum => hfalsum
  | _, rel r v => hrel r v
  | _, nrel r v => hnrel r v
  | _, and φ ψ =>
    hand φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ)
      (rec' hverum hfalsum hrel hnrel hand hor hall hex ψ)
  | _, or φ ψ =>
    hor φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ)
      (rec' hverum hfalsum hrel hnrel hand hor hall hex ψ)
  | _, all φ => hall φ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ)
  | _, ex φ => hex φ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ)


-- @@ L288-289 expanded
@[simp]
lemma complexity_neg (φ : Semiformula L ξ n) : complexity (Tilde.tilde φ) = complexity φ := by
  induction φ using rec' <;> simp [*]


-- @@ L291-291 verbatim
section «lp_section_2»


-- @@ L293-293 verbatim
variable [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)] [DecidableEq ξ]


-- @@ L295-366 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : {n : ℕ} → (φ ψ : Semiformula L ξ n) → Decidable (φ = ψ)
  | _, ⊤, ψ => by
    cases ψ using cases'
    case hverum => exact isTrue rfl
    all_goals exact isFalse (by intro h; cases h)
  | _, ⊥, ψ => by
    cases ψ using cases'
    case hfalsum => exact isTrue rfl
    all_goals exact isFalse (by intro h; cases h)
  | _, rel r v, ψ => by
    cases ψ using cases'
    case hrel k₁ k₂ r₂ v₂ =>
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact
          match decEq r r₂ with
          | isTrue h => by
            rcases h with rfl
            exact
              match Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i)) with
              | isTrue hv => isTrue (by rw [hv])
              | isFalse hv => isFalse (by intro h; cases h; exact hv rfl)
          | isFalse h => isFalse (by intro hrel; cases hrel; exact h rfl)
      · exact isFalse (by simp [e])
    all_goals exact isFalse (by intro h; cases h)
  | _, nrel r v, ψ => by
    cases ψ using cases'
    case hnrel k₁ k₂ r₂ v₂ =>
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact
          match decEq r r₂ with
          | isTrue h => by
            rcases h with rfl
            exact
              match Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i)) with
              | isTrue hv => isTrue (by rw [hv])
              | isFalse hv => isFalse (by intro h; cases h; exact hv rfl)
          | isFalse h => isFalse (by intro hnrel; cases hnrel; exact h rfl)
      · exact isFalse (by simp [e])
    all_goals exact isFalse (by intro h; cases h)
  | _, Wedge.wedge φ ψ, r => by
    cases r using cases'
    case hand φ' ψ' =>
      exact
        match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
    all_goals exact isFalse (by intro h; cases h)
  | _, Vee.vee φ ψ, r => by
    cases r using cases'
    case hor φ' ψ' =>
      exact
        match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
    all_goals exact isFalse (by intro h; cases h)
  | _, UnivQuantifier.univ φ, ψ => by
    cases ψ using cases'
    case hall φ' =>
      exact
        match hasDecEq φ φ' with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    all_goals exact isFalse (by intro h; cases h)
  | _, ExQuantifier.ex φ, ψ => by
    cases ψ using cases'
    case hex φ' =>
      exact
        match hasDecEq φ φ' with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    all_goals exact isFalse (by intro h; cases h)


-- @@ L368-368 verbatim
instance : DecidableEq (Semiformula L ξ n) := hasDecEq


-- @@ L370-370 verbatim
end «lp_section_2»


-- @@ L372-372 verbatim
/-! Quantifier Rank -/


-- @@ L374-374 verbatim
section «lp_section_3»


-- @@ L376-385 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def qr : ∀ {n}, Semiformula L ξ n → ℕ
  | _, ⊤ => 0
  | _, ⊥ => 0
  | _, rel _ _ => 0
  | _, nrel _ _ => 0
  | _, Wedge.wedge φ ψ => max φ.qr ψ.qr
  | _, Vee.vee φ ψ => max φ.qr ψ.qr
  | _, UnivQuantifier.univ φ => φ.qr + 1
  | _, ExQuantifier.ex φ => φ.qr + 1


-- @@ L387-387 verbatim
@[simp] lemma qr_top : (⊤ : Semiformula L ξ n).qr = 0 := rfl


-- @@ L389-389 verbatim
@[simp] lemma qr_bot : (⊥ : Semiformula L ξ n).qr = 0 := rfl


-- @@ L391-391 verbatim
@[simp] lemma qr_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).qr = 0 := rfl


-- @@ L393-393 verbatim
@[simp] lemma qr_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).qr = 0 := rfl


-- @@ L395-395 expanded
@[simp]
lemma qr_and (φ ψ : Semiformula L ξ n) : (Wedge.wedge φ ψ).qr = max φ.qr ψ.qr :=
  rfl


-- @@ L397-397 expanded
@[simp]
lemma qr_or (φ ψ : Semiformula L ξ n) : (Vee.vee φ ψ).qr = max φ.qr ψ.qr :=
  rfl


-- @@ L399-399 expanded
@[simp]
lemma qr_all (φ : Semiformula L ξ (n + 1)) : (UnivQuantifier.univ φ).qr = φ.qr + 1 :=
  rfl


-- @@ L401-401 expanded
@[simp]
lemma qr_ex (φ : Semiformula L ξ (n + 1)) : (ExQuantifier.ex φ).qr = φ.qr + 1 :=
  rfl


-- @@ L403-404 expanded
@[simp]
lemma qr_neg (φ : Semiformula L ξ n) : (Tilde.tilde φ).qr = φ.qr := by
  induction φ using rec' <;> simp [*]


-- @@ L406-407 expanded
@[simp]
lemma qr_imply (φ ψ : Semiformula L ξ n) : (Arrow.arrow φ ψ).qr = max φ.qr ψ.qr := by simp [imp_eq]


-- @@ L409-410 expanded
@[simp]
lemma qr_iff (φ ψ : Semiformula L ξ n) : (LogicalConnective.iff φ ψ).qr = max φ.qr ψ.qr := by
  simp [iff_eq, total_of]


-- @@ L412-412 verbatim
end «lp_section_3»


-- @@ L414-414 verbatim
/-! Open (Semi-)Formula -/


-- @@ L416-416 verbatim
section «lp_section_4»


-- @@ L418-419 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Open (φ : Semiformula L ξ n) : Prop := φ.qr = 0


-- @@ L421-421 verbatim
lemma open_top : (⊤ : Semiformula L ξ n).Open := rfl


-- @@ L423-423 verbatim
lemma open_bot : (⊥ : Semiformula L ξ n).Open := rfl


-- @@ L425-425 verbatim
lemma open_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).Open := rfl


-- @@ L427-427 verbatim
lemma open_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).Open := rfl


-- @@ L429-429 expanded
@[simp]
lemma open_and {φ ψ : Semiformula L ξ n} : (Wedge.wedge φ ψ).Open ↔ φ.Open ∧ ψ.Open := by
  simp [Open]


-- @@ L431-431 expanded
@[simp]
lemma open_or {φ ψ : Semiformula L ξ n} : (Vee.vee φ ψ).Open ↔ φ.Open ∧ ψ.Open := by simp [Open]


-- @@ L433-433 expanded
@[simp]
lemma not_open_all {φ : Semiformula L ξ (n + 1)} : ¬(UnivQuantifier.univ φ).Open := by simp [Open]


-- @@ L435-435 expanded
@[simp]
lemma not_open_ex {φ : Semiformula L ξ (n + 1)} : ¬(ExQuantifier.ex φ).Open := by simp [Open]


-- @@ L437-437 expanded
@[simp]
lemma open_neg {φ : Semiformula L ξ n} : (Tilde.tilde φ).Open ↔ φ.Open := by simp [Open]


-- @@ L439-440 expanded
@[simp]
lemma open_imply {φ ψ : Semiformula L ξ n} : (Arrow.arrow φ ψ).Open ↔ φ.Open ∧ ψ.Open := by
  simp [Open]


-- @@ L442-443 expanded
@[simp]
lemma open_iff {φ ψ : Semiformula L ξ n} : (LogicalConnective.iff φ ψ).Open ↔ φ.Open ∧ ψ.Open := by
  simp [Open]


-- @@ L445-445 verbatim
end «lp_section_4»


-- @@ L447-447 verbatim
/-! Free Variables -/


-- @@ L449-449 verbatim
section «lp_section_5»


-- @@ L451-451 verbatim
variable [DecidableEq ξ]


-- @@ L453-462 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def freeVariables : {n : ℕ} → Semiformula L ξ n → Finset ξ
  | _, rel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  | _, nrel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  | _, ⊤ => ∅
  | _, ⊥ => ∅
  | _, Wedge.wedge φ ψ => freeVariables φ ∪ freeVariables ψ
  | _, Vee.vee φ ψ => freeVariables φ ∪ freeVariables ψ
  | _, UnivQuantifier.univ φ => freeVariables φ
  | _, ExQuantifier.ex φ => freeVariables φ


-- @@ L464-465 verbatim
lemma freeVariables_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl


-- @@ L467-468 verbatim
lemma freeVariables_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl


-- @@ L470-470 verbatim
@[simp] lemma freeVariables_verum : (⊤ : Semiformula L ξ n).freeVariables = ∅ := rfl


-- @@ L472-472 verbatim
@[simp] lemma freeVariables_falsum : (⊥ : Semiformula L ξ n).freeVariables = ∅ := rfl


-- @@ L474-475 expanded
@[simp]
lemma freeVariables_and (φ ψ : Semiformula L ξ n) :
    (Wedge.wedge φ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables :=
  rfl


-- @@ L477-478 expanded
@[simp]
lemma freeVariables_or (φ ψ : Semiformula L ξ n) :
    (Vee.vee φ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables :=
  rfl


-- @@ L480-481 expanded
@[simp]
lemma freeVariables_all (φ : Semiformula L ξ (n + 1)) :
    (UnivQuantifier.univ φ).freeVariables = φ.freeVariables :=
  rfl


-- @@ L483-484 expanded
@[simp]
lemma freeVariables_ex (φ : Semiformula L ξ (n + 1)) :
    (ExQuantifier.ex φ).freeVariables = φ.freeVariables :=
  rfl


-- @@ L486-487 expanded
@[simp]
lemma freeVariables_not (φ : Semiformula L ξ n) : (Tilde.tilde φ).freeVariables = φ.freeVariables :=
  by induction φ using rec' <;> simp [*, freeVariables_rel, freeVariables_nrel]


-- @@ L489-490 expanded
@[simp]
lemma freeVariables_imp (φ ψ : Semiformula L ξ n) :
    (Arrow.arrow φ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := by simp [imp_eq]


-- @@ L492-494 expanded
@[simp]
lemma freeVariables_univClosure (φ : Semiformula L ξ n) :
    (univClosure φ).freeVariables = φ.freeVariables := by induction n <;> simp [univClosure, *]


-- @@ L496-498 verbatim
@[simp] lemma freeVariables_sentence {ο : Type*} [IsEmpty ο] (φ : Semiformula L ο n) :
    φ.freeVariables = ∅ := by
  ext x; exact IsEmpty.elim inferInstance x


-- @@ L500-501 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev «FVar?» (φ : Semiformula L ξ n) (x : ξ) : Prop := x ∈ φ.freeVariables


-- @@ L503-504 verbatim
@[simp] lemma «fvar?_rel» {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (rel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_rel]


-- @@ L506-507 verbatim
@[simp] lemma «fvar?_nrel» {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (nrel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_nrel]


-- @@ L509-509 verbatim
@[simp] lemma «fvar?_top» (x) : ¬(⊤ : Semiformula L ξ n).FVar? x := by simp [FVar?]


-- @@ L511-511 verbatim
@[simp] lemma «fvar?_falsum» (x) : ¬(⊥ : Semiformula L ξ n).FVar? x := by simp [FVar?]


-- @@ L513-514 expanded
@[simp]
lemma fvar?_and (x) (φ ψ : Semiformula L ξ n) : (Wedge.wedge φ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x :=
  by simp [FVar?]


-- @@ L516-517 expanded
@[simp]
lemma fvar?_or (x) (φ ψ : Semiformula L ξ n) : (Vee.vee φ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by
  simp [FVar?]


-- @@ L519-520 expanded
@[simp]
lemma fvar?_all (x) (φ : Semiformula L ξ (n + 1)) : (UnivQuantifier.univ φ).FVar? x ↔ φ.FVar? x :=
  by simp [FVar?]


-- @@ L522-523 expanded
@[simp]
lemma fvar?_ex (x) (φ : Semiformula L ξ (n + 1)) : (ExQuantifier.ex φ).FVar? x ↔ φ.FVar? x := by
  simp [FVar?]


-- @@ L525-526 expanded
@[simp]
lemma fvar?_univClosure (x) (φ : Semiformula L ξ n) : (univClosure φ).FVar? x ↔ φ.FVar? x := by
  simp [FVar?]


-- @@ L528-529 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def fvSup (φ : SyntacticSemiformula L n) : ℕ := (φ.freeVariables.max).recBotCoe 0 .succ


-- @@ L531-539 verbatim
lemma «lt_fvSup_of_fvar?» {φ : SyntacticSemiformula L n} : φ.FVar? m → m < φ.fvSup := by
  unfold fvSup FVar?
  intro hm
  have : ∃ s : ℕ, φ.freeVariables.max = s := Finset.max_of_mem hm
  rcases this with ⟨s, hs⟩
  have : m ≤ s := by
    have : (m : WithBot ℕ) ≤ ↑s := hs ▸ Finset.le_max hm
    exact WithBot.coe_le_coe.mp this
  simpa [hs, WithBot.recBotCoe] using Nat.lt_add_one_of_le this


-- @@ L541-542 verbatim
lemma «not_fvar?_of_lt_fvSup» (φ : SyntacticSemiformula L n) (h : φ.fvSup ≤ m) : ¬φ.FVar? m :=
  fun hm ↦ (lt_self_iff_false _).mp (lt_of_le_of_lt h <| lt_fvSup_of_fvar? hm)


-- @@ L544-545 verbatim
@[simp] lemma «not_fvar?_fvSup» (φ : SyntacticSemiformula L n) : ¬φ.FVar? φ.fvSup :=
  not_fvar?_of_lt_fvSup φ (by simp)


-- @@ L547-547 verbatim
end «lp_section_5»


-- @@ L549-549 verbatim
section «lp_section_6»


-- @@ L551-551 verbatim
variable {α : Type*} [LinearOrder α]


-- @@ L553-553 verbatim
namespace List


-- @@ L555-556 verbatim
lemma «maximam?_some_of_not_nil» {l : List α} (h : l ≠ []) : l.max?.isSome := by
  simp_all


-- @@ L558-559 verbatim
lemma «maximam?_eq_some» {l : List α} {a} (h : l.max? = some a) : ∀ x ∈ l, x ≤ a :=
  (List.max?_le_iff h (x := a)).mp le_rfl


-- @@ L561-561 verbatim
end List


-- @@ L563-563 verbatim
end «lp_section_6»


-- @@ L565-566 verbatim
lemma ne_of_ne_complexity {φ ψ : Semiformula L ξ n} (h : φ.complexity ≠ ψ.complexity) : φ ≠ ψ :=
  by rintro rfl; contradiction


-- @@ L568-568 expanded
@[simp]
lemma ne_or_left (φ ψ : Semiformula L ξ n) : φ ≠ Vee.vee φ ψ :=
  ne_of_ne_complexity (by simp)


-- @@ L570-571 expanded
@[simp]
lemma ne_or_right (φ ψ : Semiformula L ξ n) : ψ ≠ Vee.vee φ ψ :=
  ne_of_ne_complexity (Nat.ne_step_max' ψ.complexity φ.complexity)


-- @@ L573-573 verbatim
variable {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language} {ξ : Type*} {Φ : L₁ →ᵥ L₂}


-- @@ L575-584 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def lMapAux (Φ : L₁ →ᵥ L₂) : ∀ {n}, Semiformula L₁ ξ n → Semiformula L₂ ξ n
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, rel r v => rel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | _, nrel r v => nrel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | _, Wedge.wedge φ ψ => Wedge.wedge (lMapAux Φ φ) (lMapAux Φ ψ)
  | _, Vee.vee φ ψ => Vee.vee (lMapAux Φ φ) (lMapAux Φ ψ)
  | _, UnivQuantifier.univ φ => UnivQuantifier.univ (lMapAux Φ φ)
  | _, ExQuantifier.ex φ => ExQuantifier.ex (lMapAux Φ φ)


-- @@ L586-587 expanded
lemma lMapAux_neg {n} (φ : Semiformula L₁ ξ n) :
    (Tilde.tilde φ).lMapAux Φ = Tilde.tilde (φ.lMapAux Φ) := by
  induction φ using Semiformula.rec' <;> simp [*, lMapAux]


-- @@ L589-597 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def lMap (Φ : L₁ →ᵥ L₂) {n} : Hom (Semiformula L₁ ξ n) (Semiformula L₂ ξ n)
    where
  toTr := lMapAux Φ
  map_top' := by simp [lMapAux]
  map_bot' := by simp [lMapAux]
  map_and' := by simp [lMapAux]
  map_or' := by simp [lMapAux]
  map_neg' := by simp [lMapAux_neg]
  map_imply' := by simp [Semiformula.imp_eq, lMapAux_neg, ← Semiformula.neg_eq, lMapAux]


-- @@ L599-600 verbatim
lemma lMap_rel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl


-- @@ L602-603 verbatim
@[simp] lemma lMap_rel₀ (r : L₁.Rel 0) (v : Fin 0 → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) ![] := by simp[lMap_rel, Matrix.empty_eq]


-- @@ L605-607 verbatim
@[simp] lemma lMap_rel₁ (r : L₁.Rel 1) (t : Semiterm L₁ ξ n) :
    lMap Φ (rel r ![t]) = rel (Φ.rel r) ![t.lMap Φ] := by
      simp[lMap_rel, Matrix.constant_eq_singleton]


-- @@ L609-617 verbatim
@[simp] lemma lMap_rel₂ (r : L₁.Rel 2) (t₁ t₂ : Semiterm L₁ ξ n) :
    lMap Φ (rel r ![t₁, t₂]) = rel (Φ.rel r) ![t₁.lMap Φ, t₂.lMap Φ] := by
  rw [lMap_rel]
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp_all


-- @@ L619-620 verbatim
lemma lMap_nrel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl


-- @@ L622-623 verbatim
@[simp] lemma lMap_nrel₀ (r : L₁.Rel 0) (v : Fin 0 → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) ![] := by simp[lMap_nrel, Matrix.empty_eq]


-- @@ L625-627 verbatim
@[simp] lemma lMap_nrel₁ (r : L₁.Rel 1) (t : Semiterm L₁ ξ n) :
    lMap Φ (nrel r ![t]) = nrel (Φ.rel r) ![t.lMap Φ] := by
      simp[lMap_nrel, Matrix.constant_eq_singleton]


-- @@ L629-637 verbatim
@[simp] lemma lMap_nrel₂ (r : L₁.Rel 2) (t₁ t₂ : Semiterm L₁ ξ n) :
    lMap Φ (nrel r ![t₁, t₂]) = nrel (Φ.rel r) ![t₁.lMap Φ, t₂.lMap Φ] := by
  rw [lMap_nrel]
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp_all


-- @@ L639-640 expanded
@[simp]
lemma lMap_all (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (UnivQuantifier.univ φ) = UnivQuantifier.univ (lMap Φ φ) :=
  rfl


-- @@ L642-643 expanded
@[simp]
lemma lMap_ex (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (ExQuantifier.ex φ) = ExQuantifier.ex (lMap Φ φ) :=
  rfl


-- @@ L645-646 expanded
@[simp]
lemma lMap_ball (φ ψ : Semiformula L₁ ξ (n + 1)) : lMap Φ (ball φ ψ) = ball (lMap Φ φ) (lMap Φ ψ) :=
  by simp [ball]


-- @@ L648-649 expanded
@[simp]
lemma lMap_bex (φ ψ : Semiformula L₁ ξ (n + 1)) : lMap Φ (bex φ ψ) = bex (lMap Φ φ) (lMap Φ ψ) := by
  simp [bex]


-- @@ L651-652 expanded
@[simp]
lemma lMap_univClosure (φ : Semiformula L₁ ξ n) : lMap Φ (univClosure φ) = univClosure (lMap Φ φ) :=
  by induction n <;> simp [*, univClosure_succ]


-- @@ L654-655 expanded
@[simp]
lemma lMap_exClosure (φ : Semiformula L₁ ξ n) : lMap Φ (exClosure φ) = exClosure (lMap Φ φ) := by
  induction n <;> simp [*, exClosure_succ]


-- @@ L657-658 expanded
@[simp]
lemma lMap_univItr {k} (φ : Semiformula L₁ ξ (n + k)) :
    lMap Φ (univItr k φ) = univItr k (lMap Φ φ) := by induction k <;> simp [*, univItr_succ]


-- @@ L660-661 expanded
@[simp]
lemma lMap_exItr {k} (φ : Semiformula L₁ ξ (n + k)) : lMap Φ (exItr k φ) = exItr k (lMap Φ φ) := by
  induction k <;> simp [*, exItr_succ]


-- @@ L663-666 verbatim
@[simp] lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (φ : Semiformula L₁ ξ n) :
    (Semiformula.lMap Φ φ).freeVariables = φ.freeVariables := by
  induction φ using Semiformula.rec' <;> try simp [lMap_rel, lMap_nrel, freeVariables_rel,
    freeVariables_nrel, *]


-- @@ L668-668 verbatim
end Semiformula


-- @@ L670-671 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Theory (L : Language) := Set (SyntacticFormula L)


-- @@ L673-674 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ClosedTheory (L : Language) := Set (Sentence L)


-- @@ L676-676 verbatim
instance : Collection (SyntacticFormula L) (Theory L) := inferInstance


-- @@ L678-678 verbatim
instance : Collection (Sentence L) (ClosedTheory L) := inferInstance


-- @@ L680-682 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Theory.lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) :
    Theory L₂ := Semiformula.lMap Φ '' T


-- @@ L684-684 verbatim
namespace Theory


-- @@ L686-686 verbatim
variable (T U : Theory L)


-- @@ L688-688 verbatim
instance {L : Language} : Add (Theory L) := ⟨(· ∪ ·)⟩


-- @@ L690-690 verbatim
lemma add_def : T + U = T ∪ U := rfl


-- @@ L692-692 verbatim
end Theory


-- @@ L694-694 verbatim
end FirstOrder


-- @@ L696-696 verbatim
end LO
