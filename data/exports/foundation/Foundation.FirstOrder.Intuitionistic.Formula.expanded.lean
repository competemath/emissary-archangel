module

public import Foundation.FirstOrder.Basic


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-14 verbatim
/-!
# Formulas of intuitionistic first-order logic

This file defines the formulas of first-order logic.

`φ : Semiformulaᵢ L ξ n` is a (semi-)formula of language `L` with bounded variables of `Fin n` and free variables of `ξ`.
The quantification is represented by de Bruijn index.

-/


-- @@ L16-16 verbatim
namespace FFL.FirstOrder


-- @@ L18-25 verbatim
inductive Semiformulaᵢ (L : Language) (ξ : Type*) : ℕ → Type _ where
  | falsum : Semiformulaᵢ L ξ n
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformulaᵢ L ξ n
  |    and : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  |     or : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  |    imp : Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n → Semiformulaᵢ L ξ n
  |    all : Semiformulaᵢ L ξ (n + 1) → Semiformulaᵢ L ξ n
  |    exs : Semiformulaᵢ L ξ (n + 1) → Semiformulaᵢ L ξ n


-- @@ L27-27 verbatim
abbrev Formulaᵢ (L : Language) (ξ : Type*) := Semiformulaᵢ L ξ 0


-- @@ L29-29 verbatim
abbrev Sentenceᵢ (L : Language) := Formulaᵢ L Empty


-- @@ L31-31 verbatim
abbrev Semisentenceᵢ (L : Language) (n : ℕ) := Semiformulaᵢ L Empty n


-- @@ L33-33 verbatim
abbrev Semipropositionᵢ (L : Language) (n : ℕ) := Semiformulaᵢ L ℕ n


-- @@ L35-35 verbatim
abbrev Propositionᵢ (L : Language) := Semipropositionᵢ L 0


-- @@ L37-37 verbatim
variable {L : Language}


-- @@ L39-39 verbatim
namespace Semiformulaᵢ


-- @@ L41-41 verbatim
instance : Bot (Semiformulaᵢ L ξ n) := ⟨falsum⟩


-- @@ L43-43 verbatim
instance : Arrow (Semiformulaᵢ L ξ n) := ⟨imp⟩


-- @@ L45-45 verbatim
abbrev neg (φ : Semiformulaᵢ L ξ n) : Semiformulaᵢ L ξ n := φ 🡒 ⊥


-- @@ L47-47 verbatim
abbrev verum : Semiformulaᵢ L ξ n := ⊥ 🡒 ⊥


-- @@ L49-53 verbatim
instance : LogicalConnective (Semiformulaᵢ L ξ n) where
  arrow := imp
  wedge := and
  vee := or
  tilde := neg


-- @@ L55-61 verbatim
instance : LogicalNeutral (Semiformulaᵢ L ξ n) where
  top := verum
  bot := falsum

lemma neg_def (φ : Semiformulaᵢ L ξ n) : ∼φ = φ 🡒 ⊥ := rfl

lemma verum_def : (⊤ : Semiformulaᵢ L ξ n) = ⊥ 🡒 ⊥ := rfl


-- @@ L63-65 verbatim
instance : Quantifier (Semiformulaᵢ L ξ) where
  all := all
  exs := exs


-- @@ L67-67 verbatim
section ToString


-- @@ L69-69 verbatim
variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]


-- @@ L71-79 verbatim
def toStr : ∀ {n}, Semiformulaᵢ L ξ n → String
  | _, ⊥ => "\\bot"
  | _, rel (arity := 0) r _ => "{" ++ toString r ++ "}"
  | _, rel (arity := _ + 1) r v => "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | _, φ ⋏ ψ => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | _, φ ⋎ ψ => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | _, φ 🡒 ψ => "\\left(" ++ toStr φ ++ " \\to "  ++ toStr ψ ++ "\\right)"
  | n, all φ => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr φ
  | n, exs φ => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr φ


-- @@ L81-81 verbatim
instance : Repr (Semiformulaᵢ L ξ n) := ⟨fun t _ => toStr t⟩


-- @@ L83-83 verbatim
instance : ToString (Semiformulaᵢ L ξ n) := ⟨toStr⟩


-- @@ L85-85 verbatim
end ToString


-- @@ L87-88 verbatim
@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaᵢ L ξ n) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
  Iff.of_eq <| and.injEq _ _ _ _


-- @@ L90-91 verbatim
@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformulaᵢ L ξ n) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
  Iff.of_eq <| or.injEq _ _ _ _


-- @@ L93-94 verbatim
@[simp] lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformulaᵢ L ξ n} :
    φ₁ 🡒 φ₂ = ψ₁ 🡒 ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := Iff.of_eq <| imp.injEq _ _ _ _


-- @@ L96-97 verbatim
@[simp] lemma all_inj (φ ψ : Semiformulaᵢ L ξ (n + 1)) : ∀¹ φ = ∀¹ ψ ↔ φ = ψ := by
  simp [UnivQuantifier.all]


-- @@ L99-100 verbatim
@[simp] lemma exs_inj (φ ψ : Semiformulaᵢ L ξ (n + 1)) : ∃¹ φ = ∃¹ ψ ↔ φ = ψ := by
  simp [ExsQuantifier.exs]


-- @@ L102-103 verbatim
@[simp] lemma allClosure_inj (φ ψ : Semiformulaᵢ L ξ n) : ∀¹* φ = ∀¹* ψ ↔ φ = ψ := by
  induction n <;> simp [*, allClosure_succ]


-- @@ L105-106 verbatim
@[simp] lemma exsClosure_inj (φ ψ : Semiformulaᵢ L ξ n) : ∃¹* φ = ∃¹* ψ ↔ φ = ψ := by
  induction n <;> simp [*, exsClosure_succ]


-- @@ L108-109 verbatim
@[simp] lemma allItr_inj {k} (φ ψ : Semiformulaᵢ L ξ (n + k)) : ∀¹^[k] φ = ∀¹^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, allItr_succ]


-- @@ L111-112 verbatim
@[simp] lemma exsItr_inj {k} (φ ψ : Semiformulaᵢ L ξ (n + k)) : ∃¹^[k] φ = ∃¹^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, exsItr_succ]


-- @@ L114-121 verbatim
def complexity {n} : Semiformulaᵢ L ξ n → ℕ
|       ⊥ => 0
| rel _ _ => 0
|   φ ⋏ ψ => max φ.complexity ψ.complexity + 1
|   φ ⋎ ψ => max φ.complexity ψ.complexity + 1
|   φ 🡒 ψ => max φ.complexity ψ.complexity + 1
|    ∀¹ φ => φ.complexity + 1
|    ∃¹ φ => φ.complexity + 1


-- @@ L123-123 verbatim
@[simp] lemma complexity_top : complexity (⊤ : Semiformulaᵢ L ξ n) = 1 := rfl


-- @@ L125-125 verbatim
@[simp] lemma complexity_bot : complexity (⊥ : Semiformulaᵢ L ξ n) = 0 := rfl


-- @@ L127-127 verbatim
@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : complexity (rel r v) = 0 := rfl


-- @@ L129-129 verbatim
@[simp] lemma complexity_and (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L130-130 verbatim
@[simp] lemma complexity_and' (φ ψ : Semiformulaᵢ L ξ n) : complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L132-132 verbatim
@[simp] lemma complexity_or (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L133-133 verbatim
@[simp] lemma complexity_or' (φ ψ : Semiformulaᵢ L ξ n) : complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L135-135 verbatim
@[simp] lemma complexity_imp (φ ψ : Semiformulaᵢ L ξ n) : complexity (φ 🡒 ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L136-136 verbatim
@[simp] lemma complexity_imp' (φ ψ : Semiformulaᵢ L ξ n) : complexity (imp φ ψ) = max φ.complexity ψ.complexity + 1 := rfl


-- @@ L138-138 verbatim
@[simp] lemma complexity_all (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (∀¹ φ) = φ.complexity + 1 := rfl

-- @@ L139-139 verbatim
@[simp] lemma complexity_all' (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (all φ) = φ.complexity + 1 := rfl


-- @@ L141-141 verbatim
@[simp] lemma complexity_exs (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (∃¹ φ) = φ.complexity + 1 := rfl

-- @@ L142-142 verbatim
@[simp] lemma complexity_exs' (φ : Semiformulaᵢ L ξ (n + 1)) : complexity (exs φ) = φ.complexity + 1 := rfl


-- @@ L144-144 verbatim
@[simp] lemma complexity_neg (φ : Semiformulaᵢ L ξ n) : complexity (∼φ) = complexity φ + 1 := by simp [neg_def]


-- @@ L146-162 verbatim
@[elab_as_elim]
def cases' {C : ∀ n, Semiformulaᵢ L ξ n → Sort w}
  (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hAnd : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ ⋏ ψ))
  (hOr : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ ⋎ ψ))
  (hImp : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n (φ 🡒 ψ))
  (hAll : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C n (∀¹ φ))
  (hExs : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C n (∃¹ φ)) {n} :
    (φ : Semiformulaᵢ L ξ n) → C n φ
  | rel r v => hRel r v
  |       ⊥ => hFalsum
  |   φ ⋏ ψ => hAnd φ ψ
  |   φ ⋎ ψ => hOr φ ψ
  |   φ 🡒 ψ => hImp φ ψ
  |    ∀¹ φ => hAll φ
  |    ∃¹ φ => hExs φ


-- @@ L164-180 verbatim
@[elab_as_elim]
def rec' {C : ∀ n, Semiformulaᵢ L ξ n → Sort w}
  (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hAnd : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ ⋏ ψ))
  (hOr : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ ⋎ ψ))
  (hImp : ∀ {n : ℕ} (φ ψ : Semiformulaᵢ L ξ n), C n φ → C n ψ → C n (φ 🡒 ψ))
  (hAll : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C (n + 1) φ → C n (∀¹ φ))
  (hExs : ∀ {n : ℕ} (φ : Semiformulaᵢ L ξ (n + 1)), C (n + 1) φ → C n (∃¹ φ)) {n} :
    (φ : Semiformulaᵢ L ξ n) → C n φ
  | rel r v => hRel r v
  |       ⊥ => hFalsum
  |   φ ⋏ ψ => hAnd φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ) (rec' hRel hFalsum hAnd hOr hImp hAll hExs ψ)
  |   φ ⋎ ψ => hOr φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ) (rec' hRel hFalsum hAnd hOr hImp hAll hExs ψ)
  |   φ 🡒 ψ => hImp φ ψ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ) (rec' hRel hFalsum hAnd hOr hImp hAll hExs ψ)
  |    ∀¹ φ => hAll φ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ)
  |    ∃¹ φ => hExs φ (rec' hRel hFalsum hAnd hOr hImp hAll hExs φ)


-- @@ L182-182 verbatim
section Decidable


-- @@ L184-184 verbatim
variable [L.DecidableEq] [DecidableEq ξ]


-- @@ L186-230 verbatim
def hasDecEq {n} : (φ ψ : Semiformulaᵢ L ξ n) → Decidable (φ = ψ)
  | ⊥, ψ => by cases ψ using cases' <;>
      { simp only [reduceCtorEq]; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | rel r v, ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hRel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simpa [h] using Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp [h])
        · exact isFalse (by simp [e])
  | φ ⋏ ψ, χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hAnd φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | φ ⋎ ψ, χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hOr φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | φ 🡒 ψ, χ => by
      cases χ using cases' <;> try { simpa using isFalse not_false }
      case hImp φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp [hp, hq])
        | isFalse hp => isFalse (by simp [hp])
  | ∀¹ φ, ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hAll φ' => simpa using hasDecEq φ φ'
  | ∃¹ φ, ψ => by
      cases ψ using cases' <;> try { simpa using isFalse not_false }
      case hExs φ' => simpa using hasDecEq φ φ'


-- @@ L232-232 verbatim
instance : DecidableEq (Semiformulaᵢ L ξ n) := hasDecEq


-- @@ L234-234 verbatim
end Decidable


-- @@ L236-236 verbatim
end Semiformulaᵢ


-- @@ L238-238 verbatim
/-! ## (Weak) Negative formula -/


-- @@ L240-240 verbatim
namespace Semiformulaᵢ


-- @@ L242-246 verbatim
inductive IsNegative : Semiformulaᵢ L ξ n → Prop
  | falsum : IsNegative ⊥
  | and {φ ψ} : IsNegative φ → IsNegative ψ → IsNegative (φ ⋏ ψ)
  | imply {φ ψ} : IsNegative ψ → IsNegative (φ 🡒 ψ)
  | all {φ} : IsNegative φ → IsNegative (∀¹ φ)


-- @@ L248-248 verbatim
attribute [simp] IsNegative.falsum


-- @@ L250-250 verbatim
namespace IsNegative


-- @@ L252-253 verbatim
@[simp] lemma and_iff {φ ψ : Semiformulaᵢ L ξ n} : (φ ⋏ ψ).IsNegative ↔ φ.IsNegative ∧ ψ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro ⟨hφ, hψ⟩; exact .and hφ hψ⟩


-- @@ L255-256 verbatim
@[simp] lemma imp_iff {φ ψ : Semiformulaᵢ L ξ n} : (φ 🡒 ψ).IsNegative ↔ ψ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro h; exact .imply h⟩


-- @@ L258-259 verbatim
@[simp] lemma all_iff {φ : Semiformulaᵢ L ξ (n + 1)} : (∀¹ φ).IsNegative ↔ φ.IsNegative :=
  ⟨by rintro ⟨⟩; simp_all, by rintro h; exact .all h⟩


-- @@ L261-261 verbatim
@[simp] lemma verum : (⊤ : Semiformulaᵢ L ξ n).IsNegative := by simp [verum_def]


-- @@ L263-263 verbatim
@[simp] lemma not_or {φ ψ : Semiformulaᵢ L ξ n} : ¬(φ ⋎ ψ).IsNegative := by rintro ⟨⟩


-- @@ L265-265 verbatim
@[simp] lemma not_exs {φ : Semiformulaᵢ L ξ (n + 1)} : ¬(∃¹ φ).IsNegative := by rintro ⟨⟩


-- @@ L267-267 verbatim
@[simp] lemma not_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ¬(rel r v).IsNegative := by rintro ⟨⟩


-- @@ L269-269 verbatim
@[simp] lemma neg (φ : Semiformulaᵢ L ξ n) : (∼φ).IsNegative := .imply .falsum


-- @@ L271-271 verbatim
end IsNegative


-- @@ L273-273 verbatim
end Semiformulaᵢ



-- @@ L276-276 verbatim
end FFL.FirstOrder
