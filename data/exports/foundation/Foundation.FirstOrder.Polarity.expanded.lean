module

public import Foundation.FirstOrder.Basic


-- @@ L5-7 verbatim
/-!
# Polarity of formulas
-/


-- @@ L9-9 verbatim
@[expose] public section


-- @@ L11-11 verbatim
namespace FFL.FirstOrder.Semiformula


-- @@ L13-13 verbatim
variable {L : Language} {ξ : Type*}


-- @@ L15-24 verbatim
/-- A polarity of a formula -/
def polarity {n} : Semiformula L ξ n → Bool
  |  rel _ _ => true
  | nrel _ _ => false
  |        ⊤ => true
  |        ⊥ => false
  |    φ ⋏ ψ => polarity φ || polarity ψ
  |    φ ⋎ ψ => polarity φ && polarity ψ
  |     ∀¹ _ => false
  |     ∃¹ _ => true


-- @@ L26-26 verbatim
@[simp] lemma polarity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).polarity = true := rfl


-- @@ L28-28 verbatim
@[simp] lemma polarity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).polarity = false := rfl


-- @@ L30-30 verbatim
@[simp] lemma polarity_verum : (⊤ : Semiformula L ξ n).polarity = true := rfl


-- @@ L32-32 verbatim
@[simp] lemma polarity_falsum : (⊥ : Semiformula L ξ n).polarity = false := rfl


-- @@ L34-34 verbatim
@[simp] lemma polarity_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).polarity = (φ.polarity || ψ.polarity) := rfl


-- @@ L36-36 verbatim
@[simp] lemma polarity_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).polarity = (φ.polarity && ψ.polarity) := rfl


-- @@ L38-38 verbatim
@[simp] lemma polarity_all (φ : Semiformula L ξ (n + 1)) : (∀¹ φ).polarity = false := rfl


-- @@ L40-40 verbatim
@[simp] lemma polarity_ex (φ : Semiformula L ξ (n + 1)) : (∃¹ φ).polarity = true := rfl


-- @@ L42-43 verbatim
@[simp] lemma polarity_neg {n} (φ : Semiformula L ξ n) : (∼φ).polarity = !φ.polarity := by
  induction φ using rec' <;> simp [polarity, *]


-- @@ L45-46 verbatim
@[simp] lemma polarity_imply {n} (φ ψ : Semiformula L ξ n) : (φ 🡒 ψ).polarity = (!φ.polarity && ψ.polarity) := by
  simp [imp_eq]


-- @@ L48-48 verbatim
abbrev Positive (φ : Semiformula L ξ n) : Prop := φ.polarity = true


-- @@ L50-50 verbatim
abbrev Negative (φ : Semiformula L ξ n) : Prop := φ.polarity = false


-- @@ L52-52 verbatim
@[simp] lemma rel_positive {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Positive (rel r v) := rfl


-- @@ L54-54 verbatim
@[simp] lemma rel_negative {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ¬Negative (rel r v) := by simp [Negative]


-- @@ L56-56 verbatim
@[simp] lemma nrel_positive {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ¬Positive (nrel r v) := by simp [Positive]


-- @@ L58-58 verbatim
@[simp] lemma nrel_negative {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Negative (nrel r v) := rfl


-- @@ L60-60 verbatim
@[simp] lemma verum_positive : Positive (⊤ : Semiformula L ξ n) := rfl


-- @@ L62-62 verbatim
@[simp] lemma verum_negative : ¬Negative (⊤ : Semiformula L ξ n) := by simp [Negative]


-- @@ L64-64 verbatim
@[simp] lemma falsum_positive : ¬Positive (⊥ : Semiformula L ξ n) := by simp [Positive]


-- @@ L66-66 verbatim
@[simp] lemma falsum_negative : Negative (⊥ : Semiformula L ξ n) := rfl


-- @@ L68-70 verbatim
@[simp] lemma and_positive_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋏ ψ).Positive ↔ φ.Positive ∨ ψ.Positive := by
  simp [Positive]


-- @@ L72-74 verbatim
@[simp] lemma and_negative_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋏ ψ).Negative ↔ φ.Negative ∧ ψ.Negative := by
  simp [Negative]


-- @@ L76-78 verbatim
@[simp] lemma or_positive_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋎ ψ).Positive ↔ φ.Positive ∧ ψ.Positive := by
  simp [Positive]


-- @@ L80-82 verbatim
@[simp] lemma or_negative_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋎ ψ).Negative ↔ φ.Negative ∨ ψ.Negative := by
  simp [Negative]; grind


-- @@ L84-85 verbatim
@[simp] lemma ex_positive_iff {n} (φ : Semiformula L ξ (n + 1)) :
    (∃¹ φ).Positive := by simp [Positive]


-- @@ L87-88 verbatim
@[simp] lemma ex_negative_iff {n} (φ : Semiformula L ξ (n + 1)) :
    ¬(∃¹ φ).Negative := by simp [Negative]


-- @@ L90-91 verbatim
@[simp] lemma all_positive_iff {n} (φ : Semiformula L ξ (n + 1)) :
    ¬(∀¹ φ).Positive := by simp [Positive]


-- @@ L93-94 verbatim
@[simp] lemma all_negative_iff {n} (φ : Semiformula L ξ (n + 1)) :
    (∀¹ φ).Negative := by simp [Negative]


-- @@ L96-96 verbatim
@[simp] lemma neg_positive_iff {n} (φ : Semiformula L ξ n) : (∼φ).Positive ↔ φ.Negative := by simp [Positive, Negative]


-- @@ L98-102 verbatim
@[simp] lemma neg_negative_iff {n} (φ : Semiformula L ξ n) : (∼φ).Negative ↔ φ.Positive := by simp [Positive, Negative]

lemma Positive.eq_true {n} {φ : Semiformula L ξ n} (h : φ.Positive) : φ.polarity = true := h

lemma Negative.eq_false {n} {φ : Semiformula L ξ n} (h : φ.Negative) : φ.polarity = false := h


-- @@ L104-105 verbatim
@[simp] lemma polarity_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : (ω ▹ φ).polarity = φ.polarity := by
  induction φ using rec' <;> simp [polarity, *]


-- @@ L107-107 verbatim
end FFL.FirstOrder.Semiformula
