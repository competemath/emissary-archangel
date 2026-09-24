module

public import Foundation.Propositional.Formula.Basic
public import Foundation.Logic.Semantics


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
namespace FFL.Propositional


-- @@ L10-10 verbatim
variable {α : Type*}


-- @@ L12-12 verbatim
abbrev Boolean.Valuation (α : Type*) := α → Prop


-- @@ L14-14 verbatim
namespace Formula.Boolean


-- @@ L16-16 verbatim
open Propositional.Boolean (Valuation)


-- @@ L18-23 expanded
def val (v : Valuation α) : Formula α → Prop
  | atom a => v a
  | ⊥ => False
  | binop% HArrow.hArrow φ ψ => val v φ → val v ψ
  | binop% HWedge.hWedge φ ψ => val v φ ∧ val v ψ
  | binop% HVee.hVee φ ψ => val v φ ∨ val v ψ


-- @@ L25-25 verbatim
variable {v : Valuation α} {φ ψ : Formula α}


-- @@ L27-27 verbatim
instance semantics : Semantics (Valuation α) (Formula α) := ⟨fun v ↦ val v⟩


-- @@ L29-29 expanded
lemma models_iff_val : Models v φ ↔ val v φ :=
  iff_of_eq rfl


-- @@ L31-37 verbatim
instance : Semantics.Tarski (Valuation α) where
  models_verum := by simp [models_iff_val, val]
  models_falsum := by simp [models_iff_val, val]
  models_and := by simp [models_iff_val, val]
  models_or  := by simp [models_iff_val, val]
  models_not := by simp [models_iff_val, val]
  models_imply := by simp [models_iff_val, val]


-- @@ L39-39 expanded
@[simp]
protected lemma models_atom : Models v (.atom a) ↔ v a :=
  iff_of_eq rfl


-- @@ L41-45 expanded
lemma eq_fml_of_eq_atom {v u : Valuation α} (h : ∀ {a : α}, v a ↔ u a) :
    (∀ {φ : Formula α}, Models v φ ↔ Models u φ) := by intro φ;
  induction φ with
  | hatom => apply h;
  | _ => simp [*]


-- @@ L47-81 expanded
lemma iff_subst_self (s) :
    Models ((λ a => val v (Formula.subst s (.atom a))) : Valuation α) φ ↔
      Models v (Formula.subst s φ) :=
  by
  induction φ with
  | hatom a => simp [val, models_iff_val];
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ =>
    constructor; · intro hφψ hφ; apply ihψ.mp; apply hφψ; apply ihφ.mpr; exact hφ;
    · intro hφψs hφ; apply ihψ.mpr; apply hφψs; apply ihφ.mp; exact hφ;
  | hand φ ψ ihφ ihψ =>
    constructor;
    · rintro ⟨hφ, hψ⟩; constructor; · apply ihφ.mp hφ;
      · apply ihψ.mp hψ;
    · rintro ⟨hφ, hψ⟩; constructor; · apply ihφ.mpr hφ;
      · apply ihψ.mpr hψ;
  | hor φ ψ ihφ ihψ =>
    constructor;
    · rintro (hφ | hψ); · left; apply ihφ.mp hφ;
      · right; apply ihψ.mp hψ;
    · rintro (hφ | hψ); · left; apply ihφ.mpr hφ;
      · right; apply ihψ.mpr hψ;


-- @@ L83-103 expanded
@[grind =>]
lemma equiv_of_letterless (hl : φ.Letterless) : ∀ v w : Valuation _, Models v φ ↔ Models w φ := by
  intro v w;
  induction φ with
  | hatom a => grind;
  | hfalsum => grind;
  | himp φ ψ ihφ ihψ => simp only [Formula.Letterless] at hl; replace ihφ := ihφ hl.1;
    replace ihψ := ihψ hl.2; simp_all;
  | hand φ ψ ihφ ihψ => simp only [Formula.Letterless] at hl; replace ihφ := ihφ hl.1;
    replace ihψ := ihψ hl.2; simp_all;
  | hor φ ψ ihφ ihψ => simp only [Formula.Letterless] at hl; replace ihφ := ihφ hl.1;
    replace ihψ := ihψ hl.2; simp_all;


-- @@ L105-105 verbatim
end Formula.Boolean




-- @@ L109-109 verbatim
namespace Formula


-- @@ L111-111 verbatim
open Semantics (Valid)

-- @@ L112-112 verbatim
open Formula (atom)

-- @@ L113-113 verbatim
open Formula.Boolean

-- @@ L114-114 verbatim
open _root_.FFL.Propositional.Boolean


-- @@ L116-116 verbatim
variable {v : Boolean.Valuation α} {φ ψ : Formula α}


-- @@ L118-118 verbatim
abbrev IsTautology (φ : Formula α) := Valid (Boolean.Valuation α) φ


-- @@ L120-124 expanded
@[grind <=]
lemma subst_isTautology (h : φ.IsTautology) : ∀ s, (Formula.subst s φ).IsTautology := by intro s v;
  apply Formula.Boolean.iff_subst_self s |>.mp; apply h;


-- @@ L126-136 expanded
@[grind =]
lemma iff_and_isTautology :
    (binop% HWedge.hWedge φ ψ).IsTautology ↔ (φ.IsTautology) ∧ (ψ.IsTautology) :=
  by
  constructor;
  · intro h; constructor; · intro v; exact h v |>.1;
    · intro v; exact h v |>.2;
  · rintro ⟨hφ, hψ⟩ v; have := hφ v; have := hψ v; tauto;


-- @@ L138-142 expanded
@[grind <=]
lemma or_isTautology_of : φ.IsTautology ∨ ψ.IsTautology → (binop% HVee.hVee φ ψ).IsTautology :=
  by
  rintro (hφ | hψ) v; · left; exact hφ v;
  · right; exact hψ v;


-- @@ L144-147 expanded
@[grind <=]
lemma imp_isTautology_of : (ψ.IsTautology) → (binop% HArrow.hArrow φ ψ).IsTautology := by
  intro hψ v h; apply hψ;


-- @@ L148-148 verbatim
alias tautology_afortiori := imp_isTautology_of


-- @@ L150-154 verbatim
@[simp, grind .]
lemma not_bot_isTautology : ¬((⊥ : Formula α).IsTautology) := by
  intro h;
  have := @h (λ _ => True);
  simp at this;


-- @@ L156-157 verbatim
@[simp, grind .]
lemma top_isTautology : (⊤ : Formula α).IsTautology := by intro v; simp;


-- @@ L159-165 expanded
@[grind =>]
lemma tautology_of_letterless_of_not_neg_isTautology (hl : φ.Letterless) :
    ¬((unop% HTilde.hTilde φ).IsTautology) → φ.IsTautology :=
  by
  intro h v;
  obtain ⟨w, hw⟩ : ∃ x : Boolean.Valuation _, Models x φ := by simpa [IsTautology, Valid] using h;
  have H := Formula.Boolean.equiv_of_letterless hl; apply H w v |>.mp; assumption;


-- @@ L167-170 expanded
@[grind =>]
lemma neg_isTautology_of_letterless_of_isTautology (hl : φ.Letterless) :
    ¬φ.IsTautology → (unop% HTilde.hTilde φ).IsTautology := by contrapose!;
  apply tautology_of_letterless_of_not_neg_isTautology hl;


-- @@ L172-172 verbatim
end Formula



-- @@ L175-175 verbatim
end FFL.Propositional

-- @@ L176-176 verbatim
end
