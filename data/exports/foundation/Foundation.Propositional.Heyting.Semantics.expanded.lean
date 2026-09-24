module

public import Foundation.Propositional.Hilbert.Basic
public import Foundation.Logic.LindenbaumAlgebra
public import Foundation.Vorspiel.Order.Heyting


-- @@ L7-7 verbatim
@[expose] public section


-- @@ L9-9 verbatim
namespace FFL.Propositional


-- @@ L11-11 verbatim
variable {α : Type u}


-- @@ L13-13 verbatim
namespace Formula


-- @@ L15-20 expanded
def hVal {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ) : Formula α → ℍ
  | atom a => v a
  | ⊥ => ⊥
  | binop% HWedge.hWedge φ ψ => φ.hVal v ⊓ ψ.hVal v
  | binop% HVee.hVee φ ψ => φ.hVal v ⊔ ψ.hVal v
  | binop% HArrow.hArrow φ ψ => φ.hVal v ⇨ ψ.hVal v


-- @@ L22-22 verbatim
variable {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ)


-- @@ L24-24 verbatim
@[simp] lemma hVal_atom (a : α) : (atom a).hVal v = v a := rfl


-- @@ L26-26 verbatim
@[simp] lemma hVal_falsum : (⊥ : Formula α).hVal v = ⊥ := rfl


-- @@ L28-28 expanded
@[simp]
lemma hVal_and (φ ψ : Formula α) : (binop% HWedge.hWedge φ ψ).hVal v = φ.hVal v ⊓ ψ.hVal v :=
  rfl


-- @@ L30-30 expanded
@[simp]
lemma hVal_or (φ ψ : Formula α) : (binop% HVee.hVee φ ψ).hVal v = φ.hVal v ⊔ ψ.hVal v :=
  rfl


-- @@ L32-32 expanded
@[simp]
lemma hVal_imp (φ ψ : Formula α) : (binop% HArrow.hArrow φ ψ).hVal v = φ.hVal v ⇨ ψ.hVal v :=
  rfl


-- @@ L34-34 verbatim
@[simp] lemma hVal_verum : (⊤ : Formula α).hVal v = ⊤ := by simp [Formula.top_def];


-- @@ L36-36 expanded
@[simp]
lemma hVal_neg (φ : Formula α) : (unop% HTilde.hTilde φ).hVal v = (φ.hVal v)ᶜ := by
  simp [Formula.neg_def];


-- @@ L38-38 verbatim
end Formula


-- @@ L40-44 verbatim
structure HeytingSemantics (α : Type*) where
  Algebra : Type*
  valAtom : α → Algebra
  [heyting : HeytingAlgebra Algebra]
  [nontrivial : Nontrivial Algebra]


-- @@ L46-46 verbatim
namespace HeytingSemantics


-- @@ L48-48 verbatim
variable (ℍ : HeytingSemantics α)


-- @@ L50-50 verbatim
instance : CoeSort (HeytingSemantics α) (Type _) := ⟨Algebra⟩


-- @@ L52-52 verbatim
instance : HeytingAlgebra ℍ := ℍ.heyting


-- @@ L54-54 verbatim
instance : Nontrivial ℍ := ℍ.nontrivial


-- @@ L56-56 verbatim
def hVal (ℍ : HeytingSemantics α) (φ : Formula α) : ℍ := φ.hVal ℍ.valAtom


-- @@ L58-58 verbatim
scoped [FFL.Propositional] infix:45 " ⊧ₕ " => FFL.Propositional.HeytingSemantics.hVal


-- @@ L60-60 verbatim
@[simp] lemma hVal_falsum : (ℍ ⊧ₕ ⊥) = ⊥ := rfl


-- @@ L62-62 expanded
@[simp]
lemma hVal_and (φ ψ : Formula α) : (ℍ ⊧ₕ binop% HWedge.hWedge φ ψ) = (ℍ ⊧ₕ φ) ⊓ (ℍ ⊧ₕ ψ) :=
  rfl


-- @@ L64-64 expanded
@[simp]
lemma hVal_or (φ ψ : Formula α) : (ℍ ⊧ₕ binop% HVee.hVee φ ψ) = (ℍ ⊧ₕ φ) ⊔ (ℍ ⊧ₕ ψ) :=
  rfl


-- @@ L66-66 expanded
@[simp]
lemma hVal_imply (φ ψ : Formula α) : (ℍ ⊧ₕ binop% HArrow.hArrow φ ψ) = (ℍ ⊧ₕ φ) ⇨ (ℍ ⊧ₕ ψ) :=
  rfl


-- @@ L68-68 expanded
@[simp]
lemma hVal_iff (φ ψ : Formula α) : (ℍ ⊧ₕ LogicalConnective.iff φ ψ) = bihimp (ℍ ⊧ₕ φ) (ℍ ⊧ₕ ψ) := by
  simp [LogicalConnective.iff, bihimp, inf_comm]


-- @@ L70-70 verbatim
@[simp] lemma hVal_verum : (ℍ ⊧ₕ ⊤) = ⊤ := by simp [Formula.top_def];


-- @@ L72-72 expanded
@[simp]
lemma hVal_not (φ : Formula α) : (ℍ ⊧ₕ unop% HTilde.hTilde φ) = (ℍ ⊧ₕ φ)ᶜ := by
  simp [Formula.neg_def];


-- @@ L74-74 verbatim
instance : Semantics (HeytingSemantics α) (Formula α) := ⟨fun ℍ φ ↦ (ℍ ⊧ₕ φ) = ⊤⟩


-- @@ L76-76 expanded
lemma val_def {ℍ : HeytingSemantics α} {φ : Formula α} : Models ℍ φ ↔ φ.hVal ℍ.valAtom = ⊤ := by rfl


-- @@ L78-78 expanded
lemma val_def' {ℍ : HeytingSemantics α} {φ : Formula α} : Models ℍ φ ↔ (ℍ ⊧ₕ φ) = ⊤ := by rfl


-- @@ L80-80 verbatim
instance : Semantics.Top (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩


-- @@ L82-82 verbatim
instance : Semantics.Bot (HeytingSemantics α) := ⟨fun ℍ ↦ by simp [val_def]⟩


-- @@ L84-84 verbatim
instance : Semantics.And (HeytingSemantics α) := ⟨fun {ℍ φ ψ} ↦ by simp [val_def]⟩


-- @@ L86-87 expanded
@[simp]
lemma val_imply {φ ψ : Formula α} : Models ℍ binop% HArrow.hArrow φ ψ ↔ (ℍ ⊧ₕ φ) ≤ (ℍ ⊧ₕ ψ) := by
  simp [val_def]; rfl


-- @@ L89-90 expanded
@[simp]
lemma val_iff {φ ψ : Formula α} : Models ℍ (LogicalConnective.iff φ ψ) ↔ (ℍ ⊧ₕ φ) = (ℍ ⊧ₕ ψ) := by
  simp [LogicalConnective.iff, antisymm_iff]


-- @@ L92-95 expanded
lemma val_not (φ : Formula α) : Models ℍ unop% HTilde.hTilde φ ↔ (ℍ ⊧ₕ φ) = ⊥ := by
  simp only [val_def, Formula.hVal_neg];
  rw [← HeytingAlgebra.himp_bot, himp_eq_top_iff, le_bot_iff]; rfl


-- @@ L97-98 expanded
@[simp]
lemma val_or (φ ψ : Formula α) : Models ℍ binop% HVee.hVee φ ψ ↔ (ℍ ⊧ₕ φ) ⊔ (ℍ ⊧ₕ ψ) = ⊤ := by
  simp [val_def]; rfl


-- @@ L100-100 verbatim
def mod (H : Hilbert α) : Set (HeytingSemantics α) := Semantics.models (HeytingSemantics α) H


-- @@ L102-102 verbatim
variable {H : Hilbert α}


-- @@ L104-106 expanded
lemma mod_models_iff {φ : Formula α} :
    Models (mod.{_, w} H) φ ↔ ∀ ℍ : HeytingSemantics.{_, w} α, ModelsSet ℍ H → Models ℍ φ := by
  simp [mod, Semantics.models, Semantics.set_models_iff]


-- @@ L108-117 expanded
lemma sound {φ : Formula α} : Provable H φ → Models (mod H) φ := by rintro ⟨d⟩;
  apply mod_models_iff.mpr; intro ℍ hℍ;
  induction d with
  | axm hφ => apply hℍ.models_set; assumption;
  | @mdp φ ψ _ _ ihpq ihp =>
    have : (ℍ ⊧ₕ φ) ≤ (ℍ ⊧ₕ ψ) := by simpa using ihpq
    apply val_def'.mpr; simpa [val_def'.mp ihp] using this
  | _ => simp [himp_himp_inf_himp_inf_le, himp_inf_himp_inf_sup_le]


-- @@ L119-119 verbatim
instance : Sound H (mod H) := ⟨sound⟩


-- @@ L121-121 verbatim
section


-- @@ L123-123 verbatim
open Entailment.LindenbaumAlgebra


-- @@ L125-125 verbatim
variable [DecidableEq α] {H : Hilbert α} [Entailment.Consistent H] [Entailment.Int H]


-- @@ L127-130 verbatim
def lindenbaum (H : Hilbert α) [Entailment.Consistent H] [Entailment.Int H] : HeytingSemantics α where
  Algebra := Entailment.LindenbaumAlgebra H
  valAtom a := ⟦.atom a⟧
  heyting := Entailment.LindenbaumAlgebra.heyting _


-- @@ L132-137 verbatim
lemma lindenbaum_val_eq : (lindenbaum H ⊧ₕ φ) = ⟦φ⟧ := by
  induction φ with
  | hand φ ψ ihp ihq => simp_all [hVal_and]; rfl;
  | hor _ _ ihp ihq => simp_all [hVal_or]; tauto;
  | himp _ _ ihp ihq => simp_all [hVal_imply]; tauto;
  | _ => rfl


-- @@ L139-141 expanded
lemma lindenbaum_complete_iff {φ : Formula α} : Models (lindenbaum H) φ ↔ Provable H φ :=
  by
  rw [val_def', lindenbaum_val_eq]
  exact provable_iff_eq_top.symm


-- @@ L143-143 verbatim
instance : Sound H (lindenbaum H) := ⟨lindenbaum_complete_iff.mpr⟩


-- @@ L145-145 verbatim
instance : Complete H (lindenbaum H) := ⟨lindenbaum_complete_iff.mp⟩


-- @@ L147-147 verbatim
end


-- @@ L149-155 expanded
lemma complete [DecidableEq α] [Entailment.Int H] {φ : Formula α} (h : Models (mod.{_, u} H) φ) :
    Provable H φ := by
  wlog Con : Entailment.Consistent H
  · exact Entailment.not_consistent_iff_inconsistent.mp Con φ
  exact
    lindenbaum_complete_iff.mp <|
      mod_models_iff.mp h (lindenbaum H) $ by constructor; intro ψ hψ;
        exact lindenbaum_complete_iff.mpr $ Hilbert.of_schema hψ;


-- @@ L157-157 verbatim
instance [DecidableEq α] [Entailment.Int H] : Complete H (mod.{_,u} H) := ⟨complete⟩


-- @@ L159-159 verbatim
end HeytingSemantics


-- @@ L161-161 verbatim
end FFL.Propositional

-- @@ L162-162 verbatim
end
