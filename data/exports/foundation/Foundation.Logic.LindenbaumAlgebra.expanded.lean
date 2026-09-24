module

public import Foundation.Propositional.Entailment.Cl
public import Mathlib.Data.Countable.Defs


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
namespace FFL


-- @@ L10-10 verbatim
variable {F S : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]


-- @@ L12-12 verbatim
namespace Entailment


-- @@ L14-14 verbatim
variable (𝓢 : S)


-- @@ L16-16 expanded
def ProvablyEquivalent (φ ψ : F) : Prop :=
  Provable 𝓢 (LogicalConnective.iff φ ψ)


-- @@ L18-18 verbatim
local infix:45 " ≡ " => ProvablyEquivalent 𝓢


-- @@ L20-20 verbatim
protected lemma ProvablyEquivalent.refl [Entailment.Minimal 𝓢] (φ : F) : φ ≡ φ := E_id


-- @@ L22-22 verbatim
variable {𝓢}


-- @@ L24-24 verbatim
protected lemma ProvablyEquivalent.symm [Entailment.Minimal 𝓢] {φ ψ : F} : φ ≡ ψ → ψ ≡ φ := E_symm


-- @@ L26-26 verbatim
protected lemma ProvablyEquivalent.trans [Entailment.Minimal 𝓢] {φ ψ χ : F} : φ ≡ ψ → ψ ≡ χ → φ ≡ χ := E_trans


-- @@ L28-29 expanded
lemma provable_iff_provablyEquivalent_verum [Entailment.Minimal 𝓢] {φ : F} : Provable 𝓢 φ ↔ φ ≡ ⊤ :=
  ⟨fun h ↦ E_intro CV (C_of_conseq h), fun h ↦ mdp! (K_right h) verum⟩


-- @@ L31-31 verbatim
variable (𝓢)


-- @@ L33-35 verbatim
def ProvablyEquivalent.setoid [Entailment.Minimal 𝓢] : Setoid F where
  r := (· ≡ ·)
  iseqv := { refl := .refl _, symm := .symm, trans := .trans }


-- @@ L37-37 verbatim
abbrev LindenbaumAlgebra [Entailment.Minimal 𝓢] := Quotient (ProvablyEquivalent.setoid 𝓢)


-- @@ L39-39 verbatim
namespace LindenbaumAlgebra


-- @@ L41-41 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L43-43 verbatim
lemma of_eq_of {φ ψ : F} : (⟦φ⟧ : LindenbaumAlgebra 𝓢) = ⟦ψ⟧ ↔ φ ≡ ψ := Quotient.eq (r := ProvablyEquivalent.setoid 𝓢)


-- @@ L45-46 expanded
instance [DecidableEq F] : LE (LindenbaumAlgebra 𝓢) :=
  ⟨Quotient.lift₂ (fun φ ψ ↦ Provable 𝓢 binop% HArrow.hArrow φ ψ) fun φ₁ ψ₁ φ₂ ψ₂ hp hq ↦ by
      simp only [C_iff_C_of_E_of_E hp hq]⟩


-- @@ L48-48 expanded
lemma le_def [DecidableEq F] {φ ψ : F} :
    (⟦φ⟧ : LindenbaumAlgebra 𝓢) ≤ ⟦ψ⟧ ↔ Provable 𝓢 binop% HArrow.hArrow φ ψ :=
  iff_of_eq rfl


-- @@ L50-50 verbatim
instance : Top (LindenbaumAlgebra 𝓢) := ⟨⟦⊤⟧⟩


-- @@ L52-52 verbatim
instance : Bot (LindenbaumAlgebra 𝓢) := ⟨⟦⊥⟧⟩


-- @@ L54-55 expanded
instance [DecidableEq F] : Min (LindenbaumAlgebra 𝓢) :=
  ⟨Quotient.lift₂ (fun φ ψ ↦ ⟦binop% HWedge.hWedge φ ψ⟧) fun φ₁ ψ₁ φ₂ ψ₂ hp hq ↦ by
      simp only [Quotient.eq]; exact EKK_of_E_of_E hp hq⟩


-- @@ L57-58 expanded
instance [DecidableEq F] : Max (LindenbaumAlgebra 𝓢) :=
  ⟨Quotient.lift₂ (fun φ ψ ↦ ⟦binop% HVee.hVee φ ψ⟧) fun φ₁ ψ₁ φ₂ ψ₂ hp hq ↦ by
      simp only [Quotient.eq]; exact EAA_of_E_of_E hp hq⟩


-- @@ L60-61 expanded
instance [DecidableEq F] : HImp (LindenbaumAlgebra 𝓢) :=
  ⟨Quotient.lift₂ (fun φ ψ ↦ ⟦binop% HArrow.hArrow φ ψ⟧) fun φ₁ ψ₁ φ₂ ψ₂ hp hq ↦ by
      simp only [Quotient.eq]; exact ECC_of_E_of_E hp hq⟩


-- @@ L63-64 expanded
instance [DecidableEq F] : Compl (LindenbaumAlgebra 𝓢) :=
  ⟨Quotient.lift (fun φ ↦ ⟦unop% HTilde.hTilde φ⟧) fun φ₁ φ₂ hp ↦ by simp only [Quotient.eq];
      exact ENN_of_E hp⟩


-- @@ L66-66 verbatim
lemma top_def : (⊤ : LindenbaumAlgebra 𝓢) = ⟦⊤⟧ := rfl


-- @@ L68-68 verbatim
lemma bot_def : (⊥ : LindenbaumAlgebra 𝓢) = ⟦⊥⟧ := rfl


-- @@ L70-70 expanded
lemma inf_def [DecidableEq F] (φ ψ : F) :
    (⟦φ⟧ : LindenbaumAlgebra 𝓢) ⊓ ⟦ψ⟧ = ⟦binop% HWedge.hWedge φ ψ⟧ :=
  rfl


-- @@ L72-72 expanded
lemma sup_def [DecidableEq F] (φ ψ : F) :
    (⟦φ⟧ : LindenbaumAlgebra 𝓢) ⊔ ⟦ψ⟧ = ⟦binop% HVee.hVee φ ψ⟧ :=
  rfl


-- @@ L74-74 expanded
lemma himp_def [DecidableEq F] (φ ψ : F) :
    (⟦φ⟧ : LindenbaumAlgebra 𝓢) ⇨ ⟦ψ⟧ = ⟦binop% HArrow.hArrow φ ψ⟧ :=
  rfl


-- @@ L76-76 expanded
lemma compl_def [DecidableEq F] (φ : F) : (⟦φ⟧ : LindenbaumAlgebra 𝓢)ᶜ = ⟦unop% HTilde.hTilde φ⟧ :=
  rfl


-- @@ L78-136 verbatim
instance [DecidableEq F] : GeneralizedHeytingAlgebra (LindenbaumAlgebra 𝓢) where
  sup := Max.max
  inf := Min.min
  le_refl φ := by
    induction' φ using Quotient.ind with φ
    simp [le_def]
  le_trans φ ψ χ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    induction' χ using Quotient.ind with χ
    simp only [le_def]
    exact C_trans
  le_antisymm φ ψ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    simp only [le_def, of_eq_of]
    intro hp hq; exact E_intro hp hq
  inf_le_left φ ψ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    simp only [inf_def, le_def]
    exact and₁
  inf_le_right φ ψ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    simp only [inf_def, le_def]
    exact and₂
  le_inf φ ψ χ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    induction' χ using Quotient.ind with χ
    simp only [inf_def, le_def]
    exact right_K_intro
  le_sup_left φ ψ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    simp only [sup_def, le_def]
    exact or₁
  le_sup_right φ ψ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    simp only [sup_def, le_def]
    exact or₂
  sup_le φ ψ χ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    induction' χ using Quotient.ind with χ
    simp only [sup_def, le_def]
    exact left_A_intro
  le_top φ := by
    induction' φ using Quotient.ind with φ
    simp only [top_def, le_def]
    exact CV
  le_himp_iff φ ψ χ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    induction' χ using Quotient.ind with χ
    simp only [himp_def, le_def, inf_def]
    exact Iff.symm CK_iff_CC


-- @@ L138-138 verbatim
variable {𝓢}


-- @@ L140-142 expanded
lemma provable_iff_eq_top {φ : F} : Provable 𝓢 φ ↔ (⟦φ⟧ : LindenbaumAlgebra 𝓢) = ⊤ :=
  calc
    _ ↔ ProvablyEquivalent 𝓢 φ ⊤ := by rw [provable_iff_provablyEquivalent_verum]
    _ ↔ _ := by rw [top_def, Quotient.eq]; rfl;


-- @@ L144-150 verbatim
lemma inconsistent_iff_trivial : Inconsistent 𝓢 ↔ (∀ φ : LindenbaumAlgebra 𝓢, φ = ⊤) := by
  simp only [Inconsistent, provable_iff_eq_top]
  constructor
  · intro h φ;
    induction φ using Quotient.ind
    simp [h]
  · intro h f; simp [h]


-- @@ L152-157 verbatim
lemma consistent_iff_nontrivial : Consistent 𝓢 ↔ Nontrivial (LindenbaumAlgebra 𝓢) := by
  apply not_iff_not.mp
  simp only [not_consistent_iff_inconsistent, inconsistent_iff_trivial, nontrivial_iff, ne_eq, not_exists, not_not]
  constructor
  · intro h φ ψ; simp [h]
  · intro h φ; exact h φ ⊤


-- @@ L159-159 verbatim
instance nontrivial_of_consistent [Consistent 𝓢] : Nontrivial (LindenbaumAlgebra 𝓢) := consistent_iff_nontrivial.mp inferInstance


-- @@ L161-161 verbatim
instance [Countable F] : Countable (LindenbaumAlgebra 𝓢) := Quotient.countable


-- @@ L163-163 verbatim
end LindenbaumAlgebra


-- @@ L165-165 verbatim
section intuitionistic


-- @@ L167-167 verbatim
open LindenbaumAlgebra


-- @@ L169-169 verbatim
variable [Entailment.Int 𝓢]


-- @@ L171-179 expanded
instance LindenbaumAlgebra.heyting [DecidableEq F] : HeytingAlgebra (LindenbaumAlgebra 𝓢)
    where
  bot_le
    φ := by
    induction' φ using Quotient.ind with φ
    simp only [bot_def, le_def]
    exact efq
  himp_bot
    φ := by
    induction' φ using Quotient.ind with φ
    simp only [bot_def, himp_def, compl_def, Quotient.eq]
    exact mdp! CEE neg_equiv


-- @@ L181-181 verbatim
end intuitionistic


-- @@ L183-183 verbatim
section classical


-- @@ L185-185 verbatim
open LindenbaumAlgebra


-- @@ L187-187 verbatim
variable [Entailment.Cl 𝓢]


-- @@ L189-210 verbatim
instance LindenbaumAlgebra.boolean [DecidableEq F] : BooleanAlgebra (LindenbaumAlgebra 𝓢) where
  inf_compl_le_bot φ := by
    induction' φ using Quotient.ind with φ
    simp only [compl_def, inf_def, bot_def, le_def, CKNO]
  top_le_sup_compl φ := by
    induction' φ using Quotient.ind with φ
    simp only [top_def, compl_def, sup_def, le_def]
    apply C_of_conseq lem
  le_top φ := by
    induction' φ using Quotient.ind with φ
    simp only [top_def, le_def]
    exact CV
  bot_le φ := by
    induction' φ using Quotient.ind with φ
    simp only [bot_def, le_def]
    exact efq
  himp_eq φ ψ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    rw [sup_comm]
    simp only [himp_def, compl_def, sup_def, Quotient.eq]
    exact ECAN


-- @@ L212-212 verbatim
end classical


-- @@ L214-214 verbatim
end Entailment


-- @@ L216-216 verbatim
end FFL


-- @@ L218-218 verbatim
end
