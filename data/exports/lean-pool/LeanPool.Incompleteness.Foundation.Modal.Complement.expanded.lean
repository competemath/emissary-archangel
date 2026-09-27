/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Subformulas


-- @@ L10-10 verbatim
/-! # Complement -/


-- @@ L12-12 verbatim
@[expose] public section




-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal



-- @@ L20-20 verbatim
namespace Formula


-- @@ L22-25 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def complement : Formula α → Formula α
  | Tilde.tilde φ => φ
  | φ => Tilde.tilde φ


-- @@ L26-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "-" => complement


-- @@ L29-29 verbatim
namespace complement


-- @@ L31-31 verbatim
variable {φ ψ : Formula α}


-- @@ L33-33 expanded
@[simp]
lemma neg_def : -(Tilde.tilde φ) = φ := by induction φ using Formula.rec' <;> simp_all [complement]


-- @@ L35-35 expanded
@[simp]
lemma bot_def : -(⊥ : Formula α) = Tilde.tilde (⊥) := by simp only [complement]


-- @@ L37-37 expanded
@[simp]
lemma box_def : -(Box.box φ) = Tilde.tilde (Box.box φ) := by simp only [complement]


-- @@ L39-43 expanded
lemma imp_def₁ (hq : ψ ≠ ⊥) : -(Arrow.arrow φ ψ) = Tilde.tilde (Arrow.arrow φ ψ) :=
  by
  simp only [complement]; split; · rename_i h; simp [imp_eq, falsum_eq, hq] at h;
  · rfl;


-- @@ L45-47 expanded
lemma imp_def₂ (hq : ψ = ⊥) : -(Arrow.arrow φ ψ) = φ := by subst_vars; apply neg_def;


-- @@ L49-53 expanded
lemma resort_box (h : -φ = Box.box ψ) : φ = Tilde.tilde (Box.box ψ) :=
  by
  simp [complement] at h; split at h; · subst_vars; rfl;
  · contradiction;


-- @@ L55-62 expanded
lemma or (φ : Formula α) : -φ = Tilde.tilde φ ∨ ∃ ψ, Tilde.tilde ψ = φ := by
  classical
    induction φ using Formula.casesNeg with
  | himp _ _ hn => simp [imp_def₁ hn];
  | hfalsum => simp;
  | hneg => simp;
  | hatom a => simp [complement];
  | hbox φ => simp [complement]


-- @@ L64-64 verbatim
end complement


-- @@ L66-66 verbatim
end Formula



-- @@ L69-69 verbatim
namespace FormulaFinset


-- @@ L71-71 verbatim
variable [DecidableEq α]


-- @@ L73-74 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def complementary (P : FormulaFinset α) : FormulaFinset α := P ∪ (P.image (Formula.complement))

-- @@ L75-76 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:80 "⁻" => complementary


-- @@ L78-78 verbatim
variable {P P₁ P₂ : FormulaFinset α} {φ ψ χ : Formula α}


-- @@ L80-80 expanded
lemma complementary_mem (h : φ ∈ P) : φ ∈ complementary P := by simp_all [complementary];


-- @@ L82-82 expanded
lemma complementary_comp (h : φ ∈ P) : -φ ∈ complementary P := by simp [complementary]; tauto;


-- @@ L84-84 expanded
lemma mem_of (h : φ ∈ complementary P) : φ ∈ P ∨ ∃ ψ ∈ P, -ψ = φ := by
  simpa [complementary] using h;


-- @@ L86-93 expanded
lemma complementary_mem_box (hi : ∀ {ψ χ}, Arrow.arrow ψ χ ∈ P → ψ ∈ P := by trivial) :
    Box.box φ ∈ complementary P → Box.box φ ∈ P :=
  by
  intro h; rcases (mem_of h) with (h | ⟨ψ, hq, eq⟩); · assumption;
  · replace eq := Formula.complement.resort_box eq; subst eq; exact hi hq;


-- @@ L96-99 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class ComplementaryClosed (P : FormulaFinset α) (S : FormulaFinset α) : Prop where
  subset : P ⊆ complementary S
  either : ∀ φ ∈ S, φ ∈ P ∨ -φ ∈ P


-- @@ L101-104 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def SubformulaeComplementaryClosed (P : FormulaFinset α) (φ : Formula α) :
    Prop :=
  P.ComplementaryClosed φ.subformulas


-- @@ L106-106 verbatim
end FormulaFinset



-- @@ L109-109 verbatim
section «lp_section_1»


-- @@ L111-111 verbatim
variable {α : Type*}

-- @@ L112-112 verbatim
variable {S} [Entailment (Formula α) S]

-- @@ L113-113 verbatim
variable {𝓢 : S} [Entailment.ModusPonens 𝓢]


-- @@ L115-121 expanded
lemma complement_derive_bot (hp : Provable 𝓢 φ) (hcp : Provable 𝓢 (-φ)) : Provable 𝓢 ⊥ := by
  classical
    induction φ using Formula.casesNeg with
  | hfalsum => assumption
  | hatom a
  | hbox φ => unfold Formula.complement at hcp; exact mdp hcp hp
  | hneg => unfold Formula.complement at hcp; exact mdp hp hcp
  | himp φ ψ h => simp only [Formula.complement.imp_def₁ h] at hcp; exact mdp hcp hp


-- @@ L123-128 expanded
lemma neg_complement_derive_bot (hp : Provable 𝓢 (Tilde.tilde φ))
    (hcp : Provable 𝓢 (Tilde.tilde (-φ))) : Provable 𝓢 ⊥ := by
  classical
    induction φ using Formula.casesNeg with
  | hfalsum
  | hatom a
  | hbox φ => unfold Formula.complement at hcp; exact mdp hcp hp
  | hneg => unfold Formula.complement at hcp; exact mdp hp hcp
  | himp φ ψ h => simp only [Formula.complement.imp_def₁ h] at hcp; exact mdp hcp hp


-- @@ L130-130 verbatim
end «lp_section_1»


-- @@ L132-132 verbatim
end Modal

-- @@ L133-133 verbatim
end LO
