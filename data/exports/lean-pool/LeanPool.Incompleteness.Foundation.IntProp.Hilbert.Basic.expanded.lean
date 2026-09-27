/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.IntProp.Substitution
public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Basic


-- @@ L11-11 verbatim
/-! # Basic -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace IntProp


-- @@ L19-19 verbatim
variable {α : Type u}


-- @@ L21-24 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Hilbert (α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  axioms : Set (Formula α)


-- @@ L26-26 verbatim
namespace Hilbert


-- @@ L28-30 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev axiomInstances (H : Hilbert α) : Set (Formula α) :=
  {Formula.subst s φ | (φ ∈ H.axioms) (s : Substitution α)}


-- @@ L32-34 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class FiniteAxiomatizable (H : Hilbert α) where
  axioms_fin : Set.Finite H.axioms := by simp


-- @@ L36-36 verbatim
variable {H : Hilbert α}


-- @@ L38-50 expanded
/-- Imported declaration from the Incompleteness formalization. -/
inductive Deduction (H : Hilbert α) : Formula α → Type _
  | maxm {φ} : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ} : Deduction H (Arrow.arrow φ ψ) → Deduction H φ → Deduction H ψ
  | verum : Deduction H <| ⊤
  | implyS φ ψ : Deduction H <| Arrow.arrow φ (Arrow.arrow ψ φ)
  |
  implyK φ ψ χ :
    Deduction H <|
      Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ))
        (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow φ χ))
  | andElimL φ ψ : Deduction H <| Arrow.arrow (Wedge.wedge φ ψ) φ
  | andElimR φ ψ : Deduction H <| Arrow.arrow (Wedge.wedge φ ψ) ψ
  | andIntro φ ψ : Deduction H <| Arrow.arrow φ (Arrow.arrow ψ (Wedge.wedge φ ψ))
  | orIntroL φ ψ : Deduction H <| Arrow.arrow φ (Vee.vee φ ψ)
  | orIntroR φ ψ : Deduction H <| Arrow.arrow ψ (Vee.vee φ ψ)
  |
  orElim φ ψ χ :
    Deduction H <|
      Arrow.arrow (Arrow.arrow φ χ) (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Vee.vee φ ψ) χ))


-- @@ L52-52 verbatim
instance : Entailment (Formula α) (Hilbert α) := ⟨Deduction⟩


-- @@ L54-54 verbatim
open Deduction

-- @@ L55-55 verbatim
open Hilbert


-- @@ L57-57 verbatim
section «lp_section_1»


-- @@ L59-59 verbatim
instance : Entailment.ModusPonens H := ⟨mdp⟩


-- @@ L61-61 verbatim
instance : Entailment.HasAxiomImply₁ H := ⟨implyS⟩


-- @@ L63-63 verbatim
instance : Entailment.HasAxiomImply₂ H := ⟨implyK⟩


-- @@ L65-65 verbatim
instance : Entailment.HasAxiomAndInst H := ⟨andIntro⟩


-- @@ L67-75 verbatim
instance : Entailment.Minimal H where
  mdp := mdp
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  and₃ := andIntro
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim


-- @@ L77-77 verbatim
namespace Deduction


-- @@ L79-79 expanded
lemma maxm! {φ} (h : φ ∈ H.axiomInstances) : Provable H φ :=
  ⟨maxm h⟩


-- @@ L81-81 verbatim
open Entailment


-- @@ L83-103 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def rec! {motive : (φ : Formula α) → Provable H φ → Sort*}
    (maxm : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
    (mdp :
      ∀ {φ ψ},
        {hpq : Provable H (Arrow.arrow φ ψ)} →
          {hp : Provable H φ} → motive (Arrow.arrow φ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
    (verum : motive ⊤ verum!) (implyS : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) <| ⟨implyS φ ψ⟩)
    (implyK : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) <| ⟨implyK φ ψ χ⟩)
    (andElimL : ∀ {φ ψ}, motive (Arrow.arrow (Wedge.wedge φ ψ) φ) <| ⟨andElimL φ ψ⟩)
    (andElimR : ∀ {φ ψ}, motive (Arrow.arrow (Wedge.wedge φ ψ) ψ) <| ⟨andElimR φ ψ⟩)
    (andIntro : ∀ {φ ψ}, motive (Arrow.arrow φ (Arrow.arrow ψ (Wedge.wedge φ ψ))) <| ⟨andIntro φ ψ⟩)
    (orIntroL : ∀ {φ ψ}, motive (Arrow.arrow φ (Vee.vee φ ψ)) <| ⟨orIntroL φ ψ⟩)
    (orIntroR : ∀ {φ ψ}, motive (Arrow.arrow ψ (Vee.vee φ ψ)) <| ⟨orIntroR φ ψ⟩)
    (orElim :
      ∀ {φ ψ χ},
        motive
            (Arrow.arrow (Arrow.arrow φ χ)
              (Arrow.arrow (Arrow.arrow ψ χ) (Arrow.arrow (Vee.vee φ ψ) χ))) <|
          ⟨orElim φ ψ χ⟩) :
    ∀ {φ}, (d : Provable H φ) → motive φ d := by intro φ d;
  induction d.some with
  | maxm h => exact maxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | _ => aesop


-- @@ L105-112 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma subst! {φ} (s) (h : Provable H φ) : Provable H (Formula.subst s φ) := by
  induction h using Deduction.rec! with
  | mdp ihφψ ihφ => exact mdp ihφψ ihφ;
  | maxm h => obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h; exact maxm! ⟨ψ, h, s' ∘ s, subst_comp⟩
  | _ => simp;


-- @@ L114-114 verbatim
end Deduction


-- @@ L116-116 verbatim
end «lp_section_1»




-- @@ L120-120 verbatim
section «lp_section_2»


-- @@ L122-122 verbatim
open Entailment


-- @@ L124-124 verbatim
variable {H₁ H₂ : Hilbert α}


-- @@ L126-134 expanded
lemma weakerThan_of_dominate_axiomInstances
    (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axiomInstances → Provable H₂ φ) : WeakerThan H₁ H₂ := by
  apply Entailment.weakerThan_iff.mpr; intro φ h;
  induction h using Deduction.rec! with
  | maxm hp => apply hMaxm hp;
  | mdp ihpq ihp => exact mdp ihpq ihp;
  | _ => simp;


-- @@ L136-139 expanded
lemma weakerThan_of_subset_axioms (hSubset : H₁.axioms ⊆ H₂.axioms) : WeakerThan H₁ H₂ := by
  apply weakerThan_of_dominate_axiomInstances; rintro φ ⟨ψ, hs, ⟨s, rfl⟩⟩;
  exact maxm! ⟨ψ, hSubset hs, s, rfl⟩


-- @@ L141-141 verbatim
end «lp_section_2»


-- @@ L143-143 verbatim
end Hilbert


-- @@ L145-145 verbatim
end IntProp

-- @@ L146-146 verbatim
end LO
