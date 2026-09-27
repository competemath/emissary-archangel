/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.MaximalConsistentSet
public import LeanPool.Incompleteness.Foundation.Modal.Complement
import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental
import Mathlib.Data.Finset.Powerset


-- @@ L13-13 verbatim
/-! # ComplementClosedConsistentFinset -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Modal


-- @@ L21-21 verbatim
open Entailment


-- @@ L23-23 verbatim
variable {α : Type*} [DecidableEq α]

-- @@ L24-24 verbatim
variable {S} [Entailment (Formula α) S]

-- @@ L25-25 verbatim
variable {𝓢 : S}


-- @@ L27-27 verbatim
namespace FormulaFinset


-- @@ L29-29 verbatim
variable {Φ Φ₁ Φ₂ : FormulaFinset α} {φ ψ : Formula α}


-- @@ L31-32 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Consistent (𝓢 : S) (Φ : FormulaFinset α) : Prop :=
  Unprovable 𝓢 Φ ⊥


-- @@ L34-35 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Inconsistent (𝓢 : S) (Φ : FormulaFinset α) : Prop := ¬(Consistent 𝓢 Φ)


-- @@ L37-39 verbatim
omit [DecidableEq α] in
lemma iff_theory_consistent_formulae_consistent {Φ : FormulaFinset α} :
    FormulaSet.Consistent 𝓢 Φ ↔ FormulaFinset.Consistent 𝓢 Φ := by simp_all


-- @@ L41-44 verbatim
omit [DecidableEq α] in
lemma iff_inconsistent_inconsistent {Φ : FormulaFinset α} :
    FormulaSet.Inconsistent 𝓢 Φ ↔ FormulaFinset.Inconsistent 𝓢 Φ := by
  simp_all


-- @@ L46-46 verbatim
section «lp_section_1»


-- @@ L48-48 verbatim
variable [Entailment.Classical 𝓢]


-- @@ L50-54 verbatim
omit [DecidableEq α] in
lemma empty_conisistent [Entailment.Consistent 𝓢] : FormulaFinset.Consistent 𝓢 ∅ := by
  classical
  rw [←iff_theory_consistent_formulae_consistent]
  simpa only [Finset.coe_empty] using FormulaSet.emptyset_consistent (𝓢 := 𝓢) (α := α)


-- @@ L56-60 expanded
lemma provable_iff_insert_neg_not_consistent :
    FormulaFinset.Inconsistent 𝓢 (insert (Tilde.tilde φ) Φ) ↔ Provable 𝓢 (↑Φ) φ := by
  classical convert FormulaSet.provable_iff_insert_neg_not_consistent (𝓢 := 𝓢) (T := ↑Φ) (φ := φ);
  simp;


-- @@ L62-66 expanded
lemma neg_provable_iff_insert_not_consistent :
    FormulaFinset.Inconsistent 𝓢 (insert (φ) Φ) ↔ Provable 𝓢 (↑Φ) (Tilde.tilde φ) := by
  classical convert FormulaSet.neg_provable_iff_insert_not_consistent (𝓢 := 𝓢) (T := ↑Φ) (φ := φ);
  simp;


-- @@ L68-72 expanded
omit [DecidableEq α] in
lemma unprovable_iff_singleton_neg_consistent :
    FormulaFinset.Consistent 𝓢 ({Tilde.tilde φ}) ↔ Unprovable 𝓢 φ := by
  classical convert FormulaSet.unprovable_iff_singleton_neg_consistent (𝓢 := 𝓢) (φ := φ); simp;


-- @@ L74-83 expanded
omit [DecidableEq α] in
lemma unprovable_iff_singleton_compl_consistent :
    FormulaFinset.Consistent 𝓢 ({-φ}) ↔ Unprovable 𝓢 φ := by
  classical
  rcases (Formula.complement.or φ) with (hp | ⟨ψ, rfl⟩);
  · rw [hp]; convert FormulaSet.unprovable_iff_singleton_neg_consistent (𝓢 := 𝓢) (φ := φ); simp;
  · simp only [Formula.complement];
    convert FormulaSet.unprovable_iff_singleton_consistent (𝓢 := 𝓢) (φ := ψ); simp;


-- @@ L85-92 expanded
omit [DecidableEq α] in
lemma provable_iff_singleton_compl_inconsistent :
    (FormulaFinset.Inconsistent 𝓢 ({-φ})) ↔ Provable 𝓢 φ := by
  classical
  constructor; · contrapose; apply unprovable_iff_singleton_compl_consistent.mpr;
  · contrapose; apply unprovable_iff_singleton_compl_consistent.mp;


-- @@ L94-98 expanded
lemma intro_union_consistent
    (h :
      ∀ {Γ₁ Γ₂ : List (Formula α)},
        (∀ φ ∈ Γ₁, φ ∈ P₁) ∧ (∀ φ ∈ Γ₂, φ ∈ P₂) →
          Unprovable 𝓢 (Arrow.arrow (Wedge.wedge (List.conj₂ Γ₁) (List.conj₂ Γ₂)) ⊥)) :
    FormulaFinset.Consistent 𝓢 (P₁ ∪ P₂) := by rw [← iff_theory_consistent_formulae_consistent];
  simpa using FormulaSet.intro_union_consistent h;


-- @@ L100-107 expanded
lemma intro_triunion_consistent
    (h :
      ∀ {Γ₁ Γ₂ Γ₃ : List (Formula α)},
        (∀ φ ∈ Γ₁, φ ∈ P₁) ∧ (∀ φ ∈ Γ₂, φ ∈ P₂) ∧ (∀ φ ∈ Γ₃, φ ∈ P₃) →
          Unprovable 𝓢
            (Arrow.arrow (Wedge.wedge (List.conj₂ Γ₁) (Wedge.wedge (List.conj₂ Γ₂) (List.conj₂ Γ₃)))
              ⊥)) :
    FormulaFinset.Consistent 𝓢 (P₁ ∪ P₂ ∪ P₃) := by
  rw [← iff_theory_consistent_formulae_consistent]; convert FormulaSet.intro_triunion_consistent h;
  ext; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, or_assoc]


-- @@ L109-109 verbatim
end «lp_section_1»



-- @@ L112-112 verbatim
namespace existsConsistentComplementaryClosed


-- @@ L114-117 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def next (𝓢 : S) (φ : Formula α) (Φ : FormulaFinset α) : FormulaFinset α :=
  open scoped Classical in
    if FormulaFinset.Consistent 𝓢 (insert φ Φ) then insert φ Φ else insert (-φ) Φ


-- @@ L119-122 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def enum (𝓢 : S) (Φ : FormulaFinset α) : (List (Formula α)) → FormulaFinset α
  | [] => Φ
  | ψ :: qs => next 𝓢 ψ (enum 𝓢 Φ qs)

-- @@ L123-123 verbatim
local notation:max t"[" l "]" => enum 𝓢 t l


-- @@ L125-141 expanded
lemma next_consistent [Entailment.Classical 𝓢] (Φ_consis : FormulaFinset.Consistent 𝓢 Φ)
    (φ : Formula α) : FormulaFinset.Consistent 𝓢 (next 𝓢 φ Φ) := by
  classical
  simp only [next]; split; · simpa;
  · rename_i h; by_contra hC;
    have h₁ : Provable 𝓢 (↑Φ) (Tilde.tilde φ) :=
      FormulaFinset.neg_provable_iff_insert_not_consistent (𝓢 := 𝓢) (Φ := Φ) (φ := φ) |>.mp h;
    have h₂ : Provable 𝓢 (↑Φ) (Tilde.tilde (-φ)) :=
      @FormulaFinset.neg_provable_iff_insert_not_consistent α _ (𝓢 := 𝓢) _ _ (Φ := Φ) (-φ) |>.mp <|
        by simp_all
    have : Provable 𝓢 ↑Φ ⊥ := neg_complement_derive_bot h₁ h₂; contradiction;


-- @@ L143-150 verbatim
lemma enum_consistent [Entailment.Classical 𝓢]
  (Φ_consis : Φ.Consistent 𝓢) {l : List (Formula α)} : FormulaFinset.Consistent 𝓢 (Φ[l]) := by
  induction l with
  | nil => exact Φ_consis;
  | cons ψ qs ih =>
    simp only [enum];
    apply next_consistent;
    exact ih;


-- @@ L152-152 verbatim
@[simp] lemma enum_nil {Φ : FormulaFinset α} : (Φ[[]]) = Φ := by simp [enum]


-- @@ L154-157 verbatim
lemma enum_subset_step {l : List (Formula α)} : (Φ[l]) ⊆ (Φ[(ψ :: l)]) := by
  classical
  simp [enum, next];
  split <;> simp;


-- @@ L159-162 verbatim
lemma enum_subset {l : List (Formula α)} : Φ ⊆ Φ[l] := by
  induction l with
  | nil => simp;
  | cons ψ qs ih => exact Set.Subset.trans ih <| by apply enum_subset_step;


-- @@ L164-176 expanded
lemma either {l : List (Formula α)} (hp : φ ∈ l) : φ ∈ Φ[l] ∨ -φ ∈ Φ[l] := by
  classical
    induction l with
  | nil => simp_all;
  | cons ψ qs ih =>
    simp only [List.mem_cons] at hp; simp only [enum, next]; rcases hp with (rfl | hp);
    · split <;> simp [Finset.mem_insert];
    ·
      split <;>
        { simp only [Finset.mem_insert]; rcases (ih hp) with (_ | _) <;> tauto;
        }


-- @@ L178-189 expanded
lemma subset {l : List (Formula α)} {φ : Formula α} (h : φ ∈ Φ[l]) :
    φ ∈ Φ ∨ φ ∈ l ∨ (∃ ψ ∈ l, -ψ = φ) := by
  classical
    induction l generalizing φ with
  | nil => simp_all;
  | cons ψ qs ih => simp_all only [enum, next, List.mem_cons, exists_eq_or_imp];
    split at h <;>
      · rcases Finset.mem_insert.mp h with (rfl | h)
        · tauto;
        · rcases ih h <;> tauto;


-- @@ L191-191 verbatim
end existsConsistentComplementaryClosed


-- @@ L193-215 expanded
open existsConsistentComplementaryClosed in
lemma existsConsistentComplementaryClosed [Entailment.Classical 𝓢] {S : FormulaFinset α}
    (h_sub : P ⊆ complementary S) (P_consis : FormulaFinset.Consistent 𝓢 P) :
    ∃ P', P ⊆ P' ∧ FormulaFinset.Consistent 𝓢 P' ∧ P'.ComplementaryClosed S :=
  by
  use existsConsistentComplementaryClosed.enum 𝓢 P S.toList; refine ⟨?_, ?_, ?_, ?_⟩;
  · apply enum_subset;
  · exact enum_consistent P_consis;
  · simp only [FormulaFinset.complementary]; intro φ hp;
    simp only [Finset.mem_union, Finset.mem_image]; rcases subset hp with (h | h | ⟨ψ, hq₁, hq₂⟩);
    · replace h := h_sub h; simp only [complementary, Finset.mem_union, Finset.mem_image] at h;
      simp_all
    · simp_all
    · right; use ψ; simp_all
  · intro φ hp; exact either (by simpa);


-- @@ L217-217 verbatim
end FormulaFinset



-- @@ L220-220 verbatim
section «lp_section_2»


-- @@ L222-222 verbatim
open Entailment

-- @@ L223-223 verbatim
open Formula (atom)

-- @@ L224-224 verbatim
open FormulaFinset


-- @@ L226-226 verbatim
variable {Φ Ψ : FormulaFinset α}


-- @@ L228-230 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ComplementClosedConsistentFinset (𝓢 : S) (Ψ : FormulaFinset α) := { T :
    FormulaFinset α // (Consistent 𝓢 T) ∧ (T.ComplementaryClosed Ψ)}


-- @@ L232-232 verbatim
namespace ComplementClosedConsistentFinset


-- @@ L234-234 verbatim
instance : Membership (Formula α) (ComplementClosedConsistentFinset 𝓢 Ψ) := ⟨fun X φ => φ ∈ X.1⟩


-- @@ L236-236 verbatim
lemma consistent (X : ComplementClosedConsistentFinset 𝓢 Ψ) : Consistent 𝓢 X := X.2.1


-- @@ L238-238 verbatim
lemma closed (X : ComplementClosedConsistentFinset 𝓢 Ψ) : ComplementaryClosed X Ψ := X.2.2


-- @@ L240-240 verbatim
variable {X X₁ X₂ : ComplementClosedConsistentFinset 𝓢 Ψ}


-- @@ L242-242 expanded
@[simp]
lemma unprovable_falsum : Unprovable 𝓢 X.1 ⊥ :=
  X.consistent


-- @@ L244-248 expanded
lemma mem_compl_of_not_mem (hs : ψ ∈ Ψ) : ψ ∉ X → -ψ ∈ X :=
  by
  intro h; rcases X.closed.either ψ (by assumption) with (h | h); · contradiction;
  · assumption;


-- @@ L250-250 expanded
lemma mem_of_not_mem_compl (hs : ψ ∈ Ψ) : -ψ ∉ X → ψ ∈ X :=
  Not.imp_symm (mem_compl_of_not_mem hs)


-- @@ L252-255 verbatim
lemma equality_def : X₁ = X₂ ↔ X₁.1 = X₂.1 := by
  constructor;
  · intro h; cases h; rfl;
  · intro h; cases X₁; cases X₂; simp_all;


-- @@ L257-257 verbatim
variable [Entailment.Classical 𝓢]


-- @@ L259-264 expanded
lemma lindenbaum {Φ Ψ : FormulaFinset α} (X_sub : Φ ⊆ complementary Ψ) (X_consis : Φ.Consistent 𝓢) :
    ∃ X' : ComplementClosedConsistentFinset 𝓢 Ψ, Φ ⊆ X'.1 := by
  obtain ⟨Y, ⟨_, _, _⟩⟩ := FormulaFinset.existsConsistentComplementaryClosed X_sub X_consis;
  use ⟨Y, (by assumption), (by assumption)⟩;


-- @@ L266-268 verbatim
noncomputable instance [Entailment.Consistent 𝓢] :
    Inhabited (ComplementClosedConsistentFinset 𝓢 Ψ) :=
  ⟨lindenbaum (Φ := ∅) (Ψ := Ψ) (by simp) (FormulaFinset.empty_conisistent) |>.choose⟩


-- @@ L270-281 expanded
lemma membership_iff (hq_sub : ψ ∈ Ψ) : (ψ ∈ X) ↔ (Provable 𝓢 X ψ) :=
  by
  constructor; · intro h; exact Context.by_axm! h;
  · intro hp;
    suffices -ψ ∉ X by
      rcases X.closed.either ψ hq_sub with hψ | hneg
      · exact hψ
      · exact False.elim (this hneg)
    by_contra hC; have hnp : Provable 𝓢 X (-ψ) := Context.by_axm! hC;
    have := complement_derive_bot hp hnp; simpa;


-- @@ L283-283 verbatim
lemma mem_verum (h : ⊤ ∈ Ψ) : ⊤ ∈ X := membership_iff h |>.mpr verum!


-- @@ L285-285 verbatim
@[simp] lemma mem_falsum : ⊥ ∉ X := FormulaSet.not_mem_falsum_of_consistent X.consistent


-- @@ L287-313 expanded
lemma iff_mem_compl (hq_sub : ψ ∈ Ψ) : (ψ ∈ X) ↔ (-ψ ∉ X) :=
  by
  constructor;
  · intro hq; replace hq := membership_iff hq_sub |>.mp hq; by_contra hnq;
    induction ψ using Formula.casesNeg with
    | hfalsum => exact unprovable_falsum hq;
    | hatom a => simp only [Formula.complement] at hnq;
      have : Provable 𝓢 (↑X) (Tilde.tilde (atom a)) := Context.by_axm! hnq;
      have : Provable 𝓢 ↑X ⊥ := complement_derive_bot hq this; simpa;
    | hbox ψ => simp only [Formula.complement] at hnq;
      have : Provable 𝓢 (↑X) (Tilde.tilde (Box.box ψ)) := Context.by_axm! hnq;
      have : Provable 𝓢 ↑X ⊥ := complement_derive_bot hq this; simpa;
    | hneg ψ => simp only [Formula.complement] at hnq;
      have : Provable 𝓢 (↑X) ψ := Context.by_axm! hnq;
      have : Provable 𝓢 ↑X ⊥ := complement_derive_bot hq this; simpa;
    | himp ψ χ h => simp only [Formula.complement.imp_def₁ h] at hnq;
      have : Provable 𝓢 (↑X) (Tilde.tilde (Arrow.arrow ψ χ)) := Context.by_axm! hnq;
      have : Provable 𝓢 ↑X ⊥ := mdp this hq; simpa;
  · intro h; exact mem_of_not_mem_compl (by assumption) h;


-- @@ L315-340 expanded
lemma iff_mem_imp (hsub_qr : (Arrow.arrow ψ χ) ∈ Ψ) (hsub_q : ψ ∈ Ψ := by trivial)
    (hsub_r : χ ∈ Ψ := by trivial) : ((Arrow.arrow ψ χ) ∈ X) ↔ (ψ ∈ X) → (-χ ∉ X) :=
  by
  constructor;
  · intro hqr hq; apply iff_mem_compl hsub_r |>.mp; replace hqr := membership_iff hsub_qr |>.mp hqr;
    replace hq := membership_iff hsub_q |>.mp hq; exact membership_iff hsub_r |>.mpr <| mdp hqr hq;
  · intro hqr; replace hqr := not_or_of_imp hqr
    rcases hqr with (hq | hr);
    · apply membership_iff hsub_qr |>.mpr; replace hq := mem_compl_of_not_mem hsub_q hq;
      induction ψ using Formula.casesNeg with
      | hfalsum => exact efq!;
      | hatom a => exact efq_of_neg! <| Context.by_axm! (by exact hq);
      | hbox ψ => exact efq_of_neg! <| Context.by_axm! (by exact hq);
      | hneg ψ => simp only [Formula.complement.neg_def] at hq;
        exact efq_of_neg₂! <| Context.by_axm! hq;
      | himp ψ χ h => simp only [Formula.complement.imp_def₁ h] at hq;
        exact efq_of_neg! <| Context.by_axm! (by exact hq);
    · apply membership_iff (by assumption) |>.mpr;
      exact
        imply₁'! <| membership_iff (by assumption) |>.mp <| iff_mem_compl (by assumption) |>.mpr hr;


-- @@ L342-345 expanded
lemma iff_not_mem_imp (hsub_qr : (Arrow.arrow ψ χ) ∈ Ψ) (hsub_q : ψ ∈ Ψ := by trivial)
    (hsub_r : χ ∈ Ψ := by trivial) : ((Arrow.arrow ψ χ) ∉ X) ↔ (ψ ∈ X) ∧ (-χ ∈ X) := by
  simpa using @iff_mem_imp α (𝓢 := 𝓢) _ _ _ Ψ X _ ψ χ hsub_qr hsub_q hsub_r |>.not;


-- @@ L347-354 expanded
instance : Finite (ComplementClosedConsistentFinset 𝓢 Ψ) :=
  by
  let f : ComplementClosedConsistentFinset 𝓢 Ψ → (Finset.powerset (complementary Ψ)) := fun X =>
    ⟨X, by simpa using X.closed.subset⟩
  have hf : Function.Injective f := by intro X₁ X₂ h; apply equality_def.mpr; simpa [f] using h;
  exact Finite.of_injective f hf;


-- @@ L356-356 verbatim
end ComplementClosedConsistentFinset


-- @@ L358-358 verbatim
end «lp_section_2»



-- @@ L361-361 verbatim
end Modal

-- @@ L362-362 verbatim
end LO
