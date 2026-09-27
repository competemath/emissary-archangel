/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Formula
public import LeanPool.Incompleteness.Foundation.Modal.Entailment.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import LeanPool.Incompleteness.Foundation.Modal.Entailment.K
import Mathlib.Order.Zorn
import Mathlib.Tactic.TautoSet


-- @@ L15-15 verbatim
/-! # MaximalConsistentSet -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
namespace LO

-- @@ L21-21 verbatim
namespace Modal


-- @@ L23-23 verbatim
open Entailment


-- @@ L25-25 verbatim
variable {α : Type*}

-- @@ L26-26 verbatim
variable {S} [Entailment (Formula α) S]

-- @@ L27-27 verbatim
variable {𝓢 : S}


-- @@ L29-29 verbatim
namespace FormulaSet


-- @@ L31-31 verbatim
variable {T : FormulaSet α}


-- @@ L33-34 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Consistent (𝓢 : S) (T : FormulaSet α) :=
  Unprovable 𝓢 T ⊥


-- @@ L36-37 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Inconsistent (𝓢 : S) (T : FormulaSet α) := ¬(Consistent 𝓢 T)


-- @@ L39-44 expanded
lemma def_consistent : Consistent 𝓢 T ↔ ∀ Γ, (∀ ψ ∈ Γ, ψ ∈ T) → Unprovable 𝓢 Γ ⊥ :=
  by
  constructor; · intro h; simpa using Context.provable_iff.not.mp h;
  · intro h; apply Context.provable_iff.not.mpr; simp_all


-- @@ L46-51 expanded
lemma def_inconsistent :
    Inconsistent 𝓢 T ↔ ∃ (Γ : List (Formula α)), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Provable 𝓢 Γ ⊥ := by
  unfold Inconsistent; apply not_iff_not.mp; push Not; exact def_consistent;


-- @@ L53-60 verbatim
lemma union_consistent : Consistent 𝓢 (T₁ ∪ T₂) → (Consistent 𝓢 T₁) ∧ (Consistent 𝓢 T₂) := by
  intro h;
  replace h := def_consistent.mp h;
  constructor <;> {
    apply def_consistent.mpr;
    intro Γ hΓ;
    exact h Γ <| by tauto_set;
  }


-- @@ L62-62 verbatim
variable [Entailment.Classical 𝓢]


-- @@ L64-71 expanded
lemma emptyset_consistent [H_consis : Entailment.Consistent 𝓢] : Consistent 𝓢 ∅ := by
  classical obtain ⟨f, hf⟩ := H_consis.exists_unprovable; apply def_consistent.mpr; intro Γ hΓ;
  by_contra hC; replace hΓ := List.eq_nil_iff_forall_not_mem.mpr hΓ; subst hΓ;
  have : Provable 𝓢 f := efq'! <| mdp hC verum!; contradiction;


-- @@ L73-73 verbatim
variable [DecidableEq α]


-- @@ L75-80 expanded
omit [DecidableEq α] in
lemma not_mem_of_mem_neg (T_consis : Consistent 𝓢 T) (h : Tilde.tilde φ ∈ T) : φ ∉ T := by
  classical by_contra hC;
  have : Unprovable 𝓢 [φ, Tilde.tilde φ] ⊥ :=
    (def_consistent.mp T_consis) [φ, Tilde.tilde φ] (by simp_all);
  have : Provable 𝓢 [φ, Tilde.tilde φ] ⊥ :=
    Entailment.botOfMemEither! (φ := φ) (Γ := [φ, Tilde.tilde φ]) (by simp) (by simp);
  contradiction;


-- @@ L82-87 expanded
omit [DecidableEq α] in
lemma not_mem_neg_of_mem (T_consis : Consistent 𝓢 T) (h : φ ∈ T) : Tilde.tilde φ ∉ T := by
  classical by_contra hC;
  have : Unprovable 𝓢 [φ, Tilde.tilde φ] ⊥ :=
    (def_consistent.mp T_consis) [φ, Tilde.tilde φ] (by simp_all);
  have : Provable 𝓢 [φ, Tilde.tilde φ] ⊥ :=
    Entailment.botOfMemEither! (φ := φ) (Γ := [φ, Tilde.tilde φ]) (by simp) (by simp);
  contradiction;


-- @@ L89-115 expanded
omit [DecidableEq α] in
lemma iff_insert_consistent :
    Consistent 𝓢 (insert φ T) ↔
      ∀ {Γ : List (Formula α)},
        (∀ ψ ∈ Γ, ψ ∈ T) → Unprovable 𝓢 (Arrow.arrow (Wedge.wedge φ (List.conj₂ Γ)) ⊥) :=
  by
  classical
  constructor;
  · intro h Γ hΓ; by_contra hC;
    have : Unprovable 𝓢 (Arrow.arrow (Wedge.wedge φ (List.conj₂ Γ)) ⊥) :=
      iff_imply_left_cons_conj'!.not.mp <| (def_consistent.mp h) (φ :: Γ) (by simp_all);
    contradiction;
  · intro h; apply def_consistent.mpr; intro Γ hΓ;
    have : Unprovable 𝓢 (Arrow.arrow (Wedge.wedge φ (List.conj₂ (List.remove φ Γ))) ⊥) :=
      @h (Γ.remove φ)
        (by
          intro ψ hq; have := by simpa using hΓ ψ <| List.mem_of_mem_remove hq;
          cases this with
          | inl h => simpa [h] using List.mem_remove_iff.mp hq;
          | inr h => assumption; );
    by_contra hC; have := FiniteContext.provable_iff.mp hC;
    have :=
      imp_trans''! and_comm! <|
        imply_left_remove_conj! (φ := φ) <| FiniteContext.provable_iff.mp hC;
    contradiction;


-- @@ L117-123 expanded
omit [DecidableEq α] in
lemma iff_insert_inconsistent :
    Inconsistent 𝓢 (insert φ T) ↔
      ∃ Γ, (∀ φ ∈ Γ, φ ∈ T) ∧ Provable 𝓢 (Arrow.arrow (Wedge.wedge φ (List.conj₂ Γ)) ⊥) :=
  by classical unfold Inconsistent; apply not_iff_not.mp; push Not; exact iff_insert_consistent;


-- @@ L125-145 expanded
omit [DecidableEq α] in
lemma provable_iff_insert_neg_not_consistent :
    Inconsistent 𝓢 (insert (Tilde.tilde φ) T) ↔ Provable 𝓢 T φ := by
  classical
  constructor;
  · intro h; apply Context.provable_iff.mpr; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp h;
    existsi Γ; constructor; · exact hΓ₁;
    ·
      have : Provable 𝓢 Γ (Arrow.arrow (Tilde.tilde φ) ⊥) :=
        imp_swap'! <| and_imply_iff_imply_imply'!.mp hΓ₂;
      exact dne'! <| negEquiv'!.mpr this;
  · intro h; apply iff_insert_inconsistent.mpr; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    use Γ; constructor; · exact hΓ₁;
    · apply and_imply_iff_imply_imply'!.mpr; apply imp_swap'!; exact negEquiv'!.mp <| dni'! hΓ₂;


-- @@ L147-149 expanded
omit [DecidableEq α] in
lemma unprovable_iff_insert_neg_consistent :
    Consistent 𝓢 (insert (Tilde.tilde φ) T) ↔ Unprovable 𝓢 T φ := by
  classical simpa [not_not] using provable_iff_insert_neg_not_consistent.not;


-- @@ L151-157 expanded
omit [DecidableEq α] in
lemma unprovable_iff_singleton_neg_consistent : Consistent 𝓢 {Tilde.tilde φ} ↔ Unprovable 𝓢 φ := by
  classical
  have e : insert (Tilde.tilde φ) ∅ = ({Tilde.tilde φ} : FormulaSet α) := by aesop;
  have h₂ : Consistent 𝓢 (insert (Tilde.tilde φ) ∅) ↔ Unprovable 𝓢 ∅ φ :=
    unprovable_iff_insert_neg_consistent;
  rw [e] at h₂; suffices Unprovable 𝓢 φ ↔ Unprovable 𝓢 ∅ φ by tauto;
  exact Context.provable_iff_provable.not;


-- @@ L159-179 expanded
omit [DecidableEq α] in
lemma neg_provable_iff_insert_not_consistent :
    Inconsistent 𝓢 (insert (φ) T) ↔ Provable 𝓢 T (Tilde.tilde φ) := by
  classical
  constructor;
  · intro h; apply Context.provable_iff.mpr; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp h;
    existsi Γ; constructor; · exact hΓ₁;
    · apply negEquiv'!.mpr; exact imp_swap'! <| and_imply_iff_imply_imply'!.mp hΓ₂;
  · intro h; apply iff_insert_inconsistent.mpr; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ; constructor; · assumption;
    · apply and_imply_iff_imply_imply'!.mpr; apply imp_swap'!; exact negEquiv'!.mp hΓ₂;


-- @@ L181-184 expanded
omit [DecidableEq α] in
lemma neg_unprovable_iff_insert_consistent :
    Consistent 𝓢 (insert (φ) T) ↔ Unprovable 𝓢 T (Tilde.tilde φ) := by
  classical simpa [not_not] using neg_provable_iff_insert_not_consistent.not;


-- @@ L186-192 expanded
omit [DecidableEq α] in
lemma unprovable_iff_singleton_consistent : Consistent 𝓢 { φ } ↔ Unprovable 𝓢 (Tilde.tilde φ) := by
  classical
  have e : insert (φ) ∅ = ({ φ } : FormulaSet α) := by aesop;
  have h₂ := neg_unprovable_iff_insert_consistent (𝓢 := 𝓢) (T := ∅) (φ := φ); rw [e] at h₂;
  suffices Unprovable 𝓢 (Tilde.tilde φ) ↔ Unprovable 𝓢 ∅ (Tilde.tilde φ) by tauto;
  exact Context.provable_iff_provable.not;


-- @@ L194-199 expanded
omit [DecidableEq α] in
lemma unprovable_either (T_consis : Consistent 𝓢 T) :
    ¬(Provable 𝓢 T φ ∧ Provable 𝓢 T (Tilde.tilde φ)) := by
  classical by_contra hC; have ⟨hC₁, hC₂⟩ := hC; have := negMdp! hC₂ hC₁; contradiction;


-- @@ L201-206 expanded
omit [DecidableEq α] in
lemma not_mem_falsum_of_consistent (T_consis : Consistent 𝓢 T) : ⊥ ∉ T := by
  classical by_contra hC;
  have : Unprovable 𝓢 (Arrow.arrow ⊥ ⊥) := (def_consistent.mp T_consis) [⊥] (by simpa);
  have : Provable 𝓢 (Arrow.arrow ⊥ ⊥) := efq!; contradiction;


-- @@ L208-219 expanded
omit [DecidableEq α] in
lemma not_singleton_consistent [Entailment.Necessitation 𝓢] (T_consis : Consistent 𝓢 T)
    (h : Tilde.tilde (Box.box φ) ∈ T) : Consistent 𝓢 {Tilde.tilde φ} := by
  classical
  apply def_consistent.mpr; intro Γ hΓ; simp only [Set.mem_singleton_iff] at hΓ; by_contra hC;
  have : Provable 𝓢 (Arrow.arrow (Tilde.tilde (Box.box φ)) ⊥) :=
    negEquiv'!.mp <| dni'! <| nec! <| dne'! <| negEquiv'!.mpr <| replace_imply_left_conj! hΓ hC;
  have : Unprovable 𝓢 (Arrow.arrow (Tilde.tilde (Box.box φ)) ⊥) :=
    def_consistent.mp T_consis (Γ := [Tilde.tilde (Box.box φ)]) (by aesop)
  contradiction;


-- @@ L221-240 expanded
omit [DecidableEq α] in
lemma either_consistent (T_consis : Consistent 𝓢 T) (φ) :
    Consistent 𝓢 (insert φ T) ∨ Consistent 𝓢 (insert (Tilde.tilde φ) T) := by
  classical
  by_contra hC; push Not at hC; obtain ⟨hC₁, hC₂⟩ := hC
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp <| by simpa using hC₁;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_inconsistent.mp <| by simpa using hC₂;
  replace hΓ₂ := negEquiv'!.mpr hΓ₂; replace hΔ₂ := negEquiv'!.mpr hΔ₂;
  have : Provable 𝓢 (Arrow.arrow (Wedge.wedge (List.conj₂ Γ) (List.conj₂ Δ)) ⊥) :=
    negEquiv'!.mp <|
      demorgan₁'! <|
        or₃'''! (imp_trans''! (imply_of_not_or'! <| demorgan₄'! hΓ₂) or₁!)
          (imp_trans''! (imply_of_not_or'! <| demorgan₄'! hΔ₂) or₂!) lem!
  have : Unprovable 𝓢 (Arrow.arrow (Wedge.wedge (List.conj₂ Γ) (List.conj₂ Δ)) ⊥) :=
    unprovable_imp_trans''! imply_left_concat_conj! <|
      def_consistent.mp T_consis (Γ ++ Δ) <|
        by
        simp only [List.mem_append]; rintro ψ (hqΓ | hqΔ); · exact hΓ₁ ψ hqΓ;
        · exact hΔ₁ ψ hqΔ;
  contradiction;


-- @@ L242-263 expanded
omit [DecidableEq α] in
open Classical in
lemma intro_union_consistent
    (h :
      ∀ {Γ₁ Γ₂ : List (Formula α)},
        (∀ φ ∈ Γ₁, φ ∈ T₁) ∧ (∀ φ ∈ Γ₂, φ ∈ T₂) →
          Unprovable 𝓢 (Arrow.arrow (Wedge.wedge (List.conj₂ Γ₁) (List.conj₂ Γ₂)) ⊥)) :
    Consistent 𝓢 (T₁ ∪ T₂) := by
  classical apply def_consistent.mpr; intro Δ hΔ; let Δ₁ := (Δ.filter (· ∈ T₁));
  let Δ₂ := (Δ.filter (· ∈ T₂));
  have : Unprovable 𝓢 (Arrow.arrow (Wedge.wedge (List.conj₂ Δ₁) (List.conj₂ Δ₂)) ⊥) :=
    @h Δ₁ Δ₂
      ⟨(by intro _ h; simpa using List.of_mem_filter h),
        (by intro _ h; simpa using List.of_mem_filter h)⟩;
  exact
    unprovable_imp_trans''!
      (by
        apply FiniteContext.deduct'!; apply iff_provable_list_conj.mpr; intro ψ hq; cases (hΔ ψ hq);
        ·
          exact
            iff_provable_list_conj.mp (and₁'! FiniteContext.id!) ψ <|
              List.mem_filter_of_mem hq (by simpa);
        ·
          exact
            iff_provable_list_conj.mp (and₂'! FiniteContext.id!) ψ <|
              List.mem_filter_of_mem hq (by simpa);
          )
      this;


-- @@ L265-293 expanded
omit [DecidableEq α] in
open Classical in
lemma intro_triunion_consistent
    (h :
      ∀ {Γ₁ Γ₂ Γ₃ : List (Formula α)},
        (∀ φ ∈ Γ₁, φ ∈ T₁) ∧ (∀ φ ∈ Γ₂, φ ∈ T₂) ∧ (∀ φ ∈ Γ₃, φ ∈ T₃) →
          Unprovable 𝓢
            (Arrow.arrow (Wedge.wedge (List.conj₂ Γ₁) (Wedge.wedge (List.conj₂ Γ₂) (List.conj₂ Γ₃)))
              ⊥)) :
    Consistent 𝓢 (T₁ ∪ T₂ ∪ T₃) := by
  classical
  apply intro_union_consistent; rintro Γ₁₂ Γ₃ ⟨h₁₂, h₃⟩; simp only [Set.mem_union] at h₁₂;
  let Γ₁ := (Γ₁₂.filter (· ∈ T₁)); let Γ₂ := (Γ₁₂.filter (· ∈ T₂));
  apply
    unprovable_imp_trans''! (φ :=
      Wedge.wedge (List.conj₂ Γ₁) (Wedge.wedge (List.conj₂ Γ₂) (List.conj₂ Γ₃)));
  ·
    exact
      imp_trans''! (and₂'! <| and_assoc!) <| by apply and_replace_left!;
        apply imply_left_conj_concat!.mp; apply conjconj_subset!; intro φ hp;
        simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, Γ₁, Γ₂]; simp_all
  · apply h; refine ⟨?_, ?_, h₃⟩;
    · intro φ hp; rcases h₁₂ φ (List.mem_of_mem_filter hp) with (_ | _)
      · assumption;
      · simpa using List.of_mem_filter hp;
    · intro φ hp; rcases h₁₂ φ (List.mem_of_mem_filter hp) with (_ | _)
      · have := List.of_mem_filter hp; simp_all
      · assumption;


-- @@ L295-329 expanded
omit [DecidableEq α] in
omit [Entailment.Classical 𝓢] in
lemma exists_consistent_maximal_of_consistent (T_consis : Consistent 𝓢 T) :
    ∃ Z, Consistent 𝓢 Z ∧ T ⊆ Z ∧ ∀ U, Unprovable 𝓢 U ⊥ → Z ⊆ U → U = Z := by
  classical
  obtain ⟨Z, h₁, ⟨h₂, h₃⟩⟩ :=
    zorn_subset_nonempty {T : FormulaSet α | Consistent 𝓢 T}
      (by
        intro c hc chain hnc; existsi (⋃₀ c); simp only [Set.mem_ofPred_eq]; constructor;
        · apply def_consistent.mpr; intro Γ hΓ; by_contra hC;
          obtain ⟨U, hUc, hUs⟩ :=
            Set.subset_mem_chain_of_finite c hnc chain (s := ↑Γ.toFinset) (by simp)
              (by intro φ hp; simp_all);
          simp only [List.coe_toFinset] at hUs; have : Consistent 𝓢 U := hc hUc;
          have : Inconsistent 𝓢 U := by
            apply def_inconsistent.mpr; use Γ; constructor; · intro φ hp; exact hUs hp;
            · assumption;
          contradiction;
        · intro s a; exact Set.subset_sUnion_of_mem a; )
      T T_consis;
  use Z; simp_all only [Set.mem_ofPred_eq, true_and]; constructor; · assumption;
  · intro U hU hZU; apply Set.eq_of_subset_of_subset; · exact h₃ hU hZU;
    · assumption;


-- @@ L331-331 verbatim
protected alias lindenbaum := exists_consistent_maximal_of_consistent


-- @@ L333-333 verbatim
end FormulaSet




-- @@ L337-337 verbatim
open FormulaSet


-- @@ L339-341 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev MaximalConsistentSet (𝓢 : S) := { T :
    FormulaSet α // (Consistent 𝓢 T) ∧ (∀ {U}, T ⊂ U → Inconsistent 𝓢 U)}


-- @@ L343-343 verbatim
namespace MaximalConsistentSet


-- @@ L345-345 verbatim
variable {Ω Ω₁ Ω₂ : MaximalConsistentSet 𝓢}

-- @@ L346-346 verbatim
variable {φ : Formula α}


-- @@ L348-348 verbatim
instance : Membership (Formula α) (MaximalConsistentSet 𝓢) := ⟨fun Ω φ => φ ∈ Ω.1⟩


-- @@ L350-350 verbatim
lemma consistent (Ω : MaximalConsistentSet 𝓢) : Consistent 𝓢 Ω.1 := Ω.2.1


-- @@ L352-352 verbatim
lemma maximal (Ω : MaximalConsistentSet 𝓢) : Ω.1 ⊂ U → Inconsistent 𝓢 U := Ω.2.2


-- @@ L354-356 verbatim
lemma maximal' (Ω : MaximalConsistentSet 𝓢) {φ : Formula α} (hp : φ ∉ Ω) :
    Inconsistent 𝓢 (insert φ Ω.1) :=
  Ω.maximal (Set.ssubset_insert hp)


-- @@ L358-361 verbatim
lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.1 = Ω₂.1 := by
  constructor;
  · intro h; cases h; rfl;
  · intro h; cases Ω₁; cases Ω₂; simp_all;


-- @@ L363-363 verbatim
variable [DecidableEq α]


-- @@ L365-374 verbatim
omit [DecidableEq α] in
lemma exists_of_consistent (consisT : Consistent 𝓢 T) : ∃ Ω :
    MaximalConsistentSet 𝓢, (T ⊆ Ω.1) := by classical
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := FormulaSet.lindenbaum consisT;
  use ⟨Ω, ?_, ?_⟩;
  · assumption;
  · rintro U ⟨hU₁, _⟩;
    by_contra hC;
    have := hΩ₃ U hC <| hU₁;
    simp_all


-- @@ L376-376 verbatim
alias lindenbaum := exists_of_consistent


-- @@ L378-378 verbatim
section «lp_section_classical»


-- @@ L380-380 verbatim
variable [Entailment.Classical 𝓢]


-- @@ L382-385 verbatim
omit [DecidableEq α] in
instance [Entailment.Consistent 𝓢] :
    Nonempty (MaximalConsistentSet 𝓢) :=
  ⟨lindenbaum emptyset_consistent |>.choose⟩


-- @@ L387-393 expanded
omit [DecidableEq α] in
lemma either_mem (Ω : MaximalConsistentSet 𝓢) (φ) : φ ∈ Ω ∨ Tilde.tilde φ ∈ Ω := by
  classical
  by_contra hC; push Not at hC; rcases either_consistent (𝓢 := 𝓢) (Ω.consistent) φ;
  · have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  · have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;


-- @@ L395-405 expanded
omit [DecidableEq α] in
lemma membership_iff : (φ ∈ Ω) ↔ (Provable 𝓢 Ω.1 φ) := by
  classical
  constructor; · intro h; exact Context.by_axm! h;
  · intro hp;
    suffices Tilde.tilde φ ∉ Ω.1 by apply or_iff_not_imp_right.mp <| (either_mem Ω φ); assumption;
    by_contra hC; have hnp : Provable 𝓢 Ω.1 (Tilde.tilde φ) := Context.by_axm! hC;
    have : Provable 𝓢 Ω.1 ⊥ := negMdp! hnp hp; have : Unprovable 𝓢 Ω.1 ⊥ := Ω.consistent;
    contradiction;


-- @@ L407-410 verbatim
omit [DecidableEq α] in
@[simp]
lemma not_mem_falsum : ⊥ ∉ Ω := by classical
  exact not_mem_falsum_of_consistent Ω.consistent


-- @@ L412-416 verbatim
omit [DecidableEq α] in
@[simp]
lemma mem_verum : ⊤ ∈ Ω := by classical
  apply membership_iff.mpr
  apply verum!


-- @@ L418-438 expanded
omit [DecidableEq α] in
@[simp]
lemma iff_mem_neg : (Tilde.tilde φ ∈ Ω) ↔ (φ ∉ Ω) := by
  classical
  constructor;
  · intro hnp; by_contra hp; replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp; have : Provable 𝓢 Ω.1 ⊥ := negMdp! hnp hp;
    have : Unprovable 𝓢 Ω.1 ⊥ := Ω.consistent; contradiction;
  · intro hp;
    have : Consistent 𝓢 (insert (Tilde.tilde φ) Ω.1) := by
      have := provable_iff_insert_neg_not_consistent.not.mpr <| membership_iff.not.mp hp;
      unfold FormulaSet.Inconsistent at this; push Not at this; exact this;
    have := not_imp_not.mpr (@maximal (Ω := Ω) (U := insert (Tilde.tilde φ) Ω.1)) (by simpa);
    have : insert (Tilde.tilde φ) Ω.1 ⊆ Ω.1 := by simpa [Set.ssubset_def] using this;
    apply this; tauto_set;


-- @@ L440-442 expanded
omit [DecidableEq α] in
@[simp 1100]
lemma iff_mem_negneg : (Tilde.tilde (Tilde.tilde φ) ∈ Ω) ↔ (φ ∈ Ω) := by simp_all


-- @@ L444-461 expanded
omit [DecidableEq α] in
@[simp]
lemma iff_mem_imp : ((Arrow.arrow φ ψ) ∈ Ω) ↔ (φ ∈ Ω) → (ψ ∈ Ω) := by
  classical
  constructor;
  · intro hpq hp; replace dpq := membership_iff.mp hpq; replace dp := membership_iff.mp hp;
    apply membership_iff.mpr; exact mdp dpq dp;
  · intro h; replace h : φ ∉ Ω.1 ∨ ψ ∈ Ω := or_iff_not_imp_left.mpr (fun hnn => h (not_not.mp hnn));
    cases h with
    | inl h => apply membership_iff.mpr;
      exact efq_of_neg! <| membership_iff.mp <| iff_mem_neg.mpr h;
    | inr h => apply membership_iff.mpr; exact mdp imply₁! (membership_iff.mp h)


-- @@ L463-464 expanded
omit [DecidableEq α] in
lemma mdp (hφψ : Arrow.arrow φ ψ ∈ Ω) (hψ : φ ∈ Ω) : ψ ∈ Ω := by simp_all


-- @@ L466-477 expanded
omit [DecidableEq α] in
@[simp]
lemma iff_mem_and : ((Wedge.wedge φ ψ) ∈ Ω) ↔ (φ ∈ Ω) ∧ (ψ ∈ Ω) := by
  classical
  constructor;
  · intro hpq; replace hpq := membership_iff.mp hpq; constructor;
    · apply membership_iff.mpr; exact and₁'! hpq;
    · apply membership_iff.mpr; exact and₂'! hpq;
  · rintro ⟨hp, hq⟩; apply membership_iff.mpr;
    exact and₃'! (membership_iff.mp hp) (membership_iff.mp hq);


-- @@ L479-497 expanded
omit [DecidableEq α] in
@[simp]
lemma iff_mem_or : ((Vee.vee φ ψ) ∈ Ω) ↔ (φ ∈ Ω) ∨ (ψ ∈ Ω) := by
  classical
  constructor;
  · intro hpq; replace hpq := membership_iff.mp hpq; by_contra hC; push Not at hC;
    have ⟨hp, hq⟩ := hC; replace hp := membership_iff.mp <| iff_mem_neg.mpr hp;
    replace hq := membership_iff.mp <| iff_mem_neg.mpr hq;
    have : Provable 𝓢 Ω.1 ⊥ := or₃'''! (negEquiv'!.mp hp) (negEquiv'!.mp hq) hpq;
    have : Unprovable 𝓢 Ω.1 ⊥ := Ω.consistent; contradiction;
  · rintro (hp | hq); · apply membership_iff.mpr; exact or₁'! (membership_iff.mp hp);
    · apply membership_iff.mpr; exact or₂'! (membership_iff.mp hq);


-- @@ L499-504 expanded
omit [DecidableEq α] in
lemma iff_congr : (Provable 𝓢 Ω.1 (LogicalConnective.iff φ ψ)) → ((φ ∈ Ω) ↔ (ψ ∈ Ω)) := by
  classical
  intro hpq; constructor; · intro hp; exact iff_mem_imp.mp (membership_iff.mpr <| and₁'! hpq) hp;
  · intro hq; exact iff_mem_imp.mp (membership_iff.mpr <| and₂'! hpq) hq;


-- @@ L507-518 verbatim
omit [DecidableEq α] in
lemma intro_equality {h : ∀ φ, φ ∈ Ω₁.1 → φ ∈ Ω₂.1} : Ω₁ = Ω₂ := by classical
  exact equality_def.mpr <| Set.eq_of_subset_of_subset
    (by intro φ hp; exact h φ hp)
    (by
      intro φ;
      contrapose;
      intro hp;
      apply iff_mem_neg.mp;
      apply h;
      apply iff_mem_neg.mpr hp;
    )


-- @@ L520-523 expanded
omit [DecidableEq α] in
lemma neg_imp (h : ψ ∈ Ω₂ → φ ∈ Ω₁) : (Tilde.tilde φ ∈ Ω₁) → (Tilde.tilde ψ ∈ Ω₂) := by
  classical contrapose; simp_all


-- @@ L525-526 expanded
omit [DecidableEq α] in
lemma neg_iff (h : φ ∈ Ω₁ ↔ ψ ∈ Ω₂) : (Tilde.tilde φ ∈ Ω₁) ↔ (Tilde.tilde ψ ∈ Ω₂) := by simp_all


-- @@ L528-531 expanded
omit [DecidableEq α] in
lemma iff_mem_conj : (List.conj₂ Γ ∈ Ω) ↔ (∀ φ ∈ Γ, φ ∈ Ω) := by
  classical simp [membership_iff, iff_provable_list_conj];


-- @@ L533-533 verbatim
end «lp_section_classical»


-- @@ L535-535 verbatim
section «lp_section_1»


-- @@ L537-537 verbatim
variable [Entailment.K 𝓢]


-- @@ L539-568 expanded
omit [DecidableEq α] in
lemma iff_mem_multibox :
    (multibox n φ ∈ Ω) ↔
      (∀ {Ω' : MaximalConsistentSet 𝓢}, (Set.premultibox n Ω.1 ⊆ Ω'.1) → (φ ∈ Ω')) :=
  by
  classical
  constructor; · intro hp Ω' hΩ'; apply hΩ'; simpa;
  · contrapose; push Not; intro hp;
    obtain ⟨Ω', hΩ'⟩ :=
      lindenbaum (𝓢 := 𝓢) (T := insert (Tilde.tilde φ) (Set.premultibox n Ω.1))
        (by
          apply unprovable_iff_insert_neg_consistent.mpr; by_contra hC;
          obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
          have : Provable 𝓢 (Arrow.arrow (multibox n (List.conj₂ Γ)) (multibox n φ)) :=
            imply_multibox_distribute'! hΓ₂;
          have : Unprovable 𝓢 (Arrow.arrow (multibox n (List.conj₂ Γ)) (multibox n φ)) := by
            have := Context.provable_iff.not.mp <| membership_iff.not.mp hp; push Not at this;
            have : Unprovable 𝓢 (Arrow.arrow (List.conj₂ (List.multibox n Γ)) (multibox n φ)) :=
              FiniteContext.provable_iff.not.mp <| this (List.multibox n Γ) (by simp_all);
            revert this; contrapose; exact imp_trans''! collect_multibox_conj!;
          contradiction; );
    existsi Ω'; constructor; · exact Set.Subset.trans (by tauto_set) hΩ';
    · apply iff_mem_neg.mp; apply hΩ'; simp only [Set.mem_insert_iff, true_or]


-- @@ L570-573 expanded
omit [DecidableEq α] in
lemma iff_mem_box :
    (Box.box φ ∈ Ω) ↔ (∀ {Ω' : MaximalConsistentSet 𝓢}, (Set.prebox Ω.1 ⊆ Ω'.1) → (φ ∈ Ω')) :=
  iff_mem_multibox (n := 1)


-- @@ L576-579 expanded
omit [DecidableEq α] in
lemma multibox_dn_iff : (multibox n (Tilde.tilde (Tilde.tilde φ)) ∈ Ω) ↔ (multibox n φ ∈ Ω) := by
  classical simp only [iff_mem_multibox]; simp_all


-- @@ L581-583 expanded
omit [DecidableEq α] in
lemma box_dn_iff : (Box.box (Tilde.tilde (Tilde.tilde φ)) ∈ Ω) ↔ (Box.box φ ∈ Ω) := by
  classical exact multibox_dn_iff (n := 1)


-- @@ L586-597 expanded
omit [DecidableEq α] in
lemma mem_multibox_dual : multibox n φ ∈ Ω ↔ Tilde.tilde (multidia n (Tilde.tilde φ)) ∈ Ω := by
  classical
  simp only [membership_iff]; constructor;
  · intro h; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    exact
      Context.provable_iff.mpr
        ⟨Γ, hΓ₁,
          FiniteContext.provable_iff.mpr <|
            imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multibox_duality!)⟩;
  · intro h; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    exact
      Context.provable_iff.mpr
        ⟨Γ, hΓ₁,
          FiniteContext.provable_iff.mpr <|
            imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multibox_duality!)⟩;


-- @@ L599-601 expanded
omit [DecidableEq α] in
lemma mem_box_dual : Box.box φ ∈ Ω ↔ (Tilde.tilde (Dia.dia (Tilde.tilde φ)) ∈ Ω) := by
  classical exact mem_multibox_dual (n := 1)


-- @@ L603-614 expanded
omit [DecidableEq α] in
lemma mem_multidia_dual : multidia n φ ∈ Ω ↔ Tilde.tilde (multibox n (Tilde.tilde φ)) ∈ Ω := by
  classical
  simp only [membership_iff]; constructor;
  · intro h; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    exact
      Context.provable_iff.mpr
        ⟨Γ, hΓ₁,
          FiniteContext.provable_iff.mpr <|
            imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multidia_duality!)⟩;
  · intro h; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    exact
      Context.provable_iff.mpr
        ⟨Γ, hΓ₁,
          FiniteContext.provable_iff.mpr <|
            imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multidia_duality!)⟩;


-- @@ L615-617 expanded
omit [DecidableEq α] in
lemma mem_dia_dual : Dia.dia φ ∈ Ω ↔ (Tilde.tilde (Box.box (Tilde.tilde φ)) ∈ Ω) := by
  classical exact mem_multidia_dual (n := 1)


-- @@ L619-637 expanded
omit [DecidableEq α] in
lemma iff_mem_multidia :
    (multidia n φ ∈ Ω) ↔
      (∃ Ω' : MaximalConsistentSet 𝓢, (Set.premultibox n Ω.1 ⊆ Ω'.1) ∧ (φ ∈ Ω'.1)) :=
  by
  classical
  constructor;
  · intro h; have := mem_multidia_dual.mp h; have := iff_mem_neg.mp this;
    have := iff_mem_multibox.not.mp this; push Not at this; simp_all
  · rintro ⟨Ω', h₁, h₂⟩; apply mem_multidia_dual.mpr; apply iff_mem_neg.mpr;
    apply iff_mem_multibox.not.mpr; push Not; use Ω'; constructor; · exact h₁;
    · exact iff_mem_neg.mp <| iff_mem_negneg.mpr h₂;


-- @@ L638-641 expanded
omit [DecidableEq α] in
lemma iff_mem_dia :
    (Dia.dia φ ∈ Ω) ↔ (∃ Ω' : MaximalConsistentSet 𝓢, (Set.prebox Ω.1 ⊆ Ω'.1) ∧ (φ ∈ Ω'.1)) :=
  iff_mem_multidia (n := 1)


-- @@ L643-662 expanded
omit [DecidableEq α] in
lemma multibox_multidia :
    (∀ {φ : Formula α}, (multibox n φ ∈ Ω₁.1 → φ ∈ Ω₂.1)) ↔
      (∀ {φ : Formula α}, (φ ∈ Ω₂.1 → multidia n φ ∈ Ω₁.1)) :=
  by
  classical
  constructor;
  · intro h φ; contrapose; intro h₂; apply iff_mem_neg.mp; apply h; apply iff_mem_negneg.mp;
    apply (neg_iff <| mem_multidia_dual).mp; exact iff_mem_neg.mpr h₂;
  · intro h φ; contrapose; intro h₂; apply iff_mem_neg.mp; apply (neg_iff <| mem_multibox_dual).mpr;
    apply iff_mem_negneg.mpr; apply h; exact iff_mem_neg.mpr h₂;


-- @@ L664-664 verbatim
variable {Γ : List (Formula α)}


-- @@ L666-674 expanded
omit [DecidableEq α] in
lemma iff_mem_multibox_conj : (multibox n (List.conj₂ Γ) ∈ Ω) ↔ (∀ φ ∈ Γ, multibox n φ ∈ Ω) := by
  classical
  simp only [iff_mem_multibox, iff_mem_conj]; constructor; · intro h φ hφ Ω' hΩ'; exact h hΩ' _ hφ;
  · intro h Ω' hΩ' φ hφ; apply h _ hφ; tauto;


-- @@ L676-678 expanded
omit [DecidableEq α] in
lemma iff_mem_box_conj : (Box.box (List.conj₂ Γ) ∈ Ω) ↔ (∀ φ ∈ Γ, Box.box φ ∈ Ω) := by
  classical exact iff_mem_multibox_conj (n := 1)


-- @@ L680-680 verbatim
end «lp_section_1»


-- @@ L682-682 verbatim
end MaximalConsistentSet


-- @@ L684-684 verbatim
end Modal

-- @@ L685-685 verbatim
end LO
