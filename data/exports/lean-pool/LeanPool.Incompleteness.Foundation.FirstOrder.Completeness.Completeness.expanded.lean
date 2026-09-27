/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.SearchTree
public import LeanPool.Incompleteness.Foundation.FirstOrder.Completeness.SubLanguage
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Model
import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Soundness
import LeanPool.Incompleteness.Foundation.FirstOrder.Ultraproduct


-- @@ L14-14 verbatim
/-! # Completeness -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace LO


-- @@ L21-21 verbatim
namespace FirstOrder


-- @@ L23-23 verbatim
open Semiformula Completeness


-- @@ L25-25 verbatim
variable {L : Language.{u}} {T : Theory L}


-- @@ L27-27 verbatim
section «lp_section_1»


-- @@ L29-30 verbatim
variable [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] [(k : ℕ) →
  Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]


-- @@ L32-43 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def _root_.LO.FirstOrder.Derivation.completenessOfEncodable {Γ : Sequent L}
    (h : ∀ M [Nonempty M] [Structure L M], ModelsTheory M T → ∃ φ ∈ Γ, Models M φ) :
    OneSided.Derivation T Γ :=
  by
  have : WellFounded (SearchTree.Lt T Γ) := by
    by_contra nwf
    have : ∃ φ ∈ Γ, Models (Model T Γ) φ := h _ (Model.models nwf)
    rcases this with ⟨φ, hp, h⟩
    have : Evalf (Model.structure T Γ) (&·) φ := h (&·)
    have : ¬Evalf (Model.structure T Γ) (&·) φ := by
      simpa using semanticMainLemmaTop nwf (φ := φ) hp
    contradiction
  exact syntacticMainLemmaTop this


-- @@ L45-50 expanded
omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] in
lemma completenessOfEncodable {φ : SyntacticFormula L} : Consequence T φ → Provable T φ := by
  classical
    exact fun h ↦
    ⟨Derivation.completenessOfEncodable (T := T) (Γ := [φ])
        (fun _ _ _ hM ↦ ⟨φ, List.mem_of_mem_head? rfl, h hM⟩)⟩


-- @@ L52-55 verbatim
omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] in
instance : Complete T (Semantics.models (SmallStruc L) T) := by
  classical
  exact ⟨completenessOfEncodable⟩


-- @@ L57-57 verbatim
end «lp_section_1»


-- @@ L59-83 expanded
theorem complete {φ : SyntacticFormula L} : Consequence T φ → Provable T φ := fun h ↦ by
  classical
  have :
    ∃ u : Finset (SyntacticFormula L),
      ↑u ⊆ insert (Tilde.tilde ∀∀φ) T ∧ ¬Satisfiable (u : Theory L) :=
    by simpa using compact.not.mp (consequence_iff_unsatisfiable.mp h)
  rcases this with ⟨u, ssu, hu⟩
  have : ∀ k, Encodable ((languageFinset u).Func k) := fun _ ↦ Fintype.toEncodable _
  have : ∀ k, Encodable ((languageFinset u).Rel k) := fun _ ↦ Fintype.toEncodable _
  let u' : Finset (SyntacticFormula (languageFinset u)) :=
    Finset.imageOfFinset u (fun _ hp ↦ toSubLanguageFinsetSelf hp)
  have image_u' : u'.image (Semiformula.lMap L.ofSubLanguage) = u :=
    by
    ext τ
    simp [u', Finset.mem_imageOfFinset_iff]
  have : ¬Satisfiable (u' : Theory (languageFinset u)) :=
    by
    intro h
    have : Satisfiable (u : Theory L) := by
      rw [← image_u']
      simpa using
        (satisfiable_lMap L.ofSubLanguage (fun k ↦ Subtype.val_injective)
          (fun _ ↦ Subtype.val_injective) h)
    contradiction
  have : Entailment.Inconsistent (u' : Theory (languageFinset u)) :=
    Complete.inconsistent_of_unsatisfiable this
  have : Entailment.Inconsistent (u : Theory L) := by rw [← image_u', Finset.coe_image];
    exact Derivation.inconsistent_lMap L.ofSubLanguage this
  have : Entailment.Inconsistent (insert (Tilde.tilde ∀∀φ) T) := this.of_supset ssu
  exact Derivation.provable_iff_inconsistent.mpr this


-- @@ L85-85 expanded
theorem complete_iff : Consequence T φ ↔ Provable T φ :=
  ⟨fun h ↦ complete h, sound!⟩


-- @@ L87-87 verbatim
instance (T : Theory L) : Complete T (Semantics.models (SmallStruc L) T) := ⟨complete⟩


-- @@ L89-90 verbatim
lemma satisfiable_of_consistent' (h : Entailment.Consistent T) :
    Semantics.Satisfiable (SmallStruc L) T := Complete.satisfiable_of_consistent h


-- @@ L92-96 verbatim
lemma satisfiable_of_consistent (h : Entailment.Consistent T) :
    Semantics.Satisfiable (Struc.{max u w} L) T := by
  let ⟨M, _, _, h⟩ := satisfiable_iff.mp (satisfiable_of_consistent' h)
  exact satisfiable_iff.mpr ⟨ULift.{w} M, inferInstance, inferInstance,
    ((uLift_elementaryEquiv L M).modelsTheory).mpr h⟩


-- @@ L98-100 verbatim
lemma satisfiable_iff_consistent' :
    Semantics.Satisfiable (Struc.{max u w} L) T ↔ Entailment.Consistent T :=
  ⟨consistent_of_satidfiable, satisfiable_of_consistent.{u, w}⟩


-- @@ L102-103 verbatim
lemma satisfiable_iff_consistent :
    Satisfiable T ↔ Entailment.Consistent T := satisfiable_iff_consistent'.{u, u}


-- @@ L105-107 verbatim
lemma satidfiable_iff_satisfiable :
    Semantics.Satisfiable (Struc.{max u w} L) T ↔ Satisfiable T := by
  simp [satisfiable_iff_consistent'.{u, w}, satisfiable_iff_consistent]


-- @@ L109-110 expanded
lemma consequence_iff_consequence : Consequence (Struc.{max u w} L) T φ ↔ Consequence T φ := by
  simp [consequence_iff_unsatisfiable, satidfiable_iff_satisfiable.{u, w}]


-- @@ L112-113 expanded
theorem complete' {φ : SyntacticFormula L} : Consequence (Struc.{max u w} L) T φ → Provable T φ :=
  fun h ↦ complete <| consequence_iff_consequence.{u, w}.mp h


-- @@ L115-115 verbatim
instance (T : Theory L) : Complete T (Semantics.models (Struc.{max u w} L) T) := ⟨complete'.{u, w}⟩


-- @@ L117-117 verbatim
end FirstOrder


-- @@ L119-119 verbatim
end LO
