/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Block
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.ThreeDimMatching.Defs
import DescriptiveComplexity.SecondOrder


-- @@ L11-21 verbatim
/-!
# 3-dimensional matching is existential second-order definable

The membership half of its NP-completeness
(`DescriptiveComplexity.threeDimMatching_sigmaSODefinable`): a matching *is* a
relation, so a single existential block guesses it – ternary, the first of the
catalog – and the kernel spells out the seven conditions of
`DescriptiveComplexity.IsMatchingOn`: that the guessed triples are available ones
inside the three classes, that every marked element is covered, and that no
two triples share a coordinate.
-/


-- @@ L23-23 verbatim
namespace DescriptiveComplexity


-- @@ L25-25 verbatim
open FirstOrder


-- @@ L27-27 verbatim
open Language Structure SOBlock


-- @@ L29-29 verbatim
section SigmaOne


-- @@ L31-35 verbatim
/-- The single existential block of the `Σ₁` definition: the matching, a
ternary relation. -/
fo_block tdmGuessBlock over Language.tripleSys ts into tdmSOLang with t where
  /-- The guessed matching. -/
  matching : 3


-- @@ L37-39 expanded
/-- The guessed matching, as an atom. -/
private def matF {α : Type} (x y z : α) : tdmSOLang.Formula α :=
  FirstOrder.Language.Relations.formula tMatchingSym
    ![FirstOrder.Language.Term.var x, FirstOrder.Language.Term.var y,
      FirstOrder.Language.Term.var z]


-- @@ L41-43 expanded
/-- The available triples, as an atom. -/
private def tripF {α : Type} (x y z : α) : tdmSOLang.Formula α :=
  FirstOrder.Language.Relations.formula tTripSym
    ![FirstOrder.Language.Term.var x, FirstOrder.Language.Term.var y,
      FirstOrder.Language.Term.var z]


-- @@ L45-49 expanded
/-- Kernel conjunct: the guessed triples are available ones, inside the three
classes. -/
private noncomputable def tdmSubClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    ((matF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2)).imp
      (tripF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓
            FirstOrder.Language.Relations.formula₁ tXElSym
              (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
          FirstOrder.Language.Relations.formula₁ tYElSym
            (FirstOrder.Language.Term.var (Sum.inr 1)) ⊓
        FirstOrder.Language.Relations.formula₁ tZElSym (FirstOrder.Language.Term.var (Sum.inr 2))))


-- @@ L51-53 expanded
/-- Kernel conjunct: every element of the first class is covered. -/
private noncomputable def tdmCovXClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    ((FirstOrder.Language.Relations.formula₁ tXElSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
      (FirstOrder.Language.Formula.iExs (Fin 2)
        (matF (Sum.inl (Sum.inr 0)) (Sum.inr 0) (Sum.inr 1))))


-- @@ L55-57 expanded
/-- Kernel conjunct: every element of the second class is covered. -/
private noncomputable def tdmCovYClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    ((FirstOrder.Language.Relations.formula₁ tYElSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
      (FirstOrder.Language.Formula.iExs (Fin 2)
        (matF (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 1))))


-- @@ L59-61 expanded
/-- Kernel conjunct: every element of the third class is covered. -/
private noncomputable def tdmCovZClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    ((FirstOrder.Language.Relations.formula₁ tZElSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
      (FirstOrder.Language.Formula.iExs (Fin 2)
        (matF (Sum.inr 0) (Sum.inr 1) (Sum.inl (Sum.inr 0)))))


-- @@ L63-65 expanded
/-- Kernel conjunct: two triples sharing their first coordinate coincide. -/
private noncomputable def tdmUniqXClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 5)
    ((matF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ matF (Sum.inr 0) (Sum.inr 3) (Sum.inr 4)).imp
      (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
          (FirstOrder.Language.Term.var (Sum.inr 3)) ⊓
        FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 2))
          (FirstOrder.Language.Term.var (Sum.inr 4))))


-- @@ L67-69 expanded
/-- Kernel conjunct: two triples sharing their second coordinate coincide. -/
private noncomputable def tdmUniqYClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 5)
    ((matF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ matF (Sum.inr 3) (Sum.inr 1) (Sum.inr 4)).imp
      (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 3)) ⊓
        FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 2))
          (FirstOrder.Language.Term.var (Sum.inr 4))))


-- @@ L71-73 expanded
/-- Kernel conjunct: two triples sharing their third coordinate coincide. -/
private noncomputable def tdmUniqZClause : tdmSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 5)
    ((matF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓ matF (Sum.inr 3) (Sum.inr 4) (Sum.inr 2)).imp
      (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
          (FirstOrder.Language.Term.var (Sum.inr 3)) ⊓
        FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 1))
          (FirstOrder.Language.Term.var (Sum.inr 4))))


-- @@ L75-79 verbatim
/-- The first-order kernel of the `Σ₁` definition: the guessed relation is a
matching. -/
noncomputable def tdmKernel : tdmSOLang.Sentence :=
  tdmSubClause ⊓ (tdmCovXClause ⊓ (tdmCovYClause ⊓ (tdmCovZClause ⊓
    (tdmUniqXClause ⊓ (tdmUniqYClause ⊓ tdmUniqZClause)))))


-- @@ L81-81 verbatim
section Realize


-- @@ L83-83 verbatim
variable {A : Type} [Language.tripleSys.Structure A]


-- @@ L85-128 verbatim
/-- Realization of the kernel under an assignment of the guessed matching. -/
private theorem realize_tdmKernel (ρ : tdmGuessBlock.Assignment A) :
    (@Sentence.Realize tdmSOLang A
        (@sumStructure _ _ A _ (tdmGuessBlock.structure ρ)) tdmKernel) ↔
      IsMatchingOn (TSXEl (A := A)) TSYEl TSZEl TSTrip
        (fun x y z => ρ .matching ![x, y, z]) := by
  let := tdmGuessBlock.structure ρ
  have hsub : ∀ w : Fin 3 → A, RelMap (L := tdmSOLang) (M := A) tMatchingSym w ↔ ρ .matching w :=
    fun _ => Iff.rfl
  rw [tdmKernel, IsMatchingOn]
  simp only [tdmSubClause, tdmCovXClause, tdmCovYClause, tdmCovZClause, tdmUniqXClause,
    tdmUniqYClause, tdmUniqZClause, matF, tripF, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_imp, Formula.realize_equal,
    Formula.realize_rel₁, realize_rel₃, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  refine and_congr ⟨fun h x y z hm => ?_, fun h i hi => ?_⟩
    (and_congr ⟨fun h x hx => ?_, fun h i hi => ?_⟩
      (and_congr ⟨fun h y hy => ?_, fun h i hi => ?_⟩
        (and_congr ⟨fun h z hz => ?_, fun h i hi => ?_⟩
          (and_congr ⟨fun h x y z y' z' h₁ h₂ => ?_, fun h i hi => ?_⟩
            (and_congr ⟨fun h x y z x' z' h₁ h₂ => ?_, fun h i hi => ?_⟩
              ⟨fun h x y z x' y' h₁ h₂ => ?_, fun h i hi => ?_⟩)))))
  · have h' := h ![x, y, z] hm
    exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩
  · have h' := h (i 0) (i 1) (i 2) hi
    exact ⟨⟨⟨h'.1, h'.2.1⟩, h'.2.2.1⟩, h'.2.2.2⟩
  · obtain ⟨w, hw⟩ := h (fun _ => x) hx
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨y, z, hyz⟩ := h (i 0) hi
    exact ⟨![y, z], hyz⟩
  · obtain ⟨w, hw⟩ := h (fun _ => y) hy
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨x, z, hxz⟩ := h (i 0) hi
    exact ⟨![x, z], hxz⟩
  · obtain ⟨w, hw⟩ := h (fun _ => z) hz
    exact ⟨w 0, w 1, hw⟩
  · obtain ⟨x, y, hxy⟩ := h (i 0) hi
    exact ⟨![x, y], hxy⟩
  · exact h ![x, y, z, y', z'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2
  · exact h ![x, y, z, x', z'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2
  · exact h ![x, y, z, x', y'] ⟨h₁, h₂⟩
  · exact h (i 0) (i 1) (i 2) (i 3) (i 4) hi.1 hi.2


-- @@ L130-130 verbatim
end Realize


-- @@ L132-146 verbatim
/-- **3-dimensional matching is `Σ₁`-definable**: existentially guess the
matching – a ternary relation – then check first-order that it is one. Since
NP is defined as `Σ₁`-definability, this is the membership half of its
NP-completeness. -/
theorem threeDimMatching_sigmaSODefinable : SigmaSODefinable 1 ThreeDimMatching := by
  refine ⟨[tdmGuessBlock], rfl, tdmKernel, ?_⟩
  intro A _ _ _
  rw [show ThreeDimMatching.Holds A = HasThreeDimMatching A from rfl, HasThreeDimMatching,
    and_iff_right ‹Finite A›]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨fun i => match i with | .matching => fun w : Fin 3 → A => M (w 0) (w 1) (w 2),
      (realize_tdmKernel _).mpr hM⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨_, (realize_tdmKernel ρ).mp hρ⟩


-- @@ L148-148 verbatim
end SigmaOne


-- @@ L150-150 verbatim
end DescriptiveComplexity
