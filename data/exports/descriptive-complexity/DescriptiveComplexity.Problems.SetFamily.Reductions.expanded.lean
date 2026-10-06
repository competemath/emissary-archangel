/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.SetFamily.Defs


-- @@ L9-25 verbatim
/-!
# Set Cover and Hitting Set are transposes of each other

The inter-reduction inside the set family, the counterpart of the
complementation reductions of
`DescriptiveComplexity.Problems.CliqueFamily.Reductions`: the two problems are the
same condition read in the two directions of the incidence relation, so a
single interpretation of tag `Unit` and dimension 1
(`DescriptiveComplexity.transposeInterp`) – exchange the two unary marks, transpose
the incidence relation, keep the threshold – reduces each of them to the
other (`DescriptiveComplexity.setCover_fo_reduction_hittingSet` and
`DescriptiveComplexity.hittingSet_fo_reduction_setCover`), quantifier-free.

Set Packing has no such partner: its condition is not the transpose of
another problem of the family, and its hardness comes from graphs directly
(`DescriptiveComplexity.Problems.SetFamily.FromGraphs`).
-/


-- @@ L27-27 verbatim
namespace DescriptiveComplexity


-- @@ L29-29 verbatim
open FirstOrder


-- @@ L31-31 verbatim
open Language Structure BoundedFormula


-- @@ L33-33 verbatim
/-! ### Set Cover and Hitting Set are transposes of each other -/


-- @@ L35-44 expanded
/-- The transposing interpretation: ground elements and sets of the family
exchange their marks, incidence is read backwards, the threshold is kept. -/
def transposeInterp : FOInterpretation Language.setSystem Language.setSystem Unit 1 where
  relFormula {n}
    R :=
    match n, R with
    | _, .elem => fun _ =>
      FirstOrder.Language.Relations.formula₁ ssFam (FirstOrder.Language.Term.var (0, 0))
    | _, .fam => fun _ =>
      FirstOrder.Language.Relations.formula₁ ssElem (FirstOrder.Language.Term.var (0, 0))
    | _, .mem => fun _ =>
      FirstOrder.Language.Relations.formula₂ ssMem (FirstOrder.Language.Term.var (1, 0))
        (FirstOrder.Language.Term.var (0, 0))
    | _, .marked => fun _ =>
      FirstOrder.Language.Relations.formula₁ ssMarked (FirstOrder.Language.Term.var (0, 0))


-- @@ L46-46 verbatim
section TransposeCharacterizations


-- @@ L48-48 verbatim
variable {A : Type} [Language.setSystem.Structure A]


-- @@ L50-54 verbatim
@[simp]
theorem transpose_elem (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) ssElem ![((), w)] ↔ RelMap ssFam ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]


-- @@ L56-60 verbatim
@[simp]
theorem transpose_fam (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) ssFam ![((), w)] ↔ RelMap ssElem ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]


-- @@ L62-67 verbatim
@[simp]
theorem transpose_mem (w₁ w₂ : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) ssMem ![((), w₁), ((), w₂)] ↔
      RelMap ssMem ![w₂ 0, w₁ 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₂]


-- @@ L69-73 verbatim
@[simp]
theorem transpose_marked (w : Fin 1 → A) :
    RelMap (M := transposeInterp.Map A) ssMarked ![((), w)] ↔ RelMap ssMarked ![w 0] := by
  rw [FOInterpretation.relMap_map]
  simp [transposeInterp, Formula.realize_rel₁]


-- @@ L75-75 verbatim
end TransposeCharacterizations


-- @@ L77-77 verbatim
section TransposeCorrectness


-- @@ L79-79 verbatim
variable (A : Type) [Language.setSystem.Structure A]


-- @@ L81-85 verbatim
private theorem transpose_hElem :
    ∀ b : transposeInterp.Map A,
      SSElem b ↔ SSFam (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_elem w


-- @@ L87-91 verbatim
private theorem transpose_hFam :
    ∀ b : transposeInterp.Map A,
      SSFam b ↔ SSElem (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_fam w


-- @@ L93-98 verbatim
private theorem transpose_hMem :
    ∀ b b' : transposeInterp.Map A,
      SSMem b b' ↔ SSMem (transposeInterp.mapEquivSelf A b')
        (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩ ⟨⟨⟩, w'⟩
  exact transpose_mem w w'


-- @@ L100-104 verbatim
private theorem transpose_hMarked :
    ∀ b : transposeInterp.Map A,
      SSMarked b ↔ SSMarked (transposeInterp.mapEquivSelf A b) := by
  rintro ⟨⟨⟩, w⟩
  exact transpose_marked w


-- @@ L106-112 verbatim
/-- Correctness of the transposition, hitting-set-to-set-cover direction: a
hitting set of a set system is a cover of its transpose. -/
theorem hasSmallHittingSet_iff_map :
    HasSmallHittingSet A ↔ HasSmallSetCover (transposeInterp.Map A) :=
  and_congr ((transposeInterp.mapEquivSelf A).finite_iff).symm
    (CoversOn.equiv_iff (transposeInterp.mapEquivSelf A) (transpose_hElem A)
      (transpose_hFam A) (transpose_hMem A) (transpose_hMarked A)).symm


-- @@ L114-121 verbatim
/-- Correctness of the transposition, set-cover-to-hitting-set direction: a
cover of a set system is a hitting set of its transpose. -/
theorem hasSmallSetCover_iff_map :
    HasSmallSetCover A ↔ HasSmallHittingSet (transposeInterp.Map A) :=
  and_congr ((transposeInterp.mapEquivSelf A).finite_iff).symm
    (CoversOn.equiv_iff (transposeInterp.mapEquivSelf A) (transpose_hFam A)
      (transpose_hElem A) (fun b b' => transpose_hMem A b' b)
      (transpose_hMarked A)).symm


-- @@ L123-123 verbatim
end TransposeCorrectness


-- @@ L125-131 verbatim
/-- **Set Cover FO-reduces to Hitting Set**, by transposing the incidence
relation. -/
def setCover_fo_reduction_hittingSet : SetCover ≤ᶠᵒ HittingSet where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ _ := hasSmallSetCover_iff_map A


-- @@ L133-139 verbatim
/-- **Hitting Set FO-reduces to Set Cover**, by transposing the incidence
relation. -/
def hittingSet_fo_reduction_setCover : HittingSet ≤ᶠᵒ SetCover where
  Tag := Unit
  dim := 1
  toInterpretation := transposeInterp
  correct A _ _ _ := hasSmallHittingSet_iff_map A

-- @@ L140-140 verbatim
end DescriptiveComplexity
