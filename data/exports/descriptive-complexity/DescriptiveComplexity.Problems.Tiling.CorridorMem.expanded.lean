/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Tiling.Corridor
import DescriptiveComplexity.PSpace


-- @@ L10-33 verbatim
/-!
# Tiling a corridor is in PSPACE

The membership half: a corridor *is* a walk. Its states are the rows – one
binary relation variable `R x t`, read as “the column `x` of this row carries
the tile `t`” – its starting states are the rows the bottom-row description
allows, its transitions are the vertical compatibility, and its accepting states
are the rows carrying an accepting tile. That is exactly the shape of
`DescriptiveComplexity.SOTCSpec`, so the specification is a transcription rather
than a construction, and PSPACE is SO(TC).

Being a *row* – one tile per column, horizontally compatible, with the tiles the
two edge columns allow – is asked of the starting state and of every state a
transition enters, so every reachable state is a row.

## The sentence shapes

The three sentences of the specification live over two different vocabularies
(one copy of the block for the endpoints, two for the transition), so each shape
is written once over an arbitrary vocabulary with its symbols as parameters, and
read back by one realization lemma. Read over an exponential expansion the same
specification asks about a corridor of exponential width, which is the EXPSPACE
half.
-/


-- @@ L35-35 verbatim
namespace DescriptiveComplexity


-- @@ L37-37 verbatim
open FirstOrder


-- @@ L39-39 verbatim
open Language Structure


-- @@ L41-41 verbatim
/-! ### Atoms and guards, over an arbitrary vocabulary -/


-- @@ L43-43 verbatim
section Shapes


-- @@ L45-45 verbatim
variable {L : Language.{0, 0}} {γ : Type}


-- @@ L47-48 expanded
/-- A unary relation, as a formula. -/
noncomputable def atom₁ (r : L.Relations 1) (x : γ) : L.Formula γ :=
  FirstOrder.Language.Relations.formula₁ r (FirstOrder.Language.Term.var x)


-- @@ L50-51 expanded
/-- A binary relation, as a formula. -/
noncomputable def atom₂ (r : L.Relations 2) (x y : γ) : L.Formula γ :=
  FirstOrder.Language.Relations.formula₂ r (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L53-54 expanded
/-- Equality of two variables, as a formula. -/
noncomputable def atomEq (x y : γ) : L.Formula γ :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)


-- @@ L56-58 expanded
/-- `x` is the least position. -/
noncomputable def minPosF (posn : L.Relations 1) (le : L.Relations 2) (x : γ) : L.Formula γ :=
  (atom₁ posn) x ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      (((atom₁ posn) (Sum.inr 0)).imp ((atom₂ le) (Sum.inl x) (Sum.inr 0)))


-- @@ L60-62 expanded
/-- `x` is the greatest position. -/
noncomputable def maxPosF (posn : L.Relations 1) (le : L.Relations 2) (x : γ) : L.Formula γ :=
  (atom₁ posn) x ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      (((atom₁ posn) (Sum.inr 0)).imp ((atom₂ le) (Sum.inr 0) (Sum.inl x)))


-- @@ L64-68 expanded
/-- `x'` is the position immediately above `x`. -/
noncomputable def succPosF (posn : L.Relations 1) (le : L.Relations 2) (x x' : γ) : L.Formula γ :=
  (atom₁ posn) x ⊓
    ((atom₁ posn) x' ⊓
      ((atom₂ le) x x' ⊓
        (FirstOrder.Language.BoundedFormula.not (atomEq x x') ⊓
          FirstOrder.Language.Formula.iAlls (Fin 1)
            (((atom₁ posn) (Sum.inr 0) ⊓
                  ((atom₂ le) (Sum.inl x) (Sum.inr 0) ⊓ (atom₂ le) (Sum.inr 0) (Sum.inl x'))).imp
              (atomEq (Sum.inr 0) (Sum.inl x) ⊔ atomEq (Sum.inr 0) (Sum.inl x'))))))


-- @@ L70-70 verbatim
variable {M : Type} [L.Structure M] {v : γ → M}


-- @@ L72-75 verbatim
/-- Splitting a conjunction of sentences, kept at the level of `⊨` so that the
clause lemmas of this file still apply to the parts. -/
theorem realize_infS (φ ψ : L.Sentence) : (M ⊨ (φ ⊓ ψ)) ↔ ((M ⊨ φ) ∧ (M ⊨ ψ)) :=
  Formula.realize_inf


-- @@ L77-80 verbatim
@[simp]
theorem realize_atom₁ (r : L.Relations 1) (x : γ) :
    (atom₁ r x).Realize v ↔ RelMap r ![v x] := by
  simp only [atom₁, Formula.realize_rel₁, Term.realize_var]


-- @@ L82-85 verbatim
@[simp]
theorem realize_atom₂ (r : L.Relations 2) (x y : γ) :
    (atom₂ r x y).Realize v ↔ RelMap r ![v x, v y] := by
  simp only [atom₂, Formula.realize_rel₂, Term.realize_var]


-- @@ L87-89 verbatim
@[simp]
theorem realize_atomEq (x y : γ) : ((atomEq x y : L.Formula γ)).Realize v ↔ v x = v y := by
  rw [atomEq, Formula.realize_equal, Term.realize_var, Term.realize_var]


-- @@ L91-97 verbatim
@[simp]
theorem realize_minPosF (posn : L.Relations 1) (le : L.Relations 2) (x : γ) :
    (minPosF posn le x).Realize v ↔
      MinPos (fun a b : M => RelMap le ![a, b]) (fun a : M => RelMap posn ![a]) (v x) := by
  simp only [minPosF, MinPos, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_atom₁, realize_atom₂, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h q hq => h (fun _ => q) hq, fun h w hw => h (w 0) hw⟩


-- @@ L99-105 verbatim
@[simp]
theorem realize_maxPosF (posn : L.Relations 1) (le : L.Relations 2) (x : γ) :
    (maxPosF posn le x).Realize v ↔
      MaxPos (fun a b : M => RelMap le ![a, b]) (fun a : M => RelMap posn ![a]) (v x) := by
  simp only [maxPosF, MaxPos, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_atom₁, realize_atom₂, Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h q hq => h (fun _ => q) hq, fun h w hw => h (w 0) hw⟩


-- @@ L107-117 verbatim
@[simp]
theorem realize_succPosF (posn : L.Relations 1) (le : L.Relations 2) (x x' : γ) :
    (succPosF posn le x x').Realize v ↔
      SuccPos (fun a b : M => RelMap le ![a, b]) (fun a : M => RelMap posn ![a])
        (v x) (v x') := by
  simp only [succPosF, SuccPos, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_sup, realize_atom₁, realize_atom₂, realize_atomEq,
    Sum.elim_inl, Sum.elim_inr]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  exact ⟨fun h q hq h1 h2 => h (fun _ => q) ⟨hq, h1, h2⟩,
    fun h w hw => h (w 0) hw.1 hw.2.1 hw.2.2⟩


-- @@ L119-119 verbatim
end Shapes


-- @@ L121-121 verbatim
/-! ### What a row is, and what the walk asks of it -/


-- @@ L123-123 verbatim
section RowClauses


-- @@ L125-125 verbatim
variable {L : Language.{0, 0}}


-- @@ L127-129 expanded
/-- Every column of this row carries a tile of the instance. -/
noncomputable def rowTotalS (posn tile : L.Relations 1) (row : L.Relations 2) : L.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    (((atom₁ posn) (Sum.inr 0)).imp
      (FirstOrder.Language.Formula.iExs (Fin 1)
        ((atom₂ row) (Sum.inl (Sum.inr 0)) (Sum.inr 0) ⊓ (atom₁ tile) (Sum.inr 0))))


-- @@ L131-133 expanded
/-- And it carries only one. -/
noncomputable def rowFuncS (row : L.Relations 2) : L.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    (((atom₂ row) (Sum.inr 0) (Sum.inr 1) ⊓ (atom₂ row) (Sum.inr 0) (Sum.inr 2)).imp
      (atomEq (Sum.inr 1) (Sum.inr 2)))


-- @@ L135-139 expanded
/-- Neighboring columns of this row are compatible. -/
noncomputable def rowHorizS (posn : L.Relations 1) (le horiz row : L.Relations 2) : L.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
    (((succPosF posn le) (Sum.inr 0) (Sum.inr 1) ⊓
          ((atom₂ row) (Sum.inr 0) (Sum.inr 2) ⊓ (atom₂ row) (Sum.inr 1) (Sum.inr 3))).imp
      ((atom₂ horiz) (Sum.inr 2) (Sum.inr 3)))


-- @@ L141-144 expanded
/-- Its leftmost column carries a tile allowed there. -/
noncomputable def rowEdgeLS (posn ledge : L.Relations 1) (le row : L.Relations 2) : L.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    (((minPosF posn le) (Sum.inr 0) ⊓ (atom₂ row) (Sum.inr 0) (Sum.inr 1)).imp
      ((atom₁ ledge) (Sum.inr 1)))


-- @@ L146-149 expanded
/-- And its rightmost column one allowed there. -/
noncomputable def rowEdgeRS (posn redge : L.Relations 1) (le row : L.Relations 2) : L.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    (((maxPosF posn le) (Sum.inr 0) ⊓ (atom₂ row) (Sum.inr 0) (Sum.inr 1)).imp
      ((atom₁ redge) (Sum.inr 1)))


-- @@ L151-156 verbatim
/-- **Being a row**: one tile per column, horizontally compatible, with the
tiles the two edge columns allow. -/
noncomputable def rowLegalS (posn tile ledge redge : L.Relations 1)
    (le horiz row : L.Relations 2) : L.Sentence :=
  rowTotalS posn tile row ⊓ (rowFuncS row ⊓ (rowHorizS posn le horiz row ⊓
    (rowEdgeLS posn ledge le row ⊓ rowEdgeRS posn redge le row)))


-- @@ L158-165 expanded
/-- **Being the bottom row**: the corner carries a start tile and every other
column one the description allows there. -/
noncomputable def rowFirstS (posn start base : L.Relations 1) (le first row : L.Relations 2) :
    L.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    (((atom₁ posn) (Sum.inr 0) ⊓ (atom₂ row) (Sum.inr 0) (Sum.inr 1)).imp
      (((minPosF posn le) (Sum.inr 0)).imp ((atom₁ start) (Sum.inr 1)) ⊓
        (FirstOrder.Language.BoundedFormula.not ((minPosF posn le) (Sum.inr 0))).imp
          ((atom₂ first) (Sum.inr 0) (Sum.inr 1) ⊔
            FirstOrder.Language.Formula.iAlls (Fin 1)
                (FirstOrder.Language.BoundedFormula.not
                  ((atom₂ first) (Sum.inl (Sum.inr 0)) (Sum.inr 0))) ⊓
              (atom₁ base) (Sum.inr 1))))


-- @@ L167-169 expanded
/-- **Being an accepting row**: some column of it carries an accepting tile. -/
noncomputable def rowAccS (posn acc : L.Relations 1) (row : L.Relations 2) : L.Sentence :=
  FirstOrder.Language.Formula.iExs (Fin 2)
    ((atom₁ posn) (Sum.inr 0) ⊓ ((atom₂ row) (Sum.inr 0) (Sum.inr 1) ⊓ (atom₁ acc) (Sum.inr 1)))


-- @@ L171-176 expanded
/-- **One row above another**: every column's two tiles are vertically
compatible. -/
noncomputable def rowsVertS (posn : L.Relations 1) (vert rowCur rowNext : L.Relations 2) :
    L.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    (((atom₁ posn) (Sum.inr 0) ⊓
          ((atom₂ rowCur) (Sum.inr 0) (Sum.inr 1) ⊓ (atom₂ rowNext) (Sum.inr 0) (Sum.inr 2))).imp
      ((atom₂ vert) (Sum.inr 1) (Sum.inr 2)))


-- @@ L178-178 verbatim
end RowClauses


-- @@ L180-180 verbatim
/-! ### What each clause says -/


-- @@ L182-182 verbatim
section RowRealize


-- @@ L184-184 verbatim
variable {L : Language.{0, 0}} {M : Type} [L.Structure M]


-- @@ L186-197 verbatim
@[simp]
theorem realize_rowTotalS (posn tile : L.Relations 1) (row : L.Relations 2) :
    (M ⊨ rowTotalS posn tile row) ↔
      ∀ x : M, RelMap posn ![x] → ∃ t, RelMap row ![x, t] ∧ RelMap tile ![t] := by
  simp only [rowTotalS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, Formula.realize_inf, realize_atom₁, realize_atom₂,
    Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun h x hx => ?_, fun h w hw => ?_⟩
  · obtain ⟨w, hw⟩ := h (fun _ => x) hx
    exact ⟨w 0, hw⟩
  · obtain ⟨t, ht⟩ := h (w 0) hw
    exact ⟨fun _ => t, ht⟩


-- @@ L199-206 verbatim
@[simp]
theorem realize_rowFuncS (row : L.Relations 2) :
    (M ⊨ rowFuncS row) ↔
      ∀ x t t' : M, RelMap row ![x, t] → RelMap row ![x, t'] → t = t' := by
  simp only [rowFuncS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_atom₂, realize_atomEq, Sum.elim_inr]
  exact ⟨fun h x t t' h1 h2 => h ![x, t, t'] ⟨h1, h2⟩,
    fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩


-- @@ L208-217 verbatim
@[simp]
theorem realize_rowHorizS (posn : L.Relations 1) (le horiz row : L.Relations 2) :
    (M ⊨ rowHorizS posn le horiz row) ↔
      ∀ x x' t t' : M,
        SuccPos (fun a b : M => RelMap le ![a, b]) (fun a : M => RelMap posn ![a]) x x' →
        RelMap row ![x, t] → RelMap row ![x', t'] → RelMap horiz ![t, t'] := by
  simp only [rowHorizS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_atom₂, realize_succPosF, Sum.elim_inr]
  exact ⟨fun h x x' t t' h1 h2 h3 => h ![x, x', t, t'] ⟨h1, h2, h3⟩,
    fun h w hw => h (w 0) (w 1) (w 2) (w 3) hw.1 hw.2.1 hw.2.2⟩


-- @@ L219-227 verbatim
@[simp]
theorem realize_rowEdgeLS (posn ledge : L.Relations 1) (le row : L.Relations 2) :
    (M ⊨ rowEdgeLS posn ledge le row) ↔
      ∀ x t : M,
        MinPos (fun a b : M => RelMap le ![a, b]) (fun a : M => RelMap posn ![a]) x →
        RelMap row ![x, t] → RelMap ledge ![t] := by
  simp only [rowEdgeLS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_atom₁, realize_atom₂, realize_minPosF, Sum.elim_inr]
  exact ⟨fun h x t h1 h2 => h ![x, t] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩


-- @@ L229-237 verbatim
@[simp]
theorem realize_rowEdgeRS (posn redge : L.Relations 1) (le row : L.Relations 2) :
    (M ⊨ rowEdgeRS posn redge le row) ↔
      ∀ x t : M,
        MaxPos (fun a b : M => RelMap le ![a, b]) (fun a : M => RelMap posn ![a]) x →
        RelMap row ![x, t] → RelMap redge ![t] := by
  simp only [rowEdgeRS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_atom₁, realize_atom₂, realize_maxPosF, Sum.elim_inr]
  exact ⟨fun h x t h1 h2 => h ![x, t] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩


-- @@ L239-245 verbatim
@[simp]
theorem realize_rowAccS (posn acc : L.Relations 1) (row : L.Relations 2) :
    (M ⊨ rowAccS posn acc row) ↔
      ∃ x t : M, RelMap posn ![x] ∧ RelMap row ![x, t] ∧ RelMap acc ![t] := by
  simp only [rowAccS, Sentence.Realize, Formula.realize_iExs, Formula.realize_inf,
    realize_atom₁, realize_atom₂, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, w 1, hw⟩, fun ⟨x, t, hx⟩ => ⟨![x, t], hx⟩⟩


-- @@ L247-255 verbatim
@[simp]
theorem realize_rowsVertS (posn : L.Relations 1) (vert rowCur rowNext : L.Relations 2) :
    (M ⊨ rowsVertS posn vert rowCur rowNext) ↔
      ∀ x t t' : M, RelMap posn ![x] → RelMap rowCur ![x, t] → RelMap rowNext ![x, t'] →
        RelMap vert ![t, t'] := by
  simp only [rowsVertS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_atom₁, realize_atom₂, Sum.elim_inr]
  exact ⟨fun h x t t' h1 h2 h3 => h ![x, t, t'] ⟨h1, h2, h3⟩,
    fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2.1 hw.2.2⟩


-- @@ L257-281 verbatim
@[simp]
theorem realize_rowFirstS (posn start base : L.Relations 1) (le first row : L.Relations 2) :
    (M ⊨ rowFirstS posn start base le first row) ↔
      ∀ x t : M, RelMap posn ![x] → RelMap row ![x, t] →
        ((MinPos (fun a b : M => RelMap le ![a, b]) (fun a : M => RelMap posn ![a]) x →
            RelMap start ![t]) ∧
          (¬MinPos (fun a b : M => RelMap le ![a, b]) (fun a : M => RelMap posn ![a]) x →
            (RelMap first ![x, t] ∨
              ((∀ u : M, ¬RelMap first ![x, u]) ∧ RelMap base ![t])))) := by
  simp only [rowFirstS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_sup, Formula.realize_not, realize_atom₁,
    realize_atom₂, realize_minPosF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h x t h1 h2
    obtain ⟨hst, hfr⟩ := h ![x, t] ⟨h1, h2⟩
    refine ⟨hst, fun hmin => ?_⟩
    rcases hfr hmin with hf | ⟨hno, hb⟩
    · exact Or.inl hf
    · exact Or.inr ⟨fun u hu => hno (fun _ => u) hu, hb⟩
  · intro h w hw
    obtain ⟨hst, hfr⟩ := h (w 0) (w 1) hw.1 hw.2
    refine ⟨hst, fun hmin => ?_⟩
    rcases hfr hmin with hf | ⟨hno, hb⟩
    · exact Or.inl hf
    · exact Or.inr ⟨fun u hu => hno (u 0) hu, hb⟩


-- @@ L283-290 verbatim
@[simp]
theorem realize_rowLegalS (posn tile ledge redge : L.Relations 1)
    (le horiz row : L.Relations 2) :
    (M ⊨ rowLegalS posn tile ledge redge le horiz row) ↔
      ((M ⊨ rowTotalS posn tile row) ∧ (M ⊨ rowFuncS row) ∧
        (M ⊨ rowHorizS posn le horiz row) ∧ (M ⊨ rowEdgeLS posn ledge le row) ∧
        (M ⊨ rowEdgeRS posn redge le row)) := by
  simp only [rowLegalS, Sentence.Realize, Formula.realize_inf]


-- @@ L292-292 verbatim
end RowRealize


-- @@ L294-294 verbatim
/-! ### Well-formedness, as a sentence -/


-- @@ L296-296 verbatim
section WellFormed


-- @@ L298-298 verbatim
variable {L : Language.{0, 0}}


-- @@ L300-307 expanded
/-- The order is linear and there is a position: the promises the yes-instances
fold in. -/
noncomputable def orderWfS (posn : L.Relations 1) (le : L.Relations 2) : L.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) ((atom₂ le) (Sum.inr 0) (Sum.inr 0)) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 3)
          (((atom₂ le) (Sum.inr 0) (Sum.inr 1) ⊓ (atom₂ le) (Sum.inr 1) (Sum.inr 2)).imp
            ((atom₂ le) (Sum.inr 0) (Sum.inr 2))) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 2)
            (((atom₂ le) (Sum.inr 0) (Sum.inr 1) ⊓ (atom₂ le) (Sum.inr 1) (Sum.inr 0)).imp
              (atomEq (Sum.inr 0) (Sum.inr 1))) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 2)
            ((atom₂ le) (Sum.inr 0) (Sum.inr 1) ⊔ (atom₂ le) (Sum.inr 1) (Sum.inr 0)))) ⊓
    FirstOrder.Language.Formula.iExs (Fin 1) ((atom₁ posn) (Sum.inr 0))


-- @@ L309-309 verbatim
variable {M : Type} [L.Structure M]


-- @@ L311-324 verbatim
@[simp]
theorem realize_orderWfS (posn : L.Relations 1) (le : L.Relations 2) :
    (M ⊨ orderWfS posn le) ↔
      (IsLinOrd (fun a b : M => RelMap le ![a, b]) ∧ ∃ p : M, RelMap posn ![p]) := by
  simp only [orderWfS, Sentence.Realize, IsLinOrd, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_iExs, Formula.realize_imp, Formula.realize_sup, realize_atom₁,
    realize_atom₂, realize_atomEq, Sum.elim_inr]
  refine and_congr (and_congr ⟨fun h a => h fun _ => a, fun h w => h (w 0)⟩
      (and_congr ⟨fun h a b c h1 h2 => h ![a, b, c] ⟨h1, h2⟩,
          fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
        (and_congr ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩,
            fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
          ⟨fun h a b => h ![a, b], fun h w => h (w 0) (w 1)⟩))) ?_
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩


-- @@ L326-326 verbatim
end WellFormed


-- @@ L328-328 verbatim
/-! ### The specification -/


-- @@ L330-330 verbatim
section Spec


-- @@ L332-332 verbatim
open SOBlock


-- @@ L334-343 verbatim
/-- The block of the SO(TC) specification of the corridor: one binary relation
variable, read as “the column `x` of this row carries the tile `t`”.

Marked `@[reducible]` so that the numerals of a tuple of its arity elaborate:
without it `w 1` at the type `Fin (corBlock.arity i) → A` has no `OfNat`
instance. -/
@[reducible]
def corBlock : SOBlock where
  ι := Unit
  arity := fun _ => 2


-- @@ L345-346 verbatim
/-- The symbol of the row variable. -/
def corRowSym : corBlock.lang.Relations 2 := ⟨(), rfl⟩


-- @@ L348-350 verbatim
/-- The input vocabulary together with the order, over which the sentences of an
SO(TC) specification live. -/
abbrev corBase : Language := Language.tiling.sum Language.order


-- @@ L352-353 verbatim
/-- The vocabulary of the endpoint sentences: one copy of the block. -/
abbrev corLang₁ : Language := corBase.sum corBlock.lang


-- @@ L355-356 verbatim
/-- The vocabulary of the transition sentence: two copies of the block. -/
abbrev corLang₂ : Language := corLang₁.sum corBlock.lang


-- @@ L358-360 verbatim
/-- An input symbol, in the endpoint vocabulary. -/
abbrev corIn₁ {n : ℕ} (r : Language.tiling.Relations n) : corLang₁.Relations n :=
  Sum.inl (Sum.inl r)


-- @@ L362-364 verbatim
/-- An input symbol, in the transition vocabulary. -/
abbrev corIn₂ {n : ℕ} (r : Language.tiling.Relations n) : corLang₂.Relations n :=
  Sum.inl (Sum.inl (Sum.inl r))


-- @@ L366-367 verbatim
/-- The row variable, in the endpoint vocabulary. -/
abbrev corRow₁ : corLang₁.Relations 2 := Sum.inr corRowSym


-- @@ L369-370 verbatim
/-- The row variable of the *current* state, in the transition vocabulary. -/
abbrev corCur₂ : corLang₂.Relations 2 := Sum.inl (Sum.inr corRowSym)


-- @@ L372-373 verbatim
/-- The row variable of the *next* state, in the transition vocabulary. -/
abbrev corNext₂ : corLang₂.Relations 2 := Sum.inr corRowSym


-- @@ L375-392 verbatim
/-- **The SO(TC) specification of the corridor.** The states are the rows: a
starting state is a row the bottom-row description allows, a transition is the
vertical compatibility with a row entering it, and an accepting state is a row
carrying an accepting tile. Being a row is asked of the source and of every
state a transition enters, so every reachable state is one. -/
noncomputable def corSpec : SOTCSpec Language.tiling where
  B := corBlock
  step :=
    rowLegalS (corIn₂ tlPosn) (corIn₂ tlTile) (corIn₂ tlEdgeL) (corIn₂ tlEdgeR)
        (corIn₂ tlLe) (corIn₂ tlHoriz) corNext₂ ⊓
      rowsVertS (corIn₂ tlPosn) (corIn₂ tlVert) corCur₂ corNext₂
  src :=
    orderWfS (corIn₁ tlPosn) (corIn₁ tlLe) ⊓
      (rowLegalS (corIn₁ tlPosn) (corIn₁ tlTile) (corIn₁ tlEdgeL) (corIn₁ tlEdgeR)
          (corIn₁ tlLe) (corIn₁ tlHoriz) corRow₁ ⊓
        rowFirstS (corIn₁ tlPosn) (corIn₁ tlStart) (corIn₁ tlBase) (corIn₁ tlLe)
          (corIn₁ tlFirst) corRow₁)
  tgt := rowAccS (corIn₁ tlPosn) (corIn₁ tlAcc) corRow₁


-- @@ L394-394 verbatim
end Spec


-- @@ L396-396 verbatim
/-! ### Reading the specification back -/


-- @@ L398-398 verbatim
section Reading


-- @@ L400-400 verbatim
open SOBlock


-- @@ L402-402 verbatim
variable {A : Type} [Language.tiling.Structure A] [LinearOrder A]


-- @@ L404-405 verbatim
/-- The row an assignment is. -/
def corRow (ρ : corBlock.Assignment A) : A → A → Prop := fun x t => ρ () ![x, t]


-- @@ L407-415 verbatim
/-- **Being a row**: one tile per column, horizontally compatible, with the
tiles the two edge columns allow. -/
def RowLegal (R : A → A → Prop) : Prop :=
  (∀ x, TLPosn x → ∃ t, R x t ∧ TLTile t) ∧
    (∀ x t t', R x t → R x t' → t = t') ∧
    (∀ x x' t t', SuccPos (tileData A).Le (tileData A).Posn x x' → R x t → R x' t' →
      TLHoriz t t') ∧
    (∀ x t, MinPos (tileData A).Le (tileData A).Posn x → R x t → TLEdgeL t) ∧
    (∀ x t, MaxPos (tileData A).Le (tileData A).Posn x → R x t → TLEdgeR t)


-- @@ L417-422 verbatim
/-- **Being the bottom row**: the corner carries a start tile, every other
column one the description allows there. -/
def RowFirst (R : A → A → Prop) : Prop :=
  ∀ x t, TLPosn x → R x t →
    ((MinPos (tileData A).Le (tileData A).Posn x → TLStart t) ∧
      (¬MinPos (tileData A).Le (tileData A).Posn x → (tileData A).FirstTile x t))


-- @@ L424-428 verbatim
@[simp]
theorem relMap_corIn₁ {n : ℕ} (ρ : corBlock.Assignment A)
    (r : Language.tiling.Relations n) (w : Fin n → A) :
    @RelMap corLang₁ A (corBlock.structure₁ (L := corBase) ρ) n (corIn₁ r) w ↔
      RelMap r w := Iff.rfl


-- @@ L430-433 verbatim
@[simp]
theorem relMap_corRow₁ (ρ : corBlock.Assignment A) (w : Fin 2 → A) :
    @RelMap corLang₁ A (corBlock.structure₁ (L := corBase) ρ) 2 corRow₁ w ↔ ρ () w :=
  Iff.rfl


-- @@ L435-439 verbatim
@[simp]
theorem relMap_corIn₂ {n : ℕ} (ρ σ : corBlock.Assignment A)
    (r : Language.tiling.Relations n) (w : Fin n → A) :
    @RelMap corLang₂ A (corBlock.structure₂ (L := corBase) ρ σ) n (corIn₂ r) w ↔
      RelMap r w := Iff.rfl


-- @@ L441-444 verbatim
@[simp]
theorem relMap_corCur₂ (ρ σ : corBlock.Assignment A) (w : Fin 2 → A) :
    @RelMap corLang₂ A (corBlock.structure₂ (L := corBase) ρ σ) 2 corCur₂ w ↔ ρ () w :=
  Iff.rfl


-- @@ L446-449 verbatim
@[simp]
theorem relMap_corNext₂ (ρ σ : corBlock.Assignment A) (w : Fin 2 → A) :
    @RelMap corLang₂ A (corBlock.structure₂ (L := corBase) ρ σ) 2 corNext₂ w ↔ σ () w :=
  Iff.rfl


-- @@ L451-461 verbatim
/-- **What a starting state is**: the instance is well-formed and the state is
the bottom row. -/
theorem isSrc_iff (ρ : corBlock.Assignment A) :
    corSpec.IsSrc ρ ↔
      ((tileData A).WellFormed ∧ (RowLegal (corRow ρ) ∧ RowFirst (corRow ρ))) := by
  change @Sentence.Realize corLang₁ A (corBlock.structure₁ (L := corBase) ρ) corSpec.src ↔ _
  simp only [corSpec]
  simp only [realize_infS, realize_orderWfS, realize_rowLegalS,
    realize_rowFirstS, realize_rowTotalS, realize_rowFuncS, realize_rowHorizS,
    realize_rowEdgeLS, realize_rowEdgeRS, relMap_corIn₁, relMap_corRow₁]
  rfl


-- @@ L463-474 verbatim
/-- **What a transition is**: the state entered is a row, and it stands above
the state left. -/
theorem step_iff (ρ σ : corBlock.Assignment A) :
    corSpec.Step ρ σ ↔
      (RowLegal (corRow σ) ∧
        ∀ x t t', TLPosn x → corRow ρ x t → corRow σ x t' → TLVert t t') := by
  change @Sentence.Realize corLang₂ A (corBlock.structure₂ (L := corBase) ρ σ) corSpec.step ↔ _
  simp only [corSpec]
  simp only [realize_infS, realize_rowLegalS, realize_rowsVertS,
    realize_rowTotalS, realize_rowFuncS, realize_rowHorizS, realize_rowEdgeLS,
    realize_rowEdgeRS, relMap_corIn₂, relMap_corCur₂, relMap_corNext₂]
  rfl


-- @@ L476-482 verbatim
/-- **What an accepting state is**: a row with an accepting tile in it. -/
theorem isTgt_iff (ρ : corBlock.Assignment A) :
    corSpec.IsTgt ρ ↔ ∃ x t, TLPosn x ∧ corRow ρ x t ∧ TLAcc t := by
  change @Sentence.Realize corLang₁ A (corBlock.structure₁ (L := corBase) ρ) corSpec.tgt ↔ _
  simp only [corSpec]
  simp only [realize_rowAccS, relMap_corIn₁, relMap_corRow₁]
  rfl


-- @@ L484-484 verbatim
end Reading


-- @@ L486-486 verbatim
/-! ### The walk is the corridor -/


-- @@ L488-488 verbatim
section Equivalence


-- @@ L490-490 verbatim
open SOBlock


-- @@ L492-492 verbatim
variable {A : Type} [Language.tiling.Structure A] [LinearOrder A]


-- @@ L494-495 verbatim
/-- The assignment a row of a corridor is. -/
def corAsg (τ : ℕ → A → A) (k : ℕ) : corBlock.Assignment A := fun _ w => w 1 = τ k (w 0)


-- @@ L497-500 verbatim
omit [Language.tiling.Structure A] [LinearOrder A] in
@[simp]
theorem corRow_corAsg (τ : ℕ → A → A) (k : ℕ) (x t : A) :
    corRow (corAsg τ k) x t ↔ t = τ k x := Iff.rfl


-- @@ L502-541 verbatim
/-- **A corridor is a walk**: its rows, read as assignments, start at a
bottom row, step one above the other, and end at a row with an accepting
tile. -/
theorem accepts_of_corridor (hwf : (tileData A).WellFormed)
    (h : (tileData A).CorridorTileable) : corSpec.Accepts A := by
  obtain ⟨n, τ, htiles, hfst, hel, her, hhor, hver, xa, hxa, hacc⟩ := h
  have hlegal : ∀ k, k ≤ n → RowLegal (corRow (corAsg τ k)) := by
    intro k hk
    exact ⟨fun x hx => ⟨τ k x, rfl, htiles k x hk hx⟩,
      fun x t t' h1 h2 => h1.trans h2.symm,
      fun x x' t t' hs h1 h2 => by
        have e1 : t = τ k x := h1
        have e2 : t' = τ k x' := h2
        rw [e1, e2]
        exact hhor k x x' hk hs,
      fun x t hmin h1 => by
        have e1 : t = τ k x := h1
        rw [e1]
        exact hel k x hk hmin,
      fun x t hmax h1 => by
        have e1 : t = τ k x := h1
        rw [e1]
        exact her k x hk hmax⟩
  have hreach : ∀ k, k ≤ n → corSpec.Reach (corAsg τ 0) (corAsg τ k) := by
    intro k
    induction k with
    | zero => exact fun _ => Relation.ReflTransGen.refl
    | succ m ih =>
      intro hm
      refine (ih (by omega)).tail ((step_iff _ _).mpr ⟨hlegal (m + 1) hm, ?_⟩)
      intro x t t' hx h1 h2
      have e1 : t = τ m x := h1
      have e2 : t' = τ (m + 1) x := h2
      rw [e1, e2]
      exact hver m x (by omega) hx
  refine ⟨corAsg τ 0, corAsg τ n, (isSrc_iff _).mpr ⟨hwf, hlegal 0 (Nat.zero_le _), ?_⟩,
    (isTgt_iff _).mpr ⟨xa, τ n xa, hxa, rfl, hacc⟩, hreach n le_rfl⟩
  intro x t hx ht
  rw [show t = τ 0 x from ht]
  exact hfst x hx


-- @@ L543-546 verbatim
open Classical in
/-- The tile a row puts in a column, read off the relation the walk carries. -/
noncomputable def rowFun (R : A → A → Prop) : A → A :=
  fun x => if h : ∃ t, R x t then h.choose else x


-- @@ L548-552 verbatim
omit [Language.tiling.Structure A] [LinearOrder A] in
theorem rowFun_spec {R : A → A → Prop} {x : A} (h : ∃ t, R x t) : R x (rowFun R x) := by
  classical
  rw [rowFun, dite_eq_left h]
  exact h.choose_spec


-- @@ L554-566 verbatim
/-- **The corridor a walk has built so far**, with the row it has reached on
top: the induction invariant of `DescriptiveComplexity.corridor_of_accepts`. -/
def CorridorTo (n : ℕ) (τ : ℕ → A → A) (σ : corBlock.Assignment A) : Prop :=
  (∀ k x, k ≤ n → TLPosn x → TLTile (τ k x)) ∧
    (∀ x, TLPosn x →
      ((MinPos (tileData A).Le (tileData A).Posn x → TLStart (τ 0 x)) ∧
        (¬MinPos (tileData A).Le (tileData A).Posn x → (tileData A).FirstTile x (τ 0 x)))) ∧
    (∀ k x, k ≤ n → MinPos (tileData A).Le (tileData A).Posn x → TLEdgeL (τ k x)) ∧
    (∀ k x, k ≤ n → MaxPos (tileData A).Le (tileData A).Posn x → TLEdgeR (τ k x)) ∧
    (∀ k x x', k ≤ n → SuccPos (tileData A).Le (tileData A).Posn x x' →
      TLHoriz (τ k x) (τ k x')) ∧
    (∀ k x, k < n → TLPosn x → TLVert (τ k x) (τ (k + 1) x)) ∧
    RowLegal (corRow σ) ∧ ∀ x, TLPosn x → corRow σ x (τ n x)


-- @@ L568-635 verbatim
/-- **A row a walk reaches stands on a corridor**: the rows it went through are
its cells, and the row itself is its top. -/
theorem exists_corridorTo {ρ σ : corBlock.Assignment A} (hsrc : corSpec.IsSrc ρ)
    (hreach : corSpec.Reach ρ σ) : ∃ (n : ℕ) (τ : ℕ → A → A), CorridorTo n τ σ := by
  classical
  obtain ⟨hwf, hlegal, hfirst⟩ := (isSrc_iff ρ).mp hsrc
  induction hreach with
  | refl =>
    refine ⟨0, fun _ => rowFun (corRow ρ), ?_, ?_, ?_, ?_, ?_, ?_, hlegal, ?_⟩
    · intro k x _ hx
      obtain ⟨t, ht, htile⟩ := hlegal.1 x hx
      change TLTile (rowFun (corRow ρ) x)
      rw [hlegal.2.1 x (rowFun (corRow ρ) x) t (rowFun_spec ⟨t, ht⟩) ht]
      exact htile
    · exact fun x hx => hfirst x _ hx (rowFun_spec ((hlegal.1 x hx).imp fun _ h => h.1))
    · exact fun k x _ hmin =>
        hlegal.2.2.2.1 x _ hmin (rowFun_spec ((hlegal.1 x hmin.1).imp fun _ h => h.1))
    · exact fun k x _ hmax =>
        hlegal.2.2.2.2 x _ hmax (rowFun_spec ((hlegal.1 x hmax.1).imp fun _ h => h.1))
    · exact fun k x x' _ hs =>
        hlegal.2.2.1 x x' _ _ hs (rowFun_spec ((hlegal.1 x hs.1).imp fun _ h => h.1))
          (rowFun_spec ((hlegal.1 x' hs.2.1).imp fun _ h => h.1))
    · exact fun k x hk _ => absurd hk (by omega)
    · exact fun x hx => rowFun_spec ((hlegal.1 x hx).imp fun _ h => h.1)
  | @tail c d hreach hstep ih =>
    obtain ⟨n, τ, h1, h2, h3, h4, h5, h6, hc, htop⟩ := ih
    obtain ⟨hdlegal, hdvert⟩ := (step_iff c d).mp hstep
    have hspec : ∀ x, TLPosn x → corRow d x (rowFun (corRow d) x) :=
      fun x hx => rowFun_spec ((hdlegal.1 x hx).imp fun _ h => h.1)
    refine ⟨n + 1, fun k => if k = n + 1 then rowFun (corRow d) else τ k, ?_, ?_, ?_, ?_, ?_,
      ?_, hdlegal, ?_⟩
    · intro k x hk hx
      by_cases hkn : k = n + 1
      · simp only [ite_eq_left hkn]
        obtain ⟨t, ht, htile⟩ := hdlegal.1 x hx
        rw [hdlegal.2.1 x (rowFun (corRow d) x) t (hspec x hx) ht]
        exact htile
      · simp only [ite_eq_right hkn]
        exact h1 k x (by omega) hx
    · simpa only [ite_eq_right (by omega : (0 : ℕ) ≠ n + 1)] using h2
    · intro k x hk hmin
      by_cases hkn : k = n + 1
      · simp only [ite_eq_left hkn]
        exact hdlegal.2.2.2.1 x _ hmin (hspec x hmin.1)
      · simp only [ite_eq_right hkn]
        exact h3 k x (by omega) hmin
    · intro k x hk hmax
      by_cases hkn : k = n + 1
      · simp only [ite_eq_left hkn]
        exact hdlegal.2.2.2.2 x _ hmax (hspec x hmax.1)
      · simp only [ite_eq_right hkn]
        exact h4 k x (by omega) hmax
    · intro k x x' hk hs
      by_cases hkn : k = n + 1
      · simp only [ite_eq_left hkn]
        exact hdlegal.2.2.1 x x' _ _ hs (hspec x hs.1) (hspec x' hs.2.1)
      · simp only [ite_eq_right hkn]
        exact h5 k x x' (by omega) hs
    · intro k x hk hx
      by_cases hkn : k = n
      · subst hkn
        simp only [ite_eq_right (by omega : k ≠ k + 1)]
        exact hdvert x (τ k x) _ hx (htop x hx) (hspec x hx)
      · have hk1 : k + 1 ≠ n + 1 := by omega
        simp only [ite_eq_right (by omega : k ≠ n + 1), ite_eq_right hk1]
        exact h6 k x (by omega) hx
    · intro x hx
      simpa using hspec x hx


-- @@ L637-648 verbatim
/-- **A walk is a corridor**: the rows it goes through tile one, up to the row
where the accepting tile stands. -/
theorem corridor_of_accepts (h : corSpec.Accepts A) :
    (tileData A).WellFormed ∧ (tileData A).CorridorTileable := by
  obtain ⟨ρ, σ, hsrc, htgt, hreach⟩ := h
  obtain ⟨hwf, -, -⟩ := (isSrc_iff ρ).mp hsrc
  obtain ⟨n, τ, h1, h2, h3, h4, h5, h6, hlegal, htop⟩ := exists_corridorTo hsrc hreach
  obtain ⟨x, t, hx, hrow, hacc⟩ := (isTgt_iff σ).mp htgt
  refine ⟨hwf, n, τ, h1, h2, h3, h4, h5, h6, x, hx, ?_⟩
  have heq : τ n x = t := hlegal.2.1 x (τ n x) t (htop x hx) hrow
  rw [heq]
  exact hacc


-- @@ L650-654 verbatim
/-- **Tiling a corridor is SO(TC) definable**: the walk on rows is the
corridor. -/
theorem corridor_sotcDefinable : SOTCDefinable CORRIDOR := by
  refine ⟨corSpec, fun A _ _ _ _ => ⟨fun h => accepts_of_corridor h.1 h.2, ?_⟩⟩
  exact fun h => corridor_of_accepts h


-- @@ L656-657 verbatim
/-- **Tiling a corridor is in PSPACE.** -/
theorem corridor_mem_PSPACE : CORRIDOR ∈ PSPACE := corridor_sotcDefinable


-- @@ L659-659 verbatim
end Equivalence


-- @@ L661-661 verbatim
end DescriptiveComplexity
