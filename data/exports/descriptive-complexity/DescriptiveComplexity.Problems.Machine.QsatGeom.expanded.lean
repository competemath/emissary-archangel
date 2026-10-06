/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.QsatProgram


-- @@ L8-32 verbatim
/-!
# The geometry of the QBF machine's tape

Where the cells sit: which tagged tuples are positions, which is the lowest and
which the highest, and what the immediate neighbor of each one is. Everything
the run needs to know about *movement*, proved once, before any transition is
taken.

The content is that the tape

```
  ⊢   v₁ v₂ … vₙ   ⊣
```

is exactly the position order `DescriptiveComplexity.QsatTM.QLe`: the left marker
is `DescriptiveComplexity.MinPos`, the right marker is `DescriptiveComplexity.MaxPos`,
and `DescriptiveComplexity.SuccPos` steps from the left marker to the outermost
variable, from a variable to the next one the prefix binds, and from the
innermost variable to the right marker. The degenerate instance – no quantified
variable at all – is the case where the two markers are neighbors.

All of it needs the instance to be well formed, since that is exactly when the
prefix order is a linear order on the variables and `QLe` is a linear order at
all (`DescriptiveComplexity.QsatTM.isLinOrd_qLe`).
-/


-- @@ L34-34 verbatim
namespace DescriptiveComplexity


-- @@ L36-36 verbatim
open FirstOrder


-- @@ L38-38 verbatim
open Language Structure


-- @@ L40-40 verbatim
namespace QsatTM


-- @@ L42-42 verbatim
/-! ### The three position tags, compared -/


-- @@ L44-44 verbatim
private theorem tag_lt_sc : qTagIdx QTag.pStart < qTagIdx QTag.pCell := by decide

-- @@ L45-45 verbatim
private theorem tag_lt_se : qTagIdx QTag.pStart < qTagIdx QTag.pEnd := by decide

-- @@ L46-46 verbatim
private theorem tag_lt_ce : qTagIdx QTag.pCell < qTagIdx QTag.pEnd := by decide

-- @@ L47-47 verbatim
private theorem tag_nlt_cs : ¬qTagIdx QTag.pCell < qTagIdx QTag.pStart := by decide

-- @@ L48-48 verbatim
private theorem tag_nlt_ec : ¬qTagIdx QTag.pEnd < qTagIdx QTag.pCell := by decide

-- @@ L49-49 verbatim
private theorem tag_nlt_es : ¬qTagIdx QTag.pEnd < qTagIdx QTag.pStart := by decide

-- @@ L50-50 verbatim
private theorem tag_ne_cs : QTag.pCell ≠ QTag.pStart := by decide

-- @@ L51-51 verbatim
private theorem tag_ne_ec : QTag.pEnd ≠ QTag.pCell := by decide

-- @@ L52-52 verbatim
private theorem tag_ne_es : QTag.pEnd ≠ QTag.pStart := by decide


-- @@ L54-54 verbatim
noncomputable section Geometry


-- @@ L56-56 verbatim
variable {A : Type} [Language.qsat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]


-- @@ L58-58 verbatim
/-! ### Walking the quantifier prefix -/


-- @@ L60-61 verbatim
/-- `x` is the variable the prefix binds first. -/
def QMinVar (x : A) : Prop := IsQVar x ∧ ∀ y : A, IsQVar y → ¬QPrec y x


-- @@ L63-64 verbatim
/-- `x` is the variable the prefix binds last. -/
def QMaxVar (x : A) : Prop := IsQVar x ∧ ∀ y : A, IsQVar y → ¬QPrec x y


-- @@ L66-68 verbatim
/-- `y` is the variable the prefix binds immediately after `x`. -/
def QNextVar (x y : A) : Prop :=
  IsQVar x ∧ IsQVar y ∧ QPrec x y ∧ ∀ z : A, IsQVar z → QPrec x z → QPrec z y → False


-- @@ L70-70 verbatim
/-! ### The positions -/


-- @@ L72-75 verbatim
omit [Language.qsat.Structure A] in
/-- A tuple pinned at both coordinates is the tuple of least elements. -/
theorem eq_qBot_tup {w : Fin 2 → A} (h : IsMinTup w) : w = fun _ => qBot :=
  isMinTup_unique h isMinTup_qBot


-- @@ L77-77 verbatim
theorem qPosn_posStart : QPosn (posStart : QV A) := isMinTup_qBot


-- @@ L79-79 verbatim
theorem qPosn_posEnd : QPosn (posEnd : QV A) := isMinTup_qBot


-- @@ L81-82 verbatim
theorem qPosn_posCell {x : A} (hx : IsQVar x) : QPosn (posCell x : QV A) :=
  ⟨hx, fun a => qBot_le a⟩


-- @@ L84-102 verbatim
/-- **The positions of the tape, listed**: the two markers and one cell per
quantified variable. -/
theorem qPosn_iff (p : QV A) :
    QPosn p ↔ (p = posStart ∨ (∃ x : A, IsQVar x ∧ p = posCell x) ∨ p = posEnd) := by
  constructor
  · intro h
    obtain ⟨t, w⟩ := p
    cases t <;> dsimp only [QPosn] at h
    case pStart => exact Or.inl (Prod.ext rfl (eq_qBot_tup h))
    case pCell =>
      refine Or.inr (Or.inl ⟨w 0, h.1, Prod.ext rfl (funext fun i => ?_)⟩)
      fin_cases i
      · rfl
      · exact le_antisymm (h.2 _) (qBot_le _)
    case pEnd => exact Or.inr (Or.inr (Prod.ext rfl (eq_qBot_tup h)))
  · rintro (rfl | ⟨x, hx, rfl⟩ | rfl)
    · exact qPosn_posStart
    · exact qPosn_posCell hx
    · exact qPosn_posEnd


-- @@ L104-104 verbatim
/-! ### Comparing positions -/


-- @@ L106-121 verbatim
/-- Between two cells the tape order is the prefix order. -/
theorem qLe_posCell_iff (hwf : QsatWf A) {x y : A} :
    QLe (posCell x : QV A) (posCell y) ↔ PLe x y := by
  have hrefl := (isLinOrd_pLe A hwf).1
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact absurd h (Nat.lt_irrefl _)
    · rcases h with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · have hxy : x = y := h
        exact hxy ▸ hrefl x
  · intro h
    refine Or.inr ⟨rfl, ?_⟩
    rcases eq_or_ne x y with rfl | hne
    · exact Or.inr ⟨rfl, hrefl _⟩
    · exact Or.inl ⟨h, hne⟩


-- @@ L123-125 verbatim
omit [Finite A] [Nonempty A] in
/-- A tag strictly lower in the index order is lower on the tape. -/
theorem qLe_of_tagIdx_lt {p q : QV A} (h : qTagIdx p.1 < qTagIdx q.1) : QLe p q := Or.inl h


-- @@ L127-129 verbatim
omit [Finite A] [Nonempty A] in
/-- The tape order is reflexive on a well-formed instance. -/
theorem qLe_refl (hwf : QsatWf A) (p : QV A) : QLe p p := (isLinOrd_qLe A hwf).1 p


-- @@ L131-132 verbatim
theorem qLe_start_cell (x : A) : QLe (posStart : QV A) (posCell x) :=
  qLe_of_tagIdx_lt tag_lt_sc


-- @@ L134-134 verbatim
theorem qLe_start_end : QLe (posStart : QV A) posEnd := qLe_of_tagIdx_lt tag_lt_se


-- @@ L136-137 verbatim
theorem qLe_cell_end (x : A) : QLe (posCell x : QV A) posEnd :=
  qLe_of_tagIdx_lt tag_lt_ce


-- @@ L139-142 verbatim
theorem not_qLe_cell_start (x : A) : ¬QLe (posCell x : QV A) posStart := by
  rintro (h | ⟨h, -⟩)
  · exact tag_nlt_cs h
  · exact tag_ne_cs h


-- @@ L144-147 verbatim
theorem not_qLe_end_cell (x : A) : ¬QLe (posEnd : QV A) (posCell x) := by
  rintro (h | ⟨h, -⟩)
  · exact tag_nlt_ec h
  · exact tag_ne_ec h


-- @@ L149-152 verbatim
theorem not_qLe_end_start : ¬QLe (posEnd : QV A) posStart := by
  rintro (h | ⟨h, -⟩)
  · exact tag_nlt_es h
  · exact tag_ne_es h


-- @@ L154-154 verbatim
/-! ### The ends of the tape -/


-- @@ L156-162 verbatim
/-- **The left marker is the lowest position.** -/
theorem minPos_posStart (hwf : QsatWf A) : MinPos (QLe (A := A)) QPosn posStart := by
  refine ⟨qPosn_posStart, fun q hq => ?_⟩
  rcases (qPosn_iff q).mp hq with rfl | ⟨x, -, rfl⟩ | rfl
  · exact qLe_refl hwf _
  · exact qLe_start_cell x
  · exact qLe_start_end


-- @@ L164-170 verbatim
/-- **The right marker is the highest position.** -/
theorem maxPos_posEnd (hwf : QsatWf A) : MaxPos (QLe (A := A)) QPosn posEnd := by
  refine ⟨qPosn_posEnd, fun q hq => ?_⟩
  rcases (qPosn_iff q).mp hq with rfl | ⟨x, -, rfl⟩ | rfl
  · exact qLe_start_end
  · exact qLe_cell_end x
  · exact qLe_refl hwf _


-- @@ L172-172 verbatim
/-! ### Neighbors -/


-- @@ L174-174 verbatim
end Geometry


-- @@ L176-176 verbatim
end QsatTM


-- @@ L178-178 verbatim
end DescriptiveComplexity
