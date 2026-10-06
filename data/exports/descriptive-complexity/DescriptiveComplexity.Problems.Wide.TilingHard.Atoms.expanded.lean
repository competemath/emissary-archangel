/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Wide.TilingHard.Emit


-- @@ L9-25 verbatim
/-!
# The atoms the drawing is written with

The vocabulary a reduction *from* a wide machine writes its formulas in: the
machine's own relations, over the ordered expansion `Language.wide.sum
Language.order`, one shorthand each, together with the two shapes every tile
formula is built from –

* a **static** choice on the tags, `DescriptiveComplexity.TilingHard.tagIfF`,
  which is where all the case analysis of the drawing goes;
* the machine's promises as a sentence,
  `DescriptiveComplexity.TilingHard.wideWFF`, which the start tile carries.

Everything here is about the *source* of the reduction, so it says nothing about
tiles; the formulas that draw them are in
`DescriptiveComplexity.Problems.Wide.TilingHard.Draw`.
-/


-- @@ L27-27 verbatim
namespace DescriptiveComplexity


-- @@ L29-29 verbatim
open FirstOrder


-- @@ L31-31 verbatim
open Language Structure


-- @@ L33-33 verbatim
namespace TilingHard


-- @@ L35-37 verbatim
/-- The vocabulary the drawing's formulas are written in: the machine's, with
the order of the instance. -/
abbrev wideOrd : Language.{0, 0} := Language.wide.sum Language.order


-- @@ L39-39 verbatim
/-! ### The machine's relations, as atoms -/


-- @@ L41-41 verbatim
section Atoms


-- @@ L43-44 verbatim
/-- The order symbol of the machine, in the drawing's vocabulary. -/
abbrev wdLeSym : wideOrd.Relations 2 := Sum.inl wmLe


-- @@ L46-47 verbatim
/-- The transition symbol, in the drawing's vocabulary. -/
abbrev wdTrSym : wideOrd.Relations 1 := Sum.inl wmTr


-- @@ L49-50 verbatim
/-- The start-state symbol, in the drawing's vocabulary. -/
abbrev wdStartSym : wideOrd.Relations 1 := Sum.inl wmStart


-- @@ L52-53 verbatim
/-- The accepting-state symbol, in the drawing's vocabulary. -/
abbrev wdAccSym : wideOrd.Relations 1 := Sum.inl wmAcc


-- @@ L55-56 verbatim
/-- The blank symbol, in the drawing's vocabulary. -/
abbrev wdBlankSym : wideOrd.Relations 1 := Sum.inl wmBlank


-- @@ L58-59 verbatim
/-- The right-move symbol, in the drawing's vocabulary. -/
abbrev wdRightSym : wideOrd.Relations 1 := Sum.inl wmRight


-- @@ L61-62 verbatim
/-- The source-state symbol, in the drawing's vocabulary. -/
abbrev wdSrcSym : wideOrd.Relations 2 := Sum.inl wmSrc


-- @@ L64-65 verbatim
/-- The read-symbol symbol, in the drawing's vocabulary. -/
abbrev wdReadSym : wideOrd.Relations 2 := Sum.inl wmRead


-- @@ L67-68 verbatim
/-- The destination-state symbol, in the drawing's vocabulary. -/
abbrev wdDstSym : wideOrd.Relations 2 := Sum.inl wmDst


-- @@ L70-71 verbatim
/-- The written-symbol symbol, in the drawing's vocabulary. -/
abbrev wdWriteSym : wideOrd.Relations 2 := Sum.inl wmWrite


-- @@ L73-74 verbatim
/-- The input symbol, in the drawing's vocabulary. -/
abbrev wdInpSym : wideOrd.Relations 2 := Sum.inl wmInp


-- @@ L76-76 verbatim
variable {γ : Type}


-- @@ L78-79 expanded
/-- `x ≤ y` in the machine's own order. -/
noncomputable def wdLeF (x y : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ wdLeSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L81-82 expanded
/-- `t` is a transition. -/
noncomputable def wdTrF (t : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ wdTrSym (FirstOrder.Language.Term.var t)


-- @@ L84-85 expanded
/-- `q` is a start state. -/
noncomputable def wdStartF (q : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ wdStartSym (FirstOrder.Language.Term.var q)


-- @@ L87-88 expanded
/-- `q` is an accepting state. -/
noncomputable def wdAccF (q : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ wdAccSym (FirstOrder.Language.Term.var q)


-- @@ L90-91 expanded
/-- `a` is the blank symbol. -/
noncomputable def wdBlankF (a : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ wdBlankSym (FirstOrder.Language.Term.var a)


-- @@ L93-94 expanded
/-- `t` moves the head to the right. -/
noncomputable def wdRightF (t : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ wdRightSym (FirstOrder.Language.Term.var t)


-- @@ L96-97 expanded
/-- `t` applies in the state `q`. -/
noncomputable def wdSrcF (t q : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ wdSrcSym (FirstOrder.Language.Term.var t)
    (FirstOrder.Language.Term.var q)


-- @@ L99-100 expanded
/-- `t` applies on the symbol `a`. -/
noncomputable def wdReadF (t a : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ wdReadSym (FirstOrder.Language.Term.var t)
    (FirstOrder.Language.Term.var a)


-- @@ L102-103 expanded
/-- `t` moves to the state `q`. -/
noncomputable def wdDstF (t q : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ wdDstSym (FirstOrder.Language.Term.var t)
    (FirstOrder.Language.Term.var q)


-- @@ L105-106 expanded
/-- `t` writes the symbol `a`. -/
noncomputable def wdWriteF (t a : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ wdWriteSym (FirstOrder.Language.Term.var t)
    (FirstOrder.Language.Term.var a)


-- @@ L108-109 expanded
/-- The cell of `x` starts holding `a`. -/
noncomputable def wdInpF (x a : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ wdInpSym (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var a)


-- @@ L111-112 expanded
/-- `x` and `y` are the same element. -/
noncomputable def wdEqF (x y : γ) : wideOrd.Formula γ :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)


-- @@ L114-114 verbatim
variable {A : Type} [Language.wide.Structure A] [LinearOrder A] {v : γ → A}


-- @@ L116-119 verbatim
@[simp]
theorem realize_wdLeF (x y : γ) : (wdLeF x y).Realize v ↔ WMLe (v x) (v y) := by
  simp only [wdLeF, Formula.realize_rel₂]
  rfl


-- @@ L121-124 verbatim
@[simp]
theorem realize_wdTrF (t : γ) : (wdTrF t).Realize v ↔ WMTr (v t) := by
  simp only [wdTrF, Formula.realize_rel₁]
  rfl


-- @@ L126-129 verbatim
@[simp]
theorem realize_wdStartF (q : γ) : (wdStartF q).Realize v ↔ WMStart (v q) := by
  simp only [wdStartF, Formula.realize_rel₁]
  rfl


-- @@ L131-134 verbatim
@[simp]
theorem realize_wdAccF (q : γ) : (wdAccF q).Realize v ↔ WMAcc (v q) := by
  simp only [wdAccF, Formula.realize_rel₁]
  rfl


-- @@ L136-139 verbatim
@[simp]
theorem realize_wdBlankF (a : γ) : (wdBlankF a).Realize v ↔ WMBlank (v a) := by
  simp only [wdBlankF, Formula.realize_rel₁]
  rfl


-- @@ L141-144 verbatim
@[simp]
theorem realize_wdRightF (t : γ) : (wdRightF t).Realize v ↔ WMRight (v t) := by
  simp only [wdRightF, Formula.realize_rel₁]
  rfl


-- @@ L146-149 verbatim
@[simp]
theorem realize_wdSrcF (t q : γ) : (wdSrcF t q).Realize v ↔ WMSrc (v t) (v q) := by
  simp only [wdSrcF, Formula.realize_rel₂]
  rfl


-- @@ L151-154 verbatim
@[simp]
theorem realize_wdReadF (t a : γ) : (wdReadF t a).Realize v ↔ WMRead (v t) (v a) := by
  simp only [wdReadF, Formula.realize_rel₂]
  rfl


-- @@ L156-159 verbatim
@[simp]
theorem realize_wdDstF (t q : γ) : (wdDstF t q).Realize v ↔ WMDst (v t) (v q) := by
  simp only [wdDstF, Formula.realize_rel₂]
  rfl


-- @@ L161-164 verbatim
@[simp]
theorem realize_wdWriteF (t a : γ) : (wdWriteF t a).Realize v ↔ WMWrite (v t) (v a) := by
  simp only [wdWriteF, Formula.realize_rel₂]
  rfl


-- @@ L166-169 verbatim
@[simp]
theorem realize_wdInpF (x a : γ) : (wdInpF x a).Realize v ↔ WMInp (v x) (v a) := by
  simp only [wdInpF, Formula.realize_rel₂]
  rfl


-- @@ L171-173 verbatim
@[simp]
theorem realize_wdEqF (x y : γ) : (wdEqF x y).Realize v ↔ v x = v y := by
  rw [wdEqF, Formula.realize_equal, Term.realize_var, Term.realize_var]


-- @@ L175-175 verbatim
end Atoms


-- @@ L177-177 verbatim
/-! ### The two shapes every tile formula is built from -/


-- @@ L179-179 verbatim
section Shapes


-- @@ L181-181 verbatim
variable {γ : Type}


-- @@ L183-187 verbatim
open Classical in
/-- **A static choice on the tags**: the truth value a tag decides, as a
formula. Every case analysis the drawing does on tags is one of these, so the
formulas themselves stay small. -/
noncomputable def tagIfF (b : Prop) : wideOrd.Formula γ := if b then ⊤ else ⊥


-- @@ L189-198 expanded
/-- **The machine's promises**: the order is linear, the input is functional,
and there is exactly one blank. This is
`DescriptiveComplexity.WideWF` written out, and the start tile is where the
drawing carries it – a no-instance whose promises fail has no start tile, hence
no tiling. -/
noncomputable def wideWFF : wideOrd.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (wdLeF (Sum.inr 0) (Sum.inr 0)) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 3)
          ((wdLeF (Sum.inr 0) (Sum.inr 1) ⊓ wdLeF (Sum.inr 1) (Sum.inr 2)).imp
            (wdLeF (Sum.inr 0) (Sum.inr 2))) ⊓
        (FirstOrder.Language.Formula.iAlls (Fin 2)
            ((wdLeF (Sum.inr 0) (Sum.inr 1) ⊓ wdLeF (Sum.inr 1) (Sum.inr 0)).imp
              (wdEqF (Sum.inr 0) (Sum.inr 1))) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 2)
            (wdLeF (Sum.inr 0) (Sum.inr 1) ⊔ wdLeF (Sum.inr 1) (Sum.inr 0)))) ⊓
    (FirstOrder.Language.Formula.iAlls (Fin 3)
        ((wdInpF (Sum.inr 0) (Sum.inr 1) ⊓ wdInpF (Sum.inr 0) (Sum.inr 2)).imp
          (wdEqF (Sum.inr 1) (Sum.inr 2))) ⊓
      (FirstOrder.Language.Formula.iExs (Fin 1) (wdBlankF (Sum.inr 0)) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 2)
          ((wdBlankF (Sum.inr 0) ⊓ wdBlankF (Sum.inr 1)).imp (wdEqF (Sum.inr 0) (Sum.inr 1)))))


-- @@ L200-200 verbatim
variable {A : Type} [Language.wide.Structure A] [LinearOrder A] {v : γ → A}


-- @@ L202-211 verbatim
@[simp]
theorem realize_tagIfF (b : Prop) : ((tagIfF b).Realize v) ↔ b := by
  classical
  by_cases hb : b
  · rw [tagIfF, ite_eq_left hb]
    simp only [Formula.realize_top]
    exact iff_of_true trivial hb
  · rw [tagIfF, ite_eq_right hb]
    simp only [Formula.realize_bot]
    exact iff_of_false (fun h => h) hb


-- @@ L213-228 verbatim
@[simp]
theorem realize_wideWFF : ((wideWFF (γ := γ)).Realize v) ↔ WideWF A := by
  rw [wideWFF, WideWF, IsLinOrd]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, Formula.realize_sup, realize_wdLeF, realize_wdEqF,
    realize_wdInpF, realize_wdBlankF, Sum.elim_inr]
  refine and_congr (and_congr ⟨fun h a => h fun _ => a, fun h w => h (w 0)⟩
      (and_congr ⟨fun h a b c h1 h2 => h ![a, b, c] ⟨h1, h2⟩,
          fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
        (and_congr ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩,
            fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
          ⟨fun h a b => h ![a, b], fun h w => h (w 0) (w 1)⟩)))
    (and_congr ⟨fun h x a b h1 h2 => h ![x, a, b] ⟨h1, h2⟩,
        fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
      (and_congr ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩
        ⟨fun h a b h1 h2 => h ![a, b] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩))


-- @@ L230-230 verbatim
end Shapes


-- @@ L232-232 verbatim
end TilingHard


-- @@ L234-234 verbatim
end DescriptiveComplexity
