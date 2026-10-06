/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.MachineAltSpace
import DescriptiveComplexity.Exponential.Game


-- @@ L10-32 verbatim
/-!
# The guards of the alternating machine, and the configuration block

The first of the three layers that put `DescriptiveComplexity.ATMAcceptSpace`
in EXPTIME. Everything here is bookkeeping:

* the symbols of `FirstOrder.Language.turingAlt 2` in the **ordered** expansion,
  as abbreviations with declared types – a raw `Sum.inl r` inside
  `FirstOrder.Language.Relations.formula₁` does not elaborate;
* one guard per symbol, at an arbitrary variable type, with its realization
  lemma, in the style of `DescriptiveComplexity.Problems.Machine.Fixpoint`;
* the derived guards `minPosG`, `succPosG`, `initTapeG` and the two promise
  *sentences* `wfS` (`DescriptiveComplexity.TMData.WellFormed`) and
  `blocksSplitS` (`DescriptiveComplexity.ATMData.BlocksSplit`);
* the **configuration block** `cfgBlock` – one variable for the state, one for
  the head, one for the tape – its atoms at one and at two copies, and the
  lifts that read a base guard there.

The block has a binary variable for the tape because a
`DescriptiveComplexity.Config` carries a *function* `A → A`; that the variable
is one is the content of `DescriptiveComplexity.ATMSpace.isCfgS`, and
`DescriptiveComplexity.ATMSpace.cfgOf` is the assignment a configuration is.
-/


-- @@ L34-34 verbatim
namespace DescriptiveComplexity


-- @@ L36-36 verbatim
open FirstOrder


-- @@ L38-38 verbatim
open Language Structure


-- @@ L40-40 verbatim
namespace ATMSpace


-- @@ L42-42 verbatim
/-! ### The ordered vocabulary and its symbols -/


-- @@ L44-46 verbatim
/-- The ordered expansion of the alternating machine vocabulary, at two
blocks. -/
abbrev tmaOrd : Language.{0, 0} := (Language.turingAlt 2).sum Language.order


-- @@ L48-49 verbatim
/-- The position symbol. -/
abbrev posnO : tmaOrd.Relations 1 := Sum.inl atmPosn


-- @@ L51-52 verbatim
/-- The transition symbol. -/
abbrev trO : tmaOrd.Relations 1 := Sum.inl atmTr


-- @@ L54-55 verbatim
/-- The start-state symbol. -/
abbrev startO : tmaOrd.Relations 1 := Sum.inl atmStart


-- @@ L57-58 verbatim
/-- The accepting-state symbol. -/
abbrev accO : tmaOrd.Relations 1 := Sum.inl atmAcc


-- @@ L60-61 verbatim
/-- The blank symbol. -/
abbrev blankO : tmaOrd.Relations 1 := Sum.inl atmBlank


-- @@ L63-64 verbatim
/-- The move-right symbol. -/
abbrev rightO : tmaOrd.Relations 1 := Sum.inl atmRight


-- @@ L66-67 verbatim
/-- The order symbol of the machine. -/
abbrev leO : tmaOrd.Relations 2 := Sum.inl atmLe


-- @@ L69-70 verbatim
/-- The transition-source symbol. -/
abbrev srcO : tmaOrd.Relations 2 := Sum.inl atmSrc


-- @@ L72-73 verbatim
/-- The transition-read symbol. -/
abbrev readO : tmaOrd.Relations 2 := Sum.inl atmRead


-- @@ L75-76 verbatim
/-- The transition-destination symbol. -/
abbrev dstO : tmaOrd.Relations 2 := Sum.inl atmDst


-- @@ L78-79 verbatim
/-- The transition-write symbol. -/
abbrev writeO : tmaOrd.Relations 2 := Sum.inl atmWrite


-- @@ L81-82 verbatim
/-- The input symbol. -/
abbrev inpO : tmaOrd.Relations 2 := Sum.inl atmInp


-- @@ L84-85 verbatim
/-- The mark of the `i`-th player. -/
abbrev blkO (i : Fin 2) : tmaOrd.Relations 1 := Sum.inl (atmBlk i)


-- @@ L87-87 verbatim
/-! ### One guard per symbol -/


-- @@ L89-89 verbatim
section Guards


-- @@ L91-91 verbatim
variable {γ : Type}


-- @@ L93-94 expanded
/-- `x` is a position. -/
noncomputable def posnG (x : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ posnO (FirstOrder.Language.Term.var x)


-- @@ L96-97 expanded
/-- `x` is a transition. -/
noncomputable def trG (x : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ trO (FirstOrder.Language.Term.var x)


-- @@ L99-100 expanded
/-- `x` is a start state. -/
noncomputable def startG (x : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ startO (FirstOrder.Language.Term.var x)


-- @@ L102-103 expanded
/-- `x` is an accepting state. -/
noncomputable def accG (x : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ accO (FirstOrder.Language.Term.var x)


-- @@ L105-106 expanded
/-- `x` is the blank symbol. -/
noncomputable def blankG (x : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ blankO (FirstOrder.Language.Term.var x)


-- @@ L108-109 expanded
/-- The transition `x` moves the head right. -/
noncomputable def rightG (x : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ rightO (FirstOrder.Language.Term.var x)


-- @@ L111-112 expanded
/-- `x` is marked by the `i`-th player. -/
noncomputable def blkG (i : Fin 2) (x : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₁ (blkO i) (FirstOrder.Language.Term.var x)


-- @@ L114-115 expanded
/-- `x ≤ y` in the machine's own order. -/
noncomputable def leG (x y : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ leO (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L117-118 expanded
/-- The transition `x` applies in the state `y`. -/
noncomputable def srcG (x y : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ srcO (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L120-121 expanded
/-- The transition `x` reads the symbol `y`. -/
noncomputable def readG (x y : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ readO (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L123-124 expanded
/-- The transition `x` moves to the state `y`. -/
noncomputable def dstG (x y : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ dstO (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L126-127 expanded
/-- The transition `x` writes the symbol `y`. -/
noncomputable def writeG (x y : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ writeO (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L129-130 expanded
/-- The cell `x` initially holds the input symbol `y`. -/
noncomputable def inpG (x y : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Relations.formula₂ inpO (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L132-133 expanded
/-- `x` and `y` are the same element. -/
noncomputable def eqG (x y : γ) : tmaOrd.Formula γ :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)


-- @@ L135-135 verbatim
variable {A : Type} [(Language.turingAlt 2).Structure A] [LinearOrder A] {v : γ → A}


-- @@ L137-139 verbatim
@[simp]
theorem realize_posnG (x : γ) : (posnG x).Realize v ↔ ATMPosn (k := 2) (v x) := by
  rw [posnG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl


-- @@ L141-143 verbatim
@[simp]
theorem realize_trG (x : γ) : (trG x).Realize v ↔ ATMTr (k := 2) (v x) := by
  rw [trG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl


-- @@ L145-147 verbatim
@[simp]
theorem realize_startG (x : γ) : (startG x).Realize v ↔ ATMStart (k := 2) (v x) := by
  rw [startG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl


-- @@ L149-151 verbatim
@[simp]
theorem realize_accG (x : γ) : (accG x).Realize v ↔ ATMAcc (k := 2) (v x) := by
  rw [accG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl


-- @@ L153-155 verbatim
@[simp]
theorem realize_blankG (x : γ) : (blankG x).Realize v ↔ ATMBlank (k := 2) (v x) := by
  rw [blankG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl


-- @@ L157-159 verbatim
@[simp]
theorem realize_rightG (x : γ) : (rightG x).Realize v ↔ ATMRight (k := 2) (v x) := by
  rw [rightG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl


-- @@ L161-164 verbatim
@[simp]
theorem realize_blkG (i : Fin 2) (x : γ) :
    (blkG i x).Realize v ↔ RelMap (atmBlk i) ![v x] := by
  rw [blkG, Formula.realize_rel₁, relMap_sumInl]; exact Iff.rfl


-- @@ L166-168 verbatim
@[simp]
theorem realize_leG (x y : γ) : (leG x y).Realize v ↔ ATMLe (k := 2) (v x) (v y) := by
  rw [leG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl


-- @@ L170-172 verbatim
@[simp]
theorem realize_srcG (x y : γ) : (srcG x y).Realize v ↔ ATMSrc (k := 2) (v x) (v y) := by
  rw [srcG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl


-- @@ L174-176 verbatim
@[simp]
theorem realize_readG (x y : γ) : (readG x y).Realize v ↔ ATMRead (k := 2) (v x) (v y) := by
  rw [readG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl


-- @@ L178-180 verbatim
@[simp]
theorem realize_dstG (x y : γ) : (dstG x y).Realize v ↔ ATMDst (k := 2) (v x) (v y) := by
  rw [dstG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl


-- @@ L182-184 verbatim
@[simp]
theorem realize_writeG (x y : γ) : (writeG x y).Realize v ↔ ATMWrite (k := 2) (v x) (v y) := by
  rw [writeG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl


-- @@ L186-188 verbatim
@[simp]
theorem realize_inpG (x y : γ) : (inpG x y).Realize v ↔ ATMInp (k := 2) (v x) (v y) := by
  rw [inpG, Formula.realize_rel₂, relMap_sumInl]; exact Iff.rfl


-- @@ L190-192 verbatim
@[simp]
theorem realize_eqG (x y : γ) : (eqG x y).Realize v ↔ v x = v y := by
  rw [eqG, Formula.realize_equal, Term.realize_var, Term.realize_var]


-- @@ L194-194 verbatim
/-! ### The derived guards -/


-- @@ L196-198 expanded
/-- `x` is a least position. -/
noncomputable def minPosG (x : γ) : tmaOrd.Formula γ :=
  posnG x ⊓
    FirstOrder.Language.Formula.iAlls (Fin 1)
      ((posnG (Sum.inr 0)).imp (leG (Sum.inl x) (Sum.inr 0)))


-- @@ L200-203 expanded
/-- `y` is the position immediately above `x`. -/
noncomputable def succPosG (x y : γ) : tmaOrd.Formula γ :=
  posnG x ⊓
    (posnG y ⊓
      (leG x y ⊓
        (FirstOrder.Language.BoundedFormula.not (eqG x y) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 1)
            ((posnG (Sum.inr 0) ⊓ leG (Sum.inl x) (Sum.inr 0) ⊓ leG (Sum.inr 0) (Sum.inl y)).imp
              (eqG (Sum.inr 0) (Sum.inl x) ⊔ eqG (Sum.inr 0) (Sum.inl y))))))


-- @@ L205-207 expanded
/-- The cell `x` may initially hold the symbol `y`. -/
noncomputable def initTapeG (x y : γ) : tmaOrd.Formula γ :=
  inpG x y ⊔
    FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.BoundedFormula.not (inpG (Sum.inl x) (Sum.inr 0))) ⊓
      blankG y


-- @@ L209-215 verbatim
@[simp]
theorem realize_minPosG (x : γ) :
    (minPosG x).Realize v ↔ MinPos (ATMLe (k := 2)) (ATMPosn (k := 2)) (v x) := by
  rw [minPosG, Formula.realize_inf]
  simp only [Formula.realize_iAlls, Formula.realize_imp, realize_posnG, realize_leG,
    Sum.elim_inl, Sum.elim_inr]
  exact and_congr Iff.rfl ⟨fun h q hq => h (fun _ => q) hq, fun h w => h (w 0)⟩


-- @@ L217-228 verbatim
@[simp]
theorem realize_succPosG (x y : γ) :
    (succPosG x y).Realize v ↔ SuccPos (ATMLe (k := 2)) (ATMPosn (k := 2)) (v x) (v y) := by
  rw [succPosG, SuccPos]
  simp only [Formula.realize_inf, Formula.realize_not, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_sup, realize_posnG, realize_leG, realize_eqG,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hp, hq, hle, hne, hbetw⟩
    exact ⟨hp, hq, hle, hne, fun r hr h1 h2 => hbetw (fun _ => r) ⟨⟨hr, h1⟩, h2⟩⟩
  · rintro ⟨hp, hq, hle, hne, hbetw⟩
    exact ⟨hp, hq, hle, hne, fun w hw => hbetw (w 0) hw.1.1 hw.1.2 hw.2⟩


-- @@ L230-237 verbatim
@[simp]
theorem realize_initTapeG (x y : γ) :
    (initTapeG x y).Realize v ↔ (atmData 2 A).toTMData.InitTape (v x) (v y) := by
  rw [initTapeG, TMData.InitTape]
  simp only [Formula.realize_sup, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_not, realize_inpG, realize_blankG, Sum.elim_inl, Sum.elim_inr]
  exact or_congr Iff.rfl
    (and_congr ⟨fun h b => h fun _ => b, fun h w => h (w 0)⟩ Iff.rfl)


-- @@ L239-239 verbatim
end Guards


-- @@ L241-241 verbatim
/-! ### The two promises, as sentences -/


-- @@ L243-246 expanded
/-- The machine's order is linear. -/
noncomputable def isLinOrdS : tmaOrd.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1) (leG (Sum.inr 0) (Sum.inr 0)) ⊓
    (FirstOrder.Language.Formula.iAlls (Fin 3)
        ((leG (Sum.inr 0) (Sum.inr 1) ⊓ leG (Sum.inr 1) (Sum.inr 2)).imp
          (leG (Sum.inr 0) (Sum.inr 2))) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 2)
          ((leG (Sum.inr 0) (Sum.inr 1) ⊓ leG (Sum.inr 1) (Sum.inr 0)).imp
            (eqG (Sum.inr 0) (Sum.inr 1))) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 2)
          (leG (Sum.inr 0) (Sum.inr 1) ⊔ leG (Sum.inr 1) (Sum.inr 0))))


-- @@ L248-252 expanded
/-- **Well-formedness**, as a sentence: the order is linear, there is a
position, the input is functional, and there is exactly one blank. -/
noncomputable def wfS : tmaOrd.Sentence :=
  isLinOrdS ⊓
    (FirstOrder.Language.Formula.iExs (Fin 1) (posnG (Sum.inr 0)) ⊓
      (FirstOrder.Language.Formula.iAlls (Fin 3)
          ((inpG (Sum.inr 0) (Sum.inr 1) ⊓ inpG (Sum.inr 0) (Sum.inr 2)).imp
            (eqG (Sum.inr 1) (Sum.inr 2))) ⊓
        (FirstOrder.Language.Formula.iExs (Fin 1) (blankG (Sum.inr 0)) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 2)
            ((blankG (Sum.inr 0) ⊓ blankG (Sum.inr 1)).imp (eqG (Sum.inr 0) (Sum.inr 1))))))


-- @@ L254-257 expanded
/-- **The two marks split the states**, as a sentence: every state carries one
of them and not both. -/
noncomputable def blocksSplitS : tmaOrd.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    (((blkG 0) (Sum.inr 0) ⊔ (blkG 1) (Sum.inr 0)) ⊓
      FirstOrder.Language.BoundedFormula.not ((blkG 0) (Sum.inr 0) ⊓ (blkG 1) (Sum.inr 0)))


-- @@ L259-259 verbatim
section PromiseRealize


-- @@ L261-261 verbatim
variable {A : Type} [(Language.turingAlt 2).Structure A] [LinearOrder A]


-- @@ L263-272 verbatim
theorem realize_isLinOrdS : (A ⊨ isLinOrdS) ↔ IsLinOrd (ATMLe (k := 2) (A := A)) := by
  rw [isLinOrdS, IsLinOrd, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_sup, realize_leG, realize_eqG, Sum.elim_inr]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun h a => h fun _ => a, fun h w => h (w 0)⟩
  · exact ⟨fun h a b c hab hbc => h ![a, b, c] ⟨hab, hbc⟩,
      fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
  · exact ⟨fun h a b hab hba => h ![a, b] ⟨hab, hba⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩
  · exact ⟨fun h a b => h ![a, b], fun h w => h (w 0) (w 1)⟩


-- @@ L274-283 verbatim
theorem realize_wfS : (A ⊨ wfS) ↔ (atmData 2 A).toTMData.WellFormed := by
  rw [wfS, TMData.WellFormed, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, realize_inpG, realize_blankG, realize_posnG, realize_eqG,
    Sum.elim_inr]
  refine and_congr realize_isLinOrdS (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨p, hp⟩ => ⟨fun _ => p, hp⟩⟩
  · exact ⟨fun h p a b h1 h2 => h ![p, a, b] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) (w 2) hw.1 hw.2⟩
  · exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨b, hb⟩ => ⟨fun _ => b, hb⟩⟩
  · exact ⟨fun h a b ha hb => h ![a, b] ⟨ha, hb⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩


-- @@ L285-320 verbatim
/-- The two marks split the states exactly when every state carries one and not
both: a mark index of `2` or more marks nothing, so the uniqueness clause of
`DescriptiveComplexity.ATMData.BlocksSplit` only speaks about `0` and `1`. -/
theorem realize_blocksSplitS : (A ⊨ blocksSplitS) ↔ (atmData 2 A).BlocksSplit := by
  rw [blocksSplitS, Sentence.Realize]
  simp only [Formula.realize_iAlls, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_not, realize_blkG, Sum.elim_inr]
  constructor
  · intro h q
    obtain ⟨hone, hnot⟩ := h fun _ => q
    have hblk : ∀ (j : ℕ) (hj : j < 2), (atmData 2 A).Blk j q ↔ RelMap (atmBlk ⟨j, hj⟩) ![q] :=
      fun j hj => ⟨fun ⟨h', hb⟩ => by rwa [Subsingleton.elim h' hj] at hb, fun hb => ⟨hj, hb⟩⟩
    rcases hone with h0 | h1
    · refine ⟨0, by omega, (hblk 0 (by omega)).mpr h0, fun j' hj' => ?_⟩
      obtain ⟨hj2, hb⟩ := hj'
      have : j' = 0 ∨ j' = 1 := by omega
      rcases this with rfl | rfl
      · rfl
      · exact absurd ⟨h0, (hblk 1 (by omega)).mp ⟨hj2, hb⟩⟩ hnot
    · refine ⟨1, by omega, (hblk 1 (by omega)).mpr h1, fun j' hj' => ?_⟩
      obtain ⟨hj2, hb⟩ := hj'
      have : j' = 0 ∨ j' = 1 := by omega
      rcases this with rfl | rfl
      · exact absurd ⟨(hblk 0 (by omega)).mp ⟨hj2, hb⟩, h1⟩ hnot
      · rfl
  · intro h w
    obtain ⟨j, hj2, hj, huniq⟩ := h (w 0)
    have hj01 : j = 0 ∨ j = 1 := by omega
    constructor
    · rcases hj01 with rfl | rfl
      · exact Or.inl hj.2
      · exact Or.inr hj.2
    · rintro ⟨h0, h1⟩
      have e0 : (0 : ℕ) = j := huniq 0 ⟨by omega, h0⟩
      have e1 : (1 : ℕ) = j := huniq 1 ⟨by omega, h1⟩
      omega


-- @@ L322-322 verbatim
end PromiseRealize


-- @@ L324-324 verbatim
end ATMSpace


-- @@ L326-326 verbatim
end DescriptiveComplexity
