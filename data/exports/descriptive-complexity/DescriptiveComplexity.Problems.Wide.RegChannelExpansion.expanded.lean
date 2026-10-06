/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannel
import DescriptiveComplexity.Problems.Wide.Membership


-- @@ L9-26 verbatim
/-!
# The register channel, as an expansion

`DescriptiveComplexity.WideAccept` is in NEXPTIME because the wide machine of an
instance *is* the ordinary machine of an exponential expansion of it
(`DescriptiveComplexity.Problems.Wide.Membership`): twelve relation symbols,
each defined by a sentence over one or two copies of the address block. The
register channel changes exactly one of the twelve – the input – so this file
adds the sentence it needs, the expansion it names, and the membership that
follows.

The sentence is the segment channel's with one conjunct added: the segment
channel says «the address holds `z` exactly when `z ≤ x`», the register channel
says «exactly when `z ≤ x` *and* `z` carries an input symbol». Carrying one is
itself first-order (`hasInpG`), so the expansion stays what it was, and the two
expansions have the same tags, the same block and the same domain, hence the
same universe.
-/


-- @@ L28-28 verbatim
namespace DescriptiveComplexity


-- @@ L30-30 verbatim
open FirstOrder


-- @@ L32-32 verbatim
open Language Structure


-- @@ L34-34 verbatim
namespace Wide


-- @@ L36-36 verbatim
/-! ### The sentence the register channel needs -/


-- @@ L38-38 verbatim
section Guard


-- @@ L40-40 verbatim
variable {γ : Type}


-- @@ L42-45 verbatim
/-- **An element the channel writes for**, as a guard: it carries an input
symbol. -/
noncomputable def hasInpG (x : γ) : wOrd.Formula γ :=
  Formula.iExs (Fin 1) (attrG wmInp (Sum.inl x) (Sum.inr 0))


-- @@ L47-47 verbatim
variable {A : Type} [Language.wide.Structure A] [LinearOrder A] {v : γ → A}


-- @@ L49-53 verbatim
@[simp]
theorem realize_hasInpG (x : γ) : (hasInpG x).Realize v ↔ WMHasInp (v x) := by
  rw [hasInpG]
  simp only [Formula.realize_iExs, realize_attrG, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, ha⟩⟩


-- @@ L55-55 verbatim
end Guard


-- @@ L57-65 verbatim
/-- **The initial tape at the register channel**: the first address is the
segment some element `x` cuts among the elements that carry input, the second
point is a symbol `y`, and `y` is the input at `x`. -/
noncomputable def inpRegS : wide2.Sentence :=
  Formula.iExs (Fin 2)
    (Formula.iAlls (Fin 1)
        (bitAF (Sum.inr 0) ⇔ lift2 (attrG wmLe (Sum.inr 0) (Sum.inl (Sum.inr 0)) ⊓
          hasInpG (Sum.inr 0))) ⊓
      (bitBF (Sum.inr 1) ⊓ lift2 (attrG wmInp (Sum.inr 0) (Sum.inr 1))))


-- @@ L67-67 verbatim
section Realize


-- @@ L69-69 verbatim
variable {A : Type} [Language.wide.Structure A] [LinearOrder A]


-- @@ L71-80 verbatim
theorem realize_inpRegS (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) ρ σ) inpRegS ↔
      ∃ x y, WMRegSeg (wbits ρ) x ∧ wbits σ y ∧ WMInp x y) := by
  let := addrBlock.structure₂ (L := wOrd) ρ σ
  rw [inpRegS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_iAlls, Formula.realize_inf,
    Formula.realize_iff, realize_bitAF, realize_bitBF, realize_lift2, realize_attrG,
    realize_hasInpG, Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun ⟨w, hd, hb, hi⟩ => ⟨w 0, w 1, fun y => hd fun _ => y, hb, hi⟩,
    fun ⟨x, y, hd, hb, hi⟩ => ⟨![x, y], fun w => hd (w 0), hb, hi⟩⟩


-- @@ L82-82 verbatim
end Realize


-- @@ L84-84 verbatim
/-! ### The expansion, and the structure it puts on the same universe -/


-- @@ L86-89 verbatim
/-- The initial tape of the register channel, at a pair of tags. -/
noncomputable def inpRegT : WTag → WTag → wide2.Sentence
  | .addr, .ctrl => inpRegS
  | _, _ => ⊥


-- @@ L91-117 verbatim
/-- **The expansion of a wide-machine instance at the register channel**: the
tags, the block, the domain and eleven of the twelve symbols are
`DescriptiveComplexity.wideExp`'s; the input is the register channel's. -/
noncomputable def wideRegExp : ExpExpansion Language.wide where
  Tag := WTag
  B := addrBlock
  E := Language.turing
  dom := domT
  relSentence {n} r τ :=
    match n, r with
    | _, .posn => onS1 (posnT (τ 0))
    | _, .tr => onS1 (markT wmTr (τ 0))
    | _, .start => onS1 (markT wmStart (τ 0))
    | _, .acc => onS1 (markT wmAcc (τ 0))
    | _, .blank => onS1 (markT wmBlank (τ 0))
    | _, .right => onS1 (markT wmRight (τ 0))
    | _, .le => onS2 (leT (τ 0) (τ 1))
    | _, .tsrc => onS2 (binT wmSrc (τ 0) (τ 1))
    | _, .tread => onS2 (binT wmRead (τ 0) (τ 1))
    | _, .tdst => onS2 (binT wmDst (τ 0) (τ 1))
    | _, .twrite => onS2 (binT wmWrite (τ 0) (τ 1))
    | _, .inp => onS2 (inpRegT (τ 0) (τ 1))
  dom_nonempty := by
    intro A _ _ _ _
    refine ⟨.addr, addrBlock.botAssign A, ?_⟩
    let := addrBlock.structure₁ (L := wOrd) (addrBlock.botAssign A)
    exact Formula.realize_top.mpr trivial


-- @@ L119-119 verbatim
section Structure


-- @@ L121-121 verbatim
variable (A : Type) [Language.wide.Structure A] [LinearOrder A]


-- @@ L123-128 verbatim
/-- The expanded structure at the register channel. Its universe is `wideExp`'s
– the two expansions differ in one defining sentence and in nothing that decides
the points. -/
@[instance_reducible]
noncomputable def wideRegStructure : Language.turing.Structure (wideExp.Map A) :=
  wideRegExp.mapStructure A


-- @@ L130-130 verbatim
variable {A}


-- @@ L132-143 verbatim
/-- Reading a binary symbol of the register-channel expansion at two points. -/
theorem realize_twoReg (rt : Language.turing.Relations 2) (φ : WTag → WTag → wide2.Sentence)
    (h : ∀ τ : Fin 2 → wideRegExp.Tag, wideRegExp.relSentence rt τ = onS2 (φ (τ 0) (τ 1)))
    (x y : wideExp.Map A) :
    letI := wideRegStructure A
    (RelMap rt ![x, y] ↔
      @Sentence.Realize wide2 A (addrBlock.structure₂ (L := wOrd) x.1.2 y.1.2)
        (φ x.1.1 y.1.1)) := by
  let := wideRegStructure A
  have h1 := wideRegExp.relMap_map rt ![x, y]
  rw [h] at h1
  exact h1.trans (realize_onS2 _ x y)


-- @@ L145-159 verbatim
/-- **The initial tape of the expanded machine at the register channel**: the
segment an element cuts among the elements that carry input holds that element's
input symbol. -/
theorem relMap_inpReg (p q : WPoint A) :
    letI := wideRegStructure A
    (RelMap tmInp ![wideEmbed p, wideEmbed q] ↔ (wideRegData A).Inp p q) := by
  let := wideRegStructure A
  rw [realize_twoReg tmInp inpRegT (fun _ => rfl) (wideEmbed p) (wideEmbed q)]
  match p, q with
  | Sum.inl s, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inl s, Sum.inr y =>
    refine (realize_inpRegS _ _).trans ?_
    exact ⟨fun ⟨a, b, hd, hb, hr⟩ => ⟨a, hd, hb ▸ hr⟩, fun ⟨a, hd, hr⟩ => ⟨a, y, hd, rfl, hr⟩⟩
  | Sum.inr x, Sum.inl t => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)
  | Sum.inr x, Sum.inr y => exact iff_of_false (not_realize_botS₂ _ _) (fun h => h)


-- @@ L161-161 verbatim
variable (A)


-- @@ L163-181 verbatim
/-- **The wide machine at the register channel is the ordinary machine of the
register-channel expansion**, fieldwise: eleven of the twelve symbols are
defined by the same sentences as `wideExp`'s, so their readings are the same
readings, and the twelfth is `relMap_inpReg`. -/
theorem wideRegAgree :
    letI := wideRegStructure A
    TMData.Agree (wideEquiv (A := A)) (wideRegData A) (tmData (wideExp.Map A)) := by
  let := wideRegStructure A
  exact ⟨fun p => (relMap_posn p).symm, fun p q => (relMap_le p q).symm,
    fun p => (relMap_mark tmTr wmTr (fun _ => rfl) p).symm,
    fun p => (relMap_mark tmStart wmStart (fun _ => rfl) p).symm,
    fun p => (relMap_mark tmAcc wmAcc (fun _ => rfl) p).symm,
    fun p => (relMap_mark tmBlank wmBlank (fun _ => rfl) p).symm,
    fun p => (relMap_mark tmRight wmRight (fun _ => rfl) p).symm,
    fun p q => (relMap_attr tmSrc wmSrc (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr tmRead wmRead (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr tmDst wmDst (fun _ => rfl) p q).symm,
    fun p q => (relMap_attr tmWrite wmWrite (fun _ => rfl) p q).symm,
    fun p q => (relMap_inpReg p q).symm⟩


-- @@ L183-183 verbatim
end Structure


-- @@ L185-185 verbatim
end Wide


-- @@ L187-187 verbatim
/-! ### The membership -/


-- @@ L189-189 verbatim
section Membership


-- @@ L191-191 verbatim
open Wide


-- @@ L193-201 verbatim
/-- **The register-channel machine is the ordinary machine of its expansion**:
acceptance of the one is acceptance of the other. -/
theorem wideRegAccept_iff_expansion (A : Type) [Language.wide.Structure A]
    [LinearOrder A] :
    letI := wideRegStructure A
    (WideRegAccept A ↔ NTMAccept (wideExp.Map A)) := by
  let := wideRegStructure A
  have h := wideRegAgree A
  exact and_congr h.wellFormed h.accepts


-- @@ L203-213 verbatim
/-- **The register-channel machine is in NEXPTIME**, for the reason
`DescriptiveComplexity.wideAccept_mem_NEXPTIME` gives: its expansion is an
ordinary machine, and `DescriptiveComplexity.NTMAccept` is in NP. The two
problems are therefore in the same class, and a reduction may choose whichever
channel puts its input where it can reach it. -/
theorem wideRegAccept_mem_NEXPTIME : WideRegAccept ∈ NEXPTIME := by
  let hinst : ∀ (A : Type) [Language.wide.Structure A] [LinearOrder A],
      Language.turing.Structure (wideExp.Map A) := fun A => wideRegStructure A
  refine ⟨wideRegExp, NTMAccept, ntmAccept_mem_NP, ?_⟩
  intro A _ _ _ _
  exact wideRegAccept_iff_expansion A


-- @@ L215-215 verbatim
end Membership


-- @@ L217-217 verbatim
end DescriptiveComplexity
