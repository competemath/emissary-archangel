/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.RegChannel
import DescriptiveComplexity.Problems.Wide.DrawBack
import DescriptiveComplexity.Problems.Wide.LowFile
import DescriptiveComplexity.Problems.Wide.DrawName


-- @@ L11-29 verbatim
/-!
# The file of the register channel, laid out

`DescriptiveComplexity.Draw.Data.diagLaid` reads the segment channel's ruler
as a `DescriptiveComplexity.Draw.LaidFile`: one register per element of the
universe, in the universe's own order, each naming its own tag's block and its
own tuple. This file does the same for the **register channel**, whose file has
one register per element the channel writes for.

Everything the evaluation asks of a layout is the elementwise one's, restricted:

* a register *is* an element, so the block and the named coordinates spell it
  (`nameSep_regLaid`);
* every block and named tuple has a register, provided the reduction writes for
  the argument elements – which is what it does, and what makes its file lie in
  the working region (`hasName_regLaid`);
* the registers grow with the elements (`wmSetLt_wmRegSeg`), which is the one
  property the singleton channel could not give.
-/


-- @@ L31-31 verbatim
namespace DescriptiveComplexity


-- @@ L33-33 verbatim
namespace Draw


-- @@ L35-35 verbatim
namespace Data


-- @@ L37-37 verbatim
open FirstOrder


-- @@ L39-39 verbatim
open Language Structure


-- @@ L41-41 verbatim
section RegLaid


-- @@ L43-43 verbatim
variable {L : Language.{0, 0}} {dt : Data L} {A R' P' : Type}

-- @@ L44-44 verbatim
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

-- @@ L45-45 verbatim
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

-- @@ L46-46 verbatim
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]


-- @@ L48-50 verbatim
variable (dt) in
/-- **The index of the register channel's file**: the elements it writes for. -/
abbrev RegIx : Type := {x : Univ A R' P' dt.KIx dt.dd // WMHasInp x}


-- @@ L52-64 verbatim
/-- **The register channel's file, laid out**: one register per element the
channel writes for, in the universe's own order, each naming its own tag's block
and its own tuple. -/
noncomputable def regLaid (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    (hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y) :
    LaidFile dt A R' P' (dt.RegIx (A := A) (R' := R') (P' := P')) where
  cell u := wmRegSeg u.1
  le u v := tagTupleLe u.1 v.1
  blk u := tagBlk u.1.1
  arg u := u.1.2
  strictMono _u v hlt := wmSetLt_wmRegSeg h
    ⟨(hord _ _).mpr hlt.1, fun hc => hlt.2 ((hord _ _).mp hc)⟩ v.2
  cell_nonempty u := wmRegSeg_nonempty h u.2


-- @@ L66-66 verbatim
variable {h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd))}

-- @@ L67-67 verbatim
variable {hord : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y ↔ tagTupleLe x y}


-- @@ L69-78 verbatim
/-- **The file's layout order is linear**, being the universe's own read on a
subtype. -/
theorem isLinOrd_regLaid_le : IsLinOrd (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le :=
  ⟨fun u => (Wide.isLinOrd_tagTupleLe (Tag := Tag R' P' dt.KIx) (A := A) (d := dt.dd)).1 u.1,
    fun u v w h1 h2 => (Wide.isLinOrd_tagTupleLe (Tag := Tag R' P' dt.KIx)
      (A := A) (d := dt.dd)).2.1 u.1 v.1 w.1 h1 h2,
    fun u v h1 h2 => Subtype.ext ((Wide.isLinOrd_tagTupleLe (Tag := Tag R' P' dt.KIx)
      (A := A) (d := dt.dd)).2.2.1 u.1 v.1 h1 h2),
    fun u v => (Wide.isLinOrd_tagTupleLe (Tag := Tag R' P' dt.KIx)
      (A := A) (d := dt.dd)).2.2.2 u.1 v.1⟩


-- @@ L80-85 verbatim
/-- **The file's marks tell its registers apart**: a register *is* an element, so
its block and its named coordinates spell it. -/
theorem nameSep_regLaid (zero : A) (hdd : dt.dd0 ≤ dt.dd) :
    (dt.regLaid (A := A) (R' := R') (P' := P') h hord).toLayout.NameSep zero hdd :=
  fun _ _ _ hb hb' hp hp' hn =>
    Subtype.ext (eq_of_slotMark_name (hdd := hdd) (hb.trans hb'.symm) hb hn hp hp')


-- @@ L87-97 verbatim
/-- **The file has a register for every name**, provided the channel writes for
the argument elements: a register is an element, and a name is one of them. This
is the one thing the *reduction* has to arrange about its channel, and arranging
it is what puts the file in the working region – the argument tags are the
greatest (`DescriptiveComplexity.Draw.lt_arg`). -/
theorem hasName_regLaid (zero : A)
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
        Univ A R' P' dt.KIx dt.dd)) :
    (dt.regLaid (A := A) (R' := R') (P' := P') h hord).toLayout.HasName zero :=
  fun b c => ⟨⟨(Tag.arg (toLex b), padTup zero c), harg b c⟩, rfl, rfl⟩


-- @@ L99-124 verbatim
/-- **The evaluation's working area lies below the file.** A logical address is
made of argument elements; the file's registers all hold the least marked
element, which the reduction places *below* the argument tags. So no address the
evaluation manipulates ever reaches into the file, and the walks that assume it
(`DescriptiveComplexity.Draw.Data.nexIxEvalB_reachesIn`'s `hwork`) apply
unchanged.

This is the one thing the reduction owes its own marking, and the reason the
marks are «the argument elements **and one element below them**» rather than the
argument elements alone: with the latter the least marked element would itself be
an argument element, and an address holding it would be a register's neighbor
instead of lying under the file. -/
theorem work_regLaid {bot : Univ A R' P' dt.KIx dt.dd} (hbot : WMHasInp bot)
    (hleast : ∀ y : Univ A R' P' dt.KIx dt.dd, WMHasInp y → WMLe bot y)
    (hbotarg : ∀ i : dt.KIx, bot.1 ≠ Tag.arg i)
    {r : Univ A R' P' dt.KIx dt.dd → Prop}
    (hr : ∀ x : Univ A R' P' dt.KIx dt.dd, r x → ∃ i : dt.KIx, x.1 = Tag.arg i)
    (u : dt.RegIx (A := A) (R' := R') (P' := P')) :
    WMSetLt WMLe r ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell u) := by
  refine wmSetLt_wmRegSeg_of_above h hbot hleast (fun y hy => ?_) u.2
  obtain ⟨i, hi⟩ := hr y hy
  have hlt : bot.1 < y.1 := hi ▸ lt_arg bot.1 i hbotarg
  refine ⟨(hord _ _).mpr (Or.inl hlt), fun hc => ?_⟩
  rcases (hord _ _).mp hc with h' | ⟨h', -⟩
  · exact absurd h' (asymm hlt)
  · exact absurd h' (ne_of_gt hlt)


-- @@ L126-126 verbatim
/-! ### The coherences the evaluation asks of a file -/


-- @@ L128-133 verbatim
variable (dt) in
/-- **The registers an address uses**: the ones standing for argument elements.
The register below them – the one the reduction marks so that the file lies
above the working area – is never part of a logical address. -/
def RegUse (u : dt.RegIx (A := A) (R' := R') (P' := P')) : Prop :=
  ∃ i : dt.KIx, (u.1).1 = Tag.arg i


-- @@ L135-147 verbatim
/-- **A named register stands for the element it names**: the `heltP`
coherence. -/
theorem elt_reg_regLaid (zero : A)
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
        Univ A R' P' dt.KIx dt.dd))
    (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) :
    (((dt.regLaid (A := A) (R' := R') (P' := P') h hord).toLayout.reg
        (dt.hasName_regLaid (h := h) (hord := hord) zero harg) b c).1 :
      Univ A R' P' dt.KIx dt.dd) = dt.blkElt b (pad zero c) := by
  have hb := Layout.blk_reg (dt.hasName_regLaid (h := h) (hord := hord) zero harg) b c
  have ha := Layout.arg_reg (dt.hasName_regLaid (h := h) (hord := hord) zero harg) b c
  exact Prod.ext ((tagBlk_eq_some_iff _ b).mp hb) ha


-- @@ L149-152 verbatim
/-- **A register's block is the block of the element it stands for**: the
`hblkP` coherence, both sides being the tag's own block. -/
theorem blk_regLaid_eq_tagBlk (u : dt.RegIx (A := A) (R' := R') (P' := P')) :
    (dt.regLaid (A := A) (R' := R') (P' := P') h hord).blk u = tagBlk (u.1).1 := rfl


-- @@ L154-162 verbatim
/-- **The registers are ordered like the elements they stand for**: the `hmono`
coherence, which at this file is the channel's own agreement between the tag
order and the address order. -/
theorem mono_regLaid (u u' : dt.RegIx (A := A) (R' := R') (P' := P')) :
    WMLt (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le u u' ↔
      WMLt WMLe (u.1 : Univ A R' P' dt.KIx dt.dd) u'.1 := by
  unfold WMLt
  rw [hord, hord]
  exact Iff.rfl


-- @@ L164-183 verbatim
omit [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx] in
include hord in
/-- **Nothing above a used register escapes the file**: the argument tags come
last, so an element above an argument element is an argument element, and the
reduction marks all of them. This is the `hup` coherence. -/
theorem up_regLaid
    (hargall : ∀ x : Univ A R' P' dt.KIx dt.dd, (∃ i : dt.KIx, x.1 = Tag.arg i) →
      WMHasInp x)
    {u : dt.RegIx (A := A) (R' := R') (P' := P')} (hu : dt.RegUse u)
    {x : Univ A R' P' dt.KIx dt.dd} (hlt : WMLt WMLe (u.1 : Univ A R' P' dt.KIx dt.dd) x) :
    ∃ u' : dt.RegIx (A := A) (R' := R') (P' := P'), dt.RegUse u' ∧ (u'.1 : _) = x := by
  obtain ⟨i, hi⟩ := hu
  have hx : ∃ i : dt.KIx, x.1 = Tag.arg i := by
    by_contra hc
    push Not at hc
    have hlt' : x.1 < Tag.arg i := lt_arg x.1 i hc
    rcases (hord _ _).mp hlt.1 with hb | ⟨hb, -⟩
    · rw [hi] at hb; exact absurd hb (asymm hlt')
    · rw [hi] at hb; exact absurd hb.symm (ne_of_lt hlt')
  exact ⟨⟨x, hargall x hx⟩, hx, rfl⟩


-- @@ L185-196 verbatim
omit [LinearOrder A] [LinearOrder R'] [LinearOrder P'] [Finite A] [Finite R']
  [Finite P'] [Finite dt.KIx] in
/-- **A logical address is held by the file's registers**: the `hvh`
coherence. -/
theorem ixHolds_regLaid
    (hargall : ∀ x : Univ A R' P' dt.KIx dt.dd, (∃ i : dt.KIx, x.1 = Tag.arg i) →
      WMHasInp x)
    {s : Univ A R' P' dt.KIx dt.dd → Prop}
    (hs : ∀ x : Univ A R' P' dt.KIx dt.dd, s x → ∃ i : dt.KIx, x.1 = Tag.arg i) :
    IxHolds (fun u : dt.RegIx (A := A) (R' := R') (P' := P') => (u.1 : _))
      (dt.RegUse (A := A) (R' := R') (P' := P')) s :=
  fun x hx => ⟨⟨x, hargall x (hs x hx)⟩, hs x hx, rfl⟩


-- @@ L198-208 verbatim
/-- **A named register is a used one**: it stands for an argument element. This
is the `hxdUse` the stage atom's destination registers ask for. -/
theorem regUse_reg_regLaid (zero : A)
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
        Univ A R' P' dt.KIx dt.dd))
    (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A) :
    dt.RegUse ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).toLayout.reg
      (dt.hasName_regLaid (h := h) (hord := hord) zero harg) b c) :=
  ⟨toLex b, (tagBlk_eq_some_iff _ b).mp
    (Layout.blk_reg (dt.hasName_regLaid (h := h) (hord := hord) zero harg) b c)⟩


-- @@ L210-210 verbatim
/-! ### What the file costs to walk -/


-- @@ L212-212 verbatim
section Widths


-- @@ L214-214 verbatim
variable (h) (hord)


-- @@ L216-220 verbatim
variable (dt) in
/-- **The number the register channel's walks are charged against**: `2 ^` the
number of registers, which is the size of the working region and the bound every
address of the file is under. -/
noncomputable def regBound : ℕ := 2 ^ Nat.card (dt.RegIx (A := A) (R' := R') (P' := P'))


-- @@ L222-230 verbatim
/-- **Every register of the file lies below the bound**: its address is
supported on the elements the channel writes for, and so is every address below
it once those are upward closed. -/
theorem wideRank_regLaid_cell_lt
    (hup : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y → WMHasInp x → WMHasInp y)
    (u : dt.RegIx (A := A) (R' := R') (P' := P')) :
    wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell u) <
      dt.regBound (A := A) (R' := R') (P' := P') :=
  wideRank_wmRegSeg_lt h hup u.1


-- @@ L232-244 verbatim
/-- **A step of a walk over the file costs at most the bound**: consecutive
registers differ by one bit of the address, and the whole file is below the
bound. This is the `w` of every budgeted walk, where a file laid on consecutive
addresses has `w = 1` and pays the difference in the number of registers
instead. -/
theorem gap_regLaid
    (hup : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y → WMHasInp x → WMHasInp y)
    (u u' : dt.RegIx (A := A) (R' := R') (P' := P')) :
    wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell u') -
        wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell u) ≤
      dt.regBound (A := A) (R' := R') (P' := P') := by
  have := dt.wideRank_regLaid_cell_lt h hord hup u'
  omega


-- @@ L246-248 verbatim
variable (dt) in
/-- **The width a walk to a register is charged**: twice the bound, plus two. -/
noncomputable def regW : ℕ := 2 * dt.regBound (A := A) (R' := R') (P' := P') + 2


-- @@ L250-256 verbatim
variable (dt) in
/-- **The width of the pass over the whole file**: the file's two ends, the
walk between them at one bound a step, and the marker's own address. -/
noncomputable def regWP : ℕ :=
  2 * dt.regBound (A := A) (R' := R') (P' := P') +
    Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) *
      dt.regBound (A := A) (R' := R') (P' := P') + 3


-- @@ L258-261 verbatim
variable (dt) in
/-- **The width of a read below the file**: an address under the first register
is under the bound. -/
noncomputable def regWR : ℕ := dt.regBound (A := A) (R' := R') (P' := P') + 4


-- @@ L263-276 verbatim
variable (dt) in
/-- **The width of a stage's inner loop**: a pass per bit of the address it
carries, each pass priced as `regWP`. -/
noncomputable def regWK : ℕ :=
  dt.regBound (A := A) (R' := R') (P' := P') *
      (1 + (2 * dt.regBound (A := A) (R' := R') (P' := P') + 3 +
          Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) *
            dt.regBound (A := A) (R' := R') (P' := P')) +
        (2 * dt.regBound (A := A) (R' := R') (P' := P') + 5 +
          Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) *
            dt.regBound (A := A) (R' := R') (P' := P'))) + 1 +
    (2 * dt.regBound (A := A) (R' := R') (P' := P') + 3 +
      Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) *
        dt.regBound (A := A) (R' := R') (P' := P'))


-- @@ L278-278 verbatim
section Bounds


-- @@ L280-280 verbatim
variable (hup : ∀ x y : Univ A R' P' dt.KIx dt.dd, WMLe x y → WMHasInp x → WMHasInp y)

-- @@ L281-281 verbatim
variable (gtop gbot : dt.RegIx (A := A) (R' := R') (P' := P'))


-- @@ L283-290 verbatim
/-- The walk between the file's two ends is charged one bound per register. -/
private theorem regSpan_le :
    (ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gtop -
        ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gbot) *
      dt.regBound (A := A) (R' := R') (P' := P') ≤
      Nat.card (dt.RegIx (A := A) (R' := R') (P' := P')) *
        dt.regBound (A := A) (R' := R') (P' := P') :=
  Nat.mul_le_mul_right _ (le_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (ixRank_lt_card _ gtop)))


-- @@ L292-305 verbatim
include hup in
/-- **The pass over the file fits `regWP`.** -/
theorem hwP_regLaid :
    wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gtop) + 2 +
        ((ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gtop -
            ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gbot) *
          dt.regBound (A := A) (R' := R') (P' := P') + 1) +
        wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gbot) ≤
      dt.regWP (A := A) (R' := R') (P' := P') := by
  have h1 := dt.wideRank_regLaid_cell_lt h hord hup gtop
  have h2 := dt.wideRank_regLaid_cell_lt h hord hup gbot
  have h3 := dt.regSpan_le (h := h) (hord := hord) gtop gbot
  rw [regWP]
  omega


-- @@ L307-317 verbatim
include hup in
/-- **A read below the file fits `regWR`.** -/
theorem hwR_regLaid (s : Univ A R' P' dt.KIx dt.dd → Prop)
    (hs : WMSetLt WMLe s ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gbot)) :
    wideRank s + 4 ≤ dt.regWR (A := A) (R' := R') (P' := P') := by
  have h1 := dt.wideRank_regLaid_cell_lt h hord hup gbot
  have h2 : wideRank s <
      wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gbot) :=
    (wideRank_lt_iff h _ _).mpr hs
  rw [regWR]
  omega


-- @@ L319-348 verbatim
include hup in
/-- **A stage's inner loop fits `regWK`.** -/
theorem hwK_regLaid (T : Univ A R' P' dt.KIx dt.dd → Prop)
    (hT : WMSetLt WMLe T ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gbot)) :
    wideRank T *
        (1 + (wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gtop) + 3 +
            (ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gtop -
              ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gbot) *
              dt.regBound (A := A) (R' := R') (P' := P') +
            wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gbot)) +
          (wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gtop) +
            ((ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gtop -
                ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gbot) *
              dt.regBound (A := A) (R' := R') (P' := P') + 1) +
            wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gbot) + 4)) + 1 +
      (wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gtop) + 3 +
        (ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gtop -
          ixRank (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le gbot) *
          dt.regBound (A := A) (R' := R') (P' := P') +
        wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gbot)) ≤
      dt.regWK (A := A) (R' := R') (P' := P') := by
  have h1 := dt.wideRank_regLaid_cell_lt h hord hup gtop
  have h2 := dt.wideRank_regLaid_cell_lt h hord hup gbot
  have h3 := dt.regSpan_le (h := h) (hord := hord) gtop gbot
  have h4 : wideRank T <
      wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell gbot) :=
    (wideRank_lt_iff h _ _).mpr hT
  rw [regWK]
  refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul ?_ ?_) le_rfl) ?_) le_rfl <;>
    omega


-- @@ L350-366 verbatim
include hup in
/-- **A walk to a register fits `regW`.** -/
theorem hcostR_regLaid (zero : A)
    (harg : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
      WMHasInp ((Tag.arg (toLex b), padTup (dt := dt) zero c) :
        Univ A R' P' dt.KIx dt.dd))
    (v : Univ A R' P' dt.KIx dt.dd → Prop) (b : Fin dt.ko ⊕ Fin dt.ki)
    (c : Fin dt.dd0 → A) :
    2 * (wideRank ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).cell
        ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).toLayout.reg
          (dt.hasName_regLaid (h := h) (hord := hord) zero harg) b c)) -
      wideRank v) + 2 ≤ dt.regW (A := A) (R' := R') (P' := P') := by
  have h1 := dt.wideRank_regLaid_cell_lt h hord hup
    ((dt.regLaid (A := A) (R' := R') (P' := P') h hord).toLayout.reg
      (dt.hasName_regLaid (h := h) (hord := hord) zero harg) b c)
  rw [regW]
  omega


-- @@ L368-368 verbatim
end Bounds


-- @@ L370-370 verbatim
end Widths


-- @@ L372-372 verbatim
/-! ### The file's two ends -/


-- @@ L374-374 verbatim
section Ends


-- @@ L376-376 verbatim
variable (h) (hord)


-- @@ L378-387 verbatim
/-- **The file has a greatest register**, the marked elements being finitely
many and linearly ordered. -/
theorem exists_regTop (hne : ∃ x : Univ A R' P' dt.KIx dt.dd, WMHasInp x) :
    ∃ g : dt.RegIx (A := A) (R' := R') (P' := P'),
      ∀ u, (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le u g := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, -, hmax⟩ := exists_greatest
    (isLinOrd_regLaid_le (dt := dt) (A := A) (R' := R') (P' := P') (h := h) (hord := hord))
    (P := fun _ : dt.RegIx (A := A) (R' := R') (P' := P') => True) ⟨⟨x, hx⟩, trivial⟩
  exact ⟨g, fun u => hmax u trivial⟩


-- @@ L389-398 verbatim
/-- **The file has a least register**, the one the reduction places below the
argument elements. -/
theorem exists_regBot (hne : ∃ x : Univ A R' P' dt.KIx dt.dd, WMHasInp x) :
    ∃ g : dt.RegIx (A := A) (R' := R') (P' := P'),
      ∀ u, (dt.regLaid (A := A) (R' := R') (P' := P') h hord).le g u := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, -, hmin⟩ := exists_least
    (isLinOrd_regLaid_le (dt := dt) (A := A) (R' := R') (P' := P') (h := h) (hord := hord))
    (P := fun _ : dt.RegIx (A := A) (R' := R') (P' := P') => True) ⟨⟨x, hx⟩, trivial⟩
  exact ⟨g, fun u => hmin u trivial⟩


-- @@ L400-400 verbatim
end Ends


-- @@ L402-402 verbatim
end RegLaid


-- @@ L404-404 verbatim
end Data


-- @@ L406-406 verbatim
end Draw


-- @@ L408-408 verbatim
end DescriptiveComplexity
