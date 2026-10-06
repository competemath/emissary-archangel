/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawData
import DescriptiveComplexity.Problems.Wide.DrawTripKits
import DescriptiveComplexity.Problems.Wide.DrawIncrKit
import DescriptiveComplexity.Problems.Wide.DrawSweepKit
import DescriptiveComplexity.Problems.Wide.DrawAdvKit
import DescriptiveComplexity.Problems.Wide.DrawSeekKit


-- @@ L13-28 verbatim
/-!
# The call sites' kits, at the concrete slots

The kit instantiations of the EXPSPACE program: each call site of the program
is one of the kit shapes of the layer, at the slot
inventory of `DescriptiveComplexity.Problems.Wide.DrawSlots`. This file fixes
the slots and guards; the phase embeddings stay parameters (each call site
gets its own copy of the shape's phases in the program's phase sum), and so
does the control location a name guard compares against (the `Ctl` sizing is
fixed with the site enumeration, not here).

The register-file service slots are the same for every kit – `reg` the
register mark, `regLast` the file-top mark (the greatest element's cell *is*
the file's top), `wk` the working-cell marker – and the guards are exactly
the slot conditions the kits' separation lemmas were built around.
-/


-- @@ L30-30 verbatim
namespace DescriptiveComplexity


-- @@ L32-32 verbatim
namespace Draw


-- @@ L34-34 verbatim
open FirstOrder


-- @@ L36-36 verbatim
open Language Structure


-- @@ L38-38 verbatim
namespace Data


-- @@ L40-40 verbatim
variable {L : Language.{0, 0}} (dt : Data L) {A Q P : Type}


-- @@ L42-46 verbatim
/-! ### Slot distinctness

The facts every discharge asks about the service slots, provable once: the
walked registers, the register mark, the file-top mark and the marker are
pairwise distinct constructors. -/


-- @@ L48-48 verbatim
theorem mir_ne_reg : (Slot.mir : dt.SlotIx) ≠ .reg := fun h => nomatch h


-- @@ L50-50 verbatim
theorem tgt_ne_reg : (Slot.tgt : dt.SlotIx) ≠ .reg := fun h => nomatch h


-- @@ L52-52 verbatim
theorem regLast_ne_mir : (Slot.regLast : dt.SlotIx) ≠ .mir := fun h => nomatch h


-- @@ L54-54 verbatim
theorem regLast_ne_tgt : (Slot.regLast : dt.SlotIx) ≠ .tgt := fun h => nomatch h


-- @@ L56-56 verbatim
theorem wk_ne_mir : (Slot.wk : dt.SlotIx) ≠ .mir := fun h => nomatch h


-- @@ L58-58 verbatim
theorem wk_ne_tgt : (Slot.wk : dt.SlotIx) ≠ .tgt := fun h => nomatch h


-- @@ L60-60 verbatim
theorem tgt_ne_mir : (Slot.tgt : dt.SlotIx) ≠ .mir := fun h => nomatch h


-- @@ L62-62 verbatim
theorem ltp_ne_mir : (Slot.ltp : dt.SlotIx) ≠ .mir := fun h => nomatch h


-- @@ L64-64 verbatim
theorem bot_ne_mir : (Slot.bot : dt.SlotIx) ≠ .mir := fun h => nomatch h


-- @@ L66-66 verbatim
/-! ### The plain sweeps: COMPARE and COPY -/


-- @@ L68-74 verbatim
/-- **COMPARE's kit**: one question per cell of the logical interval – every
stage track agrees with its next. -/
def compareKit (one : A) (emb : SweepPh → P) : FlagSweepKit A Q dt.SlotIx P where
  t := .mir
  ltp := .ltp
  TestG := fun g => ∀ i : dt.d.B.ι, (g (.old i) = one ↔ g (.new i) = one)
  emb := emb


-- @@ L76-84 verbatim
/-- **COPY's kit**: every stage track takes its next's digit, the next stage
riding along for the following round. -/
def copyKit (ph : P) : WriteSweepKit A Q dt.SlotIx P where
  t := .mir
  ltp := .ltp
  wrG := fun g s => match s with
    | .old i => g (.new i)
    | s' => g s'
  ph := ph


-- @@ L86-86 verbatim
/-! ### The register-file trips -/


-- @@ L88-95 verbatim
/-- **The random access**: MIRROR sought to TARGET, marker in tow. -/
def seekKit (emb : SeekPh → P) : SeekKit A Q dt.SlotIx P where
  t := .mir
  tg := .tgt
  rg := .reg
  rl := .regLast
  wk := .wk
  emb := emb


-- @@ L97-100 verbatim
/-- **One round of the outer sweep**: the working cell advances one address,
MIRROR incremented in tow. -/
def advKit (emb : AdvPh → P) : AdvKit A Q dt.SlotIx P :=
  ⟨.mir, .reg, .regLast, .wk, emb⟩


-- @@ L102-104 verbatim
/-- Clearing the MIRROR register, at a random access's reset. -/
def clearMirKit (emb : TrackPh → P) : ClearKit A Q dt.SlotIx P :=
  ⟨.mir, .reg, .regLast, .wk, emb⟩


-- @@ L106-114 verbatim
/-- **TARGET := the logical top**: the pattern write of startup – the digit
set exactly at the argument-tagged cells, read off the one-hot marks. -/
def tgtTopKit (one : A) (emb : TrackPh → P) : MapKit A Q dt.SlotIx P where
  t := .tgt
  rg := .reg
  rl := .regLast
  wk := .wk
  Fb := fun g => ∃ b : Fin dt.ko ⊕ Fin dt.ki, g (.blk (some b)) = one
  emb := emb


-- @@ L116-116 verbatim
/-! ### The navigation-by-name trips -/


-- @@ L118-128 verbatim
/-- **The name guard, at computed coordinates**: this cell is the canonically
padded cell of the element whose block is `b` and whose first `dd0`
coordinates are the ones the control *computes* through `cf`. The trips of
the coordinate loops read the control's slots directly
(`DescriptiveComplexity.Draw.Data.nameG`); the leaf reads of the element
loops compute an encoded tuple from them
(`DescriptiveComplexity.Problems.Wide.DrawName`), and both are this guard. -/
def nameGF (one : A) (b : Fin dt.ko ⊕ Fin dt.ki) (cf : (Q → A) → Fin dt.dd0 → A) :
    (Q → A) → (dt.SlotIx → A) → Prop :=
  fun fc g => g (.blk (some b)) = one ∧ g .pdd = one ∧
    ∀ j : Fin dt.dd0, g (.name j) = cf fc j


-- @@ L130-135 verbatim
/-- **The name guard**: this cell is the canonically padded cell of the
element whose block is `b` and whose first `dd0` coordinates the control
holds at `coord`. -/
def nameG (one : A) (b : Fin dt.ko ⊕ Fin dt.ki) (coord : Fin dt.dd0 → Q) :
    (Q → A) → (dt.SlotIx → A) → Prop :=
  dt.nameGF one b fun fc j => fc (coord j)


-- @@ L137-137 verbatim
end Data


-- @@ L139-139 verbatim
end Draw


-- @@ L141-141 verbatim
end DescriptiveComplexity
