/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.BlkFile
import DescriptiveComplexity.Problems.Wide.DrawName


-- @@ L9-39 verbatim
/-!
# The layout of a clocked program's file

`DescriptiveComplexity.blkFile` gives a program one register per block and
tuple. This file reads that as a `DescriptiveComplexity.Draw.LaidFile`, which is
what the background (`DescriptiveComplexity.Draw.Data.ixBack`) and the loops
run against, and checks the two properties a navigation *by name* asks of a
layout.

**The width is `dd`, not `dd₀`, and that is what a seek needs.** A mark carries
`dd₀` coordinates, so a *name* is a block and `dd₀` coordinates, and a scan by
name only ever stops at a canonically padded register – which would make a file
of `dd₀`-tuples enough for the copy loops. It is not enough for the mirror: the
mirror and the target of a seek are held one bit per register, and the addresses
a seek passes through are every logical address below its target, which mark
argument elements of *every* tuple. So the index is `Option K × (Fin dd → A)`,
the register's tuple is its index's, and the named registers are those the
padding pins – exactly the ones inside it.

The two properties are then:

* `DescriptiveComplexity.Draw.Layout.NameSep` – a block and the named
  coordinates spell at most one register: the index *is* the pair, the
  coordinates below `dd₀` are the name's, and those above are `zero` on both
  sides because a scan by name asks its registers to be canonically padded.
* `DescriptiveComplexity.Draw.Layout.HasName` – and at least one, for every
  block and every name, the register being the name padded.

Together they are the stopping condition of a scan by name
(`DescriptiveComplexity.Draw.Data.nameGF_unique_addr`).
-/


-- @@ L41-41 verbatim
namespace DescriptiveComplexity


-- @@ L43-43 verbatim
namespace Draw


-- @@ L45-45 verbatim
open FirstOrder


-- @@ L47-47 verbatim
open Language Structure


-- @@ L49-49 verbatim
section BlkLayout


-- @@ L51-51 verbatim
variable {L : Language.{0, 0}} (dt : Data L) {A R' P' : Type}

-- @@ L52-52 verbatim
variable [LinearOrder A] [LinearOrder R'] [LinearOrder P']

-- @@ L53-53 verbatim
variable [Finite A] [Finite R'] [Finite P'] [Finite dt.KIx]

-- @@ L54-54 verbatim
variable [Language.wide.Structure (Univ A R' P' dt.KIx dt.dd)]

-- @@ L55-55 verbatim
variable [Finite (Univ A R' P' dt.KIx dt.dd)]


-- @@ L57-57 verbatim
namespace Data


-- @@ L59-74 verbatim
/-- **The file a clocked program lays out, with its layout**: the registers of
`DescriptiveComplexity.blkFile`, in the block-major order, each naming its own
block and its own tuple. -/
noncomputable def blkLaid
    (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))
    {base : ℕ} (hpos : 0 < base)
    (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
      Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
        (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p}) :
    LaidFile dt A R' P' (Wide.BlkIx dt.KIx A dt.dd) where
  cell := (blkFile A dt.KIx (Univ A R' P' dt.KIx dt.dd) dt.dd h hpos hbase).cell
  le := Wide.blkLe dt.KIx A dt.dd
  blk := Prod.fst
  arg := Prod.snd
  strictMono := (blkFile A dt.KIx (Univ A R' P' dt.KIx dt.dd) dt.dd h hpos hbase).strictMono
  cell_nonempty := (blkFile A dt.KIx (Univ A R' P' dt.KIx dt.dd) dt.dd h hpos hbase).cell_nonempty


-- @@ L76-76 verbatim
variable {dt}


-- @@ L78-84 verbatim
/-! ### The widths of the laid file

Every walk of the evaluation is charged against a width, and at the laid file
each of them is bounded by the stretch the file occupies: the base, the number
of registers, and – for what walks the *tape* rather than the file – the number
of addresses. These are the `hgap`, `hcostR`, `hwP`, `hwR` and `hwK` the legs
ask for, none of them computed. -/


-- @@ L86-86 verbatim
section Widths


-- @@ L88-88 verbatim
variable (h : IsLinOrd (WMLe (A := Univ A R' P' dt.KIx dt.dd)))

-- @@ L89-89 verbatim
variable {base : ℕ} (hpos : 0 < base)

-- @@ L90-92 verbatim
variable (hbase : base + Nat.card (Wide.BlkIx dt.KIx A dt.dd) ≤
  Nat.card {p : WPoint (Univ A R' P' dt.KIx dt.dd) //
    (wideData (Univ A R' P' dt.KIx dt.dd)).Posn p})


-- @@ L94-99 verbatim
omit [Finite R'] [Finite P'] in
/-- **A register's rank is its index's, above the base.** -/
theorem wideRank_blkLaid_cell (u : Wide.BlkIx dt.KIx A dt.dd) :
    wideRank ((dt.blkLaid h hpos hbase).cell u) =
      base + ixRank (Wide.blkLe dt.KIx A dt.dd) u :=
  wideRank_ixSegCell (Wide.blkLe dt.KIx A dt.dd) h hbase u


-- @@ L101-101 verbatim
variable [Nonempty A]


-- @@ L103-103 verbatim
end Widths


-- @@ L105-105 verbatim
end Data


-- @@ L107-107 verbatim
end BlkLayout


-- @@ L109-109 verbatim
end Draw


-- @@ L111-111 verbatim
end DescriptiveComplexity
