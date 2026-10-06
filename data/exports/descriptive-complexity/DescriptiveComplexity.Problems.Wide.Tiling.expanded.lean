/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Tiling.Defs
import DescriptiveComplexity.Problems.Wide.WellFormed


-- @@ L9-46 verbatim
/-!
# The wide tiling: a square addressed by the subsets of its instance

The tile system of `DescriptiveComplexity.TILING` with one exponent added *in
the semantics of the problem*, exactly as `DescriptiveComplexity.WideAccept`
adds one to a machine:

> the grid is indexed by the **subsets** of the instance, while the tiles –
> with their compatibilities, the bottom row and the accepting mark – stay an
> ordinary part of the instance.

So an instance of size `n` asks whether a `2ⁿ × 2ⁿ` square can be tiled, which
is the classical second complete problem of NEXPTIME beside a machine. Nothing
is said about resources: the universe of the tiling *is* the universe of an
exponential expansion of the instance
(`DescriptiveComplexity.Problems.Wide.TilingExp`), so membership is the
composition `TILING ∘ expansion`.

## Where the order comes from

As for the wide machine, a decision problem may not read the ambient order of
its instance, so the instance carries its own order `wtLe` and the order on
addresses is the binary-number order it induces
(`DescriptiveComplexity.WMSetLe`). Linearity is a promise, folded into the
yes-instances through `DescriptiveComplexity.TileData.WellFormed`.

## Where the bottom row goes

The bottom row is described at the **initial-segment addresses**: the address
`{y | y ≤ x}` may carry the tiles `wtFirst x` names, and every other address may
carry those `wtFirst` names of no element at all – the same device as the wide
machine's input (`wmInp`), and for the same reason: a first-order condition on
the *element* is what an expansion can carry, while a listing of `2ⁿ` cells is
not.
-/

/- The vocabulary of wide tile systems lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.wide`. -/

-- @@ L47-47 verbatim
namespace FirstOrder


-- @@ L49-49 verbatim
namespace Language


-- @@ L51-80 verbatim
/-- Relation symbols of wide tile-system instances: the tiles of
`FirstOrder.Language.tiling` with their compatibilities, and the positions and
their order replaced by an order on the elements – the digits of an address. -/
inductive wtileRel : ℕ → Type
  /-- `wtLe x y`: the order on the elements, along which an address is read as a
  binary number. -/
  | wle : wtileRel 2
  /-- `wtDig x`: `x` is a digit – one of the elements the grid's coordinates are
  subsets of. -/
  | dig : wtileRel 1
  /-- `wtTile t`: `t` is a tile. -/
  | tile : wtileRel 1
  /-- `wtAcc t`: `t` is an accepting tile. -/
  | tacc : wtileRel 1
  /-- `wtHoriz t t'`: `t'` may stand immediately to the right of `t`. -/
  | horiz : wtileRel 2
  /-- `wtVert t t'`: `t'` may stand immediately above `t`. -/
  | vert : wtileRel 2
  /-- `wtFirst x t`: the bottom row's cell of `x` may carry `t`. -/
  | first : wtileRel 2
  /-- `wtBase t`: `t` is a base tile – what the bottom row carries where the
  description says nothing. -/
  | base : wtileRel 1
  /-- `wtStart t`: `t` is a start tile – what the corner of the grid carries. -/
  | tstart : wtileRel 1
  /-- `wtEdgeL t`: `t` may stand in the leftmost column. -/
  | ledge : wtileRel 1
  /-- `wtEdgeR t`: `t` may stand in the rightmost column. -/
  | redge : wtileRel 1
  deriving DecidableEq


-- @@ L82-85 verbatim
/-- The relational vocabulary of wide tile-system instances. -/
protected def wtile : Language :=
  ⟨fun _ => Empty, wtileRel⟩
  deriving IsRelational


-- @@ L87-88 verbatim
/-- The order on the elements of the instance. -/
abbrev wtLe : Language.wtile.Relations 2 := .wle


-- @@ L90-91 verbatim
/-- The digit symbol. -/
abbrev wtDig : Language.wtile.Relations 1 := .dig


-- @@ L93-94 verbatim
/-- The tile symbol. -/
abbrev wtTile : Language.wtile.Relations 1 := .tile


-- @@ L96-97 verbatim
/-- The accepting-tile symbol. -/
abbrev wtAcc : Language.wtile.Relations 1 := .tacc


-- @@ L99-100 verbatim
/-- The horizontal-compatibility symbol. -/
abbrev wtHoriz : Language.wtile.Relations 2 := .horiz


-- @@ L102-103 verbatim
/-- The vertical-compatibility symbol. -/
abbrev wtVert : Language.wtile.Relations 2 := .vert


-- @@ L105-106 verbatim
/-- The bottom-row symbol. -/
abbrev wtFirst : Language.wtile.Relations 2 := .first


-- @@ L108-109 verbatim
/-- The base-tile symbol. -/
abbrev wtBase : Language.wtile.Relations 1 := .base


-- @@ L111-112 verbatim
/-- The start-tile symbol. -/
abbrev wtStart : Language.wtile.Relations 1 := .tstart


-- @@ L114-115 verbatim
/-- The left-edge symbol. -/
abbrev wtEdgeL : Language.wtile.Relations 1 := .ledge


-- @@ L117-118 verbatim
/-- The right-edge symbol. -/
abbrev wtEdgeR : Language.wtile.Relations 1 := .redge


-- @@ L120-120 verbatim
end Language


-- @@ L122-122 verbatim
end FirstOrder


-- @@ L124-124 verbatim
namespace DescriptiveComplexity


-- @@ L126-126 verbatim
open FirstOrder


-- @@ L128-128 verbatim
open Language Structure


-- @@ L130-130 verbatim
/-! ### The shorthands of the vocabulary -/


-- @@ L132-132 verbatim
section Shorthands


-- @@ L134-134 verbatim
variable {A : Type} [Language.wtile.Structure A]


-- @@ L136-137 verbatim
/-- The order on the elements. -/
def WTLe (a b : A) : Prop := RelMap wtLe ![a, b]


-- @@ L139-140 verbatim
/-- Being a digit: one of the elements the grid's coordinates are subsets of. -/
def WTDig (a : A) : Prop := RelMap wtDig ![a]


-- @@ L142-143 verbatim
/-- Being a tile. -/
def WTTile (a : A) : Prop := RelMap wtTile ![a]


-- @@ L145-146 verbatim
/-- Being an accepting tile. -/
def WTAcc (a : A) : Prop := RelMap wtAcc ![a]


-- @@ L148-149 verbatim
/-- Horizontal compatibility. -/
def WTHoriz (a b : A) : Prop := RelMap wtHoriz ![a, b]


-- @@ L151-152 verbatim
/-- Vertical compatibility. -/
def WTVert (a b : A) : Prop := RelMap wtVert ![a, b]


-- @@ L154-155 verbatim
/-- The bottom row, at the cell of an element. -/
def WTFirst (a b : A) : Prop := RelMap wtFirst ![a, b]


-- @@ L157-158 verbatim
/-- Being a base tile. -/
def WTBase (a : A) : Prop := RelMap wtBase ![a]


-- @@ L160-161 verbatim
/-- Being a start tile. -/
def WTStart (a : A) : Prop := RelMap wtStart ![a]


-- @@ L163-164 verbatim
/-- Being a left-edge tile: one the leftmost column may carry. -/
def WTEdgeL (a : A) : Prop := RelMap wtEdgeL ![a]


-- @@ L166-167 verbatim
/-- Being a right-edge tile: one the rightmost column may carry. -/
def WTEdgeR (a : A) : Prop := RelMap wtEdgeR ![a]


-- @@ L169-171 verbatim
/-- **An element the bottom row is described at**: one whose cell carries a
tile. These are the elements the file has cells for. -/
def WTHasFirst (a : A) : Prop := ∃ t : A, WTFirst a t


-- @@ L173-173 verbatim
end Shorthands


-- @@ L175-175 verbatim
/-! ### The universe and the tile system -/


-- @@ L177-177 verbatim
section System


-- @@ L179-179 verbatim
variable {A : Type} [Language.wtile.Structure A]


-- @@ L181-187 verbatim
/-- Being a position: an address is one exactly when it holds digits alone, so
the grid is indexed by the subsets of the *marked* part of the instance. That is
what leaves the instance room for its tiles: a tile is an element like any
other, and only the digits are coordinates. -/
def wtpPosn : WPoint A → Prop
  | Sum.inl s => ∀ x, s x → WTDig x
  | Sum.inr _ => False


-- @@ L189-196 verbatim
/-- The order on the universe of the tiling: addresses first, in the
binary-number order they inherit from the instance's own order, then the tiles
in that same order. -/
def wtpLe : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inl t => WMSetLe WTLe s t
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr x, Sum.inr y => WTLe x y


-- @@ L198-206 verbatim
/-- The bottom row: the cell of `x` – the segment `x` cuts among the elements
the description names – may carry the tiles of `x`, and every other address a
base tile. That is the same device as the register channel's input
(`DescriptiveComplexity.wpInpReg`): a file of cells, not the ruler of all the
segments, because a clocked machine's tape is described the same way and that is
where this problem's hardness comes from. -/
def wtpFirst : WPoint A → WPoint A → Prop
  | Sum.inl s, Sum.inr y => ∃ x, WMFileSeg WTLe WTHasFirst s x ∧ WTFirst x y
  | _, _ => False


-- @@ L208-222 verbatim
variable (A) in
/-- **The wide tile system an instance describes**: the tiles read off the
instance, the positions being the addresses. -/
def wideTileData : TileData (WPoint A) where
  Posn := wtpPosn
  Le := wtpLe
  Tile := wpMark WTTile
  Acc := wpMark WTAcc
  Horiz := wpAttr WTHoriz
  Vert := wpAttr WTVert
  First := wtpFirst
  Base := wpMark WTBase
  Start := wpMark WTStart
  EdgeL := wpMark WTEdgeL
  EdgeR := wpMark WTEdgeR


-- @@ L224-251 verbatim
/-- **The order of a wide tiling is linear** as soon as the instance's is: the
addresses are ordered as binary numbers, the tiles as in the instance, and the
addresses come first. -/
theorem isLinOrd_wtpLe [Finite A] (h : IsLinOrd (WTLe (A := A))) :
    IsLinOrd (wtpLe (A := A)) := by
  have hs := isLinOrd_wmSetLe h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (s | x)
    · exact hs.1 s
    · exact h.1 x
  · rintro (s | x) (t | y) (u | z) h1 h2 <;>
      first
        | exact trivial
        | exact False.elim h1
        | exact False.elim h2
        | exact hs.2.1 _ _ _ h1 h2
        | exact h.2.1 _ _ _ h1 h2
  · rintro (s | x) (t | y) h1 h2 <;>
      first
        | exact False.elim h1
        | exact False.elim h2
        | exact congrArg Sum.inl (hs.2.2.1 _ _ h1 h2)
        | exact congrArg Sum.inr (h.2.2.1 _ _ h1 h2)
  · rintro (s | x) (t | y)
    · exact hs.2.2.2 s t
    · exact Or.inl trivial
    · exact Or.inr trivial
    · exact h.2.2.2 x y


-- @@ L253-258 verbatim
/-- **The promise of a wide tiling is a promise about its instance**: the grid
adds nothing to it, the empty address being a position whatever the instance
says. -/
theorem wideTileData_wellFormed [Finite A] (h : IsLinOrd (WTLe (A := A))) :
    (wideTileData A).WellFormed :=
  ⟨isLinOrd_wtpLe h, ⟨Sum.inl fun _ => False, fun _ hc => hc.elim⟩⟩


-- @@ L260-260 verbatim
end System


-- @@ L262-262 verbatim
/-! ### Isomorphism-invariance -/


-- @@ L264-264 verbatim
section Transport


-- @@ L266-266 verbatim
variable {A B : Type} [Language.wtile.Structure A] [Language.wtile.Structure B]


-- @@ L268-280 verbatim
/-- **An isomorphism of instances is a bijection of the tilings' universes**:
an address goes to its image, a tile to its image. -/
def wtPointEquiv (e : A ≃[Language.wtile] B) : WPoint A ≃ WPoint B where
  toFun := Sum.map (fun s y => s (e.symm y)) e
  invFun := Sum.map (fun t x => t (e x)) e.symm
  left_inv := by
    rintro (s | x)
    · exact congrArg Sum.inl (funext fun z => by simp only [e.symm_apply_apply])
    · exact congrArg Sum.inr (e.symm_apply_apply x)
  right_inv := by
    rintro (t | y)
    · exact congrArg Sum.inl (funext fun z => by simp only [e.apply_symm_apply])
    · exact congrArg Sum.inr (e.apply_symm_apply y)


-- @@ L282-282 verbatim
variable (e : A ≃[Language.wtile] B)


-- @@ L284-284 verbatim
theorem wtLe_map (a a' : A) : WTLe a a' ↔ WTLe (e a) (e a') := relMap_equiv₂ e wtLe a a'


-- @@ L286-286 verbatim
theorem wtTile_map (a : A) : WTTile a ↔ WTTile (e a) := relMap_equiv₁ e wtTile a


-- @@ L288-288 verbatim
theorem wtAcc_map (a : A) : WTAcc a ↔ WTAcc (e a) := relMap_equiv₁ e wtAcc a


-- @@ L290-291 verbatim
theorem wtHoriz_map (a a' : A) : WTHoriz a a' ↔ WTHoriz (e a) (e a') :=
  relMap_equiv₂ e wtHoriz a a'


-- @@ L293-294 verbatim
theorem wtVert_map (a a' : A) : WTVert a a' ↔ WTVert (e a) (e a') :=
  relMap_equiv₂ e wtVert a a'


-- @@ L296-297 verbatim
theorem wtFirst_map (a a' : A) : WTFirst a a' ↔ WTFirst (e a) (e a') :=
  relMap_equiv₂ e wtFirst a a'


-- @@ L299-299 verbatim
theorem wtBase_map (a : A) : WTBase a ↔ WTBase (e a) := relMap_equiv₁ e wtBase a


-- @@ L301-301 verbatim
theorem wtDig_map (a : A) : WTDig a ↔ WTDig (e a) := relMap_equiv₁ e wtDig a


-- @@ L303-303 verbatim
theorem wtStart_map (a : A) : WTStart a ↔ WTStart (e a) := relMap_equiv₁ e wtStart a


-- @@ L305-305 verbatim
theorem wtEdgeL_map (a : A) : WTEdgeL a ↔ WTEdgeL (e a) := relMap_equiv₁ e wtEdgeL a


-- @@ L307-307 verbatim
theorem wtEdgeR_map (a : A) : WTEdgeR a ↔ WTEdgeR (e a) := relMap_equiv₁ e wtEdgeR a


-- @@ L309-313 verbatim
/-- The elements the bottom row is described at correspond. -/
theorem wtHasFirst_map (a : A) : WTHasFirst a ↔ WTHasFirst (e a) := by
  refine ⟨fun ⟨t, ht⟩ => ⟨e t, (wtFirst_map e a t).mp ht⟩, fun ⟨t, ht⟩ => ⟨e.symm t, ?_⟩⟩
  refine (wtFirst_map e a (e.symm t)).mpr ?_
  rwa [e.apply_symm_apply]


-- @@ L315-333 verbatim
/-- And so do the cells of the file. -/
theorem wtFileSeg_map (s : A → Prop) (x : A) :
    WMFileSeg WTLe WTHasFirst s x ↔
      WMFileSeg WTLe WTHasFirst (fun y => s (e.symm y)) (e x) := by
  refine ⟨fun h y => (h (e.symm y)).trans ?_, fun h y => ?_⟩
  · constructor
    · rintro ⟨h1, h2⟩
      have h1' := (wtLe_map e (e.symm y) x).mp h1
      have h2' := (wtHasFirst_map e (e.symm y)).mp h2
      rw [e.apply_symm_apply] at h1' h2'
      exact ⟨h1', h2'⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(wtLe_map e (e.symm y) x).mpr ?_, (wtHasFirst_map e (e.symm y)).mpr ?_⟩
      · rwa [e.apply_symm_apply]
      · rwa [e.apply_symm_apply]
  · have h1 := h (e y)
    simp only [e.symm_apply_apply] at h1
    exact h1.trans ⟨fun ⟨ha, hb⟩ => ⟨(wtLe_map e y x).mpr ha, (wtHasFirst_map e y).mpr hb⟩,
      fun ⟨ha, hb⟩ => ⟨(wtLe_map e y x).mp ha, (wtHasFirst_map e y).mp hb⟩⟩


-- @@ L335-345 verbatim
/-- The positions correspond: an address of digits is a position, a tile is
not. -/
theorem wtPosn_map (p : WPoint A) :
    (wideTileData A).Posn p ↔ (wideTileData B).Posn (wtPointEquiv e p) := by
  rcases p with s | x
  · refine ⟨fun h y hy => ?_, fun h y hy => ?_⟩
    · have hd := (wtDig_map e (e.symm y)).mp (h (e.symm y) hy)
      rwa [e.apply_symm_apply] at hd
    · refine (wtDig_map e y).mpr (h (e y) ?_)
      simpa only [e.symm_apply_apply] using hy
  · exact Iff.rfl


-- @@ L347-355 verbatim
/-- The orders correspond: the binary-number order on addresses is the
instance's order read through the isomorphism. -/
theorem wtLe_point_map (p q : WPoint A) :
    (wideTileData A).Le p q ↔ (wideTileData B).Le (wtPointEquiv e p) (wtPointEquiv e q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact wmSetLe_congr e.toEquiv (fun a a' => wtLe_map e a a') s t
  · exact Iff.rfl
  · exact Iff.rfl
  · exact wtLe_map e x y


-- @@ L357-362 verbatim
/-- The tiles correspond. -/
theorem wtTile_point_map (p : WPoint A) :
    (wideTileData A).Tile p ↔ (wideTileData B).Tile (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtTile_map e x


-- @@ L364-369 verbatim
/-- The accepting tiles correspond. -/
theorem wtAcc_point_map (p : WPoint A) :
    (wideTileData A).Acc p ↔ (wideTileData B).Acc (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtAcc_map e x


-- @@ L371-379 verbatim
/-- Horizontal compatibility corresponds. -/
theorem wtHoriz_point_map (p q : WPoint A) :
    (wideTileData A).Horiz p q ↔
      (wideTileData B).Horiz (wtPointEquiv e p) (wtPointEquiv e q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact wtHoriz_map e x y


-- @@ L381-389 verbatim
/-- Vertical compatibility corresponds. -/
theorem wtVert_point_map (p q : WPoint A) :
    (wideTileData A).Vert p q ↔
      (wideTileData B).Vert (wtPointEquiv e p) (wtPointEquiv e q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact wtVert_map e x y


-- @@ L391-405 verbatim
/-- The bottom row corresponds: the cell of an element goes to the cell of its
image. -/
theorem wtFirst_point_map (p q : WPoint A) :
    (wideTileData A).First p q ↔
      (wideTileData B).First (wtPointEquiv e p) (wtPointEquiv e q) := by
  rcases p with s | x <;> rcases q with t | y
  · exact Iff.rfl
  · refine ⟨fun ⟨z, hseg, hf⟩ => ⟨e z, (wtFileSeg_map e s z).mp hseg,
      (wtFirst_map e z y).mp hf⟩, fun ⟨z, hseg, hf⟩ => ⟨e.symm z, ?_, ?_⟩⟩
    · refine (wtFileSeg_map e s (e.symm z)).mpr ?_
      rwa [e.apply_symm_apply]
    · refine (wtFirst_map e (e.symm z) y).mpr ?_
      rwa [e.apply_symm_apply]
  · exact Iff.rfl
  · exact Iff.rfl


-- @@ L407-412 verbatim
/-- The base tiles correspond. -/
theorem wtBase_point_map (p : WPoint A) :
    (wideTileData A).Base p ↔ (wideTileData B).Base (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtBase_map e x


-- @@ L414-419 verbatim
/-- The start tiles correspond. -/
theorem wtStart_point_map (p : WPoint A) :
    (wideTileData A).Start p ↔ (wideTileData B).Start (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtStart_map e x


-- @@ L421-426 verbatim
/-- The left-edge tiles correspond. -/
theorem wtEdgeL_point_map (p : WPoint A) :
    (wideTileData A).EdgeL p ↔ (wideTileData B).EdgeL (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtEdgeL_map e x


-- @@ L428-433 verbatim
/-- And so do the right-edge tiles. -/
theorem wtEdgeR_point_map (p : WPoint A) :
    (wideTileData A).EdgeR p ↔ (wideTileData B).EdgeR (wtPointEquiv e p) := by
  rcases p with s | x
  · exact Iff.rfl
  · exact wtEdgeR_map e x


-- @@ L435-435 verbatim
end Transport


-- @@ L437-437 verbatim
/-! ### The problem -/


-- @@ L439-439 verbatim
section Problem


-- @@ L441-451 verbatim
/-- **The two halves transport**, in either direction: the wide tile system of
the image is the source's read through the isomorphism. -/
theorem wideTile_map {A B : Type} [Language.wtile.Structure A] [Language.wtile.Structure B]
    (e : A ≃[Language.wtile] B)
    (h : (wideTileData A).WellFormed ∧ (wideTileData A).Tileable) :
    (wideTileData B).WellFormed ∧ (wideTileData B).Tileable :=
  ⟨TileData.wellFormed_map _ (wtPointEquiv e) _ (wtPosn_map e) (wtLe_point_map e) h.1,
    TileData.tileable_map _ (wtPointEquiv e) _ (wtPosn_map e) (wtLe_point_map e)
      (wtTile_point_map e) (wtAcc_point_map e) (wtHoriz_point_map e)
      (wtVert_point_map e) (wtFirst_point_map e) (wtBase_point_map e)
      (wtStart_point_map e) (wtEdgeL_point_map e) (wtEdgeR_point_map e) h.2⟩


-- @@ L453-459 verbatim
/-- **Tiling a wide square.** Can the square whose sides are the *subsets* of
the instance be tiled, with the bottom row the description allows and an
accepting tile somewhere? The well-formedness promises are folded into the
yes-instances, exactly as for `DescriptiveComplexity.WideAccept`. -/
def WideTiling : DecisionProblem Language.wtile where
  Holds := fun A _ => (wideTileData A).WellFormed ∧ (wideTileData A).Tileable
  iso_invariant := fun {_ _} _ _ e => ⟨wideTile_map e, wideTile_map e.symm⟩


-- @@ L461-461 verbatim
end Problem


-- @@ L463-463 verbatim
end DescriptiveComplexity
