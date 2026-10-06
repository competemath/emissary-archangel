/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Complexity
import DescriptiveComplexity.Numbers.BinRel


-- @@ L9-51 verbatim
/-!
# Tiling a square: the local problem behind the machines

The problem the exponential classes are usually read on ([Fürer
1983][furer1983domino]; [Börger, Grädel & Gurevich 1997][borger1997classical]
is the book-length account).

A **tile system** is a set of tiles with two compatibility relations – which
tile may stand immediately to the right of which, and which immediately above
which – a description of the bottom row, and a set of accepting tiles. The
question is whether the square whose sides are the *positions* of the instance
can be tiled: every cell carries a tile, neighbors are compatible, the bottom
row and the two edge columns are as described, and some cell carries an
accepting tile.

Nothing here is about resources. As with `DescriptiveComplexity.NTMAccept`, the
grid is indexed by the elements the instance marks as positions, so an instance
of size `n` asks about an `n × n` square and the problem sits in NP; read over
an exponential expansion, the same definition asks about a `2ⁿ × 2ⁿ` square and
sits one exponential up (`DescriptiveComplexity.Problems.Wide.Tiling`).

## Why the tiling and not the machine

A tile system has no head, no clock and no time: its conditions are *local* in
two dimensions and quantify over neighbors alone. That is what makes it the
cheap second complete problem of a class whose first one is a machine – the
work is a drawing, not an evaluator.

## The shape of the conditions

The two edge columns carry tiles marked `ledge` and `redge`, which is what the
border colors of a classical tiling problem do: a condition on neighbors says
nothing about the column at either end, where one neighbor is missing.

The bottom row is described by a relation `first p t` rather than listed,
exactly as a machine's initial tape is described by `inp p a`: a first-order
condition on the position, which is what an expansion can carry. The accepting
condition is a mark on tiles, and it is what turns a *tiling* into a *decision*:
without it every tile system with a compatible bottom row is a yes-instance.
-/

/- The vocabulary of tile systems lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.turing`. -/

-- @@ L52-52 verbatim
namespace FirstOrder


-- @@ L54-54 verbatim
namespace Language


-- @@ L56-81 verbatim
/-- Relation symbols of tile-system instances. -/
inductive tilingRel : ℕ → Type
  /-- `posn p`: `p` is a position – a column, and equally a row. -/
  | posn : tilingRel 1
  /-- `tile t`: `t` is a tile. -/
  | tile : tilingRel 1
  /-- `tacc t`: `t` is an accepting tile. -/
  | tacc : tilingRel 1
  /-- `tle p q`: the linear order along which the grid is read. -/
  | tle : tilingRel 2
  /-- `horiz t t'`: `t'` may stand immediately to the right of `t`. -/
  | horiz : tilingRel 2
  /-- `vert t t'`: `t'` may stand immediately above `t`. -/
  | vert : tilingRel 2
  /-- `first p t`: the cell of the bottom row in column `p` may carry `t`. -/
  | first : tilingRel 2
  /-- `base t`: `t` is a base tile – what the bottom row carries in a column the
  description says nothing about. -/
  | base : tilingRel 1
  /-- `tstart t`: `t` is a start tile – what the corner of the grid carries. -/
  | tstart : tilingRel 1
  /-- `ledge t`: `t` may stand in the leftmost column. -/
  | ledge : tilingRel 1
  /-- `redge t`: `t` may stand in the rightmost column. -/
  | redge : tilingRel 1
  deriving DecidableEq


-- @@ L83-88 verbatim
/-- The relational vocabulary of tile-system instances: positions with their
order, tiles with their two compatibility relations, the bottom row and the
accepting tiles. -/
protected def tiling : Language :=
  ⟨fun _ => Empty, tilingRel⟩
  deriving IsRelational


-- @@ L90-91 verbatim
/-- The position symbol. -/
abbrev tlPosn : Language.tiling.Relations 1 := .posn


-- @@ L93-94 verbatim
/-- The tile symbol. -/
abbrev tlTile : Language.tiling.Relations 1 := .tile


-- @@ L96-97 verbatim
/-- The accepting-tile symbol. -/
abbrev tlAcc : Language.tiling.Relations 1 := .tacc


-- @@ L99-100 verbatim
/-- The order symbol. -/
abbrev tlLe : Language.tiling.Relations 2 := .tle


-- @@ L102-103 verbatim
/-- The horizontal-compatibility symbol. -/
abbrev tlHoriz : Language.tiling.Relations 2 := .horiz


-- @@ L105-106 verbatim
/-- The vertical-compatibility symbol. -/
abbrev tlVert : Language.tiling.Relations 2 := .vert


-- @@ L108-109 verbatim
/-- The bottom-row symbol. -/
abbrev tlFirst : Language.tiling.Relations 2 := .first


-- @@ L111-112 verbatim
/-- The base-tile symbol. -/
abbrev tlBase : Language.tiling.Relations 1 := .base


-- @@ L114-115 verbatim
/-- The start-tile symbol. -/
abbrev tlStart : Language.tiling.Relations 1 := .tstart


-- @@ L117-118 verbatim
/-- The left-edge symbol. -/
abbrev tlEdgeL : Language.tiling.Relations 1 := .ledge


-- @@ L120-121 verbatim
/-- The right-edge symbol. -/
abbrev tlEdgeR : Language.tiling.Relations 1 := .redge


-- @@ L123-123 verbatim
end Language


-- @@ L125-125 verbatim
end FirstOrder


-- @@ L127-127 verbatim
namespace DescriptiveComplexity


-- @@ L129-129 verbatim
open FirstOrder


-- @@ L131-131 verbatim
open Language Structure


-- @@ L133-133 verbatim
/-! ### The tile system an instance describes -/


-- @@ L135-163 verbatim
/-- **A tile system**, read off an instance: the positions with their order,
the tiles with their compatibilities, the bottom row and the accepting tiles.
As with `DescriptiveComplexity.TMData`, the record is a plain bundle of
predicates, so everything about tilings is stated once and read at whatever
structure supplies them. -/
structure TileData (A : Type) where
  /-- Being a position – a column, and equally a row. -/
  Posn : A → Prop
  /-- The order on positions. -/
  Le : A → A → Prop
  /-- Being a tile. -/
  Tile : A → Prop
  /-- Being an accepting tile. -/
  Acc : A → Prop
  /-- The right neighbor may carry this tile. -/
  Horiz : A → A → Prop
  /-- The upper neighbor may carry this tile. -/
  Vert : A → A → Prop
  /-- The bottom row's cell in this column may carry this tile. -/
  First : A → A → Prop
  /-- Being a base tile: what a column the description says nothing about
  carries in the bottom row. -/
  Base : A → Prop
  /-- Being a start tile: what the corner of the grid carries. -/
  Start : A → Prop
  /-- Being a left-edge tile: what the leftmost column may carry. -/
  EdgeL : A → Prop
  /-- Being a right-edge tile: what the rightmost column may carry. -/
  EdgeR : A → Prop


-- @@ L165-165 verbatim
namespace TileData


-- @@ L167-167 verbatim
variable {A : Type} (T : TileData A)


-- @@ L169-174 verbatim
/-- **The tiles the bottom row may carry in a column**: the ones the
description names there, and the base tiles in a column it names none. This is
`DescriptiveComplexity.TMData.InitTape`'s device – a description of the row
rather than a listing – and it is what lets an expansion carry it. -/
def FirstTile (x t : A) : Prop :=
  T.First x t ∨ ((∀ u, ¬T.First x u) ∧ T.Base t)


-- @@ L176-195 verbatim
/-- **A tiling of the square**: every cell carries a tile, the bottom row is one
the description allows, the two edge columns carry tiles allowed there,
horizontal and vertical neighbors are compatible, and some cell carries an
accepting tile.

The two **edge conditions** are what the classical border colors of a tiling
problem do. A condition on neighbors says nothing about a column with no
neighbor on one side, so without them a tile whose meaning is “something is
arriving from the left” could stand in the leftmost column, justified by nothing;
a machine drawn as a tiling would then grow a head out of nowhere. -/
def IsTiling (τ : A → A → A) : Prop :=
  (∀ x y, T.Posn x → T.Posn y → T.Tile (τ x y)) ∧
    (∀ x y, T.Posn x → MinPos T.Le T.Posn y →
      ((MinPos T.Le T.Posn x → T.Start (τ x y)) ∧
        (¬MinPos T.Le T.Posn x → T.FirstTile x (τ x y)))) ∧
    (∀ x y, T.Posn y → MinPos T.Le T.Posn x → T.EdgeL (τ x y)) ∧
    (∀ x y, T.Posn y → MaxPos T.Le T.Posn x → T.EdgeR (τ x y)) ∧
    (∀ x x' y, SuccPos T.Le T.Posn x x' → T.Posn y → T.Horiz (τ x y) (τ x' y)) ∧
    (∀ x y y', T.Posn x → SuccPos T.Le T.Posn y y' → T.Vert (τ x y) (τ x y')) ∧
    ∃ x y, T.Posn x ∧ T.Posn y ∧ T.Acc (τ x y)


-- @@ L197-200 verbatim
/-- **The square is tileable**: some assignment of tiles to cells is a tiling.
The assignment is a function on the whole universe – what it does off the grid
is not read, so nothing is lost by not restricting it. -/
def Tileable : Prop := ∃ τ : A → A → A, T.IsTiling τ


-- @@ L202-205 verbatim
/-- **Well-formedness**, folded into the yes-instances exactly as
`DescriptiveComplexity.TMData.WellFormed` is: the order is linear, and there is
a position to index the grid by. -/
def WellFormed : Prop := IsLinOrd T.Le ∧ ∃ p, T.Posn p


-- @@ L207-207 verbatim
/-! ### Transport along a bijection -/


-- @@ L209-209 verbatim
section Transport


-- @@ L211-211 verbatim
variable {B : Type} (u : A ≃ B) (S : TileData B)

-- @@ L212-212 verbatim
variable (hposn : ∀ a, T.Posn a ↔ S.Posn (u a)) (hle : ∀ a a', T.Le a a' ↔ S.Le (u a) (u a'))


-- @@ L214-214 verbatim
include hposn hle


-- @@ L216-222 verbatim
/-- The least position of the image is the image of the least position. -/
theorem minPos_map (a : A) :
    MinPos T.Le T.Posn a ↔ MinPos S.Le S.Posn (u a) := by
  refine and_congr (hposn a) ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    exact (hle a b).mp (h b ((hposn b).mpr hq))
  · exact (hle a q).mpr (h (u q) ((hposn q).mp hq))


-- @@ L224-230 verbatim
/-- The greatest position of the image is the image of the greatest one. -/
theorem maxPos_map (a : A) :
    MaxPos T.Le T.Posn a ↔ MaxPos S.Le S.Posn (u a) := by
  refine and_congr (hposn a) ⟨fun h q hq => ?_, fun h q hq => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    exact (hle b a).mp (h b ((hposn b).mpr hq))
  · exact (hle q a).mpr (h (u q) ((hposn q).mp hq))


-- @@ L232-244 verbatim
/-- And the successor of the image is the image of the successor. -/
theorem succPos_map (a a' : A) :
    SuccPos T.Le T.Posn a a' ↔ SuccPos S.Le S.Posn (u a) (u a') := by
  refine and_congr (hposn a) (and_congr (hposn a') (and_congr (hle a a')
    (and_congr ⟨fun h hc => h (u.injective hc), fun h hc => h (congrArg u hc)⟩ ?_)))
  refine ⟨fun h q hq h1 h2 => ?_, fun h q hq h1 h2 => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    rcases h b ((hposn b).mpr hq) ((hle a b).mpr h1) ((hle b a').mpr h2) with hc | hc
    · exact Or.inl (congrArg u hc)
    · exact Or.inr (congrArg u hc)
  · rcases h (u q) ((hposn q).mp hq) ((hle a q).mp h1) ((hle q a').mp h2) with hc | hc
    · exact Or.inl (u.injective hc)
    · exact Or.inr (u.injective hc)


-- @@ L246-246 verbatim
variable (htile : ∀ a, T.Tile a ↔ S.Tile (u a)) (hacc : ∀ a, T.Acc a ↔ S.Acc (u a))

-- @@ L247-247 verbatim
variable (hhoriz : ∀ a a', T.Horiz a a' ↔ S.Horiz (u a) (u a'))

-- @@ L248-248 verbatim
variable (hvert : ∀ a a', T.Vert a a' ↔ S.Vert (u a) (u a'))

-- @@ L249-249 verbatim
variable (hfirst : ∀ a a', T.First a a' ↔ S.First (u a) (u a'))

-- @@ L250-250 verbatim
variable (hbase : ∀ a, T.Base a ↔ S.Base (u a))

-- @@ L251-251 verbatim
variable (hstart : ∀ a, T.Start a ↔ S.Start (u a))

-- @@ L252-252 verbatim
variable (hedgeL : ∀ a, T.EdgeL a ↔ S.EdgeL (u a)) (hedgeR : ∀ a, T.EdgeR a ↔ S.EdgeR (u a))


-- @@ L254-254 verbatim
include htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR


-- @@ L256-301 verbatim
/-- **A bijection matching the two systems carries a tiling across.** -/
theorem isTiling_map {τ : A → A → A} (h : T.IsTiling τ) :
    S.IsTiling fun x y => u (τ (u.symm x) (u.symm y)) := by
  obtain ⟨htiles, hfst, hel, her, hhor, hver, x, y, hx, hy, hax⟩ := h
  refine ⟨fun p q hp hq => ?_, fun p q hp hq => ?_, fun p q hq hp => ?_,
    fun p q hq hp => ?_, fun p p' q hp hq => ?_,
    fun p q q' hp hq => ?_, u x, u y, (hposn x).mp hx, (hposn y).mp hy, ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    exact (htile _).mp (htiles a b ((hposn a).mpr hp) ((hposn b).mpr hq))
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    obtain ⟨hst, hfr⟩ := hfst a b ((hposn a).mpr hp) ((minPos_map T u S hposn hle b).mpr hq)
    refine ⟨fun hmin => (hstart _).mp (hst ((minPos_map T u S hposn hle a).mpr hmin)), ?_⟩
    intro hmin
    rcases hfr (fun hc => hmin ((minPos_map T u S hposn hle a).mp hc)) with h | ⟨hno, hb⟩
    · exact Or.inl ((hfirst _ _).mp h)
    · refine Or.inr ⟨fun v hv => ?_, (hbase _).mp hb⟩
      obtain ⟨c, rfl⟩ : ∃ c, v = u c := ⟨u.symm v, (u.apply_symm_apply v).symm⟩
      exact hno c ((hfirst a c).mpr hv)
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    exact (hedgeL _).mp
      (hel a b ((hposn b).mpr hq) ((minPos_map T u S hposn hle a).mpr hp))
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    exact (hedgeR _).mp
      (her a b ((hposn b).mpr hq) ((maxPos_map T u S hposn hle a).mpr hp))
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨a', rfl⟩ : ∃ a', p' = u a' := ⟨u.symm p', (u.apply_symm_apply p').symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    simp only [u.symm_apply_apply]
    exact (hhoriz _ _).mp
      (hhor a a' b ((succPos_map T u S hposn hle a a').mpr hp) ((hposn b).mpr hq))
  · obtain ⟨a, rfl⟩ : ∃ a, p = u a := ⟨u.symm p, (u.apply_symm_apply p).symm⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = u b := ⟨u.symm q, (u.apply_symm_apply q).symm⟩
    obtain ⟨b', rfl⟩ : ∃ b', q' = u b' := ⟨u.symm q', (u.apply_symm_apply q').symm⟩
    simp only [u.symm_apply_apply]
    exact (hvert _ _).mp
      (hver a b b' ((hposn a).mpr hp) ((succPos_map T u S hposn hle b b').mpr hq))
  · simp only [u.symm_apply_apply]
    exact (hacc _).mp hax


-- @@ L303-306 verbatim
/-- **And with it, tileability.** -/
theorem tileable_map (h : T.Tileable) : S.Tileable :=
  ⟨_, isTiling_map T u S hposn hle htile hacc hhoriz hvert hfirst hbase hstart
    hedgeL hedgeR h.choose_spec⟩


-- @@ L308-311 verbatim
omit htile hacc hhoriz hvert hfirst hbase hstart hedgeL hedgeR in
/-- **And well-formedness**: the order is linear and there is a position. -/
theorem wellFormed_map (h : T.WellFormed) : S.WellFormed :=
  ⟨IsLinOrd.of_equiv u hle h.1, ⟨u h.2.choose, (hposn _).mp h.2.choose_spec⟩⟩


-- @@ L313-313 verbatim
end Transport


-- @@ L315-315 verbatim
end TileData


-- @@ L317-317 verbatim
/-! ### The shorthands of the vocabulary -/


-- @@ L319-319 verbatim
section Shorthands


-- @@ L321-321 verbatim
variable {A : Type} [Language.tiling.Structure A]


-- @@ L323-324 verbatim
/-- Being a position. -/
def TLPosn (a : A) : Prop := RelMap tlPosn ![a]


-- @@ L326-327 verbatim
/-- Being a tile. -/
def TLTile (a : A) : Prop := RelMap tlTile ![a]


-- @@ L329-330 verbatim
/-- Being an accepting tile. -/
def TLAcc (a : A) : Prop := RelMap tlAcc ![a]


-- @@ L332-333 verbatim
/-- The order on positions. -/
def TLLe (a b : A) : Prop := RelMap tlLe ![a, b]


-- @@ L335-336 verbatim
/-- Horizontal compatibility. -/
def TLHoriz (a b : A) : Prop := RelMap tlHoriz ![a, b]


-- @@ L338-339 verbatim
/-- Vertical compatibility. -/
def TLVert (a b : A) : Prop := RelMap tlVert ![a, b]


-- @@ L341-342 verbatim
/-- The bottom row. -/
def TLFirst (a b : A) : Prop := RelMap tlFirst ![a, b]


-- @@ L344-345 verbatim
/-- Being a base tile. -/
def TLBase (a : A) : Prop := RelMap tlBase ![a]


-- @@ L347-348 verbatim
/-- Being a start tile. -/
def TLStart (a : A) : Prop := RelMap tlStart ![a]


-- @@ L350-351 verbatim
/-- Being a left-edge tile. -/
def TLEdgeL (a : A) : Prop := RelMap tlEdgeL ![a]


-- @@ L353-354 verbatim
/-- Being a right-edge tile. -/
def TLEdgeR (a : A) : Prop := RelMap tlEdgeR ![a]


-- @@ L356-368 verbatim
/-- The tile system an instance describes. -/
def tileData (A : Type) [Language.tiling.Structure A] : TileData A where
  Posn := TLPosn
  Le := TLLe
  Tile := TLTile
  Acc := TLAcc
  Horiz := TLHoriz
  Vert := TLVert
  First := TLFirst
  Base := TLBase
  Start := TLStart
  EdgeL := TLEdgeL
  EdgeR := TLEdgeR


-- @@ L370-370 verbatim
end Shorthands


-- @@ L372-372 verbatim
/-! ### The problem -/


-- @@ L374-374 verbatim
section Problem


-- @@ L376-376 verbatim
variable {A B : Type} [Language.tiling.Structure A] [Language.tiling.Structure B]


-- @@ L378-378 verbatim
section Transport


-- @@ L380-380 verbatim
variable (e : A ≃[Language.tiling] B)


-- @@ L382-382 verbatim
theorem tlPosn_map (a : A) : TLPosn a ↔ TLPosn (e a) := relMap_equiv₁ e tlPosn a


-- @@ L384-384 verbatim
theorem tlTile_map (a : A) : TLTile a ↔ TLTile (e a) := relMap_equiv₁ e tlTile a


-- @@ L386-386 verbatim
theorem tlAcc_map (a : A) : TLAcc a ↔ TLAcc (e a) := relMap_equiv₁ e tlAcc a


-- @@ L388-388 verbatim
theorem tlLe_map (a a' : A) : TLLe a a' ↔ TLLe (e a) (e a') := relMap_equiv₂ e tlLe a a'


-- @@ L390-391 verbatim
theorem tlHoriz_map (a a' : A) : TLHoriz a a' ↔ TLHoriz (e a) (e a') :=
  relMap_equiv₂ e tlHoriz a a'


-- @@ L393-394 verbatim
theorem tlVert_map (a a' : A) : TLVert a a' ↔ TLVert (e a) (e a') :=
  relMap_equiv₂ e tlVert a a'


-- @@ L396-397 verbatim
theorem tlFirst_map (a a' : A) : TLFirst a a' ↔ TLFirst (e a) (e a') :=
  relMap_equiv₂ e tlFirst a a'


-- @@ L399-399 verbatim
theorem tlBase_map (a : A) : TLBase a ↔ TLBase (e a) := relMap_equiv₁ e tlBase a


-- @@ L401-401 verbatim
theorem tlStart_map (a : A) : TLStart a ↔ TLStart (e a) := relMap_equiv₁ e tlStart a


-- @@ L403-403 verbatim
theorem tlEdgeL_map (a : A) : TLEdgeL a ↔ TLEdgeL (e a) := relMap_equiv₁ e tlEdgeL a


-- @@ L405-405 verbatim
theorem tlEdgeR_map (a : A) : TLEdgeR a ↔ TLEdgeR (e a) := relMap_equiv₁ e tlEdgeR a


-- @@ L407-414 verbatim
/-- **An isomorphism carries a tiling across**: the tiling of the image is the
tiling of the source read through the isomorphism, and every condition is a
condition on relations the isomorphism preserves. -/
theorem isTiling_map {τ : A → A → A} (h : (tileData A).IsTiling τ) :
    (tileData B).IsTiling fun u v => e (τ (e.symm u) (e.symm v)) :=
  TileData.isTiling_map _ e.toEquiv _ (tlPosn_map e) (tlLe_map e) (tlTile_map e)
    (tlAcc_map e) (tlHoriz_map e) (tlVert_map e) (tlFirst_map e) (tlBase_map e)
    (tlStart_map e) (tlEdgeL_map e) (tlEdgeR_map e) h


-- @@ L416-420 verbatim
/-- **And it carries well-formedness across**: the order and the positions are
relations of the vocabulary. -/
theorem wellFormed_map (e : A ≃[Language.tiling] B) (h : (tileData A).WellFormed) :
    (tileData B).WellFormed :=
  TileData.wellFormed_map _ e.toEquiv _ (tlPosn_map e) (tlLe_map e) h


-- @@ L422-422 verbatim
end Transport


-- @@ L424-427 verbatim
/-- **Tileability is an isomorphism invariant.** -/
theorem tileable_congr (e : A ≃[Language.tiling] B) :
    (tileData A).Tileable ↔ (tileData B).Tileable :=
  ⟨fun ⟨_, h⟩ => ⟨_, isTiling_map e h⟩, fun ⟨_, h⟩ => ⟨_, isTiling_map e.symm h⟩⟩


-- @@ L429-432 verbatim
/-- **And so is well-formedness.** -/
theorem wellFormed_congr (e : A ≃[Language.tiling] B) :
    (tileData A).WellFormed ↔ (tileData B).WellFormed :=
  ⟨wellFormed_map e, wellFormed_map e.symm⟩


-- @@ L434-442 verbatim
/-- **Tiling a square.** Can the square whose sides are the positions of the
instance be tiled, with the bottom row the description allows and an accepting
tile somewhere? The well-formedness promises of
`DescriptiveComplexity.TileData.WellFormed` are folded into the yes-instances,
exactly as for `DescriptiveComplexity.NTMAccept`. -/
def TILING : DecisionProblem Language.tiling where
  Holds := fun A _ => (tileData A).WellFormed ∧ (tileData A).Tileable
  iso_invariant := fun {_ _} _ _ e =>
    and_congr (wellFormed_congr e) (tileable_congr e)


-- @@ L444-444 verbatim
end Problem


-- @@ L446-446 verbatim
end DescriptiveComplexity
