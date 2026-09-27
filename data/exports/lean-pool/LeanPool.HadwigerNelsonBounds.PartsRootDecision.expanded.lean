/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData0
public import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData1
public import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData2
public import LeanPool.HadwigerNelsonBounds.PartsRootDecisionData3


-- @@ L13-18 verbatim
/-!
# Complete normalized root dispatch

The 1,023-node trie has 432 leaves, one for each proper normalized coloring of
the 13-vertex 2-Golomb root. Every leaf names a separately checked Parts tree.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace HadwigerNelsonBounds


-- @@ L24-42 verbatim
/-- All chunks of the complete normalized root-decision trie. -/
def partsRootDecisionNodes : Array (Array PartsRootNode) := #[
  partsRootDecisionChunk0,
  partsRootDecisionChunk1,
  partsRootDecisionChunk2,
  partsRootDecisionChunk3,
  partsRootDecisionChunk4,
  partsRootDecisionChunk5,
  partsRootDecisionChunk6,
  partsRootDecisionChunk7,
  partsRootDecisionChunk8,
  partsRootDecisionChunk9,
  partsRootDecisionChunk10,
  partsRootDecisionChunk11,
  partsRootDecisionChunk12,
  partsRootDecisionChunk13,
  partsRootDecisionChunk14,
  partsRootDecisionChunk15,
]


-- @@ L44-47 verbatim
theorem partsRootDecision_verifies :
    PartsRootVerifiesNodeB partsRootDecisionNodes 1024
      partsNormalizedRootPath 0 = true := by
  decide +kernel


-- @@ L49-54 verbatim
/-- No proper coloring of the Parts graph extends the normalized fixed root. -/
theorem no_parts_coloring_of_normalized_root {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring)
    (hroots : PartsExtends coloring partsNormalizedRootPath) : False := by
  exact partsRootDecision_not_colorable partsRootDecisionNodes 1023
    partsRootDecision_verifies hproper hroots


-- @@ L56-56 verbatim
end HadwigerNelsonBounds
