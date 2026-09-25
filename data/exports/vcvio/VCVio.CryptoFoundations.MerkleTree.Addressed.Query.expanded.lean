/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.MerkleTree.Addressed.Basic


-- @@ L11-22 verbatim
/-!
# Addressed Merkle node queries

This module gives addressed Merkle hashing a canonical query identity. A query records an address
in the caller's actual oracle-key type and the ordered pair of child labels. The explicit
`addressKey : SkeletonInternalIndex s → Address` map connects typed Merkle positions to those
keys. It may be non-injective: if two positions encode to the same concrete key, the definitions
correctly treat them as the same oracle address rather than silently distinguishing them.

`openingQueries` enumerates the exact node-hash queries induced by a complete opening. These
definitions are shared by queried-domain uniqueness and addressed random-oracle extraction.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace AddressedMerkleTree


-- @@ L28-28 verbatim
open BinaryTree InductiveMerkleTree


-- @@ L30-30 verbatim
universe u v


-- @@ L32-32 verbatim
variable {Address : Type u} {Y : Type v}


-- @@ L34-40 verbatim
/-- One addressed Merkle-node query: an actual oracle address and ordered child pair. -/
structure NodeQuery (Address : Type u) (Y : Type v) where
  /-- Address/key supplied to the underlying hash oracle. -/
  address : Address
  /-- Ordered left and right child labels. -/
  input : Y × Y
deriving DecidableEq


-- @@ L42-42 verbatim
namespace NodeQuery


-- @@ L44-46 verbatim
/-- Evaluate an addressed node query. -/
def eval (nodeHash : Address → Y → Y → Y) (query : NodeQuery Address Y) : Y :=
  nodeHash query.address query.input.1 query.input.2


-- @@ L48-48 verbatim
end NodeQuery


-- @@ L50-66 verbatim
/-- The addressed node-hash inputs induced by a complete opening, ordered from the root toward
the leaf. -/
def openingQueries : {s : Skeleton} →
    (addressKey : SkeletonInternalIndex s → Address) →
    (nodeHash : Address → Y → Y → Y) →
    (idx : SkeletonLeafIndex s) → Y → List.Vector Y idx.depth → List (NodeQuery Address Y)
  | _, _, _, .ofLeaf, _, _ => []
  | _, addressKey, nodeHash, .ofLeft idx, leaf, proof =>
      let child := getPutativeRootAddressedWithHash
        (fun a => nodeHash (addressKey (.ofLeft a))) idx leaf proof.tail
      ⟨addressKey .ofInternal, (child, proof.head)⟩ ::
        openingQueries (fun a => addressKey (.ofLeft a)) nodeHash idx leaf proof.tail
  | _, addressKey, nodeHash, .ofRight idx, leaf, proof =>
      let child := getPutativeRootAddressedWithHash
        (fun a => nodeHash (addressKey (.ofRight a))) idx leaf proof.tail
      ⟨addressKey .ofInternal, (proof.head, child)⟩ ::
        openingQueries (fun a => addressKey (.ofRight a)) nodeHash idx leaf proof.tail


-- @@ L68-74 verbatim
/-- Every node query induced by an opening occurs in `log`. -/
def OpeningCovered {s : Skeleton}
    (addressKey : SkeletonInternalIndex s → Address)
    (nodeHash : Address → Y → Y → Y)
    (log : List (NodeQuery Address Y)) (idx : SkeletonLeafIndex s)
    (leaf : Y) (proof : List.Vector Y idx.depth) : Prop :=
  ∀ query ∈ openingQueries addressKey nodeHash idx leaf proof, query ∈ log


-- @@ L76-76 verbatim
end AddressedMerkleTree
