/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Core.DyadicCell
import LeanCert.Engine.Optimization.Box


-- @@ L9-15 verbatim
/-!
# Addressed multidimensional box subdivision

Adaptive paths record both the selected coordinate and the left/right branch.
Morton addresses are deliberately separate: they describe balanced fixed-level
refinement with the regular coordinate schedule `0, 1, ..., dimension - 1`.
-/


-- @@ L17-17 verbatim
namespace LeanCert.Engine.Optimization


-- @@ L19-19 verbatim
open LeanCert.Core


-- @@ L21-22 verbatim
/-- One adaptive box decision: a bounded coordinate and a branch side. -/
abbrev BoxDecision (dimension : Nat) := Fin dimension × Bool


-- @@ L24-25 verbatim
/-- Root-relative provenance for adaptive multidimensional subdivision. -/
abbrev BoxPath (dimension : Nat) := List (BoxDecision dimension)


-- @@ L27-27 verbatim
namespace BoxPath


-- @@ L29-32 verbatim
/-- Address the child selected by the optimizer's widest-axis policy.
Empty boxes have no bounded coordinate and therefore return `none`. -/
def widestDecision? (B : Box) (upper : Bool) : Option (BoxDecision B.length) :=
  if h : B.widestDim < B.length then some (⟨B.widestDim, h⟩, upper) else none


-- @@ L34-36 verbatim
/-- Follow one addressed child. `false` selects the lower child. -/
def descend {dimension : Nat} (B : Box) (decision : BoxDecision dimension) : Box :=
  if decision.2 then (B.split decision.1.val).2 else (B.split decision.1.val).1


-- @@ L38-46 verbatim
theorem descend_widestDecision?_eq {B : Box} {upper : Bool} {decision : BoxDecision B.length}
    (hdecision : widestDecision? B upper = some decision) :
    descend B decision = if upper then B.splitWidest.2 else B.splitWidest.1 := by
  unfold widestDecision? at hdecision
  split at hdecision
  · simp only [Option.some.injEq] at hdecision
    subst decision
    simp [descend, Box.splitWidest]
  · simp at hdecision


-- @@ L48-51 verbatim
/-- Replay an adaptive path from a root box. -/
def decode {dimension : Nat} (root : Box) : BoxPath dimension → Box
  | [] => root
  | decision :: rest => decode (descend root decision) rest


-- @@ L53-55 verbatim
/-- Dimension-checked replay for data arriving across an API or serialization boundary. -/
def decode? {dimension : Nat} (root : Box) (path : BoxPath dimension) : Option Box :=
  if root.length = dimension then some (decode root path) else none


-- @@ L57-58 verbatim
@[simp] theorem decode_nil {dimension : Nat} (root : Box) :
    decode (dimension := dimension) root [] = root := rfl


-- @@ L60-62 verbatim
@[simp] theorem decode_cons {dimension : Nat} (root : Box)
    (decision : BoxDecision dimension) (rest : BoxPath dimension) :
    decode root (decision :: rest) = decode (descend root decision) rest := rfl


-- @@ L64-67 verbatim
theorem descend_length {dimension : Nat} (B : Box) (decision : BoxDecision dimension) :
    (descend B decision).length = B.length := by
  unfold descend
  split <;> simp only [Box.split_length_eq]


-- @@ L69-75 verbatim
/-- Address replay preserves the dimension of the root box. -/
theorem decode_length {dimension : Nat} (root : Box) (path : BoxPath dimension) :
    (decode root path).length = root.length := by
  induction path generalizing root with
  | nil => rfl
  | cons decision rest ih =>
      rw [decode_cons, ih, descend_length]


-- @@ L77-88 verbatim
/-- Every addressed leaf remains a semantic sub-box of its root. -/
theorem envMem_decode_subset {dimension : Nat} (root : Box) (path : BoxPath dimension)
    (ρ : Nat → ℝ) : Box.envMem ρ (decode root path) → Box.envMem ρ root := by
  induction path generalizing root with
  | nil => exact id
  | cons decision rest ih =>
      intro hmem
      have hchild : Box.envMem ρ (descend root decision) := ih _ hmem
      unfold descend at hchild
      split at hchild
      · exact Box.envMem_of_envMem_split_right root decision.1.val ρ hchild
      · exact Box.envMem_of_envMem_split root decision.1.val ρ hchild


-- @@ L90-90 verbatim
end BoxPath


-- @@ L92-100 verbatim
/-- A balanced fixed-level Morton address. Its bits are interleaved by level:
axis `0`, ..., axis `dimension - 1`, then the same schedule at the next level. -/
structure MortonAddress where
  dimension : Nat
  dimension_pos : 0 < dimension
  depth : Nat
  bits : List Bool
  bits_length : bits.length = dimension * depth
  deriving Repr


-- @@ L102-102 verbatim
namespace MortonAddress


-- @@ L104-106 verbatim
def ofBits (dimension depth : Nat) (bits : List Bool) (dimension_pos : 0 < dimension)
    (bits_length : bits.length = dimension * depth) : MortonAddress :=
  ⟨dimension, dimension_pos, depth, bits, bits_length⟩


-- @@ L108-112 verbatim
/-- Numeric Morton/Z-order identifier obtained from the interleaved bit string. -/
def code (address : MortonAddress) : Fin (2 ^ (address.dimension * address.depth)) :=
  ⟨DyadicPath.index address.bits, by
    rw [← address.bits_length]
    exact DyadicPath.index_lt_pow_length address.bits⟩


-- @@ L114-117 verbatim
/-- Expand a Morton address into the primary adaptive path representation. -/
def toBoxPath (address : MortonAddress) : BoxPath address.dimension :=
  address.bits.zipIdx.map fun (bit, index) =>
    (⟨index % address.dimension, Nat.mod_lt _ address.dimension_pos⟩, bit)


-- @@ L119-121 verbatim
@[simp] theorem toBoxPath_length (address : MortonAddress) :
    address.toBoxPath.length = address.dimension * address.depth := by
  simp [toBoxPath, address.bits_length]


-- @@ L123-127 verbatim
/-- Does an adaptive path follow the regular Morton coordinate schedule? -/
def followsSchedule (dimension : Nat) (_dimension_pos : 0 < dimension)
    (path : BoxPath dimension) : Bool :=
  path.zipIdx.all fun (decision, index) =>
    decision.1.val == index % dimension


-- @@ L129-137 verbatim
/-- Convert a balanced regularly scheduled adaptive path to a Morton address.
Irregular adaptive paths are rejected instead of being assigned a misleading ID. -/
def ofBoxPath? (dimension depth : Nat) (dimension_pos : 0 < dimension)
    (path : BoxPath dimension) : Option MortonAddress :=
  if hlength : path.length = dimension * depth then
    if followsSchedule dimension dimension_pos path then
      some ⟨dimension, dimension_pos, depth, path.map (·.2), by simpa using hlength⟩
    else none
  else none


-- @@ L139-141 verbatim
/-- Replay the balanced address through ordinary box splits. -/
def decode (address : MortonAddress) (root : Box) : Box :=
  address.toBoxPath.decode root


-- @@ L143-145 verbatim
/-- Reject a root whose dimension does not match the Morton address. -/
def decode? (address : MortonAddress) (root : Box) : Option Box :=
  address.toBoxPath.decode? root


-- @@ L147-147 verbatim
end MortonAddress


-- @@ L149-149 verbatim
end LeanCert.Engine.Optimization
