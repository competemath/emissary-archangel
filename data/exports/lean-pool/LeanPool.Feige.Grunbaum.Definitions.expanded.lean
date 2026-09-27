/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis


-- @@ L12-19 verbatim
/-!
# Definitions for Grünbaum's centroid halfspace theorem

Mathlib's `ConvexBody` permits lower-dimensional compact convex sets.  In
finite-dimensional convex geometry, a convex body is normally required to
have nonempty interior.  `FullDimensionalConvexBody` records precisely that
standard convention.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open MeasureTheory Set


-- @@ L25-25 verbatim
namespace Grunbaum


-- @@ L27-28 verbatim
/-- Euclidean space of positive dimension `d + 1`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))


-- @@ L30-39 verbatim
/-- A compact convex set with nonempty interior. -/
structure FullDimensionalConvexBody (d : ℕ) where
  /-- The underlying point set. -/
  carrier : Set (Euc d)
  /-- Convexity of the body. -/
  convex' : Convex ℝ carrier
  /-- Compactness of the body. -/
  isCompact' : IsCompact carrier
  /-- The body is full-dimensional. -/
  interior_nonempty' : (interior carrier).Nonempty


-- @@ L41-41 verbatim
namespace FullDimensionalConvexBody


-- @@ L43-48 verbatim
instance {d : ℕ} : SetLike (FullDimensionalConvexBody d) (Euc d) where
  coe := FullDimensionalConvexBody.carrier
  coe_injective C D h := by
    cases C
    cases D
    congr


-- @@ L50-52 verbatim
protected theorem convex {d : ℕ} (C : FullDimensionalConvexBody d) :
    Convex ℝ (C : Set (Euc d)) :=
  C.convex'


-- @@ L54-56 verbatim
protected theorem isCompact {d : ℕ} (C : FullDimensionalConvexBody d) :
    IsCompact (C : Set (Euc d)) :=
  C.isCompact'


-- @@ L58-60 verbatim
protected theorem isClosed {d : ℕ} (C : FullDimensionalConvexBody d) :
    IsClosed (C : Set (Euc d)) :=
  C.isCompact.isClosed


-- @@ L62-64 verbatim
protected theorem interior_nonempty {d : ℕ} (C : FullDimensionalConvexBody d) :
    (interior (C : Set (Euc d))).Nonempty :=
  C.interior_nonempty'


-- @@ L66-68 verbatim
protected theorem nonempty {d : ℕ} (C : FullDimensionalConvexBody d) :
    (C : Set (Euc d)).Nonempty :=
  C.interior_nonempty.mono interior_subset


-- @@ L70-72 verbatim
theorem volume_pos {d : ℕ} (C : FullDimensionalConvexBody d) :
    0 < volume (C : Set (Euc d)) :=
  Measure.measure_pos_of_nonempty_interior volume C.interior_nonempty


-- @@ L74-76 verbatim
theorem volume_ne_zero {d : ℕ} (C : FullDimensionalConvexBody d) :
    volume (C : Set (Euc d)) ≠ 0 :=
  C.volume_pos.ne'


-- @@ L78-80 verbatim
theorem volume_ne_top {d : ℕ} (C : FullDimensionalConvexBody d) :
    volume (C : Set (Euc d)) ≠ ⊤ :=
  C.isCompact.measure_lt_top.ne


-- @@ L82-84 verbatim
/-- The volume centroid of a full-dimensional convex body. -/
noncomputable def centroid {d : ℕ} (C : FullDimensionalConvexBody d) : Euc d :=
  ⨍ x in (C : Set (Euc d)), x ∂volume


-- @@ L86-86 verbatim
end FullDimensionalConvexBody


-- @@ L88-90 verbatim
/-- The closed halfspace cut out by `ℓ x ≤ a`. -/
def closedHalfspace {d : ℕ} (ℓ : Euc d →L[ℝ] ℝ) (a : ℝ) : Set (Euc d) :=
  ℓ ⁻¹' Iic a


-- @@ L92-100 verbatim
/-- A (proper) closed halfspace, represented by a nonzero continuous linear
functional and a threshold. -/
structure ClosedHalfspace (d : ℕ) where
  /-- The defining normal functional. -/
  normal : Euc d →L[ℝ] ℝ
  /-- The defining threshold. -/
  threshold : ℝ
  /-- A halfspace has a nonzero normal. -/
  normal_ne_zero : normal ≠ 0


-- @@ L102-102 verbatim
namespace ClosedHalfspace


-- @@ L104-105 verbatim
instance {d : ℕ} : Coe (ClosedHalfspace d) (Set (Euc d)) where
  coe H := closedHalfspace H.normal H.threshold


-- @@ L107-108 verbatim
instance {d : ℕ} : Membership (Euc d) (ClosedHalfspace d) where
  mem H x := x ∈ (H : Set (Euc d))


-- @@ L110-113 verbatim
@[simp]
theorem mem_iff {d : ℕ} {x : Euc d} {H : ClosedHalfspace d} :
    x ∈ H ↔ H.normal x ≤ H.threshold :=
  Iff.rfl


-- @@ L115-117 verbatim
theorem isClosed {d : ℕ} (H : ClosedHalfspace d) :
    IsClosed (closedHalfspace H.normal H.threshold) :=
  isClosed_Iic.preimage H.normal.continuous


-- @@ L119-119 verbatim
end ClosedHalfspace


-- @@ L121-125 verbatim
/-- The normalized volume of a body's intersection with a closed halfspace. -/
noncomputable def halfspaceVolumeRatio {d : ℕ} (C : FullDimensionalConvexBody d)
    (ℓ : Euc d →L[ℝ] ℝ) (a : ℝ) : ℝ :=
  (volume ((C : Set (Euc d)) ∩ closedHalfspace ℓ a) /
    volume (C : Set (Euc d))).toReal


-- @@ L127-129 verbatim
/-- The sharp constant `(n / (n + 1)) ^ n` in dimension `n = d + 1`. -/
noncomputable def grunbaumConstant (d : ℕ) : ℝ :=
  (((d + 1 : ℕ) : ℝ) / (d + 2 : ℕ)) ^ (d + 1)


-- @@ L131-131 verbatim
end Grunbaum
