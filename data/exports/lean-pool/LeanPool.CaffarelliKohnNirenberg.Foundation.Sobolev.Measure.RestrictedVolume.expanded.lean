/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


-- @@ L12-18 verbatim
/-!
# Restricted Lebesgue volume

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps the common restricted-volume abbreviations and
drops domain regularity predicates that are not needed by weak derivatives.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace CKN


-- @@ L24-26 verbatim
/-- Lebesgue volume restricted to a native-vector domain. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U


-- @@ L28-30 verbatim
/-- Compatibility name for the restricted volume measure. -/
noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) :=
  volumeOn U


-- @@ L32-32 verbatim
end CKN
