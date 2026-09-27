/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.PackedCertificates


-- @@ L10-10 verbatim
/-! # Erdős 97 convex-octagon formalization: Coverage Data Types -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace Erdos97Octagon.RawIncidence


-- @@ L16-23 verbatim
/-- A monotone obstruction pattern paired with its checked witness. -/
structure PatternEntry where
  /-- Identifier of the source classifier record. -/
  origin : ℕ
  /-- Packed incidences required by this monotone obstruction. -/
  mask : UInt64
  /-- The obstruction witness attached to the mask. -/
  certificate : PrefixCertificate


-- @@ L25-32 verbatim
/-- An exact complete table paired with its checked witness. -/
structure HardEntry where
  /-- Identifier of the source classifier record. -/
  origin : ℕ
  /-- Packed code for the complete incidence table. -/
  code : UInt64
  /-- The obstruction witness attached to the exact table. -/
  certificate : Certificate


-- @@ L34-36 verbatim
/-- Validate a pattern witness against precisely its required incidences. -/
def PatternEntry.validB (entry : PatternEntry) : Bool :=
  entry.certificate.toCertificate.validPackedB entry.mask


-- @@ L38-40 verbatim
/-- Validate an exact-table witness against its decoded incidence table. -/
def HardEntry.validB (entry : HardEntry) : Bool :=
  entry.certificate.validPackedB entry.code


-- @@ L42-46 verbatim
/-- A successful pattern audit supplies its mathematical witness. -/
theorem PatternEntry.valid_of_validB
    {entry : PatternEntry} (hvalid : entry.validB = true) :
    entry.certificate.toCertificate.Valid (packedIncidence entry.mask) :=
  Certificate.valid_of_validPackedB hvalid


-- @@ L48-52 verbatim
/-- A successful exact-table audit supplies its mathematical witness. -/
theorem HardEntry.valid_of_validB
    {entry : HardEntry} (hvalid : entry.validB = true) :
    entry.certificate.Valid (packedIncidence entry.code) :=
  Certificate.valid_of_validPackedB hvalid


-- @@ L54-54 verbatim
end Erdos97Octagon.RawIncidence
