/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import LeanPool.ClassificationOfSurfaces.RepresentativeCarrier
public import LeanPool.ClassificationOfSurfaces.CanonicalWords
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.MeasureTheory.Covering.Besicovitch


-- @@ L15-22 verbatim
/-!
# Carrier coordinates for canonical normal-form words

This file computes the closed-disk boundary coordinates of every canonical word position.
It reconciles the canonical positive boundary-block ordering with the trusted Eval relations'
negative angles using `Fin.rev` and integral periodicity. The resulting theorems send each of the
five canonical pairing families into the corresponding trusted equivalence closure.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace LeanEval.Topology.ClassificationOfSurfaces.NormalForm


-- @@ L28-28 verbatim
open Complex

-- @@ L29-29 verbatim
open SurfaceCellComplex


-- @@ L31-37 verbatim
/-- The point on occurrence `i` of the canonical orientable one-face presentation. -/
noncomputable def orientableOccurrencePoint (p n : ℕ)
    (i : Fin (orientableBoundaryWord p n).length) (t : unitInterval) :
    (orientableCellComplex p n).PolygonalPreRealization :=
  PolygonGluing.Side.point
    ((orientableCellComplex p n).occurrenceSide
      ⟨PUnit.unit, i⟩) t


-- @@ L39-48 verbatim
/-- The carrier bridge sends occurrence `i` to the boundary parameter `(i+t)/|word|`. -/
theorem orientableCarrier_occurrencePoint (p n : ℕ)
    (i : Fin (orientableBoundaryWord p n).length) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n i t) =
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) / (orientableBoundaryWord p n).length) := by
  simpa [orientableCellComplex, orientableOccurrencePoint] using
    oneFacePolygonalPreRealizationHomeomorph_sidePoint
      (orientableBoundaryWord p n) i t


-- @@ L50-60 verbatim
theorem orientableCarrier_handle_a_pos {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring


-- @@ L62-74 verbatim
theorem orientableCarrier_handle_a_neg {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 2)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring


-- @@ L76-86 verbatim
theorem orientableCarrier_handle_b_pos {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 1 + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring


-- @@ L88-100 verbatim
theorem orientableCarrier_handle_b_neg {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 3)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (i : ℝ) + 4 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableHandlePosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring


-- @@ L102-112 verbatim
theorem orientableCarrier_boundary_c_pos {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring


-- @@ L114-124 verbatim
theorem orientableCarrier_boundary_h_pos {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length]
  push_cast
  norm_num
  ring


-- @@ L126-138 verbatim
theorem orientableCarrier_boundary_c_neg {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) := by
  rw [orientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [orientableBoundaryPosition_val, orientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring


-- @@ L140-145 verbatim
/-- Reversing a finite index converts its real value to `n - j - 1`. -/
theorem fin_rev_cast_real {n : ℕ} (j : Fin n) :
    ((Fin.rev j : Fin n) : ℝ) = n - (j : ℝ) - 1 := by
  rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_iff.mpr j.isLt)]
  push_cast
  ring


-- @@ L147-183 verbatim
/-- Trusted boundary source `Fin.rev j` is the second canonical `cⱼ` side, modulo one turn. -/
theorem orientableBoundary_trustedSource_eq_carrier_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) := by
  have hNnat : 0 < 4 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((4 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 4 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (4 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
          (4 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t)) :=
      (orientableCarrier_boundary_c_neg j t).symm


-- @@ L185-221 verbatim
/-- Trusted boundary target `Fin.rev j` is the first canonical `cⱼ` side, modulo one turn. -/
theorem orientableBoundary_trustedTarget_eq_carrier_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) / (4 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) := by
  have hNnat : 0 < 4 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((4 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 4 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (4 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
            (4 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (4 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) /
          (4 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t) :=
      (orientableCarrier_boundary_c_pos j t).symm


-- @@ L223-233 verbatim
/-- Every canonical `aᵢ` side pairing maps into the trusted orientable equivalence closure. -/
theorem orientableCarrier_handle_a_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 2)
          (unitInterval.symm t))) := by
  rw [orientableCarrier_handle_a_pos, orientableCarrier_handle_a_neg]
  exact Relation.EqvGen.rel _ _ (OrientableRel.a (n := n) t i)


-- @@ L235-245 verbatim
/-- Every canonical `bᵢ` side pairing maps into the trusted orientable equivalence closure. -/
theorem orientableCarrier_handle_b_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 1) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableHandlePosition p n i 3)
          (unitInterval.symm t))) := by
  rw [orientableCarrier_handle_b_pos, orientableCarrier_handle_b_neg]
  exact Relation.EqvGen.rel _ _ (OrientableRel.b (n := n) t i)


-- @@ L247-260 verbatim
/-- Every canonical `cⱼ` side pairing maps into the trusted orientable equivalence closure. -/
theorem orientableCarrier_boundary_c_eqvGen
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    Relation.EqvGen (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n (orientableBoundaryPosition p n j 2)
          (unitInterval.symm t))) := by
  rw [← orientableBoundary_trustedTarget_eq_carrier_c_pos,
    ← orientableBoundary_trustedSource_eq_carrier_c_neg]
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _
      (OrientableRel.c (p := p) t (Fin.rev j)))


-- @@ L262-268 verbatim
/-- The point on occurrence `i` of the canonical nonorientable one-face presentation. -/
noncomputable def nonOrientableOccurrencePoint (p n : ℕ)
    (i : Fin (nonOrientableBoundaryWord p n).length) (t : unitInterval) :
    (nonOrientableCellComplex p n).PolygonalPreRealization :=
  PolygonGluing.Side.point
    ((nonOrientableCellComplex p n).occurrenceSide
      ⟨PUnit.unit, i⟩) t


-- @@ L270-279 verbatim
/-- The nonorientable carrier bridge sends occurrence `i` to `(i+t)/|word|`. -/
theorem nonOrientableCarrier_occurrencePoint (p n : ℕ)
    (i : Fin (nonOrientableBoundaryWord p n).length) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n i t) =
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) / (nonOrientableBoundaryWord p n).length) := by
  simpa [nonOrientableCellComplex, nonOrientableOccurrencePoint] using
    oneFacePolygonalPreRealizationHomeomorph_sidePoint
      (nonOrientableBoundaryWord p n) i t


-- @@ L281-293 verbatim
theorem nonOrientableCarrier_crosscap_a_first
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (i : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableCrosscapPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring


-- @@ L295-307 verbatim
theorem nonOrientableCarrier_crosscap_a_second
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (i : ℝ) + 1 + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableCrosscapPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring


-- @@ L309-321 verbatim
theorem nonOrientableCarrier_boundary_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring


-- @@ L323-335 verbatim
theorem nonOrientableCarrier_boundary_h_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) / (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length]
  push_cast
  norm_num
  ring


-- @@ L337-351 verbatim
theorem nonOrientableCarrier_boundary_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) := by
  rw [nonOrientableCarrier_occurrencePoint]
  apply congrArg ClosedUnitDisc.bdyPtOfReal
  simp only [nonOrientableBoundaryPosition_val, nonOrientableBoundaryWord_length,
    unitInterval.coe_symm_eq]
  push_cast
  norm_num
  ring


-- @@ L353-390 verbatim
/-- Trusted boundary source `Fin.rev j` is the second nonorientable `cⱼ` side. -/
theorem nonOrientableBoundary_trustedSource_eq_carrier_c_neg
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) := by
  have hNnat : 0 < 2 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((2 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 2 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) / (2 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
            (2 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) / (2 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + (t : ℝ)) /
          (2 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t)) :=
      (nonOrientableCarrier_boundary_c_neg j t).symm


-- @@ L392-431 verbatim
/-- Trusted boundary target `Fin.rev j` is the first nonorientable `cⱼ` side. -/
theorem nonOrientableBoundary_trustedTarget_eq_carrier_c_pos
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) =
      oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) := by
  have hNnat : 0 < 2 * p + 3 * n := by
    have hj := j.isLt
    omega
  have hN : ((2 * p + 3 * n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hNnat.ne'
  have hN' : 2 * (p : ℝ) + 3 * (n : ℝ) ≠ 0 := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN
    exact hN
  have harg :
      (2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) / (2 * p + 3 * n) =
        -(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
            (2 * p + 3 * n) + 1 := by
    rw [fin_rev_cast_real]
    field_simp [hN']
    ring
  calc
    ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n)) =
      ClosedUnitDisc.bdyPtOfReal
        (-(3 * ((Fin.rev j : Fin n) : ℝ) + 3 - (t : ℝ)) /
          (2 * p + 3 * n) + (1 : ℤ)) :=
      (ClosedUnitDisc.bdyPtOfReal_add_int _ 1).symm
    _ = ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + (t : ℝ)) /
          (2 * p + 3 * n)) := by
      simpa using congrArg ClosedUnitDisc.bdyPtOfReal harg.symm
    _ = oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t) :=
      (nonOrientableCarrier_boundary_c_pos j t).symm


-- @@ L433-445 verbatim
/-- Every canonical crosscap pairing maps into the trusted nonorientable closure. -/
theorem nonOrientableCarrier_crosscap_a_eqvGen
    {p n : ℕ} (i : Fin p) (t : unitInterval) :
    Relation.EqvGen (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableCrosscapPosition p n i 1) t)) := by
  rw [nonOrientableCarrier_crosscap_a_first,
    nonOrientableCarrier_crosscap_a_second]
  exact Relation.EqvGen.rel _ _ (NonOrientableRel.a (n := n) t i)


-- @@ L447-461 verbatim
/-- Every canonical boundary-seam pairing maps into the trusted nonorientable closure. -/
theorem nonOrientableCarrier_boundary_c_eqvGen
    {p n : ℕ} (j : Fin n) (t : unitInterval) :
    Relation.EqvGen (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 0) t))
      (oneFacePolygonalPreRealizationHomeomorph (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 2) (unitInterval.symm t))) := by
  rw [← nonOrientableBoundary_trustedTarget_eq_carrier_c_pos,
    ← nonOrientableBoundary_trustedSource_eq_carrier_c_neg]
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _
      (NonOrientableRel.c (p := p) t (Fin.rev j)))


-- @@ L463-463 verbatim
end LeanEval.Topology.ClassificationOfSurfaces.NormalForm
