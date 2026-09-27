/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.BooleanIsoperimetry.ConwayGuyCoherentGap
import LeanPool.BooleanIsoperimetry.ConwayGuyHeight
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L16-22 verbatim
/-!
# Conway--Guy normalized chamber rigidity

This file packages the concrete Conway--Guy principal relations and triangular
corrections as a `FirstCoordinateRecurrence`.  The separate height identity
supplies the one remaining arithmetic input.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace BooleanIsoperimetry.CoherentGap


-- @@ L28-35 verbatim
/-- The triangular-block identity needed to evaluate a Conway--Guy principal
relation. -/
def ConwayGuyBlockIdentity (offset : ℕ) : Prop :=
  conwayGuyHeight (offset + 2) -
      ∑ index : Fin (guide (offset + 2)),
        conwayGuyHeight (offset + 2 - index.val - 1) +
    ∑ index : Fin (guide (offset + 2) - 1),
      conwayGuyHeight (triangular index.val) = 1


-- @@ L37-53 verbatim
/-- The dimension-one Conway--Guy basis certificate. -/
noncomputable def conwayGuyBaseCertificate :
    Certificate (conwayGuyArithmetic.tower.weights 1) (basis 0) :=
  Certificate.singleton (by
    refine ⟨?_, ?_, ?_⟩
    · intro coordinate
      right
      right
      have hcoordinate : coordinate = 0 := Fin.eq_zero coordinate
      subst coordinate
      simp [basis]
    · rw [dot_basis]
      simp [ConwayGuyArithmetic.tower, ConwayGuyArithmetic.weights,
        conwayGuyArithmetic]
    · right
      right
      exact coordinateSum_basis 0)


-- @@ L55-63 verbatim
lemma principal_valid (hblock : ∀ offset, ConwayGuyBlockIdentity offset)
    (offset : ℕ) :
    IsLiftableUnit (conwayGuyArithmetic.tower.weights (offset + 2))
      (principal offset) := by
  refine ⟨principal_entry offset, ?_, ?_⟩
  · exact principal_dot offset (hblock offset)
  · right
    right
    exact principal_coordinateSum offset


-- @@ L65-74 verbatim
/-- The concrete first-coordinate recurrence, conditional only on the explicit
Conway--Guy block identity. -/
noncomputable def conwayGuyFirstCoordinateRecurrence
    (hblock : ∀ offset, ConwayGuyBlockIdentity offset) :
    FirstCoordinateRecurrence conwayGuyArithmetic.tower where
  base := conwayGuyBaseCertificate
  principal := principal
  principal_valid := principal_valid hblock
  corrections := corrections
  decomposition := principal_corrections_decomposition


-- @@ L76-88 verbatim
/-- Conditional concrete normalized chamber rigidity.  The height file
discharges `hblock` from the published Conway--Guy recurrence. -/
theorem conwayGuyNormalizedChamberRigidity_of_blockIdentity
    (hblock : ∀ offset, ConwayGuyBlockIdentity offset) {n : ℕ}
    (candidate : Fin n → ℝ)
    (hgap : ∀ relation,
      IsLiftableUnit (conwayGuyArithmetic.tower.weights n) relation →
        1 ≤ realDot relation candidate) :
    ∀ coordinate,
      (conwayGuyArithmetic.tower.weights n coordinate : ℝ) ≤
        candidate coordinate :=
  normalizedChamberRigidity conwayGuyArithmetic.tower
    (conwayGuyFirstCoordinateRecurrence hblock) candidate hgap


-- @@ L90-92 verbatim
lemma conwayGuyBlockIdentity_all (offset : ℕ) :
    ConwayGuyBlockIdentity offset := by
  exact conwayGuy_block_identity (offset + 2) (by omega)


-- @@ L94-98 verbatim
/-- The unconditional first-coordinate certificate recurrence for the
Conway--Guy row. -/
noncomputable def conwayGuyRecurrence :
    FirstCoordinateRecurrence conwayGuyArithmetic.tower :=
  conwayGuyFirstCoordinateRecurrence conwayGuyBlockIdentity_all


-- @@ L100-108 verbatim
/-- Every coordinate of every Conway--Guy row has a nonnegative integral
certificate supported on liftable unit relations. -/
theorem conwayGuyCertificate_exists (dimension : ℕ)
    (coordinate : Fin dimension) :
    Nonempty
      (Certificate (conwayGuyArithmetic.tower.weights dimension)
        (basis coordinate)) :=
  recurrenceCertificate_exists conwayGuyArithmetic.tower
    conwayGuyRecurrence dimension coordinate


-- @@ L110-125 verbatim
/-- **Conway--Guy normalized chamber rigidity.** Every real row satisfying all
unit-relation inequalities of the Conway--Guy row dominates it coordinatewise.

Bohman's distinct-subset-sum theorem is a separate external input identifying
these unit relations with consecutive gaps of the induced Boolean term order.
-/
theorem conwayGuyNormalizedChamberRigidity {n : ℕ}
    (candidate : Fin n → ℝ)
    (hgap : ∀ relation,
      IsLiftableUnit (conwayGuyArithmetic.tower.weights n) relation →
        1 ≤ realDot relation candidate) :
    ∀ coordinate,
      (conwayGuyArithmetic.tower.weights n coordinate : ℝ) ≤
        candidate coordinate :=
  normalizedChamberRigidity conwayGuyArithmetic.tower
    conwayGuyRecurrence candidate hgap


-- @@ L127-127 verbatim
end BooleanIsoperimetry.CoherentGap
