module
public import SpherePacking.Dim24.LeechLattice.Norm
public import SpherePacking.Dim24.LeechLattice.Basis
import Mathlib.Analysis.InnerProductSpace.Basic



-- @@ L7-19 verbatim
/-!
# Lattice invariants for the Leech lattice

This file defines a few standard predicates on `Submodule ℤ ℝ²⁴` and proves that the Leech lattice
satisfies them.

## Main definitions
* `EvenNormSq`, `Integral`, `Rootless`, `Unimodular`

## Main statements
* `integral_of_evenNormSq`
* `leech_evenNormSq`, `leech_integral`, `leech_rootless`, `leech_unimodular`
-/



-- @@ L22-22 verbatim
namespace SpherePacking.Dim24


-- @@ L24-24 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L26-26 verbatim
open scoped RealInnerProductSpace

-- @@ L27-27 verbatim
open MeasureTheory


-- @@ L29-31 verbatim
/-- `L` has even squared norms: `‖v‖^2 = 2n` for some `n` (depending on `v`). -/
@[expose] public def EvenNormSq (L : Submodule ℤ ℝ²⁴) : Prop :=
  ∀ v : ℝ²⁴, v ∈ L → ∃ n : ℕ, ‖v‖ ^ 2 = (2 : ℝ) * n


-- @@ L33-35 verbatim
/-- `L` is integral: all inner products of lattice vectors are integers. -/
@[expose] public def Integral (L : Submodule ℤ ℝ²⁴) : Prop :=
  ∀ u v : ℝ²⁴, u ∈ L → v ∈ L → ∃ m : ℤ, ⟪u, v⟫ = m


-- @@ L37-39 verbatim
/-- `L` has no vectors of squared norm `2`. -/
@[expose] public def Rootless (L : Submodule ℤ ℝ²⁴) : Prop :=
  ∀ v : ℝ²⁴, v ∈ L → v ≠ 0 → ‖v‖ ^ 2 ≠ (2 : ℝ)


-- @@ L41-43 verbatim
/-- `L` is unimodular (covolume `1`). -/
@[expose] public def Unimodular (L : Submodule ℤ ℝ²⁴) : Prop :=
  ZLattice.covolume L volume = 1


-- @@ L45-60 verbatim
/-- A lattice with even norm squares is integral (by the polarization identity). -/
public lemma integral_of_evenNormSq (L : Submodule ℤ ℝ²⁴) (hEven : EvenNormSq L) : Integral L := by
  intro u v hu hv
  have huv : u + v ∈ L := add_mem hu hv
  rcases hEven u hu with ⟨a, ha⟩
  rcases hEven v hv with ⟨b, hb⟩
  rcases hEven (u + v) huv with ⟨c, hc⟩
  refine ⟨(c : ℤ) - (a : ℤ) - (b : ℤ), ?_⟩
  have hadd : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := norm_add_sq_real u v
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have : ⟪u, v⟫ = (c : ℝ) - (a : ℝ) - (b : ℝ) := by
    have : (2 : ℝ) * ⟪u, v⟫ = (2 : ℝ) * (c : ℝ) - (2 : ℝ) * (a : ℝ) - (2 : ℝ) * (b : ℝ) := by
      linarith [hadd, ha, hb, hc]
    nlinarith [this, h2]
  norm_cast at this
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this


-- @@ L62-64 verbatim
/-- The Leech lattice has even squared norms. -/
public lemma leech_evenNormSq : EvenNormSq LeechLattice := by
  simpa [EvenNormSq] using leech_norm_sq_eq_two_mul


-- @@ L66-68 verbatim
/-- The Leech lattice is integral. -/
public lemma leech_integral : Integral LeechLattice :=
  by simpa using integral_of_evenNormSq (L := LeechLattice) leech_evenNormSq


-- @@ L70-76 verbatim
/-- The Leech lattice is rootless: it contains no nonzero vectors of squared norm `2`. -/
public lemma leech_rootless : Rootless LeechLattice := by
  intro v hv hv0
  have h2 : (2 : ℝ) ≤ ‖v‖ := leech_norm_lower_bound v hv hv0
  have hsq : (4 : ℝ) ≤ ‖v‖ ^ 2 := by nlinarith [h2]
  intro h
  nlinarith [hsq, h]


-- @@ L78-80 verbatim
/-- The Leech lattice is unimodular. -/
public lemma leech_unimodular : Unimodular LeechLattice := by
  simpa [Unimodular] using leech_covolume


-- @@ L82-82 verbatim
end SpherePacking.Dim24
