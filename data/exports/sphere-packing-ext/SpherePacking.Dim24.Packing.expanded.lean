module
public import SpherePacking.Dim24.LeechLattice.Defs
import SpherePacking.Dim24.LeechLattice.Basis
import SpherePacking.Dim24.LeechLattice.Norm



-- @@ L7-19 verbatim
/-!
# The Leech lattice packing

This file defines the Leech lattice packing as a periodic sphere packing in `ℝ²⁴` and computes
its density.

## Main definitions
* `LeechPacking`

## Main statements
* `LeechPacking_density`
* `LeechPacking_density_le_SpherePackingConstant`
-/


-- @@ L21-21 verbatim
namespace SpherePacking.Dim24


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open scoped BigOperators Real

-- @@ L26-26 verbatim
open MeasureTheory Metric


-- @@ L28-28 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L30-41 verbatim
/-- The Leech lattice packing as a periodic sphere packing in `ℝ²⁴`. -/
@[expose] public noncomputable def LeechPacking : PeriodicSpherePacking 24 where
  separation := 2
  lattice := LeechLattice
  centers := LeechLattice
  centers_dist := by
    intro x y hxy
    simpa [Subtype.dist_eq, dist_eq_norm] using
      (leech_norm_lower_bound ((x : ℝ²⁴) - (y : ℝ²⁴)) (sub_mem x.property y.property) (by
        intro h
        exact hxy (Subtype.ext <| sub_eq_zero.mp h)))
  lattice_action x y := add_mem


-- @@ L43-44 verbatim
/-- The separation of the Leech packing is `2`. -/
public lemma LeechPacking_separation : LeechPacking.separation = 2 := rfl


-- @@ L46-47 verbatim
/-- The underlying lattice of the Leech packing is `LeechLattice`. -/
public lemma LeechPacking_lattice : LeechPacking.lattice = LeechLattice := rfl


-- @@ L49-51 verbatim
/-- The Leech packing has a single orbit of centers under lattice translations. -/
public lemma LeechPacking_numReps : LeechPacking.numReps = 1 :=
  PeriodicSpherePacking.numReps_eq_one (S := LeechPacking) rfl


-- @@ L53-76 verbatim
/-- Density of the Leech packing: `Vol(B(0,1)) = π^12 / 12!` (since it is unimodular). -/
public theorem LeechPacking_density :
    LeechPacking.density = ENNReal.ofReal π ^ 12 / (Nat.factorial 12) := by
  have hd : (0 : ℕ) < 24 := by omega
  set L : ℝ := ∑ i : Fin 24, ‖(Leech_ℤBasis i : ℝ²⁴)‖
  let bL := Leech_ℤBasis.ofZLatticeBasis ℝ LeechLattice
  have hL : ∀ x ∈ ZSpan.fundamentalDomain bL, ‖x‖ ≤ L := by
    intro x hx
    have hfract : ZSpan.fract bL x = x :=
      (ZSpan.fract_eq_self (b := bL) (x := x)).2 hx
    simpa [L, bL, hfract] using (ZSpan.norm_fract_le (K := ℝ) (b := bL) x)
  rw [PeriodicSpherePacking.density_eq (S := LeechPacking) (b := Leech_ℤBasis) (L := L) hL hd]
  simp only [LeechPacking_numReps, Nat.cast_one, LeechPacking_separation, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, div_self, one_mul, LeechPacking_lattice,
    leech_fundamentalDomain_volume, div_one]
  have hvol :
      volume (ball (0 : ℝ²⁴) (1 : ℝ)) = ENNReal.ofReal (π ^ (12 : ℕ) / (Nat.factorial 12 : ℝ)) := by
    simpa [finrank_euclideanSpace] using
      (InnerProductSpace.volume_ball_of_dim_even (E := ℝ²⁴) (k := 12) (hk := by simp)
        (x := (0 : ℝ²⁴)) (r := (1 : ℝ)))
  rw [hvol]
  have hfac_pos : (0 : ℝ) < (Nat.factorial 12 : ℝ) := by exact_mod_cast Nat.factorial_pos 12
  rw [ENNReal.ofReal_div_of_pos hfac_pos]
  simp [ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_natCast]


-- @@ L78-82 verbatim
/-- The Leech packing realizes a lower bound on `SpherePackingConstant 24` by definition. -/
public theorem LeechPacking_density_le_SpherePackingConstant :
    LeechPacking.density ≤ SpherePackingConstant 24 := by
  simpa [SpherePackingConstant] using
    (le_iSup (fun S : SpherePacking 24 => S.density) (LeechPacking.toSpherePacking))


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end SpherePacking.Dim24
