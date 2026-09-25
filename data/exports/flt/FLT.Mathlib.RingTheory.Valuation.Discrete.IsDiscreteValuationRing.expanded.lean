/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation


-- @@ L11-16 verbatim
/-!
# Elements of valuation one

Material for `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`: an element of the
fraction field of a discrete valuation ring with valuation `1` is the image of a unit.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
universe u


-- @@ L22-22 verbatim
section


-- @@ L24-24 verbatim
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

-- @@ L25-25 verbatim
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]


-- @@ L27-36 verbatim
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing in
/-- An element of the fraction field of a discrete valuation ring with valuation `1` is the image
of a unit. -/
theorem exists_algebraMap_unit_eq_of_valuation_eq_one {x : K}
    (hx : valuation K (maximalIdeal R) x = 1) : ∃ u : Rˣ, algebraMap R K ↑u = x := by
  obtain ⟨u₀, hu₀⟩ := associated_of_valuation_eq (A := R) (K := K) x 1 (by rw [map_one]; exact hx)
  have h1 : algebraMap R K ↑u₀ * x = 1 := by rw [← Algebra.smul_def]; exact hu₀
  have h2 : algebraMap R K ↑u₀ * algebraMap R K ↑u₀⁻¹ = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact ⟨u₀⁻¹, mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h1) (h2.trans h1.symm)⟩



-- @@ L39-39 verbatim
end
