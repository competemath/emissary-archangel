/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Physlib.Electromagnetism.ThreeDimension.Basic
public import Physlib.Electromagnetism.Dynamics.IsExtrema

-- @@ L10-42 verbatim
/-!

# A. Maxwell's equations in three dimensions

Maxwell's equations relate electric and magnetic fields to electric charge and current. In three
spatial dimensions they can be written using the familiar divergence, curl, and time-derivative
operators of vector calculus.

## A.1. Main results

This module proves the four differential equations:

- `gaussLawElectric`, relating the divergence of the electric field to charge density;
- `gaussLawMagnetic`, stating that the magnetic field is divergence-free;
- `ampereLaw`, including both the electric current and displacement-current terms;
- `faradayLaw`, relating the curl of the electric field to the time derivative of the magnetic
  field.

## A.2. Relation to the covariant formulation

The electric and magnetic fields are obtained from an electromagnetic potential. Gauss's law for
the electric field and Ampère's law are derived from the covariant extremality condition
`IsExtrema`, while the two homogeneous equations follow from the potential definitions and
smoothness assumptions. The results therefore connect the tensorial backend to the standard
three-dimensional presentation.

## A.3. Current scope

The statements here are pointwise differential equations in free space. Integral formulations,
boundary conditions, and constitutive laws for material media are outside the current scope of this
module.

-/

-- @@ L43-43 verbatim
namespace Electromagnetism

-- @@ L44-44 verbatim
namespace ThreeDimension


-- @@ L46-46 verbatim
open Time

-- @@ L47-47 verbatim
open Space

-- @@ L48-48 verbatim
open ElectromagneticPotential

-- @@ L49-49 verbatim
open ContDiff


-- @@ L51-51 verbatim
variable {𝓕 : FreeSpace} (V : ElectromagneticPotential 3) (J₄ : LorentzCurrentDensity 3)


-- @@ L53-53 verbatim
local notation "φ" => V.scalarPotential 𝓕.c

-- @@ L54-54 verbatim
local notation "A" => V.vectorPotential 𝓕.c

-- @@ L55-55 verbatim
local notation "E" => V.electricField 𝓕.c

-- @@ L56-56 verbatim
local notation "B" => V.magneticField 𝓕.c

-- @@ L57-57 verbatim
local notation "ρ" => J₄.chargeDensity 𝓕.c

-- @@ L58-58 verbatim
local notation "J" => J₄.currentDensity 𝓕.c

-- @@ L59-59 verbatim
local notation "ε₀" => 𝓕.ε₀

-- @@ L60-60 verbatim
local notation "μ₀" => 𝓕.μ₀


-- @@ L62-66 expanded
/-- Gauss's law for the electric field. -/
theorem gaussLawElectric (t : Time) (x : Space) (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V)
    (hJ : ContDiff ℝ ∞ J₄) : (div (E t)) x = ρ t x / ε₀ := by
  exact ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hV J₄ hJ (𝓕 := 𝓕)).mp h t x).1


-- @@ L68-71 expanded
/-- Gauss's law for the magnetic field. -/
theorem gaussLawMagnetic (t : Time) (x : Space) (hV : ContDiff ℝ ∞ V) : (div (B t)) x = 0 := by
  rw [magneticField_eq_3D, div_of_curl_eq_zero _ (by fun_prop), Pi.zero_apply]


-- @@ L73-80 expanded
/-- Ampère's law. -/
theorem ampereLaw (t : Time) (x : Space) (h : IsExtrema 𝓕 V J₄) (hV : ContDiff ℝ ∞ V)
    (hJ : ContDiff ℝ ∞ J₄) : (curl (B t)) x = μ₀ • J t x + μ₀ • ε₀ • ∂ₜ (fun t => E t x) t :=
  by
  ext i
  have hdE := ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hV J₄ hJ (𝓕 := 𝓕)).mp h t x).2 i
  rw [← magneticField_curl_eq_magneticFieldMatrix _ (hV.of_le ENat.LEInfty.out)] at hdE
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, ← mul_assoc, hdE, add_sub_cancel]


-- @@ L82-88 expanded
/-- Faraday's law. -/
theorem faradayLaw (t : Time) (x : Space) (hV : ContDiff ℝ ∞ V) :
    (curl (E t)) x = -∂ₜ (fun t => B t x) t :=
  by
  rw [electricField_eq_3D, magneticField_eq_3D, fun_curl_sub, fun_curl_neg, curl_of_grad_eq_zero,
    time_deriv_curl_commute]
  simp only [neg_zero, Pi.zero_apply, zero_sub]
  all_goals fun_prop


-- @@ L90-90 verbatim
end ThreeDimension

-- @@ L91-91 verbatim
end Electromagnetism
