/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule

-- @@ L10-39 verbatim
/-!

# The Fourier transform on `SpaceDHilbertSpace`

## i. Overview

In this module we define the Fourier transform on `SpaceDHilbertSpace d` as a unitary operator.
Mathlib's L² Fourier transform `MeasureTheory.Lp.fourierTransformₗᵢ` is a linear isometry
equivalence of `Lp ℂ 2 volume`, hence of `SpaceDHilbertSpace d`, onto itself; packaged as
`fourierUnitary d`.

## ii. Key results

- `fourierUnitary d` : the L² Fourier transform as a unitary
  `SpaceDHilbertSpace d ≃ₗᵢ[ℂ] SpaceDHilbertSpace d`, acting as `𝓕`/`𝓕⁻`
  (`fourierUnitary_apply`, `fourierUnitary_symm_apply`).
- `schwartzIncl_fourier_eq` : `𝓕 (schwartzIncl f) = schwartzIncl (𝓕 f)`.
- `schwartzIncl_fourierInv_eq` : the inverse acts by the inverse Schwartz Fourier transform.
- `fourierUnitary_map_schwartzSubmodule` : `fourierUnitary d` maps the Schwartz submodule onto
  itself.

## iii. Table of contents

- A. The Fourier unitary
- B. Action on the Schwartz submodule

## iv. References

* None.
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
namespace QuantumMechanics

-- @@ L44-44 verbatim
namespace SpaceDHilbertSpace


-- @@ L46-46 verbatim
open MeasureTheory

-- @@ L47-47 verbatim
open SchwartzMap

-- @@ L48-48 verbatim
open scoped FourierTransform


-- @@ L50-50 verbatim
variable {d : ℕ}


-- @@ L52-52 verbatim
/-! ## A. The Fourier unitary -/


-- @@ L54-56 verbatim
/-- The L² Fourier transform as a unitary on `SpaceDHilbertSpace d`. -/
noncomputable def fourierUnitary (d : ℕ) :
    SpaceDHilbertSpace d ≃ₗᵢ[ℂ] SpaceDHilbertSpace d := Lp.fourierTransformₗᵢ (Space d) ℂ



-- @@ L59-61 verbatim
/-- `fourierUnitary d` acts as the L² Fourier transform `𝓕`. -/
@[simp]
lemma fourierUnitary_apply (ψ : SpaceDHilbertSpace d) : fourierUnitary d ψ = 𝓕 ψ := rfl


-- @@ L63-65 verbatim
/-- `(fourierUnitary d).symm` acts as the inverse L² Fourier transform `𝓕⁻`. -/
@[simp]
lemma fourierUnitary_symm_apply (ψ : SpaceDHilbertSpace d) : (fourierUnitary d).symm ψ = 𝓕⁻ ψ := rfl


-- @@ L67-67 verbatim
/-! ## B. Action on the Schwartz submodule -/


-- @@ L69-72 verbatim
/-- Applying `fourierUnitary d` to the L² class of a Schwartz map `f` gives the L² class of the
Schwartz Fourier transform `𝓕 f`. -/
lemma schwartzIncl_fourier_eq (f : 𝓢(Space d, ℂ)) :
    𝓕 (schwartzIncl volume f) = schwartzIncl volume (𝓕 f) := SchwartzMap.toLp_fourier_eq f


-- @@ L74-78 verbatim
/-- Applying `𝓕⁻` to the L² class of a Schwartz map `f` gives the L² class of the inverse
Schwartz Fourier transform `𝓕⁻ f`. -/
lemma schwartzIncl_fourierInv_eq (f : 𝓢(Space d, ℂ)) :
    𝓕⁻ (schwartzIncl volume f) = schwartzIncl volume (𝓕⁻ f) :=
  SchwartzMap.toLp_fourierInv_eq f


-- @@ L80-84 verbatim
/-- Pulling the L² class of `𝓕 f` back through the Fourier unitary recovers the L² class of `f`. -/
@[simp]
lemma fourierInv_schwartzIncl_fourier (f : 𝓢(Space d, ℂ)) :
    𝓕⁻ (schwartzIncl volume (𝓕 f)) = schwartzIncl volume f := by
  rw [← schwartzIncl_fourier_eq, FourierPair.fourierInv_fourier_eq]


-- @@ L86-93 verbatim
/-- The Fourier unitary maps the Schwartz submodule onto itself. -/
lemma fourierUnitary_map_schwartzSubmodule :
    (SchwartzSubmodule d).map (fourierUnitary d).toLinearMap = SchwartzSubmodule d := by
  apply le_antisymm
  · rintro x ⟨y, ⟨f, rfl⟩, rfl⟩
    exact ⟨𝓕 f, (schwartzIncl_fourier_eq f).symm⟩
  · rintro x ⟨g, rfl⟩
    exact ⟨𝓕⁻ (schwartzIncl volume g), ⟨𝓕⁻ g, (schwartzIncl_fourierInv_eq g).symm⟩, by simp⟩


-- @@ L95-95 verbatim
end SpaceDHilbertSpace

-- @@ L96-96 verbatim
end QuantumMechanics
