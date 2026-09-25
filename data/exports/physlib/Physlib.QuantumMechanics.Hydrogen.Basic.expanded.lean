/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.SpaceDQuantumSystem
public import Physlib.QuantumMechanics.Operators.Position

-- @@ L10-29 verbatim
/-!

# Hydrogen atom

This module introduces the `d`-dimensional hydrogen atom with `1/r` potential.

In addition to the dimension `d`, the quantum mechanical system is characterized by
a mass `m > 0` and constant `k` appearing in the potential `V = -k/r`.
The standard hydrogen atom has `d=3`, `m = mₑmₚ/(mₑ + mₚ) ≈ mₑ` and `k = e²/4πε₀`.

The potential `V = -k/r` is singular at the origin. To address this we define a regularized
Hamiltonian in which the potential is replaced by `-k·r(ε)⁻¹`, where `r(ε)² = ‖x‖² + ε²`.
This goes by several names including "soft-core" and "truncated" Coulomb potential.

## References

* https://doi.org/10.1103/PhysRevA.80.032507. [ref: doi_physreva_80_032507]
* https://doi.org/10.1063/1.3290740. [ref: doi_1063_1_3290740]

-/


-- @@ L31-31 verbatim
TODO "Prove that the Hydrogen Hamiltonian is _not_ essentially self-adjoint for `d < 3`."


-- @@ L33-33 verbatim
TODO "Prove that the Hydrogen Hamiltonian is essentially self-adjoint for `d ≥ 3`."


-- @@ L35-36 verbatim
TODO "Prove that (the closure of) the Hydrogen Hamiltonian has eigenvalues (point spectrum)
  {-½mk²ℏ⁻² / (n + ½(d - 1))² | n ∈ ℕ}. These correspond to the bound states."


-- @@ L38-39 verbatim
TODO "Prove that (the closure of) the Hydrogen Hamiltonian has continuous spectrum [0,∞).
  These correspond to scattering states."


-- @@ L41-41 verbatim
TODO "Define the Rydberg formula and Lyman, Balmer, Paschen, etc. series."


-- @@ L43-43 verbatim
TODO "Determine the wavelengths / frequencies of the Lyman, Balmer, Paschen, etc. series."


-- @@ L45-45 verbatim
TODO "Analyze the Zeeman effect using first-order degenerate perturbation theory."


-- @@ L47-47 verbatim
TODO "Analyze the Stark effect using first-order degenerate perturbation theory."


-- @@ L49-49 verbatim
@[expose] public section


-- @@ L51-51 verbatim
namespace QuantumMechanics

-- @@ L52-52 verbatim
open MeasureTheory

-- @@ L53-53 verbatim
open SchwartzMap


-- @@ L55-60 verbatim
/-- A hydrogen atom is characterized by the number of spatial dimensions `d`,
  the mass `m` and the coefficient `k` for the `1/r` potential. -/
structure HydrogenAtom extends SpaceDQuantumSystem where
  /-- Coefficient in the Coulomb potential (positive for attractive) -/
  k : ℝ
  coulomb_potential : potential = fun x ↦ -k * ‖x‖⁻¹


-- @@ L62-62 verbatim
namespace HydrogenAtom

-- @@ L63-63 verbatim
noncomputable section


-- @@ L65-65 verbatim
variable (H : HydrogenAtom)


-- @@ L67-69 verbatim
/-!
## A. Basic
-/


-- @@ L71-72 verbatim
@[simp]
lemma potential_eq : H.potential = fun x ↦ -H.k * ‖x‖⁻¹ := H.coulomb_potential


-- @@ L74-77 verbatim
@[fun_prop]
lemma potential_AESM : AEStronglyMeasurable H.potential := by
  rw [potential_eq]
  exact AEMeasurable.aestronglyMeasurable (by fun_prop)


-- @@ L79-80 verbatim
@[fun_prop]
lemma potential_AEM : AEMeasurable H.potential := H.potential_AESM.aemeasurable


-- @@ L82-84 verbatim
/-!
## B. Regularization
-/


-- @@ L86-89 expanded
/-- The hydrogen atom Hamiltonian regularized by `ε ≠ 0` is defined to be
  `𝐇(ε) ≔ (2m)⁻¹𝐩² - k·𝐫(ε)⁻¹`. -/
def hamiltonianRegCLM (ε : ℝˣ) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  (2 * H.m)⁻¹ • (momentumCLM ⬝ᵥ momentumCLM) - H.k • radiusRegPowCLM ε (-1)


-- @@ L91-92 expanded
lemma hamiltonianRegCLM_eq (ε : ℝˣ) :
    H.hamiltonianRegCLM ε =
      (2 * H.m)⁻¹ • (momentumCLM ⬝ᵥ momentumCLM) - H.k • radiusRegPowCLM ε (-1) :=
  rfl


-- @@ L94-94 verbatim
end

-- @@ L95-95 verbatim
end HydrogenAtom

-- @@ L96-96 verbatim
end QuantumMechanics
