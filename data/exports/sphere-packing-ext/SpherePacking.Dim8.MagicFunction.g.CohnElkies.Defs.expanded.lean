module
public import SpherePacking.Dim8.MagicFunction.g.Basic



-- @@ L5-20 verbatim
/-!
# Cohn-Elkies auxiliary definitions for `g`

Blueprint reference: `blueprint/src/subsections/modform-ineq.tex`.

This file introduces the auxiliary real-valued functions `A` and `B` and a radial profile
`gRadial` satisfying `g x = gRadial (‖x‖ ^ 2)`.

## Main definitions
* `gRadial`
* `A`
* `B`

## Main statement
* `g_apply_eq_gRadial_norm_sq`
-/


-- @@ L22-22 verbatim
namespace MagicFunction.g.CohnElkies


-- @@ L24-24 verbatim
open scoped FourierTransform SchwartzMap


-- @@ L26-26 verbatim
open Real Complex SchwartzMap

-- @@ L27-27 verbatim
open MagicFunction.FourierEigenfunctions


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


-- @@ L33-35 verbatim
/-- Radial profile of `g` in the variable `‖x‖^2`. -/
@[expose] public def gRadial : 𝓢(ℝ, ℂ) :=
  ((π * I) / 8640) • a' - (I / (240 * π)) • b'


-- @@ L37-39 verbatim
/-- The function `g` is radial, with profile `gRadial` in the variable `‖x‖ ^ 2`. -/
public theorem g_apply_eq_gRadial_norm_sq (x : ℝ⁸) : g x = gRadial (‖x‖ ^ 2) := by
  simp [g, gRadial, a, b, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]


-- @@ L41-49 verbatim
/--
Auxiliary function `A(t)` from the blueprint, defined as the real part of
`-t^2 * φ₀(i/t) - (36/π^2) * ψI(i t)`.

We only use `A(t)` for `t > 0`, but define it on all `ℝ`.
-/
@[expose] public def A (t : ℝ) : ℝ :=
  (-(t ^ 2)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re -
    (36 / (π ^ (2 : ℕ)) : ℝ) * (ψI' ((Complex.I : ℂ) * (t : ℂ))).re


-- @@ L51-59 verbatim
/--
Auxiliary function `B(t)` from the blueprint, defined as the real part of
`-t^2 * φ₀(i/t) + (36/π^2) * ψI(i t)`.

We only use `B(t)` for `t > 0`, but define it on all `ℝ`.
-/
@[expose] public def B (t : ℝ) : ℝ :=
  (-(t ^ 2)) * (φ₀'' ((Complex.I : ℂ) / (t : ℂ))).re +
    (36 / (π ^ (2 : ℕ)) : ℝ) * (ψI' ((Complex.I : ℂ) * (t : ℂ))).re


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end MagicFunction.g.CohnElkies
