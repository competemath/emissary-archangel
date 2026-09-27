/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpDerivativeMap


-- @@ L11-11 verbatim
/-! The L² derivative-field construction is a contraction between the actual Banach spaces. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section



-- @@ L19-19 verbatim
namespace EulerLpDerivative


-- @@ L21-21 verbatim
open MeasureTheory


-- @@ L23-26 verbatim
variable {X P V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (μ : Measure X)


-- @@ L28-38 verbatim
/-- Bundling linear, bundling `toFun`, `map_add`, `map_smul`. -/
def bundlingLinear : Lp (P →L[ℝ] V) 2 μ →ₗ[ℝ] (P →L[ℝ] Lp V 2 μ) where
  toFun := derivativeMap μ
  map_add' D E := by
    apply ContinuousLinearMap.ext
    intro a
    exact ((ContinuousLinearMap.apply ℝ V a).compLpL 2 μ).map_add D E
  map_smul' c D := by
    apply ContinuousLinearMap.ext
    intro a
    exact ((ContinuousLinearMap.apply ℝ V a).compLpL 2 μ).map_smul c D


-- @@ L40-46 verbatim
/-- Derivative bundling, bundling `toLinearMap`, `cont`. -/
def derivativeBundling : Lp (P →L[ℝ] V) 2 μ →L[ℝ] (P →L[ℝ] Lp V 2 μ) where
  toLinearMap := bundlingLinear μ
  cont := AddMonoidHomClass.continuous_of_bound (bundlingLinear (P := P) (V := V) μ) 1
    (fun D => by
      change ‖derivativeMap μ D‖ ≤ 1 * ‖D‖
      simpa only [one_mul] using derivativeMap_norm_le μ D)


-- @@ L48-49 verbatim
@[simp] theorem derivativeBundling_apply (D : Lp (P →L[ℝ] V) 2 μ) :
    derivativeBundling μ D = derivativeMap μ D := rfl


-- @@ L51-54 verbatim
theorem derivativeBundling_norm_le_one : ‖derivativeBundling (P := P) (V := V) μ‖ ≤ 1 :=
  (derivativeBundling (P := P) (V := V) μ).opNorm_le_bound zero_le_one (fun D => by
    change ‖derivativeMap μ D‖ ≤ 1 * ‖D‖
    simpa only [one_mul] using derivativeMap_norm_le μ D)


-- @@ L56-56 verbatim
end EulerLpDerivative
