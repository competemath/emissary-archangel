/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier


-- @@ L13-17 verbatim
/-!
The Fourier integral bundled with Schwartz regularity. Keeping the underlying function
explicit lets Sobolev norms expose their formula without exposing the analytic proofs
of Fourier inversion and rapid decay.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerSobolev


-- @@ L25-25 verbatim
open scoped SchwartzMap FourierTransform ContDiff


-- @@ L27-29 verbatim
variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


-- @@ L31-43 verbatim
/-- The ordinary Fourier integral with its Schwartz smoothness and decay proofs. -/
def schwartzFourier (f : 𝓢(V, E)) : 𝓢(V, E) where
  toFun := 𝓕 (f : V → E)
  smooth' := by
    have h : ContDiff ℝ ∞ ((𝓕 f : 𝓢(V, E)) : V → E) := (𝓕 f : 𝓢(V, E)).smooth'
    rw [SchwartzMap.fourier_coe] at h
    exact h
  decay' := by
    have h : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : V,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((𝓕 f : 𝓢(V, E)) : V → E) x‖ ≤ C :=
      (𝓕 f : 𝓢(V, E)).decay'
    rw [SchwartzMap.fourier_coe] at h
    exact h


-- @@ L45-46 verbatim
private theorem schwartzFourier_eq (f : 𝓢(V, E)) :
    schwartzFourier f = (𝓕 f : 𝓢(V, E)) := rfl


-- @@ L48-50 verbatim
/-- The bundled Schwartz transform has exactly the ordinary Fourier integral as its values. -/
theorem schwartzFourier_apply (f : 𝓢(V, E)) (x : V) :
    schwartzFourier f x = 𝓕 (f : V → E) x := rfl


-- @@ L52-62 verbatim
/-- The ordinary Fourier integral as a continuous linear map on Schwartz functions. -/
def schwartzFourierCLM : 𝓢(V, E) →L[ℂ] 𝓢(V, E) where
  toFun := schwartzFourier
  map_add' := by
    intro f g
    exact (FourierTransform.fourierCLM (F := 𝓢(V, E)) ℂ 𝓢(V, E)).map_add f g
  map_smul' := by
    intro c f
    exact (FourierTransform.fourierCLM (F := 𝓢(V, E)) ℂ 𝓢(V, E)).map_smul c f
  cont := by
    exact (FourierTransform.fourierCLM (F := 𝓢(V, E)) ℂ 𝓢(V, E)).continuous


-- @@ L64-66 verbatim
private theorem schwartzFourierCLM_eq :
    schwartzFourierCLM (V := V) (E := E) =
      FourierTransform.fourierCLM (F := 𝓢(V, E)) ℂ 𝓢(V, E) := rfl


-- @@ L68-68 verbatim
end EulerSobolev
