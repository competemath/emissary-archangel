/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecificLimits.Normed


-- @@ L12-12 verbatim
/-! # Tendstolems -/



-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-18 verbatim
open TopologicalSpace Set
  Metric Filter Function Complex


-- @@ L20-20 verbatim
open scoped Interval Real NNReal ENNReal Topology BigOperators Nat



-- @@ L23-30 verbatim
lemma int_tendsto_nat {f : ℤ → ℂ} {x : ℂ} (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ => f n) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop] at *
  intro ε hε
  obtain ⟨N, hN⟩ := hf ε hε
  use N.natAbs
  intro n hn
  exact hN n (by omega)


-- @@ L32-33 verbatim
lemma pnat_tendsto_nat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x)) :
  Tendsto f atTop (𝓝 x) := tendsto_comp_val_Ioi_atTop.mp hf


-- @@ L35-36 verbatim
lemma nat_tendsto_pnat (f : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) :
  Tendsto (fun n : ℕ+ => f n) atTop (𝓝 x) := tendsto_comp_val_Ioi_atTop.mpr hf


-- @@ L38-39 verbatim
lemma rest (f g : ℕ → ℂ) (x : ℂ) (hf : Tendsto f atTop (𝓝 x)) (hfg : Tendsto (g - f) atTop (𝓝 0)) :
  Tendsto g atTop (𝓝 x) := by simpa using Tendsto.add hf hfg



-- @@ L42-43 verbatim
lemma aux47 (r : ℂ) (hr : ‖r‖ < 1) : Tendsto (fun n : ℕ => 1 - r^n) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds.sub <| tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr
