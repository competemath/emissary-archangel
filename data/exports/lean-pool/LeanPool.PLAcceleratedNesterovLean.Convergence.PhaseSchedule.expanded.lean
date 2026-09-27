/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real


-- @@ L11-22 verbatim
/-!
# Retuning Parameters for Nesterov Algorithm

Defines both direct `θ` retuning parameters and phase-indexed auxiliary
parameters for the Nesterov algorithm:

- Phase k (k ≥ 1): μₖ = μ·(1 − 4⁻ᵏ), θₖ = 4⁻ᵏ

Key arithmetic facts:
- μₖ ↑ μ as k → ∞
- θₖ ↓ 0 as k → ∞
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace PLAcceleratedNesterovLean


-- @@ L30-30 verbatim
open Real


-- @@ L32-32 verbatim
/-! ## Phase parameter definitions -/


-- @@ L34-35 verbatim
/-- PL parameter at phase k: μₖ = μ · (1 - (1/4)^k). -/
def muOfPhase (μ : ℝ) (k : ℕ) : ℝ := μ * (1 - (4 : ℝ)⁻¹ ^ k)


-- @@ L37-38 verbatim
/-- Budget-split parameter at phase k: θₖ = (1/4)^k. -/
def thetaOfPhase (k : ℕ) : ℝ := (4 : ℝ)⁻¹ ^ k


-- @@ L40-43 verbatim
/-- Momentum parameter at phase k. -/
def rhoOfPhase (L : ℝ) (μ : ℝ) (k : ℕ) : ℝ :=
  let a := Real.sqrt (muOfPhase μ k / L)
  (1 - a) / (1 + a)


-- @@ L45-46 verbatim
/-- Directly retuned PL parameter: μθ = μ · (1 - θ). -/
def muOfTheta (μ θ : ℝ) : ℝ := μ * (1 - θ)


-- @@ L48-51 verbatim
/-- Directly retuned momentum parameter. -/
def rhoOfTheta (L μ θ : ℝ) : ℝ :=
  let a := Real.sqrt (muOfTheta μ θ * (1 / L))
  (1 - a) / (1 + a)


-- @@ L53-54 verbatim
/-- Step size (constant across phases). -/
def etaOfPhase (L : ℝ) : ℝ := 1 / L


-- @@ L56-56 verbatim
/-! ## Basic arithmetic properties -/


-- @@ L58-60 verbatim
theorem thetaOfPhase_pos (k : ℕ) : 0 < thetaOfPhase k := by
  simp only [thetaOfPhase]
  positivity


-- @@ L62-69 verbatim
theorem thetaOfPhase_lt_one {k : ℕ} (hk : 1 ≤ k) : thetaOfPhase k < 1 := by
  simp only [thetaOfPhase]
  have h4 : (0 : ℝ) < 4⁻¹ := by positivity
  have h4_lt1 : (4 : ℝ)⁻¹ < 1 := by norm_num
  calc (4 : ℝ)⁻¹ ^ k ≤ (4 : ℝ)⁻¹ ^ 1 := by
        apply pow_le_pow_of_le_one (le_of_lt h4) (le_of_lt h4_lt1) hk
    _ = (4 : ℝ)⁻¹ := pow_one _
    _ < 1 := h4_lt1


-- @@ L71-79 verbatim
theorem muOfPhase_pos {μ : ℝ} (hμ : 0 < μ) {k : ℕ} (hk : 1 ≤ k) :
    0 < muOfPhase μ k := by
  simp only [muOfPhase]
  apply mul_pos hμ
  have : (4 : ℝ)⁻¹ ^ k < 1 := by
    calc (4 : ℝ)⁻¹ ^ k ≤ (4 : ℝ)⁻¹ ^ 1 := by
          apply pow_le_pow_of_le_one (by positivity) (by norm_num) hk
      _ < 1 := by norm_num
  linarith


-- @@ L81-85 verbatim
/-- Positivity of the retuned parameter μθ. -/
theorem muOfTheta_pos {μ θ : ℝ} (hμ : 0 < μ) (hθ_lt1 : θ < 1) :
    0 < muOfTheta μ θ := by
  simp only [muOfTheta]
  exact mul_pos hμ (sub_pos.mpr hθ_lt1)


-- @@ L87-91 verbatim
/-- The retuned parameter is strictly below μ when θ > 0. -/
theorem muOfTheta_lt_mu {μ θ : ℝ} (hμ : 0 < μ) (hθ_pos : 0 < θ) :
    muOfTheta μ θ < μ := by
  simp only [muOfTheta]
  nlinarith


-- @@ L93-96 verbatim
theorem muOfPhase_lt_mu {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    muOfPhase μ k < μ := by
  simp only [muOfPhase]
  simp_all


-- @@ L98-104 verbatim
theorem muOfPhase_increasing {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    muOfPhase μ k ≤ muOfPhase μ (k + 1) := by
  simp only [muOfPhase]
  have h1 : (4 : ℝ)⁻¹ ^ (k + 1) ≤ (4 : ℝ)⁻¹ ^ k := by
    apply pow_le_pow_of_le_one (by positivity) (by norm_num)
    omega
  nlinarith


-- @@ L106-109 verbatim
/-- muOfPhase k = μ · (1 - θₖ) -/
theorem muOfPhase_eq (μ : ℝ) (k : ℕ) :
    muOfPhase μ k = μ * (1 - thetaOfPhase k) := by
  simp [muOfPhase, thetaOfPhase]


-- @@ L111-116 verbatim
/-- 1 - muOfPhase k / μ = θₖ -/
theorem one_sub_muOfPhase_div {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    1 - muOfPhase μ k / μ = thetaOfPhase k := by
  simp only [muOfPhase, thetaOfPhase]
  field_simp
  ring


-- @@ L118-122 verbatim
/-- a_k = √(μ_k·η) ≤ √(μ·η) for all k. -/
theorem sqrt_muOfPhase_eta_le {μ η : ℝ} (hμ : 0 < μ) (hη : 0 < η) (k : ℕ) :
    Real.sqrt (muOfPhase μ k * η) ≤ Real.sqrt (μ * η) :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
    (le_of_lt (muOfPhase_lt_mu hμ k)) (le_of_lt hη))


-- @@ L124-135 verbatim
/-- 1/(1-a_k) ≤ 1/(1-√(μη)) for all k (uniform bound on jump constants). -/
theorem one_div_one_sub_sqrt_le {μ η : ℝ} (hμ : 0 < μ) (hη : 0 < η)
    (hμη : μ * η < 1) (k : ℕ) :
    1 / (1 - Real.sqrt (muOfPhase μ k * η)) ≤
    1 / (1 - Real.sqrt (μ * η)) := by
  have ha_inf_lt1 : Real.sqrt (μ * η) < 1 := by
    calc _ < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt (mul_pos hμ hη)) hμη
      _ = 1 := Real.sqrt_one
  have ha_k_le := sqrt_muOfPhase_eta_le hμ hη k
  have h1 : 0 < 1 - Real.sqrt (muOfPhase μ k * η) := by linarith
  have h2 : 0 < 1 - Real.sqrt (μ * η) := by linarith
  exact one_div_le_one_div_of_le h2 (by linarith)


-- @@ L137-137 verbatim
/-! ## Geometric series bounds -/


-- @@ L139-160 verbatim
/-- Partial sums of r^(k+1) for 0 ≤ r < 1 are bounded by r/(1-r). -/
theorem partial_geometric_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, r ^ (k + 1) ≤ r / (1 - r) := by
  have h1mr : 0 < 1 - r := by linarith
  -- Factor: ∑ r^(k+1) = r · ∑ r^k
  have hfactor : ∑ k ∈ Finset.range K, r ^ (k + 1) =
      r * ∑ k ∈ Finset.range K, r ^ k := by
    rw [Finset.mul_sum]; congr 1; ext k; ring
  rw [hfactor]
  -- Geometric sum: (∑ r^k) · (r-1) = r^K - 1, so ∑ r^k = (1-r^K)/(1-r)
  have hgeom : (∑ k ∈ Finset.range K, r ^ k) * (r - 1) = r ^ K - 1 :=
    geom_sum_mul r K
  have hsum_eq : ∑ k ∈ Finset.range K, r ^ k = (1 - r ^ K) / (1 - r) := by
    have : (∑ k ∈ Finset.range K, r ^ k) = (1 - r ^ K) / (1 - r) := by
      rw [eq_div_iff h1mr.ne']
      linarith
    exact this
  rw [hsum_eq]
  rw [show r * ((1 - r ^ K) / (1 - r)) = r * (1 - r ^ K) / (1 - r) from by ring]
  apply div_le_div_of_nonneg_right _ (le_of_lt h1mr)
  have : 0 ≤ r ^ K := pow_nonneg hr0 K
  nlinarith


-- @@ L162-168 verbatim
/-- Partial sums of (1/2)^(k+1) are bounded by 1. -/
theorem partial_geometric_half_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((1 : ℝ) / 2) ^ (k + 1) ≤ 1 := by
  calc ∑ k ∈ Finset.range K, ((1 : ℝ) / 2) ^ (k + 1)
      ≤ (1 / 2) / (1 - 1 / 2) :=
        partial_geometric_sum_le (by norm_num) (by norm_num) K
    _ = 1 := by norm_num


-- @@ L170-176 verbatim
/-- Partial sums of (1/4)^k for k ≥ 1 are bounded by 1/3. -/
theorem partial_geometric_quarter_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((1 : ℝ) / 4) ^ (k + 1) ≤ 1 / 3 := by
  calc ∑ k ∈ Finset.range K, ((1 : ℝ) / 4) ^ (k + 1)
      ≤ (1 / 4) / (1 - 1 / 4) :=
        partial_geometric_sum_le (by norm_num) (by norm_num) K
    _ = 1 / 3 := by norm_num


-- @@ L178-178 verbatim
end PLAcceleratedNesterovLean
