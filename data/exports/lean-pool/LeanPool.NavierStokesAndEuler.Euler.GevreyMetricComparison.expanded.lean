/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevGevreyOperators
public import LeanPool.NavierStokesAndEuler.Euler.WeightedCylinderEnergy
public import LeanPool.NavierStokesAndEuler.Euler.FiniteMetricEnergy
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse


-- @@ L14-15 verbatim
/-! Cutoff-independent comparison between actual Sobolev Gevrey sums and the source's metric root
energies. -/


-- @@ L17-17 verbatim
section


-- @@ L19-19 verbatim
/-! Exact identification of the source's base-Sobolev word sum and root metric energy. -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerBaseWordMetric


-- @@ L27-28 verbatim
open EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
    EulerFiniteMetricEnergy

-- @@ L29-29 verbatim
open InnerProductSpace


-- @@ L31-32 verbatim
/-- A base Sobolev word of any length at most s. -/
abbrev BaseWord (s : ℕ) := Σ n : Fin (s + 1), Fin n.val → Fin 4


-- @@ L34-34 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L36-38 verbatim
/-- The finite family of actual strong derivatives indexed by all base Sobolev words. -/
def baseWordValues {s : ℕ} {f : LiftL2 period} (J : SpatialJet period standardDirection s f) :
    BaseWord s → LiftL2 period := fun w => J.word w.2


-- @@ L40-46 verbatim
/-- The sigma-indexed family gives exactly the previously proved strong Sobolev sum norm. -/
theorem sum_baseWordValues_norm {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period standardDirection s f) :
    (∑ w : BaseWord s, ‖baseWordValues period J w‖) = J.sobolevNorm := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  simp only [baseWordValues, Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin 4, ‖J.word w‖) (s + 1)


-- @@ L48-51 verbatim
/-- The number of base derivative words depends only on the fixed Sobolev index. -/
theorem card_baseWord (s : ℕ) : Fintype.card (BaseWord s) = ∑ n ∈ Finset.range (s + 1), 4 ^ n := by
  simp only [BaseWord, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun n => 4 ^ n) (s + 1)


-- @@ L53-56 verbatim
/-- The source's root-of-sum metric energy for all base Sobolev words. -/
def baseWordMetricNorm {s : ℕ} {f : LiftL2 period} (K : LiftL2 period →L[ℝ] LiftL2 period)
    (J : SpatialJet period standardDirection s f) : ℝ := familyMetricNorm K (baseWordValues period
        J)


-- @@ L58-72 verbatim
/-- The Sobolev sum is controlled by its metric root with a fixed base-word cardinality constant. -/
theorem sobolevNorm_le_baseWordMetric {s : ℕ} {f : LiftL2 period}
    (K : LiftL2 period →L[ℝ] LiftL2 period) (J : SpatialJet period standardDirection s f)
    (c : ℝ) (hc : 0 < c)
    (hK : ∀ u, c ^ 2 * ‖u‖ ^ 2 ≤ ⟪K u, u⟫_ℝ) :
    J.sobolevNorm ≤ (Real.sqrt (Fintype.card (BaseWord s) : ℝ) / c) * baseWordMetricNorm period K J
        := by
  rw [← sum_baseWordValues_norm period J]
  have hsum := sum_norm_le_card_sqrt_familyNorm (baseWordValues period J)
  have hmet := familyMetricNorm_lower K (baseWordValues period J) c hc.le hK
  have hn : familyNorm (baseWordValues period J) ≤ baseWordMetricNorm period K J / c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [baseWordMetricNorm, mul_comm] using hmet
  have hh := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (Fintype.card (BaseWord s) : ℝ))
  exact hsum.trans (hh.trans_eq (by ring))


-- @@ L74-81 verbatim
/-- The metric root is controlled by the actual base Sobolev sum with no extra word-count factor. -/
theorem baseWordMetric_le_sobolevNorm {s : ℕ} {f : LiftL2 period}
    (K : LiftL2 period →L[ℝ] LiftL2 period) (J : SpatialJet period standardDirection s f) :
    baseWordMetricNorm period K J ≤ Real.sqrt ‖K‖ * J.sobolevNorm := by
  have h := familyMetricNorm_upper K (baseWordValues period J)
  have hn := familyNorm_le_sum_norm (baseWordValues period J)
  rw [sum_baseWordValues_norm period J] at hn
  exact h.trans (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))


-- @@ L83-83 verbatim
end EulerBaseWordMetric


-- @@ L85-85 verbatim
end

-- @@ L86-86 verbatim
end


-- @@ L88-88 verbatim
end


-- @@ L90-90 verbatim
@[expose] public section


-- @@ L92-92 verbatim
noncomputable section


-- @@ L94-94 verbatim
namespace EulerGevreyMetricComparison


-- @@ L96-100 verbatim
open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerJetProductBounds EulerPacketWeights
  EulerSobolevGevreyOperators EulerBaseWordMetric EulerFiniteMetricEnergy
      EulerWeightedCylinderEnergy

-- @@ L101-101 verbatim
open scoped Topology


-- @@ L103-103 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L105-106 verbatim
/-- All external derivative words through the selected cutoff. -/
abbrev ExternalWord (N : ℕ) := Σ n : Fin (N+1), Fin n.val → Fin 4


-- @@ L108-112 verbatim
/-- Literal base derivatives of each external word of an actual Sobolev field. -/
def energyValues {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (u : SobolevSpace period s) :
    ExternalWord N → BaseWord q → LiftL2 period := fun I =>
  baseWordValues period (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) I.2 (by
      have := I.1.isLt; omega))


-- @@ L114-123 verbatim
/-- Exact rewriting of a valid external Sobolev block as the actual base-word derivative sums. -/
theorem blockNorm_baseWords {s q n : ℕ} (u : SobolevSpace period s) (h : n + q ≤ s) :
    blockNorm period (toJet period u) q n =
      ∑ w : Fin n → Fin 4, (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w
          h).sobolevNorm := by
  rw [blockNorm_eq_word_sizes (toJet period u) h]
  apply Finset.sum_congr rfl
  intro w _
  exact sobolevSize_eq period (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w
      h)


-- @@ L125-134 verbatim
/-- The lower comparison at one external order uses only the fixed number of base Sobolev words. -/
theorem blockNorm_metric_lower {s q n : ℕ} (u : SobolevSpace period s) (h : n + q ≤ s)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K v, v⟫_ℝ) :
    blockNorm period (toJet period u) q n ≤
      (Real.sqrt (Fintype.card (BaseWord q) : ℝ)/c) *
        ∑ w : Fin n → Fin 4, baseWordMetricNorm period K
          (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w h) := by
  rw [blockNorm_baseWords period u h, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => sobolevNorm_le_baseWordMetric period K _ c hc hK


-- @@ L136-143 verbatim
/-- The upper metric comparison is independent of the external word count. -/
theorem blockNorm_metric_upper {s q n : ℕ} (u : SobolevSpace period s) (h : n + q ≤ s)
    (K : LiftL2 period →L[ℝ] LiftL2 period) :
    (∑ w : Fin n → Fin 4, baseWordMetricNorm period K
      (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet period u) w h)) ≤
      Real.sqrt ‖K‖ * blockNorm period (toJet period u) q n := by
  rw [blockNorm_baseWords period u h, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => baseWordMetric_le_sobolevNorm period K _


-- @@ L145-153 verbatim
/-- The metric-weighted energy is exactly the external-word sum of fixed-base metric roots. -/
theorem metricSum_eq {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) :
    weightedMetricSum ρ (fun I : ExternalWord N => I.1.val) K (energyValues period q N hN u) =
      ∑ n : Fin (N+1), weight ρ n.val * ∑ w : Fin n.val → Fin 4,
        baseWordMetricNorm period K (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet
            period u) w
          (by have := n.isLt; omega)) := by
  simp only [weightedMetricSum, Fintype.sum_sigma, Finset.mul_sum, energyValues, baseWordMetricNorm]


-- @@ L155-168 verbatim
/-- The actual weighted Sobolev sum is controlled by metric roots with no external-cutoff constant.
-/
theorem weightedNorm_metric_lower {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K v, v⟫_ℝ) :
    weightedNorm period q N ρ u ≤ (Real.sqrt (Fintype.card (BaseWord q) : ℝ)/c) *
      weightedMetricSum ρ (fun I : ExternalWord N => I.1.val) K (energyValues period q N hN u) := by
  rw [metricSum_eq, weightedNorm, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have h := mul_le_mul_of_nonneg_left (blockNorm_metric_lower period (q := q) (n := n.val) u (by
      have := n.isLt; omega) K c hc hK)
    (weight_pos hρ n.val).le
  exact h.trans_eq (by ring)


-- @@ L170-182 verbatim
/-- The actual metric weighted energy is bounded by its Sobolev counterpart without a cutoff factor.
-/
theorem weightedNorm_metric_upper {s : ℕ} (q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) :
    weightedMetricSum ρ (fun I : ExternalWord N => I.1.val) K (energyValues period q N hN u) ≤
      Real.sqrt ‖K‖ * weightedNorm period q N ρ u := by
  rw [metricSum_eq, weightedNorm, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have h := mul_le_mul_of_nonneg_left (blockNorm_metric_upper period (q := q) (n := n.val) u (by
      have := n.isLt; omega) K)
    (weight_pos hρ n.val).le
  exact h.trans_eq (by ring)


-- @@ L184-187 verbatim
/-- At the fixed base index six the comparison uses exactly 5461 base words. -/
theorem card_baseWord_six : Fintype.card (BaseWord 6) = 5461 := by
  rw [card_baseWord]
  norm_num [Finset.sum_range_succ]


-- @@ L189-189 verbatim
end EulerGevreyMetricComparison
