/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Kei Tsukamoto
-/
import StatsMLlib.LearningTheory.UniformDeviation.Bounds
import StatsMLlib.Probability.Concentration.Confidence


-- @@ L9-15 verbatim
/-!
# Confidence-parameter generalization bounds

This module turns the `ε`-tail bounds of
`StatsMLlib.LearningTheory.UniformDeviation.Bounds`, for both countable and
separable classes, into statements with failure probability `0 < δ ≤ 1`.
-/


-- @@ L17-17 verbatim
section


-- @@ L19-19 verbatim
universe u v w


-- @@ L21-21 verbatim
open MeasureTheory ProbabilityTheory Real TopologicalSpace

-- @@ L22-22 verbatim
open scoped ENNReal


-- @@ L24-24 verbatim
variable {n : ℕ}

-- @@ L25-25 verbatim
variable {Ω : Type u} [MeasurableSpace Ω] {H : Type v} {𝒳 : Type w}

-- @@ L26-26 verbatim
variable {μ : Measure Ω}


-- @@ L28-28 verbatim
local notation "μⁿ" => Measure.pi (fun _ ↦ μ)


-- @@ L30-38 verbatim
/--
Confidence radius for a tail estimate without an additional prefactor:

`deterministicConfidenceRadius b δ n =
  b * √(2 * log (1 / δ) / n)`.
-/
noncomputable def deterministicConfidenceRadius
    (b δ : ℝ) (n : ℕ) : ℝ :=
  confidenceRadius 1 b δ n


-- @@ L40-48 verbatim
/--
Confidence radius for a union bound with prefactor `2`:

`sampleConfidenceRadius b δ n =
  b * √(2 * log (2 / δ) / n)`.
-/
noncomputable def sampleConfidenceRadius
    (b δ : ℝ) (n : ℕ) : ℝ :=
  confidenceRadius 2 b δ n


-- @@ L50-53 verbatim
lemma deterministicConfidenceRadius_nonneg
    {b δ : ℝ} (hb : 0 ≤ b) :
    0 ≤ deterministicConfidenceRadius b δ n := by
  exact mul_nonneg hb (Real.sqrt_nonneg _)


-- @@ L55-58 verbatim
lemma sampleConfidenceRadius_nonneg
    {b δ : ℝ} (hb : 0 ≤ b) :
    0 ≤ sampleConfidenceRadius b δ n := by
  exact mul_nonneg hb (Real.sqrt_nonneg _)


-- @@ L60-67 verbatim
lemma exp_neg_deterministicConfidenceRadius_sq
    (hn : 0 < n) {b δ : ℝ}
    (hb : 0 < b) (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (-deterministicConfidenceRadius b δ n ^ 2 * n /
        (2 * b ^ 2)).exp = δ := by
  have h := mul_exp_neg_confidenceRadius_sq
    hn (κ := 1) (b := b) (δ := δ) zero_lt_one hb hδ hδ_one
  simpa [deterministicConfidenceRadius] using h


-- @@ L69-76 verbatim
lemma two_mul_exp_neg_sampleConfidenceRadius_sq
    (hn : 0 < n) {b δ : ℝ}
    (hb : 0 < b) (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    2 * (-sampleConfidenceRadius b δ n ^ 2 * n /
        (2 * b ^ 2)).exp = δ := by
  apply mul_exp_neg_confidenceRadius_sq
    hn (κ := 2) (b := b) (δ := δ) (by norm_num) hb hδ
  linarith


-- @@ L78-103 verbatim
/--
Countable-class confidence bound from an upper bound `C` on expected
Rademacher complexity:

`Pr{UDₙ ≥ 2 C + b √(2 log(1/δ)/n)} ≤ δ`.
-/
theorem uniform_deviation_tail_bound_countable_of_rademacher_le_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H] [Countable H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hC : rademacherComplexity n F μ X ≤ C)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C + deterministicConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  calc
    _ ≤ (-deterministicConfidenceRadius b δ n ^ 2 * n /
          (2 * b ^ 2)).exp :=
      uniform_deviation_tail_bound_countable_of_rademacher_le
        (μ := μ) F hF_meas X hX hb hF_bound hC
        (deterministicConfidenceRadius_nonneg hb.le)
    _ = δ :=
      exp_neg_deterministicConfidenceRadius_sq hn hb hδ hδ_one


-- @@ L105-124 verbatim
/--
Countable-class confidence bound from a uniform fixed-sample upper bound on
empirical Rademacher complexity.
-/
theorem uniform_deviation_tail_bound_countable_of_empirical_le_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H] [Countable H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C + deterministicConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  apply uniform_deviation_tail_bound_countable_of_rademacher_le_delta
    (μ := μ) hn F hF_meas X hX hb hF_bound _ hδ hδ_one
  exact rademacherComplexity_le_of_empirical_le_countable
    (fun h ↦ (hF_meas h).comp hX) hb.le hF_bound hC


-- @@ L126-151 verbatim
/--
Countable-class sample-dependent confidence bound:

`Pr{UDₙ ≥ 2 C(S) + 3 b √(2 log(2/δ)/n)} ≤ δ`.
-/
theorem uniform_deviation_tail_bound_countable_of_sample_empirical_le_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H] [Countable H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    (C : (Fin n → 𝒳) → ℝ)
    {b δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C S)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C (X ∘ S) + 3 * sampleConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  calc
    _ ≤ 2 * (-sampleConfidenceRadius b δ n ^ 2 * n /
          (2 * b ^ 2)).exp :=
      uniform_deviation_tail_bound_countable_of_sample_empirical_le
        (μ := μ) F hF_meas X hX C hb hF_bound hC
        (sampleConfidenceRadius_nonneg hb.le)
    _ = δ :=
      two_mul_exp_neg_sampleConfidenceRadius_sq hn hb hδ hδ_one


-- @@ L153-178 verbatim
/--
Separable-class confidence bound from an upper bound `C` on expected
Rademacher complexity.
-/
theorem uniform_deviation_tail_bound_separable_of_rademacher_le_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : rademacherComplexity n F μ X ≤ C)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C + deterministicConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  calc
    _ ≤ (-deterministicConfidenceRadius b δ n ^ 2 * n /
          (2 * b ^ 2)).exp :=
      uniform_deviation_tail_bound_separable_of_rademacher_le
        (μ := μ) F hF_meas X hX hb hF_bound hF_cont hC
        (deterministicConfidenceRadius_nonneg hb.le)
    _ = δ :=
      exp_neg_deterministicConfidenceRadius_sq hn hb hδ hδ_one


-- @@ L180-206 verbatim
/--
Confidence-parameter form of the deterministic-threshold separable-class
generalization bound.

The displayed radius unfolds to
`b * √(2 * log (1 / δ) / n)`.
-/
theorem uniform_deviation_tail_bound_separable_of_empirical_le_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C + b * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  simpa [deterministicConfidenceRadius, confidenceRadius] using
    uniform_deviation_tail_bound_separable_of_rademacher_le_delta
      (μ := μ) hn F hF_meas X hX hb hF_bound hF_cont
      (rademacherComplexity_le_of_empirical_le_separable
        F X (fun h ↦ (hF_meas h).comp hX) hb.le hF_bound hF_cont hC)
      hδ hδ_one


-- @@ L208-243 verbatim
/--
Confidence-parameter form of the sample-dependent separable-class
generalization bound.

The concentration radius unfolds to
`b * √(2 * log (2 / δ) / n)` because the proof uses a union bound.
-/
theorem uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    (C : (Fin n → 𝒳) → ℝ)
    {b δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C S)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C (X ∘ S) +
          3 * (b * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  have htail :=
    uniform_deviation_tail_bound_separable_of_sample_empirical_le
      (μ := μ) F hF_meas X hX C hb hF_bound hF_cont hC
      (sampleConfidenceRadius_nonneg (n := n) (δ := δ) hb.le)
  calc
    _ = (μⁿ {S : Fin n → Ω |
        2 * C (X ∘ S) + 3 * sampleConfidenceRadius b δ n ≤
          uniformDeviation n F μ X (X ∘ S)}).toReal := by
      simp only [sampleConfidenceRadius, confidenceRadius]
    _ ≤ 2 * (-sampleConfidenceRadius b δ n ^ 2 * n /
          (2 * b ^ 2)).exp := htail
    _ = δ :=
      two_mul_exp_neg_sampleConfidenceRadius_sq hn hb hδ hδ_one



-- @@ L246-250 verbatim
/-! ## Examples

Worked uses of this module's public API. They are elaborated with the library, so they
double as acceptance tests that these statements stay usable as written.
-/


-- @@ L252-267 verbatim
example
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hn : 0 < n)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C + b * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  exact uniform_deviation_tail_bound_separable_of_empirical_le_delta
    (μ := μ) hn F hF_meas X hX hb hF_bound hF_cont hC hδ hδ_one


-- @@ L269-269 verbatim
end
