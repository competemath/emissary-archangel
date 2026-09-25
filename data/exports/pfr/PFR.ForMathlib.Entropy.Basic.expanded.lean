module

public import PFR.ForMathlib.ConditionalIndependence
public import PFR.ForMathlib.Entropy.Kernel.MutualInfo
public import PFR.ForMathlib.Uniform
public import PFR.Mathlib.Probability.ConditionalProbability


-- @@ L8-35 verbatim
/-!
# Entropy and conditional entropy

## Main definitions

* `entropy`: entropy of a random variable, defined as `measureEntropy (volume.map X)`
* `condEntropy`: conditional entropy of a random variable `X` w.r.t. another one `Y`
* `mutualInfo`: mutual information of two random variables

## Main statements

* `chain_rule`: $H[⟨X, Y⟩] = H[Y] + H[X | Y]$
* `entropy_cond_le_entropy`: $H[X | Y] ≤ H[X]$. (Chain rule another way.)
* `entropy_triple_add_entropy_le` (Submodularity of entropy.) :
  $H[X, Y, Z] + H[Z] ≤ H[X, Z] + H[Y, Z]$.

## Notations

* `H[X] = entropy X`
* `H[X | Y ← y] = Hm[(ℙ[|Y ← y]).map X]`
* `H[X | Y] = condEntropy X Y`, such that `H[X | Y] = (volume.map Y)[fun y ↦ H[X | Y ← y]]`
* `I[X : Y] = mutualInfo X Y`

All notations have variants where we can specify the measure (which is otherwise
supposed to be `volume`). For example `H[X ; μ]` and `I[X : Y ; μ]` instead of `H[X]` and
`I[X : Y]` respectively.

-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
open Function MeasureTheory Measure Real

-- @@ L40-40 verbatim
open scoped ENNReal NNReal Topology ProbabilityTheory


-- @@ L42-42 verbatim
namespace ProbabilityTheory

-- @@ L43-44 verbatim
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}


-- @@ L46-46 verbatim
section entropy


-- @@ L48-50 expanded
/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) :=
  measureEntropy (μ.map X)


-- @@ L52-52 verbatim
@[inherit_doc entropy] notation3:max "H[" X "; " μ "]" => entropy X μ

-- @@ L53-53 verbatim
@[inherit_doc entropy] notation3:max "H[" X "]" => entropy X volume

-- @@ L54-54 verbatim
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "; " μ "]" => entropy X (μ[|Y ← y])

-- @@ L55-55 verbatim
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "]" => entropy X (ℙ[|Y ← y])


-- @@ L57-58 expanded
/-- Entropy of a random variable agrees with entropy of its distribution. -/
lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = measureEntropy (μ.map X) :=
  rfl


-- @@ L60-63 expanded
/-- Entropy of a random variable is also the kernel entropy of the distribution over a Dirac mass.
-/
lemma entropy_eq_kernel_entropy (X : Ω → S) (μ : Measure Ω) :
    entropy X μ =
      ProbabilityTheory.Kernel.entropy (Kernel.const Unit (μ.map X)) (Measure.dirac ()) :=
  by simp [entropy]


-- @@ L65-67 expanded
/-- Any variable on a zero measure space has zero entropy. -/
@[simp]
lemma entropy_zero_measure (X : Ω → S) : entropy X (0 : Measure Ω) = 0 := by simp [entropy]


-- @@ L69-71 expanded
/-- Two variables that agree almost everywhere, have the same entropy. -/
lemma entropy_congr {X X' : Ω → S} (h : X =ᵐ[μ] X') : entropy X μ = entropy X' μ := by
  rw [entropy_def, Measure.map_congr h, entropy_def]


-- @@ L73-74 verbatim
/-- Entropy is always non-negative. -/
lemma entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ entropy X μ := measureEntropy_nonneg _


-- @@ L76-79 expanded
/-- Two variables that have the same distribution, have the same entropy. -/
lemma IdentDistrib.entropy_congr {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {X' : Ω' → S}
    (h : IdentDistrib X X' μ μ') : entropy X μ = entropy X' μ' := by simp [entropy_def, h.map_eq]


-- @@ L81-84 expanded
/-- Entropy is at most the logarithm of the cardinality of the range. -/
lemma entropy_le_log_card [Fintype S] [MeasurableSingletonClass S] (X : Ω → S) (μ : Measure Ω) :
    entropy X μ ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _


-- @@ L86-92 expanded
/-- Entropy is at most the logarithm of the cardinality of a set in which X almost surely takes
values in. -/
lemma entropy_le_log_card_of_mem [DiscreteMeasurableSpace S] {A : Finset S} {μ : Measure Ω}
    {X : Ω → S} (hX : Measurable X) (h : ∀ᵐ ω ∂μ, X ω ∈ A) : entropy X μ ≤ log A.card :=
  measureEntropy_le_log_card_of_mem _ <| by rwa [Measure.map_apply hX .of_discrete]


-- @@ L94-101 expanded
/-- Entropy is at most the logarithm of the cardinality of a set in which X almost surely takes
values in. -/
lemma entropy_le_log_card_of_mem_finite [DiscreteMeasurableSpace S] {A : Set S} {μ : Measure Ω}
    {X : Ω → S} (hA : A.Finite) (hX : Measurable X) (h : ∀ᵐ ω ∂μ, X ω ∈ A) :
    entropy X μ ≤ log (Nat.card A) :=
  by
  lift A to Finset S using hA
  simpa using entropy_le_log_card_of_mem (A := A) hX (μ := μ) (by simpa)


-- @@ L103-106 verbatim
/-- `H[X] = ∑ₛ P[X=s] log 1 / P[X=s]`. -/
lemma entropy_eq_sum (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] :
    entropy X μ = ∑' x, negMulLog ((μ.map X).real {x}) := by
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]


-- @@ L108-110 verbatim
lemma entropy_eq_sum' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] :
    entropy X μ = ∑' x, negMulLog ((μ.map X).real {x}) := by
  simp only [entropy_def, measureEntropy_of_isProbabilityMeasure, Measure.real]


-- @@ L112-123 verbatim
lemma entropy_eq_sum_finset {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {A : Finset S} (hA : (μ.map X) Aᶜ = 0) :
    entropy X μ = ∑ x ∈ A, negMulLog ((μ.map X).real {x}) := by
  rw [entropy_eq_sum]
  convert tsum_eq_sum ?_
  · exact SummationFilter.instLeAtTopUnconditional S
  intro s hs
  convert negMulLog_zero
  rw [Measure.real]
  convert ENNReal.toReal_zero
  convert measure_mono_null ?_ hA
  simp [hs]


-- @@ L125-128 verbatim
lemma entropy_eq_sum_finset' {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {A : Finset S} (hA : (μ.map X) Aᶜ = 0) :
    entropy X μ = ∑ x ∈ A, negMulLog ((μ.map X).real {x}) :=
  entropy_eq_sum_finset hA


-- @@ L130-133 verbatim
lemma entropy_eq_sum_finiteRange [MeasurableSingletonClass S]
    (hX : Measurable X) {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] [FiniteRange X] :
    entropy X μ = ∑ x ∈ FiniteRange.toFinset X, negMulLog ((μ.map X).real {x}) :=
  entropy_eq_sum_finset (A := FiniteRange.toFinset X) (full_measure_of_finiteRange hX)


-- @@ L135-138 verbatim
lemma entropy_eq_sum_finiteRange' [MeasurableSingletonClass S] (hX : Measurable X) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] :
    entropy X μ = ∑ x ∈ FiniteRange.toFinset X, negMulLog ((μ.map X).real {x}) :=
  entropy_eq_sum_finiteRange hX


-- @@ L140-146 expanded
/-- `H[X | Y=y] = ∑_s P[X=s | Y=y] log 1/(P[X=s | Y=y])`. -/
lemma entropy_cond_eq_sum (μ : Measure Ω) (y : T) :
    entropy X (μ[|Y ← y]) = ∑' x, negMulLog (((μ[|Y ← y]).map X).real { x }) :=
  by
  by_cases hy : μ (Y ⁻¹' { y }) = 0
  · rw [entropy_def, cond_eq_zero_of_meas_eq_zero hy]
    simp
  · rw [entropy_eq_sum]


-- @@ L148-154 expanded
lemma entropy_cond_eq_sum_finiteRange [MeasurableSingletonClass S] (hX : Measurable X)
    (μ : Measure Ω) (y : T) [FiniteRange X] :
    entropy X (μ[|Y ← y]) =
      ∑ x ∈ FiniteRange.toFinset X, negMulLog (((μ[|Y ← y]).map X).real { x }) :=
  by
  by_cases hy : μ (Y ⁻¹' { y }) = 0
  · rw [entropy_def, cond_eq_zero_of_meas_eq_zero hy]
    simp
  · rw [entropy_eq_sum_finiteRange hX]


-- @@ L156-166 expanded
/-- If `X`, `Y` are `S`-valued and `T`-valued random variables, and `Y = f(X)` for
some injection `f : S \to T`, then `H[Y] = H[X]`.
One can also use `entropy_of_comp_eq_of_comp` as an alternative if verifying injectivity is fiddly.
For the upper bound only, see `entropy_comp_le`. -/
lemma entropy_comp_of_injective [MeasurableSpace T] [Countable S] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] (μ : Measure Ω) (hX : Measurable X) (f : S → T)
    (hf : Function.Injective f) : entropy (f ∘ X) μ = entropy X μ :=
  by
  have hf_m : Measurable f := .of_discrete
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf_m hf,
    entropy_def]


-- @@ L168-172 expanded
/-- The entropy of any constant is zero. -/
@[simp]
lemma entropy_const [MeasurableSingletonClass S] [IsZeroOrProbabilityMeasure μ] (c : S) :
    entropy (fun _ ↦ c) μ = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ <;> simp [entropy, Measure.map_const]


-- @@ L174-174 verbatim
open Set


-- @@ L176-176 verbatim
open Function


-- @@ L178-190 expanded
/-- If `X` is uniformly distributed on `H`, then `H[X] = log |H|`. -/
lemma IsUniform.entropy_eq [DiscreteMeasurableSpace S] {H : Finset S} {X : Ω → S} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : IsUniform H X μ) (hX' : Measurable X) :
    entropy X μ = log (Nat.card H) :=
  by
  have (t : S) : negMulLog ((μ.map X).real { t }) = (μ.map X).real { t } * log (Nat.card H) :=
    by
    by_cases ht : t ∈ H
    · simp [negMulLog, IsUniform.measureReal_preimage_of_mem' hX hX' ht]
    · simp [negMulLog, map_measureReal_apply hX' (.singleton t), hX.measureReal_preimage_of_nmem ht]
  rw [entropy_eq_sum_finset' (A := H), Finset.sum_congr rfl (fun t _ ↦ this t), ← Finset.sum_mul,
    sum_measureReal_singleton]
  · simp [Measure.real, IsUniform.full_measure hX hX']
  rw [Measure.map_apply hX' (by measurability)]
  exact hX.measure_preimage_compl


-- @@ L192-197 expanded
/-- Variant of `IsUniform.entropy_congr` where `H` is a finite `Set` rather than `Finset`. -/
lemma IsUniform.entropy_eq' [DiscreteMeasurableSpace S] {A : Set S} (hA : A.Finite) {X : Ω → S}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : IsUniform A X μ) (hX' : Measurable X) :
    entropy X μ = log A.ncard :=
  by
  have : IsUniform hA.toFinset X μ := by simpa using hX
  simpa using this.entropy_eq hX'


-- @@ L199-211 verbatim
/-- If `X` is `S`-valued random variable, then `H[X] = log |S|` if and only if `X` is uniformly
distributed. -/
lemma entropy_eq_log_card {X : Ω → S} [Fintype S] [MeasurableSingletonClass S]
    (hX : Measurable X) (μ : Measure Ω) [hμ : NeZero μ]
    [IsFiniteMeasure μ] :
    entropy X μ = log (Fintype.card S) ↔ ∀ s, μ.map X {s} = μ Set.univ / Fintype.card S := by
  rcases eq_zero_or_neZero (μ.map X) with h | h
  · have := Measure.le_map_apply (@Measurable.aemeasurable Ω S _ _ X μ hX) Set.univ
    simp [h] at this; simp [this] at hμ
  have : IsFiniteMeasure (μ.map X) := by
    apply Measure.isFiniteMeasure_map
  rw [entropy_def, measureEntropy_eq_card_iff_measure_eq, Measure.map_apply hX MeasurableSet.univ]
  simp


-- @@ L213-298 expanded
/-- If `X` is an `S`-valued random variable, then there exists `s ∈ S` such that
`P[X = s] ≥ \exp(- H[X])`. -/
lemma prob_ge_exp_neg_entropy [MeasurableSingletonClass S] [Nonempty S] (X : Ω → S) (μ : Measure Ω)
    (hX : Measurable X) [hX' : FiniteRange X] :
    ∃ s : S, μ Set.univ * (rexp (-entropy X μ)).toNNReal ≤ μ.map X { s } :=
  by
  let μS := μ.map X
  let μs s := μS { s }
  rcases finiteSupport_of_finiteRange (X := X) with ⟨A, hA⟩
  let S_nonzero := A.filter (fun s ↦ μs s ≠ 0)
  set norm := μS A with rw_norm
  have h_norm : norm = μ Set.univ :=
    by
    have := measure_add_measure_compl (μ := μS) (s := A) (Finset.measurableSet _)
    change μS (A : Set S)ᶜ = 0 at hA
    rw [hA, add_zero] at this
    simp [norm, μS, this, Measure.map_apply hX MeasurableSet.univ]
  let pdf_nn s := norm⁻¹ * μs s
  let pdf s := (pdf_nn s).toReal
  let neg_log_pdf s := -log (pdf s)
  rcases Finset.eq_empty_or_nonempty S_nonzero with h_empty | h_nonempty
  · have h_norm_zero : μ Set.univ = 0 :=
      by
      have h : ∀ s ∈ A, μs s ≠ 0 → μs s ≠ 0 := fun _ _ h ↦ h
      rw [← h_norm, rw_norm, ← sum_measure_singleton, ← Finset.sum_filter_of_ne h,
        show Finset.filter _ _ = S_nonzero from rfl, h_empty, show Finset.sum ∅ μs = 0 from rfl]
    use Classical.arbitrary (α := S)
    simp [h_norm_zero]
  rcases exists_or_forall_not (fun s ↦ μ.map X { s } = ∞) with h_infty | h_finite
  · obtain ⟨s, h_s⟩ := h_infty
    use s; rw [h_s]; exact le_top
  rcases eq_zero_or_neZero μ with h_zero_measure | _
  · use Classical.arbitrary (α := S)
    rw [h_zero_measure, show (0 : Measure Ω) _ = 0 from rfl, zero_mul]
    exact zero_le
  have h_norm_pos : 0 < norm := by
    rw [h_norm, Measure.measure_univ_pos]
    exact NeZero.ne μ
  have h_norm_finite : norm < ∞ :=
    by
    rw [rw_norm, ← sum_measure_singleton]
    exact ENNReal.sum_lt_top.2 (fun s _ ↦ Ne.lt_top (h_finite s))
  have h_invinvnorm_finite : norm⁻¹⁻¹ ≠ ∞ :=
    by
    rw [inv_inv]
    exact LT.lt.ne_top h_norm_finite
  have h_invnorm_ne_zero : norm⁻¹ ≠ 0 := ENNReal.inv_ne_top.mp h_invinvnorm_finite
  have h_invnorm_finite : norm⁻¹ ≠ ∞ :=
    by
    rw [← ENNReal.inv_ne_zero, inv_inv]
    exact h_norm_pos.ne'
  have h_pdf_finite : ∀ s, pdf_nn s ≠ ∞ := fun s ↦ ENNReal.mul_ne_top h_invnorm_finite (h_finite s)
  have h_norm_cancel : norm * norm⁻¹ = 1 := ENNReal.mul_inv_cancel h_norm_pos.ne' h_norm_finite.ne
  have h_pdf1 : (∑ s ∈ A, pdf s) = 1 := by
    rw [← ENNReal.toReal_sum (fun s _ ↦ h_pdf_finite s), ← Finset.mul_sum, sum_measure_singleton,
      mul_comm, h_norm_cancel, ENNReal.toReal_one]
  let ⟨s_max, hs, h_min⟩ := Finset.exists_min_image S_nonzero neg_log_pdf h_nonempty
  have h_pdf_s_max_pos : 0 < pdf s_max :=
    by
    rw [Finset.mem_filter] at hs
    have h_nonzero : pdf s_max ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr
        ⟨mul_ne_zero h_invnorm_ne_zero hs.2, ENNReal.mul_ne_top h_invnorm_finite (h_finite s_max)⟩
    exact LE.le.lt_of_ne ENNReal.toReal_nonneg h_nonzero.symm
  use s_max
  rw [← h_norm, ← one_mul (μ.map X _), ← h_norm_cancel, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt h_norm_pos)
  change ENNReal.ofReal (rexp (-entropy X μ)) ≤ pdf_nn s_max
  rw [ENNReal.ofReal_le_iff_le_toReal (h_pdf_finite _), show (pdf_nn _).toReal = pdf _ from rfl, ←
    Real.exp_log h_pdf_s_max_pos]
  apply exp_monotone
  rw [neg_le, ← one_mul (-log _), ← h_pdf1, Finset.sum_mul]
  let g_lhs s := pdf s * neg_log_pdf s_max
  let g_rhs s := -pdf s * log (pdf s)
  suffices ∑ s ∈ A, g_lhs s ≤ ∑ s ∈ A, g_rhs s
    by
    have hA0 : μ.map X (A : Set S)ᶜ = 0 := ae_iff.mp hA
    convert! this
    rw [entropy_def, measureEntropy_eq_sum hA0]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hsmul : (((μ.map X) Set.univ)⁻¹ • μ.map X).real { s } = pdf s :=
      by
      have huniv : (μ.map X) Set.univ = norm :=
        by
        rw [Measure.map_apply hX MeasurableSet.univ]
        exact h_norm.symm
      simp [pdf, pdf_nn, μs, μS, Measure.real, huniv]
    simp [g_rhs, hsmul, negMulLog]
  have h_lhs : ∀ s, μs s = 0 → g_lhs s = 0 := by { intros _ h; simp [g_lhs, pdf, pdf_nn, h]
  }
  have h_rhs : ∀ s, μs s = 0 → g_rhs s = 0 := by { intros _ h; simp [g_rhs, pdf, pdf_nn, h]
  }
  rw [← Finset.sum_filter_of_ne (fun s _ ↦ (h_lhs s).mt), ←
    Finset.sum_filter_of_ne (fun s _ ↦ (h_rhs s).mt)]
  apply Finset.sum_le_sum
  intros s h_s
  rw [show g_lhs s = _ * _ from rfl, show g_rhs s = _ * _ from rfl, neg_mul_comm]
  exact mul_le_mul_of_nonneg_left (h_min s h_s) ENNReal.toReal_nonneg


-- @@ L300-312 expanded
/-- If `X` is an `S`-valued random variable, then there exists `s ∈ S` such that
`P[X=s] ≥ \exp(-H[X])`. -/
lemma prob_ge_exp_neg_entropy' [MeasurableSingletonClass S] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X) [FiniteRange X] :
    ∃ s : S, rexp (-entropy X μ) ≤ μ.real (X ⁻¹' { s }) :=
  by
  have : Nonempty S := (Measure.nonempty_of_neZero μ).map X
  obtain ⟨s, hs⟩ := prob_ge_exp_neg_entropy X μ hX
  use s
  rwa [IsProbabilityMeasure.measure_univ, one_mul,
    (show ENNReal.ofNNReal _ = ENNReal.ofReal _ from rfl),
    ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _), ← Measure.real,
    map_measureReal_apply hX (MeasurableSet.singleton s)] at hs


-- @@ L314-326 expanded
/-- If `X` is an `S`-valued random variable of non-positive entropy, then `X` is almost surely
constant. -/
lemma const_of_nonpos_entropy [MeasurableSingletonClass S] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → S} (hX : Measurable X) [FiniteRange X]
    (hent : entropy X μ ≤ 0) : ∃ s : S, μ.real (X ⁻¹' { s }) = 1 :=
  by
  rcases prob_ge_exp_neg_entropy' (μ := μ) X hX with ⟨s, hs⟩
  use s
  apply LE.le.antisymm
  · rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (subset_univ _) (by finiteness)
  refine le_trans ?_ hs
  simp [hent]


-- @@ L328-330 verbatim
variable [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]


-- @@ L332-335 expanded
/-- `H[X, f(X)] = H[X]`. -/
@[simp]
lemma entropy_prod_comp (hX : Measurable X) (μ : Measure Ω) (f : S → T) :
    entropy ⟨X, f ∘ X⟩ μ = entropy X μ :=
  entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) fun _ _ ab ↦ (Prod.ext_iff.1 ab).1


-- @@ L337-337 verbatim
variable [Countable T]


-- @@ L339-343 expanded
/-- `H[X, Y] = H[Y, X]`. -/
lemma entropy_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, Y⟩ μ = entropy ⟨Y, X⟩ μ :=
  by
  change entropy (Prod.swap ∘ ⟨Y, X⟩) μ = entropy ⟨Y, X⟩ μ
  exact entropy_comp_of_injective μ (hY.prodMk hX) Prod.swap Prod.swap_injective


-- @@ L345-349 expanded
/-- `H[(X, Y), Z] = H[X, (Y, Z)]`. -/
lemma entropy_assoc (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    entropy ⟨X, ⟨Y, Z⟩⟩ μ = entropy ⟨⟨X, Y⟩, Z⟩ μ :=
  by
  change entropy (MeasurableEquiv.prodAssoc ∘ ⟨⟨X, Y⟩, Z⟩) μ = entropy ⟨⟨X, Y⟩, Z⟩ μ
  exact entropy_comp_of_injective μ ((hX.prodMk hY).prodMk hZ) _ <| Equiv.injective _


-- @@ L351-351 verbatim
end entropy


-- @@ L353-353 verbatim
section condEntropy


-- @@ L355-355 verbatim
variable [MeasurableSpace T]


-- @@ L357-357 verbatim
variable {X : Ω → S} {Y : Ω → T}


-- @@ L359-364 expanded
/-- Conditional entropy of a random variable w.r.t. another.
This is the expectation under the law of `Y` of the entropy of the law of `X` conditioned on the
event `Y = y`. -/
noncomputable def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ entropy X (μ[|Y ← y])]


-- @@ L366-367 expanded
lemma condEntropy_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    condEntropy X Y μ = (μ.map Y)[fun y ↦ entropy X (μ[|Y ← y])] :=
  rfl


-- @@ L369-369 verbatim
@[inherit_doc condEntropy] notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ

-- @@ L370-370 verbatim
@[inherit_doc condEntropy] notation3:max "H[" X " | " Y "]" => condEntropy X Y volume


-- @@ L372-372 verbatim
section


-- @@ L374-374 verbatim
variable [MeasurableSingletonClass T]


-- @@ L376-382 expanded
lemma condEntropy_eq_zero (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] (t : T)
    (ht : (μ.map Y).real { t } = 0) : entropy X (μ[|Y ← t]) = 0 :=
  by
  convert entropy_zero_measure X
  apply cond_eq_zero_of_meas_eq_zero
  rw [map_measureReal_apply hY (.singleton t)] at ht
  rw [← measureReal_eq_zero_iff]
  exact ht


-- @@ L384-396 expanded
/-- Conditional entropy of a random variable is equal to the entropy of its conditional kernel. -/
lemma condEntropy_eq_kernel_entropy [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] [FiniteRange Y] :
    condEntropy X Y μ = ProbabilityTheory.Kernel.entropy (condDistrib X Y μ) (μ.map Y) :=
  by
  rw [condEntropy_def, Kernel.entropy]
  apply integral_congr_finiteSupport
  intro t ht
  rw [Measure.map_apply hY (.singleton _)] at ht
  simp only [entropy_def]
  congr
  ext s hs
  rw [condDistrib_apply' hX hY _ _ ht hs, Measure.map_apply hX hs, cond_apply (hY (.singleton _))]


-- @@ L398-399 verbatim
variable [Countable T] [Nonempty T] [Nonempty S] [MeasurableSingletonClass S] [Countable S]
  [Countable U] [MeasurableSingletonClass U]


-- @@ L401-412 expanded
lemma condEntropy_two_eq_kernel_entropy (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange Y] [FiniteRange Z] :
    condEntropy X ⟨Y, Z⟩ μ =
      ProbabilityTheory.Kernel.entropy (Kernel.condKernel (condDistrib (fun a ↦ (Y a, X a)) Z μ))
        (Measure.map Z μ ⊗ₘ Kernel.fst (condDistrib (fun a ↦ (Y a, X a)) Z μ)) :=
  by
  rw [Measure.compProd_congr (condDistrib_fst_ae_eq hY hX hZ μ), map_compProd_condDistrib hY hZ,
    Kernel.entropy_congr (condKernel_condDistrib_ae_eq hY hX hZ μ), ←
    Kernel.entropy_congr (swap_condDistrib_ae_eq hY hX hZ μ)]
  have : μ.map (fun ω ↦ (Z ω, Y ω)) = (μ.map (fun ω ↦ (Y ω, Z ω))).comap Prod.swap := by
    rw [map_prod_comap_swap hY hZ]
  rw [this, condEntropy_eq_kernel_entropy hX (hY.prodMk hZ), Kernel.entropy_comap_swap]


-- @@ L414-414 verbatim
end


-- @@ L416-419 expanded
/-- Any random variable on a zero measure space has zero conditional entropy. -/
@[simp]
lemma condEntropy_zero_measure (X : Ω → S) (Y : Ω → T) : condEntropy X Y (0 : Measure Ω) = 0 := by
  simp [condEntropy]


-- @@ L421-423 expanded
/-- Conditional entropy is non-negative. -/
lemma condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ condEntropy X Y μ :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)


-- @@ L425-432 expanded
/-- Conditional entropy is at most the logarithm of the cardinality of the range. -/
lemma condEntropy_le_log_card [MeasurableSingletonClass S] [Fintype S] (X : Ω → S) (Y : Ω → T)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : condEntropy X Y μ ≤ log (Fintype.card S) :=
  by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ entropy_nonneg _ _)
  · exact ae_of_all _ (fun _ ↦ entropy_le_log_card _ _)
  · simp


-- @@ L434-440 expanded
/-- `H[X|Y] = ∑_y P[Y=y] H[X|Y=y]`. -/
lemma condEntropy_eq_sum [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] (hY : Measurable Y) [FiniteRange Y] :
    condEntropy X Y μ =
      ∑ y ∈ FiniteRange.toFinset Y, ((μ.map Y).real { y }) * entropy X (μ[|Y ← y]) :=
  by
  rw [condEntropy_def, integral_eq_setIntegral (ae_mem_of_finiteRange hY),
    setIntegral_finset _ .finset]
  simp_rw [smul_eq_mul]


-- @@ L442-448 expanded
/-- `H[X|Y] = ∑_y P[Y=y] H[X|Y=y]`. -/
lemma condEntropy_eq_sum_fintype [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hY : Measurable Y) [Fintype T] :
    condEntropy X Y μ = ∑ y, μ.real (Y ⁻¹' { y }) * entropy X (μ[|Y ← y]) :=
  by
  rw [condEntropy_def, integral_fintype .of_finite]
  simp_rw [smul_eq_mul, map_measureReal_apply hY (.singleton _)]


-- @@ L450-450 verbatim
variable [MeasurableSingletonClass T]


-- @@ L452-471 expanded
lemma condEntropy_prod_eq_sum {X : Ω → S} {Y : Ω → T} {Z : Ω → T'} [MeasurableSpace T']
    [MeasurableSingletonClass T'] (μ : Measure Ω) (hY : Measurable Y) (hZ : Measurable Z)
    [IsFiniteMeasure μ] [Finite T] [Fintype T'] :
    condEntropy X ⟨Y, Z⟩ μ = ∑ z, μ.real (Z ⁻¹' { z }) * condEntropy X Y μ[|Z ⁻¹' { z }] :=
  by
  cases nonempty_fintype T
  simp_rw [condEntropy_eq_sum_fintype _ _ _ (hY.prodMk hZ), condEntropy_eq_sum_fintype _ _ _ hY,
    Fintype.sum_prod_type_right, Finset.mul_sum, ← mul_assoc]
  congr with y
  congr with x
  have A : (fun a ↦ (Y a, Z a)) ⁻¹' {(x, y)} = Z ⁻¹' { y } ∩ Y ⁻¹' { x } := by ext p;
    simp [and_comm]
  congr 2
  · rw [cond_real_apply (hZ (.singleton y)), A]
    obtain hy | hy := eq_or_ne (μ.real (Z ⁻¹' { y })) 0
    · have : μ.real (Z ⁻¹' { y } ∩ Y ⁻¹' { x }) = 0 :=
        measureReal_mono_null Set.inter_subset_left hy (by finiteness)
      simp [this, hy]
    · rw [mul_inv_cancel_left₀ hy]
  · rw [A, cond_cond_eq_cond_inter (hZ (.singleton y)) (hY (.singleton x))]


-- @@ L473-473 verbatim
variable [MeasurableSingletonClass S]


-- @@ L475-483 expanded
/-- `H[X|Y] = ∑_y ∑_x P[Y=y] P[X=x|Y=y] log ⧸(P[X=x|Y=y])`$. -/
lemma condEntropy_eq_sum_sum (hX : Measurable X) {Y : Ω → T} (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    condEntropy X Y μ =
      ∑ y ∈ FiniteRange.toFinset Y,
        ∑ x ∈ FiniteRange.toFinset X,
          ((μ.map Y).real { y }) * negMulLog (((μ[|Y ← y]).map X).real { x }) :=
  by
  rw [condEntropy_eq_sum _ _ _ hY]
  congr with y
  rw [entropy_cond_eq_sum_finiteRange hX, Finset.mul_sum]


-- @@ L485-492 expanded
omit [MeasurableSingletonClass S] in
/-- `H[X|Y] = ∑_y ∑_x P[Y=y] P[X=x|Y=y] log ⧸(P[X=x|Y=y])`$. -/
lemma condEntropy_eq_sum_sum_fintype {Y : Ω → T} (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [Fintype S] [Fintype T] :
    condEntropy X Y μ =
      ∑ y, ∑ x, (μ.map Y).real { y } * negMulLog (((μ[|Y ← y]).map X).real { x }) :=
  by
  rw [condEntropy_eq_sum_fintype _ _ _ hY]
  congr with y
  rw [entropy_cond_eq_sum, tsum_fintype, Finset.mul_sum, map_measureReal_apply hY (.singleton _)]


-- @@ L494-500 expanded
/-- Same as previous lemma, but with a sum over a product space rather than a double sum. -/
lemma condEntropy_eq_sum_prod (hX : Measurable X) {Y : Ω → T} (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    condEntropy X Y μ =
      ∑ p ∈ (FiniteRange.toFinset X) ×ˢ (FiniteRange.toFinset Y),
        (μ.map Y).real { p.2 } * negMulLog (((μ[|Y ⁻¹' { p.2 }]).map X).real { p.1 }) :=
  by rw [condEntropy_eq_sum_sum hX hY, Finset.sum_product_right]


-- @@ L502-502 verbatim
variable [Countable S]


-- @@ L504-524 expanded
/-- If `X : Ω → S`, `Y : Ω → T` are random variables, and `f : T × S → U` is
  injective for each fixed `t ∈ T`, then `H[f(Y, X) | Y] = H[X | Y]`.
  Thus for instance `H[X-Y|Y] = H[X|Y]`. -/
lemma condEntropy_of_injective [MeasurableSingletonClass U] (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (f : T → S → U) (hf : ∀ t, Injective (f t))
    [FiniteRange Y] : condEntropy (fun ω ↦ f (Y ω) (X ω)) Y μ = condEntropy X Y μ :=
  by
  rw [condEntropy_eq_sum _ _ _ hY, condEntropy_eq_sum _ _ _ hY]
  have : ∀ y, entropy (fun ω ↦ f (Y ω) (X ω)) (μ[|Y ← y]) = entropy (f y ∘ X) (μ[|Y ← y]) :=
    by
    intro y
    refine entropy_congr ?_
    have : ∀ᵐ ω ∂μ[|Y ← y], Y ω = y :=
      by
      rw [ae_iff, cond_apply (hY (.singleton _))]
      have : {a | ¬Y a = y} = (Y ⁻¹' { y })ᶜ := by ext; simp
      rw [this, Set.inter_compl_self, measure_empty, mul_zero]
    filter_upwards [this] with ω hω
    rw [hω]
    simp
  simp_rw [this]
  congr with y
  rw [entropy_comp_of_injective _ hX (f y) (hf y)]


-- @@ L526-530 expanded
/-- A weaker version of the above lemma in which `f` is independent of `Y`. -/
lemma condEntropy_comp_of_injective {Y : Ω → U} (μ : Measure Ω) (hX : Measurable X) (f : S → T)
    (hf : Injective f) : condEntropy (f ∘ X) Y μ = condEntropy X Y μ :=
  integral_congr_ae (ae_of_all _ (fun _ ↦ entropy_comp_of_injective _ hX f hf))


-- @@ L532-537 expanded
/-- `H[X, Y| Z] = H[Y, X| Z]`. -/
lemma condEntropy_comm [Countable T] {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) : condEntropy ⟨X, Y⟩ Z μ = condEntropy ⟨Y, X⟩ Z μ :=
  by
  change condEntropy ⟨X, Y⟩ Z μ = condEntropy (Prod.swap ∘ ⟨X, Y⟩) Z μ
  exact (condEntropy_comp_of_injective μ (hX.prodMk hY) Prod.swap Prod.swap_injective).symm


-- @@ L539-539 verbatim
end condEntropy


-- @@ L541-541 verbatim
section pair


-- @@ L543-543 verbatim
variable [MeasurableSpace T]

-- @@ L544-545 verbatim
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]


-- @@ L547-572 expanded
/-- One form of the chain rule : `H[X, Y] = H[X] + H[Y | X]`. -/
lemma chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    entropy ⟨X, Y⟩ μ = entropy X μ + condEntropy Y X μ :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [entropy_eq_kernel_entropy, Kernel.chain_rule]
  · simp_rw [← Kernel.map_const _ (hX.prodMk hY), Kernel.fst_map_prod _ hY, Kernel.map_const _ hX,
      Kernel.map_const _ (hX.prodMk hY)]
    congr 1
    · rw [Kernel.entropy, integral_dirac]
      rfl
    · simp_rw [condEntropy_eq_kernel_entropy hY hX]
      have : Measure.dirac () ⊗ₘ Kernel.const Unit (μ.map X) = μ.map (fun ω ↦ ((), X ω)) :=
        by
        ext s _
        rw [Measure.dirac_unit_compProd_const, Measure.map_map measurable_prodMk_left hX]
        congr
      rw [this, Kernel.entropy_congr (condDistrib_const_unit hX hY μ)]
      have : μ.map (fun ω ↦ ((), X ω)) = (μ.map X).map (Prod.mk ()) :=
        by
        ext s _
        rw [Measure.map_map measurable_prodMk_left hX]
        rfl
      rw [this, Kernel.entropy_prodMkLeft_unit]
  · apply Kernel.FiniteKernelSupport.aefiniteKernelSupport
    exact Kernel.finiteKernelSupport_of_const _


-- @@ L574-578 expanded
/-- Another form of the chain rule : `H[X, Y] = H[Y] + H[X | Y]`. -/
lemma chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    entropy ⟨X, Y⟩ μ = entropy Y μ + condEntropy X Y μ := by
  rw [entropy_comm hX hY, chain_rule' μ hY hX]


-- @@ L580-584 expanded
/-- Another form of the chain rule : `H[X | Y] = H[X, Y] - H[Y]`. -/
lemma chain_rule'' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    condEntropy X Y μ = entropy ⟨X, Y⟩ μ - entropy Y μ := by
  rw [chain_rule μ hX hY, add_sub_cancel_left]


-- @@ L586-595 expanded
/-- Two pairs of variables that have the same joint distribution, have the same
conditional entropy. -/
lemma IdentDistrib.condEntropy_eq {Ω' : Type*} [MeasurableSpace Ω'] {X : Ω → S} {Y : Ω → T}
    {μ' : Measure Ω'} {X' : Ω' → S} {Y' : Ω' → T} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (h : IdentDistrib (⟨X, Y⟩) (⟨X', Y'⟩) μ μ') [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    [FiniteRange Y'] : condEntropy X Y μ = condEntropy X' Y' μ' :=
  by
  have : IdentDistrib Y Y' μ μ' := h.comp measurable_snd
  rw [chain_rule'' _ hX hY, chain_rule'' _ hX' hY', h.entropy_congr, this.entropy_congr]


-- @@ L597-597 verbatim
variable [Countable U] [MeasurableSingletonClass U]


-- @@ L599-610 expanded
/-- If `X : Ω → S` and `Y : Ω → T` are random variables, and `f : T → U` is an
injection then `H[X | f(Y)] = H[X | Y]`. -/
lemma condEntropy_of_injective' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : T → U) (hf : Injective f) (hfY : Measurable (f ∘ Y)) [FiniteRange X]
    [FiniteRange Y] : condEntropy X (f ∘ Y) μ = condEntropy X Y μ :=
  by
  rw [chain_rule'' μ hX hY, chain_rule'' μ hX hfY, chain_rule' μ hX hY, chain_rule' μ hX hfY]
  congr 1
  · congr 1
    exact condEntropy_comp_of_injective μ hY f hf
  exact entropy_comp_of_injective μ hY f hf


-- @@ L612-615 expanded
/-- `H[X | f(X)] = H[X] - H[f(X)]`. -/
lemma condEntropy_comp_self [IsProbabilityMeasure μ] (hX : Measurable X) {f : S → U}
    (hf : Measurable f) [FiniteRange X] :
    condEntropy X (f ∘ X) μ = entropy X μ - entropy (f ∘ X) μ := by
  rw [chain_rule'' μ hX (hf.comp hX), entropy_prod_comp hX _ f]


-- @@ L617-633 expanded
/-- If `X : Ω → S`, `Y : Ω → T`, `Z : Ω → U` are random variables,
then `H[X, Y | Z] = H[X | Z] + H[Y|X, Z]`. -/
lemma cond_chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    condEntropy ⟨X, Y⟩ Z μ = condEntropy X Z μ + condEntropy Y ⟨X, Z⟩ μ :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condEntropy_eq_kernel_entropy (hX.prodMk hY) hZ, Kernel.chain_rule]
  · congr 1
    · rw [condEntropy_eq_kernel_entropy hX hZ]
      refine Kernel.entropy_congr ?_
      exact condDistrib_fst_ae_eq hX hY hZ μ
    · rw [condEntropy_two_eq_kernel_entropy hY hX hZ]
  exact Kernel.aefiniteKernelSupport_condDistrib _ _ μ (by measurability) (by measurability)


-- @@ L635-640 expanded
/-- `H[X, Y | Z] = H[Y | Z] + H[X | Y, Z]`. -/
lemma cond_chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    condEntropy ⟨X, Y⟩ Z μ = condEntropy Y Z μ + condEntropy X ⟨Y, Z⟩ μ := by
  rw [condEntropy_comm hX hY, cond_chain_rule' _ hY hX hZ]


-- @@ L642-655 expanded
/-- Data-processing inequality for the entropy: `H[f(X)] ≤ H[X]`.
To upgrade this to equality, see `entropy_of_comp_eq_of_comp` or `entropy_comp_of_injective`. -/
lemma entropy_comp_le (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (f : S → U)
    [FiniteRange X] : entropy (f ∘ X) μ ≤ entropy X μ :=
  by
  have hfX : Measurable (f ∘ X) := by fun_prop
  have : entropy X μ = entropy ⟨X, f ∘ X⟩ μ :=
    by
    refine (entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule _ hX hfX]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ


-- @@ L657-668 expanded
/-- A Schroder-Bernstein type theorem for entropy : if two random variables are functions of each
  other, then they have the same entropy. Can be used as a substitute for
  `entropy_comp_of_injective` if one doesn't want to establish the injectivity. -/
lemma entropy_of_comp_eq_of_comp (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → T) (g : T → S) (h1 : Y = f ∘ X) (h2 : X = g ∘ Y) [FiniteRange X]
    [FiniteRange Y] : entropy X μ = entropy Y μ :=
  by
  have h3 : entropy X μ ≤ entropy Y μ := by rw [h2]; exact entropy_comp_le μ hY _
  have h4 : entropy Y μ ≤ entropy X μ := by rw [h1]; exact entropy_comp_le μ hX _
  linarith


-- @@ L670-670 verbatim
end pair


-- @@ L672-672 verbatim
section mutualInfo


-- @@ L674-674 verbatim
variable [MeasurableSpace T]


-- @@ L676-680 expanded
/-- The mutual information `I[X : Y]` of two random variables
is defined to be `H[X] + H[Y] - H[X ; Y]`. -/
noncomputable def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  entropy X μ + entropy Y μ - entropy ⟨X, Y⟩ μ


-- @@ L682-682 verbatim
@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ

-- @@ L683-683 verbatim
@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y "]" => mutualInfo X Y volume


-- @@ L685-686 expanded
lemma mutualInfo_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    mutualInfo X Y μ = entropy X μ + entropy Y μ - entropy ⟨X, Y⟩ μ :=
  rfl


-- @@ L688-689 expanded
lemma entropy_add_entropy_sub_mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    entropy X μ + entropy Y μ - mutualInfo X Y μ = entropy ⟨X, Y⟩ μ :=
  sub_sub_self _ _


-- @@ L691-698 expanded
/-- Substituting variables for ones with the same distributions doesn't change the mutual
information. -/
lemma IdentDistrib.mutualInfo_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {X' : Ω' → S}
    {Y' : Ω' → T} (hXY : IdentDistrib (⟨X, Y⟩) (⟨X', Y'⟩) μ μ') :
    mutualInfo X Y μ = mutualInfo X' Y' μ' :=
  by
  have hX : IdentDistrib X X' μ μ' := hXY.comp measurable_fst
  have hY : IdentDistrib Y Y' μ μ' := hXY.comp measurable_snd
  simp_rw [mutualInfo_def, hX.entropy_congr, hY.entropy_congr, hXY.entropy_congr]


-- @@ L700-704 expanded
/-- The conditional mutual information `I[X : Y| Z]` is the mutual information of `X| Z=z` and
`Y| Z=z`, integrated over `z`. -/
noncomputable def condMutualInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U)
    (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Z)[fun z ↦ entropy X (μ[|Z ← z]) + entropy Y (μ[|Z ← z]) - entropy ⟨X, Y⟩ (μ[|Z ← z])]


-- @@ L706-708 expanded
lemma condMutualInfo_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInfo X Y Z μ =
      (μ.map Z)[fun z ↦
        entropy X (μ[|Z ← z]) + entropy Y (μ[|Z ← z]) - entropy ⟨X, Y⟩ (μ[|Z ← z])] :=
  rfl


-- @@ L710-711 verbatim
@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z ";" μ "]" => condMutualInfo X Y Z μ

-- @@ L712-713 verbatim
@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z "]" => condMutualInfo X Y Z volume


-- @@ L715-716 expanded
lemma condMutualInfo_eq_integral_mutualInfo :
    condMutualInfo X Y Z μ = (μ.map Z)[fun z ↦ mutualInfo X Y μ[|Z ⁻¹' { z }]] :=
  rfl


-- @@ L718-719 expanded
@[simp]
lemma condMutualInfo_zero_measure : condMutualInfo X Y Z 0 = 0 := by simp [condMutualInfo]


-- @@ L721-721 verbatim
section


-- @@ L723-723 verbatim
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]


-- @@ L725-737 expanded
/-- Mutual information is non-negative. -/
lemma mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [FiniteRange X]
    [FiniteRange Y] : 0 ≤ mutualInfo X Y μ :=
  by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨X, Y⟩)).map Prod.fst :=
    by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨X, Y⟩)).map Prod.snd :=
    by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg


-- @@ L739-742 expanded
/-- Subadditivity of entropy. -/
lemma entropy_pair_le_add (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [FiniteRange X]
    [FiniteRange Y] : entropy ⟨X, Y⟩ μ ≤ entropy X μ + entropy Y μ :=
  sub_nonneg.1 <| mutualInfo_nonneg hX hY _


-- @@ L744-759 expanded
/-- `I[X : Y] = 0` iff `X, Y` are independent. -/
lemma mutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    mutualInfo X Y μ = 0 ↔ IndepFun X Y μ :=
  by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨X, Y⟩)).map Prod.fst :=
    by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨X, Y⟩)).map Prod.snd :=
    by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd, ← measureMutualInfo.eq_def, measureMutualInfo_eq_zero_iff]
  simp [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    Measure.ext_iff_measureReal_singleton_finiteSupport,
    Measure.map_map measurable_fst (hX.prodMk hY), Measure.map_map measurable_snd (hX.prodMk hY),
    ← measureReal_prod_prod, Function.comp_def]


-- @@ L761-761 verbatim
protected alias ⟨_, IndepFun.mutualInfo_eq_zero⟩ := mutualInfo_eq_zero


-- @@ L763-767 expanded
/-- The mutual information with a constant is always zero. -/
lemma mutualInfo_const (hX : Measurable X) (c : T) {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    [FiniteRange X] : mutualInfo X (fun _ ↦ c) μ = 0 :=
  (indepFun_const c).mutualInfo_eq_zero hX measurable_const


-- @@ L769-773 expanded
/-- `H[X, Y] = H[X] + H[Y]` if and only if `X, Y` are independent. -/
lemma entropy_pair_eq_add (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    entropy ⟨X, Y⟩ μ = entropy X μ + entropy Y μ ↔ IndepFun X Y μ := by
  rw [eq_comm, ← sub_eq_zero, ← mutualInfo_eq_zero hX hY]; rfl


-- @@ L775-776 verbatim
/-- If `X, Y` are independent, then `H[X, Y] = H[X] + H[Y]`. -/
protected alias ⟨_, IndepFun.entropy_pair_eq_add⟩ := entropy_pair_eq_add


-- @@ L778-815 unexpanded
lemma iIndepFun.entropy_eq_add {Ω S : Type*} [hΩ: MeasureSpace Ω] [IsProbabilityMeasure hΩ.volume]
    {m : ℕ} [MeasurableSpace S] [MeasurableSingletonClass S] [Finite S]
    {X : Fin m → Ω → S} (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X) :
    H[(fun ω i ↦ X i ω)] = ∑ i, H[X i] := by
  cases nonempty_fintype S
  induction m with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    convert entropy_const Fin.elim0 <;> infer_instance
  | succ m hm =>
  calc
    _ = H[ ⟨(fun ω (i:Fin m) ↦ X i.castSucc ω), X (.last _)⟩ ] := by
      let f : (Fin (m + 1) → S) → (Fin m → S) × S := fun x ↦ (fun i ↦ x i.castSucc, x (.last m))
      convert! (entropy_comp_of_injective _ _ f _).symm
      · fun_prop
      intro x y hxy
      simp only [Prod.mk.injEq, f] at hxy
      ext i; rcases Fin.eq_castSucc_or_eq_last i with h | rfl
      · obtain ⟨j, rfl⟩ := h; replace hxy := hxy.1; exact congr($hxy j)
      tauto
    _ = H[fun ω (i:Fin m) ↦ X i.castSucc ω] + H[X (.last m)] := by
      apply (entropy_pair_eq_add _ _).mpr _ <;> try fun_prop
      let T : Finset (Fin (m + 1)) := {.last m}ᶜ
      let T' : Finset (Fin (m + 1)) := {.last m}
      let φ : (T → S) → (Fin m → S) := fun f j ↦ f ⟨ j.castSucc, by simp [T] ⟩
      let φ' : (T' → S) → S := fun f ↦ f ⟨ .last m, by simp [T'] ⟩
      exact finsets_comp' (by simp [T', T]) h_indep hX (show Measurable φ by fun_prop)
        (show Measurable φ' by fun_prop)
    _ = ∑ i:Fin m, H[X i.castSucc] + H[X (.last m)] := by
      congr; apply hm _ _
      · intro i; fun_prop
      let T : Fin m → Finset (Fin (m + 1)) := fun i ↦ {i.castSucc}
      let φ : (i:Fin m) → ((_: T i) → S) → S := fun i x ↦ x ⟨ i.castSucc, by simp [T] ⟩
      convert iIndepFun.finsets_comp T _ h_indep hX φ (by fun_prop)
      rw [Finset.pairwiseDisjoint_iff]; rintro ⟨ _, _ ⟩ _ ⟨ _, _ ⟩ _ ⟨ ⟨ _, _ ⟩, hij ⟩
      simp [T] at hij ⊢
      grind
    _ = _ := by rw [Fin.sum_univ_castSucc]



-- @@ L818-818 verbatim
variable [Countable S] [Countable T]


-- @@ L820-822 expanded
/-- `I[X : Y] = I[Y : X]`. -/
lemma mutualInfo_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    mutualInfo X Y μ = mutualInfo Y X μ := by simp_rw [mutualInfo, add_comm, entropy_comm hX hY]


-- @@ L824-830 expanded
/-- `I[X : Y] = H[X] - H[X|Y]`. -/
lemma mutualInfo_eq_entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    mutualInfo X Y μ = entropy X μ - condEntropy X Y μ :=
  by
  rw [mutualInfo_def, chain_rule μ hX hY]
  abel


-- @@ L832-836 expanded
/-- `I[X : Y] = H[Y] - H[Y | X]`. -/
lemma mutualInfo_eq_entropy_sub_condEntropy' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    mutualInfo X Y μ = entropy Y μ - condEntropy Y X μ := by
  rw [mutualInfo_comm hX hY, mutualInfo_eq_entropy_sub_condEntropy hY hX]


-- @@ L838-842 expanded
/-- `H[X] - I[X : Y] = H[X | Y]`. -/
lemma entropy_sub_mutualInfo_eq_condEntropy (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    entropy X μ - mutualInfo X Y μ = condEntropy X Y μ := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY, sub_sub_self]


-- @@ L844-848 expanded
/-- `H[Y] - I[X : Y] = H[Y | X]`. -/
lemma entropy_sub_mutualInfo_eq_condEntropy' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    entropy Y μ - mutualInfo X Y μ = condEntropy Y X μ := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' hX hY, sub_sub_self]


-- @@ L850-856 expanded
lemma IndepFun.condEntropy_eq_entropy {μ : Measure Ω} (h : IndepFun X Y μ) (hX : Measurable X)
    (hY : Measurable Y) [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    condEntropy X Y μ = entropy X μ :=
  by
  have := h.mutualInfo_eq_zero hX hY
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY] at this
  linarith


-- @@ L858-858 verbatim
variable [Countable U] [MeasurableSingletonClass U] [Nonempty S] [Nonempty T]


-- @@ L860-888 expanded
/-- The conditional mutual information agrees with the information of the conditional kernel.
-/
lemma condMutualInfo_eq_kernel_mutualInfo (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange Z] :
    condMutualInfo X Y Z μ = Kernel.mutualInfo (condDistrib (⟨X, Y⟩) Z μ) (μ.map Z) :=
  by
  rcases finiteSupport_of_finiteRange (μ := μ) (X := Z) with ⟨A, hA⟩
  simp_rw [condMutualInfo_def, entropy_def, Kernel.mutualInfo, Kernel.entropy,
    integral_eq_setIntegral hA, setIntegral_finset _ .finset, smul_eq_mul, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr with x
  · have h := condDistrib_fst_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_countable] at h
    specialize h x
    by_cases hx : (μ.map Z) { x } = 0
    · simp [hx, Measure.real]
    rw [h hx, condDistrib_apply hX hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx
  · have h := condDistrib_snd_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_countable] at h
    specialize h x
    by_cases hx : (μ.map Z) { x } = 0
    · simp [hx, Measure.real]
    rw [h hx, condDistrib_apply hY hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx
  · by_cases hx : (μ.map Z) { x } = 0
    · simp [hx, Measure.real]
    rw [condDistrib_apply (hX.prodMk hY) hZ]
    rwa [Measure.map_apply hZ (.singleton _)] at hx


-- @@ L890-890 verbatim
end


-- @@ L892-901 expanded
lemma condMutualInfo_eq_sum [MeasurableSingletonClass U] [IsFiniteMeasure μ] (hZ : Measurable Z)
    [FiniteRange Z] :
    condMutualInfo X Y Z μ =
      ∑ z ∈ FiniteRange.toFinset Z, μ.real (Z ⁻¹' { z }) * mutualInfo X Y μ[|Z ← z] :=
  by
  rw [condMutualInfo_eq_integral_mutualInfo, integral_eq_setIntegral (ae_mem_of_finiteRange hZ),
    setIntegral_finset _ .finset]
  congr 1 with z
  rw [map_measureReal_apply hZ (MeasurableSet.singleton z)]
  rfl


-- @@ L903-915 expanded
/-- A variant of `condMutualInfo_eq_sum` when `Z` has finite codomain. -/
lemma condMutualInfo_eq_sum' [MeasurableSingletonClass U] [IsFiniteMeasure μ] (hZ : Measurable Z)
    [Fintype U] : condMutualInfo X Y Z μ = ∑ z, μ.real (Z ⁻¹' { z }) * mutualInfo X Y (μ[|Z ← z]) :=
  by
  rw [condMutualInfo_eq_sum hZ]
  apply Finset.sum_subset
  · simp
  intro z _ hz
  have : Z ⁻¹' { z } = ∅ := by
    ext ω
    simp at hz
    simp [hz]
  simp [this]


-- @@ L917-917 verbatim
section


-- @@ L919-919 verbatim
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]


-- @@ L921-926 expanded
/-- Conditional information is non-nonegative. -/
lemma condMutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y) {Z : Ω → U} {μ : Measure Ω}
    [FiniteRange X] [FiniteRange Y] : 0 ≤ condMutualInfo X Y Z μ :=
  by
  refine integral_nonneg (fun z ↦ ?_)
  exact mutualInfo_nonneg hX hY _


-- @@ L928-928 verbatim
variable [Countable S] [Countable T]


-- @@ L930-934 expanded
/-- `I[X : Y | Z] = I[Y : X | Z]`. -/
lemma condMutualInfo_comm (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInfo X Y Z μ = condMutualInfo Y X Z μ := by
  simp_rw [condMutualInfo_def, add_comm, entropy_comm hX hY]


-- @@ L936-936 verbatim
variable [MeasurableSingletonClass U]


-- @@ L938-951 expanded
/-- `I[X : Y| Z] = H[X| Z] + H[Y| Z] - H[X, Y| Z]`. -/
lemma condMutualInfo_eq [Countable U] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange Z] :
    condMutualInfo X Y Z μ = condEntropy X Z μ + condEntropy Y Z μ - condEntropy ⟨X, Y⟩ Z μ :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condMutualInfo_eq_kernel_mutualInfo hX hY hZ, Kernel.mutualInfo,
    Kernel.entropy_congr (condDistrib_fst_ae_eq hX hY hZ _),
    Kernel.entropy_congr (condDistrib_snd_ae_eq hX hY hZ _), condEntropy_eq_kernel_entropy hX hZ,
    condEntropy_eq_kernel_entropy hY hZ, condEntropy_eq_kernel_entropy (hX.prodMk hY) hZ]


-- @@ L953-959 expanded
/-- `I[X : Y| Z] = H[X| Z] - H[X|Y, Z]`. -/
lemma condMutualInfo_eq' [Countable U] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    condMutualInfo X Y Z μ = condEntropy X Z μ - condEntropy X ⟨Y, Z⟩ μ :=
  by
  rw [condMutualInfo_eq hX hY hZ, cond_chain_rule _ hX hY hZ]
  ring


-- @@ L961-974 expanded
/-- If `f(Z, X)` is injective for each fixed `Z`, then `I[f(Z, X) : Y| Z] = I[X : Y| Z]`. -/
lemma condMutualInfo_of_inj_map [Countable U] [IsZeroOrProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) {V : Type*} [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (f : U → S → V) (hf : ∀ t, Function.Injective (f t))
    [FiniteRange Z] : condMutualInfo (fun ω ↦ f (Z ω) (X ω)) Y Z μ = condMutualInfo X Y Z μ :=
  by
  have hM : Measurable (Function.uncurry f ∘ ⟨Z, X⟩) := by fun_prop
  have hM : Measurable fun ω ↦ f (Z ω) (X ω) := hM
  rw [condMutualInfo_eq hM hY hZ, condMutualInfo_eq hX hY hZ]
  let g : U → (S × T) → (V × T) := fun z (x, y) ↦ (f z x, y)
  have hg : ∀ t, Function.Injective (g t) := fun _ _ _ h ↦
    Prod.ext_iff.2 ⟨hf _ (Prod.ext_iff.1 h).1, (Prod.ext_iff.1 h).2⟩
  rw [← condEntropy_of_injective μ (hX.prodMk hY) hZ g hg, ← condEntropy_of_injective μ hX hZ _ hf]


-- @@ L976-985 expanded
lemma condMutualInfo_of_inj [Countable U] (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange X]
    [FiniteRange Y] [FiniteRange Z] {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable V] {f : U → V} (hf : Function.Injective f) :
    condMutualInfo X Y (f ∘ Z) μ = condMutualInfo X Y Z μ :=
  by
  have hfZ : Measurable (f ∘ Z) := by fun_prop
  rw [condMutualInfo_eq hX hY hZ, condMutualInfo_eq hX hY hfZ,
    condEntropy_of_injective' _ hX hZ _ hf hfZ, condEntropy_of_injective' _ hY hZ _ hf hfZ,
    condEntropy_of_injective' _ (hX.prodMk hY) hZ _ hf hfZ]


-- @@ L988-1005 expanded
lemma condMutualInfo_of_inj' {S T U S' T' U' Ω : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Countable S] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Countable T] [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U]
    [MeasurableSpace S'] [MeasurableSingletonClass S'] [Countable S'] [MeasurableSpace T']
    [MeasurableSingletonClass T'] [Countable T'] [MeasurableSpace U'] [MeasurableSingletonClass U']
    [Countable U'] {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] [FiniteRange X]
    [FiniteRange Y] [FiniteRange Z] {f : S → S'} (hf : Function.Injective f) {g : T → T'}
    (hg : Function.Injective g) {h : U → U'} (hh : Function.Injective h) :
    condMutualInfo (f ∘ X) (g ∘ Y) (h ∘ Z) μ = condMutualInfo X Y Z μ :=
  calc
    _ = condMutualInfo (f ∘ X) (g ∘ Y) Z μ := by
      rw [condMutualInfo_of_inj _ _ _ _ hh] <;> try fun_prop
    _ = condMutualInfo X (g ∘ Y) Z μ :=
      (condMutualInfo_of_inj_map hX (by fun_prop) hZ (fun _ ↦ f) fun _ ↦ hf)
    _ = condMutualInfo (g ∘ Y) X Z μ := by apply condMutualInfo_comm <;> fun_prop
    _ = condMutualInfo Y X Z μ :=
      (condMutualInfo_of_inj_map hY (by fun_prop) hZ (fun _ ↦ g) (fun _ ↦ hg))
    _ = _ := by apply condMutualInfo_comm <;> fun_prop


-- @@ L1008-1025 expanded
lemma condEntropy_prod_eq_of_indepFun [Finite T] [Finite U] [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X]
    (h : IndepFun (⟨X, Y⟩) Z μ) : condEntropy X ⟨Y, Z⟩ μ = condEntropy X Y μ :=
  by
  cases nonempty_fintype U
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rw [condEntropy_prod_eq_sum _ hY hZ]
  have : condEntropy X Y μ = ∑ z, (μ.real (Z ⁻¹' { z })) * condEntropy X Y μ := by
    rw [← Finset.sum_mul, sum_measureReal_preimage_singleton _ fun z _ ↦ hZ <| .singleton z]; simp
  rw [this]
  congr with w
  rcases eq_or_ne (μ (Z ⁻¹' { w })) 0 with hw | hw
  · simp [hw, Measure.real]
  congr 1
  have : IsProbabilityMeasure (μ[|Z ⁻¹' { w }]) := cond_isProbabilityMeasure hw
  apply IdentDistrib.condEntropy_eq hX hY hX hY
  exact (h.identDistrib_cond (MeasurableSet.singleton w) (hX.prodMk hY) hZ hw).symm


-- @@ L1027-1027 verbatim
end


-- @@ L1029-1029 verbatim
section IsProbabilityMeasure


-- @@ L1031-1031 verbatim
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]


-- @@ L1033-1033 verbatim
variable [Countable U] [MeasurableSingletonClass U]


-- @@ L1035-1051 expanded
/-- `I[X : Y| Z]=0` iff `X, Y` are conditionally independent over `Z`. -/
lemma condMutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y) [IsZeroOrProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    condMutualInfo X Y Z μ = 0 ↔ CondIndepFun X Y Z μ :=
  by
  rw [condIndepFun_iff, condMutualInfo_eq_integral_mutualInfo, integral_eq_zero_iff_of_nonneg]
  · have :
      (fun x ↦ mutualInfo X Y μ[|Z ⁻¹' { x }]) =ᵐ[μ.map Z] 0 ↔
        ∀ᵐ z ∂(μ.map Z), mutualInfo X Y μ[|Z ⁻¹' { z }] = 0 :=
      by rfl
    rw [this]
    apply Filter.eventually_congr
    rw [ae_iff_of_countable]
    intro z _hz
    exact mutualInfo_eq_zero hX hY
  · intro z
    by_cases hz : μ (Z ⁻¹' { z }) = 0
    · simp [cond_eq_zero_of_meas_eq_zero hz, mutualInfo_def]
    · exact mutualInfo_nonneg hX hY _
  · exact integrable_of_finiteSupport _


-- @@ L1053-1053 verbatim
variable (μ)

-- @@ L1054-1054 verbatim
variable [Countable S] [Countable T]


-- @@ L1056-1066 expanded
/-- If `X, Y` are conditionally independent over `Z`, then `H[X, Y, Z] = H[X, Z] + H[Y, Z] - H[Z]`.
-/
lemma ent_of_cond_indep (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : CondIndepFun X Y Z μ) [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]
    [FiniteRange Z] : entropy ⟨X, ⟨Y, Z⟩⟩ μ = entropy ⟨X, Z⟩ μ + entropy ⟨Y, Z⟩ μ - entropy Z μ :=
  by
  have hI : condMutualInfo X Y Z μ = 0 := (condMutualInfo_eq_zero hX hY).mpr h
  rw [condMutualInfo_eq hX hY hZ] at hI
  rw [entropy_assoc hX hY hZ, chain_rule _ (hX.prodMk hY) hZ, chain_rule _ hX hZ,
    chain_rule _ hY hZ]
  linarith [hI]


-- @@ L1068-1068 verbatim
variable [IsZeroOrProbabilityMeasure μ]


-- @@ L1070-1073 expanded
/-- `H[X] - H[X|Y] = I[X : Y]` -/
lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : entropy X μ - condEntropy X Y μ = mutualInfo X Y μ := by
  rw [mutualInfo_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]


-- @@ L1075-1078 expanded
/-- `H[X | Y] ≤ H[X]`. -/
lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) [FiniteRange X]
    [FiniteRange Y] : condEntropy X Y μ ≤ entropy X μ :=
  sub_nonneg.1 <| by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInfo_nonneg hX hY _


-- @@ L1080-1092 expanded
/-- `H[X | Y, Z] ≤ H[X | Z]`. -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X]
    [FiniteRange Y] [FiniteRange Z] : condEntropy X ⟨Y, Z⟩ μ ≤ condEntropy X Z μ :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condEntropy_eq_kernel_entropy hX hZ, condEntropy_two_eq_kernel_entropy hX hY hZ]
  refine (Kernel.entropy_condKernel_le_entropy_snd ?_).trans_eq ?_
  · apply Kernel.aefiniteKernelSupport_condDistrib
    all_goals fun_prop
  exact Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ _)


-- @@ L1094-1108 expanded
/-- Data-processing inequality for the conditional entropy: `H[Y|f(X)] ≥ H[Y|X]`
To upgrade this to equality, see `condEntropy_of_injective'` -/
lemma condEntropy_comp_ge [FiniteRange X] [FiniteRange Y] (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (f : S → U) :
    condEntropy Y (f ∘ X) μ ≥ condEntropy Y X μ :=
  by
  have h_joint : entropy ⟨Y, ⟨X, f ∘ X⟩⟩ μ = entropy ⟨Y, X⟩ μ :=
    by
    let g : T × S → T × S × U := fun (y, x) ↦ (y, (x, f x))
    change entropy (g ∘ ⟨Y, X⟩) μ = entropy ⟨Y, X⟩ μ
    refine entropy_comp_of_injective μ (by exact Measurable.prod hY hX) g (fun _ _ h => ?_)
    repeat rewrite [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  have hZ : Measurable (f ∘ X) := by fun_prop
  rewrite [chain_rule'' μ hY hX, ← entropy_prod_comp hX μ f, ← h_joint, ←
    chain_rule'' μ hY (Measurable.prod (by exact hX) (by exact hZ))]
  exact entropy_submodular μ hY hX hZ


-- @@ L1110-1116 expanded
/-- The submodularity inequality: `H[X, Y, Z] + H[Z] ≤ H[X, Z] + H[Y, Z]`. -/
lemma entropy_triple_add_entropy_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    entropy ⟨X, ⟨Y, Z⟩⟩ μ + entropy Z μ ≤ entropy ⟨X, Z⟩ μ + entropy ⟨Y, Z⟩ μ :=
  by
  rw [chain_rule _ hX (hY.prodMk hZ), chain_rule _ hX hZ, chain_rule _ hY hZ]
  ring_nf
  exact add_le_add le_rfl (entropy_submodular _ hX hY hZ)


-- @@ L1118-1118 verbatim
end IsProbabilityMeasure

-- @@ L1119-1119 verbatim
end mutualInfo

-- @@ L1120-1120 verbatim
end ProbabilityTheory



-- @@ L1123-1123 verbatim
section dataProcessing


-- @@ L1125-1125 verbatim
open Function MeasureTheory Measure Real

-- @@ L1126-1126 verbatim
open scoped ENNReal NNReal Topology ProbabilityTheory


-- @@ L1128-1128 verbatim
namespace ProbabilityTheory


-- @@ L1130-1130 verbatim
universe uΩ uS uT uU uV uW


-- @@ L1132-1139 verbatim
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {W : Type uW}
  [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSpace V] [MeasurableSpace W]
  [Countable S] [Countable T] [Countable V] [Countable W]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V] [MeasurableSingletonClass W]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}


-- @@ L1141-1152 expanded
/-- Let `X, Y`be random variables. For any function `f, g` on the range of `X`, we have
`I[f(X) : Y] ≤ I[X : Y]`.
-/
lemma mutual_comp_le [Countable U] (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) [FiniteRange X] [FiniteRange Y] :
    mutualInfo (f ∘ X) Y μ ≤ mutualInfo X Y μ :=
  by
  have h_meas : Measurable (f ∘ X) := by fun_prop
  rw [mutualInfo_comm h_meas hY, mutualInfo_comm hX hY,
    mutualInfo_eq_entropy_sub_condEntropy hY h_meas, mutualInfo_eq_entropy_sub_condEntropy hY hX]
  gcongr
  exact condEntropy_comp_ge μ hX hY f


-- @@ L1154-1164 expanded
/-- Let `X, Y` be random variables. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f ∘ X : g ∘ Y ; μ] ≤ I[X : Y ; μ]`. -/
lemma mutual_comp_comp_le [Countable U] (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) (g : T → V) (hg : Measurable g) [FiniteRange X]
    [FiniteRange Y] : mutualInfo (f ∘ X) (g ∘ Y) μ ≤ mutualInfo X Y μ :=
  calc
    _ ≤ mutualInfo X (g ∘ Y) μ := mutual_comp_le μ hX (Measurable.comp hg hY) f
    _ = mutualInfo (g ∘ Y) X μ := (mutualInfo_comm hX (Measurable.comp hg hY) μ)
    _ ≤ mutualInfo Y X μ := (mutual_comp_le μ hY hX g)
    _ = mutualInfo X Y μ := mutualInfo_comm hY hX μ


-- @@ L1166-1182 expanded
/-- Let `X, Y, Z`. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ]`. -/
lemma condMutual_comp_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (f : S → V) (g : T → W) (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    condMutualInfo (f ∘ X) (g ∘ Y) Z μ ≤ condMutualInfo X Y Z μ :=
  by
  rw [condMutualInfo_eq_sum hZ, condMutualInfo_eq_sum hZ]
  apply Finset.sum_le_sum
  intro i _
  rcases eq_or_lt_of_le (measureReal_nonneg (μ := μ) (s := (Z ⁻¹' { i }))) with h | h
  · simp [← h]
  · gcongr
    have : IsProbabilityMeasure (μ[|Z ← i]) :=
      by
      apply cond_isProbabilityMeasure_of_finite
      · exact (ENNReal.toReal_ne_zero.mp (ne_of_gt h)).left
      · exact (ENNReal.toReal_ne_zero.mp (ne_of_gt h)).right
    apply mutual_comp_comp_le _ hX hY f g hg


-- @@ L1184-1184 verbatim
end ProbabilityTheory

-- @@ L1185-1185 verbatim
end dataProcessing


-- @@ L1187-1187 verbatim
section MeasureSpace_example


-- @@ L1189-1189 verbatim
open ProbabilityTheory


-- @@ L1191-1194 verbatim
variable {Ω S T : Type*} [MeasureSpace Ω] [IsZeroOrProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}


-- @@ L1196-1198 expanded
/-- An example to illustrate how `MeasureSpace` can be used to suppress the ambient measure. -/
example (hX : Measurable X) (hY : Measurable Y) :
    entropy ⟨X, Y⟩ volume = entropy Y volume + condEntropy X Y volume :=
  chain_rule _ hX hY


-- @@ L1200-1200 verbatim
end MeasureSpace_example
