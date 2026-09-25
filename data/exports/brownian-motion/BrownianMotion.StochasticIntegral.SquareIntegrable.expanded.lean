/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.AEEq
public import BrownianMotion.Auxiliary.MeanInequalities
public import BrownianMotion.Auxiliary.MeasureTheory
public import BrownianMotion.StochasticIntegral.ClassD
public import BrownianMotion.StochasticIntegral.DoobLp


-- @@ L14-16 verbatim
/-! # Square integrable martingales

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open MeasureTheory Filter Function TopologicalSpace AEEqProcess

-- @@ L21-21 verbatim
open scoped ENNReal NNReal Topology RealInnerProductSpace


-- @@ L23-23 verbatim
namespace ProbabilityTheory


-- @@ L25-26 verbatim
variable {ι Ω E : Type*} [NormedAddCommGroup E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}


-- @@ L28-28 verbatim
section LinearOrder


-- @@ L30-31 verbatim
variable [LinearOrder ι] [TopologicalSpace ι]
  {X Y Z : ι → Ω → E} {𝓕 : Filtration ι mΩ} {τ : Ω → WithTop ι}


-- @@ L33-33 verbatim
section IsSquareIntegrable


-- @@ L35-35 verbatim
/-! ### Predicates `IsSquareIntegrable` and `IsAESquareIntegrable` -/


-- @@ L37-37 verbatim
variable [NormedSpace ℝ E]


-- @@ L39-44 verbatim
/-- A square integrable martingale is a martingale with cadlag paths and uniformly bounded
second moments. -/
structure IsSquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  martingale : Martingale X 𝓕 P
  cadlag : ∀ ω, IsCadlag (X · ω)
  bounded : ⨆ i, eLpNorm (X i) 2 P < ∞


-- @@ L46-47 verbatim
lemma IsSquareIntegrable.isRightContinuous (hX : IsSquareIntegrable X 𝓕 P) (ω : Ω) :
    IsRightContinuous (X · ω) := (hX.cadlag ω).right_continuous


-- @@ L49-59 verbatim
lemma IsSquareIntegrable.const [IsFiniteMeasure P] {c : E} :
    IsSquareIntegrable (fun _ _ ↦ c) 𝓕 P where
  martingale := martingale_const 𝓕 P c
  cadlag ω := isCadlag_const c
  bounded := by
    obtain _ | _ := isEmpty_or_nonempty ι
    · simp
    obtain rfl | hP := eq_or_ne P 0
    · simp
    rw [iSup_const, eLpNorm_const c (by simp) hP]
    finiteness


-- @@ L61-64 verbatim
lemma IsSquareIntegrable.uniformIntegrable [IsFiniteMeasure P] (hX : IsSquareIntegrable X 𝓕 P) :
    UniformIntegrable X 1 P :=
  uniformIntegrable_of_eLpNorm_le (fun t ↦ hX.martingale.stronglyMeasurable'.aestronglyMeasurable)
    2 1 (by simp) le_rfl (⨆ t, eLpNorm (X t) 2 P) hX.bounded.ne (le_iSup _)


-- @@ L66-69 expanded
/-- An a.e.-square integrable martingale is a process that is indistinguishable from a
square integrable martingale, see `IsSquareIntegrable`. -/
def IsAESquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ Indistinguishable P X Y


-- @@ L71-78 verbatim
lemma IsSquareIntegrable.stronglyMeasurable_stoppedValue'
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι]
    (hX : IsSquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] (𝓕.stoppedValue' X τ P) := by
  borelize ι
  exact 𝓕.stronglyMeasurable_stoppedValue'
    (hX.martingale.stronglyAdapted.isStronglyProgressive_of_rightContinuous
      (fun ω ↦ (hX.cadlag ω).right_continuous)) (fun ω ↦ (hX.cadlag ω).right_continuous) hτ


-- @@ L80-85 verbatim
lemma IsAESquareIntegrable.aestronglyMeasurable_stoppedValue'
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι]
    (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    AEStronglyMeasurable[hτ.measurableSpace] (𝓕.stoppedValue' X τ P) P :=
  ⟨𝓕.stoppedValue' hX.choose τ P, hX.choose_spec.1.stronglyMeasurable_stoppedValue' hτ,
    𝓕.stoppedValue'_congr hX.choose_spec.2⟩


-- @@ L87-89 verbatim
lemma IsAESquareIntegrable.uniformIntegrable [IsFiniteMeasure P] (hX : IsAESquareIntegrable X 𝓕 P) :
    UniformIntegrable X 1 P :=
  hX.choose_spec.1.uniformIntegrable.ae_eq (fun t ↦ (hX.choose_spec.2.ae_eq_eval t).symm)


-- @@ L91-93 verbatim
lemma IsAESquareIntegrable.aestronglyAdapted (hX : IsAESquareIntegrable X 𝓕 P) :
    AEStronglyAdapted X 𝓕 P :=
  hX.choose_spec.1.martingale.stronglyAdapted.aestronglyAdapted.congr hX.choose_spec.2.symm


-- @@ L95-96 verbatim
lemma IsSquareIntegrable.isAESquareIntegrable (hX : IsSquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable X 𝓕 P := ⟨X, hX, by rfl⟩


-- @@ L98-100 verbatim
lemma IsAESquareIntegrable.const [IsFiniteMeasure P] {c : E} :
    IsAESquareIntegrable (fun _ _ ↦ c) 𝓕 P :=
  IsSquareIntegrable.const.isAESquareIntegrable


-- @@ L102-105 expanded
lemma IsAESquareIntegrable.congr {X Y : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P)
    (hXY : Indistinguishable P X Y) : IsAESquareIntegrable Y 𝓕 P :=
  by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  exact ⟨Z, hZ1, hXY.symm.trans hZ2⟩


-- @@ L107-110 expanded
lemma isAESquareIntegrable_congr {X Y : ι → Ω → E} (hXY : Indistinguishable P X Y) :
    IsAESquareIntegrable X 𝓕 P ↔ IsAESquareIntegrable Y 𝓕 P
    where
  mp h := h.congr hXY
  mpr h := h.congr hXY.symm


-- @@ L112-116 verbatim
lemma IsSquareIntegrable.memLp_two (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    MemLp (X i) 2 P := by
  refine ⟨(hX.martingale.stronglyMeasurable i).aestronglyMeasurable.mono (𝓕.le i), ?_⟩
  grw [le_iSup (fun t ↦ eLpNorm (X t) 2 P)]
  exact hX.bounded


-- @@ L118-123 verbatim
omit [TopologicalSpace ι] [NormedSpace ℝ E] in
@[simp, nontriviality]
lemma stronglyAdapted_of_subsingleton_dom [Subsingleton Ω] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) :
    StronglyAdapted 𝓕 X := by
  intro i
  exact .of_subsingleton_dom


-- @@ L125-130 verbatim
omit [TopologicalSpace ι] [NormedSpace ℝ E] in
@[simp, nontriviality]
lemma stronglyAdapted_of_subsingleton_cod [Subsingleton E] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) :
    StronglyAdapted 𝓕 X := by
  intro i
  exact .of_subsingleton_cod


-- @@ L132-140 verbatim
omit [TopologicalSpace ι] in
@[simp]
lemma martingale_of_isEmpty [IsEmpty Ω] (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    Martingale X 𝓕 P := by
  refine ⟨?_, ?_⟩
  · exact stronglyAdapted_of_subsingleton_dom _ _
  · intro i j hij
    have : P = 0 := Subsingleton.elim _ _
    simp [this, Filter.EventuallyEq, Filter.eventually_bot]


-- @@ L142-151 verbatim
@[simp]
lemma isSquareIntegrable_of_isEmpty [IsEmpty Ω]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    IsSquareIntegrable X 𝓕 P := by
  refine ⟨?_, ?_, ?_⟩
  · exact martingale_of_isEmpty _ _ _
  · intro ω
    exfalso
    exact isEmptyElim ω
  · simp


-- @@ L153-158 verbatim
lemma isSquareIntegrable_of_le_const (h_mart : Martingale X 𝓕 P) (h_cadlag : ∀ ω, IsCadlag (X · ω))
    {C : ℝ≥0} (h_bound : ∀ i, eLpNorm (X i) 2 P ≤ C) :
    IsSquareIntegrable X 𝓕 P := by
  refine ⟨h_mart, h_cadlag, ?_⟩
  rw [iSup_lt_iff]
  exact ⟨C, by simp, h_bound⟩


-- @@ L160-169 verbatim
lemma IsSquareIntegrable.integrable_sq (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    Integrable (fun ω ↦ ‖X i ω‖ ^ 2) P := by
  constructor
  · have hX_meas := (hX.martingale.stronglyAdapted i).mono (𝓕.le i)
    fun_prop
  · have hX_bound : eLpNorm (X i) 2 P < ∞ := by
      calc eLpNorm (X i) 2 P
      _ ≤ ⨆ j, eLpNorm (X j) 2 P := le_iSup (fun j ↦ eLpNorm (X j) 2 P) i
      _ < ∞ := hX.bounded
    simpa [HasFiniteIntegral, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top] using hX_bound


-- @@ L171-189 verbatim
@[to_fun]
lemma IsSquareIntegrable.add [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X + Y) 𝓕 P := by
  refine ⟨hX.martingale.add hY.martingale, fun ω ↦ (hX.cadlag ω).add (hY.cadlag ω), ?_⟩
  have hX_bound : ⨆ i, eLpNorm (X i) 2 P < ∞ := hX.bounded
  have hY_bound : ⨆ i, eLpNorm (Y i) 2 P < ∞ := hY.bounded
  calc ⨆ i, eLpNorm (fun ω ↦ X i ω + Y i ω) 2 P
      ≤ ⨆ i, (eLpNorm (X i) 2 P + eLpNorm (Y i) 2 P) := by
        refine iSup_mono fun i ↦ ?_
        exact eLpNorm_add_le
          ((hX.martingale.stronglyAdapted i).mono (𝓕.le i)).aestronglyMeasurable
          ((hY.martingale.stronglyAdapted i).mono (𝓕.le i)).aestronglyMeasurable (by simp)
    _ ≤ (⨆ i, eLpNorm (X i) 2 P) + ⨆ i, eLpNorm (Y i) 2 P := by
        refine iSup_le fun i => ?_
        gcongr
        · exact le_iSup (fun i => eLpNorm (X i) 2 P) i
        · exact le_iSup (fun i => eLpNorm (Y i) 2 P) i
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hX_bound, hY_bound⟩


-- @@ L191-197 verbatim
@[to_fun]
lemma IsAESquareIntegrable.add [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    IsAESquareIntegrable (X + Y) 𝓕 P := by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  obtain ⟨T, hT1, hT2⟩ := hY
  exact ⟨Z + T, hZ1.add hT1, hZ2.add hT2⟩


-- @@ L199-207 verbatim
@[to_fun]
lemma IsSquareIntegrable.smul [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) (r : ℝ) :
    IsSquareIntegrable (r • X) 𝓕 P where
  martingale := hX.martingale.smul r
  cadlag ω := hX.cadlag ω |>.const_smul r
  bounded := by
    change (⨆ i, eLpNorm (r • X i) 2 P) < ∞
    simp only [eLpNorm_const_smul, ← ENNReal.mul_iSup]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hX.bounded


-- @@ L209-213 verbatim
@[to_fun]
lemma IsAESquareIntegrable.smul [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) (r : ℝ) :
    IsAESquareIntegrable (r • X) 𝓕 P := by
  obtain ⟨Y, hY1, hY2⟩ := hX
  exact ⟨r • Y, hY1.smul r, hY2.const_smul⟩


-- @@ L215-218 verbatim
@[to_fun]
lemma IsSquareIntegrable.neg [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)


-- @@ L220-223 verbatim
@[to_fun]
lemma IsAESquareIntegrable.neg [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)


-- @@ L225-229 verbatim
@[to_fun]
lemma IsSquareIntegrable.sub [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X - Y) 𝓕 P := by
  simpa [sub_eq_add_neg] using (hX.add hY.neg)


-- @@ L231-235 verbatim
@[to_fun]
lemma IsAESquareIntegrable.sub [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    IsAESquareIntegrable (X - Y) 𝓕 P := by
  simpa [sub_eq_add_neg] using (hX.add hY.neg)


-- @@ L237-243 verbatim
open scoped Classical in
/-- If `hX : IsAESquareIntegrable X 𝓕 P` and `∀ᵐ ω ∂P, Continuous (X · ω)`, then
`hX.toContinuous X` is continuous everywhere, satisfies `IsSquareIntegrable` and
is indistinguishable from `X`. -/
noncomputable def IsAESquareIntegrable.toContinuous
    (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) (t : ι) (ω : Ω) : E :=
  if Continuous (hX.choose · ω) then hX.choose t ω else 0


-- @@ L245-250 verbatim
lemma IsAESquareIntegrable.continuous_toContinuous (hX : IsAESquareIntegrable X 𝓕 P) (ω : Ω) :
    Continuous (hX.toContinuous X · ω) := by
  simp_rw [toContinuous]
  split_ifs with h
  · exact h
  · exact continuous_const


-- @@ L252-257 expanded
lemma IsAESquareIntegrable.indist_toContinuous (hX1 : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hX2 : IsAESquareIntegrable X 𝓕 P) : Indistinguishable P X (hX2.toContinuous X) :=
  by
  filter_upwards [hX1, hX2.choose_spec.2] with ω h1 h2
  simp_rw [h2] at h1
  simp [toContinuous, h1, h2]


-- @@ L259-266 verbatim
lemma IsSquareIntegrable.submartingale_sq_norm [SigmaFiniteFiltration P 𝓕] [CompleteSpace E]
    (hX : IsSquareIntegrable X 𝓕 P) :
    Submartingale (fun i ω ↦ ‖X i ω‖ ^ 2) 𝓕 P := by
  refine hX.1.submartingale_convex_comp (φ := fun x ↦ ‖x‖ ^ 2) ?_ (by fun_prop) fun i ↦ ?_
  · exact ConvexOn.pow convexOn_univ_norm (fun _ _ ↦ by positivity) 2
  · refine MemLp.integrable_norm_pow ⟨?_, ?_⟩ (by linarith)
    · exact hX.1.1.stronglyMeasurable.aestronglyMeasurable
    · exact lt_of_le_of_lt (le_iSup (fun i ↦ eLpNorm (X i) 2 P) i) hX.3


-- @@ L268-284 verbatim
lemma IsSquareIntegrable.eLpNorm_mono [SigmaFiniteFiltration P 𝓕] [CompleteSpace E]
    (hX : IsSquareIntegrable X 𝓕 P) {i j : ι} (hij : i ≤ j) :
    eLpNorm (X i) 2 P ≤ eLpNorm (X j) 2 P := by
  have : ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ ∫ ω, ‖X j ω‖ ^ 2 ∂P := by
    simpa using hX.submartingale_sq_norm.setIntegral_le hij MeasurableSet.univ
  calc
  _ = (∫⁻ ω, ‖X i ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  _ = (ENNReal.ofReal (∫ ω, ‖X i ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq i)).symm
  _ ≤ (ENNReal.ofReal (∫ ω, ‖X j ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by gcongr
  _ = (∫⁻ ω, ‖X j ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq j))
  _ = eLpNorm (X j) 2 P := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal]


-- @@ L286-289 verbatim
lemma IsSquareIntegrable.ae_tendsto_limitProcess [IsFiniteMeasure P]
    (hX : IsSquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) :=
  hX.martingale.ae_tendsto_limitProcess hX.uniformIntegrable hX.isRightContinuous


-- @@ L291-297 verbatim
lemma IsAESquareIntegrable.ae_tendsto_limitProcess [IsFiniteMeasure P]
    (hX : IsAESquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  filter_upwards [hX.choose_spec.2, hX.choose_spec.1.ae_tendsto_limitProcess,
    𝓕.limitProcess_congr hX.choose_spec.2] with ω h1 h2 h3
  rw [h3]
  exact h2.congr (fun t ↦ (h1 t).symm)


-- @@ L299-304 verbatim
@[to_fun limitProcess_fun_add]
lemma IsSquareIntegrable.limitProcess_add [Nonempty ι] [IsFiniteMeasure P]
    (hX : IsSquareIntegrable X 𝓕 P) (hY : IsSquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X + Y) P =ᵐ[P] 𝓕.limitProcess X P + 𝓕.limitProcess Y P :=
  hX.martingale.limitProcess_add hX.uniformIntegrable hX.isRightContinuous
    hY.martingale hY.uniformIntegrable hY.isRightContinuous


-- @@ L306-311 verbatim
@[to_fun limitProcess_fun_sub]
lemma IsSquareIntegrable.limitProcess_sub [Nonempty ι] [IsFiniteMeasure P]
    (hX : IsSquareIntegrable X 𝓕 P) (hY : IsSquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X - Y) P =ᵐ[P] 𝓕.limitProcess X P - 𝓕.limitProcess Y P :=
  hX.martingale.limitProcess_sub hX.uniformIntegrable hX.isRightContinuous
    hY.martingale hY.uniformIntegrable hY.isRightContinuous


-- @@ L313-317 verbatim
@[to_fun limitProcess_fun_add]
lemma IsAESquareIntegrable.limitProcess_add [Nonempty ι] [IsFiniteMeasure P]
    (hX : IsAESquareIntegrable X 𝓕 P) (hY : IsAESquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X + Y) P =ᵐ[P] 𝓕.limitProcess X P + 𝓕.limitProcess Y P := by
  grw [hX.choose_spec.2, hY.choose_spec.2, hX.choose_spec.1.limitProcess_add hY.choose_spec.1]


-- @@ L319-323 verbatim
@[to_fun limitProcess_fun_sub]
lemma IsAESquareIntegrable.limitProcess_sub [Nonempty ι] [IsFiniteMeasure P]
    (hX : IsAESquareIntegrable X 𝓕 P) (hY : IsAESquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X - Y) P =ᵐ[P] 𝓕.limitProcess X P - 𝓕.limitProcess Y P := by
  grw [hX.choose_spec.2, hY.choose_spec.2, hX.choose_spec.1.limitProcess_sub hY.choose_spec.1]


-- @@ L325-328 verbatim
variable (𝓕) in
lemma tendsto_ae_condExp' (X : Ω → E) :
    ∀ᵐ ω ∂P, Tendsto (P[X | 𝓕 ·] ω) atTop (𝓝 (P[X | ⨆ t, 𝓕 t] ω)) := by
  sorry


-- @@ L330-333 verbatim
lemma IsSquareIntegrable.condExp_limitProcess_ae_eq [IsFiniteMeasure P]
    (hX : IsSquareIntegrable X 𝓕 P) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t :=
  hX.martingale.condExp_limitProcess_ae_eq hX.uniformIntegrable hX.isRightContinuous t


-- @@ L335-338 verbatim
lemma IsSquareIntegrable.condExp_limitProcess_ae_eq' [IsFiniteMeasure P]
    (hX : IsSquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    P[𝓕.limitProcess X P | hτ.measurableSpace] =ᵐ[P] 𝓕.stoppedValue' X τ P :=
  hX.martingale.condExp_limitProcess_ae_eq' hX.uniformIntegrable hX.isRightContinuous hτ


-- @@ L340-340 verbatim
attribute [gcongr] condExp_congr_ae


-- @@ L342-346 verbatim
lemma IsAESquareIntegrable.condExp_limitProcess_ae_eq [IsFiniteMeasure P] [CompleteSpace E]
    (hX : IsAESquareIntegrable X 𝓕 P) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t := by
  grw [𝓕.limitProcess_congr hX.choose_spec.2, hX.choose_spec.1.condExp_limitProcess_ae_eq,
    hX.choose_spec.2.ae_eq_eval]


-- @@ L348-352 verbatim
lemma IsAESquareIntegrable.condExp_limitProcess_ae_eq' [IsFiniteMeasure P] [CompleteSpace E]
    (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    P[𝓕.limitProcess X P | hτ.measurableSpace] =ᵐ[P] 𝓕.stoppedValue' X τ P := by
  grw [𝓕.limitProcess_congr hX.choose_spec.2, hX.choose_spec.1.condExp_limitProcess_ae_eq',
    hX.choose_spec.2]


-- @@ L354-356 verbatim
lemma IsSquareIntegrable.tendsto_eLpNorm_two_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    Tendsto (fun i ↦ eLpNorm (X i - 𝓕.limitProcess X P) 2 P) atTop (𝓝 0) := by
  sorry


-- @@ L358-366 verbatim
lemma isSquareIntegrable_of_limitProcess [CompleteSpace E]
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P) (hX3 : ∀ ω, IsCadlag (X · ω))
    (hX4 : MemLp (𝓕.limitProcess X P) 2 P) :
    IsSquareIntegrable X 𝓕 P where
  martingale := hX1
  cadlag := hX3
  bounded := by
    grw [iSup_eLpNorm_le_eLpNorm_limitProcess hX1 hX2 (fun ω ↦ (hX3 ω).right_continuous) (by simp)]
    exact hX4.2


-- @@ L368-370 verbatim
lemma IsSquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  sorry


-- @@ L372-382 verbatim
lemma IsSquareIntegrable.iSup_lintegral_pow_two_eq (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ t, ∫⁻ ω, ‖X t ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖𝓕.limitProcess X P ω‖ₑ ^ 2 ∂P := by
  apply ENNReal.rpow_left_injective (x := 1 / 2) (by simp)
  simp only
  rw [ENNReal.rpow_iSup _ (by simp)]
  convert hX.iSup_eLpNorm_eq_eLpNorm_limitProcess
  · rfl
  · rw [eLpNorm_eq_eLpNorm', eLpNorm']
    all_goals simp
  · rw [eLpNorm_eq_eLpNorm', eLpNorm']
    all_goals simp


-- @@ L384-389 verbatim
lemma IsAESquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess (hX : IsAESquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  rw [eLpNorm_congr_ae (𝓕.limitProcess_congr hX.choose_spec.2),
    ← hX.choose_spec.1.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  congr with i
  rw [eLpNorm_congr_ae (hX.choose_spec.2.ae_eq_eval i)]


-- @@ L391-396 verbatim
lemma IsSquareIntegrable.memLp_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    MemLp (𝓕.limitProcess X P) 2 P := by
  constructor
  · exact Filtration.stronglyMeasurable_limit_process'.aestronglyMeasurable
  rw [← hX.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  exact hX.bounded


-- @@ L398-401 verbatim
lemma IsAESquareIntegrable.memLp_limitProcess (hX : IsAESquareIntegrable X 𝓕 P) :
    MemLp (𝓕.limitProcess X P) 2 P := by
  rw [memLp_congr_ae (𝓕.limitProcess_congr hX.choose_spec.2)]
  exact hX.choose_spec.1.memLp_limitProcess


-- @@ L403-403 verbatim
variable [OrderTopology ι] [SecondCountableTopology ι]


-- @@ L405-416 verbatim
lemma IsSquareIntegrable.integral_iSup_norm_rpow_rpow_inv_le_limitProcess
    [CompleteSpace E] [IsFiniteMeasure P] (hX : IsSquareIntegrable X 𝓕 P) :
    (∫⁻ ω, (⨆ t, ‖X t ω‖ₑ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ 2 * eLpNorm (𝓕.limitProcess X P) 2 P := by
  simp_rw [← ENNReal.rpow_ofNat (n := 2)]
  grw [integral_iSup_norm_rpow_le hX.martingale hX.isRightContinuous,
    ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_iSup, ← hX.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  · gcongr
    · rw [one_div, ENNReal.rpow_inv_le_iff (by simp)]
      norm_num
    · rw [eLpNorm_eq_eLpNorm' (by simp) (by simp), eLpNorm']
      rfl
  all_goals simp


-- @@ L418-426 verbatim
lemma IsAESquareIntegrable.integral_iSup_norm_rpow_rpow_inv_le_limitProcess
    [CompleteSpace E] [IsFiniteMeasure P] (hX : IsAESquareIntegrable X 𝓕 P) :
    (∫⁻ ω, (⨆ t, ‖X t ω‖ₑ) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤ 2 * eLpNorm (𝓕.limitProcess X P) 2 P := by
  grw [eLpNorm_congr_ae (𝓕.limitProcess_congr hX.choose_spec.2),
    ← hX.choose_spec.1.integral_iSup_norm_rpow_rpow_inv_le_limitProcess]
  gcongr 1
  apply lintegral_mono_ae
  filter_upwards [hX.choose_spec.2] with ω h
  simp [h]


-- @@ L428-428 verbatim
variable [OrderBot ι]


-- @@ L430-430 verbatim
variable [IsFiniteMeasure P]


-- @@ L432-435 verbatim
lemma IsSquareIntegrable.limitProcess_stoppedProcess
    (hX : IsSquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (stoppedProcess X τ) P =ᵐ[P] 𝓕.stoppedValue' X τ P :=
  𝓕.limitProcess_stoppedProcess hX.martingale hX.uniformIntegrable hX.isRightContinuous hτ


-- @@ L437-441 verbatim
lemma IsAESquareIntegrable.limitProcess_stoppedProcess
    (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (stoppedProcess X τ) P =ᵐ[P] 𝓕.stoppedValue' X τ P := by
  grw [𝓕.limitProcess_congr (stoppedProcess_congr hX.choose_spec.2),
    hX.choose_spec.1.limitProcess_stoppedProcess hτ, 𝓕.stoppedValue'_congr hX.choose_spec.2]


-- @@ L443-443 verbatim
variable [CompleteSpace E]


-- @@ L445-484 verbatim
protected lemma IsSquareIntegrable.stoppedProcess
    [Approximable 𝓕 P] (hX : IsSquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    IsSquareIntegrable (stoppedProcess X τ) 𝓕 P := by
  borelize ι E
  apply isSquareIntegrable_of_limitProcess
  · exact hX.martingale.stoppedProcess (fun _ ↦ (hX.cadlag _).right_continuous) hτ
  · have : ClassD X 𝓕 P := hX.martingale.classD_iff_uniformIntegrable hX.isRightContinuous |>.2
        hX.uniformIntegrable
    simp_rw [stoppedProcess_eq_stoppedValue]
    exact this.uniformIntegrable.comp (fun t : ι ↦ ⟨fun ω ↦ min t (τ ω),
      (isStoppingTime_const 𝓕 t).min hτ, by simp⟩)
  · exact fun ω ↦ (hX.cadlag ω).stoppedProcess τ
  · refine ⟨𝓕.stronglyMeasurable_limit_process'.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp) (by simp)]
    calc
    ∫⁻ ω, ‖𝓕.limitProcess (MeasureTheory.stoppedProcess X τ) P ω‖ₑ ^ (ENNReal.toReal 2) ∂P
      = ∫⁻ ω, ‖𝓕.stoppedValue' X τ P ω‖ₑ ^ (ENNReal.toReal 2) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hX.limitProcess_stoppedProcess hτ] with ω h
      simp [h]
    _ ≤ ∫⁻ ω, (⨆ t, ‖X t ω‖ₑ) ^ (ENNReal.toReal 2) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hX.isAESquareIntegrable.ae_tendsto_limitProcess] with ω h1
      gcongr
      cases h : τ ω with
      | top =>
        simp only [h, Filtration.stoppedValue'_of_eq_top]
        grw [← ((continuous_enorm.tendsto (𝓕.limitProcess X P ω)).comp h1).limsup_eq,
          limsup_le_iSup]
        simp
      | coe t =>
        simpa [h] using le_iSup (fun s ↦ ‖X s ω‖ₑ) t
    _ ≤ 4 * ∫⁻ ω, ‖𝓕.limitProcess X P ω‖ₑ ^ (ENNReal.toReal 2) ∂P := by
      grw [integral_iSup_norm_rpow_le hX.martingale hX.isRightContinuous (by simp)]
      simp [hX.iSup_lintegral_pow_two_eq]
      norm_num
    _ < ∞ := by
      apply ENNReal.mul_lt_top (by simp)
      rw [← eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp) (by simp)]
      exact hX.memLp_limitProcess.2


-- @@ L486-491 verbatim
protected lemma IsAESquareIntegrable.stoppedProcess
    [Approximable 𝓕 P] (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    IsAESquareIntegrable (stoppedProcess X τ) 𝓕 P := by
  exact ⟨stoppedProcess hX.choose τ, hX.choose_spec.1.stoppedProcess hτ, by
    filter_upwards [hX.choose_spec.2] with ω h t
    simp [stoppedProcess, h]⟩


-- @@ L493-498 verbatim
lemma IsAESquareIntegrable.memLp_two_stoppedValue'
    [Approximable 𝓕 P] (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    MemLp (𝓕.stoppedValue' X τ P) 2 P := by
  borelize E
  rw [← memLp_congr_ae (hX.limitProcess_stoppedProcess hτ)]
  exact (hX.stoppedProcess hτ).memLp_limitProcess


-- @@ L500-500 verbatim
end IsSquareIntegrable


-- @@ L502-502 verbatim
section SquareIntegrable


-- @@ L504-504 verbatim
/-! ### The Hilbert space of square integrable martingales -/


-- @@ L506-513 verbatim
/-- A process is a purely discontinuous square integrable martingale if it is square integrable
and orthogonal to every continuous square integrable martingale in the Hilbert space of
square integrable martingales. -/
def IsPurelyDiscontinuous [InnerProductSpace ℝ E]
  (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  IsAESquareIntegrable X 𝓕 P ∧
  ∀ Y, IsAESquareIntegrable Y 𝓕 P → (∀ᵐ ω ∂P, Continuous (Y · ω)) →
    P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] = 0


-- @@ L515-522 expanded
lemma IsPurelyDiscontinuous.congr [InnerProductSpace ℝ E] (hX : IsPurelyDiscontinuous X 𝓕 P)
    (h : Indistinguishable P X Y) : IsPurelyDiscontinuous Y 𝓕 P :=
  by
  refine ⟨hX.1.congr h, fun Z hZ1 hZ2 ↦ ?_⟩
  rw [← hX.2 Z hZ1 hZ2]
  apply integral_congr_ae
  filter_upwards [𝓕.limitProcess_congr h] with ω h
  rw [h]


-- @@ L524-524 verbatim
variable [CompleteSpace E] [IsFiniteMeasure P]


-- @@ L526-526 verbatim
section NormedSpace


-- @@ L528-528 verbatim
variable [NormedSpace ℝ E]


-- @@ L530-537 expanded
variable (E P 𝓕) in
/-- The type of square integrable martingales, as a submodule of equivalence classes of
indistinguishable processes. -/
def squareIntegrableSubmodule : Submodule ℝ (AEEqProcess Ω E 𝓕 P)
    where
  carrier := {X | IsAESquareIntegrable X 𝓕 P}
  add_mem' {X Y} hX hY := (hX.add hY).congr (coeFn_add X Y).symm
  zero_mem' := IsAESquareIntegrable.const.congr coeFn_zero.symm
  smul_mem' c {X} hX := (hX.smul c).congr (coeFn_smul c X).symm


-- @@ L539-541 verbatim
variable (E P 𝓕) in
/-- The type of square integrable martingales up to indistinguishability. -/
def SquareIntegrable : Type _ := squareIntegrableSubmodule E P 𝓕


-- @@ L543-544 verbatim
instance : AddCommGroup (SquareIntegrable E P 𝓕) :=
  AddSubgroupClass.toAddCommGroup (squareIntegrableSubmodule E P 𝓕)


-- @@ L546-547 verbatim
instance : Module ℝ (SquareIntegrable E P 𝓕) :=
  Submodule.module (squareIntegrableSubmodule E P 𝓕)


-- @@ L549-551 verbatim
private
lemma SquareIntegrable.val_add (X Y : SquareIntegrable E P 𝓕) : (X + Y).1 = X.1 + Y.1 :=
  Submodule.coe_add X Y


-- @@ L553-555 verbatim
private
lemma SquareIntegrable.val_sub (X Y : SquareIntegrable E P 𝓕) : (X - Y).1 = X.1 - Y.1 :=
  Submodule.coe_sub _ X Y


-- @@ L557-559 verbatim
private
lemma SquareIntegrable.val_smul (X : SquareIntegrable E P 𝓕) (c : ℝ) : (c • X).1 = c • X.1 :=
  Submodule.coe_smul c X


-- @@ L561-563 verbatim
private
lemma SquareIntegrable.val_neg (X : SquareIntegrable E P 𝓕) : (-X).1 = -X.1 :=
  Submodule.coe_neg _ X


-- @@ L565-567 verbatim
private
lemma SquareIntegrable.val_zero : (0 : SquareIntegrable E P 𝓕).1 = 0 :=
  Submodule.coe_zero


-- @@ L569-571 verbatim
private
lemma SquareIntegrable.val_inj (X Y : SquareIntegrable E P 𝓕) : X = Y ↔ X.1 = Y.1 :=
  Subtype.ext_iff


-- @@ L573-577 verbatim
/-- The equivalence class of a process that is indistinguishable from a square integrable
martingale. -/
noncomputable def SquareIntegrable.mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) :
    SquareIntegrable E P 𝓕 :=
  ⟨.mk X hX.aestronglyAdapted, hX.congr (coeFn_mk X _).symm⟩


-- @@ L579-586 expanded
open scoped Classical in
/-- Given an equivalence class of square integrable martingales, this is a version that satisfies
`IsSquareIntegrable`. Don't use this directly, use the coercion system instead. -/
@[coe]
noncomputable def SquareIntegrable.out (X : SquareIntegrable E P 𝓕) : ι → Ω → E :=
  if h : ∃ Y, (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ Indistinguishable P X.1 Y then
    h.choose
  else X.2.choose


-- @@ L588-589 verbatim
noncomputable instance : CoeFun (SquareIntegrable E P 𝓕) (fun _ ↦ ι → Ω → E) where
  coe := SquareIntegrable.out


-- @@ L591-596 verbatim
lemma SquareIntegrable.isSquareIntegrable_coe (X : SquareIntegrable E P 𝓕) :
    IsSquareIntegrable X 𝓕 P := by
  rw [out]
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact X.2.choose_spec.1


-- @@ L598-599 verbatim
lemma SquareIntegrable.isAESquareIntegrable_coe (X : SquareIntegrable E P 𝓕) :
    IsAESquareIntegrable X 𝓕 P := X.isSquareIntegrable_coe.isAESquareIntegrable


-- @@ L601-606 expanded
lemma SquareIntegrable.val_indist_coe (X : SquareIntegrable E P 𝓕) : Indistinguishable P X.1 ↑X :=
  by
  rw [out]
  split_ifs with h
  · exact h.choose_spec.2.2
  · exact X.2.choose_spec.2


-- @@ L608-613 expanded
@[ext]
lemma SquareIntegrable.ext {X Y : SquareIntegrable E P 𝓕} (h : Indistinguishable P ↑X ↑Y) : X = Y :=
  by
  unfold SquareIntegrable
  ext
  grw [val_indist_coe, val_indist_coe, h]


-- @@ L615-617 expanded
lemma SquareIntegrable.coe_add (X Y : SquareIntegrable E P 𝓕) :
    Indistinguishable P (↑(X + Y)) (↑X + ↑Y) := by
  grw [← val_indist_coe, val_add, coeFn_add, ← val_indist_coe, ← val_indist_coe]


-- @@ L619-621 expanded
lemma SquareIntegrable.coe_sub (X Y : SquareIntegrable E P 𝓕) :
    Indistinguishable P (↑(X - Y)) (↑X - ↑Y) := by
  grw [← val_indist_coe, val_sub, coeFn_sub, val_indist_coe, val_indist_coe]


-- @@ L623-625 expanded
lemma SquareIntegrable.coe_smul (X : SquareIntegrable E P 𝓕) (c : ℝ) :
    Indistinguishable P (↑(c • X)) (c • ↑X) := by
  grw [← val_indist_coe, val_smul, coeFn_smul, val_indist_coe]


-- @@ L627-629 expanded
lemma SquareIntegrable.coe_neg (X : SquareIntegrable E P 𝓕) : Indistinguishable P (↑(-X)) (-↑X) :=
  by grw [← val_indist_coe, val_neg, coeFn_neg, val_indist_coe]


-- @@ L631-633 verbatim
private lemma SquareIntegrable.val_mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P)
    (h : AEStronglyAdapted X 𝓕 P) :
    (mk X hX).1 = .mk X h := rfl


-- @@ L635-637 expanded
lemma SquareIntegrable.mk_indist (hX : IsAESquareIntegrable X 𝓕 P) :
    Indistinguishable P (mk X hX) X := by
  grw [← val_indist_coe, val_mk X hX hX.aestronglyAdapted, coeFn_mk]


-- @@ L639-647 expanded
lemma SquareIntegrable.mk_eq_mk {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} : mk X hX = mk Y hY ↔ Indistinguishable P X Y
    where
  mp
    h := by
    rw [SquareIntegrable.val_inj, mk, mk] at h
    rwa [AEEqProcess.mk_eq_mk] at h
  mpr
    h := by
    ext
    grw [mk_indist, mk_indist, h]


-- @@ L649-653 verbatim
lemma SquareIntegrable.mk_add {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    mk (X + Y) (hX.add hY) = mk X hX + mk Y hY := by
  ext
  grw [mk_indist, coe_add, mk_indist, mk_indist]


-- @@ L655-659 verbatim
lemma SquareIntegrable.mk_sub {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    mk (X - Y) (hX.sub hY) = mk X hX - mk Y hY := by
  ext
  grw [mk_indist, coe_sub, mk_indist, mk_indist]


-- @@ L661-664 expanded
variable (E P 𝓕) in
lemma SquareIntegrable.coe_const (c : E) :
    Indistinguishable P (mk (fun _ _ ↦ c) .const : SquareIntegrable E P 𝓕) (fun _ _ ↦ c) :=
  mk_indist _


-- @@ L666-669 expanded
variable (E P 𝓕) in
lemma SquareIntegrable.coe_zero : Indistinguishable P (0 : SquareIntegrable E P 𝓕) 0 := by
  grw [← val_indist_coe, val_zero, coeFn_zero]


-- @@ L671-671 verbatim
variable [Nonempty ι]


-- @@ L673-680 expanded
open TopologicalSpace in
/-- Two modifications that are right-continuous are indistinguishable. -/
lemma indistinguishable_of_modification' {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E} [TopologicalSpace E] [TopologicalSpace T] [SeparableSpace T] [T2Space E]
    [Preorder T] (hX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) (hY : ∀ᵐ ω ∂P, IsRightContinuous (Y · ω))
    (h : ∀ t, X t =ᵐ[P] Y t) : Indistinguishable P X Y :=
  sorry


-- @@ L682-702 verbatim
variable (E P 𝓕) in
/-- The injection of square integrable martingales into the `L^2` space given by `X ↦ X ∞`.
This is a `LinearIsometryEquiv` onto the subspace of functions that are strongly measurable
with respect to `⨆ t, 𝓕 t`, see `SquareIntegrable.toL2Isom`. -/
noncomputable def SquareIntegrable.toL2 : SquareIntegrable E P 𝓕 →ₗ[ℝ] Lp E 2 P where
  toFun X := (isSquareIntegrable_coe X).memLp_limitProcess.toLp
  map_add' X Y := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_add X Y)),
      MemLp.toLp_congr _ _ (IsAESquareIntegrable.limitProcess_add _ _), MemLp.toLp_add]
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.add
        (isSquareIntegrable_coe Y).memLp_limitProcess
    · exact X.isAESquareIntegrable_coe
    · exact Y.isAESquareIntegrable_coe
    · exact (X.isSquareIntegrable_coe.add Y.isSquareIntegrable_coe).memLp_limitProcess
  map_smul' c X := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_smul X c)),
      MemLp.toLp_congr _ _ (𝓕.limitProcess_smul _ _), MemLp.toLp_const_smul]
    · simp
    · exact (isSquareIntegrable_coe X).memLp_limitProcess
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.const_smul c
    · exact ((isSquareIntegrable_coe X).smul c).memLp_limitProcess


-- @@ L704-705 verbatim
lemma SquareIntegrable.toL2_def (X : SquareIntegrable E P 𝓕) :
    toL2 E P 𝓕 X = (isSquareIntegrable_coe X).memLp_limitProcess.toLp := rfl


-- @@ L707-710 verbatim
lemma SquareIntegrable.toL2_ae_eq (X : SquareIntegrable E P 𝓕) :
    toL2 E P 𝓕 X =ᵐ[P] 𝓕.limitProcess X P := by
  rw [toL2_def]
  exact MemLp.coeFn_toLp _


-- @@ L712-712 verbatim
variable [SeparableSpace ι]


-- @@ L714-735 verbatim
lemma SquareIntegrable.injective_toL2 : Injective (toL2 E P 𝓕) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  rw [toL2_def, ← MemLp.toLp_zero, MemLp.toLp_eq_toLp_iff] at hX
  swap; · simp
  ext
  refine .trans ?_ (coe_zero _ _ _).symm
  refine indistinguishable_of_modification' ?_ ?_ fun t ↦ ?_
  · exact ae_of_all _ fun _ ↦ (isSquareIntegrable_coe _).cadlag _
      |>.right_continuous
  · exact ae_of_all _ fun _ ↦ isRightContinuous_const 0
  grw [show (0 : ι → Ω → E) t = 0 from rfl, ← lpNorm_eq_zero _ two_ne_zero, ← toReal_eLpNorm,
    ENNReal.toReal_eq_zero_iff]
  · left
    suffices eLpNorm (X t) 2 P ≤ 0 by simp_all
    grw [le_iSup fun s ↦ eLpNorm (X s) 2 P,
      (isSquareIntegrable_coe _).iSup_eLpNorm_eq_eLpNorm_limitProcess, nonpos_iff_eq_zero,
      ← ofReal_lpNorm, ENNReal.ofReal_eq_zero, lpNorm_congr hX, lpNorm_zero]
    exact (isSquareIntegrable_coe _).memLp_limitProcess
  · exact ((isSquareIntegrable_coe X).martingale.stronglyMeasurable
      t).aestronglyMeasurable.mono (𝓕.le t)
  · exact (isSquareIntegrable_coe X).memLp_two t


-- @@ L737-739 verbatim
noncomputable instance :
    NormedAddCommGroup (SquareIntegrable E P 𝓕) :=
  NormedAddCommGroup.induced _ _ (SquareIntegrable.toL2 E P 𝓕) SquareIntegrable.injective_toL2


-- @@ L741-745 verbatim
lemma SquareIntegrable.norm_def {X : SquareIntegrable E P 𝓕} :
    ‖X‖ = lpNorm (𝓕.limitProcess X P) 2 P := by
  change ‖toL2 E P 𝓕 X‖ = _
  rw [toL2_def, Lp.norm_toLp, lpNorm, if_pos]
  exact 𝓕.stronglyMeasurable_limit_process'.aestronglyMeasurable


-- @@ L747-750 verbatim
lemma SquareIntegrable.enorm_def {X : SquareIntegrable E P 𝓕} :
    ‖X‖ₑ = eLpNorm (𝓕.limitProcess X P) 2 P := by
  rw [← ofReal_norm, norm_def, ofReal_lpNorm]
  exact (isSquareIntegrable_coe X).memLp_limitProcess


-- @@ L752-752 verbatim
end NormedSpace


-- @@ L754-754 verbatim
section InnerProductSpace


-- @@ L756-756 verbatim
variable [InnerProductSpace ℝ E] [Nonempty ι] [SeparableSpace ι]


-- @@ L758-760 verbatim
noncomputable instance :
    InnerProductSpace ℝ (SquareIntegrable E P 𝓕) :=
  InnerProductSpace.induced (SquareIntegrable.toL2 E P 𝓕)


-- @@ L762-768 verbatim
lemma SquareIntegrable.inner_def {X Y : SquareIntegrable E P 𝓕} :
    ⟪X, Y⟫ = P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] := by
  rw [inner_induced_eq, toL2_def, toL2_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(isSquareIntegrable_coe X).memLp_limitProcess.coeFn_toLp,
    (isSquareIntegrable_coe Y).memLp_limitProcess.coeFn_toLp] with ω h1 h2
  simp_all


-- @@ L770-778 verbatim
lemma IsAESquareIntegrable.inner_limitProcess_eq (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] =
      ⟪SquareIntegrable.mk X hX, .mk Y hY⟫ := by
  rw [SquareIntegrable.inner_def]
  apply integral_congr_ae
  filter_upwards [𝓕.limitProcess_congr (SquareIntegrable.mk_indist hX),
    𝓕.limitProcess_congr (SquareIntegrable.mk_indist hY)] with ω h1 h2
  simp_all


-- @@ L780-782 verbatim
/-- Given a martingale `X`, this is a càdlàg martingale that is a modification of `X`. -/
def _root_.MeasureTheory.modif (X : ι → Ω → E) :
    ι → Ω → E := sorry


-- @@ L784-785 verbatim
lemma _root_.MeasureTheory.isCadlag_modif (X : ι → Ω → E) (ω : Ω) :
    IsCadlag (modif X · ω) := sorry


-- @@ L787-788 verbatim
lemma _root_.MeasureTheory.modification_modif (hX : Martingale X 𝓕 P) (t : ι) :
    modif X t =ᵐ[P] X t := sorry


-- @@ L790-790 verbatim
lemma _root_.MeasureTheory.martingale_modif : Martingale (modif X) 𝓕 P := sorry


-- @@ L792-800 verbatim
variable (𝓕) in
lemma isSquareIntegrable_modif_condExp {X : Ω → E} (hX : MemLp X 2 P) :
    IsSquareIntegrable (modif (fun t ↦ P[X | 𝓕 t])) 𝓕 P where
  martingale := martingale_modif
  cadlag := isCadlag_modif _
  bounded := by
    refine (iSup_le fun i ↦ ?_).trans_lt hX.2
    grw [eLpNorm_congr_ae (modification_modif (martingale_condExp X 𝓕 P) i),
      eLpNorm_condExp_le_eLpNorm _ (by simp)]


-- @@ L802-841 verbatim
/-- The `LinearIsometryEquiv` between square integrable martingales and
the type of `L^2` random variables that are strongly measurable with respect to `⨆ t, 𝓕 t`,
given by `X ↦ X ∞`. -/
noncomputable def SquareIntegrable.toL2Isom [OrderTopology ι] :
    SquareIntegrable E P 𝓕 ≃ₗᵢ[ℝ] lpMeas E ℝ (⨆ t, 𝓕 t) 2 P where
  toFun X := ⟨toL2 E P 𝓕 X, by
    rw [mem_lpMeas_iff_aestronglyMeasurable, aestronglyMeasurable_congr (toL2_ae_eq X)]
    exact 𝓕.stronglyMeasurable_limitProcess.aestronglyMeasurable
  ⟩
  invFun X := mk (modif (fun t ↦ P[X.1 | 𝓕 t]))
    (isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp X.1)).isAESquareIntegrable
  map_add' := by simp
  map_smul' := by simp
  left_inv X := by
    ext
    refine indistinguishable_of_modification' ?_ ?_ (fun t ↦ ?_)
    · exact ae_of_all _ (isSquareIntegrable_coe _).isRightContinuous
    · exact ae_of_all _ (isSquareIntegrable_coe _).isRightContinuous
    simp only
    grw [(mk_indist ?_).ae_eq_eval, modification_modif, toL2_def, MemLp.coeFn_toLp,
      X.isSquareIntegrable_coe.condExp_limitProcess_ae_eq]
    · exact martingale_condExp _ _ _
    · exact isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp _) |>.isAESquareIntegrable
  right_inv X := by
    ext
    simp only
    grw [toL2_def, MemLp.coeFn_toLp, 𝓕.limitProcess_congr (mk_indist _)]
    obtain ⟨u, hu⟩ := (atTop : Filter ι).exists_seq_tendsto
    have h1 : ∀ᵐ ω ∂P, ∀ n, modif (fun t ↦ P[X.1 | 𝓕 t]) (u n) ω = P[X.1 | 𝓕 (u n)] ω := by
      rw [ae_all_iff]
      exact fun _ ↦ modification_modif (martingale_condExp X.1 𝓕 P) _
    filter_upwards [h1,
      (isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp X.1)).ae_tendsto_limitProcess,
      tendsto_ae_condExp' 𝓕 X.1,
      condExp_of_aestronglyMeasurable' (iSup_le 𝓕.le) X.2
        ((Lp.memLp X.1).integrable (by simp))] with ω h1 h2 h3 h4
    rw [← h4]
    apply tendsto_nhds_unique ?_ (h3.comp hu)
    apply Tendsto.congr h1 (h2.comp hu)
  norm_map' X := rfl


-- @@ L843-845 verbatim
instance [OrderTopology ι] : CompleteSpace (SquareIntegrable E P 𝓕) :=
  haveI : Fact (⨆ t, 𝓕 t ≤ mΩ) := ⟨iSup_le 𝓕.le⟩
  SquareIntegrable.toL2Isom.toIsometryEquiv.completeSpace


-- @@ L847-847 verbatim
end InnerProductSpace


-- @@ L849-849 verbatim
end SquareIntegrable


-- @@ L851-851 verbatim
section LocallySquareIntegrable


-- @@ L853-853 verbatim
variable [NormedSpace ℝ E]


-- @@ L855-859 verbatim
/-- A stochastic process is locally square-integrable if it satisfies the square-integrable
martingale property locally. -/
def IsLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ IsSquareIntegrable Y 𝓕 P) 𝓕 X P


-- @@ L861-864 verbatim
lemma IsSquareIntegrable.isLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (hX : IsSquareIntegrable X 𝓕 P) :
    IsLocallySquareIntegrable X 𝓕 P :=
  Locally.of_prop hX


-- @@ L866-884 verbatim
/-- A locally square-integrable martingale has locally submartingale squared norm. -/
lemma IsLocallySquareIntegrable.isLocalSubmartingale_sq_norm [SigmaFiniteFiltration P 𝓕]
    [OrderBot ι] [OrderTopology ι] [CompleteSpace E]
    (hX : IsLocallySquareIntegrable X 𝓕 P) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  have h_stopped_sq_norm {τ : Ω → WithTop ι} :
      stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ ‖X t ω‖ ^ 2)) τ =
        fun t ω ↦ ‖stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω‖ ^ 2 := by
    ext t ω
    by_cases hτ : ⊥ < τ ω <;> simp [stoppedProcess, hτ]
  unfold IsLocalSubmartingale
  change Locally (fun Y : ι → Ω → ℝ ↦ Submartingale Y 𝓕 P ∧
      ∀ ω, IsCadlag (Y · ω)) 𝓕 (fun t ω ↦ ‖X t ω‖ ^ 2) P
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  have hXn := hX.stoppedProcess_localSeq n
  constructor
  · simpa [h_stopped_sq_norm] using hXn.submartingale_sq_norm
  · intro ω
    simpa [h_stopped_sq_norm] using IsCadlag.norm_sq (hXn.cadlag ω)


-- @@ L886-886 verbatim
end LocallySquareIntegrable


-- @@ L888-888 verbatim
end LinearOrder


-- @@ L890-890 verbatim
section ConditionallyCompleteLinearOrderBot


-- @@ L892-895 verbatim
variable [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedSpace ℝ E]
  {X : ι → Ω → E} {𝓕 : Filtration ι mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous] [IsFiniteMeasure P]
  [Approximable 𝓕 P]


-- @@ L897-902 verbatim
@[simp]
lemma isLocallySquareIntegrable_of_isEmpty [IsEmpty Ω]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) :
    IsLocallySquareIntegrable X 𝓕 P := by
  refine IsSquareIntegrable.isLocallySquareIntegrable ?_
  exact isSquareIntegrable_of_isEmpty _ _ _


-- @@ L904-940 expanded
lemma _root_.MeasureTheory.Martingale.isLocallySquareIntegrable_of_jump_le [PolishSpace ι]
    [CompleteSpace E] (hX : Martingale X 𝓕 P) (h_cadlag : ∀ ω, IsCadlag (X · ω)) {C : ℝ}
    (h_jump : ∀ t ω, ‖Function.jump (X · ω) t‖ ≤ C) : IsLocallySquareIntegrable X 𝓕 P :=
  by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact isLocallySquareIntegrable_of_isEmpty _ _ _
  let τ : ℕ → Ω → WithTop ι := fun n ↦ leastGE (fun i ω ↦ ‖X i ω‖) n
  refine
    ⟨τ, isLocalizingSequence_leastGE 𝓕 hX.stronglyAdapted.norm (fun ω ↦ (h_cadlag ω).norm), fun n ↦
      ?_⟩
  let Y := (stoppedProcess (fun i ↦ {ω | ⊥ < τ n ω}.indicator (X i)) (τ n))
  have hX_lt {t : ι} {ω : Ω} (ht : t < τ n ω) : ‖X t ω‖ < n :=
    by
    unfold τ leastGE at ht
    have := notMem_of_lt_hittingAfter ht (by simp)
    grind
  have hY_le t ω : ‖Y t ω‖ ≤ (n : ℝ) + ‖Function.jump (X · ω) (τ n ω).untopA‖ :=
    stoppedAtNorm_le_add_jump h_cadlag t ω (by simp)
  borelize ι E
  have h_stop : IsStoppingTime 𝓕 (τ n) :=
    by
    refine isStoppingTime_leastGE P (IsStronglyProgressive.norm ?_) (n : ℝ) (𝓕 := 𝓕)
    exact
      StronglyAdapted.isStronglyProgressive_of_rightContinuous hX.stronglyAdapted fun ω ↦
        (h_cadlag ω).right_continuous
  refine
    isSquareIntegrable_of_le_const (C := NNReal.mk (P.real .univ ^ (2 : ℝ)⁻¹ * (n + C)) ?_) ?_ ?_
      fun i ↦ ?_
  · exact hX.stoppedProcess_indicator (fun ω ↦ (h_cadlag ω).right_continuous) h_stop
  · exact isStable_isCadlag (𝓕 := 𝓕) X h_cadlag (τ n) h_stop
  · suffices 0 ≤ C by positivity
    let ω₀ := hΩ.some
    specialize h_jump ⊥ ω₀
    exact (norm_nonneg _).trans h_jump
  · rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, ENNReal.ofReal_mul (by positivity), ←
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), Measure.real_def,
      ENNReal.ofReal_toReal (by simp)]
    refine eLpNorm_le_of_ae_bound (ae_of_all _ fun ω ↦ ?_)
    grw [hY_le _ ω]
    gcongr
    exact h_jump _ _


-- @@ L942-954 verbatim
lemma _root_.MeasureTheory.Martingale.isLocallySquareIntegrable_of_continuous
    [PolishSpace ι] [CompleteSpace E] [DenselyOrdered ι]
    (hX : Martingale X 𝓕 P) (h_cont : ∀ ω, Continuous (X · ω)) :
    IsLocallySquareIntegrable X 𝓕 P := by
  refine hX.isLocallySquareIntegrable_of_jump_le (fun ω ↦ (h_cont ω).isCadlag) (fun t ω ↦ ?_)
    (C := 0)
  by_cases hτ_bot : t = ⊥
  · simp [hτ_bot]
  rw [(h_cont ω).continuousAt.jump_eq_zero]
  · simp
  · suffices (𝓝[<] t).NeBot from this.ne
    refine nhdsLT_neBot_of_exists_lt ?_
    exact ⟨⊥, by grind⟩


-- @@ L956-967 verbatim
lemma isStable_isSquareIntegrable
    [PolishSpace ι] [CompleteSpace E] [SecondCountableTopology E] [DenselyOrdered ι] :
    IsStable 𝓕 fun X : ι → Ω → E ↦ IsSquareIntegrable X 𝓕 P := by
  borelize ι E
  have h_iff (X : ι → Ω → E) : IsSquareIntegrable X 𝓕 P ↔
      ((Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω)) ∧ ⨆ i, eLpNorm (X i) 2 P < ∞) :=
    ⟨fun h ↦ ⟨⟨h.martingale, h.cadlag⟩, h.bounded⟩, fun h ↦ ⟨h.1.1, h.1.2, h.2⟩⟩
  simp_rw [h_iff]
  refine IsStable.and isStable_martingale ?_
  intro X hX τ hτ
  -- 6.11.1 in He et al., using 6.8.1
  sorry


-- @@ L969-1011 expanded
omit [NormedSpace ℝ E] [𝓕.IsRightContinuous] in
lemma isStable_jump_le {C : ℝ} (hC : 0 ≤ C) :
    IsStable 𝓕 fun X : ι → Ω → E ↦ ∀ t ω, ‖Function.jump (X · ω) t‖ ≤ C :=
  by
  suffices IsStable 𝓕 fun X ↦ ∀ ω i, ‖Function.jump (X · ω) i‖ ≤ C
    by
    convert this
    exact ⟨fun h i ω ↦ h ω i, fun h ω i ↦ h i ω⟩
  refine isStable_pathwise (fun (X : ι → E) i ↦ ‖Function.jump X i‖ ≤ C) (𝓕 := 𝓕) (fun i ↦ ?_) ?_ ?_
  · simp [hC]
  · intro X i hX j hij
    cases lt_or_eq_of_le hij with
    | inl hij =>
      suffices Function.jump (fun x ↦ X (min x i)) j = 0 by simp [this, hC]
      unfold jump
      split_ifs with h
      · simp only [hij.le, inf_of_le_right]
        rw [min_eq_right]
        · simp
        · by_contra! h_lt
          have h_covBy := h.choose_spec.2 h_lt
          grind
      · have ht_ne_bot : 𝓝[<] j ≠ ⊥ := by
          rw [ne_eq, nhdsLT_eq_bot_iff]
          simp only [isBot_iff_eq_bot, h, or_false]
          intro ht_bot
          simp [ht_bot] at hij
        simp only [hij.le, inf_of_le_right]
        rw [leftLim_congr' (g := fun _ ↦ X i)]
        · have : (𝓝[<] j).NeBot := ⟨ht_ne_bot⟩
          simp [leftLim_eq_of_tendsto (y := X i) tendsto_const_nhds]
        · exact ht_ne_bot
        · rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards [eventually_gt_nhds hij] with s hsτ hst
          rw [min_eq_right]
          exact hsτ.le
        · rw [min_eq_right hij.le]
    | inr h =>
      convert hX j using 2
      rw [jump_congr]
      grind
  · intro X Y i ⟨k, hik, hk⟩
    rw [jump_congr]
    intro s hsi
    exact hk s (hsi.trans_lt hik)


-- @@ L1013-1025 expanded
omit [NormedSpace ℝ E] [𝓕.IsRightContinuous] [IsFiniteMeasure P] [Approximable 𝓕 P] in
lemma locally_jump_le_iff {C : ℝ} (hC : 0 ≤ C) {X : ι → Ω → E} :
    Locally (fun X ↦ ∀ t ω, ‖Function.jump (X · ω) t‖ ≤ C) 𝓕 X P ↔
      ∀ᵐ ω ∂P, ∀ t, ‖Function.jump (X · ω) t‖ ≤ C :=
  by
  have h :=
    locally_iff_ae (fun (X : ι → E) t ↦ ‖Function.jump X t‖ ≤ C) ?_ ?_ (𝓕 := 𝓕) (P := P) (X := X)
  rotate_left
  · simp [hC]
  · intro X Y i ⟨k, hik, hk⟩
    rw [jump_congr]
    intro s hsi
    exact hk s (hsi.trans_lt hik)
  rw [← h]
  congr!
  exact ⟨fun h ω t ↦ h t ω, fun h t ω ↦ h ω t⟩


-- @@ L1027-1040 expanded
lemma IsLocalMartingale.isLocallySquareIntegrable_of_jump_le [DenselyOrdered ι] [NoMaxOrder ι]
    [PolishSpace ι] [SecondCountableTopology E] [CompleteSpace E] (hX : IsLocalMartingale X 𝓕 P)
    {C : ℝ} (hC : 0 ≤ C) (h_jump : ∀ᵐ ω ∂P, ∀ t, ‖Function.jump (X · ω) t‖ ≤ C) :
    IsLocallySquareIntegrable X 𝓕 P := by
  borelize ι E
  rw [← locally_jump_le_iff (𝓕 := 𝓕) hC] at h_jump
  refine
    IsStable.locally_induction₂ (r := fun X : ι → Ω → E ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω))
      (p := fun X : ι → Ω → E ↦ ∀ t ω, ‖Function.jump (X · ω) t‖ ≤ C) ?_ isStable_martingale
      (isStable_jump_le hC) isStable_isSquareIntegrable hX h_jump
  intro X hX hX_jump
  exact hX.1.isLocallySquareIntegrable_of_jump_le hX.2 hX_jump


-- @@ L1042-1054 verbatim
lemma IsLocalMartingale.isLocallySquareIntegrable_of_continuous [DenselyOrdered ι]
    [NoMaxOrder ι] [PolishSpace ι]
    [SecondCountableTopology E] [CompleteSpace E]
    (hX : IsLocalMartingale X 𝓕 P) (h_cont : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    IsLocallySquareIntegrable X 𝓕 P := by
  borelize ι E
  rw [← locally_continuous_iff (𝓕 := 𝓕)] at h_cont
  refine IsStable.locally_induction₂
    (r := fun X : ι → Ω → E ↦ Martingale X 𝓕 P ∧ ∀ ω, IsCadlag (X · ω))
    (p := fun X : ι → Ω → E ↦ ∀ ω, Continuous (X · ω)) ?_ isStable_martingale
    isStable_continuous isStable_isSquareIntegrable hX h_cont
  intro X hX hX_cont
  exact hX.1.isLocallySquareIntegrable_of_continuous hX_cont


-- @@ L1056-1056 verbatim
end ConditionallyCompleteLinearOrderBot


-- @@ L1058-1058 verbatim
end ProbabilityTheory
