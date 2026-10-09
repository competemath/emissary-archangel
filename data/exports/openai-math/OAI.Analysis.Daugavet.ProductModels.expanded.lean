import OAI.Analysis.Daugavet.HeavyTails


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L7-7 verbatim
open scoped ENNReal NNReal Topology BigOperators


-- @@ L9-9 verbatim
universe uIota uKappa uBeta uAlpha uGamma


-- @@ L11-11 verbatim
namespace ExactModuli.KW


-- @@ L13-13 verbatim
section ProductModels


-- @@ L15-15 verbatim
abbrev cube (ι : Type uIota) := ι → unitInterval

-- @@ L16-17 verbatim
abbrev cubeMeasure (ι : Type uIota) [Fintype ι] : Measure (cube ι) :=
  Measure.pi (fun _ => (volume : Measure unitInterval))

-- @@ L18-19 verbatim
abbrev pairCubeMeasure (ι : Type uIota) [Fintype ι] : Measure (ι → unitInterval × unitInterval) :=
  Measure.pi (fun _ => pairedMeasure)

-- @@ L20-22 verbatim
abbrev arrayMeasure (κ : Type uKappa) (ι : Type uIota) [Fintype κ] [Fintype ι] :
    Measure (κ → cube ι) :=
  Measure.pi (fun _ => cubeMeasure ι)

-- @@ L23-25 verbatim
abbrev pairedArrayMeasure (κ : Type uKappa) (ι : Type uIota) [Fintype κ] [Fintype ι] :
    Measure (κ → ι → unitInterval × unitInterval) :=
  Measure.pi (fun _ => pairCubeMeasure ι)


-- @@ L27-32 verbatim
lemma mp_integral {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have hm : AEStronglyMeasurable g (μ.map f) := hf.map_eq.symm ▸ hg
  exact (integral_map hf.aemeasurable hm).symm.trans (congrArg (fun P => ∫ y, g y ∂P) hf.map_eq)


-- @@ L34-39 verbatim
lemma mp_ident {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    {g : β → γ} (hg : Measurable g) : IdentDistrib (g ∘ f) g μ ν := by
  refine ⟨(hg.comp hf.measurable).aemeasurable, hg.aemeasurable, ?_⟩
  rw [← Measure.map_map hg hf.measurable, hf.map_eq]


-- @@ L41-41 verbatim
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]


-- @@ L43-43 verbatim
def rowSum (p : ℝ) (a : ι → ℝ) (v : cube ι) : ℝ := ∑ j, a j * multiplier p (v j)


-- @@ L45-46 verbatim
def diffRowSum (p : ℝ) (a : ι → ℝ) (v : ι → unitInterval × unitInterval) : ℝ :=
  ∑ j, a j * difference p (v j)


-- @@ L48-50 verbatim
lemma measurable_rowSum (p : ℝ) (a : ι → ℝ) : Measurable (rowSum p a) := by
  unfold rowSum
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul ((measurable_multiplier p).comp (measurable_pi_apply j)))


-- @@ L52-54 verbatim
lemma measurable_diffRowSum (p : ℝ) (a : ι → ℝ) : Measurable (diffRowSum p a) := by
  unfold diffRowSum
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul ((measurable_difference p).comp (measurable_pi_apply j)))


-- @@ L56-61 verbatim
lemma integrable_rowSum {p : ℝ} (hp : 1 < p) (a : ι → ℝ) :
    Integrable (rowSum p a) (cubeMeasure ι) := by
  apply integrable_finsetSum
  intro j _
  exact ((measurePreserving_eval (fun _ : ι => (volume : Measure unitInterval)) j).integrable_comp (integrable_multiplier hp).aestronglyMeasurable
    |>.mpr (integrable_multiplier hp)).const_mul _


-- @@ L63-68 verbatim
lemma integrable_diffRowSum {p : ℝ} (hp : 1 < p) (a : ι → ℝ) :
    Integrable (diffRowSum p a) (pairCubeMeasure ι) := by
  apply integrable_finsetSum
  intro j _
  exact ((measurePreserving_eval (fun _ : ι => pairedMeasure) j).integrable_comp (integrable_difference hp).aestronglyMeasurable
    |>.mpr (integrable_difference hp)).const_mul _


-- @@ L70-76 verbatim
lemma diffRowSum_lower {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2) (a : ι → ℝ) :
    coefficientNorm p a / 54 ≤ ∫ v, |diffRowSum p a v| ∂pairCubeMeasure ι := by
  apply heavy_tail_lower (μ := pairCubeMeasure ι) (fun j v => difference p (v j))
    (fun j => (measurable_difference p).comp (measurable_pi_apply j))
    (iIndepFun_pi (fun _ => (measurable_difference p).aemeasurable)) hp hpmax
  intro j
  exact mp_ident (measurePreserving_eval (fun _ : ι => pairedMeasure) j) (measurable_difference p)


-- @@ L78-85 verbatim
lemma diffRowSum_tail {p : ℝ} (hp : 1 < p) (hpmax : p ≤ 3/2) (a : ι → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (pairCubeMeasure ι).real {v | r < |diffRowSum p a v|} ≤
      10 * (scale p * coefficientNorm p a / r) ^ p := by
  apply heavy_tail_upper (μ := pairCubeMeasure ι) (fun j v => difference p (v j))
    (fun j => (measurable_difference p).comp (measurable_pi_apply j))
    (iIndepFun_pi (fun _ => (measurable_difference p).aemeasurable)) hp hpmax
    (fun j => mp_ident (measurePreserving_eval (fun _ : ι => pairedMeasure) j) (measurable_difference p)) a hr


-- @@ L87-89 verbatim
/-- Select, independently at every row, one of each pair of resampled coordinates. -/
def selectRows (b : κ → Bool) (v : κ → ι → unitInterval × unitInterval) : κ → cube ι :=
  fun k j => if b k then (v k j).2 else (v k j).1


-- @@ L91-104 verbatim
lemma measurePreserving_selectRows (b : κ → Bool) :
    MeasurePreserving (selectRows (ι := ι) b) (pairedArrayMeasure κ ι) (arrayMeasure κ ι) := by
  unfold selectRows
  apply measurePreserving_pi (fun _ : κ => pairCubeMeasure ι) (fun _ : κ => cubeMeasure ι)
    (f := fun k v j => if b k then (v j).2 else (v j).1)
  intro k
  apply measurePreserving_pi (fun _ : ι => pairedMeasure) (fun _ : ι => (volume : Measure unitInterval))
    (f := fun _ v => if b k then v.2 else v.1)
  intro j
  by_cases hb : b k = true
  · simpa [selectRows, hb] using (measurePreserving_snd :
      MeasurePreserving Prod.snd pairedMeasure (volume : Measure unitInterval))
  · simpa [selectRows, hb] using (measurePreserving_fst :
      MeasurePreserving Prod.fst pairedMeasure (volume : Measure unitInterval))


-- @@ L106-106 verbatim
end ProductModels

-- @@ L107-107 verbatim
end ExactModuli.KW


-- @@ L109-109 verbatim
end


-- @@ L111-111 verbatim
end OAI
