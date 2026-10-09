import OAI.Analysis.Daugavet.Recovery


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L7-7 verbatim
open scoped ENNReal NNReal Topology BigOperators


-- @@ L9-9 verbatim
universe uB uR uIota uKappa uBeta


-- @@ L11-11 verbatim
namespace ExactModuli.KW


-- @@ L13-15 verbatim
instance kwMeasure_probability : IsProbabilityMeasure kwMeasure := by
  unfold kwMeasure
  infer_instance


-- @@ L17-17 verbatim
abbrev KWL1 := Lp ℝ 1 kwMeasure


-- @@ L19-22 verbatim
/-- Coordinate restriction induces an actual L1 linear isometry. -/
def coordinatesL1 {ι : Type uIota} [Fintype ι] (c : ι → ℕ) (hc : Function.Injective c) :
    Lp ℝ 1 (cubeMeasure ι) →ₗᵢ[ℝ] KWL1 :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (finite_coordinates_mp c hc)


-- @@ L24-27 verbatim
/-- A common finite family of coordinates determines the whole subspace. -/
def FiniteCoordinates (G : Submodule ℝ KWL1) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℕ) (hc : Function.Injective c),
    G ≤ (coordinatesL1 c hc).toLinearMap.range


-- @@ L29-56 verbatim
lemma extend_coordinates {ι : Type uIota} {κ : Type uKappa} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (hc : Function.Injective c) :
    ∃ d : ι ⊕ κ → ℕ, Function.Injective d ∧ ∀ i, d (Sum.inl i) = c i := by
  classical
  let N := (Finset.univ.sup c) + 1
  have hbound (i : ι) : c i < N := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  let d : ι ⊕ κ → ℕ := Sum.elim c (fun j => N + (Fintype.equivFin κ j).val)
  refine ⟨d, ?_, fun i => rfl⟩
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (hc hij)
    | inr j =>
      have := hbound i
      change c i = N + (Fintype.equivFin κ j).val at hij
      omega
  | inr i =>
    cases j with
    | inl j =>
      have := hbound j
      change N + (Fintype.equivFin κ i).val = c j at hij
      omega
    | inr j =>
      apply congrArg Sum.inr
      apply (Fintype.equivFin κ).injective
      apply Fin.ext
      exact Nat.add_left_cancel hij


-- @@ L58-64 verbatim
lemma curry_mp {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι] :
    MeasurePreserving (fun v : cube (κ × ι) => fun k j => v (k,j))
      (cubeMeasure (κ × ι)) (arrayMeasure κ ι) := by
  refine ⟨by fun_prop, ?_⟩
  have h := Measure.infinitePi_map_curry (fun _ : κ => fun _ : ι => (volume : Measure unitInterval))
  simp only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_curry] at h
  exact h


-- @@ L66-68 verbatim
def splitCoordinates {β : Type uBeta} {κ : Type uKappa} {ι : Type uIota}
    (v : cube (β ⊕ (κ × ι))) : cube β × (κ → cube ι) :=
  (fun b => v (Sum.inl b), fun k j => v (Sum.inr (k,j)))


-- @@ L70-75 verbatim
lemma splitCoordinates_mp {β : Type uBeta} {κ : Type uKappa} {ι : Type uIota}
    [Fintype β] [Fintype κ] [Fintype ι] :
    MeasurePreserving (splitCoordinates : cube (β ⊕ (κ × ι)) → cube β × (κ → cube ι))
      (cubeMeasure (β ⊕ (κ × ι))) ((cubeMeasure β).prod (arrayMeasure κ ι)) := by
  exact ((MeasurePreserving.id (cubeMeasure β)).prod curry_mp).comp
    (measurePreserving_sumPiEquivProdPi (fun _ : β ⊕ (κ × ι) => (volume : Measure unitInterval)))


-- @@ L77-77 verbatim
section L1Tools

-- @@ L78-79 verbatim
variable {B : Type uB} {R : Type uR} [MeasurableSpace B] [MeasurableSpace R]
  {μ : Measure B} {ν : Measure R}


-- @@ L81-82 verbatim
def integrableL1 (f : B → ℝ) (hf : Integrable f μ) : Lp ℝ 1 μ :=
  (memLp_one_iff_integrable.mpr hf).toLp f


-- @@ L84-85 verbatim
lemma integrableL1_ae (f : B → ℝ) (hf : Integrable f μ) :
    integrableL1 f hf =ᵐ[μ] f := MemLp.coeFn_toLp _


-- @@ L87-90 verbatim
lemma L1_norm_of_ae (f : Lp ℝ 1 μ) {g : B → ℝ} (hg : f =ᵐ[μ] g) :
    ‖f‖ = ∫ b, |g b| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (hg.fun_comp abs)


-- @@ L92-93 verbatim
lemma norm_integrableL1 (f : B → ℝ) (hf : Integrable f μ) :
    ‖integrableL1 f hf‖ = ∫ b, |f b| ∂μ := L1_norm_of_ae _ (integrableL1_ae _ _)


-- @@ L95-105 verbatim
lemma coeFn_L1_sum {ι : Type uIota} (s : Finset ι) (f : ι → Lp ℝ 1 μ) :
    (∑ i ∈ s, f i : Lp ℝ 1 μ) =ᵐ[μ] fun b => ∑ i ∈ s, f i b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 1 μ
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with b hb hb'
    simpa only [Pi.add_apply, hb'] using hb


-- @@ L107-112 verbatim
lemma coeFn_L1_smul_sum {ι : Type uIota} [Fintype ι] (a : ι → ℝ) (f : ι → Lp ℝ 1 μ) :
    (∑ i, a i • f i : Lp ℝ 1 μ) =ᵐ[μ] fun b => ∑ i, a i * f i b := by
  filter_upwards [coeFn_L1_sum Finset.univ (fun i => a i • f i),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (f i))] with b hb hbi
  rw [hb]
  exact Finset.sum_congr rfl (fun i _ => by simpa using hbi i)


-- @@ L114-114 verbatim
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]


-- @@ L116-117 verbatim
def oldL1 : Lp ℝ 1 μ →ₗᵢ[ℝ] Lp ℝ 1 (μ.prod ν) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst


-- @@ L119-121 verbatim
omit [IsProbabilityMeasure μ] in
lemma oldL1_ae [IsProbabilityMeasure μ] (f : Lp ℝ 1 μ) :
    oldL1 (ν := ν) f =ᵐ[μ.prod ν] fun z => f z.1 := Lp.coeFn_compMeasurePreserving f _


-- @@ L123-123 verbatim
end L1Tools

-- @@ L124-124 verbatim
end ExactModuli.KW


-- @@ L126-126 verbatim
end


-- @@ L128-128 verbatim
end OAI
