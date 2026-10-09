import OAI.Analysis.NumericalRange.FourierResolution


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe u_44


-- @@ L9-9 verbatim
open Set Filter Metric Complex

-- @@ L10-10 verbatim
open scoped Topology ComplexConjugate

-- @@ L11-11 verbatim
open MeasureTheory Set Complex

-- @@ L12-12 verbatim
open scoped Topology Real

-- @@ L13-13 verbatim
open MeasureTheory Set Metric Complex Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
open MeasureTheory Set Filter

-- @@ L16-16 verbatim
open scoped ENNReal NNReal InnerProductSpace

-- @@ L17-17 verbatim
open scoped ComplexConjugate InnerProductSpace


-- @@ L19-19 verbatim
namespace CompleteCrouzeix


-- @@ L21-21 verbatim
section

-- @@ L22-22 verbatim
open MeasureTheory Set Complex

-- @@ L23-23 verbatim
open scoped Topology InnerProductSpace ComplexConjugate

-- @@ L24-24 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


-- @@ L26-27 verbatim
def circleTest (f : C(UnitAddCircle,ℂ)) : CircleL2 →L[ℂ] ℂ :=
  innerSL ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (star f))


-- @@ L29-37 verbatim
lemma circleTest_apply (f : C(UnitAddCircle,ℂ)) (u : CircleL2) :
    circleTest f u = ∫ t, f t * u t ∂AddCircle.haarAddCircle := by
  change inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (star f)) u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
    (p := 2) (𝕜 := ℂ) (star f)] with t ht
  rw [ht]
  simp [RCLike.inner_apply, mul_comm]


-- @@ L39-42 verbatim
lemma circleTest_add (f g : C(UnitAddCircle,ℂ)) :
    circleTest (f+g) = circleTest f+circleTest g := by
  ext u
  simp only [circleTest, star_add, map_add, add_apply]


-- @@ L44-49 verbatim
lemma circleTest_fourier (f : C(UnitAddCircle,ℂ)) (n : ℤ) :
    circleTest f (fourierLp 2 n) = ∫ t, f t * fourier n t ∂AddCircle.haarAddCircle := by
  rw [circleTest_apply]
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 2 n] with t ht
  rw [ht]


-- @@ L51-57 verbatim
lemma circleCLM_ext {E : Type u_44} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {L J : CircleL2 →L[ℂ] E} (h : ∀ n : ℤ, L (fourierLp 2 n) = J (fourierLp 2 n)) : L = J := by
  apply ContinuousLinearMap.ext_on (s := Set.range (fourierLp (T := 1) 2))
  · change ∀ x, x ∈ (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2))).topologicalClosure
    rw [span_fourierLp_closure_eq_top (by norm_num : (2 : ENNReal) ≠ ∞)]
    intro x; trivial
  · rintro _ ⟨n,rfl⟩; exact h n


-- @@ L59-73 verbatim
lemma circleTest_const_positive :
    (circleTest (1 : C(UnitAddCircle,ℂ))).comp (scalarFourier.proj 1) = 0 := by
  apply circleCLM_ext
  intro n
  simp only [ContinuousLinearMap.comp_apply, scalarFourier_fourier,
    zero_apply]
  split_ifs with hn
  · have hn' : 0 < n := by
      by_contra hnonpos
      by_cases hzero : n = 0
      · simp [frequencyPart, hzero] at hn
      · simp [frequencyPart, hzero, hnonpos] at hn
    rw [circleTest_fourier]
    simpa using integral_fourier_nonzero n (ne_of_gt hn')
  · exact map_zero _


-- @@ L75-75 verbatim
namespace AnalyticBidiskKernel

-- @@ L76-76 verbatim
variable (K : AnalyticBidiskKernel)


-- @@ L78-79 verbatim
def rowB (w : UnitAddCircle) : C(UnitAddCircle,ℂ) :=
  ⟨K.circleB w,K.continuous_circleB.comp (continuous_const.prodMk continuous_id)⟩


-- @@ L81-83 verbatim
def rowKernel (w : UnitAddCircle) : C(UnitAddCircle,ℂ) :=
  ⟨fun t => (K.kernel w t : ℂ), Complex.continuous_ofReal.comp
    (K.continuous_kernel.comp (continuous_const.prodMk continuous_id))⟩


-- @@ L85-87 verbatim
lemma rowKernel_eq (w : UnitAddCircle) : K.rowKernel w = 1 + K.rowB w + star (K.rowB w) := by
  ext t
  exact K.kernel_complex w t


-- @@ L89-101 verbatim
lemma testB_positive (w : UnitAddCircle) :
    (circleTest (K.rowB w)).comp (scalarFourier.proj 1) = circleTest (K.rowB w) := by
  apply circleCLM_ext
  intro n
  simp only [ContinuousLinearMap.comp_apply, scalarFourier_fourier]
  split_ifs with hn
  · rfl
  · rw [map_zero, circleTest_fourier]
    symm
    apply K.circleB_right_nonpos_fourier
    by_contra hh
    have hn' : 0 < n := lt_of_not_ge hh
    exact hn (by simp [frequencyPart, ne_of_gt hn', hn'])


-- @@ L103-115 verbatim
lemma testConjB_positive (w : UnitAddCircle) :
    (circleTest (star (K.rowB w))).comp (scalarFourier.proj 1) = 0 := by
  apply circleCLM_ext
  intro n
  simp only [ContinuousLinearMap.comp_apply, scalarFourier_fourier,
    zero_apply]
  split_ifs with hn
  · rw [circleTest_fourier]
    apply K.conj_circleB_right_nonneg_fourier
    by_contra hh
    have hn' : n < 0 := lt_of_not_ge hh
    exact (by simp [frequencyPart,ne_of_lt hn',not_lt.mpr hn'.le] at hn)
  · exact map_zero _


-- @@ L117-121 verbatim
lemma testKernel_positive (w : UnitAddCircle) :
    (circleTest (K.rowKernel w)).comp (scalarFourier.proj 1) = circleTest (K.rowB w) := by
  rw [K.rowKernel_eq, circleTest_add, circleTest_add,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.add_comp,
    circleTest_const_positive, K.testB_positive, K.testConjB_positive, zero_add, add_zero]


-- @@ L123-134 verbatim
lemma scalarM_positive_ae (u : CircleL2) :
    K.scalarM (scalarFourier.proj 1 u) =ᵐ[AddCircle.haarAddCircle]
      fun w => ∫ t, K.circleB w t * u t ∂AddCircle.haarAddCircle := by
  filter_upwards [K.toMarkovKernel.applyLp_ae (scalarFourier.proj 1 u)] with w hw
  refine hw.trans ?_
  change (∫ t, (K.kernel w t : ℂ) * (scalarFourier.proj 1 u) t
    ∂AddCircle.haarAddCircle) = _
  change (∫ t, K.rowKernel w t * (scalarFourier.proj 1 u) t
    ∂AddCircle.haarAddCircle) = _
  rw [← circleTest_apply]
  have he := congrArg (fun L : CircleL2 →L[ℂ] ℂ => L u) (K.testKernel_positive w)
  exact he.trans (circleTest_apply (K.rowB w) u)


-- @@ L136-136 verbatim
end AnalyticBidiskKernel

-- @@ L137-137 verbatim
end


-- @@ L139-139 verbatim
open MeasureTheory Set Complex

-- @@ L140-140 verbatim
open scoped Topology

-- @@ L141-141 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


-- @@ L143-147 verbatim
def analyticCircleTrace (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    C(UnitAddCircle,ℂ) :=
  ⟨fun t => f (t.toCircle : ℂ), hf.continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle)
    (fun t => Metric.sphere_subset_closedBall t.toCircle.property)⟩


-- @@ L149-158 verbatim
lemma analyticTrace_negative_coefficient (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) (n : ℤ) (hn : n < 0) :
    fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (analyticCircleTrace f hf)) n = 0 := by
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
    (p := 2) (𝕜 := ℂ) (analyticCircleTrace f hf)),fourierCoeff]
  obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -n by omega)
  have hk0 : k ≠ 0 := by omega
  simp only [hk, fourier_natCast_toCircle, smul_eq_mul, analyticCircleTrace,
    ContinuousMap.coe_mk]
  exact integral_analytic_mul_pow hf hk0


-- @@ L160-178 verbatim
lemma analyticTrace_negative (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 1)) :
    scalarFourier.proj 2 (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
      (analyticCircleTrace f hf)) = 0 := by
  apply circle_fourier_ext
  intro n
  rw [scalarFourier_coefficient]
  have hz : fourierCoeff (0 : CircleL2) n = 0 := by
    rw [fourierCoeff_congr_ae (Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle)]
    simp [fourierCoeff]
  rw [hz]
  split_ifs with hn
  · apply analyticTrace_negative_coefficient
    by_contra hh
    have hn0 : 0 ≤ n := le_of_not_gt hh
    by_cases he : n = 0
    · simp [frequencyPart,he] at hn
    · simp [frequencyPart,he,lt_of_le_of_ne hn0 (Ne.symm he)] at hn
  · rfl


-- @@ L180-186 verbatim
lemma scalarCauchy_fix_of_parts (K : AnalyticBidiskKernel) (u : CircleL2)
    (h : scalarFourier.proj 2 u = K.scalarM (scalarFourier.proj 1 u)) :
    scalarFourier.cauchy K.scalarM u = u := by
  change scalarFourier.proj 0 u + scalarFourier.proj 1 u +
    K.scalarM (scalarFourier.proj 1 u) = u
  rw [← h]
  exact congrArg (fun L : CircleL2 →L[ℂ] CircleL2 => L u) scalarFourier.total


-- @@ L188-188 verbatim
end CompleteCrouzeix


-- @@ L190-190 verbatim
open Set Metric Filter Complex

-- @@ L191-191 verbatim
open scoped Topology

-- @@ L192-192 verbatim
namespace CompleteCrouzeix


-- @@ L194-194 verbatim
section


-- @@ L196-196 verbatim
section


-- @@ L198-224 verbatim
theorem analytic_circle_gluing {U : Set ℂ} (hU : IsOpen U)
    (hTU : sphere 0 1 ⊆ U) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ z ∈ U ∩ ball 0 1, f z = g z) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q (closedBall 0 1) ∧ EqOn q g (sphere 0 1) := by
  classical
  let q := fun z => if z ∈ ball (0 : ℂ) 1 then f z else g z
  refine ⟨q,?_,?_⟩
  · intro z hz
    by_cases hi : z ∈ ball (0 : ℂ) 1
    · apply (hf z hi).congr
      filter_upwards [isOpen_ball.mem_nhds hi] with w hw
      simp only [q, ite_eq_left hw]
    · have hs : z ∈ sphere (0 : ℂ) 1 := by
        change dist z 0 = 1
        exact le_antisymm hz (le_of_not_gt hi)
      apply (hg z (hTU hs)).congr
      filter_upwards [hU.mem_nhds (hTU hs)] with w hw
      dsimp [q]
      split_ifs with hwi
      · exact (he w ⟨hw,hwi⟩).symm
      · rfl
  · intro z hz
    have hi : z ∉ ball (0 : ℂ) 1 := by
      intro hh
      exact ne_of_lt hh hz
    simp only [q, ite_eq_right hi]



-- @@ L227-227 verbatim
open Set Metric Complex MeasureTheory

-- @@ L228-228 verbatim
open scoped Topology

-- @@ L229-229 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


-- @@ L231-238 verbatim
lemma circleTest_toLp (f u : C(UnitAddCircle,ℂ)) :
    circleTest f (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) =
      ∫ t, f t * u t ∂AddCircle.haarAddCircle := by
  rw [circleTest_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
    (p := 2) (𝕜 := ℂ) u] with t ht
  rw [ht]


-- @@ L240-276 verbatim
lemma scalarCauchy_fix_of_analytic_correction (K : AnalyticBidiskKernel)
    (u : C(UnitAddCircle,ℂ)) (q : ℂ → ℂ)
    (hq : AnalyticOnNhd ℂ q (closedBall 0 1))
    (he : ∀ w : UnitAddCircle, u w = q (w.toCircle : ℂ) +
      ∫ t, K.circleB w t * u t ∂AddCircle.haarAddCircle) :
    scalarFourier.cauchy K.scalarM (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u := by
  let L : C(UnitAddCircle,ℂ) →L[ℂ] CircleL2 := ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
  have hparts : L u = L (analyticCircleTrace q hq) + K.scalarM (scalarFourier.proj 1 (L u)) := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
      (p := 2) (𝕜 := ℂ) u,
      ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle) (p := 2) (𝕜 := ℂ)
        (analyticCircleTrace q hq),
      Lp.coeFn_add (L (analyticCircleTrace q hq)) (K.scalarM (scalarFourier.proj 1 (L u))),
      K.scalarM_positive_ae (L u)] with w hu hq' hadd hM
    rw [hadd]
    change L u w = L (analyticCircleTrace q hq) w + K.scalarM (scalarFourier.proj 1 (L u)) w
    rw [hu,hq',hM]
    change u w = q (w.toCircle : ℂ) + ∫ t, K.circleB w t * L u t ∂AddCircle.haarAddCircle
    rw [he w]
    congr 1
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle)
      (p := 2) (𝕜 := ℂ) u] with t ht
    rw [ht]
  apply scalarCauchy_fix_of_parts
  calc
    scalarFourier.proj 2 (L u) =
      scalarFourier.proj 2 (L (analyticCircleTrace q hq)) +
        scalarFourier.proj 2 (K.scalarM (scalarFourier.proj 1 (L u))) := by
      rw [← map_add, ← hparts]
    _ = K.scalarM (scalarFourier.proj 1 (L u)) := by
      rw [analyticTrace_negative,zero_add]
      have hs := congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T (scalarFourier.proj 1 (L u))) K.scalarM_swap
      simp only [ContinuousLinearMap.comp_apply, scalarFourier.proj_proj] at hs
      simpa using hs.symm


-- @@ L278-278 verbatim
end


-- @@ L280-280 verbatim
open MeasureTheory Set Metric Complex

-- @@ L281-281 verbatim
open scoped Topology

-- @@ L282-282 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩


-- @@ L284-296 verbatim
lemma canonicalCircleCauchy_analytic {u : UnitAddCircle → ℂ} (hu : Continuous u) :
    AnalyticOnNhd ℂ (fun w => ∫ t : UnitAddCircle,
      u t*((t.toCircle : ℂ)/((t.toCircle : ℂ)-w)) ∂AddCircle.haarAddCircle) (ball 0 1) := by
  have h : AnalyticOnNhd ℂ (physicalCauchy id u) (ball 0 1) :=
    physicalCauchy_analytic analyticOnNhd_id hu isOpen_ball (by
      intro z hz t he
      have ht := t.toCircle.property
      change (t.toCircle : ℂ) = z at he
      rw [he] at ht
      exact ne_of_lt hz ht)
  convert h using 1
  funext w
  simp [physicalCauchy]


-- @@ L298-337 verbatim
lemma scalarCauchy_fix_physical_trace (K : AnalyticBidiskKernel)
    {G v : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    (hv : AnalyticOnNhd ℂ (fun w => v (G w)) U)
    (hB : ∀ w t : UnitAddCircle, K.circleB w t = exteriorCorrection G w.toCircle t.toCircle)
    (hrep : ∀ w ∈ U ∩ ball 0 1,
      physicalCauchy G (fun t => v (G t.toCircle)) (G w) = v (G w)) :
    let u : C(UnitAddCircle,ℂ) := ⟨fun t => v (G t.toCircle),
      hv.continuousOn.comp_continuous
        (continuous_subtype_val.comp AddCircle.continuous_toCircle)
        (fun t => hTU t.toCircle.property)⟩
    scalarFourier.cauchy K.scalarM (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u := by
  dsimp only
  let u : C(UnitAddCircle,ℂ) := ⟨fun t => v (G t.toCircle),
    hv.continuousOn.comp_continuous
      (continuous_subtype_val.comp AddCircle.continuous_toCircle)
      (fun t => hTU t.toCircle.property)⟩
  change scalarFourier.cauchy K.scalarM (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u) = _
  have hJ := cauchyCorrectionIntegral_analytic hU hG hi hd hTU u.continuous
  obtain ⟨q,hq,hqT⟩ := analytic_circle_gluing hU hTU
    (canonicalCircleCauchy_analytic u.continuous) (hv.sub hJ) (by
      intro w hw
      apply eq_sub_iff_add_eq.mpr
      exact (physicalCauchy_decompose hU hG hi hd hTU u.continuous hw.1 hw.2).symm.trans
        (hrep w hw))
  apply scalarCauchy_fix_of_analytic_correction K u q hq
  intro w
  have he := hqT w.toCircle.property
  change q (w.toCircle : ℂ) = v (G w.toCircle) - cauchyCorrectionIntegral G u w.toCircle at he
  rw [he]
  have hj : cauchyCorrectionIntegral G u w.toCircle =
      ∫ t, K.circleB w t * u t ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hB]
    exact mul_comm _ _
  change v (G w.toCircle) = _
  rw [hj,sub_add_cancel]


-- @@ L339-339 verbatim
end



-- @@ L342-383 verbatim
theorem reciprocalCorrection_continuousOn {a : ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hh : AnalyticOnNhd ℂ h U)
    (hne : ∀ x ∈ U, ∀ y ∈ U, exteriorDividedDifference a h x y ≠ 0) :
    ContinuousOn (Function.uncurry (reciprocalCorrection a h)) (U ×ˢ U) := by
  apply continuousOn_of_analytic_left_offDiagonal hU
    (fun y hy => reciprocalCorrection_analytic_left hU hh hne hy)
  let V := {p : ℂ × ℂ | p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2}
  let H := fun z : ℂ => z*h z
  have hH : AnalyticOnNhd ℂ H U := analyticOnNhd_id.mul hh
  have ch1 : ContinuousOn (fun p : ℂ × ℂ => h p.1) V :=
    hh.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have ch2 : ContinuousOn (fun p : ℂ × ℂ => h p.2) V :=
    hh.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cH1 : ContinuousOn (fun p : ℂ × ℂ => H p.1) V :=
    hH.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
  have cH2 : ContinuousOn (fun p : ℂ × ℂ => H p.2) V :=
    hH.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cdH2 : ContinuousOn (fun p : ℂ × ℂ => deriv H p.2) V :=
    hH.deriv.continuousOn.comp continuousOn_snd (fun p hp => hp.2.1)
  have cz : ∀ p ∈ V, p.1-p.2 ≠ 0 := fun p hp => sub_ne_zero.mpr hp.2.2
  have cq : ContinuousOn (fun p : ℂ × ℂ => (h p.1-h p.2)/(p.1-p.2)) V :=
    (ch1.sub ch2).div (continuousOn_fst.sub continuousOn_snd) cz
  have cr : ContinuousOn (fun p : ℂ × ℂ =>
      ((H p.1-H p.2)/(p.1-p.2)-deriv H p.2)/(p.1-p.2)) V :=
    (((cH1.sub cH2).div (continuousOn_fst.sub continuousOn_snd) cz).sub cdH2).div
      (continuousOn_fst.sub continuousOn_snd) cz
  have cqeq (p : ℂ × ℂ) (hp : p ∈ V) :
      exteriorDividedDifference a h p.1 p.2 =
        a-p.1*p.2*((h p.1-h p.2)/(p.1-p.2)) := by
    rw [exteriorDividedDifference, dslope_comm h p.1 p.2,
      dslope_of_ne _ hp.2.2, slope_def_field]
  have cc : ContinuousOn (fun p : ℂ × ℂ =>
      p.1*p.2*(((H p.1-H p.2)/(p.1-p.2)-deriv H p.2)/(p.1-p.2)) /
        (a-p.1*p.2*((h p.1-h p.2)/(p.1-p.2)))) V :=
    ((continuousOn_fst.mul continuousOn_snd).mul cr).div
      (continuousOn_const.sub ((continuousOn_fst.mul continuousOn_snd).mul cq))
      (fun p hp => (cqeq p hp) ▸ hne p.1 hp.1 p.2 hp.2.1)
  apply cc.congr
  intro p hp
  change reciprocalCorrection a h p.1 p.2 = _
  rw [reciprocalCorrection, cqeq p hp, dslope_of_ne _ hp.2.2, slope_def_field,
    dslope_of_ne _ hp.2.2, slope_def_field, dslope_same]


-- @@ L385-385 verbatim
end CompleteCrouzeix


-- @@ L387-387 verbatim
end


-- @@ L389-389 verbatim
end OAI
