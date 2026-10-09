import OAI.Probability.GaussianPropeller.HeatConvolution


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uX


-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L8-8 verbatim
open scoped ENNReal

-- @@ L9-9 verbatim
open scoped RealInnerProductSpace

-- @@ L10-10 verbatim
open scoped RealInnerProductSpace

-- @@ L11-11 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L12-12 verbatim
open scoped ENNReal RealInnerProductSpace

-- @@ L13-13 verbatim
open Filter

-- @@ L14-14 verbatim
open scoped Topology


-- @@ L16-16 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L17-17 verbatim
open scoped Topology


-- @@ L19-19 verbatim
namespace GaussianPropeller.Quantile


-- @@ L21-21 verbatim
noncomputable def φ (x : ℝ) : ℝ := (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-x^2/2)

-- @@ L22-22 verbatim
noncomputable def Φ (x : ℝ) : ℝ := ∫ y in Iic x, φ y


-- @@ L24-24 verbatim
lemma φ_pos (x : ℝ) : 0 < φ x := by unfold φ; positivity

-- @@ L25-25 verbatim
lemma φ_neg (x : ℝ) : φ (-x) = φ x := by simp [φ]

-- @@ L26-30 verbatim
lemma integrable_φ : Integrable φ := by
  unfold φ
  have h := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  simpa only [φ, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring] using
    h.const_mul ((Real.sqrt (2*Real.pi))⁻¹)

-- @@ L31-37 verbatim
lemma integral_φ : ∫ x, φ x = 1 := by
  unfold φ
  rw [integral_const_mul]
  simp_rw [show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
  rw [integral_gaussian]
  have hp : Real.pi/(1/2:ℝ) = 2*Real.pi := by ring
  rw [hp, inv_mul_cancel₀ (by positivity)]

-- @@ L38-42 verbatim
lemma hasDerivAt_φ (x : ℝ) : HasDerivAt φ (-x*φ x) x := by
  unfold φ
  convert ((((hasDerivAt_pow 2 x).neg.div_const 2).exp).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)) using 1
  first | rfl | (dsimp; ring)

-- @@ L43-44 verbatim
lemma continuous_φ : Continuous φ := by exact continuous_iff_continuousAt.mpr fun x =>
  (hasDerivAt_φ x).continuousAt

-- @@ L45-54 verbatim
lemma hasDerivAt_Φ (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have heq : Φ = fun a => Φ 0 + ∫ t in (0:ℝ)..a, φ t := by
    funext a
    have hi := intervalIntegral.integral_Iic_sub_Iic
      (a := 0) (b := a) integrable_φ.integrableOn integrable_φ.integrableOn
    change Φ a-Φ 0 = _ at hi
    linarith only [hi]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right integrable_φ.intervalIntegrable
    continuous_φ.stronglyMeasurable.stronglyMeasurableAtFilter continuous_φ.continuousAt).const_add _

-- @@ L55-56 verbatim
lemma continuous_Φ : Continuous Φ := continuous_iff_continuousAt.mpr fun x =>
  (hasDerivAt_Φ x).continuousAt

-- @@ L57-58 verbatim
lemma strictMono_Φ : StrictMono Φ := strictMono_of_deriv_pos (fun x => by
    rw [(hasDerivAt_Φ x).deriv]; exact φ_pos x)

-- @@ L59-62 verbatim
lemma Φ_pos (x : ℝ) : 0 < Φ x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun x => (φ_pos x).le))
    integrable_φ.integrableOn).mpr
  simp [Function.support, ne_of_gt (φ_pos _)]

-- @@ L63-67 verbatim
lemma Φ_eq_one_sub_tail (x : ℝ) : Φ x = 1 - ∫ y in Ioi x, φ y := by
  have h := integral_add_compl measurableSet_Iic integrable_φ (s := Iic x)
  rw [compl_Iic, integral_φ] at h
  unfold Φ
  linarith only [h]

-- @@ L68-73 verbatim
lemma Φ_neg (x : ℝ) : Φ (-x) = 1-Φ x := by
  have h := integral_comp_neg_Iic (-x) φ
  simp only [φ_neg, neg_neg] at h
  change Φ (-x) = (∫ y in Ioi x, φ y) at h
  rw [h, Φ_eq_one_sub_tail]
  ring

-- @@ L74-77 verbatim
lemma Φ_lt_one (x : ℝ) : Φ x < 1 := by
  have h := Φ_pos (-x)
  rw [Φ_neg] at h
  linarith only [h]

-- @@ L78-78 verbatim
lemma Φ_mem (x : ℝ) : Φ x ∈ Ioo (0:ℝ) 1 := ⟨Φ_pos x, Φ_lt_one x⟩

-- @@ L79-82 verbatim
lemma Φ_zero : Φ 0 = 1/2 := by
  have h := Φ_neg 0
  simp only [neg_zero] at h
  linarith only [h]

-- @@ L83-87 verbatim
lemma tendsto_Φ_atTop : Tendsto Φ atTop (𝓝 1) := by
  have ht := tendsto_integral_Ioi_zero (f := φ) (μ := volume) tendsto_id
  convert ht.const_sub 1 using 1
  · exact funext Φ_eq_one_sub_tail
  · norm_num

-- @@ L88-91 verbatim
lemma tendsto_Φ_atBot : Tendsto Φ atBot (𝓝 0) := by
  have ht := tendsto_Φ_atTop.comp tendsto_neg_atBot_atTop
  have hh := ht.const_sub 1
  simpa only [Function.comp_def, Φ_neg, sub_sub_cancel, sub_self] using hh

-- @@ L92-98 verbatim
lemma range_Φ : range Φ = Ioo (0:ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x,rfl⟩; exact Φ_mem x
  · have hh := isPreconnected_univ.intermediate_value_Ioo
      (l₁ := atBot) (l₂ := atTop) (by simp) (by simp) continuous_Φ.continuousOn
      tendsto_Φ_atBot tendsto_Φ_atTop
    simpa only [image_univ] using hh


-- @@ L100-101 verbatim
noncomputable def cdfIso : ℝ ≃o Ioo (0:ℝ) 1 :=
  (strictMono_Φ.orderIso Φ).trans (Set.orderIsoOfEq _ _ range_Φ)

-- @@ L102-102 verbatim
lemma cdfIso_coe (x : ℝ) : (cdfIso x : ℝ) = Φ x := rfl

-- @@ L103-104 verbatim
noncomputable def q (p : ℝ) : ℝ :=
  if h : p ∈ Ioo (0:ℝ) 1 then cdfIso.symm ⟨p,h⟩ else 0

-- @@ L105-106 verbatim
lemma q_of_mem {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : q p = cdfIso.symm ⟨p,hp⟩ := by
  simp [q, hp]

-- @@ L107-109 verbatim
lemma Φ_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : Φ (q p) = p := by
  rw [q_of_mem hp, ← cdfIso_coe]
  exact congrArg Subtype.val (cdfIso.apply_symm_apply ⟨p,hp⟩)

-- @@ L110-112 verbatim
lemma q_Φ (x : ℝ) : q (Φ x) = x := by
  rw [q_of_mem (Φ_mem x)]
  exact cdfIso.symm_apply_apply x

-- @@ L113-120 verbatim
lemma continuousOn_q : ContinuousOn q (Ioo (0:ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : Ioo (0:ℝ) 1 => q p)
  have heq : (fun p : Ioo (0:ℝ) 1 => q p) = cdfIso.symm := by
    funext p
    exact q_of_mem p.2
  rw [heq]
  exact cdfIso.symm.continuous

-- @@ L121-122 verbatim
lemma continuousAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : ContinuousAt q p :=
  continuousOn_q.continuousAt (isOpen_Ioo.mem_nhds hp)

-- @@ L123-128 verbatim
lemma hasDerivAt_q {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    HasDerivAt q (φ (q p))⁻¹ p := by
  apply HasDerivAt.of_local_left_inverse (continuousAt_q hp) (hasDerivAt_Φ (q p))
    (ne_of_gt (φ_pos _))
  filter_upwards [isOpen_Ioo.mem_nhds hp] with y hy
  exact Φ_q hy

-- @@ L129-132 verbatim
lemma strictMonoOn_q : StrictMonoOn q (Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  rw [q_of_mem ha, q_of_mem hb]
  exact cdfIso.symm.strictMono hab


-- @@ L134-134 verbatim
noncomputable def I (p : ℝ) : ℝ := φ (q p)

-- @@ L135-135 verbatim
lemma I_pos (p : ℝ) : 0 < I p := φ_pos _

-- @@ L136-136 verbatim
lemma I_Φ (x : ℝ) : I (Φ x) = φ x := by simp [I, q_Φ]

-- @@ L137-139 verbatim
lemma hasDerivAt_I {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) : HasDerivAt I (-q p) p := by
  convert (hasDerivAt_φ (q p)).comp p (hasDerivAt_q hp) using 1 <;>
    first | rfl | field_simp [ne_of_gt (φ_pos (q p))]

-- @@ L140-142 verbatim
lemma antitoneOn_I_deriv : AntitoneOn (fun p => -q p) (Ioo (0:ℝ) 1) := by
  intro a ha b hb hab
  exact neg_le_neg (strictMonoOn_q.monotoneOn ha hb hab)

-- @@ L143-150 verbatim
lemma concaveOn_I : ConcaveOn ℝ (Ioo (0:ℝ) 1) I := by
  have hanti : AntitoneOn (deriv I) (Ioo (0:ℝ) 1) := by
    intro a ha b hb hab
    rw [(hasDerivAt_I ha).deriv, (hasDerivAt_I hb).deriv]
    exact antitoneOn_I_deriv ha hb hab
  apply (hanti.mono interior_subset).concaveOn_of_deriv (convex_Ioo 0 1)
  · exact fun p hp => (hasDerivAt_I hp).continuousAt.continuousWithinAt
  · exact fun p hp => (hasDerivAt_I (interior_subset hp)).differentiableAt.differentiableWithinAt


-- @@ L152-164 verbatim
lemma concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ S f)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) :
    f y ≤ f x+d*(y-x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · simp
  · have hh := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hh']


-- @@ L166-168 verbatim
lemma I_le_tangent {p r : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (hr : r ∈ Ioo (0:ℝ) 1) :
    I r ≤ I p-q p*(r-p) := by
  simpa only [neg_mul, sub_eq_add_neg] using concave_le_tangent concaveOn_I hp hr (hasDerivAt_I hp)


-- @@ L170-173 verbatim
lemma φ_le_zero (x : ℝ) : φ x ≤ φ 0 := by
  unfold φ
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))


-- @@ L175-175 verbatim
section Integration

-- @@ L176-176 verbatim
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]


-- @@ L178-183 verbatim
lemma integrable_Φ_comp {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => Φ (f x)) μ := by
  apply Integrable.mono' (integrable_const (1:ℝ)) (continuous_Φ.comp_aestronglyMeasurable hf)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]
  exact (Φ_lt_one _).le

-- @@ L184-189 verbatim
lemma integrable_φ_comp {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => φ (f x)) μ := by
  apply Integrable.mono' (integrable_const (φ 0)) (continuous_φ.comp_aestronglyMeasurable hf)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (φ_pos _)]
  exact φ_le_zero _

-- @@ L190-202 verbatim
lemma integral_Φ_mem {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, Φ (f x) ∂μ) ∈ Ioo (0:ℝ) 1 := by
  have hpos {g : X → ℝ} (hg : Integrable g μ) (hh : ∀ x, 0 < g x) : 0 < ∫ x, g x ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun x => (hh x).le) hg).mpr
    have heq : Function.support g = univ := by ext x; simp [Function.mem_support, ne_of_gt (hh x)]
    simp [heq]
  refine ⟨hpos (integrable_Φ_comp hf) (fun x => Φ_pos _), ?_⟩
  have hh := hpos ((integrable_const (1:ℝ)).sub (integrable_Φ_comp hf))
    (fun x => sub_pos.mpr (Φ_lt_one (f x)))
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const (1:ℝ)) (integrable_Φ_comp hf), integral_const] at hh
  simp only [probReal_univ, smul_eq_mul, one_mul] at hh
  linarith only [hh]


-- @@ L204-216 verbatim
lemma integral_φ_le_I {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ x, φ (f x) ∂μ) ≤ I (∫ x, Φ (f x) ∂μ) := by
  let p := ∫ x, Φ (f x) ∂μ
  have hp : p ∈ Ioo (0:ℝ) 1 := integral_Φ_mem hf
  have hi := integral_mono (integrable_φ_comp hf)
    ((integrable_const (I p)).sub (((integrable_Φ_comp hf).sub (integrable_const p)).const_mul (q p)))
    (fun x => by simpa only [I_Φ, Pi.sub_apply] using I_le_tangent hp (Φ_mem (f x)))
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const (I p)), integral_const, integral_const_mul,
    integral_sub (integrable_Φ_comp hf) (integrable_const p), integral_const] at hi
  · simpa only [probReal_univ, smul_eq_mul, one_mul, show (∫ x, Φ (f x) ∂μ) = p from rfl,
      sub_self, mul_zero, sub_zero] using hi
  · exact ((integrable_Φ_comp hf).sub (integrable_const p)).const_mul (q p)


-- @@ L218-230 verbatim
lemma hasDerivAt_integral_shift {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (a : ℝ) :
    HasDerivAt (fun s => ∫ x, Φ (f x+s) ∂μ) (∫ x, φ (f x+a) ∂μ) a := by
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) (bound := fun _ => φ 0)
    (F' := fun s x => φ (f x+s)) (by simp) ?_ (integrable_Φ_comp (hf.add_const a))
    (continuous_φ.comp_aestronglyMeasurable (hf.add_const a)) ?_ (integrable_const (φ 0)) ?_).2
  · exact Filter.Eventually.of_forall fun s => continuous_Φ.comp_aestronglyMeasurable (hf.add_const s)
  · filter_upwards [] with x
    intro s _
    rw [Real.norm_eq_abs, abs_of_pos (φ_pos _)]
    exact φ_le_zero _
  · filter_upwards [] with x
    intro s _
    simpa only [mul_one, Function.comp_def, id_eq] using (hasDerivAt_Φ (f x+s)).comp s ((hasDerivAt_id s).const_add (f x))


-- @@ L232-236 verbatim
lemma hasDerivAt_quantile_shift {f : X → ℝ} (hf : AEStronglyMeasurable f μ) (a : ℝ) :
    HasDerivAt (fun s => q (∫ x, Φ (f x+s) ∂μ))
      ((∫ x, φ (f x+a) ∂μ)/I (∫ x, Φ (f x+a) ∂μ)) a := by
  convert (hasDerivAt_q (integral_Φ_mem (hf.add_const a))).comp a
    (hasDerivAt_integral_shift hf a) using 1 <;> first | rfl | (simp only [I]; ring)


-- @@ L238-247 verbatim
lemma quantile_shift_le {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {a : ℝ} (ha : 0 ≤ a) :
    q (∫ x, Φ (f x+a) ∂μ) ≤ q (∫ x, Φ (f x) ∂μ)+a := by
  have hd (s : ℝ) := (hasDerivAt_quantile_shift hf s).sub (hasDerivAt_id s)
  have hm : Antitone (fun s => q (∫ x, Φ (f x+s) ∂μ)-s) := antitone_of_hasDerivAt_nonpos hd
    (fun s => by
      have hh := (div_le_one (I_pos _)).mpr (integral_φ_le_I (hf.add_const s))
      exact sub_nonpos.mpr hh)
  have hh := hm ha
  simp only [add_zero, sub_zero] at hh
  linarith only [hh]


-- @@ L249-249 verbatim
end Integration

-- @@ L250-250 verbatim
end GaussianPropeller.Quantile


-- @@ L252-252 verbatim
end OAI
