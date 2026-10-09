import OAI.Analysis.DirectCrouzeix.CompactIntegrals


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped Matrix Matrix.Norms.L2Operator Kronecker


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open MeasureTheory Set Filter Metric


-- @@ L13-13 verbatim
open scoped Topology Interval ENNReal NNReal ComplexConjugate


-- @@ L15-15 verbatim
namespace DirectCrouzeix.Faber


-- @@ L17-17 verbatim
def divided (g : ℂ → ℂ) (u v : ℂ) : ℂ := chordIntegral (deriv g) (fun _ => 1) u v


-- @@ L19-20 verbatim
def dividedLeft (g : ℂ → ℂ) (u v : ℂ) : ℂ :=
  chordIntegral (deriv (deriv g)) (fun t => (1-(t:ℝ) : ℝ)) u v


-- @@ L22-22 verbatim
def chordDenominator (c : ℂ) (g : ℂ → ℂ) (u v : ℂ) : ℂ := c-u*v*divided g u v


-- @@ L24-25 verbatim
def correction (c : ℂ) (g : ℂ → ℂ) (u v : ℂ) : ℂ :=
  u*v*(divided g u v+u*dividedLeft g u v) / chordDenominator c g u v


-- @@ L27-29 verbatim
theorem divided_eq_dslope {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    divided g u v = dslope g v u := chordIntegral_deriv_eq_dslope hconv hg hu hv


-- @@ L31-35 verbatim
theorem hasDerivAt_divided_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => divided g z v) (dividedLeft g u v) u := by
  simpa only [divided, dividedLeft, one_mul] using
    hasDerivAt_chordIntegral_left hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hu hv


-- @@ L37-47 verbatim
theorem continuousOn_correction {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c : ℂ}
    (hH : ∀ u ∈ s, ∀ v ∈ s, chordDenominator c g u v ≠ 0) :
    ContinuousOn (fun p : ℂ × ℂ => correction c g p.1 p.2) (s ×ˢ s) := by
  have hD := continuousOn_chordIntegral hs hconv hg.deriv.continuousOn (continuous_const (y := (1:ℂ)))
  have hE := continuousOn_chordIntegral hs hconv hg.deriv.deriv.continuousOn
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop)
  exact ((continuous_fst.mul continuous_snd).continuousOn.mul
    (hD.add (continuous_fst.continuousOn.mul hE))).div
    (continuousOn_const.sub ((continuous_fst.mul continuous_snd).continuousOn.mul hD))
    (fun p hp => hH p.1 hp.1 p.2 hp.2)


-- @@ L49-58 verbatim
theorem analyticOnNhd_correction_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c v : ℂ} (hv : v ∈ s)
    (hH : ∀ u ∈ s, chordDenominator c g u v ≠ 0) :
    AnalyticOnNhd ℂ (fun u => correction c g u v) s := by
  have hD := analyticOnNhd_chordIntegral_left hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hv
  have hE := analyticOnNhd_chordIntegral_left hs hconv hg.deriv.deriv
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop) hv
  intro u hu
  exact (((analyticAt_id.mul analyticAt_const).mul ((hD u hu).add (analyticAt_id.mul (hE u hu)))).div
    (analyticAt_const.sub ((analyticAt_id.mul analyticAt_const).mul (hD u hu))) (hH u hu))


-- @@ L60-69 verbatim
theorem analyticOnNhd_correction_right {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c u : ℂ} (hu : u ∈ s)
    (hH : ∀ v ∈ s, chordDenominator c g u v ≠ 0) :
    AnalyticOnNhd ℂ (correction c g u) s := by
  have hD := analyticOnNhd_chordIntegral_right hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hu
  have hE := analyticOnNhd_chordIntegral_right hs hconv hg.deriv.deriv
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop) hu
  intro v hv
  exact (((analyticAt_const.mul analyticAt_id).mul ((hD v hv).add (analyticAt_const.mul (hE v hv)))).div
    (analyticAt_const.sub ((analyticAt_const.mul analyticAt_id).mul (hD v hv))) (hH v hv))


-- @@ L71-72 verbatim
@[simp] theorem correction_zero_left (c : ℂ) (g : ℂ → ℂ) (v : ℂ) : correction c g 0 v = 0 := by
  simp [correction]


-- @@ L74-75 verbatim
@[simp] theorem correction_zero_right (c : ℂ) (g : ℂ → ℂ) (u : ℂ) : correction c g u 0 = 0 := by
  simp [correction]


-- @@ L77-77 verbatim
def exterior (c : ℂ) (g : ℂ → ℂ) (ζ : ℂ) := c*ζ+g ζ⁻¹


-- @@ L79-86 verbatim
theorem hasDerivAt_exterior {s : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s)
    (c : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) (hζs : ζ⁻¹ ∈ s) :
    HasDerivAt (exterior c g) (c-ζ⁻¹^2*deriv g ζ⁻¹) ζ := by
  have hd := ((hasDerivAt_id ζ).const_mul c).add
    ((hg ζ⁻¹ hζs).differentiableAt.hasDerivAt.comp ζ (hasDerivAt_inv hζ))
  change HasDerivAt (fun z => exterior c g z) _ ζ
  simpa only [exterior, Function.comp_def, id_eq, mul_one, Pi.add_apply, inv_pow,
    div_eq_mul_inv, sub_eq_add_neg, mul_neg, mul_comm, mul_left_comm] using! hd


-- @@ L88-95 verbatim
theorem chordDenominator_off_diagonal {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u v : ℂ}
    (hu : u ∈ s) (hv : v ∈ s) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) :
    chordDenominator c g u v = (exterior c g u⁻¹ - exterior c g v⁻¹) / (u⁻¹-v⁻¹) := by
  rw [chordDenominator, divided_eq_dslope hconv hg hu hv, dslope_of_ne g huv]
  simp only [slope, smul_eq_mul, vsub_eq_sub, exterior, inv_inv]
  field_simp
  ring


-- @@ L97-101 verbatim
theorem chordDenominator_diagonal {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u : ℂ} (hu : u ∈ s) :
    chordDenominator c g u u = c-u^2*deriv g u := by
  rw [chordDenominator, divided_eq_dslope hconv hg hu hu, dslope_same]
  ring


-- @@ L103-121 verbatim
theorem chordDenominator_ne_zero {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c : ℂ} (hc : c ≠ 0)
    (hinj : InjOn (exterior c g) (Inv.inv ⁻¹' s \ {0}))
    (hd : ∀ ζ, ζ ≠ 0 → ζ⁻¹ ∈ s → deriv (exterior c g) ζ ≠ 0)
    {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) : chordDenominator c g u v ≠ 0 := by
  by_cases hu0 : u = 0
  · simp [chordDenominator, hu0, hc]
  by_cases hv0 : v = 0
  · simp [chordDenominator, hv0, hc]
  by_cases huv : u = v
  · subst v
    rw [chordDenominator_diagonal hconv hg c hu]
    have hder := (hasDerivAt_exterior hg c (inv_ne_zero hu0) (by simpa using hu)).deriv
    have hn := hd u⁻¹ (inv_ne_zero hu0) (by simpa using hu)
    rwa [hder,inv_inv] at hn
  · rw [chordDenominator_off_diagonal hconv hg c hu hv hu0 hv0 huv]
    exact div_ne_zero (sub_ne_zero.mpr (fun he => huv (inv_injective (hinj
      ⟨by simpa using hu, by simpa using hu0⟩ ⟨by simpa using hv, by simpa using hv0⟩ he))))
      (sub_ne_zero.mpr (fun he => huv (inv_injective he)))


-- @@ L123-128 verbatim
theorem divided_fundamental {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    (u-v)*divided g u v = g u-g v := by
  have hh := chordIntegral_deriv_mul hconv hg hu hv
  change divided g u v * (v-u) = _ at hh
  linear_combination -hh


-- @@ L130-138 verbatim
theorem divided_derivative_relation {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    divided g u v + (u-v)*dividedLeft g u v = deriv g u := by
  have hd := ((hasDerivAt_id u).sub_const v).mul (hasDerivAt_divided_left hs hconv hg hu hv)
  have he : (fun z => g z-g v) =ᶠ[𝓝 u] (fun z => (z-v)*divided g z v) := by
    filter_upwards [hs.mem_nhds hu] with z hz
    exact (divided_fundamental hconv hg hz hv).symm
  have hid := (hd.congr_of_eventuallyEq he).unique ((hg u hu).differentiableAt.hasDerivAt.sub_const (g v))
  simpa using hid


-- @@ L140-156 verbatim
theorem correction_identity {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u v : ℂ}
    (hu : u ∈ s) (hv : v ∈ s) (hv0 : v ≠ 0) (huv : u ≠ v)
    (hH : chordDenominator c g u v ≠ 0) :
    correction c g u v = (c-u^2*deriv g u)/(c+u*(g u-exterior c g v⁻¹)) - (1-u/v)⁻¹ := by
  have hD := divided_fundamental hconv hg hu hv
  have hE := divided_derivative_relation hs hconv hg hu hv
  have huv' : v-u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have he : c+u*(g u-exterior c g v⁻¹) = chordDenominator c g u v * (v-u)/v := by
    simp only [exterior,inv_inv,chordDenominator]
    field_simp
    linear_combination -u*v*hD
  rw [he,correction]
  have hd0 : chordDenominator c g u v * (v-u) / v ≠ 0 := div_ne_zero (mul_ne_zero hH huv') hv0
  field_simp
  simp only [chordDenominator]
  linear_combination -u^2*hE


-- @@ L158-158 verbatim
end DirectCrouzeix.Faber


-- @@ L160-160 verbatim
end


-- @@ L162-162 verbatim
end


-- @@ L164-164 verbatim
end OAI
