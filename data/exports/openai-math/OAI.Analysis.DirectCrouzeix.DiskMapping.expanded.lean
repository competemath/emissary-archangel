import OAI.Analysis.DirectCrouzeix.ExtremalEmbedding


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
noncomputable section


-- @@ L17-17 verbatim
open Filter Metric Set


-- @@ L19-19 verbatim
open scoped Topology ComplexConjugate


-- @@ L21-21 verbatim
namespace DirectCrouzeix


-- @@ L23-23 verbatim
namespace Conformal


-- @@ L25-25 verbatim
open Function Complex


-- @@ L27-27 verbatim
open scoped Pointwise


-- @@ L29-29 verbatim
def diskMobius (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)


-- @@ L31-37 verbatim
theorem diskMobius_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  rw [norm_one, norm_mul, norm_conj] at hh
  have hp := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
  nlinarith


-- @@ L39-44 verbatim
theorem diskMobius_difference (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  ring


-- @@ L46-55 verbatim
theorem diskMobius_mapsTo {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (diskMobius a) (ball 0 1) (ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  rw [mem_ball_zero_iff, diskMobius, norm_div,
    div_lt_one₀ (norm_pos_iff.mpr (diskMobius_den_ne_zero ha hz'.le))]
  have hd := diskMobius_difference a z
  have hp : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := mul_pos
    (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]


-- @@ L57-66 verbatim
theorem diskMobius_hasDerivAt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    HasDerivAt (diskMobius a) ((1 - conj a * a) / (1 - conj a * z) ^ 2) z := by
  have hh := ((hasDerivAt_id z).sub_const a).fun_div
    ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (conj a)))
    (diskMobius_den_ne_zero ha hz)
  change HasDerivAt (diskMobius a)
    ((1 * (1 - conj a * z) - (z - a) * (0 - conj a * 1)) / (1 - conj a * z) ^ 2) z at hh
  convert hh using 1
  congr 1
  ring


-- @@ L68-72 verbatim
theorem diskMobius_deriv_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    deriv (diskMobius a) z ≠ 0 := by
  rw [(diskMobius_hasDerivAt ha hz).deriv]
  exact div_ne_zero (diskMobius_den_ne_zero ha ha.le)
    (pow_ne_zero _ (diskMobius_den_ne_zero ha hz))


-- @@ L74-83 verbatim
theorem diskMobius_injOn {a : ℂ} (ha : ‖a‖ < 1) :
    InjOn (diskMobius a) (ball 0 1) := by
  intro z hz w hw he
  have hz' := (mem_ball_zero_iff.mp hz).le
  have hw' := (mem_ball_zero_iff.mp hw).le
  have hd := (div_eq_div_iff (diskMobius_den_ne_zero ha hz')
    (diskMobius_den_ne_zero ha hw')).mp he
  have hprod : (1 - conj a * a) * (z - w) = 0 := by
    linear_combination hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (diskMobius_den_ne_zero ha ha.le))


-- @@ L85-85 verbatim
@[simp] theorem diskMobius_self (a : ℂ) : diskMobius a a = 0 := by simp [diskMobius]


-- @@ L87-87 verbatim
@[simp] theorem diskMobius_zero (a : ℂ) : diskMobius a 0 = -a := by simp [diskMobius]


-- @@ L89-95 verbatim
theorem diskMobius_norm_deriv {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖deriv (diskMobius a) z‖ = (1 - ‖a‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 := by
  rw [(diskMobius_hasDerivAt ha hz).deriv, norm_div, norm_pow]
  congr 1
  rw [mul_comm (conj a), Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by nlinarith [norm_nonneg a] : 0 < 1 - ‖a‖ ^ 2)]


-- @@ L97-100 verbatim
theorem diskMobius_norm_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv (diskMobius a) 0‖ = 1 - ‖a‖ ^ 2 := by
  rw [diskMobius_norm_deriv ha (by simp)]
  simp


-- @@ L102-110 verbatim
theorem diskMobius_norm_deriv_self {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv (diskMobius a) a‖ = (1 - ‖a‖ ^ 2)⁻¹ := by
  rw [diskMobius_norm_deriv ha ha.le]
  have hd : ‖1 - conj a * a‖ = 1 - ‖a‖ ^ 2 := by
    rw [mul_comm (conj a), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by nlinarith [norm_nonneg a] : 0 < 1 - ‖a‖ ^ 2)]
  rw [hd]
  field_simp


-- @@ L112-128 verbatim
theorem hasDerivAt_squareRoot {g F : ℂ → ℂ} {x d : ℂ}
    (hg : ContinuousAt g x) (hg0 : g x ≠ 0) (hF : HasDerivAt F d x)
    (he : ∀ z, g z ^ 2 = F z) : HasDerivAt g (d / (2 * g x)) x := by
  have hn : g x + g x ≠ 0 := by simpa [← two_mul] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hg0
  have ht := hF.tendsto_slope.div
    ((hg.add_const (g x)).tendsto.mono_left nhdsWithin_le_nhds) hn
  rw [hasDerivAt_iff_tendsto_slope]
  convert ht.congr' ?_ using 1
  · congr 1
    ring
  have hnear : ∀ᶠ z in 𝓝[≠] x, g z + g x ≠ 0 :=
    ((hg.add_const (g x)).eventually_ne hn).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear] with z hz
  simp only [Pi.div_apply, slope, smul_eq_mul, vsub_eq_sub]
  rw [← he z, ← he x]
  field_simp [hz]
  ring


-- @@ L130-217 verbatim
theorem improve_embedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U)
    {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    {b : ℂ} (hb : ‖b‖ < 1) (hmiss : b ∉ f '' U) :
    ∃ G, NormalizedEmbedding U a G ∧ ‖deriv f a‖ < ‖deriv G a‖ := by
  have hfb : ∀ z ∈ U, f z ≠ b := by
    intro z hz he
    exact hmiss ⟨z, hz, he⟩
  let H : ℂ → ℂ := diskMobius b ∘ f
  have hH' (z : ℂ) (hz : z ∈ U) :
      HasDerivAt H (deriv (diskMobius b) (f z) * deriv f z) z :=
    ((diskMobius_hasDerivAt hb (mem_ball_zero_iff.mp (hf.disk hz)).le).differentiableAt.hasDerivAt).comp z
      (hf.holomorphic.hasDerivAt (hU.mem_nhds hz))
  have hHd : DifferentiableOn ℂ H U := fun z hz =>
    (hH' z hz).differentiableAt.differentiableWithinAt
  have hHdisk : MapsTo H U (ball 0 1) := (diskMobius_mapsTo hb).comp hf.disk
  have hHi : InjOn H U := (diskMobius_injOn hb).comp hf.injective hf.disk
  have hH0 : ∀ z ∈ U, H z ≠ 0 := by
    intro z hz
    dsimp [H, diskMobius, Function.comp_def]
    exact div_ne_zero (sub_ne_zero.mpr (hfb z hz))
      (diskMobius_den_ne_zero hb (mem_ball_zero_iff.mp (hf.disk hz)).le)
  obtain ⟨g, hgc, hge⟩ := Complex.exists_continuousOn_pow_eq hUc hU hHd.continuousOn
    (by rintro ⟨z, hz, he⟩; exact hH0 z hz he) (by norm_num : (2 : ℕ) ≠ 0)
  have hg0 : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz he
    have ht := hge z
    simp only [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ht
    exact hH0 z hz ht.symm
  have hgd (z : ℂ) (hz : z ∈ U) :
      HasDerivAt g (deriv H z / (2 * g z)) z :=
    hasDerivAt_squareRoot (hgc.continuousAt (hU.mem_nhds hz)) (hg0 z hz)
      (hHd.hasDerivAt (hU.mem_nhds hz)) hge
  have hgi : InjOn g U := by
    intro z hz w hw he
    apply hHi hz hw
    rw [← hge z, ← hge w, he]
  have hgb : MapsTo g U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    have hn := congrArg norm (hge z)
    rw [norm_pow] at hn
    have ht : ‖H z‖ < 1 := mem_ball_zero_iff.mp (hHdisk hz)
    nlinarith [sq_nonneg (‖g z‖ - 1)]
  have hgne (z : ℂ) (hz : z ∈ U) : deriv g z ≠ 0 := by
    rw [(hgd z hz).deriv, (hH' z hz).deriv]
    exact div_ne_zero (mul_ne_zero
      (diskMobius_deriv_ne_zero hb (mem_ball_zero_iff.mp (hf.disk hz)).le)
      (hf.derivative z hz)) (mul_ne_zero (by norm_num) (hg0 z hz))
  have hr : ‖g a‖ < 1 := mem_ball_zero_iff.mp (hgb ha)
  have hr0 : 0 < ‖g a‖ := norm_pos_iff.mpr (hg0 a ha)
  let G : ℂ → ℂ := diskMobius (g a) ∘ g
  have hG' (z : ℂ) (hz : z ∈ U) :
      HasDerivAt G (deriv (diskMobius (g a)) (g z) * deriv g z) z :=
    ((diskMobius_hasDerivAt hr (mem_ball_zero_iff.mp (hgb hz)).le).differentiableAt.hasDerivAt).comp z
      (hgd z hz).differentiableAt.hasDerivAt
  have hGN : NormalizedEmbedding U a G := by
    refine ⟨fun z hz => (hG' z hz).differentiableAt.differentiableWithinAt,
      (diskMobius_mapsTo hr).comp hgb, (diskMobius_injOn hr).comp hgi hgb, ?_, ?_⟩
    · intro z hz
      rw [(hG' z hz).deriv]
      exact mul_ne_zero (diskMobius_deriv_ne_zero hr (mem_ball_zero_iff.mp (hgb hz)).le)
        (hgne z hz)
    · exact diskMobius_self _
  refine ⟨G, hGN, ?_⟩
  have hab : ‖g a‖ ^ 2 = ‖b‖ := by
    have ht := congrArg norm (hge a)
    simpa only [norm_pow, H, Function.comp_apply, hf.normalized, diskMobius_zero, norm_neg] using ht
  have hval : ‖deriv G a‖ = (1 - ‖g a‖ ^ 2)⁻¹ *
      ((1 - ‖b‖ ^ 2) * ‖deriv f a‖ / (2 * ‖g a‖)) := by
    rw [(hG' a ha).deriv, norm_mul, diskMobius_norm_deriv_self hr,
      (hgd a ha).deriv, norm_div, (hH' a ha).deriv, norm_mul, hf.normalized,
      diskMobius_norm_deriv_zero hb, norm_mul]
    norm_num
  rw [hval]
  have hp : 0 < ‖deriv f a‖ := norm_pos_iff.mpr (hf.derivative a ha)
  have h1 : 0 < 1 - ‖g a‖ ^ 2 := by nlinarith
  have he : (1 - ‖g a‖ ^ 2)⁻¹ *
      ((1 - ‖b‖ ^ 2) * ‖deriv f a‖ / (2 * ‖g a‖)) =
      ((1 + ‖g a‖ ^ 2) / (2 * ‖g a‖)) * ‖deriv f a‖ := by
    rw [← hab]
    field_simp
    ring
  rw [he]
  have hc : 1 < (1 + ‖g a‖ ^ 2) / (2 * ‖g a‖) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hr)]
  nlinarith


-- @@ L219-227 verbatim
theorem exists_riemannMap {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f ∧ f '' U = ball 0 1 := by
  obtain ⟨f, hf, hmax⟩ := exists_extremalEmbedding hU hUc hproper ha
  refine ⟨f, hf, Subset.antisymm (by simpa using hf.disk.image_subset) ?_⟩
  intro b hb
  by_contra hmiss
  obtain ⟨G, hG, hlt⟩ := improve_embedding hU hUc ha hf (mem_ball_zero_iff.mp hb) hmiss
  exact (not_lt_of_ge (hmax G hG)) hlt


-- @@ L229-235 verbatim
theorem inverse_hasStrictDerivAt {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {z : ℂ} (hz : z ∈ U) (hd : deriv f z ≠ 0) :
    HasStrictDerivAt (Function.invFunOn f U) (deriv f z)⁻¹ (f z) := by
  apply ((hf.analyticOnNhd hU) z hz).hasStrictDerivAt.to_local_left_inverse hd
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hi.leftInvOn_invFunOn hw


-- @@ L237-241 verbatim
theorem inverse_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f) :
    DifferentiableOn ℂ (Function.invFunOn f U) (f '' U) := by
  rintro y ⟨z, hz, rfl⟩
  exact (inverse_hasStrictDerivAt hU hf.holomorphic hf.injective hz (hf.derivative z hz)).hasDerivAt.differentiableAt.differentiableWithinAt


-- @@ L243-255 verbatim
theorem compact_inverse_disk {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {r : ℝ} (hr : r < 1) :
    IsCompact (Function.invFunOn f U '' closedBall 0 r) ∧
      Function.invFunOn f U '' closedBall 0 r ⊆ U := by
  have hsub : closedBall (0 : ℂ) r ⊆ f '' U := by
    rw [hs]
    apply closedBall_subset_ball
    exact hr
  refine ⟨(isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
    ((inverse_holomorphic hU hf).continuousOn.mono hsub), ?_⟩
  rintro z ⟨w, hw, rfl⟩
  exact Function.invFunOn_mem (hsub hw)


-- @@ L257-275 verbatim
theorem norm_tendsto_one_boundary {U : Set ℂ} (hU : IsOpen U)
    {a : ℂ} {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) {p : ℂ} (hp : p ∉ U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro r hr
    have hc := compact_inverse_disk hU hf hs hr
    have hpn : p ∉ Function.invFunOn f U '' closedBall 0 r := fun h => hp (hc.2 h)
    have he : ∀ᶠ z in 𝓝 p, z ∉ Function.invFunOn f U '' closedBall 0 r :=
      hc.1.isClosed.isOpen_compl.mem_nhds hpn
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzU
    by_contra hn
    apply hz
    refine ⟨f z, ?_, hf.injective.leftInvOn_invFunOn hzU⟩
    simpa using le_of_not_gt hn
  · intro r hr
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (mem_ball_zero_iff.mp (hf.disk hz)).trans hr


-- @@ L277-277 verbatim
open InnerProductSpace Real


-- @@ L279-279 verbatim
end Conformal


-- @@ L281-281 verbatim
end DirectCrouzeix


-- @@ L283-283 verbatim
end


-- @@ L285-285 verbatim
end


-- @@ L287-287 verbatim
end


-- @@ L289-289 verbatim
end OAI
