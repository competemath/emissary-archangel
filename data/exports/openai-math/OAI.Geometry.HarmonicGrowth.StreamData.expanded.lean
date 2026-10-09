import OAI.Geometry.HarmonicGrowth.AngularTrace
import OAI.Geometry.HarmonicGrowth.PulseSystem
import OAI.Geometry.HarmonicGrowth.AngularStream
import OAI.Geometry.HarmonicGrowth.GlobalControl


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section



-- @@ L11-11 verbatim
namespace HarmonicCounterexample.AngularStream

-- @@ L12-12 verbatim
open Set Filter Schedule Pulses FiniteControl.SmoothWord

-- @@ L13-13 verbatim
open scoped Topology ContDiff BigOperators

-- @@ L14-14 verbatim
variable {n : ℕ}


-- @@ L16-19 verbatim
lemma scalarPacket_smooth (a : Fin n → ℝ) : ContDiff ℝ ∞ (unitPacketScalar a) := by
  unfold unitPacketScalar packetScalar
  exact contDiff_const.mul (ContDiff.sum (fun i _ => contDiff_const.mul
    ((bump_smooth i).comp (contDiff_const.mul contDiff_id))))


-- @@ L21-27 verbatim
lemma scalarPacket_before (a : Fin n → ℝ) {t : ℝ} (ht : duration n*t < 1) : unitPacketScalar a t=0 := by
  unfold unitPacketScalar packetScalar
  have h : ∑ i : Fin n,a i*bump i (duration n*t)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [bump_zero_before (by have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg _;linarith),mul_zero]
  rw [h,mul_zero]


-- @@ L29-36 verbatim
lemma scalarPacket_after (a : Fin n → ℝ) {t : ℝ} (ht : 2*(n:ℝ) < duration n*t) : unitPacketScalar a t=0 := by
  unfold unitPacketScalar packetScalar
  have h : ∑ i : Fin n,a i*bump i (duration n*t)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : (i:ℝ)+1 ≤ n := by exact_mod_cast i.isLt
    rw [bump_zero_after (by linarith),mul_zero]
  rw [h,mul_zero]


-- @@ L38-39 verbatim
lemma scalarPacket_zero_before (a : Fin n → ℝ) {t : ℝ} (ht : t ≤ 0) : unitPacketScalar a t=0 :=
  scalarPacket_before a (lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (duration_pos n).le ht) (by norm_num))


-- @@ L41-44 verbatim
lemma scalarPacket_zero_after (a : Fin n → ℝ) {t : ℝ} (ht : 1 ≤ t) : unitPacketScalar a t=0 := by
  apply scalarPacket_after a
  have h : duration n ≤ duration n*t := by simpa using mul_le_mul_of_nonneg_left ht (duration_pos n).le
  dsimp [duration] at h ⊢;linarith


-- @@ L46-48 verbatim
/-- The ONE genuine smooth scalar anisotropy attached to an infinite stream. -/
def scalar (s : ℕ → Fin n → ℝ) (qstar : ℝ) (j0 : ℕ) : ℝ → ℝ :=
  Pulses.profile (fun j => unitPacketScalar (s j)) qstar j0


-- @@ L50-51 verbatim
lemma scalar_smooth (s : ℕ → Fin n → ℝ) (qstar : ℝ) (j0 : ℕ) : ContDiff ℝ ∞ (scalar s qstar j0) :=
  Pulses.profile_smooth (fun j => scalarPacket_smooth (s j)) (fun j _ h => scalarPacket_zero_before (s j) h) qstar j0


-- @@ L53-54 verbatim
lemma scalar_initial (s : ℕ → Fin n → ℝ) {qstar t : ℝ} {j0 : ℕ} (ht : t ≤ time j0) : scalar s qstar j0 t=1 :=
  Pulses.profile_initial (fun j _ h => scalarPacket_zero_before (s j) h) ht


-- @@ L56-60 verbatim
lemma scalar_pulse (s : ℕ → Fin n → ℝ) {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j)
    (hlo : time j ≤ t) (hhi : t ≤ time j+pulse j) :
    scalar s qstar j0 t=1+(pulse j)⁻¹*unitPacketScalar (s j) ((t-time j)/pulse j) :=
  Pulses.profile_pulse (fun j _ h => scalarPacket_zero_before (s j) h)
    (fun j _ h => scalarPacket_zero_after (s j) h) hj hlo hhi


-- @@ L62-68 verbatim
lemma scalar_leg (s : ℕ → Fin n → ℝ) {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j)
    (hlo : time j+pulse j ≤ t) (hhi : t ≤ time (j+1)) :
    scalar s qstar j0 t=base qstar j0 t := by
  rw [scalar,Pulses.profile_period (fun j _ h => scalarPacket_zero_before (s j) h)
    (fun j _ h => scalarPacket_zero_after (s j) h) hj (by linarith [pulse_pos j]) hhi,
    base,Pulses.profile_period (by simp) (by simp) hj (by linarith [pulse_pos j]) hhi]
  simp only [Pulses.increment,scalarPacket_zero_after (s j) (t:=((t-time j)/pulse j)) ((le_div_iff₀ (pulse_pos j)).2 (by linarith)),mul_zero]


-- @@ L70-73 verbatim
lemma scalar_rest (s : ℕ → Fin n → ℝ) {qstar t : ℝ} {j0 j : ℕ} (hj : j0 ≤ j)
    (hlo : time j+3*pulse j+dwell j ≤ t) (hhi : t ≤ time (j+1)) : scalar s qstar j0 t=1 :=
  Pulses.profile_rest (fun j _ h => scalarPacket_zero_before (s j) h)
    (fun j _ h => scalarPacket_zero_after (s j) h) hj hlo hhi


-- @@ L75-93 verbatim
/-- Open round collar at the START of every pulse, including the FIRST one. -/
lemma scalar_start_collar (s : ℕ → Fin n → ℝ) (qstar : ℝ) {j0 j : ℕ} (hj : j0 ≤ j) :
    ∀ᶠ t in 𝓝 (time j),scalar s qstar j0 t=1 := by
  have hb : ∀ᶠ t in 𝓝 (time j),duration n*((t-time j)/pulse j)<1 :=
    ((continuous_const.mul ((continuous_id.sub continuous_const).div_const _)).continuousAt.eventually_lt
      continuousAt_const (by simp))
  have he : ∀ᶠ t in 𝓝 (time j),t<time j+pulse j := eventually_lt_nhds (by linarith [pulse_pos j])
  have hl : ∀ᶠ t in 𝓝 (time j),t ≤ time j → scalar s qstar j0 t=1 := by
    by_cases h0 : j=j0
    · subst j;exact Filter.Eventually.of_forall (fun t ht => scalar_initial s ht)
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      have hk : j0 ≤ k := by omega
      have hgap : time k+3*pulse k+dwell k < time (k+1) := by rw [time_succ];linarith [pulse_pos k]
      filter_upwards [eventually_gt_nhds hgap] with t ht ht'
      exact scalar_rest s hk ht.le ht'
  filter_upwards [hb,he,hl] with t ht he hl
  by_cases h : t ≤ time j
  · exact hl h
  · rw [scalar_pulse s hj (le_of_not_ge h) he.le,scalarPacket_before (s j) ht,mul_zero,add_zero]


-- @@ L95-112 verbatim
/-- Open round collar at the END of every pulse. The next ramp starts only
AFTER this collar, so changing back to the dwell angular structure is smooth. -/
lemma scalar_end_collar (s : ℕ → Fin n → ℝ) (qstar : ℝ) {j0 j : ℕ} (hj : j0 ≤ j) :
    ∀ᶠ t in 𝓝 (time j+pulse j),scalar s qstar j0 t=1 := by
  have hb : ∀ᶠ t in 𝓝 (time j+pulse j),2*(n:ℝ)<duration n*((t-time j)/pulse j) :=
    (continuousAt_const.eventually_lt
      ((continuous_const.mul ((continuous_id.sub continuous_const).div_const _)).continuousAt)
      (by rw [add_sub_cancel_left,div_self (ne_of_gt (pulse_pos j)),mul_one];simp [duration]))
  have hlo : ∀ᶠ t in 𝓝 (time j+pulse j),time j<t := eventually_gt_nhds (by linarith [pulse_pos j])
  have hhi : ∀ᶠ t in 𝓝 (time j+pulse j),t<time j+pulse j+pulse j/4 :=
    eventually_lt_nhds (by linarith [pulse_pos j])
  filter_upwards [hb,hlo,hhi] with t hb hlo hhi
  rw [scalar,Pulses.profile_period (fun j _ h => scalarPacket_zero_before (s j) h)
    (fun j _ h => scalarPacket_zero_after (s j) h) hj hlo.le (by rw [time_succ];linarith [pulse_pos j,dwell_pos j]),
    Pulses.increment,scalarPacket_after (s j) hb,mul_zero,zero_add,
    window,ramp_zero ((div_le_iff₀ (pulse_pos j)).2 (by linarith)),
    ramp_zero ((div_le_iff₀ (pulse_pos j)).2 (by linarith [pulse_pos j,dwell_pos j]))]
  ring

-- @@ L113-113 verbatim
end HarmonicCounterexample.AngularStream


-- @@ L115-115 verbatim
end


-- @@ L117-117 verbatim
noncomputable section



-- @@ L120-120 verbatim
namespace HarmonicCounterexample.AngularStream

-- @@ L121-121 verbatim
open Set Filter Schedule Pulses FiniteControl.SmoothWord

-- @@ L122-122 verbatim
open scoped Topology ContDiff BigOperators

-- @@ L123-123 verbatim
variable {n : ℕ}


-- @@ L125-125 verbatim
def scalarShape (i : Fin n) (t : ℝ) : ℝ := duration n*bump i (duration n*t)


-- @@ L127-128 verbatim
lemma scalarShape_smooth (i : Fin n) : ContDiff ℝ ∞ (scalarShape i) :=
  contDiff_const.mul ((bump_smooth i).comp (contDiff_const.mul contDiff_id))


-- @@ L130-143 verbatim
lemma scalarShape_local_zero (i : Fin n) {t : ℝ} (ht : t ∉ Icc (0:ℝ) 1) :
    scalarShape i =ᶠ[𝓝 t] fun _ => 0 := by
  by_cases h : t<0
  · filter_upwards [eventually_lt_nhds h] with u hu
    unfold scalarShape
    have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
    have hh := mul_neg_of_pos_of_neg (duration_pos n) hu
    rw [bump_zero_before (by linarith),mul_zero]
  · have h' : 1<t := by simp only [mem_Icc,not_and_or,not_le] at ht;rcases ht with ht|ht <;> linarith
    filter_upwards [eventually_gt_nhds h'] with u hu
    unfold scalarShape
    have hi : (i:ℝ)+1 ≤ n := by exact_mod_cast i.isLt
    have hh : duration n < duration n*u := by nlinarith [duration_pos n]
    rw [bump_zero_after (by dsimp [duration] at *;linarith),mul_zero]


-- @@ L145-152 verbatim
lemma scalarShape_two_bound (i : Fin n) : ∃ C : ℝ,0 ≤ C ∧
    ∀ t,|deriv (deriv (scalarShape i)) t| ≤ C := by
  have hs := (contDiff_infty_iff_deriv.1 (scalarShape_smooth i)).2
  apply bounded_of_zero_outside (contDiff_infty_iff_deriv.1 hs).2.continuous
  intro t ht
  have h := (scalarShape_local_zero i ht).deriv
  have h' := h.deriv_eq
  simpa using h'


-- @@ L154-158 verbatim
lemma scalarPacket_as_sum (a : Fin n → ℝ) : unitPacketScalar a=fun t => ∑ i,a i*scalarShape i t := by
  funext t
  simp only [unitPacketScalar,packetScalar,scalarShape,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _;ring


-- @@ L160-164 verbatim
lemma scalarPacket_deriv (a : Fin n → ℝ) : deriv (unitPacketScalar a)=
    fun t => ∑ i,a i*deriv (scalarShape i) t := by
  funext t
  rw [scalarPacket_as_sum]
  exact (HasDerivAt.fun_sum (fun i _ => (((scalarShape_smooth i).differentiable (by simp)) t).hasDerivAt.const_mul (a i))).deriv


-- @@ L166-170 verbatim
lemma scalarPacket_deriv_two (a : Fin n → ℝ) : deriv (deriv (unitPacketScalar a))=
    fun t => ∑ i,a i*deriv (deriv (scalarShape i)) t := by
  funext t
  rw [scalarPacket_deriv]
  exact (HasDerivAt.fun_sum (fun i _ => (((contDiff_infty_iff_deriv.1 (scalarShape_smooth i)).2.differentiable (by simp)) t).hasDerivAt.const_mul (a i))).deriv


-- @@ L172-186 verbatim
/-- The second time jet is uniformly bounded on the same fixed amplitude box.
This constant is chosen before the entire infinite history. -/
theorem scalarPacket_two_uniform_bound (n : ℕ) : ∃ C : ℝ,0 ≤ C ∧
    ∀ (a : Fin n → ℝ) (M : ℝ),0 ≤ M → (∀ i,|a i| ≤ M) →
      ∀ t,|deriv (deriv (unitPacketScalar a)) t| ≤ C*M := by
  classical
  choose C hC hb using fun i : Fin n => scalarShape_two_bound i
  refine ⟨∑ i,C i,Finset.sum_nonneg (fun i _ => hC i),fun a M hM ha t => ?_⟩
  rw [scalarPacket_deriv_two]
  calc
    _ ≤ ∑ i : Fin n,|a i*deriv (deriv (scalarShape i)) t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n,C i*M := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,mul_comm (C i) M]
      exact mul_le_mul (ha i) (hb i t) (abs_nonneg _) hM)
    _ = _ := by rw [Finset.sum_mul]


-- @@ L188-195 verbatim
lemma scalarPacket_deriv_eq (a : Fin n → ℝ) (t : ℝ) :
    deriv (unitPacketScalar a) t=unitPacketScalarD a t := by
  have h : HasDerivAt (packetScalar a) (packetScalarD a (duration n*t)) (duration n*t) :=
    HasDerivAt.fun_sum (fun i _ => ((bump_smooth i).differentiable (by simp) _).hasDerivAt.const_mul (a i))
  have hh := (h.comp t ((hasDerivAt_id t).const_mul (duration n))).const_mul (duration n)
  change HasDerivAt (unitPacketScalar a) _ t at hh
  rw [hh.deriv,unitPacketScalarD]
  ring


-- @@ L197-197 verbatim
end HarmonicCounterexample.AngularStream


-- @@ L199-199 verbatim
end


-- @@ L201-201 verbatim
noncomputable section



-- @@ L204-204 verbatim
namespace HarmonicCounterexample.LinearODE

-- @@ L205-205 verbatim
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord

-- @@ L206-206 verbatim
open scoped Topology ContDiff

-- @@ L207-207 verbatim
variable {κ : Type*} (w : PhysicalWord κ)


-- @@ L209-222 verbatim
/-- All three profile jet constants are selected before histories. -/
theorem PhysicalWord.scalar_uniform_bounds : ∃ M C1 C2 : ℝ,
    0 ≤ M ∧ 0 ≤ C1 ∧ 0 ≤ C2 ∧
    ∀ s : ℕ → Fin w.n → ℝ,(∀ j,s j ∈ w.admissible) → ∀ j t,
      |unitPacketScalar (s j) t| ≤ M ∧
      |deriv (unitPacketScalar (s j)) t| ≤ C1 ∧
      |deriv (deriv (unitPacketScalar (s j))) t| ≤ C2 := by
  obtain ⟨U,hU,ha⟩ := w.admissible_uniform_bound
  obtain ⟨C,hC,hb⟩ := unitPacketScalar_uniform_bound w.n
  obtain ⟨D,hD,hd⟩ := scalarPacket_two_uniform_bound w.n
  refine ⟨C*U,C*U,D*U,mul_nonneg hC hU,mul_nonneg hC hU,mul_nonneg hD hU,fun s hs j t => ?_⟩
  have h := hb (s j) U hU (ha _ (hs j)) t
  rw [scalarPacket_deriv_eq]
  exact ⟨h.1,h.2,hd (s j) U hU (ha _ (hs j)) t⟩

-- @@ L223-223 verbatim
end HarmonicCounterexample.LinearODE


-- @@ L225-225 verbatim
end


-- @@ L227-227 verbatim
noncomputable section



-- @@ L230-230 verbatim
namespace HarmonicCounterexample.LinearODE

-- @@ L231-231 verbatim
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord

-- @@ L232-232 verbatim
open scoped Topology ContDiff

-- @@ L233-233 verbatim
variable {κ : Type*} (w : PhysicalWord κ)


-- @@ L235-258 verbatim
/-- The complete global profile has uniform jet budgets selected before every
history and before the late starting index. -/
theorem PhysicalWord.profile_uniform_bounds (qstar : ℝ) : ∃ M C1 C2 : ℝ,
    0 ≤ M ∧ 0 ≤ C1 ∧ 0 ≤ C2 ∧
    ∀ s : ℕ → Fin w.n → ℝ,(∀ j,s j ∈ w.admissible) →
      (∀ j t,|unitPacketScalar (s j) t| ≤ M) ∧
      ∀ j0 j,j0 ≤ j → ∀ t ∈ Icc (time j) (time (j+1)),
        |deriv (scalar s qstar j0) t| ≤ C1/pulse j ∧
        |deriv (deriv (scalar s qstar j0)) t| ≤ C2/pulse j^2 := by
  obtain ⟨M,D1,D2,hM,hD1,hD2,hb⟩ := w.scalar_uniform_bounds
  obtain ⟨B1,B2,hB1,hB2,hb1,hb2⟩ := ramp_derivatives_bounded
  refine ⟨M,D1+2*|qstar-1| *B1,D2+2*|qstar-1| *B2,hM,
    add_nonneg hD1 (by positivity),add_nonneg hD2 (by positivity),fun s hs => ?_⟩
  refine ⟨fun j t => (hb s hs j t).1,fun j0 j hj t ht => ?_⟩
  change |deriv (profile (fun j => unitPacketScalar (s j)) qstar j0) t| ≤ _ ∧
    |deriv (deriv (profile (fun j => unitPacketScalar (s j)) qstar j0)) t| ≤ _
  rw [profile_deriv_period (fun j => scalarPacket_smooth (s j))
      (fun j _ h => scalarPacket_zero_before (s j) h) (fun j _ h => scalarPacket_zero_after (s j) h) hj ht,
    profile_deriv_two_period (fun j => scalarPacket_smooth (s j))
      (fun j _ h => scalarPacket_zero_before (s j) h) (fun j _ h => scalarPacket_zero_after (s j) h) hj ht]
  exact ⟨increment_deriv_bound (fun j => scalarPacket_smooth (s j))
      (fun j t => (hb s hs j t).2.1) hb1 qstar j t,
    increment_deriv_two_bound (fun j => scalarPacket_smooth (s j))
      (fun j t => (hb s hs j t).2.2) hb2 qstar j t⟩


-- @@ L260-274 verbatim
lemma PhysicalWord.scalar_positive_threshold {qstar : ℝ} (hq : 1 ≤ qstar) :
    ∃ J : ℕ,∀ j0,J ≤ j0 → ∀ s : ℕ → Fin w.n → ℝ,
      (∀ j,s j ∈ w.admissible) → ∀ t,1/2 ≤ scalar s qstar j0 t ∧
        scalar s qstar j0 t ≤ qstar+1/2 := by
  obtain ⟨M,D1,D2,hM,hD1,hD2,hb⟩ := w.scalar_uniform_bounds
  obtain ⟨J,hJ⟩ := eventually_atTop.1 (pulse_atTop_limit.eventually_ge_atTop (2*M))
  refine ⟨J,fun j0 hj0 s hs t => ?_⟩
  by_cases ht : t ≤ time j0
  · rw [scalar_initial s ht];constructor <;> linarith
  · obtain ⟨j,hj,hlo,hhi⟩ := GlobalGrowth.grid_bracket time_atTop j0 (le_of_not_ge ht)
    have h := profile_bounds_on_period (fun j _ ht => scalarPacket_zero_before (s j) ht)
      (fun j _ ht => scalarPacket_zero_after (s j) ht) (fun j u => (hb s hs j u).1) hq hj hlo hhi
    change 1-M/pulse j ≤ scalar s qstar j0 t ∧ scalar s qstar j0 t ≤ qstar+M/pulse j at h
    have hq : M/pulse j ≤ 1/2 := (div_le_iff₀ (pulse_pos j)).2 (by linarith [hJ j (hj0.trans hj)])
    constructor <;> linarith


-- @@ L276-313 verbatim
/-- One geometric threshold, before the subsequently tuned infinite stream,
absorbs the radial and BOTH tangent curvature costs on EVERY active period. -/
theorem PhysicalWord.curvature_threshold {m a μ qstar : ℝ}
    (hm : 1 ≤ m) (hμ : 0 < μ) (hμ1 : μ ≤ 1/4) (hqstar : 1 ≤ qstar)
    (ha : Tendsto (Scale.profile μ) atTop (𝓝 a))
    (hH : ∀ q ∈ Icc 1 qstar,0 < m+1-2*q-(m-1)*a^2*q^(-1/m))
    (hV : ∀ q ∈ Icc 1 qstar,0 < (m-1)*q*(q-a^2*q^(-1/m))) :
    ∃ J : ℕ,∀ j0,J ≤ j0 → ∀ s : ℕ → Fin w.n → ℝ,
      (∀ j,s j ∈ w.admissible) →
      (∀ t,1/2 ≤ scalar s qstar j0 t ∧ scalar s qstar j0 t ≤ qstar+1/2) ∧
      ∀ j,j0 ≤ j → ∀ t ∈ Icc (time j) (time (j+1)),
        let q := scalar s qstar j0
        let v := logSlope q
        0 ≤ Berger.radialRicciNumerator (m+1)
          (Scale.slope μ t-v t/m) (v t)
          (deriv (Scale.slope μ) t-deriv v t/m) (deriv v t) ∧
        0 < Berger.horizontalRicciNumerator (m+1)
          ((Scale.profile μ t)^2*(q t)^(-1/m)) (q t)
          (Scale.slope μ t-v t/m) (v t) (deriv (Scale.slope μ) t-deriv v t/m) ∧
        0 < Berger.verticalRicciNumerator (m+1)
          ((Scale.profile μ t)^2*(q t)^(-1/m)) (q t)
          (Scale.slope μ t-v t/m) (v t)
          (deriv (Scale.slope μ) t-deriv v t/m) (deriv v t) := by
  obtain ⟨M,C1,C2,hM,hC1,hC2,hb⟩ := w.profile_uniform_bounds qstar
  obtain ⟨J0,hJ0⟩ := w.scalar_positive_threshold hqstar
  obtain ⟨J1,hJ1⟩ := Berger.radialRicci_of_pulse_budget (C:=C1) hm hμ hμ1
  obtain ⟨J2,hJ2⟩ := Berger.tangentRicci_of_pulse_budget (C1:=C1) (C2:=C2) hM hqstar ha hH hV
  refine ⟨max J0 (max J1 J2),fun j0 hj0 s hs => ?_⟩
  have hj00 : J0 ≤ j0 := (le_max_left _ _).trans hj0
  have hj01 : J1 ≤ j0 := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hj0
  have hj02 : J2 ≤ j0 := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hj0
  refine ⟨hJ0 j0 hj00 s hs,fun j hj t ht => ?_⟩
  have hd := (hb s hs).2 j0 j hj t ht
  have hq := (hJ0 j0 hj00 s hs t).1
  have hv := profile_bounds_on_period (fun j _ h => scalarPacket_zero_before (s j) h)
    (fun j _ h => scalarPacket_zero_after (s j) h) (hb s hs).1 hqstar hj ht.1 ht.2
  exact ⟨hJ1 j (hj01.trans hj) _ t hq hd.1 ht,
    hJ2 j (hj02.trans hj) _ t (scalar_smooth s qstar j0) hq hv.1 hv.2 hd.1 hd.2 ht.1⟩

-- @@ L314-314 verbatim
end HarmonicCounterexample.LinearODE


-- @@ L316-316 verbatim
end


-- @@ L318-318 verbatim
noncomputable section



-- @@ L321-321 verbatim
namespace HarmonicCounterexample.Berger


-- @@ L323-354 verbatim
/-- The horizontal Ricci margin is smallest at the Berger dwell endpoint,
not at an untested point of the ramp. -/
lemma static_horizontal_margin {m a q qstar : ℝ} (hm : 1 < m) (ha : a^2 < 1)
    (hq : q ∈ Set.Icc 1 qstar)
    (hstar : 0 < m+1-2*qstar-(m-1)*a^2*qstar^(-1/m)) :
    0 < m+1-2*q-(m-1)*a^2*q^(-1/m) := by
  let F : ℝ → ℝ := fun x => m+1-2*x-(m-1)*a^2*x^(-1/m)
  have hd (x : ℝ) (hx : 1 ≤ x) :
      HasDerivAt F (-2+(m-1)*a^2/m*x^(-1/m-1)) x := by
    have hp := Real.hasDerivAt_rpow_const (p := -1/m) (Or.inl (by linarith : x ≠ 0))
    convert! ((hasDerivAt_const x (m+1)).sub ((hasDerivAt_id x).const_mul 2)).sub
      (hp.const_mul ((m-1)*a^2)) using 1
    ring
  have hn (x : ℝ) (hx : 1 ≤ x) : -2+(m-1)*a^2/m*x^(-1/m-1) ≤ 0 := by
    have hm0 : 0 < m := by linarith
    have hc0 : 0 ≤ (m-1)*a^2/m := div_nonneg (mul_nonneg (by linarith) (sq_nonneg a)) hm0.le
    have hc1 : (m-1)*a^2/m ≤ 1 := by
      apply (div_le_iff₀ hm0).2
      nlinarith [sq_nonneg a]
    have hp : x^(-1/m-1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx (by have := div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1:ℝ) ≤ 0) hm0.le; linarith)
    have hb := (mul_le_mul_of_nonneg_left hp hc0).trans (by simpa using hc1)
    linarith
  have hanti : AntitoneOn F (Set.Icc 1 qstar) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 1 qstar)
    · intro x hx
      exact (hd x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx).1).hasDerivWithinAt
    · intro x hx
      exact hn x (interior_subset hx).1
  exact hstar.trans_le (hanti hq ⟨hq.1.trans hq.2,le_rfl⟩ hq.2)


-- @@ L356-356 verbatim
end HarmonicCounterexample.Berger


-- @@ L358-358 verbatim
end


-- @@ L360-360 verbatim
noncomputable section



-- @@ L363-363 verbatim
namespace HarmonicCounterexample.Construction

-- @@ L364-364 verbatim
open Filter

-- @@ L365-365 verbatim
open scoped Topology


-- @@ L367-367 verbatim
def qstar : ℝ := 101/100


-- @@ L369-369 verbatim
def a : ℝ := Real.sqrt ((99853/100000:ℝ)*qstar^(1/15:ℝ))


-- @@ L371-371 verbatim
lemma qstar_pos : 0<qstar := by norm_num [qstar]

-- @@ L372-372 verbatim
lemma qstar_ge_one : 1≤qstar := by norm_num [qstar]

-- @@ L373-373 verbatim
lemma a_pos : 0<a := Real.sqrt_pos.2 (mul_pos (by norm_num) (Real.rpow_pos_of_pos qstar_pos _))

-- @@ L374-375 verbatim
lemma a_square : a^2=(99853/100000:ℝ)*qstar^(1/15:ℝ) :=
  Real.sq_sqrt (mul_nonneg (by norm_num) (Real.rpow_nonneg qstar_pos.le _))


-- @@ L377-382 verbatim
lemma qstar_small_power : qstar^(1/15:ℝ) ≤ 1001/1000 := by
  have hp : qstar ≤ (1001/1000:ℝ)^15 := by norm_num [qstar]
  have hh := Real.rpow_le_rpow qstar_pos.le hp (by norm_num : (0:ℝ) ≤ 1/15)
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1001/1000)] at hh
  norm_num at hh ⊢
  exact hh


-- @@ L384-387 verbatim
lemma a_square_lt_one : a^2<1 := by
  rw [a_square]
  have hh := mul_le_mul_of_nonneg_left qstar_small_power (by norm_num : (0:ℝ) ≤ 99853/100000)
  linarith


-- @@ L389-389 verbatim
lemma a_lt_one : a<1 := by nlinarith [a_pos,a_square_lt_one]


-- @@ L391-394 verbatim
lemma a_lower : 99/100 ≤ a := by
  have h := Real.one_le_rpow qstar_ge_one (by norm_num : (0:ℝ) ≤ 1/15)
  have he := a_square
  nlinarith [a_pos]


-- @@ L396-401 verbatim
lemma scale_total_lower : (4/5:ℝ) ≤ Scale.total := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 5)
    (by norm_num : (-1:ℝ) ≤ -1/4)
  norm_num at h
  unfold Scale.total
  linarith [Scale.primitive_nonneg 4]


-- @@ L403-409 verbatim
lemma a_close : Real.exp (-Scale.total/4) ≤ a := by
  rw [← Real.exp_log a_pos,Real.exp_le_exp]
  have h := Real.one_sub_inv_le_log_of_pos a_pos
  have hi : a⁻¹ ≤ (100/99:ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<99/100) a_lower
    simpa using hh
  linarith [scale_total_lower]


-- @@ L411-421 verbatim
lemma static_horizontal (q : ℝ) (hq : q ∈ Set.Icc 1 qstar) :
    0 < 15+1-2*q-(15-1)*a^2*q^(-1/15:ℝ) := by
  apply Berger.static_horizontal_margin (by norm_num : (1:ℝ)<15) a_square_lt_one hq
  rw [a_square]
  have hp : qstar^(1/15:ℝ)*qstar^(-1/15:ℝ)=1 := by
    rw [← Real.rpow_add qstar_pos]
    norm_num
  calc
    _ = 15+1-2*qstar-(15-1)*(99853/100000:ℝ)*
      (qstar^(1/15:ℝ)*qstar^(-1/15:ℝ)) := by ring
    _ > 0 := by rw [hp];norm_num [qstar]


-- @@ L423-425 verbatim
lemma static_vertical (q : ℝ) (hq : q ∈ Set.Icc 1 qstar) :
    0 < (15-1)*q*(q-a^2*q^(-1/15:ℝ)) :=
  Berger.static_vertical_margin (by norm_num) a_square_lt_one hq.1


-- @@ L427-429 verbatim
lemma exists_scale : ∃ μ:ℝ,0<μ ∧ μ≤1/4 ∧
    Tendsto (Scale.profile μ) atTop (𝓝 a) ∧ Real.exp (-μ*Scale.total)=a :=
  Scale.choose_scale a_pos a_lt_one a_close


-- @@ L431-431 verbatim
end HarmonicCounterexample.Construction


-- @@ L433-433 verbatim
end


-- @@ L435-435 verbatim
noncomputable section



-- @@ L438-438 verbatim
namespace HarmonicCounterexample.Control

-- @@ L439-439 verbatim
open Module RealForm ComplexAngular Berger ComplexStarModule

-- @@ L440-440 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L442-442 verbatim
section Generic

-- @@ L443-443 verbatim
variable {V W:Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

-- @@ L444-449 verbatim
lemma conj_traceFree (e:V≃ₗ[ℝ]W) (A:Module.End ℝ V) :
    e.conj (traceFreeEnd A)=traceFreeEnd (e.conj A) := by
  simp only [traceFreeEnd,LinearMap.coe_mk,AddHom.coe_mk,map_sub,map_smul,
    LinearMap.trace_conj',← e.finrank_eq]
  congr 1
  exact congrArg _ (e.conj_id)

-- @@ L450-451 verbatim
lemma conj_mul (e:V≃ₗ[ℝ]W) (A B:Module.End ℝ V) :
    e.conj (A*B)=e.conj A*e.conj B := e.conj_comp B A

-- @@ L452-452 verbatim
end Generic


-- @@ L454-454 verbatim
section Complexification

-- @@ L455-455 verbatim
variable {V:Type*} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V]

-- @@ L456-459 verbatim
lemma complexify_one : complexify (1:Module.End ℝ (selfAdjoint V))=1 := by
  ext x
  change (realPart x:V)+Complex.I • (imaginaryPart x:V)=x
  exact realPart_add_I_smul_imaginaryPart x


-- @@ L461-470 verbatim
lemma complexify_traceFree [FiniteDimensional ℂ V] (A:Module.End ℝ (selfAdjoint V)) :
    complexify (traceFreeEnd A)=traceFreeEnd (complexify A) := by
  let : FiniteDimensional ℝ (selfAdjoint V) := FiniteDimensional.of_surjective realPart realPart_surjective
  change complexifyLinear (A-(LinearMap.trace ℝ _ A/(Module.finrank ℝ _:ℝ)) • 1)=_
  rw [map_sub,map_smul]
  change complexify A-(LinearMap.trace ℝ _ A/(Module.finrank ℝ _:ℝ)) • complexify 1=_
  rw [complexify_one]
  simp only [traceFreeEnd,LinearMap.coe_mk,AddHom.coe_mk,
    complexify_trace (Module.finBasis ℝ _),real_form_finrank,← Complex.ofReal_natCast,← Complex.ofReal_div]
  rfl

-- @@ L471-471 verbatim
end Complexification


-- @@ L473-483 verbatim
lemma restrictReal_traceFree_square (l:ℕ) (J:ComplexStructure (Fin 8⊕Fin 8)) (c:ℝ) :
    restrictReal ((c:ℂ) • traceFreeEnd (harmonicField l J*harmonicField l J))=
      c • traceFreeEnd (restrictReal (harmonicField l J)*restrictReal (harmonicField l J)) := by
  apply complexify_injective
  rw [complexify_restrictReal _ (harmonicEnd_star_of_conj _ (harmonic_weighted_generator_real l c J))]
  change _=complexifyLinear (c • traceFreeEnd (_*_))
  rw [map_smul]
  change _=c • complexify (traceFreeEnd (_*_))
  rw [complexify_traceFree,complexify_mul,
    complexify_restrictReal _ (harmonicField_star l J)]
  rfl


-- @@ L485-490 verbatim
lemma cartesian_conj_rotation (l:ℕ) (J:ComplexStructure (Fin 8⊕Fin 8)) :
    (realCartesianHarmonic l).conj (restrictReal (harmonicField l J))=
      Angular.rotation (J.reindex finSumFinEquiv.symm) l := by
  apply LinearMap.ext;intro P
  change realCartesianHarmonic l (restrictReal (harmonicField l J) ((realCartesianHarmonic l).symm P))=_
  rw [realCartesian_rotation,LinearEquiv.apply_symm_apply]


-- @@ L492-496 verbatim
/-- Actual Cartesian generators share the original real-form simultaneous control. -/
def cartesianGenerator (L:ℕ) (c:Fin L→ℝ) (J:ComplexStructure (Fin 8⊕Fin 8)) :
    ∀l:Fin L,Module.End ℝ (Angular.harmonicPolynomials 16 (l.val+2)) := fun l=>
      c l • traceFreeEnd (Angular.rotation (J.reindex finSumFinEquiv.symm) (l.val+2)*
        Angular.rotation (J.reindex finSumFinEquiv.symm) (l.val+2))


-- @@ L498-502 verbatim
def endTupleConj {α:Type*} {V W:α→Type*}
    [∀i,AddCommGroup (V i)] [∀i,Module ℝ (V i)] [∀i,AddCommGroup (W i)] [∀i,Module ℝ (W i)]
    (e:∀i,V i≃ₗ[ℝ]W i) :
    (∀i,Module.End ℝ (V i)) ≃ₗ⁅ℝ⁆ (∀i,Module.End ℝ (W i)) :=
  (AlgEquiv.piCongrRight (fun i=>(e i).conjAlgEquiv ℝ)).toLieEquiv


-- @@ L504-507 verbatim
def cartesianTupleEquiv (L:ℕ) :
    (∀l:Fin L,Module.End ℝ (realHarmonicSpace (l.val+2))) ≃ₗ⁅ℝ⁆
      (∀l:Fin L,Module.End ℝ (Angular.harmonicPolynomials 16 (l.val+2))) :=
  endTupleConj (fun l:Fin L=>realCartesianHarmonic (l.val+2))


-- @@ L509-511 verbatim
lemma cartesianTupleEquiv_apply (L:ℕ)
    (X:∀l:Fin L,Module.End ℝ (realHarmonicSpace (l.val+2))) (l:Fin L) :
    cartesianTupleEquiv L X l=(realCartesianHarmonic (l.val+2)).conj (X l) := rfl


-- @@ L513-520 verbatim
lemma cartesian_generator_eq (L:ℕ) (c:Fin L→ℝ) (J:ComplexStructure (Fin 8⊕Fin 8)) :
    cartesianTupleEquiv L (realHarmonicTupleGenerator L c J)=cartesianGenerator L c J := by
  funext l
  rw [cartesianTupleEquiv_apply]
  change (realCartesianHarmonic (l.val+2)).conj (restrictReal (_ • traceFreeEnd (_*_)))=_
  rw [restrictReal_traceFree_square,map_smul,conj_traceFree,conj_mul]
  change _=c l • traceFreeEnd (_*_)
  rw [cartesian_conj_rotation]

 
-- @@ L522-539 verbatim
theorem cartesian_simultaneous (L:ℕ) (c:Fin L→ℝ) (hc:∀l,c l≠0)
    {X:∀l:Fin L,Module.End ℝ (Angular.harmonicPolynomials 16 (l.val+2))}
    (hX:∀l,LinearMap.trace ℝ _ (X l)=0) :
    X∈LieSubalgebra.lieSpan ℝ _ (Set.range (cartesianGenerator L c)) := by
  have ht (l:Fin L) : LinearMap.trace ℝ _ ((cartesianTupleEquiv L).symm X l)=0 := by
    change LinearMap.trace ℝ _ ((realCartesianHarmonic (l.val+2)).symm.conj (X l))=0
    rw [LinearMap.trace_conj',hX l]
  have h := harmonic_simultaneous_actual_real L c hc ht
  have hm : X ∈ (LieSubalgebra.lieSpan ℝ _ (Set.range (realHarmonicTupleGenerator L c))).map
      (cartesianTupleEquiv L).toLieHom :=
    (LieSubalgebra.mem_map _ _ _).mpr ⟨(cartesianTupleEquiv L).symm X,h,(cartesianTupleEquiv L).apply_symm_apply X⟩
  rw [LieSubalgebra.map_lieSpan] at hm
  have he : (cartesianTupleEquiv L).toLieHom '' Set.range (realHarmonicTupleGenerator L c)=
      Set.range (cartesianGenerator L c) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext (cartesian_generator_eq L c))
  rw [he] at hm
  exact hm

-- @@ L540-540 verbatim
end HarmonicCounterexample.Control


-- @@ L542-542 verbatim
end


-- @@ L544-544 verbatim
noncomputable section



-- @@ L547-547 verbatim
namespace HarmonicCounterexample.Control

-- @@ L548-548 verbatim
open Module

-- @@ L549-549 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing

-- @@ L550-552 verbatim
variable {α κ:Type*} {V:α→Type*} {ι:α→Type*}
  [∀i,AddCommGroup (V i)] [∀i,Module ℝ (V i)]
  [∀i,Fintype (ι i)] [∀i,DecidableEq (ι i)]


-- @@ L554-556 verbatim
def matrixTupleEquiv (b:∀i,Basis (ι i) ℝ (V i)) :
    (∀i,End ℝ (V i)) ≃ₗ⁅ℝ⁆ (∀i,Matrix (ι i) (ι i) ℝ) :=
  (AlgEquiv.piCongrRight (fun i=>LinearMap.toMatrixAlgEquiv (b i))).toLieEquiv


-- @@ L558-559 verbatim
lemma matrixTupleEquiv_apply (b:∀i,Basis (ι i) ℝ (V i)) (X:∀i,End ℝ (V i)) (i:α) :
    matrixTupleEquiv b X i=LinearMap.toMatrix (b i) (b i) (X i) := rfl


-- @@ L561-576 verbatim
theorem simultaneous_toMatrix (b:∀i,Basis (ι i) ℝ (V i))
    (g:κ→∀i,End ℝ (V i))
    (hg:∀X,(∀i,LinearMap.trace ℝ (V i) (X i)=0)→
      X∈LieSubalgebra.lieSpan ℝ _ (Set.range g)) :
    ∀X:(∀i,Matrix (ι i) (ι i) ℝ),(∀i,(X i).trace=0)→
      X∈LieSubalgebra.lieSpan ℝ _ (Set.range (fun k=>matrixTupleEquiv b (g k))) := by
  intro X hX
  have ht (i:α) : LinearMap.trace ℝ (V i) ((matrixTupleEquiv b).symm X i)=0 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (b i)]
    change (matrixTupleEquiv b ((matrixTupleEquiv b).symm X) i).trace=0
    rw [LieEquiv.apply_symm_apply]
    exact hX i
  have hm : X∈(LieSubalgebra.lieSpan ℝ _ (Set.range g)).map (matrixTupleEquiv b).toLieHom :=
    (LieSubalgebra.mem_map _ _ _).mpr ⟨(matrixTupleEquiv b).symm X,hg _ ht,(matrixTupleEquiv b).apply_symm_apply X⟩
  rw [LieSubalgebra.map_lieSpan] at hm
  simpa only [← Set.range_comp,LieEquiv.coe_toLieHom,Function.comp_def] using hm

-- @@ L577-577 verbatim
end HarmonicCounterexample.Control


-- @@ L579-579 verbatim
end


-- @@ L581-581 verbatim
noncomputable section



-- @@ L584-584 verbatim
namespace HarmonicCounterexample.LinearODE

-- @@ L585-585 verbatim
open Module

-- @@ L586-586 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- @@ L587-590 verbatim
lemma orthogonalMatrix_eigen (T:E→L[ℝ]E) (h:T.toLinearMap.IsSymmetric) :
    orthogonalMatrix (h.eigenvectorBasis rfl) T=Matrix.diagonal (h.eigenvalues rfl) := by
  change LinearMap.toMatrix _ _ T.toLinearMap=_
  exact h.toMatrix_eigenvectorBasis rfl

-- @@ L591-595 verbatim
structure SpectralData (T:E→L[ℝ]E) where
  basis : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E
  value : Fin (Module.finrank ℝ E)→ℝ
  eigen : ∀ i,T (basis i)=value i • basis i
  diagonal : orthogonalMatrix basis T=Matrix.diagonal value


-- @@ L597-601 verbatim
def spectralData (T:E→L[ℝ]E) (h:T.toLinearMap.IsSymmetric) : SpectralData T where
  basis := h.eigenvectorBasis rfl
  value := h.eigenvalues rfl
  eigen i := h.apply_eigenvectorBasis rfl i
  diagonal := orthogonalMatrix_eigen T h

-- @@ L602-602 verbatim
end HarmonicCounterexample.LinearODE


-- @@ L604-604 verbatim
end


-- @@ L606-606 verbatim
noncomputable section



-- @@ L609-609 verbatim
namespace HarmonicCounterexample.Construction

-- @@ L610-610 verbatim
open Module Berger Angular LinearODE Control ComplexAngular

-- @@ L611-611 verbatim
open scoped InnerProductSpace


-- @@ L613-613 verbatim
abbrev H (l:ℕ) := harmonicPolynomials 16 (l+2)

-- @@ L614-614 verbatim
abbrev Index (l:ℕ) := Fin (Module.finrank ℝ (H l))

-- @@ L615-615 verbatim
abbrev CS := ComplexStructure (Fin 8⊕Fin 8)

-- @@ L616-616 verbatim
def Jround : ComplexStructure (Fin 16) := (ComplexStructure.block 8).reindex (finSumFinEquiv (m:=8) (n:=8)).symm


-- @@ L618-619 verbatim
def D (l:ℕ) (J:CS) : H l→L[ℝ]H l :=
  rotationCLM (J.reindex (finSumFinEquiv (m:=8) (n:=8)).symm) (l+2)*rotationCLM (J.reindex (finSumFinEquiv (m:=8) (n:=8)).symm) (l+2)


-- @@ L621-621 verbatim
def Dround (l:ℕ) : H l→L[ℝ]H l := D l (ComplexStructure.block 8)


-- @@ L623-628 verbatim
lemma dim_ge_two (l:ℕ) : 2≤Module.finrank ℝ (H l) := by
  rw [← (realCartesianHarmonic (l+2)).finrank_eq,realHarmonicSpace_finrank,
    harmonicSpace_finrank_sixteen]
  have h1 := Nat.choose_pos (show 14≤l+16 by omega)
  have h2 := Nat.choose_pos (show 14≤l+15 by omega)
  omega


-- @@ L630-630 verbatim
instance indexNontrivial (l:ℕ) : Nontrivial (Index l) := Fin.nontrivial_iff_two_le.mpr (dim_ge_two l)

-- @@ L631-631 verbatim
instance CSnonempty : Nonempty CS := ⟨ComplexStructure.block 8⟩


-- @@ L633-634 verbatim
lemma D_symmetric (l:ℕ) (J:CS) : (D l J).IsSymmetric :=
  rotationCLM_square_symmetric _ _


-- @@ L636-636 verbatim
lemma Dround_symmetric (l:ℕ) : (Dround l).toLinearMap.IsSymmetric := D_symmetric l _


-- @@ L638-638 verbatim
def spectrum (l:ℕ) : SpectralData (Dround l) := spectralData (Dround l) (Dround_symmetric l)

-- @@ L639-639 verbatim
abbrev basis (l:ℕ) : OrthonormalBasis (Index l) ℝ (H l) := (spectrum l).basis

-- @@ L640-640 verbatim
abbrev d0 (l:ℕ) : Index l→ℝ := (spectrum l).value


-- @@ L642-643 verbatim
lemma basis_eigen (l:ℕ) (i:Index l) : Dround l (basis l i)=d0 l i • basis l i := by
  with_reducible exact (spectrum l).eigen i


-- @@ L645-646 verbatim
lemma Dround_diagonal (l:ℕ) : orthogonalMatrix (basis l) (Dround l)=Matrix.diagonal (d0 l) := by
  with_reducible exact (spectrum l).diagonal


-- @@ L648-648 verbatim
def degree (l:ℕ) : ℝ := (l:ℝ)+2

-- @@ L649-649 verbatim
def B (l:ℕ) : ℝ := degree l*(degree l+14)

-- @@ L650-650 verbatim
def beta : ℝ := (a^2)⁻¹

-- @@ L651-651 verbatim
def theta (l:ℕ) : ℝ := -7+Real.sqrt (49+beta*B l)


-- @@ L653-653 verbatim
lemma degree_pos (l:ℕ) : 0<degree l := by unfold degree;positivity

-- @@ L654-654 verbatim
lemma B_pos (l:ℕ) : 0<B l := mul_pos (degree_pos l) (by linarith [degree_pos l])

-- @@ L655-655 verbatim
lemma beta_pos : 0<beta := inv_pos.mpr (sq_pos_of_pos a_pos)

-- @@ L656-660 verbatim
lemma theta_pos (l:ℕ) : 0<theta l := by
  have hb := mul_pos beta_pos (B_pos l)
  have h := Real.sq_sqrt (show 0≤49+beta*B l by linarith)
  have hn := Real.sqrt_nonneg (49+beta*B l)
  unfold theta;nlinarith

-- @@ L661-663 verbatim
lemma theta_root (l:ℕ) : beta*B l-14*theta l-(theta l)^2=0 := by
  have h := Real.sq_sqrt (show 0≤49+beta*B l by have := mul_pos beta_pos (B_pos l);linarith)
  unfold theta;nlinarith


-- @@ L665-667 verbatim
lemma D_nonpos (l:ℕ) (J:CS) (v:H l) : inner ℝ v (D l J v) ≤ 0 := by
  have h := rotationCLM_square_nonpos (J.reindex (finSumFinEquiv (m:=8) (n:=8)).symm) (l+2) v
  exact h


-- @@ L669-674 verbatim
lemma D_lower (l:ℕ) (J:CS) (v:H l) : -(B l*‖v‖^2)≤ inner ℝ v (D l J v) := by
  have h := rotationCLM_square_lower (J.reindex (finSumFinEquiv (m:=8) (n:=8)).symm) (l+2) v
  change _ ≤ inner ℝ v (D l J v) at h
  simp only [Nat.cast_add,Nat.cast_ofNat] at h
  have hb : (l+2:ℝ)^2≤B l := by unfold B degree;nlinarith [Nat.cast_nonneg (α:=ℝ) l]
  exact (by nlinarith [sq_nonneg ‖v‖] : -(B l*‖v‖^2)≤-(l+2:ℝ)^2*‖v‖^2).trans h


-- @@ L676-693 verbatim
def system (L:ℕ) : PulseSystem (fun l:Fin L=>H l.val) (fun l:Fin L=>Index l.val) CS where
  basis l := basis l.val
  r := 1/15
  p₀ := 14
  γ := 10
  M := 2
  B l := B l.val
  β _ := beta
  θ l := theta l.val
  D l J := D l.val J
  hD l := D_nonpos l.val
  hBD l := D_lower l.val
  hM := by norm_num
  hB l := (B_pos l.val).le
  hθ l := theta_pos l.val
  hγ := by norm_num
  hden l := by have := theta_pos l.val;linarith
  hroot l := theta_root l.val


-- @@ L695-695 verbatim
end HarmonicCounterexample.Construction


-- @@ L697-697 verbatim
end


-- @@ L699-699 verbatim
noncomputable section



-- @@ L702-702 verbatim
namespace HarmonicCounterexample.LinearODE

-- @@ L703-703 verbatim
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @@ L704-710 verbatim
lemma slow_linearMap (r B beta p theta:ℝ) (D:E→L[ℝ]E) :
    (bergerSlowGenerator r B beta p theta 1 D).toLinearMap=
      (beta/(p+2*theta)) • ((r*B) • (1:Module.End ℝ E)+D.toLinearMap) := by
  ext v
  simp only [bergerSlowGenerator,mul_one,ContinuousLinearMap.coe_coe,
    smul_apply,add_apply,one_apply_eq_self,LinearMap.smul_apply,
    LinearMap.add_apply,Module.End.one_apply,smul_smul]

-- @@ L711-716 verbatim
lemma orthogonalMatrix_eq_matrix {F:Type*} [NormedAddCommGroup F] {ι:Type*} [Fintype ι] [DecidableEq ι]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (b:OrthonormalBasis ι ℝ F) (T:F→L[ℝ]F)
    (A:Module.End ℝ F) (h:T.toLinearMap=A) :
    orthogonalMatrix b T=LinearMap.toMatrix b.toBasis b.toBasis A := by
  change LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap=_
  rw [h]


-- @@ L718-721 verbatim
lemma orthogonalMatrix_toMatrix {F:Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {ι:Type*} [Fintype ι] [DecidableEq ι]
    (b:OrthonormalBasis ι ℝ F) (T:F→L[ℝ]F) :
    orthogonalMatrix b T=LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap := rfl

-- @@ L722-722 verbatim
end HarmonicCounterexample.LinearODE


-- @@ L724-724 verbatim
end


-- @@ L726-726 verbatim
noncomputable section



-- @@ L729-729 verbatim
namespace HarmonicCounterexample.Control

-- @@ L730-730 verbatim
open Module

-- @@ L731-733 verbatim
variable {α:Type*} {V:α→Type*} {ι:α→Type*}
  [∀i,AddCommGroup (V i)] [∀i,Module ℝ (V i)]
  [∀i,Fintype (ι i)] [∀i,DecidableEq (ι i)]

-- @@ L734-737 verbatim
lemma matrixTupleEquiv_trace (b:∀i,Basis (ι i) ℝ (V i))
    (X:∀i,Module.End ℝ (V i)) (i:α) :
    (matrixTupleEquiv b X i).trace=LinearMap.trace ℝ (V i) (X i) :=
  (LinearMap.trace_eq_matrix_trace ℝ (b i) (X i)).symm

-- @@ L738-738 verbatim
end HarmonicCounterexample.Control


-- @@ L740-740 verbatim
end


-- @@ L742-742 verbatim
noncomputable section



-- @@ L745-745 verbatim
namespace HarmonicCounterexample.Construction

-- @@ L746-746 verbatim
open Module Angular LinearODE Control Berger

-- @@ L747-747 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing

-- @@ L748-748 verbatim
open scoped BigOperators


-- @@ L750-754 verbatim
lemma D_trace (l:ℕ) (J:CS) : LinearMap.trace ℝ (H l) (D l J).toLinearMap=
    -(B l/15)*(Module.finrank ℝ (H l):ℝ) := by
  have h := rotation_square_trace16 (J.reindex (finSumFinEquiv (m:=8) (n:=8)).symm) (l+2)
  simp only [Nat.cast_add,Nat.cast_ofNat] at h
  exact h


-- @@ L756-757 verbatim
lemma rank_ne (l:ℕ) : (Module.finrank ℝ (H l):ℝ)≠0 := by
  exact_mod_cast (show Module.finrank ℝ (H l)≠0 by have := dim_ge_two l;omega)


-- @@ L759-764 verbatim
lemma traceFree_D (l:ℕ) (J:CS) :
    traceFreeEnd (D l J).toLinearMap=(B l/15) • (1:Module.End ℝ (H l))+(D l J).toLinearMap := by
  change (D l J).toLinearMap-(LinearMap.trace ℝ (H l) (D l J).toLinearMap/
    (Module.finrank ℝ (H l):ℝ)) • 1=_
  rw [D_trace,mul_div_cancel_right₀ _ (rank_ne l)]
  module


-- @@ L766-770 verbatim
lemma traceFree_D_trace (l:ℕ) (J:CS) :
    LinearMap.trace ℝ (H l) (traceFreeEnd (D l J).toLinearMap)=0 := by
  rw [traceFree_D,map_add,map_smul,LinearMap.trace_one,D_trace]
  simp only [smul_eq_mul]
  ring


-- @@ L772-772 verbatim
def controlScale (L:ℕ) (l:Fin L) : ℝ := beta/(14+2*theta l.val)

-- @@ L773-774 verbatim
lemma controlScale_ne (L:ℕ) (l:Fin L) : controlScale L l≠0 :=
  div_ne_zero beta_pos.ne' (by have := theta_pos l.val;linarith)


-- @@ L776-782 verbatim
lemma slow_toLinearMap (l:ℕ) (J:CS) :
    (bergerSlowGenerator (1/15) (B l) beta 14 (theta l) 1 (D l J)).toLinearMap=
      (beta/(14+2*theta l)) • traceFreeEnd (D l J).toLinearMap := by
  rw [traceFree_D]
  have h := LinearODE.slow_linearMap (1/15) (B l) beta 14 (theta l) (D l J)
  norm_num only [one_div_mul_eq_div] at h
  with_reducible exact h


-- @@ L784-787 verbatim
lemma D_toLinearMap (l:ℕ) (J:CS) : (D l J).toLinearMap=
    rotation (J.reindex finSumFinEquiv.symm) (l+2)*rotation (J.reindex finSumFinEquiv.symm) (l+2) := by
  ext P
  rfl


-- @@ L789-796 verbatim
lemma generator_eq (L:ℕ) : (system L).generator=
    fun J=>matrixTupleEquiv (fun l:Fin L=>(basis l.val).toBasis)
      (cartesianGenerator L (controlScale L) J) := by
  funext J l
  simp only [PulseSystem.generator,matrixTupleEquiv_apply,cartesianGenerator,system]
  rw [orthogonalMatrix_toMatrix,slow_toLinearMap,D_toLinearMap]
  unfold controlScale
  congr 1


-- @@ L798-804 verbatim
lemma generator_trace (L:ℕ) (J:CS) (l:Fin L) : ((system L).generator J l).trace=0 := by
  rw [generator_eq,matrixTupleEquiv_trace]
  have h := traceFree_D_trace l.val J
  have hm := (LinearMap.trace ℝ (H l.val)).map_smul (controlScale L l)
    (traceFreeEnd (D l.val J).toLinearMap)
  simp only [h,smul_zero] at hm
  exact hm


-- @@ L806-812 verbatim
lemma generator_full (L:ℕ) (X:∀l:Fin L,Matrix (Index l.val) (Index l.val) ℝ)
    (hX:∀l,(X l).trace=0) :
    X∈LieSubalgebra.lieSpan ℝ _ (Set.range (system L).generator) := by
  rw [generator_eq]
  exact simultaneous_toMatrix (fun l:Fin L=>(basis l.val).toBasis)
    (cartesianGenerator L (controlScale L))
    (fun X hX=>cartesian_simultaneous L (controlScale L) (controlScale_ne L) hX) X hX


-- @@ L814-814 verbatim
end HarmonicCounterexample.Construction


-- @@ L816-816 verbatim
end


-- @@ L818-818 verbatim
end OAI
