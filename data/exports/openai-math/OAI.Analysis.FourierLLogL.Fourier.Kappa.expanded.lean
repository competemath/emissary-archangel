import OAI.Analysis.FourierLLogL.Fourier.Haar

-- @@ L2-2 verbatim
/-! # The translation-averaged Haar kernel -/


-- @@ L4-4 verbatim
open MeasureTheory Filter Set Function

-- @@ L5-5 verbatim
open scoped ENNReal BigOperators Topology Real


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
namespace FourierLLogL.Period

-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-13 verbatim
def kappa (t : ℝ) : ℝ :=
  ∫ v, haarG v * haarH (v-t)


-- @@ L15-19 verbatim
lemma kappa_eq_mean (t : ℝ) : kappa t =
    ∫ v, haarG v * haarH (v-t) ∂μ₁ := by
  apply Eq.symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv; rw [G_outside hv, zero_mul]


-- @@ L21-21 verbatim
private def Step (a b x : ℝ) : ℝ := (Ico a b).indicator (fun _ => 1) x

-- @@ L22-22 verbatim
private def P (n : ℕ) (x : ℝ) := Step ((n:ℝ)/4) ((n:ℝ)/4+1/4) x


-- @@ L24-24 verbatim
def hatK (x : ℝ) : ℝ := max 0 (1/4 - |x|)


-- @@ L26-30 verbatim
private lemma step_split {a b c : ℝ} (h : a ≤ b) (h' : b ≤ c) (x) :
    Step a c x = Step a b x + Step b c x := by
  unfold Step
  simp only [indicator_apply, mem_Ico]
  split_ifs <;> grind


-- @@ L32-37 verbatim
private lemma haarH_step (x) :
    haarH x = (P 0 x + P 1 x) - (P 2 x + P 3 x) := by
  change Step 0 (1/2) x - Step (1/2) 1 x = _
  rw [step_split (b:=1/4) (by norm_num) (by norm_num) x,
    step_split (c:=1) (b:=3/4) (by norm_num) (by norm_num) x]
  norm_num [P]


-- @@ L39-42 verbatim
private lemma step_twice (a b c x : ℝ) :
    Step b c (2*x-a) = Step ((b+a)/2) ((c+a)/2) x := by
  simp only [Step, indicator_apply, mem_Ico]
  split_ifs <;> grind


-- @@ L44-50 verbatim
private lemma haarG_step (x) :
    haarG x = (P 0 x - P 1 x) - (P 2 x - P 3 x) := by
  change Step 0 (1/2) (2*x) - Step (1/2) 1 (2*x) -
    (Step 0 (1/2) (2*x-1) - Step (1/2) 1 (2*x-1)) = _
  nth_rw 1 2 [show 2*x = 2*x - 0 from (sub_zero _).symm]
  simp only [step_twice]
  norm_num [P]


-- @@ L52-54 verbatim
private lemma step_trans (a b t x : ℝ) : Step a b (x-t) = Step (a+t) (b+t) x := by
  simp only [Step, indicator_apply, mem_Ico]
  split_ifs <;> grind


-- @@ L56-59 verbatim
private lemma step_mul (a b c d x : ℝ) :
    Step a b x * Step c d x = Step (max a c) (min b d) x := by
  simp only [Step, indicator_apply, mem_Ico, max_le_iff, lt_min_iff]
  split_ifs <;> grind


-- @@ L61-63 verbatim
private lemma integrable_step (a b) : Integrable (Step a b) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact integrable_const _


-- @@ L65-69 verbatim
private lemma integral_step (a b) : (∫ v, Step a b v) = max 0 (b-a) := by
  unfold Step
  rw [integral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal']
  rw [max_comm]


-- @@ L71-73 verbatim
private lemma pair_id (t x : ℝ) (n m) : P n x * P m (x-t) =
    Step (max ((n:ℝ)/4) ((m:ℝ)/4+t)) (min ((n:ℝ)/4+1/4) ((m:ℝ)/4+1/4+t)) x := by
  unfold P; rw [step_trans, step_mul]


-- @@ L75-77 verbatim
private lemma integrable_pair (t : ℝ) (n m) : Integrable (fun x => P n x * P m (x-t)) := by
  simp_rw [pair_id]
  exact integrable_step _ _


-- @@ L79-85 verbatim
private lemma integral_pair (t : ℝ) (n m) : (∫ x, P n x * P m (x-t)) =
    hatK (t-(((n:ℝ)-m)/4)) := by
  simp_rw [pair_id]
  rw [integral_step, hatK]
  congr 1
  rw [abs_eq_max_neg]
  grind


-- @@ L87-114 verbatim
lemma kappa_eq (t : ℝ) :
    kappa t = hatK (t-3/4) - hatK (t+3/4) + 3*hatK (t+1/4) - 3*hatK (t-1/4) := by
  let F (n : ℕ) (x : ℝ) := P n x * haarH (x-t)
  let G (n : ℕ) :=
    (∫ x, P n x * P 0 (x-t)) + (∫ x, P n x * P 1 (x-t)) -
    ((∫ x, P n x * P 2 (x-t)) + (∫ x, P n x * P 3 (x-t)))
  have H (n : ℕ) : Integrable (F n) ∧ (∫ x, F n x) = G n := by
    let f (m : ℕ) (x : ℝ) := P n x * P m (x-t)
    have hm (m) : Integrable (f m) := integrable_pair t n m
    have he (x : ℝ) : F n x = (f 0 x + f 1 x)-(f 2 x + f 3 x) := by
      unfold F f; rw [haarH_step]; ring
    have hfunc : F n = fun x => (f 0 x + f 1 x)-(f 2 x + f 3 x) := funext he
    have h1 : Integrable fun x => f 0 x + f 1 x := (hm _).add (hm _)
    have h2 : Integrable fun x => f 2 x + f 3 x := (hm _).add (hm _)
    rw [hfunc, integral_sub h1 h2, integral_add (hm 0) (hm 1), integral_add (hm 2) (hm 3)]
    exact ⟨h1.sub h2, rfl⟩
  have he (x) : haarG x * haarH (x-t) = (F 0 x - F 1 x)-(F 2 x - F 3 x) := by
    rw [haarG_step]; unfold F; ring
  unfold kappa
  simp_rw [he]
  have h1 : Integrable (fun x => F 0 x - F 1 x) := (H _).1.sub (H _).1
  have h2 : Integrable (fun x => F 2 x - F 3 x) := (H _).1.sub (H _).1
  rw [integral_sub h1 h2, integral_sub (H 0).1 (H 1).1, integral_sub (H 2).1 (H 3).1]
  simp_rw [(H _).2]
  dsimp only [G]
  simp_rw [integral_pair]
  push_cast
  ring_nf


-- @@ L116-116 verbatim
lemma hatK_cont : Continuous hatK := by unfold hatK; fun_prop

-- @@ L117-117 verbatim
lemma hatK_neg (x) : hatK (-x) = hatK x := by simp [hatK]

-- @@ L118-118 verbatim
lemma hatK_bound (x) : |hatK x| ≤ 1/4 := by unfold hatK; grind

-- @@ L119-119 verbatim
lemma hatK_zero {x : ℝ} (hx : (1/4:ℝ) ≤ |x|) : hatK x = 0 := max_eq_left (by linarith)


-- @@ L121-125 verbatim
lemma kappa_cont : Continuous kappa := by
  have heq := funext kappa_eq
  rw [heq]
  have hh := hatK_cont
  fun_prop


-- @@ L127-131 verbatim
lemma kappa_neg (t) : kappa (-t) = - kappa t := by
  rw [kappa_eq, kappa_eq]
  simp only [show ∀ a : ℝ, -t+a = -(t-a) by intro a; ring,
    show ∀ a : ℝ, -t-a = -(t+a) by intro a; ring, hatK_neg]
  ring


-- @@ L133-136 verbatim
lemma kappa_outside (t : ℝ) (ht : 1 ≤ |t|) : kappa t = 0 := by
  rw [kappa_eq]
  rw [hatK_zero (by grind), hatK_zero (by grind), hatK_zero (by grind), hatK_zero (by grind)]
  norm_num


-- @@ L138-144 verbatim
lemma kappa_bound (t : ℝ) : |kappa t| ≤ 2 := by
  rw [kappa_eq]
  have a := hatK_bound (t-3/4)
  have b := hatK_bound (t+3/4)
  have c := hatK_bound (t+1/4)
  have d := hatK_bound (t-1/4)
  grind



-- @@ L147-168 verbatim
lemma hatK_integral (a : ℝ) : (∫ t in Ico (a-1/4) (a+1/4), hatK (t-a)) = 1/16 := by
  have hc : Continuous fun t => hatK (t-a) := hatK_cont.comp (continuous_id.sub continuous_const)
  rw [seg_eq_interval _ (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (a-1/4) a)
      (hc.intervalIntegrable a (a+1/4))]
  have hL : (∫ t in a-1/4..a, hatK (t-a)) = ∫ t in a-1/4..a, (t+(1/4-a)) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    unfold hatK
    grind
  have hR : (∫ t in a..a+1/4, hatK (t-a)) = ∫ t in a..a+1/4, ((1/4+a)-t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    unfold hatK
    grind
  rw [hL,hR, intervalIntegral.integral_add, intervalIntegral.integral_sub (a:=a)]
  · norm_num
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop


-- @@ L170-176 verbatim
lemma hatK_inside {a : ℝ} (ha : 1/4 ≤ a) (ha' : a ≤ 3/4) :
    (∫ t in Ico (0:ℝ) 1, hatK (t-a)) = 1/16 := by
  have hh (t) (ht : t ∉ Ico (a-1/4) (a+1/4)) : hatK (t-a) = 0 :=
    hatK_zero (by grind)
  rw [← hatK_integral a, setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero hh]
  intro t ht; apply hh; grind


-- @@ L178-182 verbatim
lemma hatK_outside {a : ℝ} (ha : 1/4 ≤ a) :
    (∫ t in Ico (0:ℝ) 1, hatK (t+a)) = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero ?_
  intro t ht
  exact hatK_zero (by grind)


-- @@ L184-184 verbatim
def constK : ℝ := -1/8


-- @@ L186-203 verbatim
lemma kappa_integral : (∫ t in Ico (0:ℝ) 1, kappa t) = constK := by
  simp_rw [kappa_eq]
  have hL (a : ℝ) : IntegrableOn (fun t => hatK (t-a)) (Ico (0:ℝ) 1) := by
    refine seg_integrable _ (hatK_cont.measurable.comp (by fun_prop)) (1/4) _ _ ?_
    intro t _; exact hatK_bound _
  have hR (a : ℝ) : IntegrableOn (fun t => hatK (t+a)) (Ico (0:ℝ) 1) := by
    simpa using hL (-a)
  rw [integral_sub, integral_add, integral_sub]
  · rw [integral_const_mul, integral_const_mul, hatK_inside (by norm_num) (by norm_num),
      hatK_inside (by norm_num) (by norm_num), hatK_outside (by norm_num),
      hatK_outside (by norm_num)]; norm_num [constK]
  all_goals first
    | exact hR _
    | exact hL _
    | exact (hL _).sub (hR _)
    | exact Integrable.const_mul (hR _) _
    | exact Integrable.const_mul (hL _) _
    | exact ((hL _).sub (hR _)).add (Integrable.const_mul (hR _) _)


-- @@ L205-205 verbatim
end

-- @@ L206-206 verbatim
end FourierLLogL.Period


-- @@ L208-208 verbatim
end OAI
