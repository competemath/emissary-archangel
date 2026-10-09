import OAI.Geometry.LatticeCovering.Sampling


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
section

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Real

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
open scoped BigOperators

-- @@ L15-15 verbatim
open MeasureTheory Set

-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
open Module Submodule MeasureTheory

-- @@ L18-18 verbatim
open scoped BigOperators

-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
open Real Filter Topology

-- @@ L21-21 verbatim
noncomputable section

-- @@ L22-22 verbatim
open scoped BigOperators

-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-24 verbatim
open Filter Topology Asymptotics


-- @@ L26-26 verbatim
namespace SingleLatticeCovering.Sampler.Numeric


-- @@ L28-28 verbatim
def cStar : ℝ := Real.log 2 / 8


-- @@ L30-30 verbatim
lemma cStar_pos : 0 < cStar := div_pos (Real.log_pos (by norm_num)) (by norm_num)


-- @@ L32-38 verbatim
lemma tendsto_rpow_ratio {p q : ℝ} (h : p < q) :
    Tendsto (fun b : ℝ => b^p/b^q) atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (sub_pos.mpr h)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  rw [← Real.rpow_sub hb]
  congr 1
  ring


-- @@ L40-47 verbatim
lemma tendsto_rpow_mul_exp_neg_rpow (p : ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun b : ℝ => b^p * Real.exp (-c*b^a)) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p/a) c hc).comp
    (tendsto_rpow_atTop ha)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hb.le]
  rw [mul_div_cancel₀ _ ha.ne']



-- @@ L50-65 verbatim
lemma eventually_first_stage_log :
    ∀ᶠ b : ℝ in atTop,
      Real.log 8 + (1/5 : ℝ)*Real.log b + 2*b^(65/100 : ℝ) ≤
        (Real.log 2/4)*b^(69/100 : ℝ) := by
  have hp : (0 : ℝ) < 69/100 := by norm_num
  have h0 := (tendsto_rpow_atTop hp).inv_tendsto_atTop.const_mul (Real.log 8)
  have h1 := (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero.const_mul (1/5 : ℝ)
  have h2 := (tendsto_rpow_ratio (by norm_num : (65/100 : ℝ) < 69/100)).const_mul (2 : ℝ)
  have hl : Tendsto (fun b : ℝ =>
      (Real.log 8+(1/5 : ℝ)*Real.log b+2*b^(65/100 : ℝ))/b^(69/100 : ℝ)) atTop (𝓝 0) := by
    convert (h0.add h1).add h2 using 1 <;> try norm_num
    funext b
    ring
  have hc : (0 : ℝ) < Real.log 2/4 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  filter_upwards [hl.eventually (gt_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with b hb hb₀
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hb₀ _)).mp hb).le



-- @@ L68-91 verbatim
lemma eventually_thresholds :
    ∀ᶠ b : ℝ in atTop,
      1 < b ∧
      Real.log 8 + (1/5 : ℝ)*Real.log b + 2*b^(65/100 : ℝ) ≤
        (Real.log 2/4)*b^(69/100 : ℝ) ∧
      4/cStar ≤ b^(59/100 : ℝ) ∧
      b^(341/100 : ℝ)*Real.exp (-(Real.log 2/2)*b^(69/100 : ℝ)) ≤ cStar/4 ∧
      b^(1/2 : ℝ)*Real.exp (-cStar*b^(69/100 : ℝ)) ≤ 1/2 ∧
      b^(3/2 : ℝ)*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) ≤ 1/2 := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 59/100)).eventually
    (eventually_ge_atTop (4/cStar))
  have he0 := (tendsto_rpow_mul_exp_neg_rpow (341/100 : ℝ)
    (by norm_num : (0 : ℝ) < 69/100)
    (div_pos (Real.log_pos (by norm_num)) (by norm_num) : (0 : ℝ) < Real.log 2/2)).eventually
    (gt_mem_nhds (div_pos cStar_pos (by norm_num) : (0 : ℝ) < cStar/4))
  have he1 := (tendsto_rpow_mul_exp_neg_rpow (1/2 : ℝ)
    (by norm_num : (0 : ℝ) < 69/100) cStar_pos).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have he2 := (tendsto_rpow_mul_exp_neg_rpow (3/2 : ℝ)
    (by norm_num : (0 : ℝ) < 59/100) (div_pos cStar_pos (by norm_num : (0 : ℝ) < 2))).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_first_stage_log, hpow, he0, he1, he2]
    with b hb hlog hpow he0 he1 he2
  exact ⟨hb, hlog, hpow, he0.le, he1.le, he2.le⟩


-- @@ L93-93 verbatim
def delta (b : ℝ) : ℝ := b^(-1/10 : ℝ)

-- @@ L94-94 verbatim
def theta (s : ℕ) : ℝ := cStar*(s : ℝ)/2


-- @@ L96-96 verbatim
lemma delta_pos {b : ℝ} (hb : 0 < b) : 0 < delta b := Real.rpow_pos_of_pos hb _


-- @@ L98-99 verbatim
lemma delta_lt_one {b : ℝ} (hb : 1 < b) : delta b < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hb (by norm_num)


-- @@ L101-102 verbatim
lemma theta_pos {b : ℝ} {s : ℕ} (hb : 0 < b) (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) :
    0 < theta s := div_pos (mul_pos cStar_pos ((Real.rpow_pos_of_pos hb _).trans_le hs)) (by norm_num)


-- @@ L104-110 verbatim
lemma half_counts (s : ℕ) :
    (s : ℝ)/2-1 ≤ (s/2 : ℕ) ∧ (s : ℝ)/2 ≤ (s-s/2 : ℕ) ∧ s-s/2 ≤ s := by
  have hk : s ≤ 2*(s/2)+1 := by omega
  have hj : s ≤ 2*(s-s/2) := by omega
  have hk' : (s : ℝ) ≤ 2*(s/2 : ℕ)+1 := by exact_mod_cast hk
  have hj' : (s : ℝ) ≤ 2*(s-s/2 : ℕ) := by exact_mod_cast hj
  exact ⟨by linarith, by linarith, Nat.sub_le _ _⟩


-- @@ L112-115 verbatim
lemma rpow_delta_identity {b : ℝ} (hb : 0 < b) :
    b^(69/100 : ℝ)*delta b = b^(59/100 : ℝ) := by
  rw [delta, ← Real.rpow_add hb]
  norm_num


-- @@ L117-124 verbatim
lemma theta_delta_lower {b : ℝ} {s : ℕ} (hb : 0 < b)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) :
    (cStar/2)*b^(59/100 : ℝ) ≤ theta s*delta b := by
  rw [← rpow_delta_identity hb]
  have hh := mul_le_mul_of_nonneg_right hs (delta_pos hb).le
  have hh' := mul_le_mul_of_nonneg_left hh (div_pos cStar_pos (by norm_num : (0 : ℝ) < 2)).le
  dsimp [theta]
  nlinarith only [hh']


-- @@ L126-127 verbatim
lemma two_pow_eq_exp (j : ℕ) : (2 : ℝ)^j = Real.exp ((j : ℝ)*Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]


-- @@ L129-136 verbatim
lemma two_pow_lower {b : ℝ} {s j : ℕ}
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hj : (s : ℝ)/2 ≤ (j : ℝ)) :
    Real.exp ((Real.log 2/2)*b^(69/100 : ℝ)) ≤ (2 : ℝ)^j := by
  rw [two_pow_eq_exp]
  apply Real.exp_le_exp.mpr
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hs hl.le,
    mul_le_mul_of_nonneg_right hj hl.le]



-- @@ L139-165 verbatim
lemma potential_errors_le {b L : ℝ} {s j : ℕ} (hb : 0 < b)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hj : (s : ℝ)/2 ≤ (j : ℝ))
    (hL : L ≤ b^4) (hpow : 4/cStar ≤ b^(59/100 : ℝ))
    (hpoly : b^(341/100 : ℝ)*Real.exp (-(Real.log 2/2)*b^(69/100 : ℝ)) ≤ cStar/4) :
    1/theta s+L/(theta s*(2 : ℝ)^j) ≤ delta b := by
  have hθ := theta_pos hb hs
  have hδ := delta_pos hb
  have ht := theta_delta_lower hb hs
  have he := two_pow_lower hs hj
  have hpow' := (div_le_iff₀ cStar_pos).mp hpow
  have hfirst : 1/theta s ≤ delta b/2 := by
    apply (div_le_iff₀ hθ).mpr
    nlinarith
  have hpoly' : b^(341/100 : ℝ) ≤ (cStar/4)*Real.exp ((Real.log 2/2)*b^(69/100 : ℝ)) := by
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv] at hpoly
    exact (div_le_iff₀ (Real.exp_pos _)).mp hpoly
  have hprod : b^(341/100 : ℝ)*b^(59/100 : ℝ) = b^4 := by
    rw [← Real.rpow_add hb]
    norm_num
  have hfour := mul_le_mul_of_nonneg_right hpoly' (Real.rpow_pos_of_pos hb (59/100 : ℝ)).le
  rw [hprod] at hfour
  have hsecond : b^4/(theta s*(2 : ℝ)^j) ≤ delta b/2 := by
    apply (div_le_iff₀ (mul_pos hθ (by positivity))).mpr
    have hmul := mul_le_mul ht he (Real.exp_pos _).le (mul_pos hθ hδ).le
    nlinarith [hfour]
  have hL' := div_le_div_of_nonneg_right hL (mul_pos hθ (by positivity : (0 : ℝ) < 2^j)).le
  linarith


-- @@ L167-172 verbatim
lemma delta_sq {b : ℝ} (hb : 0 < b) :
    (delta b)^2 = Real.exp (-(1/5 : ℝ)*Real.log b) := by
  rw [delta, Real.rpow_def_of_pos hb, ← Real.exp_nat_mul]
  congr 1
  norm_num
  ring


-- @@ L174-176 verbatim
lemma log_eight : Real.log 8 = 3*Real.log 2 := by
  rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
  norm_num


-- @@ L178-180 verbatim
lemma log_four : Real.log 4 = 2*Real.log 2 := by
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
  norm_num



-- @@ L183-229 verbatim
lemma first_stage_ratio_le {b V μ : ℝ} {s k : ℕ} (hb : 0 < b)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hk : (s : ℝ)/2-1 ≤ (k : ℝ))
    (hμ : 1/2 ≤ μ) (hV : V ≤ Real.exp (2*b^(65/100 : ℝ)))
    (hlog : Real.log 8+(1/5 : ℝ)*Real.log b+2*b^(65/100 : ℝ) ≤
      (Real.log 2/4)*b^(69/100 : ℝ)) :
    (V/((2 : ℝ)^k*(delta b*μ)^2))/Real.exp (-2*theta s) ≤
      Real.exp (-cStar*(s : ℝ)) := by
  have hδ := delta_pos hb
  have hμpos : 0 < μ := by linarith
  have hD : 0 < (2 : ℝ)^k*(delta b*μ)^2 := by positivity
  have hexponent : 2*b^(65/100 : ℝ) ≤
      (k : ℝ)*Real.log 2-(1/5 : ℝ)*Real.log b-Real.log 4-2*cStar*(s : ℝ) := by
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hs' := mul_le_mul_of_nonneg_left hs (div_pos hl (by norm_num : (0 : ℝ) < 4)).le
    have hk' := mul_le_mul_of_nonneg_right hk hl.le
    rw [log_eight] at hlog
    rw [log_four]
    dsimp [cStar]
    nlinarith
  have heq : (2 : ℝ)^k*(delta b)^2/4*Real.exp (-2*cStar*(s : ℝ)) =
      Real.exp ((k : ℝ)*Real.log 2-(1/5 : ℝ)*Real.log b-Real.log 4-2*cStar*(s : ℝ)) := by
    rw [two_pow_eq_exp, delta_sq hb]
    conv_lhs => rw [show (4 : ℝ) = Real.exp (Real.log 4) by rw [Real.exp_log (by norm_num)]]
    rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
    congr 1
    ring
  have hden : (2 : ℝ)^k*(delta b)^2/4 ≤ (2 : ℝ)^k*(delta b*μ)^2 := by
    have hm : (1/4 : ℝ) ≤ μ^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg (delta b))
    have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2^k by positivity)
    nlinarith only [hh']
  have hv : V ≤ (2 : ℝ)^k*(delta b*μ)^2*Real.exp (-2*cStar*(s : ℝ)) := by
    calc
      V ≤ Real.exp (2*b^(65/100 : ℝ)) := hV
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
      _ = _ := heq.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hden (Real.exp_pos _).le
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  apply (div_le_iff₀ hD).mpr
  have hprod : Real.exp (-cStar*(s : ℝ))*Real.exp (-2*theta s) =
      Real.exp (-2*cStar*(s : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [theta]
    ring
  rw [hprod, mul_comm]
  exact hv



-- @@ L232-246 verbatim
lemma failure_tail_le {b : ℝ} {s j : ℕ} (hb : 0 < b)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hj : j ≤ s) (hsb : (s : ℝ) ≤ b) :
    Real.exp (-cStar*(s : ℝ)) + (j : ℝ)*Real.exp (-(theta s*delta b)) ≤
      Real.exp (-cStar*b^(69/100 : ℝ)) +
        b*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) := by
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr cStar_pos.le)
  · apply mul_le_mul
    · exact (Nat.cast_le.mpr hj).trans hsb
    · apply Real.exp_le_exp.mpr
      have h := theta_delta_lower hb hs
      nlinarith only [h]
    · exact (Real.exp_pos _).le
    · exact hb.le


-- @@ L248-262 verbatim
lemma failure_tail_le_rpow {b : ℝ} (hb : 0 < b)
    (h₁ : b^(1/2 : ℝ)*Real.exp (-cStar*b^(69/100 : ℝ)) ≤ 1/2)
    (h₂ : b^(3/2 : ℝ)*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) ≤ 1/2) :
    Real.exp (-cStar*b^(69/100 : ℝ)) +
      b*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) ≤ b^(-1/2 : ℝ) := by
  apply le_of_mul_le_mul_left (a := b^(1/2 : ℝ)) _ (Real.rpow_pos_of_pos hb _)
  have heq : b^(1/2 : ℝ)*b = b^(3/2 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one b]
    rw [← Real.rpow_add hb]
    norm_num
  have hinv : b^(1/2 : ℝ)*b^(-1/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hb]
    norm_num
  rw [mul_add, ← mul_assoc, heq, hinv]
  linarith


-- @@ L264-264 verbatim
end SingleLatticeCovering.Sampler.Numeric


-- @@ L266-266 verbatim
namespace SingleLatticeCovering.Sampler

-- @@ L267-267 verbatim
universe u v

-- @@ L268-268 verbatim
open Numeric


-- @@ L270-270 verbatim
section Endpoint

-- @@ L271-271 verbatim
universe w

-- @@ L272-272 verbatim
variable {G : Type w} [AddCommGroup G] [Fintype G]


-- @@ L274-283 verbatim
lemma variance_le_exp {b : ℝ} {f : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hupper : ∀ x, f x ≤ Real.exp (b^(65/100 : ℝ))) :
    (𝔼 x, (f x-(𝔼 y, f y))^2) ≤ Real.exp (2*b^(65/100 : ℝ)) := by
  rw [variance_eq]
  have h : (𝔼 x, (f x)^2) ≤ Real.exp (2*b^(65/100 : ℝ)) := by
    have hm := expect_mono (fun x => sq_le_sq₀ (hf x) (Real.exp_pos _).le |>.mpr (hupper x))
    rw [Fintype.expect_const, ← Real.exp_nat_mul] at hm
    norm_num at hm
    convert hm using 1 ; norm_num
  linarith [sq_nonneg (𝔼 x, f x)]



-- @@ L286-313 verbatim
lemma sampler_at_thresholds {b : ℝ} (hb : 1 < b)
    (hlog : Real.log 8+(1/5 : ℝ)*Real.log b+2*b^(65/100 : ℝ) ≤
      (Real.log 2/4)*b^(69/100 : ℝ))
    (hpow : 4/cStar ≤ b^(59/100 : ℝ))
    (hpoly : b^(341/100 : ℝ)*Real.exp (-(Real.log 2/2)*b^(69/100 : ℝ)) ≤ cStar/4)
    (hG : Real.log (Fintype.card G) ≤ b^4)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hupper : ∀ x, f x ≤ Real.exp (b^(65/100 : ℝ)))
    (hmean : 1/2 ≤ 𝔼 x, f x) (s : ℕ)
    (hs : b^(69/100 : ℝ) ≤ (s : ℝ)) (hsb : (s : ℝ) ≤ b) :
    probability (fun w : Fin s → G => ∃ x,
      (∑ e : Fin s → Bool, f (x-subsetShift w e))/(2 : ℝ)^s <
        (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y)) ≤
      Real.exp (-cStar*b^(69/100 : ℝ)) +
        b*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) := by
  have hb₀ : 0 < b := zero_lt_one.trans hb
  have hh := half_counts s
  have hθ := theta_pos hb₀ hs
  have hd := delta_pos hb₀
  have hd₁ := delta_lt_one hb
  have hμ : 0 < 𝔼 x, f x := lt_of_lt_of_le (by norm_num) hmean
  have hp := potential_errors_le hb₀ hs hh.2.1 hG hpow hpoly
  have hsample := sampler_explicit_parameters f hf hd hd₁ hθ hμ (s/2) (s-s/2) hp
  have heq : s/2+(s-s/2) = s := by omega
  rw [heq] at hsample
  apply hsample.trans
  apply le_trans (add_le_add (first_stage_ratio_le hb₀ hs hh.1 hmean
    (variance_le_exp hf hupper) hlog) le_rfl)
  exact failure_tail_le hb₀ hs hh.2.2 hsb


-- @@ L315-315 verbatim
end Endpoint






-- @@ L321-348 verbatim
theorem uniform_boolean_sampling :
    ∃ b₀ : ℝ, 1 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b →
      ∀ (G : Type u) [AddCommGroup G] [Fintype G],
        Real.log (Fintype.card G) ≤ b^4 →
        ∀ f : G → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ Real.exp (b^(65/100 : ℝ))) →
        (1/2 ≤ 𝔼 x, f x) → (𝔼 x, f x) ≤ 2 →
        ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
        probability (fun w : Fin s → G => ∀ x,
          (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y) ≤
            (∑ e : Fin s → Bool, f (x-subsetShift w e))/(2 : ℝ)^s) ≥
          1-Real.exp (-cStar*b^(69/100 : ℝ))-
            b*Real.exp (-(cStar/2)*b^(59/100 : ℝ)) ∧
        probability (fun w : Fin s → G => ∃ x,
          (∑ e : Fin s → Bool, f (x-subsetShift w e))/(2 : ℝ)^s <
            (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y)) ≤ b^(-1/2 : ℝ) := by
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp eventually_thresholds
  refine ⟨max b₀ 2, by exact lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro b hb G _ _ hG f hf hupper hmean _ s hs hsb
  obtain ⟨hb₁, hlog, hpow, hpoly, h₁, h₂⟩ := hb₀ b ((le_max_left _ _).trans hb)
  have hfail := sampler_at_thresholds hb₁ hlog hpow hpoly hG f hf hupper hmean s hs hsb
  constructor
  · have hc := probability_compl (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-subsetShift w e))/(2 : ℝ)^s <
          (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y))
    simp only [not_exists, not_lt] at hc
    rw [hc]
    linarith
  · exact hfail.trans (failure_tail_le_rpow (zero_lt_one.trans hb₁) h₁ h₂)



-- @@ L351-351 verbatim
end SingleLatticeCovering.Sampler





-- @@ L356-356 verbatim
noncomputable section


-- @@ L358-358 verbatim
open scoped BigOperators

-- @@ L359-359 verbatim
open Classical


-- @@ L361-361 verbatim
namespace SingleLatticeCovering.Bits

-- @@ L362-362 verbatim
universe u v

-- @@ L363-363 verbatim
variable {I : Type u} [Fintype I]



-- @@ L366-366 verbatim
def bitMass (q : ℝ) (e : Bool) : ℝ := if e then q else 1-q


-- @@ L368-368 verbatim
def productMass (q : I → ℝ) (e : I → Bool) : ℝ := ∏ i, bitMass (q i) (e i)


-- @@ L370-370 verbatim
def integral (q : I → ℝ) (f : (I → Bool) → ℝ) : ℝ := ∑ e, productMass q e * f e


-- @@ L372-373 verbatim
lemma bitMass_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (e : Bool) :
    0 ≤ bitMass q e := by cases e <;> simp [bitMass] <;> linarith


-- @@ L375-377 verbatim
lemma productMass_nonneg {q : I → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (e : I → Bool) : 0 ≤ productMass q e :=
  Finset.prod_nonneg (fun i _ => bitMass_nonneg (hq i) (hq1 i) _)


-- @@ L379-381 verbatim
lemma sum_bitMass (q : ℝ) : (∑ e : Bool, bitMass q e) = 1 := by
  rw [Fintype.sum_bool]
  simp [bitMass]


-- @@ L383-386 verbatim
lemma sum_productMass (q : I → ℝ) : (∑ e, productMass q e) = 1 := by
  unfold productMass
  rw [← Fintype.prod_sum]
  simp only [sum_bitMass, Finset.prod_const_one]


-- @@ L388-389 verbatim
lemma integral_const (q : I → ℝ) (c : ℝ) : integral q (fun _ => c) = c := by
  simp only [integral, ← Finset.sum_mul, sum_productMass, one_mul]


-- @@ L391-393 verbatim
lemma integral_add (q : I → ℝ) (f g : (I → Bool) → ℝ) :
    integral q (fun e => f e+g e) = integral q f+integral q g := by
  simp only [integral, mul_add, Finset.sum_add_distrib]


-- @@ L395-397 verbatim
lemma integral_sub (q : I → ℝ) (f g : (I → Bool) → ℝ) :
    integral q (fun e => f e-g e) = integral q f-integral q g := by
  simp only [integral, mul_sub, Finset.sum_sub_distrib]


-- @@ L399-404 verbatim
lemma integral_smul (q : I → ℝ) (c : ℝ) (f : (I → Bool) → ℝ) :
    integral q (fun e => c*f e) = c*integral q f := by
  simp only [integral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring


-- @@ L406-409 verbatim
lemma integral_sum {J : Type v} [Fintype J] (q : I → ℝ) (f : J → (I → Bool) → ℝ) :
    integral q (fun e => ∑ j, f j e) = ∑ j, integral q (f j) := by
  simp only [integral, Finset.mul_sum]
  exact Finset.sum_comm


-- @@ L411-413 verbatim
lemma integral_mono {q : I → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    {f g : (I → Bool) → ℝ} (hfg : ∀ e, f e ≤ g e) : integral q f ≤ integral q g :=
  Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hfg e) (productMass_nonneg hq hq1 e))




-- @@ L417-420 verbatim
lemma integral_prod (q : I → ℝ) (h : I → Bool → ℝ) :
    integral q (fun e => ∏ i, h i (e i)) = ∏ i, ∑ a : Bool, bitMass (q i) a*h i a := by
  simp only [integral, productMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => bitMass (q i) a*h i a)).symm



-- @@ L423-435 verbatim
lemma integral_coordinate (q : I → ℝ) (i : I) (h : Bool → ℝ) :
    integral q (fun e => h (e i)) = ∑ a : Bool, bitMass (q i) a*h a := by
  classical
  have hp (e : I → Bool) : h (e i) = ∏ j, if j=i then h (e j) else (1 : ℝ) := by simp
  simp_rw [hp]
  rw [integral_prod q (fun j a => if j=i then h a else 1)]
  have he (j : I) : (∑ a : Bool, bitMass (q j) a*(if j=i then h a else 1)) =
      if j=i then (∑ a : Bool, bitMass (q i) a*h a) else 1 := by
    by_cases hj : j=i
    · subst j; simp only [↓reduceIte]
    · simp only [hj, ↓reduceIte, mul_one, sum_bitMass]
  simp_rw [he]
  simp


-- @@ L437-460 verbatim
lemma integral_two_coordinates (q : I → ℝ) {i j : I} (hij : i ≠ j) (h k : Bool → ℝ) :
    integral q (fun e => h (e i)*k (e j)) =
      (∑ a : Bool, bitMass (q i) a*h a)*(∑ a : Bool, bitMass (q j) a*k a) := by
  classical
  have hp (e : I → Bool) : h (e i)*k (e j) =
      ∏ l, (if l=i then h (e l) else 1)*(if l=j then k (e l) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hp]
  rw [integral_prod q (fun l a => (if l=i then h a else 1)*(if l=j then k a else 1))]
  have he (l : I) :
      (∑ a : Bool, bitMass (q l) a*((if l=i then h a else 1)*(if l=j then k a else 1))) =
      (if l=i then (∑ a : Bool, bitMass (q i) a*h a) else 1)*
      (if l=j then (∑ a : Bool, bitMass (q j) a*k a) else 1) := by
    by_cases hli : l=i
    · subst l
      simp only [hij, ↓reduceIte, mul_one]
    · by_cases hlj : l=j
      · subst l
        simp only [hli, ↓reduceIte, one_mul]
      · simp only [hli, hlj, ↓reduceIte, mul_one, sum_bitMass]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp



-- @@ L463-463 verbatim
def count (e : I → Bool) : ℝ := ∑ i, if e i then (1 : ℝ) else 0


-- @@ L465-465 verbatim
def meanCount (q : I → ℝ) : ℝ := ∑ i, q i


-- @@ L467-473 verbatim
lemma integral_count (q : I → ℝ) : integral q count = meanCount q := by
  unfold count meanCount
  rw [integral_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_coordinate q i (fun a => if a then (1 : ℝ) else 0), Fintype.sum_bool]
  simp [bitMass]


-- @@ L475-477 verbatim
lemma count_sub_mean (q : I → ℝ) (e : I → Bool) :
    count e - meanCount q = ∑ i, ((if e i then (1 : ℝ) else 0)-q i) := by
  simp only [count, meanCount, Finset.sum_sub_distrib]


-- @@ L479-502 verbatim
lemma variance_count (q : I → ℝ) :
    integral q (fun e => (count e - meanCount q)^2) = ∑ i, q i*(1-q i) := by
  classical
  have hp (e : I → Bool) : (count e-meanCount q)^2 =
      ∑ i, ∑ j, ((if e i then (1 : ℝ) else 0)-q i)*((if e j then (1 : ℝ) else 0)-q j) := by
    rw [count_sub_mean, pow_two, Finset.sum_mul_sum]
  simp_rw [hp]
  rw [integral_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sum, Finset.sum_eq_single i]
  · have hid : (fun e : I → Bool => ((if e i then (1 : ℝ) else 0)-q i)*
        ((if e i then (1 : ℝ) else 0)-q i)) =
      (fun e => ((if e i then (1 : ℝ) else 0)-q i)^2) := by funext e; ring
    rw [hid, integral_coordinate q i (fun a => ((if a then (1 : ℝ) else 0)-q i)^2), Fintype.sum_bool]
    simp only [bitMass, Bool.false_eq_true, ↓reduceIte]
    ring
  · intro j _ hji
    rw [integral_two_coordinates q (Ne.symm hji)
      (fun a => (if a then (1 : ℝ) else 0)-q i) (fun a => (if a then (1 : ℝ) else 0)-q j),
      Fintype.sum_bool, Fintype.sum_bool]
    simp only [bitMass, Bool.false_eq_true, ↓reduceIte]
    ring
  · simp



-- @@ L505-525 verbatim
theorem few_selected_probability {q : I → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hmean : 0 < meanCount q) {t : ℝ} (ht : t ≤ meanCount q/2) :
    integral q (fun e => if count e < t then (1 : ℝ) else 0) ≤ 4/meanCount q := by
  have hv : integral q (fun e => (count e-meanCount q)^2) ≤ meanCount q := by
    rw [variance_count]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (q i)]
  have hp : (meanCount q)^2/4 * integral q (fun e => if count e < t then (1 : ℝ) else 0) ≤
      integral q (fun e => (count e-meanCount q)^2) := by
    rw [← integral_smul]
    apply integral_mono hq hq1
    intro e
    split_ifs with he
    · have hh : count e < meanCount q/2 := he.trans_le ht
      nlinarith [sq_nonneg (count e-meanCount q/2)]
    · simp only [mul_zero, sq_nonneg]
  have hpos : 0 < (meanCount q)^2/4 := by positivity
  have hquot : meanCount q / ((meanCount q)^2/4) = 4/meanCount q := by field_simp
  rw [← hquot]
  exact (le_div_iff₀ hpos).mpr (by nlinarith [hp.trans hv])



-- @@ L528-528 verbatim
def fairRate (q : ℝ) : ℝ := 2*min q (1-q)

-- @@ L529-529 verbatim
def likelyBit (q : ℝ) : Bool := decide (1/2 ≤ q)

-- @@ L530-531 verbatim
def conditionalBit (q : ℝ) (s e : Bool) : ℝ :=
  if s then 1/2 else if e=likelyBit q then 1 else 0


-- @@ L533-534 verbatim
def conditionalMass (q : I → ℝ) (s e : I → Bool) : ℝ :=
  ∏ i, conditionalBit (q i) (s i) (e i)


-- @@ L536-538 verbatim
lemma fairRate_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ fairRate q := by
  unfold fairRate
  exact mul_nonneg (by norm_num) (le_min hq (sub_nonneg.mpr hq1))


-- @@ L540-544 verbatim
lemma fairRate_le_one (q : ℝ) : fairRate q ≤ 1 := by
  unfold fairRate
  have h := min_le_left q (1-q)
  have h' := min_le_right q (1-q)
  linarith


-- @@ L546-548 verbatim
lemma conditionalBit_nonneg (q : ℝ) (s e : Bool) : 0 ≤ conditionalBit q s e := by
  unfold conditionalBit
  split_ifs <;> norm_num


-- @@ L550-553 verbatim
lemma sum_conditionalBit (q : ℝ) (s : Bool) : (∑ e : Bool, conditionalBit q s e) = 1 := by
  cases s <;> rw [Fintype.sum_bool] <;> unfold conditionalBit <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases likelyBit q <;> norm_num
  · norm_num


-- @@ L555-566 verbatim
lemma bit_mixture (q : ℝ) (e : Bool) :
    (∑ s : Bool, bitMass (fairRate q) s*conditionalBit q s e) = bitMass q e := by
  rw [Fintype.sum_bool]
  by_cases hq : (1/2 : ℝ) ≤ q
  · have hm : min q (1-q) = 1-q := min_eq_right (by linarith)
    have hd : likelyBit q = true := by simp only [likelyBit, decide_eq_true_eq]; exact hq
    cases e <;> simp only [conditionalBit, hd, fairRate, hm, bitMass, Bool.false_eq_true,
      ↓reduceIte] <;> ring
  · have hm : min q (1-q) = q := min_eq_left (by linarith)
    have hd : likelyBit q = false := by simp only [likelyBit, decide_eq_false_iff_not]; exact hq
    cases e <;> simp only [conditionalBit, hd, fairRate, hm, bitMass, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte] <;> ring


-- @@ L568-569 verbatim
lemma conditionalMass_nonneg (q : I → ℝ) (s e : I → Bool) : 0 ≤ conditionalMass q s e :=
  Finset.prod_nonneg (fun _ _ => conditionalBit_nonneg _ _ _)


-- @@ L571-574 verbatim
lemma sum_conditionalMass (q : I → ℝ) (s : I → Bool) : (∑ e, conditionalMass q s e) = 1 := by
  unfold conditionalMass
  rw [← Fintype.prod_sum]
  simp only [sum_conditionalBit, Finset.prod_const_one]



-- @@ L577-582 verbatim
theorem product_mixture (q : I → ℝ) (e : I → Bool) :
    (∑ s, productMass (fun i => fairRate (q i)) s * conditionalMass q s e) = productMass q e := by
  unfold conditionalMass productMass
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i a => bitMass (fairRate (q i)) a * conditionalBit (q i) a (e i))]
  simp only [bit_mixture]



-- @@ L585-595 verbatim
theorem integral_mixture (q : I → ℝ) (f : (I → Bool) → ℝ) :
    integral q f = integral (fun i => fairRate (q i))
      (fun s => ∑ e, conditionalMass q s e*f e) := by
  unfold integral
  simp_rw [← product_mixture q, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro e _
  ring


-- @@ L597-597 verbatim
end SingleLatticeCovering.Bits




-- @@ L601-601 verbatim
namespace SingleLatticeCovering.Bits

-- @@ L602-602 verbatim
universe u w

-- @@ L603-603 verbatim
variable {I : Type u} [Fintype I]



-- @@ L606-606 verbatim
abbrev Selected (s : I → Bool) := {i // s i = true}

-- @@ L607-607 verbatim
abbrev Frozen (s : I → Bool) := {i // ¬s i = true}


-- @@ L609-610 verbatim
def cubeSplit (s : I → Bool) : (I → Bool) ≃ ((Selected s → Bool) × (Frozen s → Bool)) :=
  Equiv.piEquivPiSubtypeProd (fun i => s i=true) (fun _ => Bool)


-- @@ L612-613 verbatim
def filled (q : I → ℝ) (s : I → Bool) (a : Selected s → Bool) : I → Bool :=
  (cubeSplit s).symm (a, fun j => likelyBit (q j))


-- @@ L615-628 verbatim
lemma conditionalMass_split (q : I → ℝ) (s e : I → Bool) :
    conditionalMass q s e =
      (1/2 : ℝ)^(Fintype.card (Selected s)) *
        if (fun j : Frozen s => e j)=(fun j : Frozen s => likelyBit (q j)) then 1 else 0 := by
  classical
  unfold conditionalMass
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => s i=true)]
  have h₁ (j : Selected s) : conditionalBit (q j) (s j) (e j) = (1/2 : ℝ) := by
    simp only [conditionalBit, j.property, ↓reduceIte]
  have h₂ (j : Frozen s) : conditionalBit (q j) (s j) (e j) =
      if e j=likelyBit (q j) then (1 : ℝ) else 0 := by
    simp only [conditionalBit, j.property, Bool.false_eq_true, ↓reduceIte]
  simp_rw [h₁, h₂]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.prod_boole, funext_iff]


-- @@ L630-650 verbatim
lemma conditional_integral_eq_subcube (q : I → ℝ) (s : I → Bool) (f : (I → Bool) → ℝ) :
    (∑ e, conditionalMass q s e*f e) =
      (∑ a : Selected s → Bool, f (filled q s a))/(2 : ℝ)^(Fintype.card (Selected s)) := by
  classical
  calc
    _ = ∑ ab : (Selected s → Bool) × (Frozen s → Bool),
        conditionalMass q s ((cubeSplit s).symm ab)*f ((cubeSplit s).symm ab) :=
      Fintype.sum_equiv (cubeSplit s) _ _ (fun e => by simp only [Equiv.symm_apply_apply])
    _ = ∑ a : Selected s → Bool, (1/2 : ℝ)^(Fintype.card (Selected s))*f (filled q s a) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      have he (d : Frozen s → Bool) :
          (fun j : Frozen s => (cubeSplit s).symm (a,d) j) = d := by
        funext j
        simp [cubeSplit, Equiv.piEquivPiSubtypeProd, j.property]
      simp_rw [conditionalMass_split, he]
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, filled]
    _ = _ := by
      rw [← Finset.mul_sum, one_div, inv_pow, div_eq_mul_inv, mul_comm]


-- @@ L652-654 verbatim
lemma count_eq_card_selected (s : I → Bool) : count s = (Fintype.card (Selected s) : ℝ) := by
  classical
  simp [count, Selected, Fintype.card_subtype]




-- @@ L658-685 verbatim
theorem mixture_lower_bound {q : I → ℝ} (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (good : (I → Bool) → Prop) [DecidablePred good]
    (f : (I → Bool) → ℝ) (hf : ∀ e, 0 ≤ f e) (a : ℝ) (_ : 0 ≤ a)
    (hgood : ∀ s, good s → a ≤ ∑ e, conditionalMass q s e*f e) :
    (1-integral (fun i => fairRate (q i)) (fun s => if good s then 0 else 1))*a ≤ integral q f := by
  rw [integral_mixture q f]
  have hc : integral (fun i => fairRate (q i)) (fun s => if good s then (1 : ℝ) else 0) =
      1-integral (fun i => fairRate (q i)) (fun s => if good s then 0 else 1) := by
    calc
      _ = integral (fun i => fairRate (q i)) (fun s => 1-(if good s then 0 else 1)) := by
        congr 1
        funext s
        split_ifs <;> norm_num
      _ = _ := by rw [integral_sub, integral_const]

  rw [← hc]
  calc
    _ = integral (fun i => fairRate (q i)) (fun s => if good s then a else 0) := by
      rw [mul_comm, ← integral_smul]
      congr 1
      funext s
      split_ifs <;> ring
    _ ≤ _ := by
      apply integral_mono (fun i => fairRate_nonneg (hq i) (hq1 i)) (fun i => fairRate_le_one (q i))
      intro s
      split_ifs with hs
      · exact hgood s hs
      · exact Finset.sum_nonneg (fun e _ => mul_nonneg (conditionalMass_nonneg _ _ _) (hf e))




-- @@ L689-702 verbatim
lemma expect_restrict {G : Type w} [Fintype G] [Nonempty G] (s : I → Bool)
    (f : (Selected s → G) → ℝ) :
    (𝔼 w : I → G, f (fun j : Selected s => w j)) = 𝔼 v : Selected s → G, f v := by
  classical
  let E := Equiv.piEquivPiSubtypeProd (fun i => s i=true) (fun _ => G)
  calc
    _ = 𝔼 ab : (Selected s → G) × (Frozen s → G), f ab.1 :=
      Fintype.expect_equiv E _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Fintype.expect_eq_sum_div_card, Fintype.card_prod, Nat.cast_mul,
        Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      have h : (Fintype.card (Frozen s → G) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp


-- @@ L704-704 verbatim
end SingleLatticeCovering.Bits





-- @@ L709-709 verbatim
end

-- @@ L710-710 verbatim
end

-- @@ L711-711 verbatim
end

-- @@ L712-712 verbatim
end

-- @@ L713-713 verbatim
end

-- @@ L714-714 verbatim
end

-- @@ L715-715 verbatim
end

-- @@ L716-716 verbatim
end

-- @@ L717-717 verbatim
end

-- @@ L718-718 verbatim
end


-- @@ L720-720 verbatim
end OAI
