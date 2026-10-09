import OAI.Probability.EntangledGames.ConditionedStep


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_I u_Ω


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
namespace ThresholdParallelRepetition.FiniteProbability.Tests

-- @@ L10-10 verbatim
open Law

-- @@ L11-12 verbatim
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)


-- @@ L14-14 verbatim
def threshold (s : ℝ) : ℝ := ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0)

-- @@ L15-17 verbatim
omit [DecidableEq I] in
lemma threshold_nonneg (s : ℝ) : 0 ≤ threshold ρ win s := by
  apply avg_nonneg; intro ω; split_ifs <;> norm_num

-- @@ L18-20 verbatim
omit [DecidableEq I] in
lemma threshold_le_one (s : ℝ) : threshold ρ win s ≤ 1 := by
  apply avg_le_const; intro ω; split_ifs <;> norm_num


-- @@ L22-33 verbatim
omit [DecidableEq I] in
lemma threshold_markov {s : ℝ} (_hs : 0 ≤ s) : threshold ρ win s*s ≤ ρ.avg (rate win) := by
  change ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0)*s ≤ _
  rw [mul_comm]
  change s • ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0) ≤ _
  rw [← avg_smul]
  apply ρ.avg_mono
  intro ω
  change s*(if s ≤ rate win ω then 1 else 0) ≤ rate win ω
  split_ifs with h
  · simpa using h
  · simpa using rate_nonneg win ω


-- @@ L35-44 verbatim
omit [DecidableEq I] in
lemma threshold_mean_bound {v δ : ℝ} (hδ : 0 < δ) (hs : v+δ ≤ 1)
    (hmean : ρ.avg (rate win) ≤ v) : threshold ρ win (v+δ) ≤ Real.exp (-δ) := by
  have hmean0 : 0 ≤ ρ.avg (rate win) := ρ.avg_nonneg (rate_nonneg win)
  have hv : 0 ≤ v := hmean0.trans hmean
  have hm := (threshold_markov ρ win (show 0 ≤ v+δ by linarith)).trans hmean
  have hq := threshold_le_one ρ win (v+δ)
  have hmul := mul_nonneg (show 0 ≤ 1-(v+δ) by linarith) (show 0 ≤ 1-threshold ρ win (v+δ) by linarith)
  have he := Real.add_one_le_exp (-δ)
  nlinarith


-- @@ L46-53 verbatim
lemma geometric_bound {v δ : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1) (T : ℕ) :
    (∑ s ∈ Finset.range T, (v+δ/2)^s) ≤ 2/δ := by
  have hr : 0 ≤ v+δ/2 := by linarith
  have hsum : 0 ≤ ∑ s ∈ Finset.range T, (v+δ/2)^s := Finset.sum_nonneg (fun s _ => pow_nonneg hr s)
  have hg := geom_sum_mul_neg (v+δ/2) T
  have hm := mul_le_mul_of_nonneg_left (show δ/2 ≤ 1-(v+δ/2) by linarith) hsum
  apply (le_div_iff₀ hδ).mpr
  nlinarith [pow_nonneg hr T]


-- @@ L55-64 verbatim
lemma threshold_power_bound {v δ e : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1)
    (he : 0 ≤ e) (T : ℕ)
    (hstep : ∀ c : Finset I, c.card < T →
      (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) ≤ (v+δ/2)*mass ρ win c+e) :
    threshold ρ win (v+δ)*(v+δ)^T ≤ (v+δ/2)^T+e*(2/δ) := by
  have hlo := threshold_moment_lower ρ win (show 0 ≤ v+δ by linarith) T
  have hhi := moment_upper ρ win (show 0 ≤ v+δ/2 by linarith) he T hstep T ∅ (by simp)
  rw [mass_empty, mul_one] at hhi
  have hg := mul_le_mul_of_nonneg_left (geometric_bound hv hδ hs T) he
  exact hlo.trans (hhi.trans (by linarith))


-- @@ L66-66 verbatim
end ThresholdParallelRepetition.FiniteProbability.Tests


-- @@ L68-68 verbatim
end


-- @@ L70-70 verbatim
noncomputable section

-- @@ L71-71 verbatim
open scoped BigOperators MatrixOrder ComplexOrder

-- @@ L72-72 verbatim
open Matrix

-- @@ L73-73 verbatim
namespace ThresholdParallelRepetition

-- @@ L74-74 verbatim
open QuantumSampling FiniteProbability Law MixedExposure

-- @@ L75-75 verbatim
namespace RepeatedModel

-- @@ L76-80 verbatim
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)

-- @@ L81-81 verbatim
include hμ hV


-- @@ L83-105 verbatim
lemma all_event_step {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (T : ℕ)
    (hT : (T : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))))
    (c : Finset I) (hc : c.card < T) :
    (uniform (R := I)).avg (fun i => M.mass (insert i c)) ≤
      (entangledValue G+δ/2)*M.mass c+Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83)) := by
  have hk : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : (1:ℝ) ≤ (((a+1)*(b+1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
  have hc' : (c.card : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))) :=
    (show (c.card : ℝ) ≤ T by exact_mod_cast hc.le).trans hT
  by_cases hp : Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83)) ≤ M.mass c
  · have hp0 := (Real.exp_pos _).trans_le hp
    obtain ⟨hsize, hcard, hsmall⟩ := testing_parameters_good hδ hδ1 hk hd hc' hp
    have hcNat : c.card < Fintype.card I := by exact_mod_cast hcard
    have hs : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
        ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80 := by
      simpa only [Nat.cast_sub hcNat.le] using hsmall
    exact (M.good_event_step G hμ hV c hp0 hcNat hδ hδ1 hsize hs).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hh := (uniform (R := I)).avg_le_const (fun i => M.mass_insert_le c i)
    have hv : 0 ≤ entangledValue G+δ/2 := by linarith [entangledValue_nonneg G]
    have hm := mul_nonneg hv (M.mass_nonneg c)
    linarith


-- @@ L107-114 verbatim
lemma threshold_power_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) (T : ℕ)
    (hT : (T : ℝ) ≤ δ^9*(Fintype.card I : ℝ)/((2:ℝ)^90*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ)))) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ)*(entangledValue G+δ)^T ≤
      (entangledValue G+δ/2)^T+Real.exp (-(δ^8*(Fintype.card I : ℝ)/(2:ℝ)^83))*(2/δ) := by
  have hv := entangledValue_nonneg G
  have hδ1 : δ ≤ 1 := by linarith
  exact Tests.threshold_power_bound M.joint M.winsAt hv hδ hs (Real.exp_pos _).le T
    (fun c hc => M.all_event_step G hμ hV hδ hδ1 T hT c hc)


-- @@ L116-118 verbatim
lemma threshold_mean_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ) ≤ Real.exp (-δ) :=
  Tests.threshold_mean_bound M.joint M.winsAt hδ hs (M.unconditional_rate_le_value G hμ hV)


-- @@ L120-120 verbatim
end RepeatedModel

-- @@ L121-121 verbatim
end ThresholdParallelRepetition


-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end OAI
