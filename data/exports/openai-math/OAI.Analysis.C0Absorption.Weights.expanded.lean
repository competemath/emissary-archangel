import OAI.Analysis.C0Absorption.Grid


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Filter Topology

-- @@ L6-6 verbatim
open scoped NNReal BigOperators ZeroAtInfty

-- @@ L7-7 verbatim
open NormedSpace


-- @@ L9-9 verbatim
namespace C0Absorption

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open Set Filter Topology

-- @@ L12-12 verbatim
open scoped NNReal BigOperators ZeroAtInfty


-- @@ L14-14 verbatim
def eta : ℝ := 1/1000

-- @@ L15-15 verbatim
def scheduleH : ℝ := 10000


-- @@ L17-17 verbatim
theorem eta_pos : 0 < eta := by norm_num [eta]

-- @@ L18-18 verbatim
theorem scheduleH_pos : 0 < scheduleH := by norm_num [scheduleH]

-- @@ L19-22 verbatim
theorem schedule_speed : Real.pi/scheduleH ≤ eta/2 := by
  have h := Real.pi_lt_four
  norm_num [scheduleH,eta]
  linarith


-- @@ L24-28 verbatim
theorem bandL_pos (j : ℕ) : 0 < (bandL j : ℝ) := by
  let : Nonempty (BandGrid j) := ⟨fun _ => ⟨0,by constructor; exact neg_nonpos.mpr (Int.natCast_nonneg _); exact Int.natCast_nonneg _⟩⟩
  have hc : (0 : ℝ) < Fintype.card (BandGrid j) := by exact_mod_cast Fintype.card_pos
  simp only [bandL,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,NNReal.coe_pow]
  positivity


-- @@ L30-32 verbatim
def rho : ℕ → ℝ
  | 0 => 1/2
  | j+1 => min (Real.exp (-scheduleH)*rho j/2) (eta/(8*bandL (j+1)))


-- @@ L34-39 verbatim
theorem rho_pos (j : ℕ) : 0 < rho j := by
  induction j with
  | zero => norm_num [rho]
  | succ j ih =>
    change 0 < min _ _
    exact lt_min (by positivity) (div_pos eta_pos (mul_pos (by norm_num) (bandL_pos _)))


-- @@ L41-43 verbatim
theorem rho_step (j : ℕ) : rho (j+1) < Real.exp (-scheduleH)*rho j := by
  have hp : 0 < Real.exp (-scheduleH)*rho j := mul_pos (Real.exp_pos _) (rho_pos j)
  exact (min_le_left _ _).trans_lt (by linarith)


-- @@ L45-48 verbatim
theorem rho_half_step (j : ℕ) : rho (j+1) ≤ rho j/2 := by
  have he : Real.exp (-scheduleH) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num [scheduleH])
  exact (min_le_left _ _).trans (div_le_div_of_nonneg_right
    (by nlinarith [rho_pos j]) (by norm_num))


-- @@ L50-56 verbatim
theorem rho_bound (j : ℕ) : rho j ≤ (1/2 : ℝ)^(j+1) := by
  induction j with
  | zero => norm_num [rho]
  | succ j ih =>
    refine (rho_half_step j).trans ?_
    rw [pow_succ]
    linarith


-- @@ L58-61 verbatim
theorem rho_lt_one (j : ℕ) : rho j < 1 := by
  have hh := rho_bound j
  have hp : (1/2 : ℝ)^(j+1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  exact hh.trans_lt hp


-- @@ L63-68 verbatim
theorem rho_lip_budget {j : ℕ} (hj : 0 < j) : bandL j*rho j ≤ eta/4 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hh : rho (k+1) ≤ eta/(8*bandL (k+1)) := min_le_right _ _
  have hp := bandL_pos (k+1)
  have he := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) hp)).mp hh
  linarith [eta_pos]


-- @@ L70-73 verbatim
theorem rho_tendsto : Tendsto rho atTop (nhds 0) := by
  apply squeeze_zero (fun j => (rho_pos j).le) rho_bound
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp
    (tendsto_add_atTop_nat 1)


-- @@ L75-75 verbatim
def ell (j : ℕ) : ℝ := Real.exp (-scheduleH)*rho (j+1)


-- @@ L77-77 verbatim
theorem ell_pos (j : ℕ) : 0 < ell j := mul_pos (Real.exp_pos _) (rho_pos _)

-- @@ L78-80 verbatim
theorem ell_tendsto : Tendsto ell atTop (nhds 0) := by
  change Tendsto (fun j => Real.exp (-scheduleH)*rho (j+1)) atTop (nhds 0)
  convert (tendsto_const_nhds (x := Real.exp (-scheduleH))).mul (rho_tendsto.comp (tendsto_add_atTop_nat 1)) using 1 <;> simp


-- @@ L82-85 verbatim
theorem log_rho_step (j : ℕ) : Real.log (rho (j+1)) < Real.log (rho j)-scheduleH := by
  have hh := Real.strictMonoOn_log (rho_pos (j+1))
    (mul_pos (Real.exp_pos _) (rho_pos j)) (rho_step j)
  rwa [Real.log_mul (Real.exp_pos _).ne' (rho_pos j).ne',Real.log_exp,neg_add_eq_sub] at hh


-- @@ L87-88 verbatim
def transitionAngle (j : ℕ) (u : ℝ) : ℝ :=
  Real.pi/(2*scheduleH) * min scheduleH (max 0 (Real.log (rho j)-u))


-- @@ L90-93 verbatim
theorem transitionAngle_nonneg (j : ℕ) (u : ℝ) : 0 ≤ transitionAngle j u := by
  unfold transitionAngle
  exact mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num [scheduleH] : 0 ≤ 2*scheduleH))
    (le_min scheduleH_pos.le (le_max_left _ _))


-- @@ L95-100 verbatim
theorem transitionAngle_le (j : ℕ) (u : ℝ) : transitionAngle j u ≤ Real.pi/2 := by
  have hh : min scheduleH (max 0 (Real.log (rho j)-u)) ≤ scheduleH := min_le_left _ _
  have hc : 0 ≤ Real.pi/(2*scheduleH) := div_nonneg Real.pi_pos.le (by norm_num [scheduleH])
  have hb := mul_le_mul_of_nonneg_left hh hc
  have he : Real.pi/(2*scheduleH)*scheduleH=Real.pi/2 := by norm_num [scheduleH]; ring
  exact hb.trans_eq he


-- @@ L102-105 verbatim
theorem transitionAngle_zero (j : ℕ) {u : ℝ} (hu : Real.log (rho j) ≤ u) :
    transitionAngle j u=0 := by
  simp only [transitionAngle,max_eq_left (by linarith : Real.log (rho j)-u ≤ 0),
    min_eq_right scheduleH_pos.le,mul_zero]


-- @@ L107-112 verbatim
theorem transitionAngle_full (j : ℕ) {u : ℝ} (hu : u ≤ Real.log (rho j)-scheduleH) :
    transitionAngle j u=Real.pi/2 := by
  unfold transitionAngle
  rw [min_eq_left (le_max_of_le_right (by linarith : scheduleH ≤ Real.log (rho j)-u))]
  norm_num [scheduleH]
  ring


-- @@ L114-118 verbatim
theorem transitionAngle_dichotomy (j : ℕ) (u : ℝ) :
    transitionAngle (j+1) u=0 ∨ transitionAngle j u=Real.pi/2 := by
  by_cases hu : Real.log (rho (j+1)) ≤ u
  · exact Or.inl (transitionAngle_zero (j+1) hu)
  · exact Or.inr (transitionAngle_full j (by linarith [log_rho_step j]))


-- @@ L120-120 verbatim
def transitionInterval (j : ℕ) : Set ℝ := Icc (Real.log (rho j)-scheduleH) (Real.log (rho j))


-- @@ L122-125 verbatim
theorem log_rho_antitone : Antitone (fun j => Real.log (rho j)) := by
  apply antitone_nat_of_succ_le
  intro j
  linarith [log_rho_step j,scheduleH_pos]


-- @@ L127-137 verbatim
theorem transitionInterval_disjoint : Pairwise (fun i j => Disjoint (transitionInterval i) (transitionInterval j)) := by
  suffices ∀ i j, i<j → Disjoint (transitionInterval i) (transitionInterval j) by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hh|hh
    · exact this i j hh
    · exact (this j i hh).symm
  intro i j hij
  have hh := (log_rho_antitone (Nat.succ_le_of_lt hij)).trans_lt (log_rho_step i)
  apply Set.disjoint_left.mpr
  intro u hi hj
  exact (not_le_of_gt hh) (hi.1.trans hj.2)


-- @@ L139-139 verbatim
end

-- @@ L140-140 verbatim
end C0Absorption


-- @@ L142-142 verbatim
namespace C0Absorption

-- @@ L143-143 verbatim
noncomputable section

-- @@ L144-144 verbatim
open Set Filter Topology

-- @@ L145-145 verbatim
open scoped NNReal BigOperators ZeroAtInfty


-- @@ L147-179 verbatim
theorem finite_variation_sum_lipschitz {A : Type*} [Fintype A]
    (f : A → ℝ → ℝ) (C : A → Set ℝ) {K : ℝ≥0}
    (hdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hf : ∀ i, LipschitzWith K (f i))
    (hconst : ∀ i x, x ∉ C i → ∀ᶠ y in nhds x, f i y=f i x) :
    LipschitzWith K (fun x => ∑ i,f i x) := by
  classical
  have hloc (x : ℝ) : ∀ᶠ y in nhds x,
      dist (∑ i,f i x) (∑ i,f i y) ≤ K*dist x y := by
    by_cases h : ∃ i, x ∈ C i
    · obtain ⟨j,hj⟩ := h
      have hh (i : A) : i ≠ j → ∀ᶠ y in nhds x, f i y=f i x := by
        intro hij
        exact hconst i x (fun hi => Set.disjoint_left.mp (hdis hij) hi hj)
      have he : ∀ᶠ y in nhds x, ∀ i, i≠j → f i y=f i x :=
        Filter.eventually_all.mpr (fun i => by
          by_cases hij : i=j
          · exact Filter.Eventually.of_forall (by simp [hij])
          · filter_upwards [hh i hij] with y hy using fun _ => hy)
      filter_upwards [he] with y hy
      rw [Real.dist_eq,← Finset.sum_sub_distrib,
        Finset.sum_eq_single j (fun i _ hij => by rw [hy i hij,sub_self]) (by simp)]
      exact (hf j).dist_le_mul x y
    · push Not at h
      filter_upwards [Filter.eventually_all.mpr (fun i => hconst i x (h i))] with y hy
      simp only [hy,dist_self]
      positivity
  have hc : Continuous (fun x => ∑ i,f i x) := continuous_finsetSum _ (fun i _ => (hf i).continuous)
  have hl := lipschitzOn_convex_of_local (convex_univ : Convex ℝ (univ : Set ℝ)) hc.continuousOn
    (fun x _ => by simpa only [nhdsWithin_univ] using hloc x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact hl.dist_le_mul x (mem_univ _) y (mem_univ _)


-- @@ L181-181 verbatim
def angleSpeed : ℝ≥0 := ⟨Real.pi/(2*scheduleH),div_nonneg Real.pi_pos.le (by norm_num [scheduleH])⟩


-- @@ L183-194 verbatim
theorem transitionAngle_lipschitz (j : ℕ) : LipschitzWith angleSpeed (transitionAngle j) := by
  have hl : LipschitzWith 1 (fun u : ℝ => Real.log (rho j)-u) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [Real.dist_eq,sub_sub_sub_cancel_left,NNReal.coe_one,one_mul,abs_sub_comm,le_refl]
  have hb := (hl.const_max 0).const_min scheduleH
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change |angleSpeed*(min scheduleH (max 0 (Real.log (rho j)-u)))-
      angleSpeed*(min scheduleH (max 0 (Real.log (rho j)-v)))| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg angleSpeed.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using hb.dist_le_mul u v) angleSpeed.coe_nonneg


-- @@ L196-199 verbatim
theorem transitionAngle_antitone (j : ℕ) : Antitone (transitionAngle j) := by
  intro u v huv
  apply mul_le_mul_of_nonneg_left _ angleSpeed.coe_nonneg
  exact min_le_min_left _ (max_le_max_left _ (by linarith))


-- @@ L201-214 verbatim
theorem transitionAngle_locally_constant (j : ℕ) (u : ℝ) (hu : u ∉ transitionInterval j) :
    ∀ᶠ v in nhds u, transitionAngle j v=transitionAngle j u := by
  have h : u < Real.log (rho j)-scheduleH ∨ Real.log (rho j)<u := by
    change ¬(Real.log (rho j)-scheduleH ≤ u ∧ u ≤ Real.log (rho j)) at hu
    rcases lt_or_ge u (Real.log (rho j)-scheduleH) with h|h
    · exact Or.inl h
    · right
      by_contra hn
      exact hu ⟨h,le_of_not_gt hn⟩
  rcases h with h|h
  · filter_upwards [eventually_lt_nhds h] with v hv
    rw [transitionAngle_full j hv.le,transitionAngle_full j h.le]
  · filter_upwards [eventually_gt_nhds h] with v hv
    rw [transitionAngle_zero j hv.le,transitionAngle_zero j h.le]


-- @@ L216-239 verbatim
theorem angle_sum_distance (J : ℕ) (u v : ℝ) :
    (∑ j : Fin J, |transitionAngle (j+1) u-transitionAngle (j+1) v|) ≤
      angleSpeed*dist u v := by
  have hh := finite_variation_sum_lipschitz
    (fun j : Fin J => transitionAngle (j+1)) (fun j : Fin J => transitionInterval (j+1))
    (fun i j hij => transitionInterval_disjoint (by intro he; exact hij (Fin.ext (by omega))))
    (fun j => transitionAngle_lipschitz (j+1))
    (fun j => transitionAngle_locally_constant (j+1))
  have he (x y : ℝ) (hxy : x≤y) :
      (∑ j : Fin J, |transitionAngle (j+1) x-transitionAngle (j+1) y|) =
        dist (∑ j : Fin J,transitionAngle (j+1) x) (∑ j : Fin J,transitionAngle (j+1) y) := by
    rw [Real.dist_eq,← Finset.sum_sub_distrib,abs_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j _
      exact abs_of_nonneg (sub_nonneg.mpr (transitionAngle_antitone (j+1) hxy))
    · exact Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (transitionAngle_antitone (j+1) hxy))
  rcases le_total u v with huv|hvu
  · rw [he u v huv]
    exact hh.dist_le_mul u v
  · have heq : (∑ j : Fin J, |transitionAngle (j+1) u-transitionAngle (j+1) v|)=
        ∑ j : Fin J, |transitionAngle (j+1) v-transitionAngle (j+1) u| :=
        Finset.sum_congr rfl (fun j _ => abs_sub_comm _ _)
    rw [heq,he v u hvu]
    simpa only [dist_comm] using hh.dist_le_mul v u


-- @@ L241-241 verbatim
end

-- @@ L242-242 verbatim
end C0Absorption


-- @@ L244-244 verbatim
end OAI
