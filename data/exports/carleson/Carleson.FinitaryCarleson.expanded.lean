module

public import Carleson.Discrete.MainTheorem
public import Carleson.TileExistence


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
open MeasureTheory Measure NNReal Metric Complex Set

-- @@ L9-9 verbatim
open scoped ENNReal

-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
open scoped ShortVariables

-- @@ L13-14 verbatim
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]


-- @@ L16-26 verbatim
theorem integrable_tile_sum_operator
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) {x : X} {s : ℤ} :
    Integrable fun y ↦ Ks s x y * f y * exp (I * (Q x y - Q x x)) := by
  simp_rw [mul_assoc, mul_comm (Ks s x _)]
  refine integrable_Ks_x (one_lt_realD X) |>.bdd_mul (c := 1) ?_ (ae_of_all _ fun y ↦ ?_)
  · exact hf.mul ((measurable_ofReal.comp (map_continuous (Q x)).measurable |>.sub
      measurable_const).const_mul I).cexp |>.aestronglyMeasurable
  · rw [norm_mul, ← one_mul 1]
    gcongr
    · exact le_trans (h2f y) (F.indicator_le_self' (by simp) y)
    · rw_mod_cast [mul_comm, norm_exp_ofReal_mul_I]


-- @@ L28-28 verbatim
section


-- @@ L30-30 expanded
variable [TileStructure Q (defaultD a) (defaultκ a) (defaultS X) (cancelPt X)]


-- @@ L32-33 verbatim
@[reducible] -- Used to simplify notation in the proof of `tile_sum_operator`
private def 𝔓X_s (s : ℤ) := (@Finset.univ (𝔓 X) _).filter (fun p ↦ 𝔰 p = s)


-- @@ L35-35 verbatim
private lemma 𝔰_eq {s : ℤ} {p : 𝔓 X} (hp : p ∈ 𝔓X_s s) : 𝔰 p = s := (Finset.mem_filter.mp hp).2


-- @@ L37-44 expanded
open scoped Classical in
private lemma 𝔓_biUnion :
    @Finset.univ (𝔓 X) _ = (Icc (-defaultS X : ℤ) (defaultS X)).toFinset.biUnion 𝔓X_s :=
  by
  ext p
  refine ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ p⟩
  rw [Finset.mem_biUnion]
  refine ⟨𝔰 p, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  rw [toFinset_Icc, Finset.mem_Icc]
  exact range_s_subset ⟨𝓘 p, rfl⟩


-- @@ L46-54 expanded
private lemma sum_eq_zero_of_notMem_Icc {f : X → ℂ} {x : X} (s : ℤ)
    (hs :
      s ∈ (Icc (-defaultS X : ℤ) (defaultS X)).toFinset.filter (fun t ↦ t ∉ Icc (σ₁ x) (σ₂ x))) :
    ∑ i ∈ Finset.univ.filter (fun p ↦ 𝔰 p = s), carlesonOn i f x = 0 :=
  by
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  rw [Finset.mem_filter_univ] at hp
  simp only [mem_Icc, not_and, not_le, toFinset_Icc, Finset.mem_filter, Finset.mem_Icc] at hs
  rw [carlesonOn, Set.indicator_of_notMem]
  simp only [E, Grid.mem_def, mem_Icc, sep_and, mem_inter_iff, mem_ofPred_eq, not_and, not_le]
  exact fun _ ⟨_, h⟩ _ ↦ hp ▸ hs.2 (hp ▸ h)


-- @@ L56-67 expanded
lemma exists_Grid {x : X} (hx : x ∈ G) {s : ℤ} (hs : s ∈ (Icc (σ₁ x) (σ₂ x)).toFinset) :
    ∃ I : Grid X, GridStructure.s I = s ∧ x ∈ I :=
  by
  have DS : (defaultD a : ℝ) ^ defaultS X = (defaultD a : ℝ) ^ (defaultS X : ℤ) := rfl
  have : x ∈ ball (cancelPt X) (defaultD a ^ defaultS X / 4) := G_subset hx
  rw [← c_topCube (X := X), DS, ← s_topCube (X := X)] at this
  have x_mem_topCube := ball_subset_Grid this
  by_cases hS : s = defaultS X
  · exact ⟨topCube, by rw [s_topCube, hS], x_mem_topCube⟩
  have s_mem : s ∈ Ico (-defaultS X : ℤ) (GridStructure.s (X := X) topCube) :=
    have : s ∈ Icc (-defaultS X : ℤ) (defaultS X) := Icc_σ_subset_Icc_S (mem_toFinset.1 hs)
    ⟨this.1, s_topCube (X := X) ▸ lt_of_le_of_ne this.2 hS⟩
  simpa only [mem_iUnion, exists_prop] using! Grid_subset_biUnion s s_mem x_mem_topCube


-- @@ L69-98 expanded
/-- Lemma 4.0.3 -/
theorem tile_sum_operator {G' : Set X} {f : X → ℂ} {x : X} (hx : x ∈ G \ G') :
    ∑ (p : 𝔓 X), carlesonOn p f x =
      ∑ s ∈ Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * (Q x y - Q x x)) :=
  by
  classical
  rw [𝔓_biUnion, Finset.sum_biUnion]; swap
  · exact fun s _ s' _ hss' A hAs hAs' p pA ↦ False.elim <| hss' (𝔰_eq (hAs pA) ▸ 𝔰_eq (hAs' pA))
  rw [←
    (Icc (-defaultS X : ℤ) (defaultS X)).toFinset.sum_filter_add_sum_filter_not
      (fun s ↦ s ∈ Icc (σ₁ x) (σ₂ x))]
  rw [Finset.sum_eq_zero sum_eq_zero_of_notMem_Icc, add_zero]
  refine Finset.sum_congr (Finset.ext fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩) (fun s hs ↦ ?_)
  · rw [Finset.mem_filter, ← mem_toFinset] at hs
    exact hs.2
  · rw [mem_toFinset] at hs
    rw [toFinset_Icc, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.2 (Icc_σ_subset_Icc_S hs), hs⟩
  · rcases exists_Grid hx.1 hs with ⟨I, Is, xI⟩
    obtain ⟨p, 𝓘pI, Qp⟩ : ∃ (p : 𝔓 X), 𝓘 p = I ∧ Q x ∈ Ω p := by simpa using! biUnion_Ω ⟨x, rfl⟩
    have p𝔓Xs : p ∈ 𝔓X_s s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [𝔰, 𝓘pI]; exact Is⟩
    have : ∀ p' ∈ 𝔓X_s s, p' ≠ p → carlesonOn p' f x = 0 :=
      by
      intro p' p'𝔓Xs p'p
      apply indicator_of_notMem
      simp only [E, mem_ofPred_eq, not_and]
      refine fun x_in_𝓘p' Qp' ↦ False.elim ?_
      have s_eq := 𝔰_eq p𝔓Xs ▸ 𝔰_eq p'𝔓Xs
      have : ¬Disjoint (𝓘 p' : Set X) (𝓘 p : Set X) := not_disjoint_iff.2 ⟨x, x_in_𝓘p', 𝓘pI ▸ xI⟩
      exact disjoint_left.1 (disjoint_Ω p'p <| Or.resolve_right (eq_or_disjoint s_eq) this) Qp' Qp
    rw [Finset.sum_eq_single_of_mem p p𝔓Xs this]
    have xEp : x ∈ E p :=
      ⟨𝓘pI ▸ xI, Qp, by simpa only [toFinset_Icc, Finset.mem_Icc, 𝔰_eq p𝔓Xs] using! hs⟩
    simp_rw [carlesonOn_def', indicator_of_mem xEp, 𝔰_eq p𝔓Xs]


-- @@ L100-100 verbatim
end


-- @@ L102-104 verbatim
/-- The constant used in Proposition 2.0.1.
Has value `2 ^ (442 * a ^ 3) / (q - 1) ^ 5` in the blueprint. -/
def C2_0_1 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := C2_0_2 a q


-- @@ L106-106 expanded
lemma C2_0_1_pos [TileStructure Q (defaultD a) (defaultκ a) (defaultS X) (cancelPt X)] :
    C2_0_1 a («nnq» X) > 0 :=
  C2_0_2_pos


-- @@ L108-124 expanded
variable (X) in
/-- Proposition 2.0.1 -/
theorem finitary_carleson :
    ∃ G',
      MeasurableSet G' ∧
        2 * volume G' ≤ volume G ∧
          ∀ f : X → ℂ,
            Measurable f →
              (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
                ∫⁻ x in G \ G', ‖∑ s ∈ Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * Q x y)‖ₑ ≤
                  C2_0_1 a («nnq» X) * (volume G) ^ (1 - q⁻¹) * (volume F) ^ q⁻¹ :=
  by
  have g : GridStructure X (defaultD a) (defaultκ a) (defaultS X) (cancelPt X) := grid_existence X
  have t : TileStructure Q (defaultD a) (defaultκ a) (defaultS X) (cancelPt X) := tile_existence X
  clear g
  rcases discrete_carleson X with ⟨G', hG', h2G', hfG'⟩
  refine ⟨G', hG', h2G', fun f meas_f h2f ↦ le_of_eq_of_le ?_ (hfG' f meas_f h2f)⟩
  refine setLIntegral_congr_fun (measurableSet_G.diff hG') fun x hx ↦ ?_
  simp_rw [carlesonSum, mem_univ, Finset.filter_true, tile_sum_operator hx, mul_sub, exp_sub,
    mul_div, div_eq_mul_inv, ← smul_eq_mul, integral_smul_const, ← Finset.sum_smul,
    _root_.enorm_smul]
  suffices ‖(cexp (I • ((Q x) x : ℂ)))⁻¹‖ₑ = 1 by rw [this, mul_one]
  simp [mul_comm I, enorm_eq_nnnorm]

