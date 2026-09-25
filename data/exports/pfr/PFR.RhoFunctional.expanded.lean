module

public import PFR.ForMathlib.ThreeVariables
public import PFR.Kullback
public import PFR.Main


-- @@ L7-11 verbatim
/-!
# The rho functional

Definition of the rho functional and basic facts
-/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
open MeasureTheory ProbabilityTheory Real Set Function Measure Filter

-- @@ L16-16 verbatim
open scoped Pointwise ENNReal Topology

-- @@ L17-17 verbatim
universe uG


-- @@ L19-19 verbatim
section


-- @@ L21-23 verbatim
variable {G : Type uG} [AddCommGroup G] [Finite G] [hGm : MeasurableSpace G]
  [DiscreteMeasurableSpace G] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X Y Z : Ω → G} {A : Finset G}


-- @@ L25-35 expanded
/-- The set of possible values of $D_{KL}(X \Vert U_A + T)$, where $U_A$ is uniform on $A$ and
$T$ ranges over $G$-valued random variables independent of $U_A$. We also require an absolute
continuity condition so that the KL divergence makes sense in `ℝ`.

To avoid universe issues, we express this using measures on `G`, but the equivalence with the
above point of view follows from `rhoMinus_le` below. -/
noncomputable def rhoMinusSet (X : Ω → G) (A : Finset G) (μ : Measure Ω) : Set ℝ :=
  {x : ℝ |
    ∃ (μ' : Measure G),
      IsProbabilityMeasure μ' ∧
        (∀ y, (μ'.prod (uniformOn A)).map (Prod.fst + Prod.snd) { y } = 0 → μ.map X { y } = 0) ∧
          x = KLDiv X (Prod.fst + Prod.snd) μ (μ'.prod (uniformOn A))}


-- @@ L37-54 verbatim
lemma map_prod_uniformOn_ne_zero {y : G} (hA : A.Nonempty)
    {μ : Measure G} [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) :
    (μ.prod (uniformOn A)).map (Prod.fst + Prod.snd) {y} ≠ 0 := by
  cases nonempty_fintype G
  intro h
  obtain ⟨a, ha⟩ : ∃ x, x ∈ A := by exact hA
  let ν := uniformOn (A : Set G)
  have : IsProbabilityMeasure ν :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  have h_indep : IndepFun Prod.fst Prod.snd (μ.prod ν) := ProbabilityTheory.indepFun_fst_snd
  rw [h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp)] at h
  specialize h a (Finset.mem_univ a)
  have : (Measure.map Prod.snd (μ.prod ν)) {a} ≠ 0 := by
    simp [Measure.map_snd_prod, ν, uniformOn_apply_singleton_of_mem (by exact ha) A.finite_toSet]
  simp only [mul_eq_zero, this, false_or, Measure.map_fst_prod] at h
  simp only [measure_univ, one_smul] at h
  exact hμ (y - a) h


-- @@ L56-65 expanded
lemma nonempty_rhoMinusSet [IsZeroOrProbabilityMeasure μ] (hA : A.Nonempty) :
    Set.Nonempty (rhoMinusSet X A μ) :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with hμ | hμ
  ·
    refine
      ⟨0,
        ⟨uniformOn (A : Set G), isProbabilityMeasure_uniformOn A.finite_toSet hA, by simp [hμ], by
          simp [hμ, KLDiv]⟩⟩
  set μ' := uniformOn (univ : Set G) with hμ'
  have : IsProbabilityMeasure μ' := isProbabilityMeasure_uniformOn finite_univ univ_nonempty
  refine ⟨_, ⟨μ', this, fun y hy ↦ (map_prod_uniformOn_ne_zero hA ?_ hy).elim, rfl⟩⟩
  intro x
  simp [hμ', uniformOn_apply_singleton_of_mem (mem_univ _) finite_univ]


-- @@ L67-70 verbatim
lemma nonneg_of_mem_rhoMinusSet [IsZeroOrProbabilityMeasure μ] {x : ℝ}
    (hx : x ∈ rhoMinusSet X A μ) : 0 ≤ x := by
  rcases hx with ⟨μ, hμ, habs, rfl⟩
  exact KLDiv_nonneg habs


-- @@ L72-73 expanded
lemma bddBelow_rhoMinusSet [IsZeroOrProbabilityMeasure μ] : BddBelow (rhoMinusSet X A μ) :=
  ⟨0, fun _ hx ↦ nonneg_of_mem_rhoMinusSet hx⟩


-- @@ L75-82 expanded
lemma rhoMinusSet_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → G} (h : IdentDistrib X X' μ μ') : rhoMinusSet X A μ = rhoMinusSet X' A μ' :=
  by
  have I (μ'' : Measure G) :
    KLDiv X (Prod.fst + Prod.snd) μ (μ''.prod (uniformOn (A : Set G))) =
      KLDiv X' (Prod.fst + Prod.snd) μ' (μ''.prod (uniformOn (A : Set G))) :=
    by
    apply ProbabilityTheory.IdentDistrib.KLDiv_eq _ _ h
    exact .refl (by fun_prop)
  simp only [rhoMinusSet, h.map_eq, I]


-- @@ L84-88 verbatim
/-- For any $G$-valued random variable $X$, we define $\rho^-(X)$ to be the infimum of
$D_{KL}(X \Vert U_A + T)$, where $U_A$ is uniform on $A$ and $T$ ranges over $G$-valued random
variables independent of $U_A$. -/
noncomputable def rhoMinus (X : Ω → G) (A : Finset G) (μ : Measure Ω) : ℝ :=
  sInf (rhoMinusSet X A μ)


-- @@ L90-90 verbatim
@[inherit_doc rhoMinus] notation3:max "ρ⁻[" X " ; " μ " # " A "]" => rhoMinus X A μ


-- @@ L92-92 verbatim
@[inherit_doc rhoMinus] notation3:max "ρ⁻[" X " # " A "]" => rhoMinus X A volume


-- @@ L94-96 expanded
lemma rhoMinus_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {X' : Ω' → G} {μ' : Measure Ω'}
    (h : IdentDistrib X X' μ μ') : rhoMinus X A μ = rhoMinus X' A μ' := by
  simp [rhoMinus, rhoMinusSet_eq_of_identDistrib h]


-- @@ L98-103 expanded
lemma rhoMinus_le_def [IsZeroOrProbabilityMeasure μ] {μ' : Measure G} [IsProbabilityMeasure μ']
    (habs : ∀ y, (μ'.prod (uniformOn A)).map (Prod.fst + Prod.snd) { y } = 0 → μ.map X { y } = 0) :
    rhoMinus X A μ ≤ KLDiv X (Prod.fst + Prod.snd) μ (μ'.prod (uniformOn A)) :=
  by
  apply csInf_le bddBelow_rhoMinusSet
  exact ⟨μ', by infer_instance, habs, rfl⟩


-- @@ L105-127 expanded
lemma rhoMinus_le [IsZeroOrProbabilityMeasure μ] (hA : A.Nonempty) {Ω' : Type*} [MeasurableSpace Ω']
    {T : Ω' → G} {U : Ω' → G} {μ' : Measure Ω'} [IsProbabilityMeasure μ'] (hunif : IsUniform A U μ')
    (hT : Measurable T) (hU : Measurable U) (h_indep : IndepFun T U μ')
    (habs : ∀ y, (μ'.map (T + U)) { y } = 0 → μ.map X { y } = 0) :
    rhoMinus X A μ ≤ KLDiv X (T + U) μ μ' :=
  by
  cases nonempty_fintype G
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  have E : μ'.map U = uniformOn (A : Set G) := hunif.map_eq_uniformOn hU A.finite_toSet hA
  have M :
    (Measure.map (Prod.fst + Prod.snd) ((μ'.map T).prod (uniformOn ↑A))) =
      (Measure.map (T + U) μ') :=
    by
    ext s _
    rw [h_indep.map_add_eq_sum hT hU]
    have : IndepFun Prod.fst Prod.snd ((μ'.map T).prod (uniformOn (A : Set G))) :=
      ProbabilityTheory.indepFun_fst_snd
    rw [this.map_add_eq_sum measurable_fst measurable_snd, Measure.map_fst_prod,
      Measure.map_snd_prod]
    simp [E]
  apply csInf_le bddBelow_rhoMinusSet
  simp only [rhoMinusSet, Set.mem_ofPred_eq]
  exact ⟨μ'.map T, inferInstance, by rwa [M], by simp [KLDiv, M]⟩


-- @@ L129-132 expanded
/-- We have $\rho^-(X) \geq 0$. -/
lemma rhoMinus_nonneg [IsZeroOrProbabilityMeasure μ] {X : Ω → G} {A : Finset G} :
    0 ≤ rhoMinus X A μ :=
  Real.sInf_nonneg fun _ ↦ nonneg_of_mem_rhoMinusSet


-- @@ L134-138 expanded
lemma rhoMinus_zero_measure (hP : μ = 0) {X : Ω → G} {A : Finset G} : rhoMinus X A μ = 0 :=
  by
  have : ∃ (μ' : Measure G), IsProbabilityMeasure μ' :=
    ⟨uniformOn Set.univ, isProbabilityMeasure_uniformOn finite_univ univ_nonempty⟩
  simp [rhoMinus, rhoMinusSet, hP, this, KLDiv]


-- @@ L140-192 expanded
private lemma rhoMinus_continuous_aux1 (hA : A.Nonempty) {r : ℝ} (hr : rhoMinus X A μ < r)
    [IsProbabilityMeasure μ] [TopologicalSpace G] [DiscreteTopology G] :
    ∃ (μ' : Measure G),
      IsProbabilityMeasure μ' ∧
        (∀ y, 0 < μ' { y }) ∧ KLDiv X (Prod.fst + Prod.snd) μ (μ'.prod (uniformOn A)) < r :=
  by
  rcases (csInf_lt_iff bddBelow_rhoMinusSet (nonempty_rhoMinusSet hA)).1 hr with
    ⟨-, ⟨μ₀, hPμ₀, habs, rfl⟩, h₀⟩
  lift μ₀ to ProbabilityMeasure G using hPμ₀
  obtain ⟨u, -, u_mem, hu⟩ := exists_seq_strictAnti_tendsto' (x := (0 : ℝ≥0∞)) zero_lt_one
  let ν : ℕ → Measure G := fun n ↦ (1 - u n) • μ₀.toMeasure + u n • uniformOn univ
  have : IsProbabilityMeasure (uniformOn (univ : Set G)) :=
    isProbabilityMeasure_uniformOn finite_univ univ_nonempty
  have P n : IsProbabilityMeasure (ν n) :=
    by
    simp only [isProbabilityMeasure_iff, coe_add, coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one, ν]
    rw [ENNReal.sub_add_eq_add_sub, ENNReal.add_sub_cancel_right]
    · exact ne_of_lt ((u_mem n).2.trans ENNReal.one_lt_top)
    · exact (u_mem n).2.le
    · exact ne_of_lt ((u_mem n).2.trans ENNReal.one_lt_top)
  let νP n : ProbabilityMeasure G := ⟨ν n, P n⟩
  have L : Tendsto νP atTop (𝓝 μ₀) :=
    by
    rw [ProbabilityMeasure.tendsto_iff_forall_apply_tendsto_ennreal]
    intro g
    simp only [ProbabilityMeasure.coe_mk, coe_add, coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, νP, ν]
    have : 𝓝 (μ₀.toMeasure { g }) = 𝓝 ((1 - 0) * μ₀.toMeasure { g } + 0 * (uniformOn univ { g })) :=
      by simp
    rw [this]
    apply Tendsto.add
    · apply ENNReal.Tendsto.mul_const _ (by simp)
      exact ENNReal.Tendsto.sub tendsto_const_nhds hu (by simp)
    · exact ENNReal.Tendsto.mul_const hu (by simp)
  let PA : ProbabilityMeasure G := ⟨uniformOn A, isProbabilityMeasure_uniformOn (A.finite_toSet) hA⟩
  have hPA : (PA : Measure G) = uniformOn ↑A := rfl
  have : Tendsto (fun n ↦ (νP n).prod PA) atTop (𝓝 (μ₀.prod PA)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (μ₀, PA)).comp (f := fun n ↦ (νP n, PA)) <|
      L.prodMk_nhds tendsto_const_nhds
  have C : Continuous (Prod.fst + Prod.snd : G × G → G) := by fun_prop
  have Z :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ this (f := Prod.fst + Prod.snd) C
  have M (x : G) (hx : ((μ₀.prod PA).map (Prod.fst + Prod.snd)) { x } = 0) : μ.map X { x } = 0 :=
    habs _ <| by simpa [hPA] using hx
  have T := tendsto_KLDiv_id_right (X := X) (μ := μ) (G := G) Z M
  have :
    KLDiv X id μ (Measure.map (Prod.fst + Prod.snd) (μ₀.toMeasure.prod (uniformOn ↑A))) =
      KLDiv X (Prod.fst + Prod.snd) μ (μ₀.toMeasure.prod (uniformOn ↑A)) :=
    by simp [KLDiv]
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod, this, hPA] at T
  rcases ((tendsto_order.1 T).2 _ h₀).exists with ⟨n, hn⟩
  refine ⟨ν n, P n, fun y ↦ ?_, ?_⟩
  · simp [(u_mem n).1, ν, uniformOn_apply_singleton_of_mem (mem_univ _) finite_univ]
  · have :
      KLDiv X id μ (Measure.map (Prod.fst + Prod.snd) ((ν n).prod (uniformOn ↑A))) =
        KLDiv X (Prod.fst + Prod.snd) μ ((ν n).prod (uniformOn ↑A)) :=
      by simp [KLDiv]
    simpa [νP, this] using hn


-- @@ L194-209 expanded
private lemma rhoMinus_continuous_aux2 (hA : A.Nonempty) {μ : ProbabilityMeasure G} {r : ℝ}
    (hr : rhoMinus id A μ < r) [TopologicalSpace G] [DiscreteTopology G] :
    ∀ᶠ (μ' : ProbabilityMeasure G) in 𝓝 μ, rhoMinus id A μ' < r :=
  by
  obtain ⟨ν, νP, ν_pos, hν⟩ :
    ∃ (ν : Measure G),
      IsProbabilityMeasure ν ∧
        (∀ y, 0 < ν { y }) ∧ KLDiv id (Prod.fst + Prod.snd) μ (ν.prod (uniformOn A)) < r :=
    by apply rhoMinus_continuous_aux1 hA hr
  have :
    Tendsto
      (fun (μ' : ProbabilityMeasure G) ↦ KLDiv id (Prod.fst + Prod.snd) μ' (ν.prod (uniformOn A)))
      (𝓝 μ) (𝓝 (KLDiv id (Prod.fst + Prod.snd) μ (ν.prod (uniformOn A)))) :=
    tendsto_KLDiv_id_left tendsto_id
  filter_upwards [(tendsto_order.1 this).2 _ hν] with μ' hμ'
  apply lt_of_le_of_lt _ hμ'
  apply rhoMinus_le_def
  intro y hy
  contrapose hy
  exact map_prod_uniformOn_ne_zero hA (fun x ↦ (ν_pos x).ne')


-- @@ L211-382 expanded
private lemma rhoMinus_continuous_aux3 (hA : A.Nonempty) {μ : ProbabilityMeasure G} {ε : ℝ}
    (hε : 0 < ε) [TopologicalSpace G] [DiscreteTopology G] :
    ∀ᶠ (μ' : ProbabilityMeasure G) in 𝓝 μ, rhoMinus id A μ < rhoMinus id A μ' + ε :=
  by
  cases nonempty_fintype G
  obtain ⟨c, c_pos, hc⟩ : ∃ c > 0, ∀ g, μ.toMeasure.real { g } ≠ 0 → c ≤ μ.toMeasure.real { g } :=
    by
    let B := {g | μ.toMeasure.real { g } ≠ 0}
    have : B.Finite := toFinite B
    have : B.Nonempty := by
      by_contra! H
      simp [-ProbabilityMeasure.measureReal_eq_coe_coeFn, ne_eq, -NNReal.coe_eq_zero,
        eq_empty_iff_forall_notMem, mem_ofPred_eq, Decidable.not_not, B] at H
      have : ∑ g, μ.toMeasure.real { g } = 1 := by
        simp [-ProbabilityMeasure.measureReal_eq_coe_coeFn]
      simp [H] at this
    have Bn : (B.toFinset.image (fun g ↦ μ.toMeasure.real { g })).Nonempty := by simpa using this
    let c := (B.toFinset.image (fun g ↦ μ.toMeasure.real { g })).min' Bn
    refine ⟨c, ?_, fun g hg ↦ ?_⟩
    · have : c ∈ B.toFinset.image (fun g ↦ ((μ : Measure G) { g }).toReal) := Finset.min'_mem _ _
      simp only [ne_eq, toFinset_ofPred, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, B] at this
      rcases this with ⟨g, hg, cg⟩
      rw [← cg]
      exact lt_of_le_of_ne (by simp) (Ne.symm hg)
    · apply Finset.min'_le
      simp only [Finset.mem_image, mem_toFinset]
      exact ⟨g, hg, rfl⟩
  let C := (rhoMinus id A μ + entropy id (μ : Measure G) + 3 * c / 2) / (c / 2)
  have C_nonneg : 0 ≤ C := by
    have : 0 ≤ rhoMinus id A μ := rhoMinus_nonneg
    have : 0 ≤ entropy id (μ : Measure G) := entropy_nonneg _ _
    positivity
  obtain ⟨δ, δpos, hδc, hδ⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < c / 2 ∧ δ * (2 + C * Fintype.card G) < ε :=
    by
    refine ⟨(min (c / 2) (ε / (2 + C * Fintype.card G))) / 2, ?_, ?_, ?_⟩
    · positivity
    · exact (half_lt_self (by positivity)).trans_le (min_le_left _ _)
    · rw [← lt_div_iff₀ (by positivity)]
      exact (half_lt_self (by positivity)).trans_le (min_le_right _ _)
  have E₁ :
    ∀ᶠ (μ' : ProbabilityMeasure G) in 𝓝 μ,
      |entropy id (μ' : Measure G) - entropy id (μ : Measure G)| < δ :=
    by
    have :
      Tendsto (fun (μ' : ProbabilityMeasure G) ↦ entropy id (μ' : Measure G)) (𝓝 μ)
        (𝓝 (entropy id (μ : Measure G))) :=
      continuous_entropy_restrict_probabilityMeasure.continuousAt
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 this)).2 _ δpos
  have E₂ :
    ∀ᶠ (μ' : ProbabilityMeasure G) in 𝓝 μ,
      ∀ g, |μ'.toMeasure.real { g } - μ.toMeasure.real { g }| < δ :=
    by
    rw [eventually_all]
    intro g
    have :
      Tendsto (fun (μ' : ProbabilityMeasure G) ↦ ((μ' : Measure G) { g }).toReal) (𝓝 μ)
        (𝓝 (((μ : Measure G) { g }).toReal)) :=
      by
      rw [ENNReal.tendsto_toReal_iff (by simp) (by simp)]
      exact (ProbabilityMeasure.tendsto_iff_forall_apply_tendsto_ennreal _ _).1 tendsto_id _
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 this)).2 _ δpos
  have M : rhoMinus id A μ < rhoMinus id A μ + δ := by linarith
  filter_upwards [rhoMinus_continuous_aux2 hA M, E₁, E₂] with μ' h' h₁ h₂
  have h₃ g (hg : μ.toMeasure.real { g } ≠ 0) : c / 2 ≤ μ'.toMeasure.real { g } :=
    by
    have : c ≤ μ.toMeasure.real { g } := hc _ hg
    linarith [neg_le_of_abs_le (h₂ g).le]
  have : rhoMinus id A μ' < rhoMinus id A μ' + δ := by linarith
  have : ∃ b ∈ rhoMinusSet id A μ', b < rhoMinus id A μ' + δ :=
    (csInf_lt_iff (bddBelow_rhoMinusSet (μ := μ') (X := id) (A := A))
          (nonempty_rhoMinusSet hA (X := id) (μ := μ'))).1
      this
  rcases this with ⟨-, ⟨ν, νP, h'_abs, rfl⟩, h⟩
  simp only [Measure.map_id] at h'_abs
  set m := Measure.map (Prod.fst + Prod.snd) (ν.prod (uniformOn A)) with hm
  have m_nonpos g : log (m { g }).toReal ≤ 0 :=
    by
    apply log_nonpos (by simp)
    have : m { g } ≤ 1 := prob_le_one
    simpa using ENNReal.toReal_mono (by simp) this
  have h_abs : ∀ g, m { g } = 0 → (μ : Measure G) { g } = 0 :=
    by
    intro y hy
    have Z := h'_abs y hy
    contrapose! Z
    intro hy
    have : μ.toMeasure.real { y } ≠ 0 := by simpa [measureReal_eq_zero_iff] using Z
    have T := h₃ _ this
    simp [hy, measureReal_def] at T
    linarith
  have I₀ :
    KLDiv id (Prod.fst + Prod.snd) μ' (ν.prod (uniformOn A)) =
      -entropy id (μ' : Measure G) - ∑ g, μ'.toMeasure.real { g } * log (m.real { g }) :=
    by
    rw [KLDiv_eq_sum, entropy_eq_sum, tsum_fintype, ← Finset.sum_neg_distrib, ←
      Finset.sum_sub_distrib]
    congr with g
    simp only [Measure.map_id, negMulLog, neg_mul]
    rcases eq_or_ne (μ'.toMeasure.real { g }) 0 with h | h
    · simp [h]
    rw [log_div, hm]
    · ring
    · exact h
    · contrapose! h
      simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h ⊢
      apply h'_abs _ (by simpa [ENNReal.toReal_eq_zero_iff] using h)
  have M g (hg : μ.toMeasure.real { g } ≠ 0) : |log (m.real { g })| ≤ C :=
    by
    rw [le_div_iff₀' (by positivity)]
    calc
      (c / 2) * |log (m.real { g })|
      _ ≤ μ'.toMeasure.real { g } * |log (m.real { g })| :=
        by
        gcongr
        apply h₃ _ (by simpa [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] using hg)
      _ ≤ ∑ g, ((μ' : Measure G) { g }).toReal * |log ((m { g }).toReal)| := by
        apply Finset.single_le_sum (a := g) (fun i hi ↦ by positivity) (Finset.mem_univ g)
      _ = ∑ g, ((μ' : Measure G) { g }).toReal * (-log ((m { g }).toReal)) :=
        by
        congr with g
        rw [abs_of_nonpos (m_nonpos g)]
      _ = KLDiv id (Prod.fst + Prod.snd) μ' (ν.prod (uniformOn A)) + entropy id (μ' : Measure G) :=
        by
        simp_rw [I₀, mul_neg, Finset.sum_neg_distrib]
        abel
      _ ≤ (rhoMinus id A μ' + δ) + entropy id (μ' : Measure G) := by linarith
      _ ≤ ((rhoMinus id A μ + δ) + δ) + (entropy id (μ : Measure G) + δ) :=
        by
        gcongr
        linarith [le_of_abs_le h₁.le]
      _ ≤ rhoMinus id A μ + entropy id (μ : Measure G) + 3 * c / 2 := by linarith
  calc
    rhoMinus id A μ
    _ ≤ KLDiv id (Prod.fst + Prod.snd) μ (ν.prod (uniformOn A)) :=
      (rhoMinus_le_def (by simpa using h_abs))
    _ = -entropy id (μ : Measure G) - ∑ g, μ.toMeasure.real { g } * log (m.real { g }) :=
      by
      rw [KLDiv_eq_sum, entropy_eq_sum, tsum_fintype, ← Finset.sum_neg_distrib, ←
        Finset.sum_sub_distrib]
      congr with g
      simp only [Measure.map_id, negMulLog, neg_mul]
      rcases eq_or_ne (μ.toMeasure.real { g }) 0 with h | h
      · simp [h]
      rw [log_div, hm]
      · ring
      · exact h
      · contrapose! h
        simp only [measureReal_def, ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] at h ⊢
        exact h_abs _ h
    _ ≤
        -entropy id (μ : Measure G) -
          ∑ g ∈ {g | μ.toMeasure.real { g } ≠ 0}, μ.toMeasure.real { g } * log (m.real { g }) :=
      by
      gcongr
      · intro g hg h'g
        simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Decidable.not_not] at h'g
        simp [h'g]
      · exact Finset.filter_subset _ _
    _ ≤
        -entropy id (μ : Measure G) -
          ∑ g ∈ {g | μ.toMeasure.real { g } ≠ 0},
            (μ'.toMeasure.real { g } + δ) * log (m.real { g }) :=
      by
      apply sub_le_sub le_rfl
      apply Finset.sum_le_sum (fun g hg ↦ ?_)
      apply mul_le_mul_of_nonpos_right _ (m_nonpos g)
      linarith [neg_le_of_abs_le (h₂ g).le]
    _ ≤
        -entropy id (μ : Measure G) -
          (∑ g ∈ {g | μ.toMeasure.real { g } ≠ 0}, μ'.toMeasure.real { g } * log (m.real { g }) +
            ∑ g ∈ {g | μ.toMeasure.real { g } ≠ 0}, δ * (-C)) :=
      by
      rw [← Finset.sum_add_distrib]
      gcongr with g hg
      rw [add_mul]
      gcongr
      rw [neg_le]
      exact (neg_le_abs _).trans (M g (by simpa using hg))
    _ ≤
        (-entropy id (μ' : Measure G) + δ) +
          (-∑ g, μ'.toMeasure.real { g } * log (m.real { g }) + Fintype.card G * (δ * C)) :=
      by
      simp only [mul_neg, Finset.sum_const, nsmul_eq_mul, sub_eq_add_neg, neg_add,
        ← Finset.sum_neg_distrib, neg_neg]
      gcongr
      · linarith [le_of_abs_le h₁.le]
      · intro g hg h'g
        rw [← neg_mul, neg_mul_comm]
        have T := neg_nonneg.2 (m_nonpos g)
        positivity
      · exact Finset.filter_subset _ _
      · exact Finset.card_le_univ _
    _ = KLDiv id (Prod.fst + Prod.snd) μ' (ν.prod (uniformOn A)) + δ * (1 + C * Fintype.card G) :=
      by
      rw [I₀]
      ring
    _ ≤ (rhoMinus id A μ' + δ) + δ * (1 + C * Fintype.card G) := by linarith
    _ = rhoMinus id A μ' + δ * (2 + C * Fintype.card G) := by ring
    _ < rhoMinus id A μ' + ε := by linarith


-- @@ L384-391 expanded
lemma rhoMinus_continuous [TopologicalSpace G] [DiscreteTopology G] (hA : A.Nonempty) :
    Continuous (fun (μ : ProbabilityMeasure G) ↦ rhoMinus id A μ) :=
  by
  apply continuous_iff_continuousAt.2 (fun μ ↦ ?_)
  refine tendsto_order.2 ⟨fun r hr ↦ ?_, fun r hr ↦ rhoMinus_continuous_aux2 hA hr⟩
  dsimp at hr
  have : 0 < rhoMinus id A μ - r := by linarith
  filter_upwards [rhoMinus_continuous_aux3 hA this (μ := μ)] with μ' hμ'
  linarith


-- @@ L393-396 expanded
/-- For any $G$-valued random variable $X$, we define
$\rho^+(X) := \rho^-(X) + \bbH(X) - \bbH(U_A)$. -/
noncomputable def rhoPlus (X : Ω → G) (A : Finset G) (μ : Measure Ω) : ℝ :=
  rhoMinus X A μ + entropy X μ - log (Nat.card A)


-- @@ L398-398 verbatim
@[inherit_doc rhoPlus] notation3:max "ρ⁺[" X " ; " μ " # " A "]" => rhoPlus X A μ


-- @@ L400-400 verbatim
@[inherit_doc rhoPlus] notation3:max "ρ⁺[" X " # " A "]" => rhoPlus X A volume


-- @@ L402-408 expanded
lemma rhoPlus_continuous [TopologicalSpace G] [DiscreteTopology G] (hA : A.Nonempty) :
    Continuous (fun (μ : ProbabilityMeasure G) ↦ rhoPlus id A μ) :=
  by
  apply Continuous.add
  · apply Continuous.add
    · apply rhoMinus_continuous hA
    · apply continuous_entropy_restrict_probabilityMeasure
  · exact continuous_const


-- @@ L410-412 expanded
lemma rhoPlus_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {X' : Ω' → G} {μ' : Measure Ω'}
    (h : IdentDistrib X X' μ μ') : rhoPlus X A μ = rhoPlus X' A μ' := by
  simp [rhoPlus, rhoMinus_eq_of_identDistrib h, h.entropy_congr]


-- @@ L414-420 expanded
omit [MeasurableSpace G] [DiscreteMeasurableSpace G] in
lemma bddAbove_card_inter_add {A H : Set G} : BddAbove {Nat.card (A ∩ (t +ᵥ H) : Set G) | t : G} :=
  by
  refine ⟨Nat.card A, fun k hk ↦ ?_⟩
  simp only [mem_ofPred_eq] at hk
  rcases hk with ⟨t, rfl⟩
  exact Nat.card_mono (toFinite _) inter_subset_left


-- @@ L422-431 verbatim
omit [MeasurableSpace G] [DiscreteMeasurableSpace G] in
lemma exists_mem_card_inter_add (H : AddSubgroup G) {A : Set G} (hA : A.Nonempty) :
    ∃ k > 0, k ∈ {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} := by
  rcases hA with ⟨t, ht⟩
  have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) := by
    apply Nonempty.to_subtype
    refine ⟨t, ht, ?_⟩
    exact mem_vadd_set.2 ⟨0, zero_mem H, by simp⟩
  refine ⟨Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G), Nat.card_pos, ?_⟩
  simp only [mem_ofPred_eq, exists_apply_eq_apply]


-- @@ L433-447 verbatim
omit [MeasurableSpace G] [DiscreteMeasurableSpace G] in
lemma exists_card_inter_add_eq_sSup (H : AddSubgroup G) {A : Set G} (hA : A.Nonempty) :
    ∃ t : G, (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)
        = sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G})
      ∧ 0 < Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) := by
  set k := sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G}
  rcases exists_mem_card_inter_add H hA with ⟨n, n_pos, hn⟩
  have : k ∈ {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} :=
    Nat.sSup_mem ⟨n, hn⟩ bddAbove_card_inter_add
  rcases this with ⟨t, ht⟩
  have : 0 < Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) := by
    apply lt_of_lt_of_le n_pos
    rw [ht]
    exact le_csSup bddAbove_card_inter_add hn
  exact ⟨t, ht, this⟩


-- @@ L449-540 expanded
private lemma le_rhoMinus_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G} {U : Ω → G}
    (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    log (Nat.card A) - log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) ≤
      rhoMinus U A μ :=
  by
  cases nonempty_fintype G
  apply le_csInf (nonempty_rhoMinusSet hA)
  rintro - ⟨μ', hμ', habs, rfl⟩
  let T : G × G → G := Prod.fst
  have hT : Measurable T := measurable_fst
  let UA : G × G → G := Prod.snd
  have hUA : Measurable UA := measurable_snd
  let : MeasureSpace (G × G) := ⟨μ'.prod (uniformOn (A : Set G))⟩
  have hprod : (ℙ : Measure (G × G)) = μ'.prod (uniformOn (A : Set G)) := rfl
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  have : IsProbabilityMeasure (Measure.map T ℙ) := by rw [hprod, Measure.map_fst_prod]; simp [hμ']
  have h_indep : IndepFun T UA := ProbabilityTheory.indepFun_fst_snd
  have hUA_unif : IsUniform A UA :=
    by
    have : IsUniform A id (uniformOn (A : Set G)) := isUniform_uniformOn
    apply IsUniform.of_identDistrib this ?_ A.measurableSet
    exact measurePreserving_snd.identDistrib aemeasurable_id
  have : IsProbabilityMeasure (ℙ : Measure (G × G)) := by rw [hprod]; infer_instance
  let H' : Finset G := Set.Finite.toFinset (toFinite H)
  have hunif' : IsUniform H' U μ := by convert hunif; simp [H']
  have I₁ :
    KLDiv U (T + UA) μ ℙ =
      ∑ h ∈ H',
        1 / (H : Set G).ncard * log ((1 / (H : Set G).ncard) / (volume.map (T + UA)).real { h }) :=
    by
    rw [KLDiv_eq_sum, ← Finset.sum_subset (Finset.subset_univ H')]; swap
    · intro x _ hH
      rw [map_measureReal_apply hU (measurableSet_singleton x), hunif.measureReal_preimage_of_nmem]
      · simp
      · simpa [H'] using hH
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    rw [hunif'.measureReal_preimage_of_mem' hU hi]
    congr <;> simp [H', ← Set.ncard_eq_toFinset_card]
  have I₂ :
    (∑ h ∈ H', 1 / (H : Set G).ncard : ℝ) *
        log ((∑ h ∈ H', 1 / (H : Set G).ncard : ℝ) / (∑ h ∈ H', (volume.map (T + UA)).real { h })) ≤
      KLDiv U (T + UA) μ ℙ :=
    by
    rw [I₁]
    apply Real.sum_mul_log_div_leq (by simp) (by simp) (fun i hi h'i ↦ ?_)
    have : (μ.map U).real { i } = 0 :=
      by
      simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h'i ⊢
      simp [habs i h'i]
    simp [hunif'.measureReal_preimage_of_mem' hU hi, (ZeroMemClass.coe_nonempty H).ne_empty,
      H'] at this
  have : (∑ h ∈ H', 1 / (H : Set G).ncard : ℝ) = 1 :=
    by
    simp only [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_one]
    rw [div_eq_one_iff_eq]
    · simp [H', ← Set.ncard_eq_toFinset_card]
    · simp [ne_of_gt, Set.ncard_eq_zero (Set.toFinite _)]
  simp only [this, one_mul] at I₂
  simp only [sum_measureReal_singleton, one_div, log_inv] at I₂
  apply le_trans _ I₂
  have I₃ :
    ((Measure.map (T + UA) ℙ).real ↑H') ≤
      1 * ((sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G}) / Nat.card A) :=
    by
    have : ∑ x : G, ((Measure.map T ℙ).real { x }) = 1 := by simp
    rw [← this, add_comm, h_indep.symm.real_map_add_eq_sum hUA hT, Finset.sum_mul]
    simp_rw [map_measureReal_apply hUA (DiscreteMeasurableSpace.forall_measurableSet _),
      hUA_unif.measureReal_preimage hUA]
    simp only [probReal_univ, singleton_add, image_add_left, neg_neg, one_mul,
      Nat.card_eq_fintype_card, Fintype.card_coe, ge_iff_le, H']
    apply Finset.sum_le_sum (fun i _ ↦ ?_)
    gcongr
    apply le_csSup bddAbove_card_inter_add
    rw [inter_comm]
    refine ⟨-i, ?_⟩
    congr
    ext j
    simp [mem_vadd_set_iff_neg_vadd_mem]
  rw [one_mul] at I₃
  have :
    -log ((sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G}) / Nat.card A) ≤
      -log ((Measure.map (T + UA) ℙ).real ↑H') :=
    by
    apply neg_le_neg
    apply log_le_log _ I₃
    apply lt_of_le_of_ne (by simp) (fun h ↦ ?_)
    rw [Eq.comm] at h
    simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h
    have : Measure.map (T + UA) ℙ ({(0 : G)} : Set G) = 0 := measure_mono_null (by simp [H']) h
    have Z := habs _ this
    rw [Measure.map_apply hU (measurableSet_singleton 0),
      hunif'.measure_preimage_of_mem hU (by simp [H'])] at Z
    simp at Z
  convert! this using 1
  rw [log_div]
  · abel
  · norm_cast
    rcases exists_mem_card_inter_add H hA with ⟨k, k_pos, hk⟩
    exact (lt_of_lt_of_le k_pos (le_csSup bddAbove_card_inter_add hk)).ne'
  · norm_cast
    apply ne_of_gt
    have : Nonempty { x // x ∈ A } := hA.to_subtype
    exact Nat.card_pos


-- @@ L542-620 expanded
private lemma rhoMinus_le_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G} (t : G)
    {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty)
    (h'A : (A ∩ (t +ᵥ (H : Set G)) : Set G).Nonempty) (hU : Measurable U) :
    rhoMinus U A μ ≤ log (Nat.card A) - log (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)) :=
  by
  cases nonempty_fintype G
  classical
  have mapU : .map U μ = uniformOn (H : Set G) :=
    hunif.map_eq_uniformOn hU (H : Set G).toFinite <| ZeroMemClass.coe_nonempty _
  obtain ⟨a, ha, h'a⟩ := by exact h'A
  rcases mem_vadd_set.1 h'a with ⟨v, vH, rfl⟩
  simp only [vadd_eq_add, Finset.mem_coe] at ha
  have P z : (fun x ↦ x - t) ⁻¹' { z } = {z + t} := by ext w; simp [sub_eq_iff_eq_add]
  set μ' := μ.map ((· - t) ∘ U) with hμ'
  have μ'_sing z : μ' { z } = uniformOn (H : Set G) {z + t} := by
    rw [hμ', ← Measure.map_map (by fun_prop) hU,
      Measure.map_apply (by fun_prop) (measurableSet_singleton _), mapU, P]
  have μ'_sing_real z : μ'.real { z } = (uniformOn (H : Set G)).real {z + t} :=
    by
    rw [measureReal_def, μ'_sing]
    rfl
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  have h_indep : IndepFun Prod.fst Prod.snd (μ'.prod (uniformOn (A : Set G))) := indepFun_fst_snd
  apply csInf_le bddBelow_rhoMinusSet
  simp only [rhoMinusSet, Nat.card_eq_fintype_card, Fintype.card_coe, mem_ofPred_eq]
  refine ⟨μ', inferInstance, fun y h ↦ ?_, ?_⟩
  · rw [mapU]
    apply uniformOn_apply_singleton_of_not_mem (fun yH ↦ ?_)
    rw [h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd,
      Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp), Measure.map_snd_prod,
      Measure.map_fst_prod] at h
    specialize h (t + v)
    simp only [Finset.mem_univ, measure_univ, one_smul,
      uniformOn_apply_singleton_of_mem (by exact ha) A.finite_toSet, Finset.coe_sort_coe,
      Nat.card_eq_fintype_card, Fintype.card_coe, one_div, μ'_sing, mul_eq_zero,
      ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, false_or, true_implies] at h
    rw [uniformOn_apply_singleton_of_mem _ (toFinite (H : Set G))] at h
    · simp at h
    · convert! (H.sub_mem yH vH) using 1
      abel
  let H' : Finset G := Set.toFinset H
  have hunif' : IsUniform H' U μ := by convert hunif; ext; simp [H']
  rw [KLDiv_eq_sum, ← Finset.sum_subset (Finset.subset_univ H')]; swap
  · intro x _ hH
    rw [map_measureReal_apply hU (measurableSet_singleton x), hunif.measureReal_preimage_of_nmem]
    · simp
    · simpa [H'] using hH
  have :
    ∑ x ∈ H',
        (μ.map U).real { x } *
          log
            ((μ.map U).real { x } /
              ((μ'.prod (uniformOn ↑A)).map (Prod.fst + Prod.snd)).real { x }) =
      ∑ x ∈ H',
        (1 / (H : Set G).ncard) *
          log
            ((1 / (H : Set G).ncard) /
              (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) / (Nat.card A * (H : Set G).ncard))) :=
    by
    have (x) (hx : x ∈ H') : (μ.map U).real { x } = 1 / (H : Set G).ncard :=
      by
      rw [map_measureReal_apply hU (measurableSet_singleton _),
        hunif'.measureReal_preimage_of_mem hU hx]
      simp [H', ← Nat.card_coe_set_eq]
    congr! with x hx
    · exact this _ hx
    · exact this _ hx
    replace hx : x ∈ H := by simpa [H'] using hx
    have (y : G) : x - y + t ∈ H ↔ y ∈ t +ᵥ (H : Set G).toFinset := by
      simpa [sub_eq_add_neg, add_assoc, H.add_mem_cancel_left hx, ← Finset.neg_vadd_mem_iff] using
        H.neg_mem_iff (x := -t + y)
    rw [h_indep.real_map_add_singleton_eq_sum measurable_fst measurable_snd]
    simp [μ'_sing_real, toFinite, uniformOn_real_singleton, ← ite_and, div_eq_mul_inv, -mul_inv_rev,
      mul_inv, this, ← Finset.mem_inter, Finset.filter_mem_eq_inter]
  have C : H'.card = (H : Set G).ncard := by simp [H', ← Nat.card_coe_set_eq]
  simp only [this, one_div, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.sum_const, C,
    nsmul_eq_mul, ← mul_assoc]
  rw [mul_inv_cancel₀, one_mul]; swap
  · norm_cast
    exact Nat.card_pos.ne'
  have C₁ : Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) ≠ 0 :=
    by
    have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) := h'A.to_subtype
    exact Nat.card_pos.ne'
  have C₃ : (H : Set G).ncard ≠ 0 := Nat.card_pos.ne'
  rw [← log_div (by positivity) (by simpa using C₁)]
  congr 1
  field_simp


-- @@ L622-632 expanded
/-- If $H$ is a finite subgroup of $G$, then
$\rho^-(U_H) = \log |A| - \log \max_t |A \cap (H+t)|$. -/
lemma rhoMinus_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G} {U : Ω → G}
    (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    rhoMinus U A μ =
      log (Nat.card A) - log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) :=
  by
  apply le_antisymm _ (le_rhoMinus_of_subgroup hunif hA hU)
  rcases exists_card_inter_add_eq_sSup (A := A) H hA with ⟨t, ht, hpos⟩
  rw [← ht]
  have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) := (Nat.card_pos_iff.1 hpos).1
  exact rhoMinus_le_of_subgroup t hunif hA .of_subtype hU


-- @@ L634-642 expanded
/-- If $H$ is a finite subgroup of $G$, then
$\rho^+(U_H) = \log |H| - \log \max_t |A \cap (H+t)|$. -/
lemma rhoPlus_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G} {U : Ω → G}
    (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    rhoPlus U A μ =
      log ((H : Set G).ncard) -
        log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) :=
  by
  have : entropy U μ = log ((H : Set G).ncard) := hunif.entropy_eq' (toFinite _) hU
  rw [rhoPlus, rhoMinus_of_subgroup hunif hA hU, this]
  abel


-- @@ L644-646 expanded
/-- We define $\rho(X) := (\rho^+(X) + \rho^-(X))/2$. -/
noncomputable def rho (X : Ω → G) (A : Finset G) (μ : Measure Ω) : ℝ :=
  (rhoMinus X A μ + rhoPlus X A μ) / 2


-- @@ L648-648 verbatim
@[inherit_doc rho] notation3:max "ρ[" X " ; " μ " # " A "]" => rho X A μ


-- @@ L650-650 verbatim
@[inherit_doc rho] notation3:max "ρ[" X " # " A "]" => rho X A volume



-- @@ L653-655 expanded
lemma rho_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {X' : Ω' → G} {μ' : Measure Ω'}
    (h : IdentDistrib X X' μ μ') : rho X A μ = rho X' A μ' := by
  simp [rho, rhoMinus_eq_of_identDistrib h, rhoPlus_eq_of_identDistrib h]


-- @@ L657-668 expanded
/-- We have $\rho(U_A) = 0$. -/
lemma rho_of_uniform [IsProbabilityMeasure μ] {U : Ω → G} {A : Finset G} (hunif : IsUniform A U μ)
    (hU : Measurable U) (hA : A.Nonempty) : rho U A μ = 0 :=
  by
  have : entropy U μ = log (Nat.card A) := hunif.entropy_eq' (toFinite _) hU
  simp only [rho, rhoPlus, this, Nat.card_eq_fintype_card, Fintype.card_coe, add_sub_cancel_right,
    add_self_div_two]
  apply le_antisymm _ rhoMinus_nonneg
  have Z :=
    rhoMinus_le hA (X := U) (T := fun _ ↦ 0) hunif measurable_const hU (indepFun_const 0).symm (μ :=
      μ)
  have : (fun x ↦ 0) + U = U := by ext y; simp
  simpa [this] using Z


-- @@ L670-718 expanded
/-- If $H$ is a finite subgroup of $G$, and $\rho(U_H) \leq r$, then there exists $t$ such
that $|A \cap (H+t)| \geq e^{-r} \sqrt{|A||H|}$, and $|H|/|A| \in [e^{-2r}, e^{2r}]$. -/
lemma rho_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G} {U : Ω → G}
    (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) (r : ℝ)
    (hr : rho U A μ ≤ r) :
    ∃ t : G,
      exp (-r) * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (1 / 2 : ℝ) ≤
          Nat.card ↑(↑A ∩ (t +ᵥ (H : Set G))) ∧
        Nat.card A ≤ exp (2 * r) * (H : Set G).ncard ∧
          (H : Set G).ncard ≤ exp (2 * r) * Nat.card A :=
  by
  have hr' : rho U A μ ≤ r := hr
  have Hpos : 0 < ((H : Set G).ncard : ℝ) := by exact_mod_cast Nat.card_pos
  have : Nonempty A := hA.to_subtype
  have Apos : 0 < (Nat.card A : ℝ) := by exact_mod_cast Nat.card_pos
  simp only [rho] at hr
  rw [rhoMinus_of_subgroup hunif hA hU, rhoPlus_of_subgroup hunif hA hU] at hr
  rcases exists_card_inter_add_eq_sSup (A := A) H hA with ⟨t, ht, hpos⟩
  rw [← ht] at hr
  have Rm : 0 ≤ rhoMinus U A μ := rhoMinus_nonneg
  have RM : 0 ≤ rhoPlus U A μ :=
    by
    rw [rhoPlus_of_subgroup hunif hA hU, ← ht, sub_nonneg]
    apply log_le_log (mod_cast hpos)
    norm_cast
    have : Nat.card (t +ᵥ (H : Set G) : Set G) = (H : Set G).ncard := by
      apply Nat.card_image_of_injective (add_right_injective t)
    rw [← this]
    exact Nat.card_mono (toFinite _) inter_subset_right
  have I : |log ((H : Set G).ncard) - log (Nat.card A)| ≤ 2 * r :=
    calc
      |log ((H : Set G).ncard) - log (Nat.card A)|
      _ = |entropy U μ - log (Nat.card A)| := by rw [hunif.entropy_eq' (toFinite _) hU]
      _ = |rhoPlus U A μ - rhoMinus U A μ| := by congr 1; simp [rhoPlus]; abel
      _ ≤ rhoPlus U A μ + rhoMinus U A μ :=
        ((abs_sub _ _).trans_eq (by simp [abs_of_nonneg, Rm, RM]))
      _ = 2 * rho U A μ := by simp [rho]; ring
      _ ≤ 2 * r := by linarith
  refine ⟨t, ?_, ?_, ?_⟩
  · have :
      -r + (log (Nat.card A) + log ((H : Set G).ncard)) * (1 / 2 : ℝ) ≤
        log (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)) :=
      by linarith
    have := exp_monotone this
    rwa [exp_add, exp_log (mod_cast hpos), exp_mul, exp_add, exp_log Hpos, exp_log Apos, mul_rpow, ←
        mul_assoc] at this <;>
      positivity
  · have : log (Nat.card A) ≤ 2 * r + log ((H : Set G).ncard) := by
      linarith [(abs_sub_le_iff.1 I).2]
    have := exp_monotone this
    rwa [exp_log Apos, exp_add, exp_log Hpos] at this
  · have : log ((H : Set G).ncard) ≤ 2 * r + log (Nat.card A) := by
      linarith [(abs_sub_le_iff.1 I).1]
    have := exp_monotone this
    rwa [exp_log Hpos, exp_add, exp_log Apos] at this


-- @@ L720-731 expanded
/-- If $H$ is a finite subgroup of $G$, and $\rho(U_H) \leq r$, then there exists $t$ such
that $|A \cap (H+t)| \geq e^{-r} \sqrt{|A||H|}$, and $|H|/|A| \in [e^{-2r}, e^{2r}]$. -/
lemma rho_of_submodule [IsProbabilityMeasure μ] [Module (ZMod 2) G] {H : Submodule (ZMod 2) G}
    {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U)
    (r : ℝ) (hr : rho U A μ ≤ r) :
    ∃ t : G,
      exp (-r) * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (1 / 2 : ℝ) ≤
          Nat.card ↑(↑A ∩ (t +ᵥ (H : Set G))) ∧
        Nat.card A ≤ exp (2 * r) * (H : Set G).ncard ∧
          (H : Set G).ncard ≤ exp (2 * r) * Nat.card A :=
  rho_of_subgroup (H := H.toAddSubgroup) hunif hA hU r hr


-- @@ L733-737 expanded
/-- \rho(X)$ depends continuously on the distribution of $X$. -/
lemma rho_continuous [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] {A : Finset G}
    (hA : A.Nonempty) : Continuous fun μ : ProbabilityMeasure G ↦ rho (id : G → G) A μ :=
  ((rhoMinus_continuous hA).add (rhoPlus_continuous hA)).div_const _


-- @@ L739-752 expanded
lemma tendsto_rho_probabilityMeasure {α : Type*} {l : Filter α} [TopologicalSpace Ω] [BorelSpace Ω]
    [TopologicalSpace G] [BorelSpace G] [DiscreteTopology G] {X : Ω → G} (hX : Continuous X)
    (hA : A.Nonempty) {μ : α → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
    (hμ : Tendsto μ l (𝓝 ν)) : Tendsto (fun n ↦ rho X A (μ n : Measure Ω)) l (𝓝 (rho X A ν)) :=
  by
  have J (η : ProbabilityMeasure Ω) : rho X A η = rho (id : G → G) A (η.map X) :=
    by
    apply rho_eq_of_identDistrib
    exact ⟨hX.aemeasurable, aemeasurable_id, by simp⟩
  simp_rw [J]
  have Z := ((rho_continuous hA).tendsto ((ν.map X)))
  have T : Tendsto (fun n ↦ (μ n).map X) l (𝓝 (ν.map X)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hμ hX
  apply Z.comp T


-- @@ L754-811 expanded
/-- If $X,Y$ are independent, one has
  $$ \rho^-(X+Y) \leq \rho^-(X)$$ -/
lemma rhoMinus_of_sum [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hA : A.Nonempty) (h_indep : IndepFun X Y μ) : rhoMinus (X + Y) A μ ≤ rhoMinus X A μ :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with hμ | hμ
  · simp [rhoMinus_zero_measure hμ]
  apply le_csInf (nonempty_rhoMinusSet hA)
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  rintro - ⟨μ', μ'_prob, habs, rfl⟩
  obtain ⟨Ω', hΩ', m, X', Y', T, U, hm, h_indep', hX', hY', hT, hU, hXX', hYY', hTμ, hU_unif⟩ :=
    independent_copies4_nondep (X₁ := X) (X₂ := Y) (X₃ := id) (X₄ := id) hX hY measurable_id
      measurable_id μ μ μ' (uniformOn (A : Set G))
  let : MeasureSpace Ω' := ⟨m⟩
  have hP : (ℙ : Measure Ω') = m := rfl
  have hTU : IdentDistrib (T + U) (Prod.fst + Prod.snd) ℙ (μ'.prod (uniformOn (A : Set G))) :=
    by
    apply IdentDistrib.add
    · exact hTμ.trans IdentDistrib.fst_id.symm
    · exact hU_unif.trans IdentDistrib.snd_id.symm
    · exact h_indep'.indepFun (i := 2) (j := 3) (by simp)
    · exact indepFun_fst_snd
  have hXY : IdentDistrib (X + Y) (X' + Y') μ ℙ :=
    by
    apply IdentDistrib.add hXX'.symm hYY'.symm h_indep
    exact h_indep'.indepFun zero_ne_one
  have hX'TUY' : IndepFun (⟨X', T + U⟩) Y' ℙ :=
    by
    have I : iIndepFun ![X', Y', T + U] m :=
      ProbabilityTheory.iIndepFun.apply_two_last h_indep' hX' hY' hT hU (phi := fun a b ↦ a + b)
        (by fun_prop)
    exact (I.reindex_three_bac.pair_last_of_three hY' hX' (by fun_prop)).symm
  have I₁ : rhoMinus (X + Y) A μ ≤ KLDiv (X + Y) ((T + Y') + U) μ ℙ :=
    by
    apply rhoMinus_le hA _ (by fun_prop) (by fun_prop)
    · have : iIndepFun ![U, X', T, Y'] := h_indep'.reindex_four_dacb
      have : iIndepFun ![U, X', T + Y'] :=
        this.apply_two_last (phi := fun a b ↦ a + b) hU hX' hT hY' (by fun_prop)
      apply this.indepFun (i := 2) (j := 0)
      simp
    · rw [hXY.map_eq]
      have : T + Y' + U = (T + U) + Y' := by abel
      rw [this]
      apply absolutelyContinuous_add_of_indep hX'TUY' hX' (by fun_prop) hY'
      rw [hTU.map_eq, hP, hXX'.map_eq]
      exact habs
    · exact isUniform_uniformOn.of_identDistrib hU_unif.symm A.measurableSet
  have I₂ : KLDiv (X + Y) ((T + Y') + U) μ ℙ = KLDiv (X' + Y') ((T + U) + Y') volume volume :=
    by
    apply IdentDistrib.KLDiv_eq _ _ hXY
    have : T + Y' + U = T + U + Y' := by abel
    rw [this]
    exact .refl <| by fun_prop
  have I₃ : KLDiv (X' + Y') ((T + U) + Y') volume volume ≤ KLDiv X' (T + U) volume volume :=
    by
    apply KLDiv_add_le_KLDiv_of_indep _ (by fun_prop) (by fun_prop) (by fun_prop)
    · rw [hTU.map_eq, hP, hXX'.map_eq]
      exact habs
    · exact hX'TUY'
  have I₄ :
    KLDiv X' (T + U) volume volume =
      KLDiv X (Prod.fst + Prod.snd) μ (μ'.prod (uniformOn (A : Set G))) :=
    IdentDistrib.KLDiv_eq _ _ hXX' hTU
  exact ((I₁.trans_eq I₂).trans I₃).trans_eq I₄


-- @@ L813-820 expanded
/-- If $X,Y$ are independent, one has
$$ \rho^+(X+Y) \leq \rho^+(X) + \bbH[X+Y] - \bbH[X]$$ -/
lemma rhoPlus_of_sum [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    rhoPlus (X + Y) A μ ≤ rhoPlus X A μ + entropy (X + Y) μ - entropy X μ :=
  by
  simp [rhoPlus]
  have := rhoMinus_of_sum hX hY hA h_indep
  linarith


-- @@ L822-829 expanded
/-- If $X,Y$ are independent, one has
$$\rho(X+Y) \leq \rho(X) + \frac{1}{2}( \bbH[X+Y] - \bbH[X]).$$ -/
lemma rho_of_sum [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    rho (X + Y) A μ ≤ rho X A μ + (entropy (X + Y) μ - entropy X μ) / 2 :=
  by
  simp [rho, rhoPlus]
  have := rhoMinus_of_sum hX hY hA h_indep
  linarith


-- @@ L831-837 expanded
private lemma rho_le_translate [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hA : A.Nonempty)
    (s : G) : rho (fun ω ↦ X ω + s) A μ ≤ rho X A μ :=
  by
  have : rho (fun ω ↦ X ω + s) A μ ≤ rho X A μ + (entropy (fun ω ↦ X ω + s) μ - entropy X μ) / 2 :=
    rho_of_sum (Y := fun ω ↦ s) hX measurable_const hA (indepFun_const s)
  have : entropy (fun ω ↦ X ω + s) μ = entropy X μ := entropy_add_const hX _
  linarith


-- @@ L839-845 expanded
lemma rho_of_translate [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hA : A.Nonempty)
    (s : G) : rho (fun ω ↦ X ω + s) A μ = rho X A μ :=
  by
  apply le_antisymm (rho_le_translate hX hA s)
  simpa using
    rho_le_translate (X := fun ω ↦ X ω + s) (by fun_prop) hA
      (-s)
        -- This may not be the optimal spelling for condRho, feel free to improve


-- @@ L846-849 expanded
/-- We define $\rho(X|Y) := \sum_y {\bf P}(Y=y) \rho(X|Y=y)$. -/
noncomputable def condRho {S : Type*} (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω) : ℝ :=
  ∑' s, μ.real (Y ⁻¹' { s }) * rho X A μ[|Y ← s]


-- @@ L851-854 expanded
/-- Average of rhoMinus along the fibers. -/
noncomputable def condRhoMinus {S : Type*} (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω) :
    ℝ :=
  ∑' s, μ.real (Y ⁻¹' { s }) * rhoMinus X A μ[|Y ← s]


-- @@ L856-859 expanded
/-- Average of rhoPlus along the fibers. -/
noncomputable def condRhoPlus {S : Type*} (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω) :
    ℝ :=
  ∑' s, μ.real (Y ⁻¹' { s }) * rhoPlus X A μ[|Y ← s]


-- @@ L861-862 verbatim
@[inherit_doc condRho]
notation3:max "ρ[" X " | " Z " ; " μ " # " A "]" => condRho X Z A μ


-- @@ L864-865 verbatim
@[inherit_doc condRho]
notation3:max "ρ[" X " | " Z " # " A "]" => condRho X Z A volume


-- @@ L867-868 verbatim
@[inherit_doc condRhoMinus]
notation3:max "ρ⁻[" X " | " Z " ; " μ " # " A "]" => condRhoMinus X Z A μ


-- @@ L870-871 verbatim
@[inherit_doc condRhoPlus]
notation3:max "ρ⁺[" X " | " Z " ; " μ " # " A "]" => condRhoPlus X Z A μ


-- @@ L873-877 expanded
/-- For any $s\in G$, $\rho(X+s|Y)=\rho(X|Y)$. -/
lemma condRho_of_translate {S : Type*} {Y : Ω → S} (hX : Measurable X) (hA : A.Nonempty) (s : G) :
    condRho (fun ω ↦ X ω + s) Y A μ = condRho X Y A μ := by simp [condRho, rho_of_translate hX hA]


-- @@ L879-897 expanded
omit [Finite G] [DiscreteMeasurableSpace G] in
variable (X) in
/-- If $f$ is injective, then $\rho(X|f(Y))=\rho(X|Y)$. -/
lemma condRho_of_injective {S T : Type*} (Y : Ω → S) {A : Finset G} {f : S → T}
    (hf : Function.Injective f) : condRho X (f ∘ Y) A μ = condRho X Y A μ :=
  by
  simp only [condRho]
  rw [← hf.tsum_eq]
  · have I c : f ∘ Y ⁻¹' {f c} = Y ⁻¹' { c } := by ext z; simp [hf.eq_iff]
    simp [I]
  · intro y hy
    have : f ∘ Y ⁻¹' { y } ≠ ∅ := by
      intro h
      simp [h] at hy
    rcases Set.nonempty_iff_ne_empty.2 this with ⟨a, ha⟩
    simp only [mem_preimage, Function.comp_apply, mem_singleton_iff] at ha
    rw [← ha]
    exact mem_range_self (Y a)


-- @@ L899-922 expanded
lemma condRho_eq_of_identDistrib {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    {Y : Ω → G} {W : Ω → S} {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {Y' : Ω' → G}
    {W' : Ω' → S} (hY : Measurable Y) (hW : Measurable W) (hY' : Measurable Y')
    (hW' : Measurable W') (h : IdentDistrib (⟨Y, W⟩) (⟨Y', W'⟩) μ μ') :
    condRho Y W A μ = condRho Y' W' A μ' :=
  by
  rw [condRho]
  congr with g
  have M : μ (W ⁻¹' { g }) = μ' (W' ⁻¹' { g }) :=
    by
    have I : IdentDistrib W W' μ μ' := h.comp (u := Prod.snd) measurable_snd
    rw [← map_apply hW (.singleton _), ← map_apply hW' (.singleton _), I.map_eq]
  have M' : μ.real (W ⁻¹' { g }) = μ'.real (W' ⁻¹' { g }) := by simp [measureReal_def, M]
  rw [M']
  congr 1
  apply rho_eq_of_identDistrib
  refine ⟨hY.aemeasurable, hY'.aemeasurable, ?_⟩
  ext s hs
  rw [map_apply hY hs, map_apply hY' hs, cond_apply (hW (.singleton _)),
    cond_apply (hW' (.singleton _)), M]
  congr
  have E : W ⁻¹' { g } ∩ Y ⁻¹' s = (⟨Y, W⟩) ⁻¹' (s ×ˢ { g }) := by ext; aesop
  have F : W' ⁻¹' { g } ∩ Y' ⁻¹' s = (⟨Y', W'⟩) ⁻¹' (s ×ˢ { g }) := by ext; aesop
  rw [E, F, ← map_apply (by fun_prop) (hs.prod (.singleton _)), ←
    map_apply (by fun_prop) (hs.prod (.singleton _)), h.map_eq]


-- @@ L924-950 expanded
/-- $$ \rho^-(X|Z) \leq \rho^-(X) + \bbH[X] - \bbH[X|Z]$$ -/
lemma condRhoMinus_le [IsZeroOrProbabilityMeasure μ] {S : Type*} [MeasurableSpace S] [Finite S]
    [MeasurableSingletonClass S] {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z)
    (hA : A.Nonempty) : condRhoMinus X Z A μ ≤ rhoMinus X A μ + entropy X μ - condEntropy X Z μ :=
  by
  cases nonempty_fintype S
  have : IsProbabilityMeasure (uniformOn (A : Set G)) := by
    apply isProbabilityMeasure_uniformOn A.finite_toSet hA
  suffices condRhoMinus X Z A μ - entropy X μ + condEntropy X Z μ ≤ rhoMinus X A μ by linarith
  apply le_csInf (nonempty_rhoMinusSet hA)
  rintro - ⟨μ', hμ', habs, rfl⟩
  rw [condRhoMinus, tsum_fintype]
  let : MeasureSpace (G × G) := ⟨μ'.prod (uniformOn (A : Set G))⟩
  have hP : (ℙ : Measure (G × G)) = μ'.prod (uniformOn (A : Set G)) := rfl
  have : IsProbabilityMeasure (ℙ : Measure (G × G)) := by rw [hP]; infer_instance
  have :
    ∑ b : S, μ.real (Z ⁻¹' { b }) * rhoMinus X A μ[|Z ← b] ≤
      condKLDiv X (Prod.fst + Prod.snd : G × G → G) Z μ ℙ :=
    by
    rw [condKLDiv, tsum_fintype]
    apply Finset.sum_le_sum (fun i hi ↦ ?_)
    gcongr
    apply rhoMinus_le_def fun y hy ↦ ?_
    have T := habs y hy
    rw [Measure.map_apply hX (measurableSet_singleton _)] at T ⊢
    exact cond_absolutelyContinuous T
  rw [condKLDiv_eq hX hZ (by exact habs)] at this
  rw [← hP]
  linarith


-- @@ L952-967 expanded
/-- $$ \rho^+(X|Z) \leq \rho^+(X)$$ -/
lemma condRhoPlus_le [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S] [Finite S]
    [MeasurableSingletonClass S] {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z)
    (hA : A.Nonempty) : condRhoPlus X Z A μ ≤ rhoPlus X A μ :=
  by
  cases nonempty_fintype S
  have I₁ := condRhoMinus_le hX hZ hA (μ := μ)
  simp_rw [condRhoPlus, rhoPlus, tsum_fintype]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, tsub_le_iff_right]
  rw [← Finset.sum_mul, ← tsum_fintype (L := SummationFilter.unconditional _), ← condRhoMinus, ←
    condEntropy_eq_sum_fintype _ _ _ hZ]
  simp_rw [← map_measureReal_apply hZ (measurableSet_singleton _)]
  simp only [sum_measureReal_singleton, Finset.coe_univ, probReal_univ, one_mul, sub_add_cancel,
    ge_iff_le]
  linarith


-- @@ L969-975 expanded
omit [Finite G] [DiscreteMeasurableSpace G] in
lemma condRho_eq {S : Type*} [Finite S] {Z : Ω → S} :
    condRho X Z A μ = (condRhoMinus X Z A μ + condRhoPlus X Z A μ) / 2 :=
  by
  cases nonempty_fintype S
  simp_rw [condRho, rho, ← mul_div_assoc, tsum_fintype, ← Finset.sum_div, mul_add,
    Finset.sum_add_distrib, ← tsum_fintype (L := SummationFilter.unconditional _)]
  rfl


-- @@ L977-983 expanded
/-- $$ \rho(X|Z) \leq \rho(X) + \frac{1}{2}( \bbH[X] - \bbH[X|Z])$$ -/
lemma condRho_le [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S] [Finite S]
    [MeasurableSingletonClass S] {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z)
    (hA : A.Nonempty) : condRho X Z A μ ≤ rho X A μ + (entropy X μ - condEntropy X Z μ) / 2 :=
  by
  rw [condRho_eq, rho]
  linarith [condRhoMinus_le hX hZ hA (μ := μ), condRhoPlus_le hX hZ hA (μ := μ)]


-- @@ L985-1009 expanded
omit [Finite G] [DiscreteMeasurableSpace G] in
lemma condRho_prod_eq_sum [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S] [Fintype S]
    [MeasurableSingletonClass S] {Z T : Ω → S} (hZ : Measurable Z) (hT : Measurable T) :
    condRho X ⟨Z, T⟩ A μ = ∑ g, μ.real (T ⁻¹' { g }) * condRho X Z A μ[|T ← g] :=
  by
  rw [condRho, tsum_fintype, ← Finset.univ_product_univ, Finset.sum_product_right]
  congr 1 with w
  simp only [condRho, tsum_fintype, Finset.mul_sum]
  congr 1 with w'
  rw [← mul_assoc]
  have A : (fun a ↦ (Z a, T a)) ⁻¹' {(w', w)} = Z ⁻¹' { w' } ∩ T ⁻¹' { w } := by ext; simp
  congr 1
  · simp only [A, ProbabilityTheory.cond]
    rcases le_or_gt (μ.real (T ⁻¹' { w })) 0 with hw | hw
    · have : μ.real (Z ⁻¹' { w' } ∩ T ⁻¹' { w }) = 0 :=
        le_antisymm (le_trans (measureReal_mono Set.inter_subset_right) hw) measureReal_nonneg
      have hw' : μ.real (T ⁻¹' { w }) = 0 := le_antisymm hw measureReal_nonneg
      simp [hw', this]
    · simp only [measureReal_ennreal_smul_apply, ENNReal.toReal_inv]
      rw [← mul_assoc, ← measureReal_def, mul_inv_cancel₀ hw.ne', one_mul]
      rw [measureReal_def, measureReal_def, Measure.restrict_apply]
      exact hZ (measurableSet_singleton w')
  · congr 1
    rw [A, cond_cond_eq_cond_inter' (hT (.singleton _)) (hZ (.singleton _)), Set.inter_comm]
    finiteness


-- @@ L1011-1030 expanded
/-- $$ \rho(X|Z) \leq \rho(X) + \frac{1}{2}( \bbH[X] - \bbH[X|Z])$$, conditional version -/
lemma condRho_prod_le [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S] [Finite S]
    [MeasurableSingletonClass S] {Z T : Ω → S} (hX : Measurable X) (hZ : Measurable Z)
    (hT : Measurable T) (hA : A.Nonempty) :
    condRho X ⟨Z, T⟩ A μ ≤ condRho X T A μ + (condEntropy X T μ - condEntropy X ⟨Z, T⟩ μ) / 2 :=
  by
  cases nonempty_fintype S
  rw [condRho_prod_eq_sum hZ hT]
  have :
    ∑ g : S, μ.real (T ⁻¹' { g }) * condRho X Z A μ[|T ⁻¹' { g }] ≤
      ∑ g : S,
        μ.real (T ⁻¹' { g }) *
          (rho X A μ[|T ⁻¹' { g }] +
            (entropy X μ[|T ⁻¹' { g }] - condEntropy X Z μ[|T ⁻¹' { g }]) / 2) :=
    by
    apply Finset.sum_le_sum (fun g hg ↦ ?_)
    rcases eq_or_ne (μ.real (T ⁻¹' { g })) 0 with hpg | hpg
    · simp [hpg]
    gcongr
    have hμ : IsProbabilityMeasure (μ[|T ⁻¹' { g }]) := cond_isProbabilityMeasure_of_real hpg
    exact condRho_le hX hZ hA
  apply this.trans_eq
  simp_rw [mul_add, mul_div, mul_sub, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_sub_distrib, condRho, tsum_fintype, condEntropy_eq_sum_fintype X T μ hT,
    condEntropy_prod_eq_sum μ hZ hT]


-- @@ L1032-1050 expanded
lemma condRho_prod_eq_of_indepFun [IsProbabilityMeasure μ] {X : Ω → G} {S : Type*} [Finite S]
    [MeasurableSpace S] [MeasurableSingletonClass S] {W W' : Ω → S} (hX : Measurable X)
    (hW : Measurable W) (hW' : Measurable W') (h : IndepFun (⟨X, W⟩) W' μ) :
    condRho X ⟨W, W'⟩ A μ = condRho X W A μ :=
  by
  cases nonempty_fintype S
  rw [condRho_prod_eq_sum hW hW']
  have : condRho X W A μ = ∑ z, μ.real (W' ⁻¹' { z }) * condRho X W A μ :=
    by
    rw [← Finset.sum_mul, sum_measureReal_preimage_singleton]
    · simp
    · exact fun y hy ↦ hW' (measurableSet_singleton y)
  rw [this]
  congr with w
  rcases eq_or_ne (μ.real (W' ⁻¹' { w })) 0 with hw | hw
  · simp [hw]
  congr 1
  apply condRho_eq_of_identDistrib hX hW hX hW
  simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at hw
  exact (h.identDistrib_cond (MeasurableSet.singleton w) (by fun_prop) hW' hw).symm


-- @@ L1052-1052 verbatim
variable [Module (ZMod 2) G]


-- @@ L1054-1067 expanded
/-- If $X,Y$ are independent, then
  $$ \rho(X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$ -/
lemma rho_of_sum_le [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    rho (X + Y) A μ ≤ (rho X A μ + rho Y A μ + rdist X Y μ μ) / 2 :=
  by
  have I : rho (X + Y) A μ ≤ rho X A μ + (entropy (X + Y) μ - entropy X μ) / 2 :=
    rho_of_sum hX hY hA h_indep
  have J : rho (Y + X) A μ ≤ rho Y A μ + (entropy (Y + X) μ - entropy Y μ) / 2 :=
    rho_of_sum hY hX hA h_indep.symm
  have : Y + X = X + Y := by abel
  rw [this] at J
  have : X - Y = X + Y := ZModModule.sub_eq_add _ _
  rw [h_indep.rdist_eq hX hY, sub_eq_add_neg, this]
  linarith


-- @@ L1069-1107 expanded
/-- If $X,Y$ are independent, then
  $$ \rho(X | X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$ -/
lemma condRho_of_sum_le [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    condRho X (X + Y) A μ ≤ (rho X A μ + rho Y A μ + rdist X Y μ μ) / 2 :=
  by
  have I : condRho X (X + Y) A μ ≤ rho X A μ + (entropy X μ - condEntropy X (X + Y) μ) / 2 :=
    condRho_le hX (by fun_prop) hA
  have I' : entropy X μ - condEntropy X (X + Y) μ = entropy (X + Y) μ - entropy Y μ :=
    by
    rw [ProbabilityTheory.chain_rule'' _ hX (by fun_prop), entropy_add_right hX hY,
      IndepFun.entropy_pair_eq_add hX hY h_indep]
    abel
  have J : condRho Y (Y + X) A μ ≤ rho Y A μ + (entropy Y μ - condEntropy Y (Y + X) μ) / 2 :=
    condRho_le hY (by fun_prop) hA
  have J' : entropy Y μ - condEntropy Y (Y + X) μ = entropy (Y + X) μ - entropy X μ :=
    by
    rw [ProbabilityTheory.chain_rule'' _ hY (by fun_prop), entropy_add_right hY hX,
      IndepFun.entropy_pair_eq_add hY hX h_indep.symm]
    abel
  have : Y + X = X + Y := by abel
  simp only [this] at J J'
  have : condRho X (X + Y) A μ = condRho Y (X + Y) A μ :=
    by
    simp only [condRho]
    congr with s
    congr 1
    have : rho X A μ[|(X + Y) ⁻¹' { s }] = rho (fun ω ↦ X ω + s) A μ[|(X + Y) ⁻¹' { s }] := by
      rw [rho_of_translate hX hA]
    rw [this]
    apply rho_eq_of_identDistrib
    apply IdentDistrib.of_ae_eq (by fun_prop)
    have : MeasurableSet ((X + Y) ⁻¹' { s }) :=
      by
      have : Measurable (X + Y) := by fun_prop
      exact this (measurableSet_singleton _)
    filter_upwards [ae_cond_mem this] with a ha
    simp only [mem_preimage, Pi.add_apply, mem_singleton_iff] at ha
    rw [← ha]
    nth_rewrite 1 [← ZModModule.neg_eq_self (X a)]
    abel
  have : X - Y = X + Y := ZModModule.sub_eq_add _ _
  rw [h_indep.rdist_eq hX hY, sub_eq_add_neg, this]
  linarith


-- @@ L1109-1109 verbatim
end


-- @@ L1111-1111 verbatim
section phiMinimizer


-- @@ L1113-1114 verbatim
variable {G : Type uG} [AddCommGroup G] [Finite G] [hGm : MeasurableSpace G]
  [DiscreteMeasurableSpace G] {Ω : Type*} [MeasureSpace Ω] {X Y Z : Ω → G} {A : Finset G}


-- @@ L1116-1120 expanded
/-- Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$. -/
noncomputable def phi {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → G) (η : ℝ) (A : Finset G)
    (μ : Measure Ω) : ℝ :=
  rdist X Y μ μ + η * (rho X A μ + rho Y A μ)


-- @@ L1122-1130 verbatim
/-- Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$
and define a \emph{$\phi$-minimizer} to be a pair of random variables $X,Y$ which
minimizes $\phi[X;Y]$. -/
def phiMinimizes {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → G) (η : ℝ) (A : Finset G)
    (μ : Measure Ω) : Prop :=
  ∀ (Ω' : Type uG) (_ : MeasureSpace Ω') (X' Y' : Ω' → G),
    IsProbabilityMeasure (ℙ : Measure Ω') → Measurable X' → Measurable Y' →
    phi X Y η A μ ≤ phi X' Y' η A ℙ


-- @@ L1132-1139 verbatim
lemma phiMinimizes_of_identDistrib {Ω' : Type*} [MeasureSpace Ω']
    {X Y : Ω → G} {X' Y' : Ω' → G} {η : ℝ} {A : Finset G}
    (h_min : phiMinimizes X Y η A ℙ) (h₁ : IdentDistrib X X') (h₂ : IdentDistrib Y Y') :
    phiMinimizes X' Y' η A ℙ := by
  have : phi X Y η A ℙ = phi X' Y' η A ℙ := by
    simp only [phi]
    rw [h₁.rdist_congr h₂, rho_eq_of_identDistrib h₁, rho_eq_of_identDistrib h₂]
  simpa [phiMinimizes, this] using h_min


-- @@ L1141-1147 verbatim
lemma phiMinimizes_comm [IsProbabilityMeasure (ℙ : Measure Ω)] {X Y : Ω → G} {η : ℝ} {A : Finset G}
    (h_min : phiMinimizes X Y η A ℙ) : phiMinimizes Y X η A ℙ := by
  have : phi Y X η A ℙ = phi X Y η A ℙ := by
    simp only [phi]
    rw [rdist_symm]
    linarith
  simpa [phiMinimizes, this] using h_min


-- @@ L1149-1149 verbatim
variable {η : ℝ} (hη : 0 < η)


-- @@ L1151-1186 expanded
/-- There exists a $\phi$-minimizer. -/
lemma phi_min_exists (hA : A.Nonempty) :
    ∃ (μ : Measure (G × G)), IsProbabilityMeasure μ ∧ phiMinimizes Prod.fst Prod.snd η A μ :=
  by
  let : TopologicalSpace G := (⊥ : TopologicalSpace G)
  have : DiscreteTopology G := ⟨rfl⟩
  let iG : Inhabited G := ⟨0⟩
  have T : Continuous (fun (μ : ProbabilityMeasure (G × G)) ↦ phi Prod.fst Prod.snd η A μ) :=
    by
    apply continuous_iff_continuousAt.2 (fun μ ↦ ?_)
    apply Tendsto.add
    · apply tendsto_rdist_probabilityMeasure continuous_fst continuous_snd tendsto_id
    apply Tendsto.const_mul
    apply Tendsto.add
    · apply tendsto_rho_probabilityMeasure continuous_fst hA tendsto_id
    · apply tendsto_rho_probabilityMeasure continuous_snd hA tendsto_id
  obtain ⟨μ, _, hμ⟩ :=
    @IsCompact.exists_isMinOn ℝ (ProbabilityMeasure (G × G)) _ _ _ _ Set.univ isCompact_univ
      ⟨default, trivial⟩ _ T.continuousOn
  refine ⟨μ, by infer_instance, ?_⟩
  intro Ω' mΩ' X' Y' hP hX' hY'
  let ν : Measure (G × G) := Measure.map (⟨X', Y'⟩) ℙ
  let ν' : ProbabilityMeasure (G × G) := ⟨ν, inferInstance⟩
  have : phi Prod.fst Prod.snd η A ↑μ ≤ phi Prod.fst Prod.snd η A ↑ν' := hμ (mem_univ _)
  apply this.trans_eq
  have h₁ : IdentDistrib Prod.fst X' (ν' : Measure (G × G)) ℙ :=
    by
    refine ⟨measurable_fst.aemeasurable, hX'.aemeasurable, ?_⟩
    simp only [ProbabilityMeasure.coe_mk, ν', ν]
    rw [Measure.map_map measurable_fst (by fun_prop)]
    rfl
  have h₂ : IdentDistrib Prod.snd Y' (ν' : Measure (G × G)) ℙ :=
    by
    refine ⟨measurable_snd.aemeasurable, hY'.aemeasurable, ?_⟩
    simp only [ProbabilityMeasure.coe_mk, ν', ν]
    rw [Measure.map_map measurable_snd (by fun_prop)]
    rfl
  simp [phi, h₁.rdist_congr h₂, rho_eq_of_identDistrib h₁, rho_eq_of_identDistrib h₂]
    -- Let $(X_1, X_2)$ be a $\phi$-minimizer, and $\tilde X_1, \tilde X_2$ be independent copies
    -- of $X_1,X_2$ respectively.


-- @@ L1187-1191 verbatim
variable {X₁ X₂ X₁' X₂' : Ω → G} (h_min : phiMinimizes X₁ X₂ η A ℙ)
  (h₁ : IdentDistrib X₁ X₁')
  (h₂ : IdentDistrib X₂ X₂')
  (h_indep : iIndepFun ![X₁, X₂, X₁', X₂'])
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')


-- @@ L1193-1193 expanded
local notation3 "I₁" => condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume


-- @@ L1194-1194 expanded
local notation3 "I₂" => condMutualInfo (X₁ + X₂) (X₁ + X₁') (X₁ + X₂ + X₁' + X₂') volume


-- @@ L1195-1196 expanded
/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => rdist X₁ X₂ volume volume


-- @@ L1198-1221 expanded
lemma le_rdist_of_phiMinimizes (h_min : phiMinimizes X₁ X₂ η A ℙ) {Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {X₁' : Ω₁ → G} {X₂' : Ω₂ → G}
    (hX₁' : Measurable X₁') (hX₂' : Measurable X₂') :
    rdist X₁ X₂ volume volume - η * (rho X₁' A μ₁ - rho X₁ A volume) -
        η * (rho X₂' A μ₂ - rho X₂ A volume) ≤
      rdist X₁' X₂' μ₁ μ₂ :=
  by
  let Ω' : Type uG := G × G
  let m : Measure Ω' := (Measure.map X₁' μ₁).prod (Measure.map X₂' μ₂)
  have m_prob : IsProbabilityMeasure m := by infer_instance
  let : MeasureSpace Ω' := ⟨m⟩
  have hP : (ℙ : Measure Ω') = m := rfl
  let Y₁ : G × G → G := Prod.fst
  let Y₂ : G × G → G := Prod.snd
  have : phi X₁ X₂ η A ℙ ≤ phi Y₁ Y₂ η A ℙ := h_min _ _ _ _ m_prob measurable_fst measurable_snd
  have Id₁ : IdentDistrib Y₁ X₁' ℙ μ₁ :=
    ⟨measurable_fst.aemeasurable, hX₁'.aemeasurable, by simp [Y₁, hP, m]⟩
  have Id₂ : IdentDistrib Y₂ X₂' ℙ μ₂ :=
    ⟨measurable_snd.aemeasurable, hX₂'.aemeasurable, by simp [Y₂, hP, m]⟩
  have I : rdist Y₁ Y₂ volume volume = rdist X₁' X₂' μ₁ μ₂ := Id₁.rdist_congr Id₂
  have J : rho Y₁ A volume = rho X₁' A μ₁ := rho_eq_of_identDistrib Id₁
  have K : rho Y₂ A volume = rho X₂' A μ₂ := rho_eq_of_identDistrib Id₂
  simp only [phi, I, J, K] at this
  linarith


-- @@ L1223-1230 expanded
lemma le_rdist_of_phiMinimizes' (h_min : phiMinimizes X₁ X₂ η A ℙ) {Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {X₁' : Ω₁ → G} {X₂' : Ω₂ → G}
    (hX₁' : Measurable X₁') (hX₂' : Measurable X₂') :
    rdist X₁ X₂ volume volume ≤
      rdist X₁' X₂' μ₁ μ₂ + η * (rho X₁' A μ₁ - rho X₁ A volume) +
        η * (rho X₂' A μ₂ - rho X₂ A volume) :=
  by linarith [le_rdist_of_phiMinimizes h_min hX₁' hX₂' (μ₁ := μ₁) (μ₂ := μ₂)]


-- @@ L1232-1232 verbatim
variable [IsProbabilityMeasure (ℙ : Measure Ω)]


-- @@ L1234-1277 expanded
lemma condRho_le_condRuzsaDist_of_phiMinimizes {S T : Type*} [Finite S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Finite T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (h : phiMinimizes X₁ X₂ η A ℙ) (h1 : Measurable X₁') (h2 : Measurable X₂') {Z : Ω → S}
    {W : Ω → T} (hZ : Measurable Z) (hW : Measurable W) :
    k - η * (condRho X₁' Z A volume - rho X₁ A volume) -
        η * (condRho X₂' W A volume - rho X₂ A volume) ≤
      condRuzsaDist X₁' Z X₂' W volume volume :=
  by
  cases nonempty_fintype S
  cases nonempty_fintype T
  have hz (a : ℝ) : a = ∑ z, (Measure.real ℙ (Z ⁻¹' { z })) * a :=
    by
    simp_rw [← Finset.sum_mul, ← map_measureReal_apply hZ (MeasurableSet.singleton _),
      sum_measureReal_singleton]
    simp
  have hw (a : ℝ) : a = ∑ w, (Measure.real ℙ (W ⁻¹' { w })) * a :=
    by
    simp_rw [← Finset.sum_mul, ← map_measureReal_apply hW (MeasurableSet.singleton _),
      sum_measureReal_singleton]
    simp
  rw [condRuzsaDist_eq_sum' h1 hZ h2 hW, hz (rdist X₁ X₂ volume volume), hz (rho X₁ A volume),
    hz (η * (condRho X₂' W A volume - rho X₂ A volume)), condRho, tsum_fintype, ←
    Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro z _
  rw [condRho, tsum_fintype, hw (rho X₂ A volume),
    hw
      ((Measure.real ℙ (Z ⁻¹' { z })) * k -
        η *
          ((Measure.real ℙ (Z ⁻¹' { z })) * rho X₁' A ℙ[|Z ⁻¹' { z }] -
            (Measure.real ℙ (Z ⁻¹' { z })) * rho X₁ A volume)),
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro w _
  rcases eq_or_ne (Measure.real ℙ (Z ⁻¹' { z })) 0 with hpz | hpz
  · simp [hpz]
  rcases eq_or_ne (Measure.real ℙ (W ⁻¹' { w })) 0 with hpw | hpw
  · simp [hpw]
  set μ := ℙ[|Z ← z]
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_real hpz
  set μ' := ℙ[|W ← w]
  have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure_of_real hpw
  suffices
    rdist X₁ X₂ volume volume - η * (rho X₁' A μ - rho X₁ A volume) -
        η * (rho X₂' A μ' - rho X₂ A volume) ≤
      rdist X₁' X₂' μ μ'
    by
    replace this :=
      mul_le_mul_of_nonneg_left this
        (show 0 ≤ (Measure.real ℙ (Z ⁻¹' { z })) * (Measure.real ℙ (W ⁻¹' { w })) by positivity)
    convert this using 1
    ring
  exact le_rdist_of_phiMinimizes h h1 h2


-- @@ L1280-1284 verbatim
variable [Module (ZMod 2) G]

/- *****************************************
First estimate
********************************************* -/


-- @@ L1286-1321 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min hη in
/-- $I_1\le 2\eta d[X_1;X_2]$ -/
lemma I_one_le (hA : A.Nonempty) : I₁ ≤ 2 * η * rdist X₁ X₂ volume volume :=
  by
  have :
    rdist (X₁ + X₂') (X₂ + X₁') volume volume +
          condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume +
        I₁ =
      2 * k :=
    rdist_add_rdist_add_condMutual_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep.reindex_four_abdc
  have :
    k - η * (condRho X₁ (X₁ + X₂') A volume - rho X₁ A volume) -
        η * (condRho X₂ (X₂ + X₁') A volume - rho X₂ A volume) ≤
      condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume :=
    condRho_le_condRuzsaDist_of_phiMinimizes h_min hX₁ hX₂ (by fun_prop) (by fun_prop)
  have :
    k - η * (rho (X₁ + X₂') A volume - rho X₁ A volume) -
        η * (rho (X₂ + X₁') A volume - rho X₂ A volume) ≤
      rdist (X₁ + X₂') (X₂ + X₁') volume volume :=
    le_rdist_of_phiMinimizes h_min (hX₁.add hX₂') (hX₂.add hX₁')
  have :
    rho (X₁ + X₂') A volume ≤ (rho X₁ A volume + rho X₂ A volume + rdist X₁ X₂ volume volume) / 2 :=
    by
    rw [rho_eq_of_identDistrib h₂, h₂.rdist_congr_right hX₁.aemeasurable]
    apply rho_of_sum_le hX₁ hX₂' hA
    simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
  have :
    rho (X₂ + X₁') A volume ≤ (rho X₁ A volume + rho X₂ A volume + rdist X₁ X₂ volume volume) / 2 :=
    by
    rw [add_comm, rho_eq_of_identDistrib h₁, h₁.rdist_congr_left hX₂.aemeasurable]
    apply rho_of_sum_le hX₁' hX₂ hA
    simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 1 by decide)
  have :
    condRho X₁ (X₁ + X₂') A volume ≤
      (rho X₁ A volume + rho X₂ A volume + rdist X₁ X₂ volume volume) / 2 :=
    by
    rw [rho_eq_of_identDistrib h₂, h₂.rdist_congr_right hX₁.aemeasurable]
    apply condRho_of_sum_le hX₁ hX₂' hA
    simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
  have :
    condRho X₂ (X₂ + X₁') A volume ≤
      (rho X₁ A volume + rho X₂ A volume + rdist X₁ X₂ volume volume) / 2 :=
    by
    have :
      condRho X₂ (X₂ + X₁') A volume ≤
        (rho X₂ A volume + rho X₁' A volume + rdist X₂ X₁' volume volume) / 2 :=
      by
      apply condRho_of_sum_le hX₂ hX₁' hA
      simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 2 by decide)
    have I : rho X₁' A volume = rho X₁ A volume := rho_eq_of_identDistrib h₁.symm
    have J : rdist X₂ X₁' volume volume = rdist X₁ X₂ volume volume := by
      rw [rdist_symm, h₁.rdist_congr_left hX₂.aemeasurable]
    linarith
  nlinarith
    /- *****************************************
    Second estimate
    ********************************************* -/


-- @@ L1323-1371 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
lemma I_two_aux :
    rdist X₁ X₁ volume volume + rdist X₂ X₂ volume volume =
      rdist (X₁ + X₂') (X₂ + X₁') volume volume +
          condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume +
        I₂ :=
  by
  cases nonempty_fintype G
  have Z :
    rdist X₁' X₁ volume volume + rdist X₂' X₂ volume volume =
      rdist (X₁' + X₂') (X₁ + X₂) volume volume +
          condRuzsaDist X₁' (X₁' + X₂') X₁ (X₁ + X₂) volume volume +
        condMutualInfo (X₁' + X₁) (X₁ + X₂) (X₁' + X₁ + X₂' + X₂) volume :=
    sum_of_rdist_eq_char_2' X₁' X₁ X₂' X₂ h_indep.reindex_four_cadb hX₁' hX₁ hX₂' hX₂
  have C₁ : X₁' + X₁ + X₂' + X₂ = X₁ + X₂ + X₁' + X₂' := by abel
  have C₂ : X₁' + X₁ = X₁ + X₁' := by abel
  have C₃ : rdist X₁' X₁ volume volume = rdist X₁ X₁ volume volume :=
    h₁.symm.rdist_congr_left hX₁.aemeasurable
  have C₄ : rdist X₂' X₂ volume volume = rdist X₂ X₂ volume volume :=
    h₂.symm.rdist_congr_left hX₂.aemeasurable
  have C₅ : rdist (X₁' + X₂') (X₁ + X₂) volume volume = rdist (X₁ + X₂') (X₂ + X₁') volume volume :=
    by
    apply IdentDistrib.rdist_congr
    · apply h₁.symm.add (.refl hX₂'.aemeasurable)
      · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 3 by decide)
      · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
    · rw [add_comm]
      refine .add (.refl hX₂.aemeasurable) h₁ ?_ ?_
      · simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 0 by decide)
      · simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 2 by decide)
  have C₆ :
    condRuzsaDist X₁' (X₁' + X₂') X₁ (X₁ + X₂) volume volume =
      condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume :=
    by
    have A :
      condRuzsaDist X₁' (X₁' + X₂') X₁ (X₁ + X₂) volume volume =
        condRuzsaDist X₁ (X₁ + X₂') X₁' (X₂ + X₁') volume volume :=
      by
      apply
        condRuzsaDist_of_copy hX₁' (by fun_prop) hX₁ (by fun_prop) hX₁ (by fun_prop) hX₁'
          (by fun_prop)
      · have : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂'⟩) :=
          by
          apply h₁.symm.prodMk (.refl hX₂'.aemeasurable)
          · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 3 by decide)
          · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
        exact this.comp (u := fun (a : G × G) ↦ (a.1, a.1 + a.2)) (by fun_prop)
      · rw [add_comm]
        have : IdentDistrib (⟨X₁, X₂⟩) (⟨X₁', X₂⟩) :=
          by
          apply h₁.prodMk (.refl hX₂.aemeasurable)
          · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 1 by decide)
          · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 1 by decide)
        exact this.comp (u := fun (a : G × G) ↦ (a.1, a.2 + a.1)) (by fun_prop)
    have B :
      condRuzsaDist X₁ (X₁ + X₂') X₁' (X₂ + X₁') volume volume =
        condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume :=
      by
      have J z w :
        rdist X₁ X₁' ℙ[|(X₁ + X₂') ⁻¹' { z }] ℙ[|(X₂ + X₁') ⁻¹' { w }] =
          rdist X₁ X₂ ℙ[|(X₁ + X₂') ⁻¹' { z }] ℙ[|(X₂ + X₁') ⁻¹' { w }] :=
        by
        rw [← rdist_add_const hX₁ hX₂ (c := w)]
        apply (IdentDistrib.refl hX₁.aemeasurable).rdist_congr
        apply IdentDistrib.of_ae_eq hX₁'.aemeasurable
        filter_upwards [ae_cond_mem (hX₂.add hX₁' (measurableSet_singleton _))] with x hx
        simp only [mem_preimage, Pi.add_apply, mem_singleton_iff] at hx
        simp [← hx, ← add_assoc, ZModModule.add_self (X₂ x)]
      rw [condRuzsaDist_eq_sum' hX₁ (by fun_prop) hX₁' (by fun_prop),
        condRuzsaDist_eq_sum' hX₁ (by fun_prop) hX₂ (by fun_prop)]
      simp [J]
    exact A.trans B
  rwa [condMutualInfo_comm (by fun_prop) (by fun_prop), C₁, C₂, C₃, C₄, C₅, C₆] at Z


-- @@ L1373-1382 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
/-- $d[X_1;X_1]+d[X_2;X_2]= 2d[X_1;X_2]+(I_2-I_1)$. -/
lemma rdist_add_rdist_eq :
    rdist X₁ X₁ volume volume + rdist X₂ X₂ volume volume = 2 * k + (I₂ - I₁) :=
  by
  have :
    rdist (X₁ + X₂') (X₂ + X₁') volume volume +
          condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume +
        I₁ =
      2 * k :=
    rdist_add_rdist_add_condMutual_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep.reindex_four_abdc
  have :
    rdist X₁ X₁ volume volume + rdist X₂ X₂ volume volume =
      rdist (X₁ + X₂') (X₂ + X₁') volume volume +
          condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume +
        I₂ :=
    I_two_aux h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂'
  linarith


-- @@ L1384-1398 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
lemma I_two_aux' :
    2 * k =
      rdist (X₁ + X₁') (X₂ + X₂') volume volume +
          condRuzsaDist X₁ (X₁ + X₁') X₂ (X₂ + X₂') volume volume +
        I₂ :=
  by
  have Z :
    rdist X₂ X₁ volume volume + rdist X₂' X₁' volume volume =
      rdist (X₂ + X₂') (X₁ + X₁') volume volume +
          condRuzsaDist X₂ (X₂ + X₂') X₁ (X₁ + X₁') volume volume +
        condMutualInfo (X₂ + X₁) (X₁ + X₁') (X₂ + X₁ + X₂' + X₁') volume :=
    sum_of_rdist_eq_char_2' X₂ X₁ X₂' X₁' h_indep.reindex_four_badc hX₂ hX₁ hX₂' hX₁'
  have C₁ : X₂ + X₁ = X₁ + X₂ := by abel
  have C₂ : X₁ + X₂ + X₂' + X₁' = X₁ + X₂ + X₁' + X₂' := by abel
  have C₃ : rdist X₂ X₁ volume volume = rdist X₁ X₂ volume volume := rdist_symm
  have C₄ : rdist X₂' X₁' volume volume = rdist X₁ X₂ volume volume := by rw [rdist_symm];
    exact h₁.symm.rdist_congr h₂.symm
  have C₅ : rdist (X₂ + X₂') (X₁ + X₁') volume volume = rdist (X₁ + X₁') (X₂ + X₂') volume volume :=
    rdist_symm
  have C₆ :
    condRuzsaDist X₂ (X₂ + X₂') X₁ (X₁ + X₁') volume volume =
      condRuzsaDist X₁ (X₁ + X₁') X₂ (X₂ + X₂') volume volume :=
    condRuzsaDist_symm
  rw [C₁, C₂, C₃, C₄, C₅] at Z
  linarith


-- @@ L1400-1439 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min hη in
/-- $I_2\le 2\eta d[X_1;X_2] + \frac{\eta}{1-\eta}(2\eta d[X_1;X_2]-I_1)$. -/
lemma I_two_le (hA : A.Nonempty) (h'η : η < 1) :
    I₂ ≤ 2 * η * k + (η / (1 - η)) * (2 * η * k - I₁) :=
  by
  have W :
    k - η * (rho (X₁ + X₁') A volume - rho X₁ A volume) -
        η * (rho (X₂ + X₂') A volume - rho X₂ A volume) ≤
      rdist (X₁ + X₁') (X₂ + X₂') volume volume :=
    le_rdist_of_phiMinimizes h_min (hX₁.add hX₁') (hX₂.add hX₂') (μ₁ := ℙ) (μ₂ := ℙ)
  have W' :
    k - η * (condRho X₁ (X₁ + X₁') A volume - rho X₁ A volume) -
        η * (condRho X₂ (X₂ + X₂') A volume - rho X₂ A volume) ≤
      condRuzsaDist X₁ (X₁ + X₁') X₂ (X₂ + X₂') volume volume :=
    condRho_le_condRuzsaDist_of_phiMinimizes h_min hX₁ hX₂ (hX₁.add hX₁') (hX₂.add hX₂')
  have Z :
    2 * k =
      rdist (X₁ + X₁') (X₂ + X₂') volume volume +
          condRuzsaDist X₁ (X₁ + X₁') X₂ (X₂ + X₂') volume volume +
        I₂ :=
    I_two_aux' h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂'
  have :
    rho (X₁ + X₁') A volume ≤ (rho X₁ A volume + rho X₁ A volume + rdist X₁ X₁ volume volume) / 2 :=
    by
    refine
      (rho_of_sum_le hX₁ hX₁' hA
            (by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide))).trans_eq
        ?_
    rw [rho_eq_of_identDistrib h₁.symm, h₁.rdist_congr_right hX₁.aemeasurable]
  have :
    rho (X₂ + X₂') A volume ≤ (rho X₂ A volume + rho X₂ A volume + rdist X₂ X₂ volume volume) / 2 :=
    by
    refine
      (rho_of_sum_le hX₂ hX₂' hA
            (by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide))).trans_eq
        ?_
    rw [rho_eq_of_identDistrib h₂.symm, h₂.rdist_congr_right hX₂.aemeasurable]
  have :
    condRho X₁ (X₁ + X₁') A volume ≤
      (rho X₁ A volume + rho X₁ A volume + rdist X₁ X₁ volume volume) / 2 :=
    by
    refine
      (condRho_of_sum_le hX₁ hX₁' hA
            (by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide))).trans_eq
        ?_
    rw [rho_eq_of_identDistrib h₁.symm, h₁.rdist_congr_right hX₁.aemeasurable]
  have :
    condRho X₂ (X₂ + X₂') A volume ≤
      (rho X₂ A volume + rho X₂ A volume + rdist X₂ X₂ volume volume) / 2 :=
    by
    refine
      (condRho_of_sum_le hX₂ hX₂' hA
            (by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide))).trans_eq
        ?_
    rw [rho_eq_of_identDistrib h₂.symm, h₂.rdist_congr_right hX₂.aemeasurable]
  have : I₂ ≤ η * (rdist X₁ X₁ volume volume + rdist X₂ X₂ volume volume) := by nlinarith
  rw [rdist_add_rdist_eq h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂'] at this
  have one_eta : 0 < 1 - η := by linarith
  apply (mul_le_mul_iff_of_pos_left one_eta).1
  have : (1 - η) * I₂ ≤ 2 * η * k - I₁ * η := by linarith
  apply this.trans_eq
  field_simp
  ring
    /- ****************************************
    End Game
    ******************************************* -/


-- @@ L1441-1480 expanded
include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
$$d[X_1;X_2]\le 3\bbI[T_1:T_2\mid T_3] + (2\bbH[T_3]-\bbH[T_1]-\bbH[T_2])
  + \eta(\rho(T_1|T_3)+\rho(T_2|T_3)-\rho(X_1)-\rho(X_2)).$$ -/
lemma dist_le_of_sum_zero {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    [IsProbabilityMeasure μ] {T₁ T₂ T₃ : Ω' → G} (hsum : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁)
    (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) :
    k ≤
      3 * mutualInfo T₁ T₂ μ + (2 * entropy T₃ μ - entropy T₁ μ - entropy T₂ μ) +
        η * (condRho T₁ T₃ A μ + condRho T₂ T₃ A μ - rho X₁ A volume - rho X₂ A volume) :=
  by
  cases nonempty_fintype G
  let : MeasureSpace Ω' := ⟨μ⟩
  have : μ = ℙ := rfl
  simp only [this]
  have :
    ∑ t, (Measure.real ℙ (T₃ ⁻¹' { t })) * rdist X₁ X₂ volume volume ≤
      ∑ t,
        (Measure.real ℙ (T₃ ⁻¹' { t })) *
          (rdist T₁ T₂ ℙ[|T₃ ← t] ℙ[|T₃ ← t] + η * (rho T₁ A ℙ[|T₃ ← t] - rho X₁ A volume) +
            η * (rho T₂ A ℙ[|T₃ ← t] - rho X₂ A volume)) :=
    by
    apply Finset.sum_le_sum (fun t ht ↦ ?_)
    rcases eq_or_ne (Measure.real ℙ (T₃ ⁻¹' { t })) 0 with h't | h't
    · simp [h't]
    have : IsProbabilityMeasure (ℙ[|T₃ ← t]) := cond_isProbabilityMeasure_of_real h't
    gcongr
    exact le_rdist_of_phiMinimizes' h_min hT₁ hT₂
  have :
    k ≤
      ∑ x : G, (Measure.real ℙ (T₃ ⁻¹' { x })) * rdist T₁ T₂ ℙ[|T₃ ← x] ℙ[|T₃ ← x] +
          η * (condRho T₁ T₃ A volume - rho X₁ A volume) +
        η * (condRho T₂ T₃ A volume - rho X₂ A volume) :=
    by
    have S : ∑ i : G, (Measure.real ℙ (T₃ ⁻¹' { i })) = 1 := by
      simp [← map_measureReal_apply hT₃ (measurableSet_singleton _)]
    simp_rw [← Finset.sum_mul, S, mul_add, Finset.sum_add_distrib, ← mul_assoc, mul_comm _ η,
      mul_assoc, ← Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_sub, ← Finset.sum_mul,
      S] at this
    simpa [mul_sub, condRho, tsum_fintype] using this
  have J :
    ∑ x : G, (Measure.real ℙ (T₃ ⁻¹' { x })) * rdist T₁ T₂ ℙ[|T₃ ← x] ℙ[|T₃ ← x] ≤
      3 * mutualInfo T₁ T₂ volume + 2 * entropy T₃ volume - entropy T₁ volume - entropy T₂ volume :=
    by
    have h2T₃ : T₃ = T₁ + T₂ :=
      calc
        T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hsum, _root_.zero_sub]; simp [ZModModule.neg_eq_self]
        _ = T₁ + T₂ := by rw [add_sub_cancel_right]
    subst h2T₃
    simpa [integral_fintype .of_finite, map_measureReal_apply hT₃ (.singleton _)] using
      ent_bsg hT₁ hT₂ (μ := ℙ)
  linarith


-- @@ L1482-1509 expanded
include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
$$d[X_1;X_2]\le 3\bbI[T_1:T_2\mid T_3] + (2\bbH[T_3]-\bbH[T_1]-\bbH[T_2])+ \eta(\rho(T_1|T_3)
  +\rho(T_2|T_3)-\rho(X_1)-\rho(X_2)).$$ -/
lemma dist_le_of_sum_zero_cond {Ω' : Type*} [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω')] {T₁ T₂ T₃ S : Ω' → G} (hsum : T₁ + T₂ + T₃ = 0)
    (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) (hS : Measurable S) :
    k ≤
      3 * condMutualInfo T₁ T₂ S volume +
          (2 * condEntropy T₃ S volume - condEntropy T₁ S volume - condEntropy T₂ S volume) +
        η *
          (condRho T₁ ⟨T₃, S⟩ A volume + condRho T₂ ⟨T₃, S⟩ A volume - rho X₁ A volume -
            rho X₂ A volume) :=
  by
  cases nonempty_fintype G
  have hw (a : ℝ) : a = ∑ w, (Measure.real ℙ (S ⁻¹' { w })) * a :=
    by
    simp_rw [← Finset.sum_mul, ← map_measureReal_apply hS (MeasurableSet.singleton _),
      sum_measureReal_singleton]
    simp
  rw [condMutualInfo_eq_sum' hS, condEntropy_eq_sum_fintype _ _ _ hS,
    condEntropy_eq_sum_fintype _ _ _ hS, condEntropy_eq_sum_fintype _ _ _ hS,
    condRho_prod_eq_sum hT₃ hS, condRho_prod_eq_sum hT₃ hS, hw k, hw (rho X₁ A volume),
    hw (rho X₂ A volume)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, mul_sub, mul_add]
  gcongr with g hg
  rcases eq_or_ne (Measure.real ℙ (S ⁻¹' { g })) 0 with hpg | hpg
  · simp [hpg]
  set μ := ℙ[|S ← g]
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_real hpg
  have := dist_le_of_sum_zero (μ := μ) h_min hsum hT₁ hT₂ hT₃
  have := mul_le_mul_of_nonneg_left this (show 0 ≤ (Measure.real ℙ (S ⁻¹' { g })) by simp)
  linarith


-- @@ L1511-1529 expanded
include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2] \leq \sum_{1 \leq i < j \leq 3} \bbI[T_i:T_j]
  + \frac{\eta}{3} \sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j) + \rho(T_j|T_i) -\rho(X_1)-\rho(X_2))$$
-/
lemma dist_le_of_sum_zero' {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
    {T₁ T₂ T₃ : Ω' → G} (hsum : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂)
    (hT₃ : Measurable T₃) :
    k ≤
      mutualInfo T₁ T₂ volume + mutualInfo T₁ T₃ volume + mutualInfo T₂ T₃ volume +
        (η / 3) *
          ((condRho T₁ T₂ A volume + condRho T₂ T₁ A volume - rho X₁ A volume - rho X₂ A volume) +
              (condRho T₁ T₃ A volume + condRho T₃ T₁ A volume - rho X₁ A volume -
                rho X₂ A volume) +
            (condRho T₂ T₃ A volume + condRho T₃ T₂ A volume - rho X₁ A volume -
              rho X₂ A volume)) :=
  by
  have := dist_le_of_sum_zero h_min hsum hT₁ hT₂ hT₃ (μ := ℙ)
  have : T₁ + T₃ + T₂ = 0 := by convert hsum using 1; abel
  have := dist_le_of_sum_zero h_min this hT₁ hT₃ hT₂ (μ := ℙ)
  have : T₂ + T₃ + T₁ = 0 := by convert hsum using 1; abel
  have := dist_le_of_sum_zero h_min this hT₂ hT₃ hT₁ (μ := ℙ)
  linarith


-- @@ L1531-1550 expanded
include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2] \leq \sum_{1 \leq i < j \leq 3} \bbI[T_i:T_j]
  + \frac{\eta}{3} \sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j) + \rho(T_j|T_i) -\rho(X_1)-\rho(X_2))$$
-/
lemma dist_le_of_sum_zero_cond' {Ω' : Type*} [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω')] {T₁ T₂ T₃ : Ω' → G} (S : Ω' → G)
    (hsum : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)
    (hS : Measurable S) :
    k ≤
      condMutualInfo T₁ T₂ S volume + condMutualInfo T₁ T₃ S volume +
          condMutualInfo T₂ T₃ S volume +
        (η / 3) *
          ((condRho T₁ ⟨T₂, S⟩ A volume + condRho T₂ ⟨T₁, S⟩ A volume - rho X₁ A volume -
                rho X₂ A volume) +
              (condRho T₁ ⟨T₃, S⟩ A volume + condRho T₃ ⟨T₁, S⟩ A volume - rho X₁ A volume -
                rho X₂ A volume) +
            (condRho T₂ ⟨T₃, S⟩ A volume + condRho T₃ ⟨T₂, S⟩ A volume - rho X₁ A volume -
              rho X₂ A volume)) :=
  by
  have := dist_le_of_sum_zero_cond h_min hsum hT₁ hT₂ hT₃ hS
  have : T₁ + T₃ + T₂ = 0 := by convert hsum using 1; abel
  have := dist_le_of_sum_zero_cond h_min this hT₁ hT₃ hT₂ hS
  have : T₂ + T₃ + T₁ = 0 := by convert hsum using 1; abel
  have := dist_le_of_sum_zero_cond h_min this hT₂ hT₃ hT₁ hS
  linarith


-- @@ L1552-1577 expanded
lemma new_gen_ineq_aux1 {Y₁ Y₂ Y₃ Y₄ : Ω → G} (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂)
    (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄) (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄])
    (hA : A.Nonempty) :
    condRho (Y₁ + Y₂) ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ A volume ≤
      (rho Y₁ A volume + rho Y₂ A volume + rho Y₃ A volume + rho Y₄ A volume) / 4 +
          (rdist Y₁ Y₂ volume volume + rdist Y₃ Y₄ volume volume) / 4 +
        (rdist (Y₁ + Y₂) (Y₃ + Y₄) volume volume +
            condMutualInfo (Y₁ + Y₂) (Y₁ + Y₃) (Y₁ + Y₂ + Y₃ + Y₄) volume) /
          2 :=
  by
  set S := Y₁ + Y₂ + Y₃ + Y₄
  set T₁ := Y₁ + Y₂
  set T₂ := Y₁ + Y₃
  set T₁' := Y₃ + Y₄
  set T₂' := Y₂ + Y₄
  have : condRho T₁ ⟨T₂, S⟩ A volume ≤ condRho T₁ S A volume + condMutualInfo T₁ T₂ S volume / 2 :=
    by
    rw [condMutualInfo_eq' (by fun_prop) (by fun_prop) (by fun_prop)]
    exact condRho_prod_le (by fun_prop) (by fun_prop) (by fun_prop) hA
  have :
    condRho T₁ S A volume ≤ (rho T₁ A volume + rho T₁' A volume + rdist T₁ T₁' volume volume) / 2 :=
    by
    have S_eq : S = T₁ + T₁' := by simp only [S, T₁, T₁']; abel
    rw [S_eq]
    apply condRho_of_sum_le (by fun_prop) (by fun_prop) hA
    exact
      h_indep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption) 0 1 2 3
        (by decide) (by decide) (by decide) (by decide)
  have : rho T₁ A volume ≤ (rho Y₁ A volume + rho Y₂ A volume + rdist Y₁ Y₂ volume volume) / 2 :=
    rho_of_sum_le hY₁ hY₂ hA (h_indep.indepFun (i := 0) (j := 1) (by decide))
  have : rho T₁' A volume ≤ (rho Y₃ A volume + rho Y₄ A volume + rdist Y₃ Y₄ volume volume) / 2 :=
    rho_of_sum_le hY₃ hY₄ hA (h_indep.indepFun (i := 2) (j := 3) (by decide))
  linarith


-- @@ L1579-1678 expanded
lemma new_gen_ineq_aux2 {Y₁ Y₂ Y₃ Y₄ : Ω → G} (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂)
    (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄) (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄])
    (hA : A.Nonempty) :
    condRho (Y₁ + Y₂) ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ A volume ≤
      (rho Y₁ A volume + rho Y₂ A volume + rho Y₃ A volume + rho Y₄ A volume) / 4 +
          (rdist Y₁ Y₃ volume volume + rdist Y₂ Y₄ volume volume) / 4 +
        condRuzsaDist Y₁ (Y₁ + Y₃) Y₂ (Y₂ + Y₄) volume volume / 2 :=
  by
  cases nonempty_fintype G
  set S := Y₁ + Y₂ + Y₃ + Y₄
  set T₁ := Y₁ + Y₂
  set T₂ := Y₁ + Y₃
  set T₁' := Y₃ + Y₄
  set T₂' := Y₂ + Y₄
  have I : IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩) :=
    by
    refine
      (h_indep.indepFun_prodMk_prodMk ?_ 0 2 1 3 (by decide) (by decide) (by decide) (by decide))
    intro i; fin_cases i <;> assumption
  calc
    condRho (Y₁ + Y₂) ⟨T₂, S⟩ A volume = condRho (Y₁ + Y₂) ⟨T₂, T₂'⟩ A volume :=
      by
      have : S = T₂ + T₂' := by simp only [S, T₂, T₂']; abel
      rw [this]
      let e : G × G ≃ G × G :=
        { toFun p := ⟨p.1, p.1 + p.2⟩
          invFun p := ⟨p.1, p.2 - p.1⟩
          left_inv := by intro ⟨a, b⟩; simp
          right_inv := by intro ⟨a, b⟩; simp }
      exact condRho_of_injective T₁ (⟨T₂, T₂'⟩) (f := e) (A := A) e.injective
    _ = ∑ w, (Measure.real ℙ (⟨T₂, T₂'⟩ ⁻¹' { w })) * rho (Y₁ + Y₂) A ℙ[|⟨T₂, T₂'⟩ ← w] := by
      rw [condRho, tsum_fintype]
    _ ≤
        ∑ w,
          (Measure.real ℙ (⟨T₂, T₂'⟩ ⁻¹' { w })) *
            ((rho Y₁ A ℙ[|⟨T₂, T₂'⟩ ← w] + rho Y₂ A ℙ[|⟨T₂, T₂'⟩ ← w] +
                rdist Y₁ Y₂ ℙ[|⟨T₂, T₂'⟩ ← w] ℙ[|⟨T₂, T₂'⟩ ← w]) /
              2) :=
      by
      gcongr with w hw
      have : IndepFun Y₁ Y₂ (ℙ[|⟨T₂, T₂'⟩ ⁻¹' { w }]) :=
        by
        have E :
          (⟨Y₁, Y₃⟩) ⁻¹' {p | p.1 + p.2 = w.1} ∩ (⟨Y₂, Y₄⟩) ⁻¹' {p | p.1 + p.2 = w.2} =
            ⟨T₂, T₂'⟩ ⁻¹' { w } :=
          by aesop
        have I :
          IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩)
            (ℙ[|(⟨Y₁, Y₃⟩) ⁻¹' {p | p.1 + p.2 = w.1} ∩ (⟨Y₂, Y₄⟩) ⁻¹' {p | p.1 + p.2 = w.2}]) :=
          I.cond (measurable_add (.singleton w.1)) (measurable_add (.singleton w.2))
            (hY₁.prodMk hY₃) (hY₂.prodMk hY₄)
        rw [E] at I
        exact I.comp measurable_fst measurable_fst
      exact rho_of_sum_le hY₁ hY₂ hA this
    _ =
        (condRho Y₁ ⟨T₂, T₂'⟩ A volume + condRho Y₂ ⟨T₂, T₂'⟩ A volume +
            condRuzsaDist Y₁ T₂ Y₂ T₂' volume volume) /
          2 :=
      by
      simp_rw [← mul_div_assoc, ← Finset.sum_div, mul_add, Finset.sum_add_distrib, condRho,
        tsum_fintype]
      congr
      rw [condRuzsaDist_eq_sum' hY₁ (by fun_prop) hY₂ (by fun_prop), Fintype.sum_prod_type]
      congr with x
      congr with y
      have : (⟨T₂, T₂'⟩) ⁻¹' {(x, y)} = (Y₁ + Y₃) ⁻¹' { x } ∩ (Y₂ + Y₄) ⁻¹' { y } := by ext p;
        simp [T₂, T₂']
      rw [this]
      have J : IndepFun (Y₁ + Y₃) (Y₂ + Y₄) := by exact I.comp measurable_add measurable_add
      rw [J.measureReal_inter_preimage_eq_mul (.singleton x) (.singleton y)]
      rcases eq_or_ne (Measure.real ℙ ((Y₁ + Y₃) ⁻¹' { x })) 0 with h1 | h1
      · simp [h1, T₂]
      rcases eq_or_ne (Measure.real ℙ ((Y₂ + Y₄) ⁻¹' { y })) 0 with h2 | h2
      · simp [h2, T₂']
      congr 1
      have A :
        IdentDistrib Y₁ Y₁ (ℙ[|(Y₁ + Y₃) ⁻¹' { x } ∩ (Y₂ + Y₄) ⁻¹' { y }])
          (ℙ[|(Y₁ + Y₃) ⁻¹' { x }]) :=
        by
        rw [←
          cond_cond_eq_cond_inter' (by exact hY₁.add hY₃ (.singleton _))
            (by exact hY₂.add hY₄ (.singleton _)) (by finiteness)]
        have : IsProbabilityMeasure (ℙ[|(Y₁ + Y₃) ⁻¹' { x }]) :=
          cond_isProbabilityMeasure_of_real h1
        apply (IndepFun.identDistrib_cond _ (.singleton _) hY₁ (by fun_prop) _).symm
        · have : IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩) (ℙ[|(⟨Y₁, Y₃⟩) ⁻¹' {p | p.1 + p.2 = x}]) :=
            I.cond_left (measurable_add (.singleton x)) (hY₁.prodMk hY₃)
          exact this.comp measurable_fst measurable_add
        · rw [cond_apply, J.measure_inter_preimage_eq_mul _ _ (.singleton x) (.singleton y)]
          · simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h1 h2
            simp [h1, h2]
          · exact hY₁.add hY₃ (.singleton _)
      refine A.rdist_congr ?_
      rw [Set.inter_comm, ←
        cond_cond_eq_cond_inter' (by exact hY₂.add hY₄ (.singleton _))
          (by exact hY₁.add hY₃ (.singleton _)) (by finiteness)]
      have : IsProbabilityMeasure (ℙ[|(Y₂ + Y₄) ⁻¹' { y }]) := cond_isProbabilityMeasure_of_real h2
      apply (IndepFun.identDistrib_cond _ (.singleton _) hY₂ (hY₁.add hY₃) _).symm
      · have : IndepFun (⟨Y₂, Y₄⟩) (⟨Y₁, Y₃⟩) (ℙ[|(⟨Y₂, Y₄⟩) ⁻¹' {p | p.1 + p.2 = y}]) :=
          I.symm.cond_left (measurable_add (.singleton y)) (hY₂.prodMk hY₄)
        exact this.comp measurable_fst measurable_add
      · rw [cond_apply (hY₂.add hY₄ (.singleton y)),
          J.symm.measure_inter_preimage_eq_mul _ _ (.singleton _) (.singleton _)]
        simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h1 h2
        simp [h1, h2]
    _ =
        (condRho Y₁ T₂ A volume + condRho Y₂ T₂' A volume +
            condRuzsaDist Y₁ T₂ Y₂ T₂' volume volume) /
          2 :=
      by
      congr 3
      · apply condRho_prod_eq_of_indepFun hY₁ (by fun_prop) (by fun_prop)
        exact I.comp (measurable_fst.prodMk measurable_add) measurable_add
      · have : condRho Y₂ ⟨T₂, T₂'⟩ A volume = condRho Y₂ ⟨T₂', T₂⟩ A volume :=
          condRho_of_injective Y₂ (⟨T₂', T₂⟩) (f := Prod.swap) Prod.swap_injective
        rw [this]
        apply condRho_prod_eq_of_indepFun hY₂ (by fun_prop) (by fun_prop)
        exact I.symm.comp (measurable_fst.prodMk measurable_add) measurable_add
    _ ≤
        ((rho Y₁ A volume + rho Y₃ A volume + rdist Y₁ Y₃ volume volume) / 2 +
              (rho Y₂ A volume + rho Y₄ A volume + rdist Y₂ Y₄ volume volume) / 2 +
            condRuzsaDist Y₁ T₂ Y₂ T₂' volume volume) /
          2 :=
      by
      gcongr
      · exact condRho_of_sum_le hY₁ hY₃ hA (h_indep.indepFun (i := 0) (j := 2) (by decide))
      · exact condRho_of_sum_le hY₂ hY₄ hA (h_indep.indepFun (i := 1) (j := 3) (by decide))
    _ =
        (rho Y₁ A volume + rho Y₂ A volume + rho Y₃ A volume + rho Y₄ A volume) / 4 +
            (rdist Y₁ Y₃ volume volume + rdist Y₂ Y₄ volume volume) / 4 +
          condRuzsaDist Y₁ (Y₁ + Y₃) Y₂ (Y₂ + Y₄) volume volume / 2 :=
      by ring


-- @@ L1680-1689 expanded
lemma new_gen_ineq {Y₁ Y₂ Y₃ Y₄ : Ω → G} (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂)
    (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄) (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄])
    (hA : A.Nonempty) :
    condRho (Y₁ + Y₂) ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ A volume ≤
      (rho Y₁ A volume + rho Y₂ A volume + rho Y₃ A volume + rho Y₄ A volume) / 4 +
          (rdist Y₁ Y₂ volume volume + rdist Y₃ Y₄ volume volume + rdist Y₁ Y₃ volume volume +
              rdist Y₂ Y₄ volume volume) /
            8 +
        (rdist (Y₁ + Y₂) (Y₃ + Y₄) volume volume +
              condMutualInfo (Y₁ + Y₂) (Y₁ + Y₃) (Y₁ + Y₂ + Y₃ + Y₄) volume +
            condRuzsaDist Y₁ (Y₁ + Y₃) Y₂ (Y₂ + Y₄) volume volume) /
          4 :=
  by
  have := new_gen_ineq_aux1 hY₁ hY₂ hY₃ hY₄ h_indep hA
  have := new_gen_ineq_aux2 hY₁ hY₂ hY₃ hY₄ h_indep hA
  linarith


-- @@ L1691-1744 expanded
/-- For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define
$S:=Y_1+Y_2+Y_3+Y_4$, $T_1:=Y_1+Y_2$, $T_2:=Y_1+Y_3$. Then
  $$\rho(T_1|T_2,S)+\rho(T_2|T_1,S) - \frac{1}{2}\sum_{i} \rho(Y_i)
    \le \frac{1}{2}(d[Y_1;Y_2]+d[Y_3;Y_4]+d[Y_1;Y_3]+d[Y_2;Y_4]).$$
-/
lemma condRho_sum_le {Y₁ Y₂ Y₃ Y₄ : Ω → G} (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂)
    (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄) (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄])
    (hA : A.Nonempty) :
    condRho (Y₁ + Y₂) ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ A volume +
          condRho (Y₁ + Y₃) ⟨Y₁ + Y₂, Y₁ + Y₂ + Y₃ + Y₄⟩ A volume -
        (rho Y₁ A volume + rho Y₂ A volume + rho Y₃ A volume + rho Y₄ A volume) / 2 ≤
      (rdist Y₁ Y₂ volume volume + rdist Y₃ Y₄ volume volume + rdist Y₁ Y₃ volume volume +
          rdist Y₂ Y₄ volume volume) /
        2 :=
  by
  set S := Y₁ + Y₂ + Y₃ + Y₄
  set T₁ := Y₁ + Y₂
  set T₂ := Y₁ + Y₃
  set T₁' := Y₃ + Y₄
  set T₂' := Y₂ + Y₄
  have J :
    condRho T₁ ⟨T₂, S⟩ A volume ≤
      (rho Y₁ A volume + rho Y₂ A volume + rho Y₃ A volume + rho Y₄ A volume) / 4 +
          (rdist Y₁ Y₂ volume volume + rdist Y₃ Y₄ volume volume + rdist Y₁ Y₃ volume volume +
              rdist Y₂ Y₄ volume volume) /
            8 +
        (rdist (Y₁ + Y₂) (Y₃ + Y₄) volume volume +
              condMutualInfo (Y₁ + Y₂) (Y₁ + Y₃) (Y₁ + Y₂ + Y₃ + Y₄) volume +
            condRuzsaDist Y₁ (Y₁ + Y₃) Y₂ (Y₂ + Y₄) volume volume) /
          4 :=
    new_gen_ineq hY₁ hY₂ hY₃ hY₄ h_indep hA
  have J' :
    condRho T₂ ⟨T₁, Y₁ + Y₃ + Y₂ + Y₄⟩ A volume ≤
      (rho Y₁ A volume + rho Y₃ A volume + rho Y₂ A volume + rho Y₄ A volume) / 4 +
          (rdist Y₁ Y₃ volume volume + rdist Y₂ Y₄ volume volume + rdist Y₁ Y₂ volume volume +
              rdist Y₃ Y₄ volume volume) /
            8 +
        (rdist (Y₁ + Y₃) (Y₂ + Y₄) volume volume +
              condMutualInfo (Y₁ + Y₃) (Y₁ + Y₂) (Y₁ + Y₃ + Y₂ + Y₄) volume +
            condRuzsaDist Y₁ (Y₁ + Y₂) Y₃ (Y₃ + Y₄) volume volume) /
          4 :=
    new_gen_ineq hY₁ hY₃ hY₂ hY₄ h_indep.reindex_four_acbd hA
  have : Y₁ + Y₃ + Y₂ + Y₄ = S := by simp only [S]; abel
  rw [this] at J'
  have :
    rdist (Y₁ + Y₂) (Y₃ + Y₄) volume volume +
                condMutualInfo (Y₁ + Y₂) (Y₁ + Y₃) (Y₁ + Y₂ + Y₃ + Y₄) volume +
              condRuzsaDist Y₁ (Y₁ + Y₃) Y₂ (Y₂ + Y₄) volume volume +
            rdist (Y₁ + Y₃) (Y₂ + Y₄) volume volume +
          condMutualInfo (Y₁ + Y₃) (Y₁ + Y₂) S volume +
        condRuzsaDist Y₁ (Y₁ + Y₂) Y₃ (Y₃ + Y₄) volume volume =
      (rdist Y₁ Y₂ volume volume + rdist Y₃ Y₄ volume volume) +
        (rdist Y₁ Y₃ volume volume + rdist Y₂ Y₄ volume volume) :=
    by
    have K : Y₁ + Y₃ + Y₂ + Y₄ = S := by simp only [S]; abel
    have K' :
      condMutualInfo (Y₁ + Y₃) (Y₁ + Y₂) (Y₁ + Y₂ + Y₃ + Y₄) volume =
        condMutualInfo (Y₁ + Y₃) (Y₃ + Y₄) (Y₁ + Y₂ + Y₃ + Y₄) volume :=
      by
      have : Measurable (Y₁ + Y₃) := by fun_prop
      rw [condMutualInfo_comm this (by fun_prop), condMutualInfo_comm this (by fun_prop)]
      have B :=
        condMutualInfo_of_inj_map (X := Y₃ + Y₄) (Y := Y₁ + Y₃) (Z := Y₁ + Y₂ + Y₃ + Y₄)
          (by fun_prop) (by fun_prop) (by fun_prop) (fun a b ↦ a - b) (fun a ↦ sub_right_injective)
          (μ := ℙ)
      convert B with g
      simp
    have K'' :
      condMutualInfo (Y₁ + Y₂) (Y₁ + Y₃) (Y₁ + Y₂ + Y₃ + Y₄) volume =
        condMutualInfo (Y₁ + Y₂) (Y₂ + Y₄) (Y₁ + Y₂ + Y₃ + Y₄) volume :=
      by
      have : Measurable (Y₁ + Y₂) := by fun_prop
      rw [condMutualInfo_comm this (by fun_prop), condMutualInfo_comm this (by fun_prop)]
      have B :=
        condMutualInfo_of_inj_map (X := Y₂ + Y₄) (Y := Y₁ + Y₂) (Z := Y₁ + Y₂ + Y₃ + Y₄)
          (by fun_prop) (by fun_prop) (by fun_prop) (fun a b ↦ a - b) (fun a ↦ sub_right_injective)
          (μ := ℙ)
      convert B with g
      simp
      abel
    rw [sum_of_rdist_eq_char_2' Y₁ Y₂ Y₃ Y₄ h_indep hY₁ hY₂ hY₃ hY₄,
      sum_of_rdist_eq_char_2' Y₁ Y₃ Y₂ Y₄ h_indep.reindex_four_acbd hY₁ hY₃ hY₂ hY₄, K, K', K'']
    abel
  linarith


-- @@ L1746-1773 expanded
/-- For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define
$T_1:=Y_1+Y_2, T_2:=Y_1+Y_3, T_3:=Y_2+Y_3$ and $S:=Y_1+Y_2+Y_3+Y_4$. Then
  $$\sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j,S) + \rho(T_j|T_i,S)
    - \frac{1}{2}\sum_{i} \rho(Y_i))\le \sum_{1\leq i < j \leq 4}d[Y_i;Y_j]$$ -/
lemma condRho_sum_le' {Y₁ Y₂ Y₃ Y₄ : Ω → G} (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂)
    (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄) (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄])
    (hA : A.Nonempty) :
    let S := Y₁ + Y₂ + Y₃ + Y₄
    let T₁ := Y₁ + Y₂
    let T₂ := Y₁ + Y₃
    let T₃ := Y₂ + Y₃
    condRho T₁ ⟨T₂, S⟩ A volume + condRho T₂ ⟨T₁, S⟩ A volume + condRho T₁ ⟨T₃, S⟩ A volume +
              condRho T₃ ⟨T₁, S⟩ A volume +
            condRho T₂ ⟨T₃, S⟩ A volume +
          condRho T₃ ⟨T₂, S⟩ A volume -
        3 * (rho Y₁ A volume + rho Y₂ A volume + rho Y₃ A volume + rho Y₄ A volume) / 2 ≤
      rdist Y₁ Y₂ volume volume + rdist Y₁ Y₃ volume volume + rdist Y₁ Y₄ volume volume +
            rdist Y₂ Y₃ volume volume +
          rdist Y₂ Y₄ volume volume +
        rdist Y₃ Y₄ volume volume :=
  by
  have K₁ := condRho_sum_le hY₁ hY₂ hY₃ hY₄ h_indep hA
  have K₂ := condRho_sum_le hY₂ hY₁ hY₃ hY₄ h_indep.reindex_four_bacd hA
  have Y₂₁ : Y₂ + Y₁ = Y₁ + Y₂ := by abel
  have dY₂₁ : rdist Y₂ Y₁ volume volume = rdist Y₁ Y₂ volume volume := rdist_symm
  rw [Y₂₁, dY₂₁] at K₂
  have K₃ := condRho_sum_le hY₃ hY₁ hY₂ hY₄ h_indep.reindex_four_cabd hA
  have Y₃₁ : Y₃ + Y₁ = Y₁ + Y₃ := by abel
  have Y₃₂ : Y₃ + Y₂ = Y₂ + Y₃ := by abel
  have S₃ : Y₁ + Y₃ + Y₂ + Y₄ = Y₁ + Y₂ + Y₃ + Y₄ := by abel
  have dY₃₁ : rdist Y₃ Y₁ volume volume = rdist Y₁ Y₃ volume volume := rdist_symm
  have dY₃₂ : rdist Y₃ Y₂ volume volume = rdist Y₂ Y₃ volume volume := rdist_symm
  rw [Y₃₁, Y₃₂, S₃, dY₃₁, dY₃₂] at K₃
  linarith


-- @@ L1775-1839 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min hη in
/-- If $X_1, X_2$ is a $\phi$-minimizer, then $d[X_1;X_2] = 0$. -/
lemma dist_of_min_eq_zero' (hA : A.Nonempty) (hη' : η < 1 / 8) : rdist X₁ X₂ volume volume = 0 :=
  by
  let T₁ := X₁ + X₂
  let T₂ := X₁ + X₁'
  let T₃ := X₁' + X₂
  have hsum : T₁ + T₂ + T₃ = 0 :=
    by
    have : T₁ + T₂ + T₃ = 2 • (X₁ + X₁' + X₂) := by simp only [T₁, T₂, T₃]; abel
    rwa [ZModModule.char_nsmul_eq_zero 2 (X₁ + X₁' + X₂)] at this
  let S := X₁ + X₂ + X₁' + X₂'
  have J₁ :
    k ≤
      I₁ + 2 * I₂ +
        η / 3 *
          (condRho T₁ ⟨T₂, S⟩ A volume + condRho T₂ ⟨T₁, S⟩ A volume + condRho T₁ ⟨T₃, S⟩ A volume +
                  condRho T₃ ⟨T₁, S⟩ A volume +
                condRho T₂ ⟨T₃, S⟩ A volume +
              condRho T₃ ⟨T₂, S⟩ A volume -
            3 * (rho X₁ A volume + rho X₂ A volume)) :=
    by
    have K :=
      dist_le_of_sum_zero_cond' h_min S hsum (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    have : condMutualInfo T₂ T₃ S volume = I₂ :=
      by
      rw [condMutualInfo_comm (by fun_prop) (by fun_prop)]
      have : X₁ + X₁' = X₁' + X₁ := by abel
      convert I₃_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h_indep using 2
    linarith
  have J₂ :
    k ≤
      I₁ + 2 * I₂ +
        η / 3 *
          (k + rdist X₁ X₁' volume volume + rdist X₁ X₂' volume volume +
                rdist X₂ X₁' volume volume +
              rdist X₂ X₂' volume volume +
            rdist X₁' X₂' volume volume) :=
    by
    apply J₁.trans
    gcongr
    have W : X₂ + X₁' = X₁' + X₂ := by abel
    have := condRho_sum_le' hX₁ hX₂ hX₁' hX₂' h_indep hA
    simp only [W] at this
    have : rho X₁' A volume = rho X₁ A volume := rho_eq_of_identDistrib h₁.symm
    have : rho X₂' A volume = rho X₂ A volume := rho_eq_of_identDistrib h₂.symm
    linarith
  have J₃ : k ≤ I₁ + 2 * I₂ + η / 3 * (6 * k + I₂ - I₁) :=
    by
    apply J₂.trans_eq
    congr 2
    have : rdist X₁ X₁' volume volume = rdist X₁ X₁ volume volume :=
      h₁.symm.rdist_congr_right hX₁.aemeasurable
    have : rdist X₁ X₂' volume volume = rdist X₁ X₂ volume volume :=
      h₂.symm.rdist_congr_right hX₁.aemeasurable
    have : rdist X₂ X₁' volume volume = rdist X₁ X₂ volume volume := by rw [rdist_symm];
      exact h₁.symm.rdist_congr_left hX₂.aemeasurable
    have : rdist X₂ X₂' volume volume = rdist X₂ X₂ volume volume :=
      h₂.symm.rdist_congr_right hX₂.aemeasurable
    have : rdist X₁' X₂' volume volume = rdist X₁ X₂ volume volume := h₁.symm.rdist_congr h₂.symm
    have := rdist_add_rdist_eq h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂'
    linarith
  let D := 2 * η * k - I₁
  have J₄ : k ≤ 8 * η * k - (3 - 10 * η) / (3 * (1 - η)) * D :=
    by
    have I₁_eq : I₁ = 2 * η * k - D := by simp only [D]; abel
    have : I₂ ≤ 2 * η * k + η / (1 - η) * D :=
      I_two_le hη h_min h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂' hA (by linarith)
    calc
      k ≤ I₁ + 2 * I₂ + η / 3 * (6 * k + I₂ - I₁) := J₃
      _ = 2 * η * k + I₁ + 2 * I₂ + η / 3 * (I₂ - I₁) := by ring
      _ ≤
          2 * η * k + (2 * η * k - D) + 2 * (2 * η * k + η / (1 - η) * D) +
            η / 3 * ((2 * η * k + η / (1 - η) * D) - (2 * η * k - D)) :=
        by
        rw [I₁_eq]
        gcongr
      _ = 8 * η * k - (3 - 10 * η) / (3 * (1 - η)) * D :=
        by
        have : 1 - η ≠ 0 := ne_of_gt (by linarith)
        field_simp
        ring
  have J₅ : k ≤ 8 * η * k - 0 := by
    apply J₄.trans
    gcongr
    have : 0 ≤ D := sub_nonneg_of_le (I_one_le hη h_min h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂' hA)
    apply mul_nonneg _ this
    exact div_nonneg (by linarith) (by linarith)
  have : k ≤ 0 := by nlinarith
  exact le_antisymm this (rdist_nonneg hX₁ hX₂)


-- @@ L1841-1850 expanded
include hX₁ hX₂ h_min hη in
theorem dist_of_min_eq_zero (hA : A.Nonempty) (hη' : η < 1 / 8) : rdist X₁ X₂ volume volume = 0 :=
  by
  let
    ⟨Ω', m', μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1',
      h_id2'⟩ :=
    independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_congr h_id2]
  let : MeasureSpace Ω' := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure Ω') := hμ
  have h'_min : phiMinimizes Y₁ Y₂ η A ℙ := phiMinimizes_of_identDistrib h_min h_id1.symm h_id2.symm
  exact
    dist_of_min_eq_zero' hη h'_min (h_id1.trans h_id1'.symm) (h_id2.trans h_id2'.symm) h_indep hY₁
      hY₂ hY₁' hY₂' hA hη'


-- @@ L1852-1852 verbatim
open Filter

-- @@ L1853-1853 verbatim
open scoped Topology


-- @@ L1855-1907 expanded
/-- For `η ≤ 1/8`, there exist phi-minimizers `X₁, X₂` at zero Rusza distance. For `η < 1/8`,
all minimizers are fine, by `dist_of_min_eq_zero`. For `η = 1/8`, we use a limit of
minimizers for `η < 1/8`, which exists by compactness. -/
lemma phiMinimizer_exists_rdist_eq_zero (hA : A.Nonempty) :
    ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
      Measurable X₁ ∧
        Measurable X₂ ∧
          IsProbabilityMeasure (ℙ : Measure Ω) ∧
            phiMinimizes X₁ X₂ (1 / 8 : ℝ) A ℙ ∧ rdist X₁ X₂ volume volume = 0 :=
  by
  -- let `uₙ` be a sequence converging from below to `η`. In particular, `uₙ < 1/8`.
  
  obtain ⟨u, -, u_mem, u_lim⟩ :
    ∃ u, StrictMono u ∧ (∀ (n : ℕ), u n ∈ Set.Ioo 0 (1 / 8 : ℝ)) ∧ Tendsto u atTop (𝓝 (1 / 8)) :=
    exists_seq_strictMono_tendsto'
      (by norm_num)
        -- For each `n`, consider a minimizer associated to `η = uₙ`.
        
  have :
    ∀ n,
      ∃ (μ : Measure (G × G)), IsProbabilityMeasure μ ∧ phiMinimizes Prod.fst Prod.snd (u n) A μ :=
    fun n ↦ phi_min_exists hA
  choose μ μ_prob hμ using this
  let μ' : ℕ → ProbabilityMeasure (G × G) := fun n ↦ ⟨μ n, μ_prob n⟩
  let : TopologicalSpace G := (⊥ : TopologicalSpace G)
  have : DiscreteTopology G :=
    ⟨rfl⟩
      -- The limiting pair of measures will be the desired minimizer.
      
  rcases IsCompact.tendsto_subseq (x := μ') isCompact_univ (fun n ↦ mem_univ _) with
    ⟨ν, -, φ, φmono, hν⟩
  have φlim : Tendsto φ atTop atTop := φmono.tendsto_atTop
  let M : MeasureSpace (G × G) := ⟨ν⟩
  have : IsProbabilityMeasure (ℙ : Measure (G × G)) := ν.instIsProbabilityMeasureToMeasure
  refine
    ⟨G × G, M, Prod.fst, Prod.snd, measurable_fst, measurable_snd, by infer_instance, ?_, ?_⟩
      -- check that it is indeed a minimizer, as a limit of minimizers.
      
  · intro Ω' mΩ' X' Y' hP hX' hY'
    have I n : phi Prod.fst Prod.snd (u n) A (μ n) ≤ phi X' Y' (u n) A ℙ := hμ n _ _ _ _ hP hX' hY'
    have L1 :
      Tendsto (fun n ↦ phi Prod.fst Prod.snd (u (φ n)) A (μ (φ n))) atTop
        (𝓝 (phi Prod.fst Prod.snd (1 / 8) A ν)) :=
      by
      apply Tendsto.add
      · apply tendsto_rdist_probabilityMeasure continuous_fst continuous_snd hν
      apply Tendsto.mul (u_lim.comp φlim)
      apply Tendsto.add
      · apply tendsto_rho_probabilityMeasure continuous_fst hA hν
      · apply tendsto_rho_probabilityMeasure continuous_snd hA hν
    have L2 : Tendsto (fun n ↦ phi X' Y' (u (φ n)) A ℙ) atTop (𝓝 (phi X' Y' (1 / 8) A ℙ)) :=
      Tendsto.const_add _ (Tendsto.mul_const _ (u_lim.comp φlim))
    exact
      le_of_tendsto_of_tendsto' L1 L2
        (fun n ↦ I _)
          -- check that it has zero Rusza distance, as a limit of a sequence at zero Rusza distance.
          
  · -- The minimizer associated to `uₙ` is at zero Rusza distance of itself, by
        -- lemma `tau_strictly_decreases'`.
    
    have I0 n : rdist Prod.fst Prod.snd (μ n) (μ n) = 0 :=
      by
      let M : MeasureSpace (G × G) := ⟨μ n⟩
      apply dist_of_min_eq_zero (u_mem n).1 (hμ n) measurable_fst measurable_snd hA (u_mem n).2
    have :
      Tendsto (fun x ↦ rdist Prod.fst Prod.snd (μ (φ x)) (μ (φ x))) atTop
        (𝓝 (rdist (@Prod.fst G G) (@Prod.snd G G) volume volume)) :=
      by apply tendsto_rdist_probabilityMeasure continuous_fst continuous_snd hν
    simp_rw [I0, tendsto_const_nhds_iff] at this
    exact this.symm


-- @@ L1909-1909 verbatim
end phiMinimizer


-- @@ L1911-1911 verbatim
section PFR


-- @@ L1913-1914 verbatim
variable {G : Type uG} [AddCommGroup G] [Finite G] [Module (ZMod 2) G]
  {Ω : Type uG} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {A : Finset G}


-- @@ L1916-1952 expanded
/-- For any random variables $Y_1,Y_2$, there exist a subgroup $H$ such that
  $$ 2\rho(U_H) \leq \rho(Y_1) + \rho(Y_2) + 8 d[Y_1;Y_2].$$ -/
theorem rho_PFR_conjecture [MeasurableSpace G] [DiscreteMeasurableSpace G] (Y₁ Y₂ : Ω → G)
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (A : Finset G) (hA : A.Nonempty) :
    ∃ (H : Submodule (ZMod 2) G) (Ω' : Type uG) (mΩ' : MeasureSpace Ω') (U : Ω' → G),
      IsProbabilityMeasure (ℙ : Measure Ω') ∧
        Measurable U ∧
          IsUniform H U ∧
            2 * rho U A volume ≤
              rho Y₁ A volume + rho Y₂ A volume + 8 * rdist Y₁ Y₂ volume volume :=
  by
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, hP, htau_min, hdist⟩ := phiMinimizer_exists_rdist_eq_zero hA
  wlog h : rho X₁ A volume ≤ rho X₂ A volume generalizing X₁ X₂
  · rw [rdist_symm] at hdist
    exact
      this X₂ X₁ hX₂ hX₁ (phiMinimizes_comm htau_min) hdist
        (by linarith)
          -- use for `U` a translate of `X` to make sure that `0` is in its support.
          
  obtain ⟨x₀, h₀⟩ : ∃ x₀, ℙ (X₁ ⁻¹' { x₀ }) ≠ 0 :=
    by
    by_contra! h
    have A a : (ℙ : Measure Ω').map X₁ { a } = 0 :=
      by
      rw [Measure.map_apply hX₁ .of_discrete]
      exact h _
    refine IsProbabilityMeasure.ne_zero ((ℙ : Measure Ω').map X₁) ?_
    rw [← Measure.sum_smul_dirac (μ := (ℙ : Measure Ω').map X₁)]
    simp [A]
  have h_unif : IsUniform (symmGroup X₁ hX₁) (fun ω ↦ X₁ ω - x₀) :=
    by
    have h' : rdist X₁ X₁ volume volume = 0 :=
      by
      apply le_antisymm _ (rdist_nonneg hX₁ hX₁)
      calc
        rdist X₁ X₁ volume volume ≤ rdist X₁ X₂ volume volume + rdist X₂ X₁ volume volume :=
          rdist_triangle hX₁ hX₂ hX₁
        _ = 0 := by rw [hdist, rdist_symm, hdist, zero_add]
    exact isUniform_sub_const_of_rdist_eq_zero hX₁ h' h₀
  refine
    ⟨AddSubgroup.toZModSubmodule 2 (symmGroup X₁ hX₁), Ω', by infer_instance, fun ω ↦ X₁ ω - x₀, by
      infer_instance, by fun_prop, by exact h_unif, ?_⟩
  have J :
    rdist X₁ X₂ volume volume + (1 / 8) * (rho X₁ A volume + rho X₂ A volume) ≤
      rdist Y₁ Y₂ volume volume + (1 / 8) * (rho Y₁ A volume + rho Y₂ A volume) :=
    by
    have Z := le_rdist_of_phiMinimizes htau_min hY₁ hY₂ (μ₁ := ℙ) (μ₂ := ℙ)
    linarith
  rw [hdist, zero_add] at J
  have : rho (fun ω ↦ X₁ ω - x₀) A volume = rho X₁ A volume := by
    simp_rw [sub_eq_add_neg, rho_of_translate hX₁ hA]
  linarith


-- @@ L1954-2000 expanded
/-- If $|A+A| \leq K|A|$, then there exists a subgroup $H$ and $t\in G$ such that
$|A \cap (H+t)| \geq K^{-4} \sqrt{|A||V|}$, and $|H|/|A|\in[K^{-8},K^8]$. -/
lemma better_PFR_conjecture_aux0 {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (t : G),
      K ^ (-4 : ℤ) * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (1 / 2 : ℝ) ≤
          Nat.card ↑(A ∩ (H + { t })) ∧
        Nat.card A ≤ K ^ 8 * (H : Set G).ncard ∧ (H : Set G).ncard ≤ K ^ 8 * Nat.card A :=
  by
  have A_fin : Finite A := by infer_instance
  classical
  let mG : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := ⟨fun _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' (Set.toFinite _) h₀A hA
  let A' := A.toFinite.toFinset
  have h₀A' : Finset.Nonempty A' := by simpa [A', Finset.Nonempty]
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' h₀A' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -⟩
  rw [hAA'] at UAunif
  have hadd_sub : A + A = A - A := by ext; simp [Set.mem_add, Set.mem_sub, ZModModule.sub_eq_add]
  rw [hadd_sub] at hA
  have : rdist UA UA volume volume ≤ log K :=
    rdist_le_of_isUniform_of_card_add_le h₀A hA UAunif UAmeas
  rw [← hadd_sub] at hA
  rcases rho_PFR_conjecture UA UA UAmeas UAmeas A' h₀A' with
    ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  have ineq : rho UH A' volume ≤ 4 * log K :=
    by
    rw [← hAA'] at UAunif
    have : rho UA A' volume = 0 := rho_of_uniform UAunif UAmeas h₀A'
    linarith
  set r := 4 * log K with hr
  have J : K ^ (-4 : ℤ) = exp (-r) :=
    by
    rw [hr, ← neg_mul, mul_comm, exp_mul, exp_log K_pos]
    norm_cast
  have J' : K ^ 8 = exp (2 * r) :=
    by
    have : 2 * r = 8 * log K := by ring
    rw [this, mul_comm, exp_mul, exp_log K_pos]
    norm_cast
  rw [J, J']
  refine ⟨H, ?_⟩
  have Z := rho_of_submodule UHunif h₀A' UHmeas r ineq
  have : Nat.card A = Nat.card A' := by simp [← hAA']
  have I t : t +ᵥ (H : Set G) = (H : Set G) + { t } := by ext z;
    simp [mem_vadd_set_iff_neg_vadd_mem, add_comm]
  simp_rw [← I]
  convert Z
  exact hAA'.symm


-- @@ L2002-2046 verbatim
/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup $H$
such that $A$ can be covered by at most $K^5 |A|^{1/2} / |H|^{1/2}$ cosets of $H$, and $H$ has
the same cardinality as $A$ up to a multiplicative factor $K^8$. -/
lemma better_PFR_conjecture_aux {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c ≤ K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * ((H : Set G).ncard : ℝ) ^ (-1 / 2 : ℝ)
      ∧ (H : Set G).ncard ≤ K ^ 8 * Nat.card A
      ∧ Nat.card A ≤ K ^ 8 * (H : Set G).ncard ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' (Set.toFinite _) h₀A hA
  rcases better_PFR_conjecture_aux0 h₀A hA with ⟨H, x₀, J, IAH, IHA⟩
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos
    positivity
  have Hne : Set.Nonempty (A ∩ (H + {x₀})) := by
    by_contra h'
    have : 0 < (H : Set G).ncard := Nat.card_pos
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    rw [not_nonempty_iff_eq_empty.1 h'] at this
    simp at this
    /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  have Z3 :
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ) ≤ (K ^ 5 * Nat.card A ^ (1/2 : ℝ) *
        (H : Set G).ncard ^ (-1/2 : ℝ)) * Nat.card ↑(A ∩ (↑H + {x₀})) := by
    calc
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ)
      _ ≤ Nat.card (A + A) := by
        gcongr; exact Nat.card_mono (toFinite _) <| add_subset_add_left inter_subset_left
      _ ≤ K * Nat.card A := hA
      _ = (K ^ 5 * Nat.card A ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
          (K ^ (-4 : ℤ) * Nat.card A ^ (1/2 : ℝ) * (H : Set G).ncard ^ (1/2 : ℝ)) := by
        simp_rw [← rpow_natCast, ← rpow_intCast]; rpow_ring; norm_num
      _ ≤ (K ^ 5 * Nat.card A ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
        Nat.card ↑(A ∩ (↑H + {x₀})) := by gcongr
  obtain ⟨u, huA, hucard, hAu, -⟩ :=
    Set.ruzsa_covering_add (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne (by convert Z3)
  have A_subset_uH : A ⊆ u + H := by
    grw [hAu, inter_subset_right, add_sub_add_comm, singleton_sub_singleton, _root_.sub_self]
    simp
  exact ⟨H, u, hucard, IHA, IAH, A_subset_uH⟩


-- @@ L2048-2112 verbatim
/-- If $A \subset {\bf F}_2^n$ is finite non-empty with $|A+A| \leq K|A|$, then there exists a
subgroup $H$ of ${\bf F}_2^n$ with $|H| \leq |A|$ such that $A$ can be covered by at most $2K^9$
translates of $H$. -/
lemma better_PFR_conjecture {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c < 2 * K ^ 9 ∧ (H : Set G).ncard ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' (Set.toFinite _) h₀A hA
  -- consider the subgroup `H` given by Lemma `PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (-1 / 2 : ℝ)
      ∧ (H : Set G).ncard ≤ K ^ 8 * Nat.card A ∧ Nat.card A ≤ K ^ 8 * (H : Set G).ncard
      ∧ A ⊆ c + H :=
    better_PFR_conjecture_aux h₀A hA
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos; positivity
  rcases le_or_gt ((H : Set G).ncard) (Nat.card A) with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (-1 / 2 : ℝ) := hc
    _ ≤ K ^ 5 * (K ^ 8 * (H : Set G).ncard) ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (-1 / 2 : ℝ) := by
      gcongr
    _ = K ^ 9 := by simp_rw [← rpow_natCast]; rpow_ring; norm_num
    _ < 2 * K ^ 9 := by linarith [show 0 < K ^ 9 by positivity]
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / 2 < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : Submodule (ZMod 2) G, Nat.card H' ≤ Nat.card A
          ∧ Nat.card A < 2 * Nat.card H' ∧ H' ≤ H := by
      have A_pos' : 0 < Nat.card A := mod_cast A_pos
      exact ZModModule.exists_submodule_subset_card_le Nat.prime_two H h.le A_pos'.ne'
    have : (Nat.card A / 2 : ℝ) < Nat.card H' := by
      rw [div_lt_iff₀ zero_lt_two, mul_comm]; norm_cast
    have H'_pos : (0 : ℝ) < Nat.card H' := by
      have : 0 < Nat.card H' := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ :=
      H'.toAddSubgroup.exists_left_transversal_of_le (H := H.toAddSubgroup) H'H
    dsimp at HH'u
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast natCard_add_le
    _ ≤ (K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * ((H : Set G).ncard ^ (-1 / 2 : ℝ)))
          * ((H : Set G).ncard / Nat.card H') := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * ((H : Set G).ncard ^ (-1 / 2 : ℝ)))
          * ((H : Set G).ncard / (Nat.card A / 2)) := by
        gcongr
    _ = (K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * ((H : Set G).ncard ^ (-1 / 2 : ℝ)))
          * ((H : Set G).ncard * (Nat.card A : ℝ)⁻¹ * 2) := by
        field_simp
    _ = 2 * K ^ 5 * Nat.card A ^ (-1 / 2 : ℝ) * (H : Set G).ncard ^ (1 / 2 : ℝ) := by
        rpow_ring
        field_simp
        norm_num
    _ ≤ 2 * K ^ 5 * Nat.card A ^ (-1 / 2 : ℝ) * (K ^ 8 * Nat.card A) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = 2 * K ^ 9 := by
        simp_rw [← rpow_natCast]
        rpow_ring
        norm_num


-- @@ L2114-2138 expanded
/-- Corollary of `better_PFR_conjecture` in which the ambient group is not required to be finite
(but) then $H$ and $c$ are finite. -/
theorem better_PFR_conjecture' {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] {A : Set G} {K : ℝ}
    (h₀A : A.Nonempty) (Afin : A.Finite) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      c.Finite ∧
        (H : Set G).Finite ∧ Nat.card c < 2 * K ^ 9 ∧ (H : Set G).ncard ≤ Nat.card A ∧ A ⊆ c + H :=
  by
  let G' := Submodule.span (ZMod 2) A
  let G'fin : Fintype G' := (Afin.submoduleSpan _).fintype
  let ι : G' →ₗ[ZMod 2] G := G'.subtype
  have ι_inj : Injective ι := G'.toAddSubgroup.subtype_injective
  let A' : Set G' := ι ⁻¹' A
  have A_rg : A ⊆ range ι :=
    by
    simp only [Submodule.coe_subtype, Subtype.range_coe_subtype, G', ι]
    exact Submodule.subset_span
  have cardA' : Nat.card A' = Nat.card A := Nat.card_preimage_of_injective ι_inj A_rg
  have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
    rwa [cardA', ← preimage_add _ ι_inj A_rg A_rg,
      Nat.card_preimage_of_injective ι_inj (add_subset_range _ A_rg A_rg)]
  rcases better_PFR_conjecture (h₀A.preimage' A_rg) hA' with ⟨H', c', hc', hH', hH'₂⟩
  refine ⟨H'.map ι, ι '' c', toFinite _, toFinite (ι '' H'), ?_, ?_, fun x hx ↦ ?_⟩
  · rwa [Nat.card_image_of_injective ι_inj]
  · simpa [Set.ncard_image_of_injective _ ι_inj, ← cardA']
  · erw [← image_add]
    exact ⟨⟨x, Submodule.subset_span hx⟩, hH'₂ hx, rfl⟩


-- @@ L2140-2140 verbatim
end PFR
