module

public import PFR.Fibring
public import PFR.TauFunctional


-- @@ L6-24 verbatim
/-!
# First estimate

The first estimate on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ are independent random variables, with $X_1,\tilde X_1$ copies
  of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $k := d[X_1;X_2]$
* $I_1 := I [X_1+X_2 : \tilde X_1 + X_2 | X_1+X_2+\tilde X_1+\tilde X_2]$

## Main results

* `first_estimate` : $I_1 ≤ 2 η k$
* `ent_ofsum_le` : $H[X_1+X_2+\tilde X_1+\tilde X_2] \le \tfrac{1}{2} H[X_1]+\tfrac{1}{2} H[X_2] +
  (2 + \eta) k - I_1.$
-/


-- @@ L26-26 verbatim
public section


-- @@ L28-28 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L30-31 verbatim
variable {G : Type*} [addgroup : AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G]


-- @@ L33-33 verbatim
variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]


-- @@ L35-35 verbatim
variable (p : refPackage Ω₀₁ Ω₀₂ G)


-- @@ L37-37 verbatim
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]


-- @@ L39-40 verbatim
variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')


-- @@ L42-42 verbatim
variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

-- @@ L43-43 verbatim
variable (h_indep : iIndepFun ![X₁, X₂, X₂', X₁'])

-- @@ L44-44 verbatim
variable (h_min : TauMinimizes p X₁ X₂)


-- @@ L46-47 expanded
/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => rdist X₁ X₂ volume volume


-- @@ L49-51 expanded
/-- `I₁ := I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₂` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume


-- @@ L53-76 expanded
include h_indep hX₁ hX₂ hX₁' hX₂' h₁ h₂ in
/-- The sum of
$$ d[X_1+\tilde X_2;X_2+\tilde X_1] + d[X_1|X_1+\tilde X_2; X_2|X_2+\tilde X_1] $$
and
$$ I[X_1+ X_2 : \tilde X_1 + X_2 \,|\, X_1 + X_2 + \tilde X_1 + \tilde X_2] $$
is equal to $2k$. -/
lemma rdist_add_rdist_add_condMutual_eq [Module (ZMod 2) G] :
    rdist (X₁ + X₂') (X₂ + X₁') volume volume +
          condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume +
        condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume =
      2 * rdist X₁ X₂ volume volume :=
  by
  cases nonempty_fintype G
  have h0 : ![X₁, X₂, X₂', X₁'] 0 = X₁ := rfl
  have h1 : ![X₁, X₂, X₂', X₁'] 1 = X₂ := rfl
  have h2 : ![X₁, X₂, X₂', X₁'] 2 = X₂' := rfl
  have h3 : ![X₁, X₂, X₂', X₁'] 3 = X₁' := rfl
  have h :=
    sum_of_rdist_eq_char_2 ![X₁, X₂, X₂', X₁'] h_indep (fun i => by fin_cases i <;> assumption)
  rw [h0, h1, h2, h3] at h
  have heq : rdist X₂' X₁' volume volume = rdist X₁ X₂ volume volume :=
    by
    rw [rdist_symm]
    apply h₁.symm.rdist_congr h₂.symm
  rw [heq] at h
  convert h.symm using 1
  · congr 2 <;> abel
  · ring


-- @@ L78-86 expanded
include h_min hX₁ hX₂ hX₁' hX₂' in
/-- The distance $d[X_1+\tilde X_2; X_2+\tilde X_1]$ is at least
$$k - \eta (d[X^0_1; X_1+\tilde X_2] - d[X^0_1; X_1]) -
  \eta (d[X^0_2; X_2+\tilde X_1] - d[X^0_2; X_2]).$$ -/
lemma rdist_of_sums_ge :
    rdist (X₁ + X₂') (X₂ + X₁') volume volume ≥
      rdist X₁ X₂ volume volume -
          p.η * (rdist p.X₀₁ (X₁ + X₂') volume volume - rdist p.X₀₁ X₁ volume volume) -
        p.η * (rdist p.X₀₂ (X₂ + X₁') volume volume - rdist p.X₀₂ X₂ volume volume) :=
  distance_ge_of_min _ h_min (hX₁.add hX₂') (hX₂.add hX₁')


-- @@ L88-97 expanded
include h_min hX₁ hX₂ hX₁' hX₂' in
/-- The distance $d[X_1|X_1+\tilde X_2; X_2|X_2+\tilde X_1]$ is at least
$$ k - \eta (d[X^0_1; X_1 | X_1 + \tilde X_2] - d[X^0_1; X_1])
  - \eta(d[X^0_2; X_2 | X_2 + \tilde X_1] - d[X^0_2; X_2]).$$
-/
lemma condRuzsaDist_of_sums_ge :
    condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume ≥
      rdist X₁ X₂ volume volume -
          p.η * (condRuzsaDist' p.X₀₁ X₁ (X₁ + X₂') volume volume - rdist p.X₀₁ X₁ volume volume) -
        p.η * (condRuzsaDist' p.X₀₂ X₂ (X₂ + X₁') volume volume - rdist p.X₀₂ X₂ volume volume) :=
  condRuzsaDistance_ge_of_min _ h_min hX₁ hX₂ _ _ (by fun_prop) (by fun_prop)


-- @@ L99-99 verbatim
variable [Module (ZMod 2) G]


-- @@ L101-108 expanded
include hX₁ hX₂' h_indep h₂ in
/-- `d[X₀₁ # X₁ + X₂'] - d[X₀₁ # X₁] ≤ k/2 + H[X₂]/4 - H[X₁]/4`. -/
lemma diff_rdist_le_1 [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] :
    rdist p.X₀₁ (X₁ + X₂') volume volume - rdist p.X₀₁ X₁ volume volume ≤
      rdist X₁ X₂ volume volume / 2 + entropy X₂ volume / 4 - entropy X₁ volume / 4 :=
  by
  have h : IndepFun X₁ X₂' := by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide)
  convert condRuzsaDist_diff_le' ℙ p.hmeas1 hX₁ hX₂' h using 4
  · exact h₂.rdist_congr_right hX₁.aemeasurable
  · exact h₂.entropy_congr


-- @@ L110-119 expanded
include hX₁' hX₂ h_indep h₁ in
/-- $$ d[X^0_2;X_2+\tilde X_1] - d[X^0_2; X_2] \leq \tfrac{1}{2} k +
  \tfrac{1}{4} \mathbb{H}[X_1] - \tfrac{1}{4} \mathbb{H}[X_2].$$ -/
lemma diff_rdist_le_2 [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
    rdist p.X₀₂ (X₂ + X₁') volume volume - rdist p.X₀₂ X₂ volume volume ≤
      rdist X₁ X₂ volume volume / 2 + entropy X₁ volume / 4 - entropy X₂ volume / 4 :=
  by
  have h : IndepFun X₂ X₁' := by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide)
  convert condRuzsaDist_diff_le' ℙ p.hmeas2 hX₂ hX₁' h using 4
  · rw [rdist_symm]
    exact h₁.rdist_congr_right hX₂.aemeasurable
  · exact h₁.entropy_congr


-- @@ L121-129 expanded
include h_indep hX₁ hX₂' h₂ in
/-- $$ d[X_1^0;X_1|X_1+\tilde X_2] - d[X_1^0;X_1] \leq
    \tfrac{1}{2} k + \tfrac{1}{4} \mathbb{H}[X_1] - \tfrac{1}{4} \mathbb{H}[X_2].$$ -/
lemma diff_rdist_le_3 [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] :
    condRuzsaDist' p.X₀₁ X₁ (X₁ + X₂') volume volume - rdist p.X₀₁ X₁ volume volume ≤
      rdist X₁ X₂ volume volume / 2 + entropy X₁ volume / 4 - entropy X₂ volume / 4 :=
  by
  have h : IndepFun X₁ X₂' := by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide)
  convert condRuzsaDist_diff_le''' ℙ p.hmeas1 hX₁ hX₂' h using 3
  · rw [h₂.rdist_congr_right hX₁.aemeasurable]
  · apply h₂.entropy_congr


-- @@ L131-131 verbatim
include h_indep hX₂ hX₁' h₁

-- @@ L132-139 expanded
/-- $$ d[X_2^0; X_2|X_2+\tilde X_1] - d[X_2^0; X_2] \leq
    \tfrac{1}{2}k + \tfrac{1}{4} \mathbb{H}[X_2] - \tfrac{1}{4} \mathbb{H}[X_1].$$ -/
lemma diff_rdist_le_4 [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
    condRuzsaDist' p.X₀₂ X₂ (X₂ + X₁') volume volume - rdist p.X₀₂ X₂ volume volume ≤
      rdist X₁ X₂ volume volume / 2 + entropy X₂ volume / 4 - entropy X₁ volume / 4 :=
  by
  have h : IndepFun X₂ X₁' := by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide)
  convert condRuzsaDist_diff_le''' ℙ p.hmeas2 hX₂ hX₁' h using 3
  · rw [rdist_symm, h₁.rdist_congr_right hX₂.aemeasurable]
  · apply h₁.entropy_congr


-- @@ L141-153 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_min in
/-- We have $I_1 \leq 2 \eta k$ -/
lemma first_estimate [IsProbabilityMeasure (ℙ : Measure Ω₀₁)]
    [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
    condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume ≤
      2 * p.η * rdist X₁ X₂ volume volume :=
  by
  have v1 := rdist_add_rdist_add_condMutual_eq X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  have v2 := rdist_of_sums_ge p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_› ‹_›
  have v3 := condRuzsaDist_of_sums_ge p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› (by fun_prop) (by aesop)
  have v4 := mul_le_mul_of_nonneg_left (diff_rdist_le_1 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›) p.hη.le
  have v5 := mul_le_mul_of_nonneg_left (diff_rdist_le_2 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›) p.hη.le
  have v6 := mul_le_mul_of_nonneg_left (diff_rdist_le_3 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›) p.hη.le
  have v7 := mul_le_mul_of_nonneg_left (diff_rdist_le_4 p X₁ X₂ X₁' X₂' ‹_› ‹_› ‹_› ‹_›) p.hη.le
  linarith [v1, v2, v3, v4, v5, v6, v7]


-- @@ L155-215 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_min in
/-- $$\mathbb{H}[X_1+X_2+\tilde X_1+\tilde X_2]
  \le \tfrac{1}{2} \mathbb{H}[X_1]+\tfrac{1}{2} \mathbb{H}[X_2] + (2 + \eta) k - I_1.$$ -/
lemma ent_ofsum_le [IsProbabilityMeasure (ℙ : Measure Ω₀₁)]
    [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
    entropy (X₁ + X₂ + X₁' + X₂') volume ≤
      entropy X₁ volume / 2 + entropy X₂ volume / 2 + (2 + p.η) * rdist X₁ X₂ volume volume -
        condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume :=
  by
  let D := rdist (X₁ + X₂') (X₂ + X₁') volume volume
  let Dcc := condRuzsaDist X₁ (X₁ + X₂') X₂ (X₂ + X₁') volume volume
  let D1 := rdist p.X₀₁ X₁ volume volume
  let Dc1 := condRuzsaDist' p.X₀₁ X₁ (X₁ + X₂') volume volume
  let D2 := rdist p.X₀₂ X₂ volume volume
  let Dc2 := condRuzsaDist' p.X₀₂ X₂ (X₂ + X₁') volume volume
  have lem68 :
    D + Dcc + condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume =
      2 * rdist X₁ X₂ volume volume :=
    rdist_add_rdist_add_condMutual_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep
  have lem610 : Dcc ≥ rdist X₁ X₂ volume volume - p.η * (Dc1 - D1) - p.η * (Dc2 - D2) :=
    condRuzsaDist_of_sums_ge p X₁ X₂ X₁' X₂' hX₁ hX₂ (by fun_prop) (by aesop) h_min
  have lem611c :
    Dc1 - D1 ≤ rdist X₁ X₂ volume volume / 2 + entropy X₁ volume / 4 - entropy X₂ volume / 4 :=
    diff_rdist_le_3 p X₁ X₂ X₁' X₂' hX₁ hX₂' h₂ h_indep
  have lem611d :
    Dc2 - D2 ≤ rdist X₁ X₂ volume volume / 2 + entropy X₂ volume / 4 - entropy X₁ volume / 4 :=
    diff_rdist_le_4 p X₁ X₂ X₁' X₂' hX₂ hX₁' h₁ h_indep
  have aux :
    D + condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume ≤
      (1 + p.η) * rdist X₁ X₂ volume volume :=
    by
    calc
      D + condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume ≤
          rdist X₁ X₂ volume volume + p.η * (Dc1 - D1) + p.η * (Dc2 - D2) :=
        ?_
      _ ≤
          rdist X₁ X₂ volume volume +
              p.η *
                (rdist X₁ X₂ volume volume / 2 + entropy X₁ volume / 4 - entropy X₂ volume / 4) +
            p.η * (rdist X₁ X₂ volume volume / 2 + entropy X₂ volume / 4 - entropy X₁ volume / 4) :=
        ?_
      _ = (1 + p.η) * rdist X₁ X₂ volume volume := by ring
    · linarith
    · gcongr <;> exact p.hη.le
  have ent_sub_eq_ent_add :
    entropy (X₁ + X₂' - (X₂ + X₁')) volume = entropy (X₁ + X₂' + (X₂ + X₁')) volume := by
    simp [ZModModule.sub_eq_add]
  have rw₁ : X₁ + X₂' + (X₂ + X₁') = X₁ + X₂ + X₁' + X₂' := by abel
  have ind_aux : IndepFun (X₁ + X₂') (X₂ + X₁') := by
    exact
      iIndepFun.indepFun_add_add h_indep (fun i ↦ by fin_cases i <;> assumption) 0 2 1 3 (by decide)
        (by decide) (by decide) (by decide)
  have ind :
    D =
      entropy (X₁ + X₂' - (X₂ + X₁')) volume - entropy (X₁ + X₂') volume / 2 -
        entropy (X₂ + X₁') volume / 2 :=
    ind_aux.rdist_eq (by fun_prop) (by fun_prop)
  rw [ind, ent_sub_eq_ent_add, rw₁] at aux
  have obs :
    entropy (X₁ + X₂ + X₁' + X₂') volume ≤
      entropy (X₁ + X₂') volume / 2 + entropy (X₂ + X₁') volume / 2 +
          (1 + p.η) * rdist X₁ X₂ volume volume -
        condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume :=
    by linarith
  have rw₂ :
    entropy (X₁ + X₂') volume =
      rdist X₁ X₂ volume volume + entropy X₁ volume / 2 + entropy X₂ volume / 2 :=
    by
    have HX₂_eq : entropy X₂ volume = entropy X₂' volume :=
      congr_arg (fun (μ : Measure G) ↦ measureEntropy (μ := μ)) h₂.map_eq
    have k_eq :
      rdist X₁ X₂ volume volume =
        entropy (X₁ - X₂') volume - entropy X₁ volume / 2 - entropy X₂' volume / 2 :=
      by
      have k_eq_aux : rdist X₁ X₂ volume volume = rdist X₁ X₂' volume volume :=
        h₂.rdist_congr_right hX₁.aemeasurable
      rw [k_eq_aux]
      exact (h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide)).rdist_eq hX₁ hX₂'
    rw [k_eq, ← ZModModule.sub_eq_add, ← HX₂_eq]
    ring
  have rw₃ :
    entropy (X₂ + X₁') volume =
      rdist X₁ X₂ volume volume + entropy X₁ volume / 2 + entropy X₂ volume / 2 :=
    by
    have HX₁_eq : entropy X₁ volume = entropy X₁' volume :=
      congr_arg (fun (μ : Measure G) ↦ measureEntropy (μ := μ)) h₁.map_eq
    have k_eq' :
      rdist X₁ X₂ volume volume =
        entropy (X₁' - X₂) volume - entropy X₁' volume / 2 - entropy X₂ volume / 2 :=
      by
      have k_eq_aux : rdist X₁ X₂ volume volume = rdist X₁' X₂ volume volume :=
        h₁.rdist_congr_left hX₂.aemeasurable
      rw [k_eq_aux]
      exact (h_indep.indepFun (show (3 : Fin 4) ≠ 1 by decide)).rdist_eq hX₁' hX₂
    rw [add_comm X₂ X₁', k_eq', ← ZModModule.sub_eq_add, ← HX₁_eq]
    ring
  calc
    entropy (X₁ + X₂ + X₁' + X₂') volume ≤
        entropy (X₁ + X₂') volume / 2 + entropy (X₂ + X₁') volume / 2 +
            (1 + p.η) * rdist X₁ X₂ volume volume -
          condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume :=
      obs
    _ =
        (rdist X₁ X₂ volume volume + entropy X₁ volume / 2 + entropy X₂ volume / 2) / 2 +
              (rdist X₁ X₂ volume volume + entropy X₁ volume / 2 + entropy X₂ volume / 2) / 2 +
            (1 + p.η) * rdist X₁ X₂ volume volume -
          condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume :=
      by rw [rw₂, rw₃]
    _ =
        entropy X₁ volume / 2 + entropy X₂ volume / 2 + (2 + p.η) * rdist X₁ X₂ volume volume -
          condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume :=
      by ring

