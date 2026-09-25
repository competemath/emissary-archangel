module

public import PFR.FirstEstimate
public import PFR.SecondEstimate


-- @@ L6-31 verbatim
/-!
# Endgame

The endgame on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies
    of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $U := X_1 + X_2$
* $V := \tilde X_1 + X_2$
* $W := X_1 + \tilde X_1$
* $S := X_1 + X_2 + \tilde X_1 + \tilde X_2$.
* $I_1 := I[U : V | S]$
* $I_2 := I[U : W | S]$
* $I_3 := I[V : W | S]$ (not explicitly defined in Lean)

# Main results:

* `sum_condMutual_le` : An upper bound on the total conditional mutual information $I_1+I_2+I_3$.
* `sum_dist_diff_le`: A sum of the "costs" of $U$, $V$, $W$.
* `construct_good`: A construction of two random variables with small Ruzsa distance between them
  given some random variables with control on total cost, as well as total mutual information.
-/


-- @@ L33-33 verbatim
public section


-- @@ L35-35 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L37-38 verbatim
variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G]


-- @@ L40-41 verbatim
variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]


-- @@ L43-43 verbatim
variable (p : refPackage Ω₀₁ Ω₀₂ G)


-- @@ L45-45 verbatim
variable {Ω : Type*} [mΩ : MeasureSpace Ω]


-- @@ L47-48 verbatim
variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')


-- @@ L50-50 verbatim
variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')


-- @@ L52-52 verbatim
variable (h_indep : iIndepFun ![X₁, X₂, X₁', X₂'])


-- @@ L54-54 verbatim
variable (h_min : TauMinimizes p X₁ X₂)


-- @@ L56-57 expanded
/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => rdist X₁ X₂ volume volume


-- @@ L59-60 verbatim
/-- `U := X₁ + X₂` -/
local notation3 "U" => X₁ + X₂


-- @@ L62-63 verbatim
/-- `V := X₁' + X₂` -/
local notation3 "V" => X₁' + X₂


-- @@ L65-66 verbatim
/-- `W := X₁' + X₁` -/
local notation3 "W" => X₁' + X₁


-- @@ L68-69 verbatim
/-- `S := X₁ + X₂ + X₁' + X₂'` -/
local notation3 "S" => X₁ + X₂ + X₁' + X₂'


-- @@ L71-73 expanded
/-- `I₁ := I[U : V | S]`, the conditional mutual information of `U = X₁ + X₂` and `V = X₁' + X₂`
given the quadruple sum `S = X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume


-- @@ L75-79 expanded
/-- `I₂ := I[U : W | S]`, the conditional mutual information of `U = X₁ + X₂` and `W = X₁' + X₁`
given the quadruple sum `S = X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₂" => condMutualInfo (X₁ + X₂) (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume


-- @@ L80-83 verbatim
private lemma hmeas2 {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
    [MeasurableSingletonClass G] :
    Measurable fun p : Fin 4 → G => ((p 0 + p 1, p 0 + p 2), p 0 + p 1 + p 2 + p 3) := by
  fun_prop


-- @@ L85-129 expanded
include h_indep hX₁ hX₂ hX₁' hX₂' h₁ in
/-- The quantity `I_3 = I[V:W|S]` is equal to `I_2`. -/
lemma I₃_eq [IsProbabilityMeasure (ℙ : Measure Ω)] :
    condMutualInfo (X₁' + X₂) (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume =
      condMutualInfo (X₁ + X₂) (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume :=
  by
  have h_indep2 : iIndepFun ![X₁', X₂, X₁, X₂'] := by exact h_indep.reindex_four_cbad
  have hident :
    IdentDistrib (fun a (i : Fin 4) => ![X₁, X₂, X₁', X₂'] i a)
      (fun a (j : Fin 4) => ![X₁', X₂, X₁, X₂'] j a) :=
    by
    exact
      { aemeasurable_fst := by
          apply Measurable.aemeasurable
          rw [measurable_pi_iff]
          intro x
          fin_cases x; all_goals aesop
        aemeasurable_snd := by
          apply Measurable.aemeasurable
          rw [measurable_pi_iff]
          intro x
          fin_cases x; all_goals aesop
        map_eq :=
          by
          rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
                  (Fin.cases hX₁.aemeasurable <|
                    Fin.cases hX₂.aemeasurable <|
                      Fin.cases hX₁'.aemeasurable <| Fin.cases hX₂'.aemeasurable Fin.rec0)).mp
              h_indep,
            (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
                  (Fin.cases hX₁'.aemeasurable <|
                    Fin.cases hX₂.aemeasurable <|
                      Fin.cases hX₁.aemeasurable <| Fin.cases hX₂'.aemeasurable Fin.rec0)).mp
              h_indep2]
          congr
          ext i
          fin_cases i
          all_goals simp [h₁.map_eq] }
  have hmeas1 : Measurable (fun p : Fin 4 → G => (p 0 + p 1, p 0 + p 1 + p 2 + p 3)) := by fun_prop
  have hUVS :
    IdentDistrib (prod (X₁ + X₂) (X₁ + X₂ + X₁' + X₂')) (prod (X₁' + X₂) (X₁ + X₂ + X₁' + X₂')) :=
    by convert! hident.comp hmeas1; simp; abel
  have hUVWS :
    IdentDistrib (prod (prod (X₁ + X₂) (X₁' + X₁)) (X₁ + X₂ + X₁' + X₂'))
      (prod (prod (X₁' + X₂) (X₁' + X₁)) (X₁ + X₂ + X₁' + X₂')) :=
    by convert (hident.comp hmeas2) <;> simp <;> abel
  have hU : Measurable (X₁ + X₂) := Measurable.add hX₁ hX₂
  have hV : Measurable (X₁' + X₂) := Measurable.add hX₁' hX₂
  have hW : Measurable (X₁' + X₁) := Measurable.add hX₁' hX₁
  have hS : Measurable (X₁ + X₂ + X₁' + X₂') := by fun_prop
  rw [condMutualInfo_eq hV hW hS, condMutualInfo_eq hU hW hS, chain_rule'' ℙ hU hS,
    chain_rule'' ℙ hV hS, chain_rule'' ℙ hW hS, chain_rule'' ℙ _ hS, chain_rule'' ℙ _ hS,
    hUVS.entropy_congr, hUVWS.entropy_congr]
  · exact Measurable.prod hU hW
  · exact Measurable.prod hV hW


-- @@ L131-145 expanded
include h_indep hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_min in
/-- `I[U : V | S] + I[V : W | S] + I[W : U | S]` is less than or equal to
`6 * η * k - (1 - 5 * η) / (1 - η) * (2 * η * k - I₁)`.
-/
lemma sum_condMutual_le [Module (ZMod 2) G] [IsProbabilityMeasure (ℙ : Measure Ω)] :
    condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume +
          condMutualInfo (X₁' + X₂) (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume +
        condMutualInfo (X₁' + X₁) (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume ≤
      6 * p.η * rdist X₁ X₂ volume volume -
        (1 - 5 * p.η) / (1 - p.η) *
          (2 * p.η * rdist X₁ X₂ volume volume -
            condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume) :=
  by
  have :
    condMutualInfo (X₁' + X₁) (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume =
      condMutualInfo (X₁ + X₂) (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume :=
    condMutualInfo_comm (by fun_prop) (by fun_prop) ..
  rw [I₃_eq, this]
  any_goals simpa
  have h₂ := second_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have : 0 < 1 - p.η := by linarith [p.hη']
  field_simp at h₂ ⊢
  linarith


-- @@ L147-148 expanded
local notation3:max "c[" A "; " μ " # " B " ; " μ' "]" =>
  rdist p.X₀₁ A ℙ μ - rdist p.X₀₁ X₁ volume volume +
    (rdist p.X₀₂ B ℙ μ' - rdist p.X₀₂ X₂ volume volume)


-- @@ L150-151 expanded
local notation3:max "c[" A " # " B "]" =>
  rdist p.X₀₁ A volume volume - rdist p.X₀₁ X₁ volume volume +
    (rdist p.X₀₂ B volume volume - rdist p.X₀₂ X₂ volume volume)


-- @@ L153-154 expanded
local notation3:max "c[" A " | " B " # " C " | " D "]" =>
  condRuzsaDist' p.X₀₁ A B volume volume - rdist p.X₀₁ X₁ volume volume +
    (condRuzsaDist' p.X₀₂ C D volume volume - rdist p.X₀₂ X₂ volume volume)


-- @@ L156-160 expanded
include h_indep h₁ h₂ in
lemma hU [IsProbabilityMeasure (ℙ : Measure Ω)] :
    entropy (X₁ + X₂) volume = entropy (X₁' + X₂') volume :=
  IdentDistrib.entropy_congr
    (h₁.add h₂ (h_indep.indepFun (show (0 : Fin 4) ≠ 1 by norm_cast))
      (h_indep.indepFun (show (2 : Fin 4) ≠ 3 by norm_cast)))


-- @@ L162-166 verbatim
variable {X₁ X₂ X₁' X₂'} in
include h_indep hX₁ hX₂ hX₁' hX₂' in
lemma independenceCondition1 :
    iIndepFun ![X₁, X₂, X₁' + X₂'] :=
  h_indep.apply_two_last hX₁ hX₂ hX₁' hX₂' measurable_add


-- @@ L168-172 expanded
include h₁ h₂ h_indep in
lemma hV [IsProbabilityMeasure (ℙ : Measure Ω)] :
    entropy (X₁' + X₂) volume = entropy (X₁ + X₂') volume :=
  IdentDistrib.entropy_congr
    (h₁.symm.add h₂ (h_indep.indepFun (show (2 : Fin 4) ≠ 1 by norm_cast))
      (h_indep.indepFun (show (0 : Fin 4) ≠ 3 by norm_cast)))


-- @@ L174-178 verbatim
include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition2 :
    iIndepFun ![X₂, X₁, X₁' + X₂'] :=
  independenceCondition1 hX₂ hX₁ hX₁' hX₂' h_indep.reindex_four_bacd


-- @@ L180-184 verbatim
include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition3 :
    iIndepFun ![X₁', X₂, X₁ + X₂'] :=
  independenceCondition1 hX₁' hX₂ hX₁ hX₂' h_indep.reindex_four_cbad


-- @@ L186-190 verbatim
include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition4 :
    iIndepFun ![X₂, X₁', X₁ + X₂'] :=
  independenceCondition1 hX₂ hX₁' hX₁ hX₂' h_indep.reindex_four_bcad


-- @@ L192-196 verbatim
include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition5 :
    iIndepFun ![X₁, X₁', X₂ + X₂'] :=
  independenceCondition1 hX₁ hX₁' hX₂ hX₂' h_indep.reindex_four_acbd


-- @@ L198-202 verbatim
include h_indep hX₁ hX₂ hX₁' hX₂' in
variable {X₁ X₂ X₁' X₂'} in
lemma independenceCondition6 :
    iIndepFun ![X₂, X₂', X₁' + X₁] :=
  independenceCondition1 hX₂ hX₂' hX₁' hX₁ h_indep.reindex_four_bdca


-- @@ L204-308 expanded
include h_indep hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_min in
/-- $$ \sum_{i=1}^2 \sum_{A\in\{U,V,W\}} \big(d[X^0_i;A|S] - d[X^0_i;X_i]\big)$$
is less than or equal to
$$ \leq (6 - 3\eta) k + 3(2 \eta k - I_1).$$
-/
lemma sum_dist_diff_le [IsProbabilityMeasure (ℙ : Measure Ω)] [Module (ZMod 2) G] :
    condRuzsaDist' p.X₀₁ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₁ X₁ volume volume +
            (condRuzsaDist' p.X₀₂ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₂ X₂ volume volume) +
          (condRuzsaDist' p.X₀₁ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₁ X₁ volume volume +
            (condRuzsaDist' p.X₀₂ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₂ X₂ volume volume)) +
        (condRuzsaDist' p.X₀₁ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₁ X₁ volume volume +
          (condRuzsaDist' p.X₀₂ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₂ X₂ volume volume)) ≤
      (6 - 3 * p.η) * rdist X₁ X₂ volume volume +
        3 *
          (2 * p.η * rdist X₁ X₂ volume volume -
            condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume) :=
  by
  let X₀₁ := p.X₀₁
  let X₀₂ := p.X₀₂
  have ineq1 :
    condRuzsaDist' X₀₁ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume - rdist X₀₁ X₁ volume volume ≤
      (entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₁ ℙ) / 2 :=
    by
    have aux1 :
      entropy (X₁ + X₂ + X₁' + X₂') volume + entropy (X₁ + X₂) volume - entropy X₁ volume -
          entropy (X₁' + X₂') volume =
        entropy (X₁ + X₂ + X₁' + X₂') volume - entropy X₁ volume :=
      by rw [hU X₁ X₂ X₁' X₂' h₁ h₂ h_indep]; ring
    have aux2 :
      condRuzsaDist' X₀₁ (X₁ + X₂) (X₁ + X₂ + (X₁' + X₂')) volume volume -
          rdist X₀₁ X₁ volume volume ≤
        (entropy (X₁ + X₂ + (X₁' + X₂')) volume + entropy (X₁ + X₂) volume - entropy X₁ volume -
            entropy (X₁' + X₂') volume) /
          2 :=
      condRuzsaDist_diff_ofsum_le ℙ (hX := p.hmeas1) (hY := hX₁) (hZ := hX₂)
        (Measurable.add hX₁' hX₂') (independenceCondition1 hX₁ hX₂ hX₁' hX₂' h_indep)
    rw [← add_assoc, aux1] at aux2
    linarith [aux2]
  have ineq2 :
    condRuzsaDist' X₀₂ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume - rdist X₀₂ X₂ volume volume ≤
      (entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₂ ℙ) / 2 :=
    by
    have aux1 :
      entropy (X₁ + X₂ + X₁' + X₂') volume + entropy (X₁ + X₂) volume - entropy X₂ volume -
          entropy (X₁' + X₂') volume =
        entropy (X₁ + X₂ + X₁' + X₂') volume - entropy X₂ volume :=
      by rw [hU X₁ X₂ X₁' X₂' h₁ h₂ h_indep]; ring
    have aux2 :
      condRuzsaDist' X₀₂ (X₁ + X₂) (X₁ + X₂ + (X₁' + X₂')) volume volume -
          rdist X₀₂ X₂ volume volume ≤
        (entropy (X₁ + X₂ + (X₁' + X₂')) volume + entropy (X₁ + X₂) volume - entropy X₂ volume -
            entropy (X₁' + X₂') volume) /
          2 :=
      by
      rw [(show X₁ + X₂ = X₂ + X₁ from add_comm _ _)]
      apply
        condRuzsaDist_diff_ofsum_le ℙ (p.hmeas2) (hX₂) (hX₁) (Measurable.add hX₁' hX₂')
          (independenceCondition2 hX₁ hX₂ hX₁' hX₂' h_indep)
    rw [← add_assoc, aux1] at aux2
    linarith [aux2]
  have V_add_eq : X₁' + X₂ + (X₁ + X₂') = X₁ + X₂ + X₁' + X₂' := by abel
  have ineq3 :
    condRuzsaDist' X₀₁ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume - rdist X₀₁ X₁ volume volume ≤
      (entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₁ ℙ) / 2 :=
    by
    have aux2 :
      condRuzsaDist' p.X₀₁ (X₁' + X₂) (X₁' + X₂ + (X₁ + X₂')) volume volume -
          rdist p.X₀₁ X₁' volume volume ≤
        (entropy (X₁' + X₂ + (X₁ + X₂')) volume + entropy (X₁' + X₂) volume - entropy X₁' volume -
            entropy (X₁ + X₂') volume) /
          2 :=
      condRuzsaDist_diff_ofsum_le ℙ (p.hmeas1) (hX₁') (hX₂) (Measurable.add hX₁ hX₂')
        (independenceCondition3 hX₁ hX₂ hX₁' hX₂' h_indep)
    have aux1 :
      entropy (X₁ + X₂ + X₁' + X₂') volume + entropy (X₁' + X₂) volume - entropy X₁' volume -
          entropy (X₁ + X₂') volume =
        entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₁ ℙ :=
      by rw [hV X₁ X₂ X₁' X₂' h₁ h₂ h_indep, h₁.entropy_congr]; ring
    rw [← h₁.rdist_congr_right p.hmeas1.aemeasurable, V_add_eq, aux1] at aux2
    linarith [aux2]
  have ineq4 :
    condRuzsaDist' X₀₂ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume - rdist X₀₂ X₂ volume volume ≤
      (entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₂ ℙ) / 2 :=
    by
    have aux2 :
      condRuzsaDist' p.X₀₂ (X₁' + X₂) (X₁' + X₂ + (X₁ + X₂')) volume volume -
          rdist p.X₀₂ X₂ volume volume ≤
        (entropy (X₁' + X₂ + (X₁ + X₂')) volume + entropy (X₁' + X₂) volume - entropy X₂ volume -
            entropy (X₁ + X₂') volume) /
          2 :=
      by
      rw [(show X₁' + X₂ = X₂ + X₁' from add_comm _ _)]
      apply
        condRuzsaDist_diff_ofsum_le ℙ (p.hmeas2) (hX₂) (hX₁') (Measurable.add hX₁ hX₂')
          (independenceCondition4 hX₁ hX₂ hX₁' hX₂' h_indep)
    have aux1 :
      entropy (X₁ + X₂ + X₁' + X₂') volume + entropy (X₁' + X₂) volume - entropy X₂ volume -
          entropy (X₁ + X₂') volume =
        entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₂ ℙ :=
      by rw [hV X₁ X₂ X₁' X₂' h₁ h₂ h_indep]; ring
    rw [V_add_eq, aux1] at aux2
    linarith [aux2]
  let W' := X₂ + X₂'
  have ineq5 :
    condRuzsaDist' X₀₁ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume - rdist X₀₁ X₁ volume volume ≤
      (entropy (X₁ + X₂ + X₁' + X₂') ℙ + entropy (X₁' + X₁) ℙ - entropy X₁ ℙ - entropy W' ℙ) / 2 :=
    by
    have :=
      condRuzsaDist_diff_ofsum_le ℙ p.hmeas1 hX₁ hX₁' (Measurable.add hX₂ hX₂')
        (independenceCondition5 hX₁ hX₂ hX₁' hX₂' h_indep)
    grind
  have ineq6 :
    condRuzsaDist' X₀₂ W' (X₁ + X₂ + X₁' + X₂') volume volume - rdist X₀₂ X₂ volume volume ≤
      (entropy (X₁ + X₂ + X₁' + X₂') ℙ + entropy W' ℙ - entropy X₂ ℙ - entropy (X₁' + X₁) ℙ) / 2 :=
    by
    have :=
      condRuzsaDist_diff_ofsum_le ℙ p.hmeas2 hX₂ hX₂' (Measurable.add hX₁' hX₁)
        (independenceCondition6 hX₁ hX₂ hX₁' hX₂' h_indep)
    grind
  have dist_eq :
    condRuzsaDist' X₀₂ W' (X₁ + X₂ + X₁' + X₂') volume volume =
      condRuzsaDist' X₀₂ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume :=
    by
    have S_eq : X₁ + X₂ + X₁' + X₂' = (X₂ + X₂') + (X₁' + X₁) := by
      rw [add_comm X₁' X₁, add_assoc _ X₂', add_comm X₂', ← add_assoc X₂, ← add_assoc X₂,
        add_comm X₂]
    rw [S_eq]
    apply
      condRuzsaDist'_of_inj_map' p.hmeas2 (hX₂.add hX₂')
        (hX₁'.add hX₁)
          -- Put everything together to bound the sum of the `c` terms
          
  have ineq7 :
    condRuzsaDist' p.X₀₁ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₁ X₁ volume volume +
            (condRuzsaDist' p.X₀₂ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₂ X₂ volume volume) +
          (condRuzsaDist' p.X₀₁ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₁ X₁ volume volume +
            (condRuzsaDist' p.X₀₂ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₂ X₂ volume volume)) +
        (condRuzsaDist' p.X₀₁ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₁ X₁ volume volume +
          (condRuzsaDist' p.X₀₂ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₂ X₂ volume volume)) ≤
      3 * entropy (X₁ + X₂ + X₁' + X₂') ℙ - 3 / 2 * entropy X₁ ℙ - 3 / 2 * entropy X₂ ℙ :=
    by
    have step₁ :
      condRuzsaDist' p.X₀₁ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₁ X₁ volume volume +
          (condRuzsaDist' p.X₀₂ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₂ X₂ volume volume) ≤
        entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2 :=
      calc
        _ =
            (condRuzsaDist' p.X₀₁ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist p.X₀₁ X₁ volume volume) +
              (condRuzsaDist' p.X₀₂ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist p.X₀₂ X₂ volume volume) :=
          by ring
        _ ≤
            (entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₁ ℙ) / 2 +
              (entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₂ ℙ) / 2 :=
          (add_le_add ineq1 ineq2)
        _ = entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2 := by ring
    have step₂ :
      condRuzsaDist' p.X₀₁ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₁ X₁ volume volume +
          (condRuzsaDist' p.X₀₂ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₂ X₂ volume volume) ≤
        entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2 :=
      calc
        condRuzsaDist' p.X₀₁ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₁ X₁ volume volume +
            (condRuzsaDist' p.X₀₂ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₂ X₂ volume volume)
        _ =
            condRuzsaDist' p.X₀₁ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist p.X₀₁ X₁ volume volume +
              (condRuzsaDist' p.X₀₂ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist p.X₀₂ X₂ volume volume) :=
          by ring
        _ ≤
            (entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₁ ℙ) / 2 +
              (entropy (X₁ + X₂ + X₁' + X₂') ℙ - entropy X₂ ℙ) / 2 :=
          (add_le_add ineq3 ineq4)
        _ = entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2 := by ring
    have step₃ :
      condRuzsaDist' p.X₀₁ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₁ X₁ volume volume +
          (condRuzsaDist' p.X₀₂ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₂ X₂ volume volume) ≤
        entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2 :=
      calc
        condRuzsaDist' p.X₀₁ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist p.X₀₁ X₁ volume volume +
              (condRuzsaDist' p.X₀₂ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist p.X₀₂ X₂ volume volume) =
            (condRuzsaDist' X₀₁ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist X₀₁ X₁ volume volume) +
              (condRuzsaDist' X₀₂ W' (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist X₀₂ X₂ volume volume) :=
          by rw [dist_eq]
        _ ≤
            (entropy (X₁ + X₂ + X₁' + X₂') ℙ + entropy (X₁' + X₁) ℙ - entropy X₁ ℙ - entropy W' ℙ) /
                2 +
              (entropy (X₁ + X₂ + X₁' + X₂') ℙ + entropy W' ℙ - entropy X₂ ℙ -
                  entropy (X₁' + X₁) ℙ) /
                2 :=
          (add_le_add ineq5 ineq6)
        _ = entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2 := by ring
    calc
      condRuzsaDist' p.X₀₁ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
                  rdist p.X₀₁ X₁ volume volume +
                (condRuzsaDist' p.X₀₂ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
                  rdist p.X₀₂ X₂ volume volume) +
              (condRuzsaDist' p.X₀₁ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
                  rdist p.X₀₁ X₁ volume volume +
                (condRuzsaDist' p.X₀₂ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
                  rdist p.X₀₂ X₂ volume volume)) +
            (condRuzsaDist' p.X₀₁ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist p.X₀₁ X₁ volume volume +
              (condRuzsaDist' p.X₀₂ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
                rdist p.X₀₂ X₂ volume volume)) ≤
          (entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2) +
              (entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2) +
            (entropy (X₁ + X₂ + X₁' + X₂') ℙ - (entropy X₁ ℙ + entropy X₂ ℙ) / 2) :=
        add_le_add (add_le_add step₁ step₂) step₃
      _ = 3 * entropy (X₁ + X₂ + X₁' + X₂') ℙ - 3 / 2 * entropy X₁ ℙ - 3 / 2 * entropy X₂ ℙ := by
        ring
  have h_indep' : iIndepFun ![X₁, X₂, X₂', X₁'] :=
    by
    refine .of_precomp (Equiv.swap (2 : Fin 4) 3).surjective ?_
    convert h_indep using 1
    ext x
    fin_cases x;
    all_goals { aesop
    }
  have ineq8 :
    3 * entropy (X₁ + X₂ + X₁' + X₂') ℙ ≤
      3 / 2 * (entropy X₁ ℙ + entropy X₂ ℙ) + 3 * (2 + p.η) * rdist X₁ X₂ volume volume -
        3 * condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume :=
    calc
      3 * entropy (X₁ + X₂ + X₁' + X₂') ℙ ≤
          3 *
            (entropy X₁ ℙ / 2 + entropy X₂ ℙ / 2 + (2 + p.η) * rdist X₁ X₂ volume volume -
              condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume) :=
        by
        gcongr
        exact ent_ofsum_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min
      _ =
          3 / 2 * (entropy X₁ ℙ + entropy X₂ ℙ) + 3 * (2 + p.η) * rdist X₁ X₂ volume volume -
            3 * condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume :=
        by
        ring
          -- Final computation
          
  calc
    condRuzsaDist' p.X₀₁ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₁ X₁ volume volume +
            (condRuzsaDist' p.X₀₂ (X₁ + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₂ X₂ volume volume) +
          (condRuzsaDist' p.X₀₁ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₁ X₁ volume volume +
            (condRuzsaDist' p.X₀₂ (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume volume -
              rdist p.X₀₂ X₂ volume volume)) +
        (condRuzsaDist' p.X₀₁ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₁ X₁ volume volume +
          (condRuzsaDist' p.X₀₂ (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume volume -
            rdist p.X₀₂ X₂ volume volume))
    _ ≤ 3 * entropy (X₁ + X₂ + X₁' + X₂') ℙ - 3 / 2 * entropy X₁ ℙ - 3 / 2 * entropy X₂ ℙ := ineq7
    _ = 3 * entropy (X₁ + X₂ + X₁' + X₂') ℙ - (3 / 2 * (entropy X₁ ℙ + entropy X₂ ℙ)) := by ring
    _ ≤
        (3 / 2 * (entropy X₁ ℙ + entropy X₂ ℙ) + 3 * (2 + p.η) * rdist X₁ X₂ volume volume -
            3 * condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume) -
          (3 / 2 * (entropy X₁ ℙ + entropy X₂ ℙ)) :=
      (sub_le_sub_right ineq8 _)
    _ =
        (6 - 3 * p.η) * rdist X₁ X₂ volume volume +
          3 *
            (2 * p.η * rdist X₁ X₂ volume volume -
              condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume) :=
      by ring


-- @@ L310-313 expanded
omit [Finite G] hG [MeasurableSingletonClass G] mΩ in
/-- `U + V + W = 0`. -/
lemma sum_uvw_eq_zero [Module (ZMod 2) G] : X₁ + X₂ + (X₁' + X₂) + (X₁' + X₁) = 0 := by
  simp [add_assoc, ← ZModModule.sub_eq_add X₁', ZModModule.add_self]


-- @@ L315-315 verbatim
section construct_good

-- @@ L316-316 verbatim
variable {Ω' : Type*} [MeasureSpace Ω']


-- @@ L318-328 expanded
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] in
lemma cond_c_eq_integral [IsProbabilityMeasure (ℙ : Measure Ω')] {Y Z : Ω' → G} (hY : Measurable Y)
    (hZ : Measurable Z) :
    condRuzsaDist' p.X₀₁ Y Z volume volume - rdist p.X₀₁ X₁ volume volume +
        (condRuzsaDist' p.X₀₂ Y Z volume volume - rdist p.X₀₂ X₂ volume volume) =
      (Measure.map Z ℙ)[fun z =>
        rdist p.X₀₁ Y ℙ ℙ[|Z ← z] - rdist p.X₀₁ X₁ volume volume +
          (rdist p.X₀₂ Y ℙ ℙ[|Z ← z] - rdist p.X₀₂ X₂ volume volume)] :=
  by
  cases nonempty_fintype G
  simp only [integral_fintype .of_finite, smul_sub, smul_add, smul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  simp_rw [← integral_fintype .of_finite]
  rw [← condRuzsaDist'_eq_integral _ hY hZ, ← condRuzsaDist'_eq_integral _ hY hZ, integral_const,
    integral_const]
  simp


-- @@ L330-330 verbatim
variable {T₁ T₂ T₃ : Ω' → G} (hT : T₁ + T₂ + T₃ = 0)

-- @@ L331-333 verbatim
variable (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)
  [IsProbabilityMeasure (ℙ : Measure Ω')] [Module (ZMod 2) G]
  --[IsProbabilityMeasure (ℙ : Measure Ω)]


-- @@ L335-335 expanded
local notation3:max "δ[" μ "]" => mutualInfo T₁ T₂ μ + mutualInfo T₂ T₃ μ + mutualInfo T₃ T₁ μ


-- @@ L336-336 expanded
local notation3:max "δ" =>
  mutualInfo T₁ T₂ volume + mutualInfo T₂ T₃ volume + mutualInfo T₃ T₁ volume


-- @@ L338-338 expanded
local notation3:max "ψ[" A " # " B "]" =>
  rdist A B volume volume +
    p.η *
      (rdist p.X₀₁ A volume volume - rdist p.X₀₁ X₁ volume volume +
        (rdist p.X₀₂ B volume volume - rdist p.X₀₂ X₂ volume volume))


-- @@ L339-340 expanded
local notation3:max "ψ[" A "; " μ " # " B " ; " μ' "]" =>
  rdist A B μ μ' +
    p.η *
      (rdist p.X₀₁ A ℙ μ - rdist p.X₀₁ X₁ volume volume +
        (rdist p.X₀₂ B ℙ μ' - rdist p.X₀₂ X₂ volume volume))


-- @@ L342-398 expanded
include hT₁ hT₂ hT₃ hT h_min in
/-- If $T_1, T_2, T_3$ are $G$-valued random variables with $T_1+T_2+T_3=0$ holds identically and
$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$
Then there exist random variables $T'_1, T'_2$ such that
$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X_1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2]) $$
is at most
$$ \delta + \eta ( d[X^0_1;T_1]-d[X^0_1;X_1]) + \eta (d[X^0_2;T_2]-d[X^0_2;X_2]) $$
$$ + \tfrac12 \eta I[T_1: T_3] + \tfrac12 \eta I[T_2: T_3].$$
-/
lemma construct_good_prelim :
    rdist X₁ X₂ volume volume ≤
      δ +
          p.η *
            (rdist p.X₀₁ T₁ volume volume - rdist p.X₀₁ X₁ volume volume +
              (rdist p.X₀₂ T₂ volume volume - rdist p.X₀₂ X₂ volume volume)) +
        p.η * (mutualInfo T₁ T₃ volume + mutualInfo T₂ T₃ volume) / 2 :=
  by
  let sum1 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ rdist T₁ T₂ ℙ[|T₃ ⁻¹' { t }] ℙ[|T₃ ⁻¹' { t }]]
  let sum2 : ℝ :=
    (Measure.map T₃ ℙ)[fun t ↦ rdist p.X₀₁ T₁ ℙ ℙ[|T₃ ⁻¹' { t }] - rdist p.X₀₁ X₁ volume volume]
  let sum3 : ℝ :=
    (Measure.map T₃ ℙ)[fun t ↦ rdist p.X₀₂ T₂ ℙ ℙ[|T₃ ⁻¹' { t }] - rdist p.X₀₂ X₂ volume volume]
  let sum4 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ ψ[T₁; ℙ[|T₃ ⁻¹' { t }] # T₂ ; ℙ[|T₃ ⁻¹' { t }]]]
  have hp.η : 0 ≤ p.η := by linarith [p.hη]
  have h2T₃ : T₃ = T₁ + T₂ :=
    calc
      T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hT, zero_sub]; simp [ZModModule.neg_eq_self]
      _ = T₁ + T₂ := by rw [add_sub_cancel_right]
  have h2T₁ : T₁ = T₂ + T₃ := by simp [h2T₃, add_left_comm, ZModModule.add_self]
  have h2T₂ : T₂ = T₃ + T₁ := by simp [h2T₁, add_left_comm, ZModModule.add_self]
  have h1 : sum1 ≤ δ :=
    by
    have h1 :
      sum1 ≤
        3 * mutualInfo T₁ T₂ volume + 2 * entropy T₃ volume - entropy T₁ volume -
          entropy T₂ volume :=
      by subst h2T₃; exact ent_bsg hT₁ hT₂
    have h2 : entropy ⟨T₂, T₃⟩ volume = entropy ⟨T₁, T₂⟩ volume := by
      rw [h2T₃, entropy_add_right', entropy_comm] <;> assumption
    have h3 : entropy ⟨T₁, T₂⟩ volume = entropy ⟨T₃, T₁⟩ volume := by
      rw [h2T₃, entropy_add_left, entropy_comm] <;> assumption
    simp_rw [mutualInfo_def] at h1 ⊢; linarith
  have h2 :
    p.η * sum2 ≤
      p.η *
        (rdist p.X₀₁ T₁ volume volume - rdist p.X₀₁ X₁ volume volume +
          mutualInfo T₁ T₃ volume / 2) :=
    by
    have : sum2 = condRuzsaDist' p.X₀₁ T₁ T₃ volume volume - rdist p.X₀₁ X₁ volume volume :=
      by
      simp only [integral_sub .of_finite .of_finite, integral_const, smul_eq_mul, sum2]
      simp [condRuzsaDist'_eq_sum hT₁ hT₃,
        integral_eq_setIntegral (FiniteRange.ae_mem_toFinset hT₃.aemeasurable),
        setIntegral_finset _ .finset, map_measureReal_apply hT₃ (.singleton _)]
    gcongr
    linarith [condRuzsaDist_le' ℙ ℙ p.hmeas1 hT₁ hT₃]
  have h3 :
    p.η * sum3 ≤
      p.η *
        (rdist p.X₀₂ T₂ volume volume - rdist p.X₀₂ X₂ volume volume +
          mutualInfo T₂ T₃ volume / 2) :=
    by
    have : sum3 = condRuzsaDist' p.X₀₂ T₂ T₃ volume volume - rdist p.X₀₂ X₂ volume volume :=
      by
      simp only [integral_sub .of_finite .of_finite, integral_const, smul_eq_mul, sum3]
      simp [condRuzsaDist'_eq_sum hT₂ hT₃,
        integral_eq_setIntegral (FiniteRange.ae_mem_toFinset hT₃.aemeasurable),
        setIntegral_finset _ .finset, map_measureReal_apply hT₃ (.singleton _)]
    gcongr
    linarith [condRuzsaDist_le' ℙ ℙ p.hmeas2 hT₂ hT₃]
  have h4 :
    sum4 ≤
      δ +
          p.η *
            (rdist p.X₀₁ T₁ volume volume - rdist p.X₀₁ X₁ volume volume +
              (rdist p.X₀₂ T₂ volume volume - rdist p.X₀₂ X₂ volume volume)) +
        p.η * (mutualInfo T₁ T₃ volume + mutualInfo T₂ T₃ volume) / 2 :=
    by
    suffices sum4 = sum1 + p.η * (sum2 + sum3) by linarith
    simp only [sum1, sum2, sum3, sum4, integral_add .of_finite .of_finite, integral_const_mul]
  have hk : rdist X₁ X₂ volume volume ≤ sum4 :=
    by
    suffices (Measure.map T₃ ℙ)[fun _ ↦ rdist X₁ X₂ volume volume] ≤ sum4 by simpa using this
    refine integral_mono_ae .of_finite .of_finite <| ae_iff_of_countable.2 fun t ht ↦ ?_
    have : IsProbabilityMeasure (ℙ[|T₃ ⁻¹' { t }]) :=
      cond_isProbabilityMeasure (by simpa [hT₃] using ht)
    dsimp only
    linarith only [distance_ge_of_min' (μ := ℙ[|T₃ ⁻¹' { t }]) (μ' := ℙ[|T₃ ⁻¹' { t }]) p h_min hT₁
        hT₂]
  exact hk.trans h4


-- @@ L400-421 expanded
include hT₁ hT₂ hT₃ hT h_min in
/-- If $T_1, T_2, T_3$ are $G$-valued random variables with $T_1+T_2+T_3=0$ holds identically and
-
$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$

Then there exist random variables $T'_1, T'_2$ such that

$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X _1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2])$$

is at most

$$\delta + \frac{\eta}{3} \biggl( \delta + \sum_{i=1}^2 \sum_{j = 1}^3
    (d[X^0_i;T_j] - d[X^0_i; X_i]) \biggr).$$
-/
lemma construct_good :
    rdist X₁ X₂ volume volume ≤
      δ +
        (p.η / 3) *
          (δ +
                (rdist p.X₀₁ T₁ volume volume - rdist p.X₀₁ X₁ volume volume +
                  (rdist p.X₀₂ T₁ volume volume - rdist p.X₀₂ X₂ volume volume)) +
              (rdist p.X₀₁ T₂ volume volume - rdist p.X₀₁ X₁ volume volume +
                (rdist p.X₀₂ T₂ volume volume - rdist p.X₀₂ X₂ volume volume)) +
            (rdist p.X₀₁ T₃ volume volume - rdist p.X₀₁ X₁ volume volume +
              (rdist p.X₀₂ T₃ volume volume - rdist p.X₀₂ X₂ volume volume))) :=
  by
  have v2 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₁ hT₃ hT₂
  have v3 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₂ hT₁ hT₃
  have v6 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₃ hT₂ hT₁
  simp only [mutualInfo, entropy_comm hT₂ hT₁, entropy_comm hT₃ hT₁, entropy_comm hT₃ hT₂] at *
  linarith


-- @@ L423-428 expanded
include hT₁ hT₂ hT₃ hT h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω')] in
lemma construct_good' (μ : Measure Ω') [IsProbabilityMeasure μ] :
    rdist X₁ X₂ volume volume ≤
      δ[μ] +
        (p.η / 3) *
          (δ[μ] +
                (rdist p.X₀₁ T₁ ℙ μ - rdist p.X₀₁ X₁ volume volume +
                  (rdist p.X₀₂ T₁ ℙ μ - rdist p.X₀₂ X₂ volume volume)) +
              (rdist p.X₀₁ T₂ ℙ μ - rdist p.X₀₁ X₁ volume volume +
                (rdist p.X₀₂ T₂ ℙ μ - rdist p.X₀₂ X₂ volume volume)) +
            (rdist p.X₀₁ T₃ ℙ μ - rdist p.X₀₁ X₁ volume volume +
              (rdist p.X₀₂ T₃ ℙ μ - rdist p.X₀₂ X₂ volume volume))) :=
  by
  let : MeasureSpace Ω' := ⟨μ⟩
  apply construct_good p X₁ X₂ h_min hT hT₁ hT₂ hT₃


-- @@ L430-430 verbatim
variable {R : Ω' → G} (hR : Measurable R)

-- @@ L431-431 expanded
local notation3:max "δ'" =>
  condMutualInfo T₁ T₂ R volume + condMutualInfo T₂ T₃ R volume + condMutualInfo T₃ T₁ R volume


-- @@ L433-438 verbatim
omit [AddCommGroup G] in
lemma delta'_eq_integral :
    δ' = (Measure.map R ℙ)[fun r => δ[ℙ[|R⁻¹' {r}]]] := by
  cases nonempty_fintype G
  simp_rw [condMutualInfo_eq_integral_mutualInfo, integral_fintype .of_finite, smul_add,
    Finset.sum_add_distrib]


-- @@ L440-461 expanded
include hT₁ hT₂ hT₃ hT h_min hR in
lemma cond_construct_good :
    rdist X₁ X₂ volume volume ≤
      δ' +
        (p.η / 3) *
          (δ' +
                (condRuzsaDist' p.X₀₁ T₁ R volume volume - rdist p.X₀₁ X₁ volume volume +
                  (condRuzsaDist' p.X₀₂ T₁ R volume volume - rdist p.X₀₂ X₂ volume volume)) +
              (condRuzsaDist' p.X₀₁ T₂ R volume volume - rdist p.X₀₁ X₁ volume volume +
                (condRuzsaDist' p.X₀₂ T₂ R volume volume - rdist p.X₀₂ X₂ volume volume)) +
            (condRuzsaDist' p.X₀₁ T₃ R volume volume - rdist p.X₀₁ X₁ volume volume +
              (condRuzsaDist' p.X₀₂ T₃ R volume volume - rdist p.X₀₂ X₂ volume volume))) :=
  by
  cases nonempty_fintype G
  rw [delta'_eq_integral, cond_c_eq_integral _ _ _ hT₁ hR, cond_c_eq_integral _ _ _ hT₂ hR,
    cond_c_eq_integral _ _ _ hT₃ hR]
  simp_rw [integral_fintype .of_finite, ← Finset.sum_add_distrib, ← smul_add, Finset.mul_sum,
    mul_smul_comm, ← Finset.sum_add_distrib, ← smul_add]
  simp_rw [← integral_fintype .of_finite]
  calc
    rdist X₁ X₂ volume volume = (Measure.map R ℙ)[fun _r => rdist X₁ X₂ volume volume] := by
      rw [integral_const]; simp
    _ ≤ _ := ?_
  simp_rw [integral_fintype .of_finite]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : ℙ (R ⁻¹' { r }) = 0
  · simp [Measure.real, Measure.map_apply hR (.singleton r), hr]
  simp_rw [smul_eq_mul]
  gcongr
  have : IsProbabilityMeasure (ℙ[|R ⁻¹' { r }]) := cond_isProbabilityMeasure hr
  apply construct_good' p X₁ X₂ h_min hT hT₁ hT₂ hT₃


-- @@ L463-463 verbatim
end construct_good


-- @@ L465-487 expanded
include hX₁ hX₂ h_min h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂' in
/-- If `d[X₁ ; X₂] > 0` then there are `G`-valued random variables `X₁', X₂'` such that
Phrased in the contrapositive form for convenience of proof. -/
theorem tau_strictly_decreases_aux [IsProbabilityMeasure (ℙ : Measure Ω)] [Module (ZMod 2) G]
    (hpη : p.η = 1 / 9) : rdist X₁ X₂ volume volume = 0 :=
  by
  have h0 :=
    cond_construct_good p X₁ X₂ h_min (sum_uvw_eq_zero ..) (show Measurable (X₁ + X₂) by fun_prop)
      (show Measurable (X₁' + X₂) by fun_prop) (show Measurable (X₁' + X₁) by fun_prop)
      (show Measurable (X₁ + X₂ + X₁' + X₂') by fun_prop)
  have h1 := sum_condMutual_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have h2 := sum_dist_diff_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have h_indep' : iIndepFun ![X₁, X₂, X₂', X₁'] :=
    by
    let σ : Fin 4 ≃ Fin 4 :=
      { toFun := ![0, 1, 3, 2]
        invFun := ![0, 1, 3, 2]
        left_inv := by intro i; fin_cases i <;> rfl
        right_inv := by intro i; fin_cases i <;> rfl }
    refine .of_precomp σ.symm.surjective ?_
    convert h_indep using 1
    ext i; fin_cases i <;> rfl
  have h3 := first_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep' h_min
  have hk : 0 ≤ rdist X₁ X₂ volume volume := rdist_nonneg hX₁ hX₂
  rw [hpη] at *
  linarith only [hk, h0, h1, h2, h3]

