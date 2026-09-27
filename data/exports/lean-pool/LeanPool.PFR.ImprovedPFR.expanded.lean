/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.PFR.TauFunctional
import LeanPool.PFR.Endgame
import LeanPool.PFR.Fibring
import LeanPool.PFR.FirstEstimate
import LeanPool.PFR.ForMathlib.Entropy.Group
import LeanPool.PFR.ForMathlib.FourVariables
import LeanPool.PFR.HundredPercent
import LeanPool.PFR.SecondEstimate
import LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.ConditionalProbability
import LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov


-- @@ L23-27 verbatim
/-!
# Improved PFR

An improvement to PFR that lowers the exponent from 12 to 11.
-/


-- @@ L29-32 verbatim
open scoped ZhangYeungPFR


/- In this file the power notation will always mean the base and exponent are real numbers. -/

-- @@ L33-33 verbatim
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))


-- @@ L35-35 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L37-37 verbatim
section GeneralInequality

-- @@ L38-39 verbatim
variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [Module (ZMod 2) G] [MeasurableAdd₂ G]


-- @@ L41-41 verbatim
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]


-- @@ L43-43 verbatim
variable {Ω₀ : Type*} [MeasureSpace Ω₀] [IsProbabilityMeasure (ℙ : Measure Ω₀)]


-- @@ L45-45 verbatim
variable (Y : Ω₀ → G) (hY : Measurable Y)


-- @@ L47-48 verbatim
variable (Z₁ Z₂ Z₃ Z₄ : Ω → G)
  (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) (hZ₄ : Measurable Z₄)


-- @@ L50-50 verbatim
variable (h_indep : iIndepFun ![Z₁, Z₂, Z₃, Z₄])


-- @@ L52-52 verbatim
local notation3 "Sum" => Z₁ + Z₂ + Z₃ + Z₄


-- @@ L54-89 expanded
include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
public lemma gen_ineq_aux1 :
    condRuzsaDist' Y (Z₁ + Z₂) ⟨Z₁ + Z₃, Sum⟩ volume volume ≤
      rdist Y Z₁ volume volume +
          (rdist Z₁ Z₂ volume volume + rdist Z₁ Z₃ volume volume + rdist Z₂ Z₄ volume volume -
              condRuzsaDist Z₁ (Z₁ + Z₂) Z₃ (Z₃ + Z₄) volume volume) /
            2 +
        (entropy (Z₁ + Z₂) volume - entropy (Z₃ + Z₄) volume + entropy Z₂ volume -
            entropy Z₁ volume) /
          4 :=
  by
  have hS : Measurable Sum := by fun_prop
  have C :
    rdist Z₁ Z₃ volume volume + rdist Z₂ Z₄ volume volume =
      rdist (Z₁ + Z₂) (Z₃ + Z₄) volume volume +
          condRuzsaDist Z₁ (Z₁ + Z₂) Z₃ (Z₃ + Z₄) volume volume +
        condMutualInfo (Z₁ + Z₂) (Z₁ + Z₃) Sum volume :=
    by
    have M :
      rdist Z₃ Z₁ volume volume + rdist Z₄ Z₂ volume volume =
        rdist (Z₃ + Z₄) (Z₁ + Z₂) volume volume +
            condRuzsaDist Z₃ (Z₃ + Z₄) Z₁ (Z₁ + Z₂) volume volume +
          condMutualInfo (Z₃ + Z₁) (Z₁ + Z₂) (Z₃ + Z₁ + Z₄ + Z₂) volume :=
      by
      apply sum_of_rdist_eq_char_2 ![Z₃, Z₁, Z₄, Z₂] h_indep.reindex_four_cadb (fun i ↦ ?_)
      fin_cases i <;> assumption
    have J1 : Z₃ + Z₁ + Z₄ + Z₂ = Z₁ + Z₂ + Z₃ + Z₄ := by abel
    have J2 : Z₃ + Z₁ = Z₁ + Z₃ := by abel
    simp_rw [J1, J2] at M
    simpa only [rdist_symm (Y := Z₁), rdist_symm (X := Z₄), rdist_symm (X := Z₃ + Z₄),
      condRuzsaDist_symm (Z := Z₃ + Z₄) (W := Z₁ + Z₂) (by fun_prop) (by fun_prop),
      condMutualInfo_comm (X := Z₁ + Z₃) (Y := Z₁ + Z₂) (by fun_prop) (by fun_prop)] using M
  calc
    condRuzsaDist' Y (Z₁ + Z₂) ⟨Z₁ + Z₃, Sum⟩ volume volume ≤
        condRuzsaDist' Y (Z₁ + Z₂) Sum volume volume +
          condMutualInfo (Z₁ + Z₂) (Z₁ + Z₃) Sum volume / 2 :=
      condRuzsaDist_le'_prod (ℙ : Measure Ω₀) (ℙ : Measure Ω) hY (hZ₁.add hZ₂) (hZ₁.add hZ₃) hS
    _ ≤
        rdist Y (Z₁ + Z₂) volume volume +
            (rdist (Z₁ + Z₂) (Z₃ + Z₄) volume volume +
                condMutualInfo (Z₁ + Z₂) (Z₁ + Z₃) Sum volume) /
              2 +
          (entropy (Z₁ + Z₂) volume - entropy (Z₃ + Z₄) volume) / 4 :=
      by
      have I : IndepFun (Z₁ + Z₂) (Z₃ + Z₄) := by
        exact
          h_indep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption) 0 1 2 3
            (by decide) (by decide) (by decide) (by decide)
      grind [condRuzsaDist_diff_le''' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY (hZ₁.add hZ₂)
            (hZ₃.add hZ₄) I]
    _ ≤
        rdist Y Z₁ volume volume +
            (rdist Z₁ Z₂ volume volume + rdist (Z₁ + Z₂) (Z₃ + Z₄) volume volume +
                condMutualInfo (Z₁ + Z₂) (Z₁ + Z₃) Sum volume) /
              2 +
          (entropy (Z₁ + Z₂) volume - entropy (Z₃ + Z₄) volume + entropy Z₂ volume -
              entropy Z₁ volume) /
            4 :=
      by
      have I : IndepFun Z₁ Z₂ := by exact h_indep.indepFun (show 0 ≠ 1 by decide)
      have A := condRuzsaDist_diff_le' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY hZ₁ hZ₂ I
      linarith
    _ = _ := by linarith


-- @@ L91-210 expanded
include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
public lemma gen_ineq_aux2 :
    condRuzsaDist' Y (Z₁ + Z₂) ⟨Z₁ + Z₃, Sum⟩ volume volume ≤
      rdist Y Z₁ volume volume +
          (rdist Z₁ Z₃ volume volume + condRuzsaDist Z₁ (Z₁ + Z₃) Z₂ (Z₂ + Z₄) volume volume) / 2 +
        (condEntropy Z₂ (Z₂ + Z₄) volume - condEntropy Z₁ (Z₁ + Z₃) volume + entropy Z₁ volume -
            entropy Z₃ volume) /
          4 :=
  by
  cases nonempty_fintype G
  have hS : Measurable Sum := by fun_prop
  have I : IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩) :=
    by
    refine
      (h_indep.indepFun_prodMk_prodMk ?_ 0 2 1 3 (by decide) (by decide) (by decide) (by decide))
    intro i; fin_cases i <;> assumption
  calc
    condRuzsaDist' Y (Z₁ + Z₂) ⟨Z₁ + Z₃, Sum⟩ volume volume =
        condRuzsaDist' Y (Z₁ + Z₂) ⟨Z₁ + Z₃, Z₂ + Z₄⟩ volume volume :=
      by
      let e : G × G ≃ G × G :=
        { toFun p := ⟨p.1, p.2 - p.1⟩
          invFun p := ⟨p.1, p.2 + p.1⟩
          left_inv := by intro ⟨a, b⟩; simp
          right_inv := by intro ⟨a, b⟩; simp }
      convert!
        (condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂) (⟨Z₁ + Z₃, Sum⟩) e
            (hZ₁.add hZ₂) ((hZ₁.add hZ₃).prodMk hS) (.of_discrete (f := e)) e.injective).symm
      simp only [e, Pi.add_apply, Equiv.coe_fn_mk, Function.comp_apply]
      abel
    _ =
        ∑ w,
          (Measure.real ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' { w })) *
            rdist Y (Z₁ + Z₂) ℙ ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w] :=
      by
      rw [condRuzsaDist'_eq_sum']
      · exact hZ₁.add hZ₂
      · exact (hZ₁.add hZ₃).prodMk (hZ₂.add hZ₄)
    _ ≤
        ∑ w,
          Measure.real ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' { w }) *
            (rdist Y Z₁ ℙ ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w] +
                  rdist Z₁ Z₂ ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' { w }] ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' { w }] /
                    2 +
                entropy Z₂ (ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]) / 4 -
              entropy Z₁ (ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]) / 4) :=
      by
      apply Finset.sum_le_sum (fun w _h'w ↦ ?_)
      rcases eq_or_ne (Measure.real ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' { w })) 0 with hw | hw
      · simp [hw]
      gcongr
      have : IsProbabilityMeasure (ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]) :=
        cond_isProbabilityMeasure_of_real hw
      have : IndepFun Z₁ Z₂ (ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' { w }]) :=
        by
        have E :
          (⟨Z₁, Z₃⟩) ⁻¹' {p | p.1 + p.2 = w.1} ∩ (⟨Z₂, Z₄⟩) ⁻¹' {p | p.1 + p.2 = w.2} =
            ⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' { w } :=
          by aesop
        have I :
          IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩)
            (ℙ[|(⟨Z₁, Z₃⟩) ⁻¹' {p | p.1 + p.2 = w.1} ∩ (⟨Z₂, Z₄⟩) ⁻¹' {p | p.1 + p.2 = w.2}]) :=
          I.cond (measurable_add (.singleton w.1)) (measurable_add (.singleton w.2))
            (hZ₁.prodMk hZ₃) (hZ₂.prodMk hZ₄)
        rw [E] at I
        exact I.comp measurable_fst measurable_fst
      have :=
        condRuzsaDist_diff_le' (ℙ : Measure Ω₀) (μ' := ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]) hY hZ₁ hZ₂ this
      linarith
    _ =
        condRuzsaDist' Y Z₁ (Z₁ + Z₃) volume volume +
              condRuzsaDist Z₁ (Z₁ + Z₃) Z₂ (Z₂ + Z₄) volume volume / 2 +
            condEntropy Z₂ (Z₂ + Z₄) volume / 4 -
          condEntropy Z₁ (Z₁ + Z₃) volume / 4 :=
      by
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      congr
      · rw [← condRuzsaDist'_eq_sum' hZ₁ (by fun_prop)]
        apply condRuszaDist_prod_eq_of_indepFun hY hZ₁ (by fun_prop) (by fun_prop)
        exact I.comp (measurable_fst.prodMk measurable_add) measurable_add
      · simp_rw [← mul_div_assoc, ← Finset.sum_div]
        rw [condRuzsaDist_eq_sum' hZ₁ (by fun_prop) hZ₂ (by fun_prop), Fintype.sum_prod_type]
        congr with x
        congr with y
        have : (⟨Z₁ + Z₃, Z₂ + Z₄⟩) ⁻¹' {(x, y)} = (Z₁ + Z₃) ⁻¹' { x } ∩ (Z₂ + Z₄) ⁻¹' { y } := by
          ext p; simp
        rw [this]
        have J : IndepFun (Z₁ + Z₃) (Z₂ + Z₄) := by exact I.comp measurable_add measurable_add
        rw [J.measureReal_inter_preimage_eq_mul (.singleton x) (.singleton y)]
        rcases eq_or_ne (Measure.real ℙ ((Z₁ + Z₃) ⁻¹' { x })) 0 with h1 | h1
        · simp [h1]
        rcases eq_or_ne (Measure.real ℙ ((Z₂ + Z₄) ⁻¹' { y })) 0 with h2 | h2
        · simp [h2]
        congr 1
        have A :
          IdentDistrib Z₁ Z₁ (ℙ[|(Z₁ + Z₃) ⁻¹' { x } ∩ (Z₂ + Z₄) ⁻¹' { y }])
            (ℙ[|(Z₁ + Z₃) ⁻¹' { x }]) :=
          by
          rw [←
            cond_cond_eq_cond_inter' (by exact hZ₁.add hZ₃ (.singleton _))
              (by exact hZ₂.add hZ₄ (.singleton _)) (by finiteness)]
          have : IsProbabilityMeasure (ℙ[|(Z₁ + Z₃) ⁻¹' { x }]) :=
            cond_isProbabilityMeasure_of_real h1
          apply (IndepFun.identDistrib_cond _ (.singleton _) hZ₁ (by fun_prop) _).symm
          · have : IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩) (ℙ[|(⟨Z₁, Z₃⟩) ⁻¹' {p | p.1 + p.2 = x}]) :=
              I.cond_left (measurable_add (.singleton x)) (hZ₁.prodMk hZ₃)
            exact this.comp measurable_fst measurable_add
          · rw [cond_apply, J.measure_inter_preimage_eq_mul _ _ (.singleton x) (.singleton y)]
            · simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h1 h2
              simp [h1, h2]
            · exact hZ₁.add hZ₃ (.singleton _)
        have B :
          IdentDistrib Z₂ Z₂ (ℙ[|(Z₁ + Z₃) ⁻¹' { x } ∩ (Z₂ + Z₄) ⁻¹' { y }])
            (ℙ[|(Z₂ + Z₄) ⁻¹' { y }]) :=
          by
          rw [Set.inter_comm, ←
            cond_cond_eq_cond_inter' (by exact hZ₂.add hZ₄ (.singleton _))
              (by exact hZ₁.add hZ₃ (.singleton _)) (by finiteness)]
          have : IsProbabilityMeasure (ℙ[|(Z₂ + Z₄) ⁻¹' { y }]) :=
            cond_isProbabilityMeasure_of_real h2
          apply (IndepFun.identDistrib_cond _ (.singleton _) hZ₂ (hZ₁.add hZ₃) _).symm
          · have : IndepFun (⟨Z₂, Z₄⟩) (⟨Z₁, Z₃⟩) (ℙ[|(⟨Z₂, Z₄⟩) ⁻¹' {p | p.1 + p.2 = y}]) :=
              I.symm.cond_left (measurable_add (.singleton y)) (hZ₂.prodMk hZ₄)
            exact this.comp measurable_fst measurable_add
          · rw [cond_apply (hZ₂.add hZ₄ (.singleton y)),
              J.symm.measure_inter_preimage_eq_mul _ _ (.singleton _) (.singleton _)]
            simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h1 h2
            simp [h1, h2]
        exact A.rdist_congr B
      · have I1 : condEntropy Z₂ (Z₂ + Z₄) volume = condEntropy Z₂ ⟨Z₂ + Z₄, Z₁ + Z₃⟩ volume :=
          by
          apply (condEntropy_prod_eq_of_indepFun hZ₂ (by fun_prop) (by fun_prop) _).symm
          exact I.symm.comp (measurable_fst.prodMk measurable_add) measurable_add
        have I2 :
          condEntropy Z₂ ⟨Z₂ + Z₄, Z₁ + Z₃⟩ volume = condEntropy Z₂ ⟨Z₁ + Z₃, Z₂ + Z₄⟩ volume :=
          condEntropy_of_injective' _ hZ₂ ((hZ₁.add hZ₃).prodMk (hZ₂.add hZ₄)) _
            (Equiv.prodComm G G).injective ((hZ₂.add hZ₄).prodMk (hZ₁.add hZ₃))
        rw [I1, I2, condEntropy_eq_sum_fintype _ _ _ (by fun_prop)]
        simp_rw [← mul_div_assoc, Finset.sum_div]
      · have : condEntropy Z₁ (Z₁ + Z₃) volume = condEntropy Z₁ ⟨Z₁ + Z₃, Z₂ + Z₄⟩ volume :=
          by
          apply (condEntropy_prod_eq_of_indepFun hZ₁ (hZ₁.add hZ₃) (hZ₂.add hZ₄) _).symm
          exact I.comp (measurable_fst.prodMk measurable_add) measurable_add
        rw [this, condEntropy_eq_sum_fintype _ _ _ (by fun_prop)]
        simp_rw [← mul_div_assoc, Finset.sum_div]
    _ ≤
        (rdist Y Z₁ volume volume + rdist Z₁ Z₃ volume volume / 2 + entropy Z₁ volume / 4 -
                entropy Z₃ volume / 4) +
              condRuzsaDist Z₁ (Z₁ + Z₃) Z₂ (Z₂ + Z₄) volume volume / 2 +
            condEntropy Z₂ (Z₂ + Z₄) volume / 4 -
          condEntropy Z₁ (Z₁ + Z₃) volume / 4 :=
      by
      gcongr
      have I : IndepFun Z₁ Z₃ := by exact h_indep.indepFun (show 0 ≠ 2 by decide)
      have := condRuzsaDist_diff_le''' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY hZ₁ hZ₃ I
      linarith
    _ = _ := by ring


-- @@ L212-227 expanded
include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
/-- Let `Z₁, Z₂, Z₃, Z₄` be independent `G`-valued random variables, and let `Y` be another
`G`-valued random variable. Set `S := Z₁ + Z₂ + Z₃ + Z₄`. Then
`d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] - d[Y # Z₁] ≤`
`(d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4`
`+ (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4`
`+ (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8`.
-/
public lemma gen_ineq_00 :
    condRuzsaDist' Y (Z₁ + Z₂) ⟨Z₁ + Z₃, Sum⟩ volume volume - rdist Y Z₁ volume volume ≤
      (rdist Z₁ Z₂ volume volume + 2 * rdist Z₁ Z₃ volume volume + rdist Z₂ Z₄ volume volume) / 4 +
          (condRuzsaDist Z₁ (Z₁ + Z₃) Z₂ (Z₂ + Z₄) volume volume -
              condRuzsaDist Z₁ (Z₁ + Z₂) Z₃ (Z₃ + Z₄) volume volume) /
            4 +
        (entropy (Z₁ + Z₂) volume - entropy (Z₃ + Z₄) volume + entropy Z₂ volume -
                entropy Z₃ volume +
              condEntropy Z₂ (Z₂ + Z₄) volume -
            condEntropy Z₁ (Z₁ + Z₃) volume) /
          8 :=
  by
  have I1 := gen_ineq_aux1 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep
  have I2 := gen_ineq_aux2 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep
  linarith


-- @@ L229-245 expanded
include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
/-- Other version of `gen_ineq_00`, in which we switch to the complement in the second term. -/
public lemma gen_ineq_01 :
    condRuzsaDist' Y (Z₁ + Z₂) ⟨Z₂ + Z₄, Sum⟩ volume volume - rdist Y Z₁ volume volume ≤
      (rdist Z₁ Z₂ volume volume + 2 * rdist Z₁ Z₃ volume volume + rdist Z₂ Z₄ volume volume) / 4 +
          (condRuzsaDist Z₁ (Z₁ + Z₃) Z₂ (Z₂ + Z₄) volume volume -
              condRuzsaDist Z₁ (Z₁ + Z₂) Z₃ (Z₃ + Z₄) volume volume) /
            4 +
        (entropy (Z₁ + Z₂) volume - entropy (Z₃ + Z₄) volume + entropy Z₂ volume -
                entropy Z₃ volume +
              condEntropy Z₂ (Z₂ + Z₄) volume -
            condEntropy Z₁ (Z₁ + Z₃) volume) /
          8 :=
  by
  convert gen_ineq_00 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep using 2
  let e : G × G ≃ G × G :=
    { toFun p := ⟨p.2 - p.1, p.2⟩
      invFun p := ⟨-p.1 + p.2, p.2⟩
      left_inv := by intro ⟨a, b⟩; simp
      right_inv := by intro ⟨a, b⟩; simp }
  convert!
    (condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂) (⟨Z₁ + Z₃, Sum⟩) e
      (by fun_prop) (by fun_prop) (by fun_prop) e.injective) with
    p
  simp only [e, Pi.add_apply, Equiv.coe_fn_mk, Function.comp_apply]
  abel


-- @@ L247-269 expanded
include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
/-- Other version of `gen_ineq_00`, in which we switch to the complement in the first term. -/
public lemma gen_ineq_10 :
    condRuzsaDist' Y (Z₃ + Z₄) ⟨Z₁ + Z₃, Sum⟩ volume volume - rdist Y Z₁ volume volume ≤
      (rdist Z₁ Z₂ volume volume + 2 * rdist Z₁ Z₃ volume volume + rdist Z₂ Z₄ volume volume) / 4 +
          (condRuzsaDist Z₁ (Z₁ + Z₃) Z₂ (Z₂ + Z₄) volume volume -
              condRuzsaDist Z₁ (Z₁ + Z₂) Z₃ (Z₃ + Z₄) volume volume) /
            4 +
        (entropy (Z₁ + Z₂) volume - entropy (Z₃ + Z₄) volume + entropy Z₂ volume -
                entropy Z₃ volume +
              condEntropy Z₂ (Z₂ + Z₄) volume -
            condEntropy Z₁ (Z₁ + Z₃) volume) /
          8 :=
  by
  convert gen_ineq_00 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep using 2
  have hS : Measurable Sum := by fun_prop
  let e : G × G ≃ G × G := Equiv.prodComm G G
  have A : e ∘ ⟨Z₁ + Z₃, Sum⟩ = ⟨Sum, Z₁ + Z₃⟩ := by ext p <;> rfl
  rw [←
    condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₃ + Z₄) (⟨Z₁ + Z₃, Sum⟩) e
      (by fun_prop) (by fun_prop) (by fun_prop) e.injective,
    ←
    condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂) (⟨Z₁ + Z₃, Sum⟩) e
      (by fun_prop) (by fun_prop) (by fun_prop) e.injective,
    A, condRuzsaDist'_prod_eq_sum _ _ (by fun_prop) hS (by fun_prop),
    condRuzsaDist'_prod_eq_sum _ _ (by fun_prop) hS (by fun_prop)]
  congr with w
  rcases eq_or_ne (Measure.real ℙ ((Z₁ + Z₃) ⁻¹' { w })) 0 with hw | hw
  · simp [hw]
  have : IsProbabilityMeasure (ℙ[|(Z₁ + Z₃) ⁻¹' { w }]) := cond_isProbabilityMeasure_of_real hw
  have : Sum = (Z₁ + Z₂) + (Z₃ + Z₄) := by abel
  rw [this, condRuzsaDist'_of_inj_map' hY (by fun_prop) (by fun_prop)]


-- @@ L271-271 verbatim
end GeneralInequality


-- @@ L273-273 verbatim
section MainEstimates


-- @@ L275-275 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L277-278 verbatim
variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [Module (ZMod 2) G]


-- @@ L280-281 verbatim
variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]


-- @@ L283-283 verbatim
variable {p : refPackage Ω₀₁ Ω₀₂ G}


-- @@ L285-285 verbatim
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]


-- @@ L287-288 verbatim
variable {X₁ X₂ X₁' X₂' : Ω → G}
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')


-- @@ L290-290 verbatim
variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')


-- @@ L292-292 verbatim
variable (h_indep : iIndepFun ![X₁, X₂, X₂', X₁'])


-- @@ L294-294 verbatim
variable (h_min : tauMinimizes p X₁ X₂)


-- @@ L296-297 expanded
/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => rdist X₁ X₂ volume volume


-- @@ L299-300 verbatim
/-- `U := X₁ + X₂` -/
local notation3 "U" => X₁ + X₂


-- @@ L302-303 verbatim
/-- `V := X₁' + X₂` -/
local notation3 "V" => X₁' + X₂


-- @@ L305-306 verbatim
/-- `W := X₁' + X₁` -/
local notation3 "W" => X₁' + X₁


-- @@ L308-309 verbatim
/-- `S := X₁ + X₂ + X₁' + X₂'` -/
local notation3 "S" => X₁ + X₂ + X₁' + X₂'


-- @@ L311-313 expanded
/-- `I₁ := I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₂` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => condMutualInfo (X₁ + X₂) (X₁' + X₂) (X₁ + X₂ + X₁' + X₂') volume


-- @@ L315-317 expanded
/-- `I₂ := I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₁` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₂" => condMutualInfo (X₁ + X₂) (X₁' + X₁) (X₁ + X₂ + X₁' + X₂') volume


-- @@ L319-320 expanded
local notation3:max "c[" A "; " μ " # " B " ; " μ' "]" =>
  rdist p.X₀₁ A ℙ μ - rdist p.X₀₁ X₁ volume volume +
    (rdist p.X₀₂ B ℙ μ' - rdist p.X₀₂ X₂ volume volume)


-- @@ L322-323 expanded
local notation3:max "c[" A " # " B "]" =>
  rdist p.X₀₁ A volume volume - rdist p.X₀₁ X₁ volume volume +
    (rdist p.X₀₂ B volume volume - rdist p.X₀₂ X₂ volume volume)


-- @@ L325-326 expanded
local notation3:max "c[" A " | " B " # " C " | " D "]" =>
  condRuzsaDist' p.X₀₁ A B volume volume - rdist p.X₀₁ X₁ volume volume +
    (condRuzsaDist' p.X₀₂ C D volume volume - rdist p.X₀₂ X₂ volume volume)


-- @@ L328-328 verbatim
section aux


-- @@ L330-330 verbatim
variable {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]

-- @@ L331-331 verbatim
variable {T₁ T₂ T₃ : Ω' → G} (hT : T₁ + T₂ + T₃ = 0)

-- @@ L332-332 verbatim
variable (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)


-- @@ L334-334 expanded
local notation3:max "δ[" μ "]" => mutualInfo T₁ T₂ μ + mutualInfo T₂ T₃ μ + mutualInfo T₃ T₁ μ


-- @@ L335-335 expanded
local notation3:max "δ" =>
  mutualInfo T₁ T₂ volume + mutualInfo T₂ T₃ volume + mutualInfo T₃ T₁ volume


-- @@ L337-337 expanded
local notation3:max "ψ[" A " # " B "]" => rdist A B volume volume + p.η * (c[A # B])


-- @@ L338-339 expanded
local notation3:max "ψ[" A "; " μ " # " B " ; " μ' "]" => rdist A B μ μ' + p.η * c[A; μ # B ; μ']


-- @@ L341-394 expanded
include hT hT₁ hT₂ hT₃ h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
    [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- For any $T_1, T_2, T_3$ adding up to $0$, then $k$ is at most
$$ \delta + \eta (d[X^0_1;T_1|T_3]-d[X^0_1;X_1]) + \eta (d[X^0_2;T_2|T_3]-d[X^0_2;X_2])$$
where $\delta = I[T₁ : T₂; μ] + I[T₂ : T₃; μ] + I[T₃ : T₁; μ]$. -/
public lemma construct_good_prelim' : k ≤ δ + p.η * c[T₁ | T₃ # T₂ | T₃] :=
  by
  let sum1 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ rdist T₁ T₂ ℙ[|T₃ ⁻¹' { t }] ℙ[|T₃ ⁻¹' { t }]]
  let sum2 : ℝ :=
    (Measure.map T₃ ℙ)[fun t ↦ rdist p.X₀₁ T₁ ℙ ℙ[|T₃ ⁻¹' { t }] - rdist p.X₀₁ X₁ volume volume]
  let sum3 : ℝ :=
    (Measure.map T₃ ℙ)[fun t ↦ rdist p.X₀₂ T₂ ℙ ℙ[|T₃ ⁻¹' { t }] - rdist p.X₀₂ X₂ volume volume]
  let sum4 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ ψ[T₁; ℙ[|T₃ ⁻¹' { t }] # T₂ ; ℙ[|T₃ ⁻¹' { t }]]]
  have h2T₃ : T₃ = T₁ + T₂ := by
    calc
      T₃ = T₁ + T₂ + T₃ - T₃ := by simp [hT, ZModModule.neg_eq_self]
      _ = T₁ + T₂ := by rw [add_sub_cancel_right]
  have hP : IsProbabilityMeasure (Measure.map T₃ ℙ) := inferInstance
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
    simp_rw [mutualInfo_def] at h1 ⊢;
    linarith
      -- rewrite sum2 and sum3 as Rusza distances
      
  have h2 : sum2 = condRuzsaDist' p.X₀₁ T₁ T₃ volume volume - rdist p.X₀₁ X₁ volume volume :=
    by
    simp only [sum2, integral_sub .of_finite .of_finite, integral_const, smul_eq_mul]
    simp [condRuzsaDist'_eq_sum hT₁ hT₃,
      integral_eq_setIntegral (FiniteRange.ae_mem_toFinset _ T₃ hT₃.aemeasurable),
      setIntegral_finset _ .finset, map_measureReal_apply hT₃ (.singleton _), smul_eq_mul]
  have h3 : sum3 = condRuzsaDist' p.X₀₂ T₂ T₃ volume volume - rdist p.X₀₂ X₂ volume volume :=
    by
    simp only [sum3, integral_sub .of_finite .of_finite, integral_const, smul_eq_mul]
    simp [condRuzsaDist'_eq_sum hT₂ hT₃,
      integral_eq_setIntegral (FiniteRange.ae_mem_toFinset _ T₃ hT₃.aemeasurable),
      setIntegral_finset _ .finset, map_measureReal_apply hT₃ (.singleton _)]
      -- put all these estimates together to bound sum4
      
  have h4 :
    sum4 ≤
      δ +
        p.η *
          ((condRuzsaDist' p.X₀₁ T₁ T₃ volume volume - rdist p.X₀₁ X₁ volume volume) +
            (condRuzsaDist' p.X₀₂ T₂ T₃ volume volume - rdist p.X₀₂ X₂ volume volume)) :=
    by
    have : sum4 = sum1 + p.η * (sum2 + sum3) := by
      simp only [sum1, sum2, sum3, sum4, integral_add .of_finite .of_finite, integral_const_mul]
    rw [this, h2, h3, add_assoc, mul_add]
    linarith
  have hk : k ≤ sum4 :=
    by
    suffices (Measure.map T₃ ℙ)[fun _ ↦ k] ≤ sum4 by simpa using this
    refine integral_mono_ae .of_finite .of_finite <| ae_iff_of_countable.2 fun t ht ↦ ?_
    have : IsProbabilityMeasure (ℙ[|T₃ ⁻¹' { t }]) :=
      cond_isProbabilityMeasure (by simpa [hT₃] using ht)
    dsimp only
    linarith only [distance_ge_of_min' (μ := ℙ[|T₃ ⁻¹' { t }]) (μ' := ℙ[|T₃ ⁻¹' { t }]) p h_min hT₁
        hT₂]
  exact hk.trans h4


-- @@ L396-396 verbatim
open Module


-- @@ L398-429 expanded
include hT hT₁ hT₂ hT₃ h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
    [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- In fact $k$ is at most
 $$ \delta + \frac{\eta}{6} \sum_{i=1}^2 \sum_{1 \leq j,l \leq 3; j \neq l}
     (d[X^0_i;T_j|T_l] - d[X^0_i; X_i]).$$
-/
public lemma construct_good_improved' :
    k ≤
      δ +
        (p.η / 6) *
          ((condRuzsaDist' p.X₀₁ T₁ T₂ volume volume - rdist p.X₀₁ X₁ volume volume) +
                                (condRuzsaDist' p.X₀₁ T₁ T₃ volume volume -
                                  rdist p.X₀₁ X₁ volume volume) +
                              (condRuzsaDist' p.X₀₁ T₂ T₁ volume volume -
                                rdist p.X₀₁ X₁ volume volume) +
                            (condRuzsaDist' p.X₀₁ T₂ T₃ volume volume -
                              rdist p.X₀₁ X₁ volume volume) +
                          (condRuzsaDist' p.X₀₁ T₃ T₁ volume volume -
                            rdist p.X₀₁ X₁ volume volume) +
                        (condRuzsaDist' p.X₀₁ T₃ T₂ volume volume - rdist p.X₀₁ X₁ volume volume) +
                      (condRuzsaDist' p.X₀₂ T₁ T₂ volume volume - rdist p.X₀₂ X₂ volume volume) +
                    (condRuzsaDist' p.X₀₂ T₁ T₃ volume volume - rdist p.X₀₂ X₂ volume volume) +
                  (condRuzsaDist' p.X₀₂ T₂ T₁ volume volume - rdist p.X₀₂ X₂ volume volume) +
                (condRuzsaDist' p.X₀₂ T₂ T₃ volume volume - rdist p.X₀₂ X₂ volume volume) +
              (condRuzsaDist' p.X₀₂ T₃ T₁ volume volume - rdist p.X₀₂ X₂ volume volume) +
            (condRuzsaDist' p.X₀₂ T₃ T₂ volume volume - rdist p.X₀₂ X₂ volume volume)) :=
  by
  have I1 : mutualInfo T₂ T₁ volume = mutualInfo T₁ T₂ volume := mutualInfo_comm hT₂ hT₁ _
  have I2 : mutualInfo T₃ T₁ volume = mutualInfo T₁ T₃ volume := mutualInfo_comm hT₃ hT₁ _
  have I3 : mutualInfo T₃ T₂ volume = mutualInfo T₂ T₃ volume := mutualInfo_comm hT₃ hT₂ _
  have Z123 := construct_good_prelim' h_min hT hT₁ hT₂ hT₃
  have h132 : T₁ + T₃ + T₂ = 0 := by rw [← hT]; abel
  have Z132 := construct_good_prelim' h_min h132 hT₁ hT₃ hT₂
  have h213 : T₂ + T₁ + T₃ = 0 := by rw [← hT]; abel
  have Z213 := construct_good_prelim' h_min h213 hT₂ hT₁ hT₃
  have h231 : T₂ + T₃ + T₁ = 0 := by rw [← hT]; abel
  have Z231 := construct_good_prelim' h_min h231 hT₂ hT₃ hT₁
  have h312 : T₃ + T₁ + T₂ = 0 := by rw [← hT]; abel
  have Z312 := construct_good_prelim' h_min h312 hT₃ hT₁ hT₂
  have h321 : T₃ + T₂ + T₁ = 0 := by rw [← hT]; abel
  have Z321 := construct_good_prelim' h_min h321 hT₃ hT₂ hT₁
  simp only [I1, I2, I3] at Z123 Z132 Z213 Z231 Z312 Z321
  linarith


-- @@ L431-449 expanded
include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
    [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Rephrase `construct_good_improved'` with an explicit probability measure, as we will
apply it to (varying) conditional measures. -/
public lemma construct_good_improved'' {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    [IsProbabilityMeasure μ] {T₁ T₂ T₃ : Ω' → G} (hT : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁)
    (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) :
    k ≤
      mutualInfo T₁ T₂ μ + mutualInfo T₂ T₃ μ + mutualInfo T₃ T₁ μ +
        (p.η / 6) *
          ((condRuzsaDist' p.X₀₁ T₁ T₂ ℙ μ - rdist p.X₀₁ X₁ volume volume) +
                                (condRuzsaDist' p.X₀₁ T₁ T₃ ℙ μ - rdist p.X₀₁ X₁ volume volume) +
                              (condRuzsaDist' p.X₀₁ T₂ T₁ ℙ μ - rdist p.X₀₁ X₁ volume volume) +
                            (condRuzsaDist' p.X₀₁ T₂ T₃ ℙ μ - rdist p.X₀₁ X₁ volume volume) +
                          (condRuzsaDist' p.X₀₁ T₃ T₁ ℙ μ - rdist p.X₀₁ X₁ volume volume) +
                        (condRuzsaDist' p.X₀₁ T₃ T₂ ℙ μ - rdist p.X₀₁ X₁ volume volume) +
                      (condRuzsaDist' p.X₀₂ T₁ T₂ ℙ μ - rdist p.X₀₂ X₂ volume volume) +
                    (condRuzsaDist' p.X₀₂ T₁ T₃ ℙ μ - rdist p.X₀₂ X₂ volume volume) +
                  (condRuzsaDist' p.X₀₂ T₂ T₁ ℙ μ - rdist p.X₀₂ X₂ volume volume) +
                (condRuzsaDist' p.X₀₂ T₂ T₃ ℙ μ - rdist p.X₀₂ X₂ volume volume) +
              (condRuzsaDist' p.X₀₂ T₃ T₁ ℙ μ - rdist p.X₀₂ X₂ volume volume) +
            (condRuzsaDist' p.X₀₂ T₃ T₂ ℙ μ - rdist p.X₀₂ X₂ volume volume)) :=
  by
  let M : MeasureSpace Ω' := ⟨μ⟩
  exact construct_good_improved' h_min hT hT₁ hT₂ hT₃


-- @@ L451-451 verbatim
end aux


-- @@ L453-492 expanded
include hX₁ hX₂ hX₁' hX₂' h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] in
/-- $k$ is at most
$$ \leq I(U : V \, | \, S) + I(V : W \, | \,S) + I(W : U \, | \, S) + \frac{\eta}{6}
\sum_{i=1}^2 \sum_{A,B \in \{U,V,W\}: A \neq B} (d[X^0_i;A|B,S] - d[X^0_i; X_i]).$$
-/
public lemma averaged_construct_good :
    k ≤
      (condMutualInfo U V S volume + condMutualInfo V W S volume + condMutualInfo W U S volume) +
        p.η / 6 *
          (((condRuzsaDist' p.X₀₁ U ⟨V, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
                      (condRuzsaDist' p.X₀₁ U ⟨W, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
                    (condRuzsaDist' p.X₀₁ V ⟨U, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
                  (condRuzsaDist' p.X₀₁ V ⟨W, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
                (condRuzsaDist' p.X₀₁ W ⟨U, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
              (condRuzsaDist' p.X₀₁ W ⟨V, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume)) +
            ((condRuzsaDist' p.X₀₂ U ⟨V, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
                      (condRuzsaDist' p.X₀₂ U ⟨W, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
                    (condRuzsaDist' p.X₀₂ V ⟨U, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
                  (condRuzsaDist' p.X₀₂ V ⟨W, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
                (condRuzsaDist' p.X₀₂ W ⟨U, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
              (condRuzsaDist' p.X₀₂ W ⟨V, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume))) :=
  by
  cases nonempty_fintype G
  have hS : Measurable S := by fun_prop
  have hU : Measurable U := by fun_prop
  have hV : Measurable V := by fun_prop
  have hW : Measurable W := by fun_prop
  have hUVW : U + V + W = 0 := sum_uvw_eq_zero X₁ X₂ X₁'
  have hz (a : ℝ) : a = ∑ z, (Measure.real ℙ (S ⁻¹' { z })) * a :=
    by
    rw [← Finset.sum_mul, sum_measureReal_preimage_singleton]
    · simp only [Finset.coe_univ, Set.preimage_univ, probReal_univ, one_mul]
    · intro y hy
      apply hS
      exact measurableSet_singleton y
  rw [hz k, hz (rdist p.X₀₁ X₁ volume volume), hz (rdist p.X₀₂ X₂ volume volume)]
  simp only [condMutualInfo_eq_sum' hS, ← Finset.sum_add_distrib, ← mul_add,
    condRuzsaDist'_prod_eq_sum', hU, hS, hV, hW, ← Finset.sum_sub_distrib, ← mul_sub,
    mul_comm (p.η / 6)]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum (fun i _hi ↦ ?_)
  rcases eq_or_ne (Measure.real ℙ (S ⁻¹' { i })) 0 with h'i | h'i
  · simp [h'i]
  rw [mul_assoc, ← mul_add]
  gcongr
  have : IsProbabilityMeasure (ℙ[|S ⁻¹' { i }]) := cond_isProbabilityMeasure_of_real h'i
  linarith [construct_good_improved'' h_min (ℙ[|S ⁻¹' { i }]) hUVW hU hV hW]


-- @@ L494-506 expanded
include h₁ h₂ h_indep in
omit [AddCommGroup G] [Finite G] [MeasurableSingletonClass G] [Module (ZMod 2) G] in
/-- Replacing either or both independent coordinates by their copies preserves their joint law. -/
private lemma identDistrib_copy_pairs :
    IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) ∧
      IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) ∧ IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) :=
  by
  exact
    ⟨h₁.symm.prodMk (IdentDistrib.refl h₂.aemeasurable_fst)
        (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one),
      (IdentDistrib.refl h₁.aemeasurable_fst).prodMk h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one),
      h₁.symm.prodMk h₂.symm (h_indep.indepFun (show 3 ≠ 2 by decide))
        (h_indep.indepFun zero_ne_one)⟩


-- @@ L508-508 verbatim
variable (p)


-- @@ L510-582 expanded
include hX₁ hX₂ hX₁' hX₂' h_indep h₁ h₂ in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] in
public lemma dist_diff_bound_1 :
    (condRuzsaDist' p.X₀₁ U ⟨V, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
                (condRuzsaDist' p.X₀₁ U ⟨W, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
              (condRuzsaDist' p.X₀₁ V ⟨U, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
            (condRuzsaDist' p.X₀₁ V ⟨W, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
          (condRuzsaDist' p.X₀₁ W ⟨U, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) +
        (condRuzsaDist' p.X₀₁ W ⟨V, S⟩ volume volume - rdist p.X₀₁ X₁ volume volume) ≤
      (16 * k + 6 * rdist X₁ X₁ volume volume + 2 * rdist X₂ X₂ volume volume) / 4 +
          (entropy (X₁ + X₁') volume - entropy (X₂ + X₂') volume) / 4 +
        (condEntropy X₂ (X₂ + X₂') volume - condEntropy X₁ (X₁ + X₁') volume) / 4 :=
  by
  obtain ⟨hFirstCopy, hSecondCopy, hBothCopies⟩ := identDistrib_copy_pairs h₁ h₂ h_indep
  have I1 := gen_ineq_01 p.X₀₁ p.hmeas1 X₁ X₂ X₂' X₁' hX₁ hX₂ hX₂' hX₁' h_indep.reindex_four_abcd
  have I2 := gen_ineq_00 p.X₀₁ p.hmeas1 X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h_indep.reindex_four_abdc
  have I3 := gen_ineq_10 p.X₀₁ p.hmeas1 X₁ X₂' X₂ X₁' hX₁ hX₂' hX₂ hX₁' h_indep.reindex_four_acbd
  have I4 := gen_ineq_10 p.X₀₁ p.hmeas1 X₁ X₂' X₁' X₂ hX₁ hX₂' hX₁' hX₂ h_indep.reindex_four_acdb
  have I5 := gen_ineq_00 p.X₀₁ p.hmeas1 X₁ X₁' X₂ X₂' hX₁ hX₁' hX₂ hX₂' h_indep.reindex_four_adbc
  have I6 := gen_ineq_01 p.X₀₁ p.hmeas1 X₁ X₁' X₂' X₂ hX₁ hX₁' hX₂' hX₂ h_indep.reindex_four_adcb
  have C1 : U + X₂' + X₁' = S := by abel
  have C2 : W + X₂ + X₂' = S := by abel
  have C3 : X₁ + X₂' + X₂ + X₁' = S := by abel
  have C4 : X₁ + X₂' + X₁' + X₂ = S := by abel
  have C5 : W + X₂' + X₂ = S := by abel
  have C7 : X₂ + X₁' = V := by abel
  have C8 : X₁ + X₁' = W := by abel
  have C9 : rdist X₁ X₂' volume volume = rdist X₁ X₂ volume volume :=
    h₂.symm.rdist_congr_right hX₁.aemeasurable
  have C10 : rdist X₂ X₁' volume volume = rdist X₁' X₂ volume volume := rdist_symm
  have C11 : rdist X₁ X₁' volume volume = rdist X₁ X₁ volume volume :=
    h₁.symm.rdist_congr_right hX₁.aemeasurable
  have C12 : rdist X₁' X₂' volume volume = rdist X₁ X₂ volume volume := h₁.symm.rdist_congr h₂.symm
  have C13 : rdist X₂ X₂' volume volume = rdist X₂ X₂ volume volume :=
    h₂.symm.rdist_congr_right hX₂.aemeasurable
  have C14 : rdist X₁' X₂ volume volume = rdist X₁ X₂ volume volume :=
    h₁.symm.rdist_congr_left hX₂.aemeasurable
  have C15 : entropy (X₁' + X₂') volume = entropy U volume :=
    by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    exact hBothCopies.comp measurable_add
  have C16 : entropy X₂' volume = entropy X₂ volume := h₂.symm.entropy_congr
  have C17 : entropy X₁' volume = entropy X₁ volume := h₁.symm.entropy_congr
  have C18 : rdist X₂' X₁' volume volume = rdist X₁' X₂' volume volume := rdist_symm
  have C19 : entropy (X₂' + X₁') volume = entropy U volume := by rw [add_comm]; exact C15
  have C20 : rdist X₂' X₂ volume volume = rdist X₂ X₂ volume volume :=
    h₂.symm.rdist_congr_left hX₂.aemeasurable
  have C21 : entropy V volume = entropy U volume :=
    by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    exact hFirstCopy.comp measurable_add
  have C22 : entropy (X₁ + X₂') volume = entropy (X₁ + X₂) volume :=
    by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    exact hSecondCopy.comp measurable_add
  have C23 : X₂' + X₂ = X₂ + X₂' := by abel
  have C24 : condEntropy X₁ (X₁ + X₂') volume = condEntropy X₁ (X₁ + X₂) volume :=
    by
    apply IdentDistrib.condEntropy_eq hX₁ (hX₁.add hX₂') hX₁ (hX₁.add hX₂)
    exact hSecondCopy.comp (measurable_fst.prodMk measurable_add)
  have C25 : condEntropy X₂ V volume = condEntropy X₂ (X₁ + X₂) volume :=
    by
    apply IdentDistrib.condEntropy_eq hX₂ (hX₁'.add hX₂) hX₂ (hX₁.add hX₂)
    exact hFirstCopy.comp (measurable_snd.prodMk measurable_add)
  have C26 : condEntropy X₂' (X₂' + X₁') volume = condEntropy X₂ (X₁ + X₂) volume :=
    by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁'.add hX₂') hX₂ (hX₁.add hX₂)
    exact hBothCopies.comp (measurable_snd.prodMk measurable_add)
  have C27 : condEntropy X₂' (X₂ + X₂') volume = condEntropy X₂ (X₂ + X₂') volume :=
    by
    conv_lhs => rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₂'.add hX₂) hX₂ (hX₂.add hX₂')
    have I : IdentDistrib (⟨X₂', X₂⟩) (⟨X₂, X₂'⟩) :=
      h₂.symm.prodMk h₂ (h_indep.indepFun (show 2 ≠ 1 by decide))
        (h_indep.indepFun (show 1 ≠ 2 by decide))
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C28 : condEntropy X₁' (X₁' + X₂') volume = condEntropy X₁ (X₁ + X₂) volume :=
    by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add hX₂') hX₁ (hX₁.add hX₂)
    exact hBothCopies.comp (measurable_fst.prodMk measurable_add)
  have C29 : condEntropy X₁' V volume = condEntropy X₁ (X₁ + X₂) volume :=
    by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add hX₂) hX₁ (hX₁.add hX₂)
    exact hFirstCopy.comp (measurable_fst.prodMk measurable_add)
  have C30 : condEntropy X₂ (X₁ + X₂) volume = condEntropy X₁ (X₁ + X₂) volume :=
    by
    have := condEntropy_of_injective ℙ hX₁ (hX₁.add hX₂) _ (fun p ↦ add_right_injective p)
    convert! this with ω
    simp [add_comm (X₁ ω), add_assoc (X₂ ω), ZModModule.add_self]
  simp only [C1, C2, C3, C4, C5, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19, C20,
    C21, C22, C23, C24, C25, C26, C27, C28, C29, C30] at I1 I2 I3 I4 I5 I6 ⊢
  linarith only [I1, I2, I3, I4, I5, I6]


-- @@ L584-665 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] in
public lemma dist_diff_bound_2 :
    ((condRuzsaDist' p.X₀₂ U ⟨V, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
                (condRuzsaDist' p.X₀₂ U ⟨W, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
              (condRuzsaDist' p.X₀₂ V ⟨U, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
            (condRuzsaDist' p.X₀₂ V ⟨W, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
          (condRuzsaDist' p.X₀₂ W ⟨U, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume) +
        (condRuzsaDist' p.X₀₂ W ⟨V, S⟩ volume volume - rdist p.X₀₂ X₂ volume volume)) ≤
      (16 * k + 6 * rdist X₂ X₂ volume volume + 2 * rdist X₁ X₁ volume volume) / 4 +
          (entropy (X₂ + X₂') volume - entropy (X₁ + X₁') volume) / 4 +
        (condEntropy X₁ (X₁ + X₁') volume - condEntropy X₂ (X₂ + X₂') volume) / 4 :=
  by
  obtain ⟨hFirstCopy, hSecondCopy, hBothCopies⟩ := identDistrib_copy_pairs h₁ h₂ h_indep
  have I1 := gen_ineq_01 p.X₀₂ p.hmeas2 X₂ X₁ X₂' X₁' hX₂ hX₁ hX₂' hX₁' h_indep.reindex_four_bacd
  have I2 := gen_ineq_00 p.X₀₂ p.hmeas2 X₂ X₁ X₁' X₂' hX₂ hX₁ hX₁' hX₂' h_indep.reindex_four_badc
  have I3 := gen_ineq_10 p.X₀₂ p.hmeas2 X₂ X₂' X₁ X₁' hX₂ hX₂' hX₁ hX₁' h_indep.reindex_four_bcad
  have I4 := gen_ineq_10 p.X₀₂ p.hmeas2 X₂ X₂' X₁' X₁ hX₂ hX₂' hX₁' hX₁ h_indep.reindex_four_bcda
  have I5 := gen_ineq_00 p.X₀₂ p.hmeas2 X₂ X₁' X₁ X₂' hX₂ hX₁' hX₁ hX₂' h_indep.reindex_four_bdac
  have I6 := gen_ineq_01 p.X₀₂ p.hmeas2 X₂ X₁' X₂' X₁ hX₂ hX₁' hX₂' hX₁ h_indep.reindex_four_bdca
  have C1 : X₂ + X₁ = X₁ + X₂ := by abel
  have C2 : X₁ + X₁' = W := by abel
  have C3 : U + X₂' + X₁' = S := by abel
  have C4 : X₂ + X₁' = V := by abel
  have C5 : X₂ + X₂' + X₁ + X₁' = S := by abel
  have C6 : X₂ + X₂' + X₁' + X₁ = S := by abel
  have C7 : V + X₁ + X₂' = S := by abel
  have C8 : V + X₂' + X₁ = S := by abel
  have C9 : rdist X₂ X₁ volume volume = rdist X₁ X₂ volume volume := rdist_symm
  have C10 : rdist X₁ X₂' volume volume = rdist X₁ X₂ volume volume :=
    h₂.symm.rdist_congr_right hX₁.aemeasurable
  have C11 : rdist X₂ X₁' volume volume = rdist X₁ X₂ volume volume :=
    by
    rw [rdist_symm]
    exact h₁.symm.rdist_congr_left hX₂.aemeasurable
  have C12 : rdist X₂' X₁' volume volume = rdist X₁' X₂' volume volume := rdist_symm
  have C13 : rdist X₂' X₁ volume volume = rdist X₁ X₂' volume volume := rdist_symm
  have C14 : rdist X₁' X₁ volume volume = rdist X₁ X₁' volume volume := rdist_symm
  have C15 : rdist X₁' X₂' volume volume = rdist X₁ X₂ volume volume := h₁.symm.rdist_congr h₂.symm
  have C16 : entropy (X₁' + X₂') volume = entropy (X₁ + X₂) volume :=
    by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    exact hBothCopies.comp measurable_add
  have C17 : entropy (X₂' + X₁') volume = entropy (X₁ + X₂) volume := by rw [add_comm]; exact C16
  have C18 : entropy X₁' volume = entropy X₁ volume := h₁.symm.entropy_congr
  have C19 : entropy X₂' volume = entropy X₂ volume := h₂.symm.entropy_congr
  have C20 : entropy (X₁ + X₂') volume = entropy (X₁ + X₂) volume :=
    by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    exact hSecondCopy.comp measurable_add
  have C21 : condEntropy X₁' W volume = condEntropy X₁ W volume :=
    by
    conv_rhs => rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add hX₁) hX₁ (hX₁.add hX₁')
    have I : IdentDistrib (⟨X₁', X₁⟩) (⟨X₁, X₁'⟩) :=
      h₁.symm.prodMk h₁ (h_indep.indepFun (show 3 ≠ 0 by decide))
        (h_indep.indepFun (show 0 ≠ 3 by decide))
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C22 : condEntropy X₂' (X₂' + X₁) volume = condEntropy X₂ (X₁ + X₂) volume :=
    by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁.add hX₂') hX₂ (hX₁.add hX₂)
    exact hSecondCopy.comp (measurable_snd.prodMk measurable_add)
  have C23 : condEntropy X₁ (X₁ + X₂') volume = condEntropy X₁ (X₁ + X₂) volume :=
    by
    apply IdentDistrib.condEntropy_eq hX₁ (hX₁.add hX₂') hX₁ (hX₁.add hX₂)
    exact hSecondCopy.comp (measurable_fst.prodMk measurable_add)
  have C24 : condEntropy X₂ V volume = condEntropy X₂ (X₁ + X₂) volume :=
    by
    apply IdentDistrib.condEntropy_eq hX₂ (hX₁'.add hX₂) hX₂ (hX₁.add hX₂)
    exact hFirstCopy.comp (measurable_snd.prodMk measurable_add)
  have C25 : condEntropy X₂' (X₂' + X₁') volume = condEntropy X₂ (X₁ + X₂) volume :=
    by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁'.add hX₂') hX₂ (hX₁.add hX₂)
    exact hBothCopies.comp (measurable_snd.prodMk measurable_add)
  have C26 : condEntropy X₁' (X₁' + X₂') volume = condEntropy X₁ (X₁ + X₂) volume :=
    by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add hX₂') hX₁ (hX₁.add hX₂)
    exact hBothCopies.comp (measurable_fst.prodMk measurable_add)
  have C27 : condEntropy X₂ (X₁ + X₂) volume = condEntropy X₁ (X₁ + X₂) volume :=
    by
    have := condEntropy_of_injective ℙ hX₁ (hX₁.add hX₂) _ (fun p ↦ add_right_injective p)
    convert! this with ω
    simp [add_comm (X₁ ω), add_assoc (X₂ ω), ZModModule.add_self]
  have C28 : entropy V volume = entropy U volume :=
    by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    exact hFirstCopy.comp measurable_add
  have C29 : entropy (X₂' + X₁) volume = entropy (X₁ + X₂) volume :=
    by
    rw [add_comm]
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    exact hSecondCopy.comp measurable_add
  have C30 : rdist X₁ X₁' volume volume = rdist X₁ X₁ volume volume :=
    h₁.symm.rdist_congr_right hX₁.aemeasurable
  have C31 : rdist X₂ X₂' volume volume = rdist X₂ X₂ volume volume :=
    h₂.symm.rdist_congr_right hX₂.aemeasurable
  simp only [C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19,
    C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31] at I1 I2 I3 I4 I5 I6 ⊢
  linarith only [I1, I2, I3, I4, I5, I6]


-- @@ L667-676 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min in
public lemma averaged_final :
    k ≤
      (6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁)) +
        p.η / 6 * (8 * k + 2 * (rdist X₁ X₁ volume volume + rdist X₂ X₂ volume volume)) :=
  by
  apply (averaged_construct_good hX₁ hX₂ hX₁' hX₂' h_min).trans
  have : 0 ≤ p.η := p.hη.le
  have := sum_condMutual_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep.reindex_four_abdc h_min
  gcongr ?_ + (p.η / 6) * ?_
  linarith [dist_diff_bound_1 p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep,
    dist_diff_bound_2 p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep]


-- @@ L678-702 expanded
include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min in
/-- Suppose $0 < \eta < 1/8$. Let $X_1, X_2$ be tau-minimizers. Then $d[X_1;X_2] = 0$. The proof
of this lemma uses copies `X₁', X₂'` already in the context. For a version that does not assume
these are given and constructs them instead, use `tau_strictly_decreases'`.
-/
public theorem tau_strictly_decreases_aux' (hp : 8 * p.η < 1) : rdist X₁ X₂ volume volume = 0 :=
  by
  have : 0 < p.η := p.hη
  have : k ≤ 8 * p.η * k := by
    calc
      k ≤
          (6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁)) +
            p.η / 6 * (8 * k + 2 * (rdist X₁ X₁ volume volume + rdist X₂ X₂ volume volume)) :=
        averaged_final p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
      _ ≤
          6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁) +
            p.η / 6 * (8 * k + 2 * (2 * (k + (2 * p.η * k - I₁) / (1 - p.η)))) :=
        by
        gcongr
        exact
          second_estimate_aux p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep.reindex_four_abdc
            h_min
      _ = 8 * p.η * k - (1 - 5 * p.η - 4 / 6 * p.η) * (2 * p.η * k - I₁) / (1 - p.η) := by ring
      _ ≤ 8 * p.η * k := by
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        apply div_nonneg _ (by linarith)
        apply mul_nonneg (by linarith) _
        linarith [first_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min]
  apply le_antisymm _ (rdist_nonneg hX₁ hX₂)
  nlinarith


-- @@ L704-714 expanded
include hX₁ hX₂ h_min in
public theorem tau_strictly_decreases' (hp : 8 * p.η < 1) : rdist X₁ X₂ volume volume = 0 :=
  by
  let
    ⟨A, mA, μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1', h_id2'⟩ :=
    independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_congr h_id2]
  let _ : MeasureSpace A := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure A) := hμ
  rw [← h_id1.tauMinimizes p h_id2] at h_min
  exact
    tau_strictly_decreases_aux' p hY₁ hY₂ hY₁' hY₂' (h_id1.trans h_id1'.symm)
      (h_id2.trans h_id2'.symm) h_indep.reindex_four_abdc h_min hp


-- @@ L716-716 verbatim
end MainEstimates


-- @@ L718-718 verbatim
section EntropicPFR


-- @@ L720-720 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L721-721 verbatim
universe uG


-- @@ L723-723 verbatim
open scoped Topology

-- @@ L724-724 verbatim
open Filter Set


-- @@ L726-727 verbatim
variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]


-- @@ L729-730 verbatim
variable {G : Type uG} [AddCommGroup G] [Module (ZMod 2) G] [Finite G] [MeasurableSpace G]
  [MeasurableSingletonClass G]

-- @@ L731-731 verbatim
variable (p : refPackage Ω₀₁ Ω₀₂ G)


-- @@ L733-813 expanded
/-- For `p.η ≤ 1/8`, there exist τ-minimizers `X₁, X₂` at zero Rusza distance. For `p.η < 1/8`,
all minimizers are fine, by `tau_strictly_decreases'`. For `p.η = 1/8`, we use a limit of
minimizers for `η < 1/8`, which exists by compactness. -/
public lemma tau_minimizer_exists_rdist_eq_zero :
    ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
      Measurable X₁ ∧
        Measurable X₂ ∧
          IsProbabilityMeasure (ℙ : Measure Ω) ∧
            tauMinimizes p X₁ X₂ ∧ rdist X₁ X₂ volume volume = 0 :=
  by
  -- let `uₙ` be a sequence converging from below to `η`. In particular, `uₙ < 1/8`.
  
  obtain ⟨u, -, u_mem, u_lim⟩ :
    ∃ u, StrictMono u ∧ (∀ (n : ℕ), u n ∈ Set.Ioo 0 p.η) ∧ Tendsto u atTop (𝓝 p.η) :=
    exists_seq_strictMono_tendsto' p.hη
  let q : ℕ → refPackage Ω₀₁ Ω₀₂ G := fun n ↦
    ⟨p.X₀₁, p.X₀₂, p.hmeas1, p.hmeas2, u n, (u_mem n).1, by linarith [(u_mem n).2, p.hη']⟩
  have :
    ∀ n,
      ∃ (μ : Measure G × Measure G),
        IsProbabilityMeasure μ.1 ∧
          IsProbabilityMeasure μ.2 ∧
            ∀ (ν₁ : Measure G) (ν₂ : Measure G),
              IsProbabilityMeasure ν₁ →
                IsProbabilityMeasure ν₂ → tau (q n) id id μ.1 μ.2 ≤ tau (q n) id id ν₁ ν₂ :=
    fun n ↦ tau_min_exists_measure (q n)
  choose μ μ1_prob μ2_prob hμ using this
  have I n : rdist id id (μ n).1 (μ n).2 = 0 :=
    by
    let M : MeasureSpace (G × G) := ⟨(μ n).1.prod (μ n).2⟩
    have : IsProbabilityMeasure ((μ n).1.prod (μ n).2) := by infer_instance
    have : rdist (@Prod.fst G G) (@Prod.snd G G) volume volume = rdist id id (μ n).1 (μ n).2 :=
      IdentDistrib.rdist_congr IdentDistrib.fst_id IdentDistrib.snd_id
    rw [← this]
    apply
      tau_strictly_decreases' (q n) measurable_fst measurable_snd ?_
        (by linarith [(u_mem n).2, p.hη'])
    intro ν₁ ν₂ h₁ h₂
    have A :
      tau (q n) (@Prod.fst G G) (@Prod.snd G G) MeasureTheory.MeasureSpace.volume
          MeasureTheory.MeasureSpace.volume =
        tau (q n) id id (μ n).1 (μ n).2 :=
      ProbabilityTheory.IdentDistrib.tau_eq (q n) IdentDistrib.fst_id IdentDistrib.snd_id
    rw [A]
    exact hμ n _ _ h₁ h₂
  let μ' : ℕ → ProbabilityMeasure G × ProbabilityMeasure G := fun n ↦
    (⟨(μ n).1, μ1_prob n⟩, ⟨(μ n).2, μ2_prob n⟩)
  let _i : TopologicalSpace G := (⊥ : TopologicalSpace G)
  have : DiscreteTopology G :=
    ⟨rfl⟩
      -- The limiting pair of measures will be the desired minimizer.
      
  rcases IsCompact.tendsto_subseq (x := μ') isCompact_univ (fun n ↦ mem_univ _) with
    ⟨ν, -, φ, φmono, hν⟩
  have φlim : Tendsto φ atTop atTop := φmono.tendsto_atTop
  let M : MeasureSpace (G × G) := ⟨(ν.1 : Measure G).prod ν.2⟩
  have P : IsProbabilityMeasure ((ν.1 : Measure G).prod (ν.2 : Measure G)) := by infer_instance
  refine
    ⟨G × G, M, Prod.fst, Prod.snd, measurable_fst, measurable_snd, P, ?_, ?_⟩
      -- check that it is indeed a minimizer, as a limit of minimizers.
      
  · intro ν₁ ν₂ h₁ h₂
    have A :
      tau p (@Prod.fst G G) (@Prod.snd G G) MeasureTheory.MeasureSpace.volume
          MeasureTheory.MeasureSpace.volume =
        tau p id id ν.1 ν.2 :=
      ProbabilityTheory.IdentDistrib.tau_eq p IdentDistrib.fst_id IdentDistrib.snd_id
    rw [A]
    have L1 :
      Tendsto (fun n ↦ tau (q (φ n)) id id (μ (φ n)).1 (μ (φ n)).2) atTop
        (𝓝 (tau p id id ν.1 ν.2)) :=
      by
      apply
        Tendsto.add (Tendsto.add ?_ (Tendsto.mul (u_lim.comp φlim) ?_))
          (Tendsto.mul (u_lim.comp φlim) ?_)
      · apply Tendsto.comp (continuous_rdist_restrict_probabilityMeasure.tendsto _) hν
      · have :
          Continuous
            (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ rdist p.X₀₁ id ℙ μ.1) :=
          Continuous.comp (continuous_rdist_restrict_probabilityMeasure₁' _ _ p.hmeas1)
            continuous_fst
        apply Tendsto.comp (this.tendsto _) hν
      · have :
          Continuous
            (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ rdist p.X₀₂ id ℙ μ.2) :=
          Continuous.comp (continuous_rdist_restrict_probabilityMeasure₁' _ _ p.hmeas2)
            continuous_snd
        apply Tendsto.comp (this.tendsto _) hν
    have L2 : Tendsto (fun n ↦ tau (q (φ n)) id id ν₁ ν₂) atTop (𝓝 (tau p id id ν₁ ν₂)) :=
      Tendsto.add
        (Tendsto.add tendsto_const_nhds (Tendsto.mul (u_lim.comp φlim) tendsto_const_nhds))
        (Tendsto.mul (u_lim.comp φlim) tendsto_const_nhds)
    exact
      le_of_tendsto_of_tendsto' L1 L2
        (fun n ↦ hμ (φ n) _ _ h₁ h₂)
          -- check that it has zero Rusza distance, as a limit of a sequence at zero Rusza distance.
          
  · have : rdist (@Prod.fst G G) (@Prod.snd G G) volume volume = rdist id id ν.1 ν.2 :=
      IdentDistrib.rdist_congr IdentDistrib.fst_id IdentDistrib.snd_id
    rw [this]
    have L1 :
      Tendsto (fun n ↦ rdist id id (μ (φ n)).1 (μ (φ n)).2) atTop
        (𝓝 (rdist id id ν.1 (ν.2 : Measure G))) :=
      by apply Tendsto.comp (continuous_rdist_restrict_probabilityMeasure.tendsto _) hν
    have L2 : Tendsto (fun n ↦ rdist id id (μ (φ n)).1 (μ (φ n)).2) atTop (𝓝 0) := by simp [I]
    exact tendsto_nhds_unique L1 L2


-- @@ L815-831 expanded
/-- `entropic_PFR_conjecture_improv`: For two $G$-valued random variables $X^0_1, X^0_2$, there is
some subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 10 d[X^0_1;X^0_2]$. -/
public theorem entropic_PFR_conjecture_improv (hpη : p.η = 1 / 8) :
    ∃ (H : Submodule (ZMod 2) G) (Ω : Type uG) (mΩ : MeasureSpace Ω) (U : Ω → G),
      IsProbabilityMeasure (ℙ : Measure Ω) ∧
        Measurable U ∧
          IsUniform H U ∧
            rdist p.X₀₁ U volume volume + rdist p.X₀₂ U volume volume ≤
              10 * rdist p.X₀₁ p.X₀₂ volume volume :=
  by
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, hP, htau_min, hdist⟩ := tau_minimizer_exists_rdist_eq_zero p
  obtain ⟨H, U, hU, hH_unif, hdistX₁, hdistX₂⟩ := exists_isUniform_of_rdist_eq_zero hX₁ hX₂ hdist
  refine ⟨AddSubgroup.toZModSubmodule 2 H, Ω', inferInstance, U, inferInstance, hU, hH_unif, ?_⟩
  have h :
    tau p X₁ X₂ MeasureTheory.MeasureSpace.volume MeasureTheory.MeasureSpace.volume ≤
      tau p p.X₀₂ p.X₀₁ MeasureTheory.MeasureSpace.volume MeasureTheory.MeasureSpace.volume :=
    is_tau_min p htau_min p.hmeas2 p.hmeas1
  rw [tau, tau, hpη] at h
  norm_num at h
  have : rdist p.X₀₁ p.X₀₂ volume volume = rdist p.X₀₂ p.X₀₁ volume volume := rdist_symm
  have : rdist p.X₀₁ U volume volume ≤ rdist p.X₀₁ X₁ volume volume + rdist X₁ U volume volume :=
    rdist_triangle p.hmeas1 hX₁ hU
  have : rdist p.X₀₂ U volume volume ≤ rdist p.X₀₂ X₂ volume volume + rdist X₂ U volume volume :=
    rdist_triangle p.hmeas2 hX₂ hU
  linarith


-- @@ L834-834 verbatim
end EntropicPFR
