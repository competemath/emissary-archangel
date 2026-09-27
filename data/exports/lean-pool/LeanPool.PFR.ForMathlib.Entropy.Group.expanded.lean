/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.ZhangYeungInequality.PFR.ForMathlib.Entropy.Basic


-- @@ L11-13 verbatim
/-!
# Entropy identities in additive groups
-/


-- @@ L15-15 verbatim
open scoped ZhangYeungPFR



-- @@ L18-18 verbatim
open Function MeasureTheory Measure Real

-- @@ L19-19 verbatim
open scoped ENNReal NNReal Topology ProbabilityTheory


-- @@ L21-21 verbatim
universe uΩ uS uT uU

-- @@ L22-26 verbatim
variable {Ω : Type uΩ} {G : Type uS} {T : Type uT} {U : Type uU} [mΩ : MeasurableSpace Ω]
  [Countable G] [Countable T] [Countable U]
  [hG : MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass G] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Group G] {X Y : Ω → G} {μ : Measure Ω}


-- @@ L28-28 verbatim
namespace ProbabilityTheory

-- @@ L29-29 verbatim
section entropy


-- @@ L31-35 expanded
@[to_additive (attr := simp)]
public lemma entropy_mul_const (hX : Measurable X) (c : G) :
    entropy (X * fun _ ↦ c) μ = entropy X μ := by
  apply entropy_comp_of_injective μ hX _ <| mul_left_injective c


-- @@ L37-43 expanded
/-- `H[X, X * Y] = H[X, Y]`. -/
@[to_additive /-- `H[X, X + Y] = H[X, Y]` -/
    ]
public lemma entropy_mul_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, X * Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodShear Equiv.mulLeft ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ <| Equiv.injective _


-- @@ L45-51 expanded
/-- `H[X, Y * X] = H[X, Y]` -/
@[to_additive /-- `H[X, Y + X] = H[X, Y]` -/
    ]
public lemma entropy_mul_right' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, Y * X⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodShear Equiv.mulRight ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ <| Equiv.injective _


-- @@ L53-58 expanded
/-- `H[Y * X, Y] = H[X, Y]` -/
@[to_additive /-- `H[Y + X, Y] = H[X, Y]` -/
    ]
public lemma entropy_mul_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨Y * X, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  (entropy_comm (hY.mul hX) hY _).trans <| (entropy_mul_right hY hX _).trans <| entropy_comm hY hX _


-- @@ L60-66 expanded
/-- `H[X * Y, Y] = H[X, Y]` -/
@[to_additive /-- `H[X + Y, Y] = H[X, Y]` -/
    ]
public lemma entropy_mul_left' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X * Y, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  (entropy_comm (hX.mul hY) hY _).trans <|
    (entropy_mul_right' hY hX _).trans <| entropy_comm hY hX _


-- @@ L68-74 expanded
/-- `H[X, Y⁻¹] = H[X, Y]` -/
@[to_additive /-- `H[X, -Y] = H[X, Y]` -/
    ]
public lemma entropy_inv_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, Y⁻¹⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodCongr (Equiv.inv _) ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)


-- @@ L76-82 expanded
/-- `H[X⁻¹, Y] = H[X, Y]` -/
@[to_additive /-- `H[-X, Y] = H[X, Y]` -/
    ]
public lemma entropy_inv_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X⁻¹, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.inv _).prodCongr (Equiv.refl _) ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)


-- @@ L84-90 expanded
/-- `H[X, X / Y] = H[X, Y]` -/
@[to_additive /-- `H[X, X - Y] = H[X, Y]` -/
    ]
public lemma entropy_div_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, X / Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodShear Equiv.divLeft ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)


-- @@ L92-98 expanded
/-- `H[X, Y / X] = H[X, Y]` -/
@[to_additive /-- `H[X, Y - X] = H[X, Y]` -/
    ]
public lemma entropy_div_right' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, Y / X⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodShear Equiv.divRight ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)


-- @@ L102-108 expanded
/-- `H[X / Y, Y] = H[X, Y]` -/
@[to_additive /-- `H[X - Y, Y] = H[X, Y]` -/
    ]
public lemma entropy_div_left' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X / Y, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  (entropy_comm (hX.div hY) hY _).trans <|
    (entropy_div_right' hY hX _).trans <| entropy_comm hY hX _


-- @@ L110-114 expanded
/-- If `X` is `G`-valued, then `H[X⁻¹]=H[X]`. -/
@[to_additive /-- If `X` is `G`-valued, then `H[-X]=H[X]`. -/
    ]
public lemma entropy_inv (hX : Measurable X) : entropy X⁻¹ μ = entropy X μ :=
  entropy_comp_of_injective μ hX (·⁻¹) inv_injective


-- @@ L116-120 expanded
/-- `H[X / Y] = H[Y / X]` -/
@[to_additive /-- `H[X - Y] = H[Y - X]` -/
    ]
public lemma entropy_div_comm {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) :
    entropy (X / Y) μ = entropy (Y / X) μ := by rw [← inv_div]; exact entropy_inv (hY.div hX)


-- @@ L125-125 verbatim
end entropy


-- @@ L127-127 verbatim
section condEntropy

-- @@ L128-128 verbatim
variable [IsFiniteMeasure μ] [FiniteRange Y]


-- @@ L130-135 expanded
/-- `H[Y * X | Y] = H[X | Y]` -/
@[to_additive /-- `H[Y + X | Y] = H[X | Y]` -/
    ]
public lemma condEntropy_mul_left (hX : Measurable X) (hY : Measurable Y) :
    condEntropy (Y * X) Y μ = condEntropy X Y μ :=
  condEntropy_of_injective μ hX hY (fun y x ↦ y * x) mul_right_injective


-- @@ L137-142 expanded
/-- `H[X * Y | Y] = H[X | Y]` -/
@[to_additive /-- `H[X + Y | Y] = H[X | Y]` -/
    ]
public lemma condEntropy_mul_right (hX : Measurable X) (hY : Measurable Y) :
    condEntropy (X * Y) Y μ = condEntropy X Y μ :=
  condEntropy_of_injective μ hX hY (fun y x ↦ x * y) mul_left_injective


-- @@ L144-149 expanded
/-- `H[Y / X | Y] = H[X | Y]` -/
@[to_additive /-- `H[Y - X | Y] = H[X | Y]` -/
    ]
public lemma condEntropy_div_left (hX : Measurable X) (hY : Measurable Y) :
    condEntropy (Y / X) Y μ = condEntropy X Y μ :=
  condEntropy_of_injective μ hX hY (fun y x ↦ y / x) fun _ ↦ div_right_injective


-- @@ L151-156 expanded
/-- `H[X / Y | Y] = H[X | Y]` -/
@[to_additive /-- `H[X - Y | Y] = H[X | Y]` -/
    ]
public lemma condEntropy_div_right (hX : Measurable X) (hY : Measurable Y) :
    condEntropy (X / Y) Y μ = condEntropy X Y μ :=
  condEntropy_of_injective μ hX hY (fun y x ↦ x / y) fun _ ↦ div_left_injective


-- @@ L158-158 verbatim
end condEntropy


-- @@ L160-160 verbatim
section mutualInfo


-- @@ L162-162 verbatim
variable [FiniteRange X] [FiniteRange Y]


-- @@ L164-171 expanded
/-- `I[X : X * Y] = H[X * Y] - H[Y]` iff `X, Y` are independent. -/
@[to_additive /-- `I[X : X + Y] = H[X + Y] - H[Y]` iff `X, Y` are independent. -/
    ]
public lemma mutualInfo_mul_right (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h : IndepFun X Y μ) :
    mutualInfo X (X * Y) μ = entropy (X * Y) μ - entropy Y μ :=
  by
  rw [mutualInfo_def, entropy_mul_right hX hY, h.entropy_pair_eq_add hX hY]
  abel


-- @@ L173-173 verbatim
end mutualInfo


-- @@ L175-175 verbatim
section IsProbabilityMeasure

-- @@ L176-176 verbatim
variable [IsProbabilityMeasure μ] {Y : Ω → G} [FiniteRange X] [FiniteRange Y]


-- @@ L178-184 expanded
/-- `H[X] - I[X : Y] ≤ H[X * Y]` -/
@[to_additive /-- `H[X] - I[X : Y] ≤ H[X + Y]` -/
    ]
public lemma entropy_sub_mutualInfo_le_entropy_mul (hX : Measurable X) (hY : Measurable Y) :
    entropy X μ - mutualInfo X Y μ ≤ entropy (X * Y) μ :=
  by
  rw [entropy_sub_mutualInfo_eq_condEntropy hX hY, ← condEntropy_mul_right hX hY]
  exact condEntropy_le_entropy _ (hX.mul hY) hY


-- @@ L186-192 expanded
/-- `H[Y] - I[X : Y] ≤ H[X * Y]` -/
@[to_additive /-- `H[Y] - I[X : Y] ≤ H[X + Y]` -/
    ]
public lemma entropy_sub_mutualInfo_le_entropy_mul' (hX : Measurable X) (hY : Measurable Y) :
    entropy Y μ - mutualInfo X Y μ ≤ entropy (X * Y) μ :=
  by
  rw [entropy_sub_mutualInfo_eq_condEntropy' hX hY, ← condEntropy_mul_left hY hX]
  exact condEntropy_le_entropy _ (hX.mul hY) hX


-- @@ L194-200 expanded
/-- `H[X] - I[X : Y] ≤ H[X / Y]` -/
@[to_additive /-- `H[X] - I[X : Y] ≤ H[X - Y]` -/
    ]
public lemma entropy_sub_mutualInfo_le_entropy_div (hX : Measurable X) (hY : Measurable Y) :
    entropy X μ - mutualInfo X Y μ ≤ entropy (X / Y) μ :=
  by
  rw [entropy_sub_mutualInfo_eq_condEntropy hX hY, ← condEntropy_div_right hX hY]
  exact condEntropy_le_entropy _ (hX.div hY) hY


-- @@ L202-209 expanded
/-- `H[Y] - I[X : Y] ≤ H[X / Y]` -/
@[to_additive /-- `H[Y] - I[X : Y] ≤ H[X - Y]` -/
    ]
public lemma entropy_sub_mutualInfo_le_entropy_div' (hX : Measurable X) (hY : Measurable Y) :
    entropy Y μ - mutualInfo X Y μ ≤ entropy (X / Y) μ :=
  by
  rw [mutualInfo_comm hX hY, entropy_sub_mutualInfo_eq_condEntropy hY hX, ←
    condEntropy_div_left hY hX]
  exact condEntropy_le_entropy _ (hX.div hY) hX


-- @@ L211-217 expanded
/-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X * Y]` -/
@[to_additive /-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X + Y]` -/
    ]
public lemma max_entropy_sub_mutualInfo_le_entropy_mul (hX : Measurable X) (hY : Measurable Y) :
    max (entropy X μ) (entropy Y μ) - mutualInfo X Y μ ≤ entropy (X * Y) μ :=
  by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_sub_mutualInfo_le_entropy_mul hX hY, entropy_sub_mutualInfo_le_entropy_mul' hX hY⟩


-- @@ L219-225 expanded
/-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X / Y]` -/
@[to_additive /-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X - Y]` -/
    ]
public lemma max_entropy_sub_mutualInfo_le_entropy_div (hX : Measurable X) (hY : Measurable Y) :
    max (entropy X μ) (entropy Y μ) - mutualInfo X Y μ ≤ entropy (X / Y) μ :=
  by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_sub_mutualInfo_le_entropy_div hX hY, entropy_sub_mutualInfo_le_entropy_div' hX hY⟩


-- @@ L229-234 expanded
/-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X * Y]`. -/
@[to_additive /-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X + Y]` -/
    ]
public lemma max_entropy_le_entropy_mul (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y μ) : max (entropy X μ) (entropy Y μ) ≤ entropy (X * Y) μ := by
  simpa [h.mutualInfo_eq_zero hX hY] using max_entropy_sub_mutualInfo_le_entropy_mul hX hY (μ := μ)


-- @@ L236-241 expanded
/-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X / Y]`. -/
@[to_additive /-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X - Y]`. -/
    ]
public lemma max_entropy_le_entropy_div (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y μ) : max (entropy X μ) (entropy Y μ) ≤ entropy (X / Y) μ := by
  simpa [h.mutualInfo_eq_zero hX hY] using max_entropy_sub_mutualInfo_le_entropy_div hX hY (μ := μ)


-- @@ L243-269 expanded
/-- If `X₁, ..., Xₙ` are independent and `s ⊆ {1, ..., n}`, then for all `i ∈ s`,
`H[Xᵢ] ≤ H[∏ j ∈ s, Xⱼ]`. -/
@[to_additive /-- If `X₁, ..., Xₙ` are independent and `s ⊆ {1, ..., n}`, then for all `i ∈ s`,
    `H[Xᵢ] ≤ H[∑ j ∈ s, Xⱼ]`. -/
    ]
public lemma max_entropy_le_entropy_prod {G : Type*} [Countable G] [hG : MeasurableSpace G]
    [MeasurableSingletonClass G] [CommGroup G] [MeasurableMul₂ G] {I : Type*} {s : Finset I}
    {i₀ : I} (hi₀ : i₀ ∈ s) {X : I → Ω → G} [∀ i, FiniteRange (X i)]
    (hX : (i : I) → Measurable (X i)) (h_indep : iIndepFun X μ) :
    entropy (X i₀) μ ≤ entropy (∏ i ∈ s, X i) μ :=
  by
  have hs : s.Nonempty := ⟨i₀, hi₀⟩
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp_all
  | cons j s Hnot _ Hind =>
    rw [Finset.prod_cons]
    rcases Finset.mem_cons.mp hi₀ with rfl | hi₀
    ·
      calc
        _ ≤ max (entropy (X i₀) μ) (entropy (∏ i ∈ s, X i) μ) := le_max_left _ _
        _ ≤ entropy (X i₀ * ∏ i ∈ s, X i) μ :=
          by
          refine max_entropy_le_entropy_mul (hX i₀) (by fun_prop) ?_
          exact iIndepFun.indepFun_finsetProd_of_notMem h_indep hX Hnot |>.symm
    ·
      calc
        _ ≤ entropy (∏ i ∈ s, X i) μ := Hind hi₀
        _ ≤ max (entropy (X j) μ) (entropy (∏ i ∈ s, X i) μ) := (le_max_right _ _)
        _ ≤ entropy (X j * ∏ x ∈ s, X x) μ :=
          by
          refine max_entropy_le_entropy_mul (hX j) (by fun_prop) ?_
          exact iIndepFun.indepFun_finsetProd_of_notMem h_indep hX Hnot |>.symm


-- @@ L271-271 verbatim
end IsProbabilityMeasure

-- @@ L272-272 verbatim
end ProbabilityTheory
