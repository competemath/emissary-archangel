module

public import PFR.ForMathlib.Entropy.Basic
public import PFR.ForMathlib.Entropy.Kernel.Group


-- @@ L6-6 verbatim
public section


-- @@ L8-8 verbatim
open Function MeasureTheory Measure Real

-- @@ L9-9 verbatim
open scoped ENNReal NNReal Topology ProbabilityTheory


-- @@ L11-11 verbatim
universe uΩ uS uT uU

-- @@ L12-16 verbatim
variable {Ω : Type uΩ} {G : Type uS} {T : Type uT} {U : Type uU} [mΩ : MeasurableSpace Ω]
  [Countable G] [Countable T] [Countable U]
  [hG : MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass G] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Group G] {X Y : Ω → G} {μ : Measure Ω}


-- @@ L18-18 verbatim
namespace ProbabilityTheory

-- @@ L19-19 verbatim
section entropy


-- @@ L21-24 expanded
@[to_additive (attr := simp)]
lemma entropy_mul_const (hX : Measurable X) (c : G) : entropy (X * fun _ ↦ c) μ = entropy X μ := by
  apply entropy_comp_of_injective μ hX _ <| mul_left_injective c


-- @@ L26-31 expanded
/-- `H[X, X * Y] = H[X, Y]`. -/
@[to_additive /-- `H[X, X + Y] = H[X, Y]` -/
    ]
lemma entropy_mul_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, X * Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodShear Equiv.mulLeft ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ <| Equiv.injective _


-- @@ L33-38 expanded
/-- `H[X, Y * X] = H[X, Y]` -/
@[to_additive /-- `H[X, Y + X] = H[X, Y]` -/
    ]
lemma entropy_mul_right' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, Y * X⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodShear Equiv.mulRight ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ <| Equiv.injective _


-- @@ L40-44 expanded
/-- `H[Y * X, Y] = H[X, Y]` -/
@[to_additive /-- `H[Y + X, Y] = H[X, Y]` -/
    ]
lemma entropy_mul_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨Y * X, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  (entropy_comm (hY.mul hX) hY _).trans <| (entropy_mul_right hY hX _).trans <| entropy_comm hY hX _


-- @@ L46-51 expanded
/-- `H[X * Y, Y] = H[X, Y]` -/
@[to_additive /-- `H[X + Y, Y] = H[X, Y]` -/
    ]
lemma entropy_mul_left' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X * Y, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  (entropy_comm (hX.mul hY) hY _).trans <|
    (entropy_mul_right' hY hX _).trans <| entropy_comm hY hX _


-- @@ L53-58 expanded
/-- `H[X, Y⁻¹] = H[X, Y]` -/
@[to_additive /-- `H[X, -Y] = H[X, Y]` -/
    ]
lemma entropy_inv_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, Y⁻¹⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodCongr (Equiv.inv _) ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)


-- @@ L60-65 expanded
/-- `H[X⁻¹, Y] = H[X, Y]` -/
@[to_additive /-- `H[-X, Y] = H[X, Y]` -/
    ]
lemma entropy_inv_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X⁻¹, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.inv _).prodCongr (Equiv.refl _) ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)


-- @@ L67-72 expanded
/-- `H[X, X / Y] = H[X, Y]` -/
@[to_additive /-- `H[X, X - Y] = H[X, Y]` -/
    ]
lemma entropy_div_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, X / Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodShear Equiv.divLeft ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)


-- @@ L74-79 expanded
/-- `H[X, Y / X] = H[X, Y]` -/
@[to_additive /-- `H[X, Y - X] = H[X, Y]` -/
    ]
lemma entropy_div_right' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X, Y / X⟩ μ = entropy ⟨X, Y⟩ μ :=
  by
  change entropy ((Equiv.refl _).prodShear Equiv.divRight ∘ ⟨X, Y⟩) μ = entropy ⟨X, Y⟩ μ
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)


-- @@ L81-85 expanded
/-- `H[Y / X, Y] = H[X, Y]` -/
@[to_additive /-- `H[Y - X, Y] = H[X, Y]` -/
    ]
lemma entropy_div_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨Y / X, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  (entropy_comm (hY.div hX) hY _).trans <| (entropy_div_right hY hX _).trans <| entropy_comm hY hX _


-- @@ L87-92 expanded
/-- `H[X / Y, Y] = H[X, Y]` -/
@[to_additive /-- `H[X - Y, Y] = H[X, Y]` -/
    ]
lemma entropy_div_left' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    entropy ⟨X / Y, Y⟩ μ = entropy ⟨X, Y⟩ μ :=
  (entropy_comm (hX.div hY) hY _).trans <|
    (entropy_div_right' hY hX _).trans <| entropy_comm hY hX _


-- @@ L94-97 expanded
/-- If `X` is `G`-valued, then `H[X⁻¹]=H[X]`. -/
@[to_additive /-- If `X` is `G`-valued, then `H[-X]=H[X]`. -/
    ]
lemma entropy_inv (hX : Measurable X) : entropy X⁻¹ μ = entropy X μ :=
  entropy_comp_of_injective μ hX (·⁻¹) inv_injective


-- @@ L99-102 expanded
/-- `H[X / Y] = H[Y / X]` -/
@[to_additive /-- `H[X - Y] = H[Y - X]` -/
    ]
lemma entropy_div_comm {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) :
    entropy (X / Y) μ = entropy (Y / X) μ := by rw [← inv_div]; exact entropy_inv (hY.div hX)


-- @@ L105-123 expanded
/-- `max(H[X | Z], H[Y | Z]) - I[X : Y | Z] ≤ H[X / Y | Z]` -/
@[to_additive /-- `max(H[X | Z], H[Y | Z]) - I[X : Y | Z] ≤ H[X - Y | Z]` -/
    ]
lemma max_condEntropy_sub_condMutualInfo_le_condEntropy_div [FiniteRange X] [FiniteRange Y]
    {Z : Ω → T} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [IsProbabilityMeasure μ]
    [FiniteRange Z] :
    (max (condEntropy X Z μ) (condEntropy Y Z μ)) - condMutualInfo X Y Z μ ≤
      condEntropy (X / Y) Z μ :=
  by
  rw [condMutualInfo_comm hX hY, condEntropy_eq_kernel_entropy hX hZ,
    condEntropy_eq_kernel_entropy hY hZ, condMutualInfo_eq_kernel_mutualInfo hY hX hZ,
    condEntropy_eq_kernel_entropy ?_ hZ]
  swap; · exact hX.div hY
  rw [Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ μ).symm,
    Kernel.entropy_congr (condDistrib_fst_ae_eq hY hX hZ μ).symm, max_comm]
  refine (Kernel.max_entropy_sub_mutualInfo_le_entropy_div _ _ ?_).trans_eq ?_
  · exact Kernel.aefiniteKernelSupport_condDistrib _ _ _ (hY.prodMk hX) hZ
  rw [Kernel.entropy_div_comm]
  have h :=
    condDistrib_comp hZ.aemeasurable (hY.prodMk hX).aemeasurable (f := fun x ↦ x.2 / x.1)
      (by fun_prop) (μ := μ) (mβ := inferInstance)
  rw [Kernel.entropy_congr h.symm]
  rfl


-- @@ L125-125 verbatim
end entropy


-- @@ L127-127 verbatim
section condEntropy

-- @@ L128-128 verbatim
variable [IsFiniteMeasure μ] [FiniteRange Y]


-- @@ L130-134 expanded
/-- `H[Y * X | Y] = H[X | Y]` -/
@[to_additive /-- `H[Y + X | Y] = H[X | Y]` -/
    ]
lemma condEntropy_mul_left (hX : Measurable X) (hY : Measurable Y) :
    condEntropy (Y * X) Y μ = condEntropy X Y μ :=
  condEntropy_of_injective μ hX hY (fun y x ↦ y * x) mul_right_injective


-- @@ L136-140 expanded
/-- `H[X * Y | Y] = H[X | Y]` -/
@[to_additive /-- `H[X + Y | Y] = H[X | Y]` -/
    ]
lemma condEntropy_mul_right (hX : Measurable X) (hY : Measurable Y) :
    condEntropy (X * Y) Y μ = condEntropy X Y μ :=
  condEntropy_of_injective μ hX hY (fun y x ↦ x * y) mul_left_injective


-- @@ L142-146 expanded
/-- `H[Y / X | Y] = H[X | Y]` -/
@[to_additive /-- `H[Y - X | Y] = H[X | Y]` -/
    ]
lemma condEntropy_div_left (hX : Measurable X) (hY : Measurable Y) :
    condEntropy (Y / X) Y μ = condEntropy X Y μ :=
  condEntropy_of_injective μ hX hY (fun y x ↦ y / x) fun _ ↦ div_right_injective


-- @@ L148-152 expanded
/-- `H[X / Y | Y] = H[X | Y]` -/
@[to_additive /-- `H[X - Y | Y] = H[X | Y]` -/
    ]
lemma condEntropy_div_right (hX : Measurable X) (hY : Measurable Y) :
    condEntropy (X / Y) Y μ = condEntropy X Y μ :=
  condEntropy_of_injective μ hX hY (fun y x ↦ x / y) fun _ ↦ div_left_injective


-- @@ L154-154 verbatim
end condEntropy


-- @@ L156-156 verbatim
section mutualInfo


-- @@ L158-158 verbatim
variable [FiniteRange X] [FiniteRange Y]


-- @@ L160-166 expanded
/-- `I[X : X * Y] = H[X * Y] - H[Y]` iff `X, Y` are independent. -/
@[to_additive /-- `I[X : X + Y] = H[X + Y] - H[Y]` iff `X, Y` are independent. -/
    ]
lemma mutualInfo_mul_right (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h : IndepFun X Y μ) :
    mutualInfo X (X * Y) μ = entropy (X * Y) μ - entropy Y μ :=
  by
  rw [mutualInfo_def, entropy_mul_right hX hY, h.entropy_pair_eq_add hX hY]
  abel


-- @@ L168-168 verbatim
end mutualInfo


-- @@ L170-170 verbatim
section IsProbabilityMeasure

-- @@ L171-171 verbatim
variable [IsProbabilityMeasure μ] {Y : Ω → G} [FiniteRange X] [FiniteRange Y]


-- @@ L173-178 expanded
/-- `H[X] - I[X : Y] ≤ H[X * Y]` -/
@[to_additive /-- `H[X] - I[X : Y] ≤ H[X + Y]` -/
    ]
lemma entropy_sub_mutualInfo_le_entropy_mul (hX : Measurable X) (hY : Measurable Y) :
    entropy X μ - mutualInfo X Y μ ≤ entropy (X * Y) μ :=
  by
  rw [entropy_sub_mutualInfo_eq_condEntropy hX hY, ← condEntropy_mul_right hX hY]
  exact condEntropy_le_entropy _ (hX.mul hY) hY


-- @@ L180-185 expanded
/-- `H[Y] - I[X : Y] ≤ H[X * Y]` -/
@[to_additive /-- `H[Y] - I[X : Y] ≤ H[X + Y]` -/
    ]
lemma entropy_sub_mutualInfo_le_entropy_mul' (hX : Measurable X) (hY : Measurable Y) :
    entropy Y μ - mutualInfo X Y μ ≤ entropy (X * Y) μ :=
  by
  rw [entropy_sub_mutualInfo_eq_condEntropy' hX hY, ← condEntropy_mul_left hY hX]
  exact condEntropy_le_entropy _ (hX.mul hY) hX


-- @@ L187-192 expanded
/-- `H[X] - I[X : Y] ≤ H[X / Y]` -/
@[to_additive /-- `H[X] - I[X : Y] ≤ H[X - Y]` -/
    ]
lemma entropy_sub_mutualInfo_le_entropy_div (hX : Measurable X) (hY : Measurable Y) :
    entropy X μ - mutualInfo X Y μ ≤ entropy (X / Y) μ :=
  by
  rw [entropy_sub_mutualInfo_eq_condEntropy hX hY, ← condEntropy_div_right hX hY]
  exact condEntropy_le_entropy _ (hX.div hY) hY


-- @@ L194-200 expanded
/-- `H[Y] - I[X : Y] ≤ H[X / Y]` -/
@[to_additive /-- `H[Y] - I[X : Y] ≤ H[X - Y]` -/
    ]
lemma entropy_sub_mutualInfo_le_entropy_div' (hX : Measurable X) (hY : Measurable Y) :
    entropy Y μ - mutualInfo X Y μ ≤ entropy (X / Y) μ :=
  by
  rw [mutualInfo_comm hX hY, entropy_sub_mutualInfo_eq_condEntropy hY hX, ←
    condEntropy_div_left hY hX]
  exact condEntropy_le_entropy _ (hX.div hY) hX


-- @@ L202-207 expanded
/-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X * Y]` -/
@[to_additive /-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X + Y]` -/
    ]
lemma max_entropy_sub_mutualInfo_le_entropy_mul (hX : Measurable X) (hY : Measurable Y) :
    max (entropy X μ) (entropy Y μ) - mutualInfo X Y μ ≤ entropy (X * Y) μ :=
  by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_sub_mutualInfo_le_entropy_mul hX hY, entropy_sub_mutualInfo_le_entropy_mul' hX hY⟩


-- @@ L209-214 expanded
/-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X / Y]` -/
@[to_additive /-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X - Y]` -/
    ]
lemma max_entropy_sub_mutualInfo_le_entropy_div (hX : Measurable X) (hY : Measurable Y) :
    max (entropy X μ) (entropy Y μ) - mutualInfo X Y μ ≤ entropy (X / Y) μ :=
  by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_sub_mutualInfo_le_entropy_div hX hY, entropy_sub_mutualInfo_le_entropy_div' hX hY⟩


-- @@ L216-232 expanded
/-- `max(H[X | Z], H[Y | Z]) - I[X : Y | Z] ≤ H[X * Y | Z]` -/
@[to_additive /-- `max(H[X | Z], H[Y | Z]) - I[X : Y | Z] ≤ H[X + Y | Z]` -/
    ]
lemma max_condEntropy_sub_condMutualInfo_le_condEntropy_mul {Z : Ω → T} [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    max (condEntropy X Z μ) (condEntropy Y Z μ) - condMutualInfo X Y Z μ ≤
      condEntropy (X * Y) Z μ :=
  by
  rw [condMutualInfo_comm hX hY, condEntropy_eq_kernel_entropy hX hZ,
    condEntropy_eq_kernel_entropy hY hZ, condMutualInfo_eq_kernel_mutualInfo hY hX hZ,
    condEntropy_eq_kernel_entropy (show Measurable (X * Y) from hX.mul hY) hZ]
  rw [Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ μ).symm,
    Kernel.entropy_congr (condDistrib_fst_ae_eq hY hX hZ μ).symm, max_comm]
  refine (Kernel.max_entropy_sub_mutualInfo_le_entropy_mul' _ _ ?_).trans_eq ?_
  · exact Kernel.aefiniteKernelSupport_condDistrib _ _ _ (hY.prodMk hX) hZ
  have h :=
    condDistrib_comp hZ.aemeasurable (hY.prodMk hX).aemeasurable (f := fun x ↦ x.2 * x.1)
      (by fun_prop) (μ := μ) (mβ := inferInstance)
  rw [Kernel.entropy_congr h.symm]
  rfl


-- @@ L234-238 expanded
/-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X * Y]`. -/
@[to_additive /-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X + Y]` -/
    ]
lemma max_entropy_le_entropy_mul (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) :
    max (entropy X μ) (entropy Y μ) ≤ entropy (X * Y) μ := by
  simpa [h.mutualInfo_eq_zero hX hY] using max_entropy_sub_mutualInfo_le_entropy_mul hX hY (μ := μ)


-- @@ L240-244 expanded
/-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X / Y]`. -/
@[to_additive /-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X - Y]`. -/
    ]
lemma max_entropy_le_entropy_div (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) :
    max (entropy X μ) (entropy Y μ) ≤ entropy (X / Y) μ := by
  simpa [h.mutualInfo_eq_zero hX hY] using max_entropy_sub_mutualInfo_le_entropy_div hX hY (μ := μ)


-- @@ L246-271 expanded
/-- If `X₁, ..., Xₙ` are independent and `s ⊆ {1, ..., n}`, then for all `i ∈ s`,
`H[Xᵢ] ≤ H[∏ j ∈ s, Xⱼ]`. -/
@[to_additive /-- If `X₁, ..., Xₙ` are independent and `s ⊆ {1, ..., n}`, then for all `i ∈ s`,
    `H[Xᵢ] ≤ H[∑ j ∈ s, Xⱼ]`. -/
    ]
lemma max_entropy_le_entropy_prod {G : Type*} [Countable G] [hG : MeasurableSpace G]
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


-- @@ L273-273 verbatim
end IsProbabilityMeasure

-- @@ L274-274 verbatim
end ProbabilityTheory
