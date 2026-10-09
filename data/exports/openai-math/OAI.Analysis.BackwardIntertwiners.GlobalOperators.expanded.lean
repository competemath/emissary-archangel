import OAI.Analysis.BackwardIntertwiners.BackwardWeights


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace BackwardIntertwiners

-- @@ L6-6 verbatim
open Filter

-- @@ L7-7 verbatim
open scoped Topology

-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open Topology MeasureTheory Set

-- @@ L11-11 verbatim
open scoped ENNReal


-- @@ L13-13 verbatim
section Fields

-- @@ L14-14 verbatim
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}


-- @@ L16-23 verbatim
lemma weightedPermutation_stronglyMeasurable (e : ℤ ≃ ℤ) (a : X → ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x j, ‖a x j‖ ≤ C)
    (hm : ∀ j, Measurable (fun x => a x j))
    {f : X → Fiber} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun x => fiberWeightedPermutation e (a x) C hC (ha x) (f x)) := by
  apply fiberCoordinates_stronglyMeasurable
  intro j
  exact (hm (e j)).mul (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (e j)).continuous.comp_stronglyMeasurable hf).measurable)


-- @@ L25-32 verbatim
lemma weightedPermutation_aestronglyMeasurable (e : ℤ ≃ ℤ) (a : X → ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x j, ‖a x j‖ ≤ C)
    (hm : ∀ j, Measurable (fun x => a x j))
    {f : X → Fiber} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => fiberWeightedPermutation e (a x) C hC (ha x) (f x)) μ := by
  apply (weightedPermutation_stronglyMeasurable e a C hC ha hm hf.stronglyMeasurable_mk).aestronglyMeasurable.congr
  filter_upwards [hf.ae_eq_mk] with x hx
  rw [hx]



-- @@ L35-40 verbatim
def scalarMultiplier (g : Lp ℂ ∞ μ) : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => g • f
      map_add' := Lp.add_smul g
      map_smul' := fun c f => (Lp.smul_comm c g f).symm }
    ‖g‖ (Lp.norm_smul_le g)


-- @@ L42-48 verbatim
def fieldVector (A : X → Fiber →L[ℂ] Fiber) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : Lp Fiber 2 μ :=
  ((Lp.memLp f).of_le_mul (hm f (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x =>
      (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)))).toLp _


-- @@ L50-54 verbatim
lemma fieldVector_ae (A : X → Fiber →L[ℂ] Fiber) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : fieldVector A C hA hm f =ᵐ[μ] fun x => A x (f x) :=
  MemLp.coeFn_toLp _


-- @@ L56-66 verbatim
lemma fieldVector_norm (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : ‖fieldVector A C hA hm f‖ ≤ C*‖f‖ := by
  calc
    _ ≤ ‖(C:ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [fieldVector_ae A C hA hm f, Lp.coeFn_smul (C:ℂ) f] with x hx hs
      rw [hx, hs, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
      exact (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _))
    _ = C*‖f‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]


-- @@ L68-87 verbatim
def fieldOperator (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  LinearMap.mkContinuous
    { toFun := fieldVector A C hA hm
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [fieldVector_ae A C hA hm (f+g), fieldVector_ae A C hA hm f,
          fieldVector_ae A C hA hm g, Lp.coeFn_add f g,
          Lp.coeFn_add (fieldVector A C hA hm f) (fieldVector A C hA hm g)] with x h₁ h₂ h₃ h₄ h₅
        simp only [h₁,h₂,h₃,h₄,h₅,Pi.add_apply,map_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [fieldVector_ae A C hA hm (c • f), fieldVector_ae A C hA hm f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (fieldVector A C hA hm f)] with x h₁ h₂ h₃ h₄
        simp only [RingHom.id_apply, h₁,h₂,h₃,h₄,Pi.smul_apply,map_smul] }
    C (fieldVector_norm A C hC hA hm)


-- @@ L89-93 verbatim
lemma fieldOperator_ae (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : fieldOperator A C hC hA hm f =ᵐ[μ] fun x => A x (f x) :=
  fieldVector_ae A C hA hm f


-- @@ L95-99 verbatim
lemma fieldOperator_norm (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ) :
    ‖fieldOperator A C hC hA hm‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (fieldVector_norm A C hC hA hm)


-- @@ L101-102 verbatim
lemma scalarMultiplier_ae (g : Lp ℂ ∞ μ) (f : Lp Fiber 2 μ) :
    scalarMultiplier g f =ᵐ[μ] fun x => g x • f x := Lp.coeFn_lpSMul g f

-- @@ L103-104 verbatim
lemma scalarMultiplier_norm_le (g : Lp ℂ ∞ μ) : ‖scalarMultiplier (μ := μ) g‖ ≤ ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) (Lp.norm_smul_le g)

-- @@ L105-105 verbatim
end Fields


-- @@ L107-107 verbatim
abbrev GlobalHilbert := Lp Fiber 2 baseMeasure


-- @@ L109-110 verbatim
def OperatorInvariant {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : Submodule ℂ H) (T : H →L[ℂ] H) : Prop := ∀ v ∈ L, T v ∈ L


-- @@ L112-114 verbatim
def generatedAlgebra (S V : GlobalHilbert →L[ℂ] GlobalHilbert) :
    Subalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) :=
  Algebra.adjoin ℂ ({S,V} ∪ Set.range (scalarMultiplier (μ := baseMeasure)))


-- @@ L116-118 verbatim
def AlgebraTransitive (A : Subalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert)) : Prop :=
  ∀ L : Submodule ℂ GlobalHilbert, IsClosed (L : Set GlobalHilbert) →
    (∀ T ∈ A, OperatorInvariant L T) → L = ⊥ ∨ L = ⊤



-- @@ L121-126 verbatim
structure DirectModelData where
  Sx : Base → Fiber →L[ℂ] Fiber
  S : GlobalHilbert →L[ℂ] GlobalHilbert
  b : Base → ℤ → ℝ
  Vx : Base → Fiber →L[ℂ] Fiber
  V : GlobalHilbert →L[ℂ] GlobalHilbert





-- @@ L131-153 verbatim
structure DirectModelProperties (D : DirectModelData) : Prop where
  beta_measurable : ∀ j, Measurable (fun x => explicitBeta x j)
  beta_positive : ∀ x j, 0 < explicitBeta x j
  forward_coordinates : ∀ x v j, D.Sx x v j = (explicitBeta x (j-1):ℂ)*v (j-1)
  forward_field : ∀ f, D.S f =ᵐ[baseMeasure] fun x => D.Sx x (f x)
  fiber_lattice : ∀ x (L : Submodule ℂ Fiber),
    (IsClosed (L : Set Fiber) ∧ OperatorInvariant L (D.Sx x)) ↔
      L = ⊥ ∨ L = ⊤ ∨ ∃ h : ℤ, L = coordinateTail h
  S_nonzero : D.S ≠ 0
  S_norm : ‖D.S‖ = Real.exp (-10)
  power_bound : ∀ n : ℕ, 1 ≤ n → ‖D.S^n‖ ≤ Real.exp (-10*(((n+1)^2/4:ℕ):ℝ))
  V_contraction : ‖D.V‖ ≤ 1
  commute : D.S * D.V = D.V * D.S
  backward_measurable : ∀ j, Measurable (fun x => D.b x j)
  backward_bounds : ∀ x j, 0 ≤ D.b x j ∧ D.b x j ≤ 1
  backward_coordinates : ∀ x v j, D.Vx x v j = (D.b x (j+1):ℂ)*v (j+1)
  backward_field : ∀ f, ∀ᵐ x ∂baseMeasure, D.V f (odometer x) = D.Vx x (f x)
  common_conull : ∃ Xstar : Set Base, MeasurableSet Xstar ∧ baseMeasure Xstarᶜ = 0 ∧
    odometer ⁻¹' Xstar = Xstar ∧ ∀ x ∈ Xstar,
      (∀ j, 0 < D.b x j) ∧
      (∀ h : ℤ, ((coordinateTail h).map (D.Vx x).toLinearMap).topologicalClosure = coordinateTail (h-1)) ∧
      DenseRange (D.Vx x)
  transitive : AlgebraTransitive (generatedAlgebra D.S D.V)




-- @@ L157-160 verbatim
def forwardFiber (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberWeightedPermutation (Equiv.subRight 1) (fun j => (explicitBeta x j:ℂ))
    (Real.exp (-10)) (Real.exp_pos _).le
    (fun j => by simpa only [Complex.norm_real, Real.norm_of_nonneg (explicitBeta_pos x j).le] using explicitBeta_le x j)

-- @@ L161-163 verbatim
def backwardFiber (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberWeightedPermutation (Equiv.addRight 1) (fun j => (backwardCoeff x j:ℂ)) 1 (by norm_num)
    (fun j => by simpa only [Complex.norm_real, Real.norm_of_nonneg (backwardCoeff_bounds x j).1] using (backwardCoeff_bounds x j).2)

-- @@ L164-165 verbatim
@[simp] lemma forwardFiber_apply (x : Base) (v : Fiber) (j : ℤ) :
    forwardFiber x v j = (explicitBeta x (j-1):ℂ) * v (j-1) := rfl

-- @@ L166-167 verbatim
@[simp] lemma backwardFiber_apply (x : Base) (v : Fiber) (j : ℤ) :
    backwardFiber x v j = (backwardCoeff x (j+1):ℂ) * v (j+1) := rfl

-- @@ L168-169 verbatim
lemma forwardFiber_norm_le (x : Base) : ‖forwardFiber x‖ ≤ Real.exp (-10) :=
  fiberWeightedPermutation_norm_le _ _ _ _ _

-- @@ L170-171 verbatim
lemma backwardFiber_norm_le (x : Base) : ‖backwardFiber x‖ ≤ 1 :=
  fiberWeightedPermutation_norm_le _ _ _ _ _

-- @@ L172-180 verbatim
lemma forwardFiber_single (x : Base) (j : ℤ) (c : ℂ) :
    forwardFiber x (lp.single 2 j c) = lp.single 2 (j+1) ((explicitBeta x j:ℂ)*c) := by
  ext k
  rw [forwardFiber_apply]
  by_cases hk : k = j+1
  · subst k
    simp
  · have hj : k-1 ≠ j := by omega
    simp only [lp.single_apply_ne _ _ _ hk, lp.single_apply_ne _ _ _ hj, mul_zero]

-- @@ L181-189 verbatim
lemma backwardFiber_single (x : Base) (j : ℤ) (c : ℂ) :
    backwardFiber x (lp.single 2 j c) = lp.single 2 (j-1) ((backwardCoeff x j:ℂ)*c) := by
  ext k
  rw [backwardFiber_apply]
  by_cases hk : k = j-1
  · subst k
    simp
  · have hj : k+1 ≠ j := by omega
    simp only [lp.single_apply_ne _ _ _ hk, lp.single_apply_ne _ _ _ hj, mul_zero]

-- @@ L190-196 verbatim
lemma forwardFiber_norm (x : Base) : ‖forwardFiber x‖ = Real.exp (-10) := by
  apply le_antisymm (forwardFiber_norm_le x)
  have hh := (forwardFiber x).le_opNorm (lp.single 2 0 (1:ℂ))
  rw [forwardFiber_single, explicitBeta_zero, mul_one, lp.norm_single (by norm_num : (0:ENNReal)<2),
    lp.norm_single (by norm_num : (0:ENNReal)<2), norm_one, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hh
  exact hh


-- @@ L198-205 verbatim
lemma backwardFiber_intertwines (x : Base) :
    forwardFiber (odometer x) * backwardFiber x = backwardFiber x * forwardFiber x := by
  ext v j
  simp only [mul_apply_eq_comp, forwardFiber_apply, backwardFiber_apply,
    sub_add_cancel, add_sub_cancel_right]
  have hc := congrArg (fun r : ℝ => (r:ℂ)) (backwardCoeff_recurrence x j)
  push_cast at hc
  linear_combination -hc * v j


-- @@ L207-214 verbatim
lemma coordinateTail_isClosed (h : ℤ) : IsClosed (coordinateTail h : Set Fiber) := by
  have he : (coordinateTail h : Set Fiber) = ⋂ j : ℤ, ⋂ _ : j < h, {v : Fiber | v j = 0} := by
    ext v
    change (∀ j : ℤ, j < h → v j = 0) ↔ _
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).continuous continuous_const

-- @@ L215-218 verbatim
lemma forwardFiber_tail (x : Base) (h : ℤ) {v : Fiber} (hv : v ∈ coordinateTail h) :
    forwardFiber x v ∈ coordinateTail h := by
  intro j hj
  rw [forwardFiber_apply, hv _ (by omega), mul_zero]

-- @@ L219-222 verbatim
lemma backwardFiber_tail (x : Base) (h : ℤ) {v : Fiber} (hv : v ∈ coordinateTail h) :
    backwardFiber x v ∈ coordinateTail (h-1) := by
  intro j hj
  rw [backwardFiber_apply, hv _ (by omega), mul_zero]

-- @@ L223-226 verbatim
lemma single_mem_coordinateTail {h j : ℤ} (hj : h ≤ j) (c : ℂ) :
    (lp.single 2 j c : Fiber) ∈ coordinateTail h := by
  intro k hk
  exact lp.single_apply_ne _ _ _ (by omega)


-- @@ L228-250 verbatim
lemma backwardFiber_tail_closure {x : Base} (hx : x ∈ goodBase) (h : ℤ) :
    ((coordinateTail h).map (backwardFiber x).toLinearMap).topologicalClosure = coordinateTail (h-1) := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ ?_ (coordinateTail_isClosed (h-1))
    rintro _ ⟨v,hv,rfl⟩
    exact backwardFiber_tail x h hv
  · intro v hv
    let P := ((coordinateTail h).map (backwardFiber x).toLinearMap).topologicalClosure
    have hP : IsClosed (P : Set Fiber) := Submodule.isClosed_topologicalClosure _
    apply hP.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ∞) v)
    apply Filter.Eventually.of_forall
    intro s
    apply P.sum_mem
    intro j _
    by_cases hj : j < h-1
    · rw [hv j hj, lp.single_zero]
      exact P.zero_mem
    · apply (Submodule.le_topologicalClosure ((coordinateTail h).map (backwardFiber x).toLinearMap))
      refine ⟨lp.single 2 (j+1) (v j / (backwardCoeff x (j+1):ℂ)),
        single_mem_coordinateTail (by omega) _, ?_⟩
      change backwardFiber x (_) = _
      rw [backwardFiber_single, add_sub_cancel_right, mul_div_cancel₀]
      exact_mod_cast ne_of_gt (backwardCoeff_pos hx (j+1))


-- @@ L252-264 verbatim
lemma backwardFiber_denseRange {x : Base} (hx : x ∈ goodBase) : DenseRange (backwardFiber x) := by
  intro v
  have hcl : IsClosed (closure (Set.range (backwardFiber x))) := isClosed_closure
  apply hcl.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ∞) v)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ j ∈ s, lp.single 2 (j+1) (v j / (backwardCoeff x (j+1):ℂ)), ?_⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [backwardFiber_single, add_sub_cancel_right, mul_div_cancel₀]
  exact_mod_cast ne_of_gt (backwardCoeff_pos hx (j+1))


-- @@ L266-282 verbatim
lemma explicitExponent_distance (x : Base) (j : ℤ) :
    10*(coordinateDistance j:ℝ) ≤ explicitExponent x j := by
  cases j with
  | ofNat n =>
    have hd : coordinateDistance (n:ℤ) = (n:ℤ)+1 := by
      unfold coordinateDistance
      omega
    change 10*(coordinateDistance (n:ℤ):ℝ) ≤ halfExponent (plusResidue x) n
    rw [hd]
    simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast] using halfExponent_lower (plusResidue x) n
  | negSucc n =>
    have hd : coordinateDistance (Int.negSucc n) = (n:ℤ)+1 := by
      unfold coordinateDistance
      omega
    rw [hd]
    change _ ≤ halfExponent (minusResidue x) n
    simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast] using halfExponent_lower (minusResidue x) n


-- @@ L284-291 verbatim
lemma interval_exponent_lower (x : Base) (n : ℕ) (j : ℤ) :
    10*(powerCost n:ℝ) ≤ ∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)) := by
  have hc : (powerCost n:ℝ) ≤ ∑ r ∈ Finset.range n, (coordinateDistance (j+(r:ℤ)):ℝ) := by
    exact_mod_cast sum_coordinateDistance_lower n j
  calc
    _ ≤ 10*(∑ r ∈ Finset.range n, (coordinateDistance (j+(r:ℤ)):ℝ)) := by linarith
    _ = ∑ r ∈ Finset.range n, 10*(coordinateDistance (j+(r:ℤ)):ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun _ _ => explicitExponent_distance x _


-- @@ L293-305 verbatim
lemma forwardFiber_power_input (x : Base) (n : ℕ) (v : Fiber) (j : ℤ) :
    (forwardFiber x ^ n) v (j+(n:ℤ)) =
      (Real.exp (-(∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)))):ℂ)*v j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, forwardFiber_apply]
    have hi : j+((n+1:ℕ):ℤ)-1 = j+(n:ℤ) := by omega
    rw [hi, ih, Finset.sum_range_succ]
    change (Real.exp (-explicitExponent x (j+(n:ℤ))):ℂ)*
      ((Real.exp (-(∑ r ∈ Finset.range n, explicitExponent x (j+(r:ℤ)))):ℂ)*v j) = _
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [neg_add_rev]


-- @@ L307-325 verbatim
lemma forwardFiber_power_norm (x : Base) (n : ℕ) :
    ‖forwardFiber x ^ n‖ ≤ Real.exp (-10*(powerCost n:ℝ)) := by
  let C := Real.exp (-10*(powerCost n:ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  calc
    _ ≤ ‖(C:ℂ) • fiberReindex (Equiv.subRight (n:ℤ)) v‖ := by
      apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
      intro j
      have hi : j = (j-(n:ℤ))+(n:ℤ) := by omega
      conv_lhs => rw [hi, forwardFiber_power_input]
      simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, fiberReindex_apply, Equiv.subRight_apply,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hC]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using neg_le_neg (interval_exponent_lower x n (j-(n:ℤ)))
    _ = C*‖v‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, (fiberReindex _).norm_map]



-- @@ L328-332 verbatim
lemma forwardFiber_aestronglyMeasurable (f : Base → Fiber) (hf : AEStronglyMeasurable f baseMeasure) :
    AEStronglyMeasurable (fun x => forwardFiber x (f x)) baseMeasure := by
  apply weightedPermutation_aestronglyMeasurable
  · exact fun j => Complex.measurable_ofReal.comp (measurable_explicitBeta j)
  · exact hf

-- @@ L333-337 verbatim
lemma backwardFiber_aestronglyMeasurable (f : Base → Fiber) (hf : AEStronglyMeasurable f baseMeasure) :
    AEStronglyMeasurable (fun x => backwardFiber x (f x)) baseMeasure := by
  apply weightedPermutation_aestronglyMeasurable
  · exact fun j => Complex.measurable_ofReal.comp (measurable_backwardCoeff j)
  · exact hf


-- @@ L339-341 verbatim
def forwardOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  fieldOperator forwardFiber (Real.exp (-10)) (Real.exp_pos _).le
    forwardFiber_norm_le forwardFiber_aestronglyMeasurable

-- @@ L342-344 verbatim
lemma forwardOperator_ae (f : GlobalHilbert) :
    forwardOperator f =ᵐ[baseMeasure] fun x => forwardFiber x (f x) :=
  fieldOperator_ae _ _ _ _ _ f

-- @@ L345-346 verbatim
lemma forwardOperator_norm_le : ‖forwardOperator‖ ≤ Real.exp (-10) :=
  fieldOperator_norm _ _ _ _ _


-- @@ L348-348 verbatim
def inverseOdometer (x : Base) : Base := (show PadicInt 2 from x)-1

-- @@ L349-351 verbatim
@[simp] lemma inverseOdometer_odometer (x : Base) : inverseOdometer (odometer x) = x := by
  change ((show PadicInt 2 from x)+1)-1 = _
  exact add_sub_cancel_right _ _

-- @@ L352-354 verbatim
@[simp] lemma odometer_inverseOdometer (x : Base) : odometer (inverseOdometer x) = x := by
  change ((show PadicInt 2 from x)-1)+1 = _
  exact sub_add_cancel _ _

-- @@ L355-361 verbatim
lemma inverseOdometer_preserving : MeasurePreserving inverseOdometer baseMeasure baseMeasure := by
  have hh := measurePreserving_completion (α := PadicInt 2) (measurePreserving_add_right baseHaar (-1))
  have he : inverseOdometer = (show Base → Base from fun x : PadicInt 2 => x + (-1)) := by
    funext x
    exact @sub_eq_add_neg (PadicInt 2) _ (show PadicInt 2 from x) 1
  rw [he]
  exact hh


-- @@ L363-369 verbatim
def odometerMeasurableEquiv : Base ≃ᵐ Base where
  toFun := odometer
  invFun := inverseOdometer
  left_inv := inverseOdometer_odometer
  right_inv := odometer_inverseOdometer
  measurable_toFun := odometer_ergodic.measurable
  measurable_invFun := inverseOdometer_preserving.measurable


-- @@ L371-372 verbatim
def backwardFieldOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  fieldOperator backwardFiber 1 (by norm_num) backwardFiber_norm_le backwardFiber_aestronglyMeasurable


-- @@ L374-375 verbatim
def backwardOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  (Lp.compMeasurePreservingₗᵢ ℂ inverseOdometer inverseOdometer_preserving).toContinuousLinearMap.comp backwardFieldOperator


-- @@ L377-382 verbatim
lemma backwardOperator_ae_inverse (f : GlobalHilbert) :
    backwardOperator f =ᵐ[baseMeasure] fun x => backwardFiber (inverseOdometer x) (f (inverseOdometer x)) := by
  have h₁ := Lp.coeFn_compMeasurePreserving (backwardFieldOperator f) inverseOdometer_preserving
  have h₂ := (fieldOperator_ae backwardFiber 1 (by norm_num) backwardFiber_norm_le
    backwardFiber_aestronglyMeasurable f).comp_tendsto inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae
  exact h₁.trans h₂


-- @@ L384-388 verbatim
lemma backwardOperator_ae (f : GlobalHilbert) :
    ∀ᵐ x ∂baseMeasure, backwardOperator f (odometer x) = backwardFiber x (f x) := by
  filter_upwards [(backwardOperator_ae_inverse f).comp_tendsto
    odometer_ergodic.quasiMeasurePreserving.tendsto_ae] with x hx
  simpa only [Function.comp_def,inverseOdometer_odometer] using hx


-- @@ L390-395 verbatim
lemma backwardOperator_norm : ‖backwardOperator‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖Lp.compMeasurePreserving inverseOdometer inverseOdometer_preserving (backwardFieldOperator f)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  exact fieldVector_norm backwardFiber 1 (by norm_num) backwardFiber_norm_le backwardFiber_aestronglyMeasurable f


-- @@ L397-409 verbatim
lemma forward_backward_commute : forwardOperator * backwardOperator = backwardOperator * forwardOperator := by
  ext1 f
  apply Lp.ext
  filter_upwards [forwardOperator_ae (backwardOperator f), backwardOperator_ae_inverse f,
    backwardOperator_ae_inverse (forwardOperator f),
    (forwardOperator_ae f).comp_tendsto inverseOdometer_preserving.quasiMeasurePreserving.tendsto_ae] with x h₁ h₂ h₃ h₄
  change forwardOperator (backwardOperator f) x = backwardOperator (forwardOperator f) x
  rw [h₁,h₂,h₃]

  dsimp only [Function.comp_def] at h₄
  rw [h₄]
  have hh := congrArg (fun A : Fiber →L[ℂ] Fiber => A (f (inverseOdometer x))) (backwardFiber_intertwines (inverseOdometer x))
  simpa only [mul_apply_eq_comp, odometer_inverseOdometer] using hh


-- @@ L411-418 verbatim
lemma forward_scalar_commute (g : Lp ℂ ∞ baseMeasure) :
    forwardOperator * scalarMultiplier g = scalarMultiplier g * forwardOperator := by
  ext1 f
  apply Lp.ext
  filter_upwards [forwardOperator_ae (scalarMultiplier g f), scalarMultiplier_ae g f,
    scalarMultiplier_ae g (forwardOperator f), forwardOperator_ae f] with x h₁ h₂ h₃ h₄
  change forwardOperator (scalarMultiplier g f) x = scalarMultiplier g (forwardOperator f) x
  simp only [h₁,h₂,h₃,h₄,map_smul]


-- @@ L420-420 verbatim
def constantBasis (j : ℤ) : GlobalHilbert := Lp.const 2 baseMeasure (lp.single 2 j (1:ℂ))

-- @@ L421-423 verbatim
lemma constantBasis_norm (j : ℤ) : ‖constantBasis j‖ = 1 := by
  rw [constantBasis, Lp.norm_const 2 baseMeasure _ (by norm_num), lp.norm_single (by norm_num : (0:ENNReal)<2)]
  simp

-- @@ L424-425 verbatim
lemma constantBasis_ae (j : ℤ) : constantBasis j =ᵐ[baseMeasure] fun _ => lp.single 2 j (1:ℂ) :=
  Lp.coeFn_const _ _ _

-- @@ L426-433 verbatim
lemma forwardOperator_constantBasis_zero :
    forwardOperator (constantBasis 0) = (Real.exp (-10):ℂ) • constantBasis 1 := by
  apply Lp.ext
  filter_upwards [forwardOperator_ae (constantBasis 0), constantBasis_ae 0, constantBasis_ae 1,
    Lp.coeFn_smul (Real.exp (-10):ℂ) (constantBasis 1)] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,h₄,Pi.smul_apply,h₃,forwardFiber_single,explicitBeta_zero,mul_one]
  rw [← lp.single_smul]
  simp

-- @@ L434-439 verbatim
lemma forwardOperator_norm : ‖forwardOperator‖ = Real.exp (-10) := by
  apply le_antisymm forwardOperator_norm_le
  have h := forwardOperator.le_opNorm (constantBasis 0)
  rw [forwardOperator_constantBasis_zero, norm_smul, constantBasis_norm, constantBasis_norm,
    mul_one, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h
  exact h

-- @@ L440-444 verbatim
lemma forwardOperator_ne_zero : forwardOperator ≠ 0 := by
  intro h
  have hh := forwardOperator_norm
  rw [h, norm_zero] at hh
  exact (Real.exp_ne_zero (-10)) hh.symm


-- @@ L446-453 verbatim
lemma forwardOperator_power_ae (n : ℕ) (f : GlobalHilbert) :
    (forwardOperator^n) f =ᵐ[baseMeasure] fun x => (forwardFiber x ^ n) (f x) := by
  induction n with
  | zero => filter_upwards [] with x; rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [forwardOperator_ae ((forwardOperator^n) f), ih] with x h₁ h₂
    simp only [h₁,h₂,pow_succ',mul_apply_eq_comp]

-- @@ L454-467 verbatim
lemma forwardOperator_power_norm (n : ℕ) :
    ‖forwardOperator^n‖ ≤ Real.exp (-10*(powerCost n:ℝ)) := by
  let C := Real.exp (-10*(powerCost n:ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  calc
    _ ≤ ‖(C:ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [forwardOperator_power_ae n f, Lp.coeFn_smul (C:ℂ) f] with x h₁ h₂
      rw [h₁,h₂,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
      exact (forwardFiber x ^ n).le_opNorm (f x) |>.trans
        (mul_le_mul_of_nonneg_right (forwardFiber_power_norm x n) (norm_nonneg _))
    _ = C*‖f‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]



-- @@ L470-470 verbatim
end

-- @@ L471-471 verbatim
end BackwardIntertwiners


-- @@ L473-473 verbatim
end OAI
