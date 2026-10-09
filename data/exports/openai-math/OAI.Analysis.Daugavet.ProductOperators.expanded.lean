import OAI.Analysis.Daugavet.FiniteCoordinates


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L7-7 verbatim
open scoped ENNReal NNReal Topology BigOperators


-- @@ L9-9 verbatim
universe uX uB uIota uKappa


-- @@ L11-11 verbatim
namespace ExactModuli.KW

-- @@ L12-12 verbatim
section ProductAtoms

-- @@ L13-13 verbatim
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

-- @@ L14-14 verbatim
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]


-- @@ L16-16 verbatim
def arrayMultiplier (p : ℝ) (k : κ) (j : ι) (v : κ → cube ι) : ℝ := multiplier p (v k j)


-- @@ L18-21 verbatim
lemma array_coordinate_mp (k : κ) (j : ι) :
    MeasurePreserving (fun v : κ → cube ι => v k j) (arrayMeasure κ ι) volume :=
  (measurePreserving_eval (fun _ : ι => (volume : Measure unitInterval)) j).comp
    (measurePreserving_eval (fun _ : κ => cubeMeasure ι) k)


-- @@ L23-26 verbatim
lemma integrable_arrayMultiplier {p : ℝ} (hp : 1 < p) (k : κ) (j : ι) :
    Integrable (arrayMultiplier p k j) (arrayMeasure κ ι) :=
  ((array_coordinate_mp k j).integrable_comp (integrable_multiplier hp).aestronglyMeasurable).mpr
    (integrable_multiplier hp)


-- @@ L28-31 verbatim
lemma integral_arrayMultiplier {p : ℝ} (hp : 1 < p) (k : κ) (j : ι) :
    (∫ v, arrayMultiplier p k j v ∂arrayMeasure κ ι) = 1 :=
  (mp_integral (array_coordinate_mp k j) (integrable_multiplier hp).aestronglyMeasurable).trans
    (integral_multiplier hp)


-- @@ L33-36 verbatim
omit [Fintype κ] [Fintype ι] in
lemma measurable_arrayMultiplier [Fintype κ] [Fintype ι] (p : ℝ) (k : κ) (j : ι) :
    Measurable (arrayMultiplier p k j) :=
  (measurable_multiplier p).comp (by fun_prop)


-- @@ L38-42 verbatim
lemma arrayMultiplier_tail {p c : ℝ} (hp : 1 < p) (hc : scale p ≤ c) (k : κ) (j : ι) :
    (arrayMeasure κ ι).real {v | c < arrayMultiplier p k j v} = (scale p / c)^p := by
  have he := (array_coordinate_mp k j).measureReal_preimage
    (measurableSet_lt (measurable_const (a := c)) (measurable_multiplier p)).nullMeasurableSet
  exact he.trans (multiplier_tail hp hc)


-- @@ L44-47 verbatim
def atomL1 {p : ℝ} (hp : 1 < p) (u : Lp ℝ 1 μ) (k : κ) (j : ι) :
    Lp ℝ 1 (μ.prod (arrayMeasure κ ι)) :=
  integrableL1 (fun z => u z.1 * arrayMultiplier p k j z.2)
    ((L1.integrable_coeFn u).mul_prod (integrable_arrayMultiplier hp k j))


-- @@ L49-53 verbatim
omit [IsProbabilityMeasure μ] in
lemma atomL1_ae [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (u : Lp ℝ 1 μ) (k : κ) (j : ι) :
    atomL1 hp u k j =ᵐ[μ.prod (arrayMeasure κ ι)]
      fun z => u z.1 * arrayMultiplier p k j z.2 := integrableL1_ae _ _


-- @@ L55-62 verbatim
lemma norm_atomL1 {p : ℝ} (hp : 1 < p) (u : Lp ℝ 1 μ) (k : κ) (j : ι) :
    ‖atomL1 hp u k j‖ = ‖u‖ := by
  rw [L1_norm_of_ae _ (atomL1_ae hp u k j)]
  simp only [abs_mul, arrayMultiplier, abs_of_nonneg (multiplier_nonneg hp _) ]
  change (∫ z : B × (κ → cube ι), |u z.1| * arrayMultiplier p k j z.2 ∂μ.prod (arrayMeasure κ ι)) = ‖u‖
  rw [integral_prod_mul (fun b => |u b|) (arrayMultiplier p k j), integral_arrayMultiplier hp,
    mul_one, L1.norm_eq_integral_norm]
  rfl


-- @@ L64-79 verbatim
lemma atomL1_near_additive {p c h : ℝ} (hp : 1 < p) (hc : 0 ≤ c) (hpc : scale p ≤ c)
    (herr : 2 * ((scale p / c)^p + c) < h) {w u : Lp ℝ 1 μ}
    (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) (k : κ) (j : ι) :
    2 - h ≤ ‖oldL1 w + atomL1 hp u k j‖ := by
  have hn := near_additivity (L1.integrable_coeFn w) (L1.integrable_coeFn u)
    (integrable_arrayMultiplier hp k j) (measurable_arrayMultiplier p k j)
    (fun _ => multiplier_nonneg hp _) (by simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm w).symm.trans hw)
    (by simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm u).symm.trans hu)
    (integral_arrayMultiplier hp k j) hc
  rw [arrayMultiplier_tail hp hpc k j] at hn
  have hae : (oldL1 w + atomL1 hp u k j : Lp ℝ 1 (μ.prod (arrayMeasure κ ι))) =ᵐ[μ.prod (arrayMeasure κ ι)]
      fun z => w z.1 + u z.1 * arrayMultiplier p k j z.2 := by
    filter_upwards [Lp.coeFn_add (oldL1 w) (atomL1 hp u k j), oldL1_ae w, atomL1_ae hp u k j] with z h₁ h₂ h₃
    simpa only [Pi.add_apply, h₂, h₃] using h₁
  rw [L1_norm_of_ae _ hae]
  linarith


-- @@ L81-81 verbatim
end ProductAtoms


-- @@ L83-83 verbatim
section LinearCombinations

-- @@ L84-84 verbatim
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

-- @@ L85-85 verbatim
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]


-- @@ L87-90 verbatim
def matrixCombination (v : κ → ι → X) : (κ → ι → ℝ) →ₗ[ℝ] X where
  toFun a := ∑ k, ∑ j, a k j • v k j
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]


-- @@ L92-92 verbatim
end LinearCombinations


-- @@ L94-94 verbatim
section ProductOperator

-- @@ L95-95 verbatim
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

-- @@ L96-96 verbatim
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]


-- @@ L98-100 verbatim
def productOperator {p : ℝ} (hp : 1 < p) (u : κ → Lp ℝ 1 μ) :
    (Lp ℝ 1 μ × (κ → ι → ℝ)) →ₗ[ℝ] Lp ℝ 1 (μ.prod (arrayMeasure κ ι)) :=
  oldL1.toLinearMap.coprod (matrixCombination (fun k j => atomL1 hp (u k) k j))


-- @@ L102-125 verbatim
lemma productOperator_ae {p : ℝ} (hp : 1 < p) (x : Lp ℝ 1 μ) (u : κ → Lp ℝ 1 μ) (a : κ → ι → ℝ) :
    productOperator hp u (x,a) =ᵐ[μ.prod (arrayMeasure κ ι)]
      enlargedFunction p x (fun k => (u k : B → ℝ)) a := by
  have hrows (k : κ) : (∑ j, a k j • atomL1 hp (u k) k j : Lp ℝ 1 (μ.prod (arrayMeasure κ ι)))
      =ᵐ[μ.prod (arrayMeasure κ ι)] fun z => u k z.1 * rowSum p (a k) (z.2 k) := by
    filter_upwards [coeFn_L1_smul_sum (a k) (fun j => atomL1 hp (u k) k j),
      ae_all_iff.mpr (fun j => atomL1_ae hp (u k) k j)] with z hz hzj
    rw [hz]
    simp only [rowSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hzj j]
    dsimp [arrayMultiplier]
    ring
  filter_upwards [Lp.coeFn_add (oldL1 x) (matrixCombination (fun k j => atomL1 hp (u k) k j) a),
    oldL1_ae x, coeFn_L1_sum Finset.univ (fun k => ∑ j, a k j • atomL1 hp (u k) k j),
    ae_all_iff.mpr hrows] with z hz hzx hzs hzrow
  change (oldL1 x + matrixCombination (fun k j => atomL1 hp (u k) k j) a : Lp ℝ 1 (μ.prod (arrayMeasure κ ι))) z = _
  rw [hz]
  simp only [Pi.add_apply, hzx, enlargedFunction]
  congr 1
  change (∑ k, ∑ j, a k j • atomL1 hp (u k) k j : Lp ℝ 1 (μ.prod (arrayMeasure κ ι))) z = _
  rw [hzs]
  exact Finset.sum_congr rfl (fun k _ => hzrow k)


-- @@ L127-131 verbatim
omit [IsProbabilityMeasure μ] in
lemma productOperator_zero_coeff [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (u : κ → Lp ℝ 1 μ) (x : Lp ℝ 1 μ) :
    productOperator (ι := ι) hp u (x,0) = oldL1 x := by
  simp [productOperator, matrixCombination]


-- @@ L133-133 verbatim
end ProductOperator

-- @@ L134-134 verbatim
end ExactModuli.KW


-- @@ L136-136 verbatim
end


-- @@ L138-138 verbatim
end OAI
