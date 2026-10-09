import OAI.Analysis.TracialSplitting.Hypertraces


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe uA uH uI uV


-- @@ L9-9 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L11-11 verbatim
open UniformSpace.Completion


-- @@ L13-13 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L15-15 verbatim
open scoped TensorProduct InnerProductSpace


-- @@ L17-17 verbatim
open UniformSpace.Completion


-- @@ L19-19 verbatim
namespace NuclearTrace


-- @@ L21-21 verbatim
open scoped TensorProduct ComplexOrder InnerProductSpace


-- @@ L23-23 verbatim
variable {H : Type uH} {V : Type uV} {I : Type uI} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


-- @@ L25-25 verbatim
variable [Fintype I]


-- @@ L27-44 verbatim
lemma stateTest_mem_closure_dense (T : I → H →L[ℂ] H)
    (hT : ∀ i, IsSelfAdjoint (T i)) (σ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (hσ : σ 1 = 1)
    (j : V → H) (hj : DenseRange j) :
    stateTest T σ ∈ closure (convexHull ℝ (Set.range (vectorTest T ∘ j))) := by
  have hcont : Continuous (vectorTest T) := by
    apply continuous_pi
    intro i
    change Continuous (fun ξ : H => (⟪ξ,T i ξ⟫_ℂ).re)
    fun_prop
  have hv (ξ : H) : vectorTest T ξ ∈ closure (convexHull ℝ (Set.range (vectorTest T ∘ j))) := by
    refine hj.induction_on ξ (isClosed_closure.preimage hcont) ?_
    intro v
    exact subset_closure (subset_convexHull ℝ _ ⟨v,rfl⟩)
  apply (closure_minimal (convexHull_min ?_
    (convex_convexHull ℝ (Set.range (vectorTest T ∘ j))).closure) isClosed_closure)
    (stateTest_mem_closure T hT σ hσ)
  rintro _ ⟨ξ,_,rfl⟩
  exact hv ξ


-- @@ L46-68 verbatim
theorem dense_vector_state_approximation (T : I → H →L[ℂ] H)
    (hT : ∀ i, IsSelfAdjoint (T i)) (σ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (hσ : σ 1 = 1)
    (j : V → H) (hj : DenseRange j) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (v : Fin n → V),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧
      ∀ i, |(σ (T i)).re - ∑ k, w k * (⟪j (v k),T i (j (v k))⟫_ℂ).re| < ε := by
  classical
  obtain ⟨z,hz,hzε⟩ := Metric.mem_closure_iff.mp
    (stateTest_mem_closure_dense T hT σ hσ j hj) ε hε
  obtain ⟨J,_,w,y,hw,hw1,hy,hsum⟩ := mem_convexHull_iff_exists_fintype.mp hz
  choose v hv using hy
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J,w ∘ e,v ∘ e,fun k => hw (e k),(e.sum_comp w).trans hw1,?_⟩
  intro i
  have hle := (norm_le_pi_norm (stateTest T σ-z) i).trans_lt (by
    simpa only [dist_eq_norm] using hzε)
  have he : (∑ k : Fin (Fintype.card J), w (e k) *
      (⟪j (v (e k)),T i (j (v (e k)))⟫_ℂ).re) = z i := by
    rw [e.sum_comp (fun k => w k * (⟪j (v k),T i (j (v k))⟫_ℂ).re)]
    have hv' := congrFun hsum i
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,← hv,
      Function.comp_apply,vectorTest] using hv'
  simpa only [Function.comp_apply,he,Real.norm_eq_abs,Pi.sub_apply,stateTest] using hle


-- @@ L70-70 verbatim
end NuclearTrace


-- @@ L72-72 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L74-74 verbatim
open UniformSpace.Completion


-- @@ L76-76 verbatim
namespace NuclearTrace


-- @@ L78-78 verbatim
section


-- @@ L80-80 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L82-82 verbatim
variable (f g : A →ₚ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)


-- @@ L84-84 verbatim
variable (hfg : ∀ a : A, 0 ≤ a → (g a).re ≤ C * (f a).re)


-- @@ L86-91 verbatim
include hfg hC in
lemma domination_preGNS_norm (a : A) :
    ‖g.toPreGNS a‖ ≤ Real.sqrt C * ‖f.toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt (hfg _ (star_mul_self_nonneg a))


-- @@ L93-96 verbatim
def dominationPreGNS : f.PreGNS →L[ℂ] g.PreGNS :=
  (g.toPreGNS.toLinearMap.comp f.ofPreGNS.toLinearMap).mkContinuous
    (Real.sqrt C) (fun x => by
      simpa using domination_preGNS_norm f g hC hfg (f.ofPreGNS x))


-- @@ L98-99 verbatim
@[simp] lemma dominationPreGNS_apply (x : f.PreGNS) :
    dominationPreGNS f g hC hfg x = g.toPreGNS (f.ofPreGNS x) := rfl


-- @@ L101-102 verbatim
def dominationGNS : f.GNS →L[ℂ] g.GNS :=
  (dominationPreGNS f g hC hfg).completion


-- @@ L104-106 verbatim
@[simp] lemma dominationGNS_coe (x : f.PreGNS) :
    dominationGNS f g hC hfg (x : f.GNS) = (g.toPreGNS (f.ofPreGNS x) : g.GNS) := by
  simp [dominationGNS]


-- @@ L108-112 verbatim
lemma dominationGNS_norm_bound (x : f.GNS) :
    ‖dominationGNS f g hC hfg x‖ ≤ Real.sqrt C * ‖x‖ := by
  induction x using induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x => simpa using domination_preGNS_norm f g hC hfg (f.ofPreGNS x)


-- @@ L114-120 verbatim
lemma dominationGNS_intertwines (a : A) :
    (dominationGNS f g hC hfg).comp (f.gnsStarAlgHom a) =
      (g.gnsStarAlgHom a).comp (dominationGNS f g hC hfg) := by
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x => simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS]


-- @@ L122-128 verbatim
lemma dominationGNS_adjoint_intertwines (a : A) :
    (dominationGNS f g hC hfg).adjoint.comp (g.gnsStarAlgHom a) =
      (f.gnsStarAlgHom a).comp (dominationGNS f g hC hfg).adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint
    (dominationGNS_intertwines f g hC hfg (star a))
  simpa only [ContinuousLinearMap.adjoint_comp,map_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using h.symm


-- @@ L130-131 verbatim
def dominationDensity : f.GNS →L[ℂ] f.GNS :=
  (dominationGNS f g hC hfg).adjoint.comp (dominationGNS f g hC hfg)


-- @@ L133-135 verbatim
lemma dominationDensity_nonneg : 0 ≤ dominationDensity f g hC hfg := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _


-- @@ L137-155 verbatim
lemma dominationDensity_le : dominationDensity f g hC hfg ≤ C • (1 : f.GNS →L[ℂ] f.GNS) := by
  apply sub_nonneg.mp
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨((IsSelfAdjoint.all C).smul (IsSelfAdjoint.one _)).sub
    (dominationDensity_nonneg f g hC hfg).isSelfAdjoint, ?_⟩
  intro x
  have hb : ‖dominationGNS f g hC hfg x‖^2 ≤ C * ‖x‖^2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg x))).mpr
      (dominationGNS_norm_bound f g hC hfg x)
    rw [mul_pow,Real.sq_sqrt hC] at h
    exact h
  change 0 ≤ (⟪(C • (1 : f.GNS →L[ℂ] f.GNS) - dominationDensity f g hC hfg) x,x⟫_ℂ).re
  simp only [sub_apply,smul_apply,one_apply_eq_self,inner_sub_left,
    inner_smul_left_eq_smul,Complex.sub_re,Complex.smul_re,smul_eq_mul,
    dominationDensity,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow,Complex.ofReal_re]
  linarith


-- @@ L157-164 verbatim
lemma dominationDensity_commutes (a : A) :
    Commute (dominationDensity f g hC hfg) (f.gnsStarAlgHom a) := by
  change (dominationDensity f g hC hfg).comp (f.gnsStarAlgHom a) =
    (f.gnsStarAlgHom a).comp (dominationDensity f g hC hfg)
  unfold dominationDensity
  rw [ContinuousLinearMap.comp_assoc,dominationGNS_intertwines,
    ← ContinuousLinearMap.comp_assoc,dominationGNS_adjoint_intertwines,
    ContinuousLinearMap.comp_assoc]


-- @@ L166-172 verbatim
lemma dominationDensity_value (a : A) :
    ⟪(f.toPreGNS 1 : f.GNS),dominationDensity f g hC hfg
      (f.gnsStarAlgHom a (f.toPreGNS 1 : f.GNS))⟫_ℂ = g a := by
  unfold dominationDensity
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS,
    PositiveLinearMap.preGNS_inner_def]


-- @@ L174-174 verbatim
end


-- @@ L176-176 verbatim
open scoped ComplexStarModule


-- @@ L178-178 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L180-186 verbatim
def selfAdjointComplexification (l : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (l (ℜ a) : ℂ) + Complex.I * (l (ℑ a) : ℂ)
  map_add' a b := by simp only [map_add,Complex.ofReal_add]; ring
  map_smul' z a := by
    simp only [realPart_smul,imaginaryPart_smul,map_sub,map_add,map_smul,
      Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]


-- @@ L188-191 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointComplexification_apply (l : selfAdjoint A →ₗ[ℝ] ℝ)
    (a : selfAdjoint A) : selfAdjointComplexification l a = (l a : ℂ) := by
  simp [selfAdjointComplexification]


-- @@ L193-193 verbatim
variable (f : A →ₚ[ℂ] ℂ) (l : selfAdjoint A →ₗ[ℝ] ℝ) (C : ℝ)


-- @@ L195-195 verbatim
variable (hl : ∀ a : selfAdjoint A, 0 ≤ (a : A) → |l a| ≤ C * (f a).re)


-- @@ L197-211 verbatim
include hl in
lemma real_perturbation_nonneg {a : A} (ha : 0 ≤ a) :
    0 ≤ (C : ℂ) • f a + selfAdjointComplexification l a := by
  have hc := hl ⟨a,ha.isSelfAdjoint⟩ ha
  have he : selfAdjointComplexification l a = (l ⟨a,ha.isSelfAdjoint⟩ : ℂ) :=
    selfAdjointComplexification_apply l ⟨a,ha.isSelfAdjoint⟩
  rw [he]
  have hf := f.map_nonneg ha
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    linarith [neg_abs_le (l ⟨a,ha.isSelfAdjoint⟩)]
  · simp only [smul_eq_mul,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,← hf.2,Complex.zero_im,mul_zero,zero_mul,add_zero]


-- @@ L213-221 verbatim
def realPerturbation : A →ₚ[ℂ] ℂ where
  toLinearMap := (C : ℂ) • f.toLinearMap + selfAdjointComplexification l
  monotone' := by
    intro a b hab
    have h := real_perturbation_nonneg f l C hl (sub_nonneg.mpr hab)
    simp only [map_sub,smul_sub] at h
    change (C : ℂ) • f a + selfAdjointComplexification l a ≤
      (C : ℂ) • f b + selfAdjointComplexification l b
    exact sub_nonneg.mp (by convert h using 1; ring)


-- @@ L223-224 verbatim
lemma realPerturbation_apply (a : A) : realPerturbation f l C hl a =
    (C : ℂ) • f a + selfAdjointComplexification l a := rfl


-- @@ L226-232 verbatim
lemma realPerturbation_le {a : A} (ha : 0 ≤ a) :
    (realPerturbation f l C hl a).re ≤ (2*C) * (f a).re := by
  rw [realPerturbation_apply,
    selfAdjointComplexification_apply l (⟨a,ha.isSelfAdjoint⟩ : selfAdjoint A)]
  simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  linarith [hl ⟨a,ha.isSelfAdjoint⟩ ha,le_abs_self (l ⟨a,ha.isSelfAdjoint⟩)]


-- @@ L234-271 verbatim
include hl in
theorem real_functional_in_commutant (hC : 0 ≤ C) :
    ∃ T : f.GNS →L[ℂ] f.GNS, IsSelfAdjoint T ∧
      (-C) • (1 : f.GNS →L[ℂ] f.GNS) ≤ T ∧ T ≤ C • (1 : f.GNS →L[ℂ] f.GNS) ∧
      (∀ a, Commute T (f.gnsStarAlgHom a)) ∧
      ∀ a : selfAdjoint A, l a =
        (⟪(f.toPreGNS 1 : f.GNS),T (f.gnsStarAlgHom a (f.toPreGNS 1 : f.GNS))⟫_ℂ).re := by
  let : Algebra ℝ (f.GNS →L[ℂ] f.GNS) := Algebra.complexToReal
  let : Module ℝ (f.GNS →L[ℂ] f.GNS) := Module.complexToReal _
  let g := realPerturbation f l C hl
  have hg : ∀ a : A, 0 ≤ a → (g a).re ≤ (2*C)*(f a).re :=
    fun _ ha => realPerturbation_le f l C hl ha
  have h2C : 0 ≤ 2*C := mul_nonneg (by norm_num) hC
  let R := dominationDensity f g h2C hg
  have hR0 : 0 ≤ R := dominationDensity_nonneg f g h2C hg
  have hRle : R ≤ (2*C) • (1 : f.GNS →L[ℂ] f.GNS) := dominationDensity_le f g h2C hg
  have hRsa : IsSelfAdjoint R := hR0.isSelfAdjoint
  refine ⟨R - C • (1 : f.GNS →L[ℂ] f.GNS),
    hRsa.sub ((IsSelfAdjoint.all C).smul (IsSelfAdjoint.one _)), ?_, ?_, ?_, ?_⟩
  · simpa only [zero_sub,neg_smul] using sub_le_sub_right hR0 (C • (1 : f.GNS →L[ℂ] f.GNS))
  · apply (sub_le_iff_le_add).mpr
    simpa only [two_mul, add_smul] using hRle
  · intro a
    have hR := dominationDensity_commutes f g h2C hg a
    exact hR.sub_left ((Commute.one_left _).smul_left C)
  · intro a
    have hval := dominationDensity_value f g h2C hg (a : A)
    change (⟪(f.toPreGNS 1 : f.GNS),R (f.gnsStarAlgHom a (f.toPreGNS 1 : f.GNS))⟫_ℂ) = g a at hval
    have hfval : (⟪(f.toPreGNS 1 : f.GNS),f.gnsStarAlgHom a (f.toPreGNS 1 : f.GNS)⟫_ℂ) = f a := by
      simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS,
        PositiveLinearMap.preGNS_inner_def]
    simp only [sub_apply,smul_apply,one_apply_eq_self,inner_sub_right,
      inner_smul_right_eq_smul,Complex.sub_re,Complex.smul_re,smul_eq_mul,hval,hfval]
    change l a = ((C : ℂ) • f a + selfAdjointComplexification l a).re - C * (f a).re
    rw [selfAdjointComplexification_apply]
    simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    ring


-- @@ L273-273 verbatim
end NuclearTrace


-- @@ L275-275 verbatim
end


-- @@ L277-277 verbatim
end OAI
