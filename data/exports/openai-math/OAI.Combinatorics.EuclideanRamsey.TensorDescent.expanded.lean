import OAI.Combinatorics.EuclideanRamsey.TensorNecessity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uIndex


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped TensorProduct RealInnerProductSpace


-- @@ L11-11 verbatim
namespace EuclideanRamsey


-- @@ L13-13 verbatim
section Descent

-- @@ L14-14 verbatim
variable (F : IntermediateField ℚ ℝ) {ι : Type uIndex} (b : Module.Basis ι F ℝ)


-- @@ L16-18 verbatim
def tensorCoordinates : (ℝ ⊗[ℚ] ℝ) ≃ₗ[ℚ] (ι × ι →₀ (F ⊗[ℚ] F)) :=
  (TensorProduct.congr (b.repr.restrictScalars ℚ) (b.repr.restrictScalars ℚ)).trans
    (finsuppTensorFinsupp ℚ ℚ F F ι ι)


-- @@ L20-23 verbatim
lemma tensorCoordinates_tmul (x y : ℝ) (k : ι × ι) :
    tensorCoordinates F b (x ⊗ₜ[ℚ] y) k = b.repr x k.1 ⊗ₜ[ℚ] b.repr y k.2 := by
  rcases k with ⟨l, m⟩
  simp [tensorCoordinates]


-- @@ L25-28 verbatim
lemma tensorCoordinates_symm_single_tmul (x y : F) (k : ι × ι) :
    (tensorCoordinates F b).symm (Finsupp.single k (x ⊗ₜ[ℚ] y)) =
      (x • b k.1) ⊗ₜ[ℚ] (y • b k.2) := by
  simp [tensorCoordinates, finsuppTensorFinsupp_symm_single]


-- @@ L30-32 verbatim
lemma repr_mul (x : F) (u : ℝ) :
    b.repr ((x : ℝ) * u) = x • b.repr u := by
  simpa only [Algebra.smul_def, IntermediateField.algebraMap_apply] using b.repr.map_smul x u


-- @@ L34-47 verbatim
lemma tensorCoordinates_sandwich (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
    tensorCoordinates F b (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T *
      ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) =
      (x ⊗ₜ[ℚ] y) • tensorCoordinates F b T := by
  ext k
  induction T using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      tensorCoordinates_tmul, Finsupp.smul_apply, smul_eq_mul]
    rw [repr_mul, mul_comm v (y : ℝ), repr_mul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
  | add U V hU hV =>
    simpa only [mul_add, add_mul, map_add, Finsupp.add_apply, smul_add,
      Finsupp.smul_apply] using congrArg₂ (· + ·) hU hV


-- @@ L49-49 verbatim
variable (φ : ℝ →ₗ[F] F)


-- @@ L51-51 verbatim
local instance tensorRing : CommRing (F ⊗[ℚ] F) := inferInstance


-- @@ L53-54 verbatim
def coefficientTrace : (ι × ι →₀ (F ⊗[ℚ] F)) →ₗ[(F ⊗[ℚ] F)] (F ⊗[ℚ] F) :=
  Finsupp.linearCombination (F ⊗[ℚ] F) (fun k => φ (b k.1 * b k.2) ⊗ₜ[ℚ] (1 : F))


-- @@ L56-57 verbatim
def tensorDescent : (ℝ ⊗[ℚ] ℝ) →ₗ[ℚ] (F ⊗[ℚ] F) :=
  ((coefficientTrace F b φ).restrictScalars ℚ).comp (tensorCoordinates F b).toLinearMap


-- @@ L59-66 verbatim
lemma tensorDescent_sandwich (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
    tensorDescent F b φ (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T *
      ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) =
      (x ⊗ₜ[ℚ] (1 : F)) * tensorDescent F b φ T * ((1 : F) ⊗ₜ[ℚ] y) := by
  change coefficientTrace F b φ (tensorCoordinates F b _) = _
  rw [tensorCoordinates_sandwich, map_smul]
  change (x ⊗ₜ[ℚ] y) * tensorDescent F b φ T = _
  rw [mul_right_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


-- @@ L68-84 verbatim
lemma coefficientTrace_multiply (z : ι × ι →₀ (F ⊗[ℚ] F)) :
    Algebra.TensorProduct.lmul' ℚ (coefficientTrace F b φ z) =
      φ (Algebra.TensorProduct.lmul' ℚ ((tensorCoordinates F b).symm z)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single k z =>
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [Finsupp.single_add, map_add, hz, hw]
    | tmul x y =>
      simp only [coefficientTrace, Finsupp.linearCombination_single, smul_eq_mul,
        map_mul, Algebra.TensorProduct.lmul'_apply_tmul, mul_one,
        tensorCoordinates_symm_single_tmul]
      have hmul : (x • b k.1) * (y • b k.2) = (x * y) • (b k.1 * b k.2) := by
        simp only [Algebra.smul_def, map_mul]
        ring
      rw [hmul, map_smul, smul_eq_mul]


-- @@ L86-90 verbatim
lemma tensorDescent_multiply (T : ℝ ⊗[ℚ] ℝ) :
    Algebra.TensorProduct.lmul' ℚ (tensorDescent F b φ T) =
      φ (Algebra.TensorProduct.lmul' ℚ T) := by
  change Algebra.TensorProduct.lmul' ℚ (coefficientTrace F b φ (tensorCoordinates F b T)) = _
  rw [coefficientTrace_multiply, LinearEquiv.symm_apply_apply]


-- @@ L92-92 verbatim
end Descent


-- @@ L94-119 verbatim
theorem realCriterion_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : RealCriterion a) : FieldCriterion a := by
  classical
  let F := coordinateField a
  let b := Module.Free.chooseBasis F ℝ
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : ℝ) ≠ 0)
  let δ := tensorDescent F b φ
  obtain ⟨P, he, hm⟩ := h
  refine ⟨fun α β => δ (P α β), ?_, ?_⟩
  · intro i
    have haug (α : Option (Fin d)) : ((augmented a i α : F) : ℝ) = realAugmented a i α := by
      cases α <;> rfl
    have hd := congrArg δ (he i)
    change δ (∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
      ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = δ 0 at hd
    simp only [map_sum, map_zero] at hd
    simpa only [δ, ← haug, tensorDescent_sandwich] using hd
  · intro α β
    change Algebra.TensorProduct.lmul' ℚ (tensorDescent F b φ (P (some α) (some β))) = _
    rw [tensorDescent_multiply]
    have hab := congrFun (congrFun hm α) β
    change Algebra.TensorProduct.lmul' ℚ (P (some α) (some β)) = _ at hab
    rw [hab]
    by_cases heq : α = β
    · simp only [Matrix.one_apply, heq, ite_true, hφ]
    · simp only [Matrix.one_apply, heq, ite_false, map_zero]


-- @@ L121-124 verbatim
theorem ramsey_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hR : Ramsey a) : FieldCriterion a :=
  realCriterion_fieldCriterion a (ramsey_realCriterion a hs hspan hR)


-- @@ L126-126 verbatim
end EuclideanRamsey


-- @@ L128-128 verbatim
namespace EuclideanRamsey

-- @@ L129-129 verbatim
open scoped TensorProduct BigOperators


-- @@ L131-156 verbatim
theorem fieldCriterion_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : FieldCriterion a) : RealCriterion a := by
  classical
  obtain ⟨P,hP,hG⟩ := h
  let φ : TensorRing a →ₐ[ℚ] RealTensor :=
    Algebra.TensorProduct.map (coordinateField a).val (coordinateField a).val
  have haug (i : Fin s) (α : Option (Fin d)) :
      ((augmented a i α : Coeff a) : ℝ) = realAugmented a i α := by
    cases α <;> rfl
  have hmul (T : TensorRing a) :
      Algebra.TensorProduct.lmul' ℚ (φ T) = (multiply a T : ℝ) := by
    induction T using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp [hx,hy]
  refine ⟨fun α β => φ (P α β),?_,?_⟩
  · intro i
    have hh := congrArg φ (hP i)
    have hφ (x y : Coeff a) : φ (x ⊗ₜ[ℚ] y) = (x:ℝ) ⊗ₜ[ℚ] (y:ℝ) := rfl
    change (∑ α,∑ β,(realAugmented a i α ⊗ₜ[ℚ] (1:ℝ))*φ (P α β)*
      ((1:ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = 0
    simpa only [map_sum,map_mul,map_zero,hφ,haug,OneMemClass.coe_one] using hh
  · ext α β
    change Algebra.TensorProduct.lmul' ℚ (φ (P (some α) (some β))) = _
    rw [hmul,hG]
    simp only [Matrix.one_apply]
    split_ifs <;> rfl


-- @@ L158-158 verbatim
end EuclideanRamsey


-- @@ L160-160 verbatim
end


-- @@ L162-162 verbatim
end OAI
