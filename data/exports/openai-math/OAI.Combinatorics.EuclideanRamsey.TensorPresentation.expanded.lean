import OAI.Combinatorics.EuclideanRamsey.AdicLifting


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uVector


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped TensorProduct RealInnerProductSpace

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open Real Filter Topology MeasureTheory Polynomial

-- @@ L12-12 verbatim
open Matrix MeasureTheory

-- @@ L13-13 verbatim
open MeasureTheory

-- @@ L14-14 verbatim
open Matrix

-- @@ L15-15 verbatim
open scoped MatrixOrder Matrix.Norms.L2Operator

-- @@ L16-16 verbatim
open MeasureTheory Matrix

-- @@ L17-17 verbatim
open scoped TensorProduct

-- @@ L18-18 verbatim
open scoped BigOperators Pointwise Topology

-- @@ L19-19 verbatim
open MeasureTheory Filter

-- @@ L20-20 verbatim
open scoped BigOperators Pointwise

-- @@ L21-21 verbatim
open scoped BigOperators Topology


-- @@ L23-23 verbatim
open scoped TensorProduct RealInnerProductSpace

-- @@ L24-24 verbatim
namespace EuclideanRamsey


-- @@ L26-26 verbatim
end EuclideanRamsey

-- @@ L27-27 verbatim
namespace EuclideanRamsey

-- @@ L28-28 verbatim
open scoped TensorProduct BigOperators


-- @@ L30-30 verbatim
abbrev AffineVector (d : ℕ) := Option (Fin d) → ℝ


-- @@ L32-35 verbatim
def affineArray {d : ℕ} :
    (AffineVector d ⊗[ℚ] AffineVector d) ≃ₗ[ℚ] RealArray d :=
  (TensorProduct.piLeft ℚ (AffineVector d) (fun _ : Option (Fin d) => ℝ)).trans
    (LinearEquiv.piCongrRight (fun _ => TensorProduct.piRight ℚ ℚ ℝ (fun _ : Option (Fin d) => ℝ)))


-- @@ L37-39 verbatim
@[simp] lemma affineArray_tmul {d : ℕ} (w z : AffineVector d) (α β : Option (Fin d)) :
    affineArray (w ⊗ₜ[ℚ] z) α β = w α ⊗ₜ[ℚ] z β := by
  rfl


-- @@ L41-45 verbatim
def rowEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : AffineVector d →ₗ[ℚ] ℝ where
  toFun w := ∑ α,realAugmented a i α * w α
  map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [Pi.smul_apply,RingHom.id_apply,Rat.smul_def,mul_left_comm,Finset.mul_sum]


-- @@ L47-57 verbatim
lemma arrayEvaluation_affineArray {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (T : AffineVector d ⊗[ℚ] AffineVector d) :
    arrayEvaluation a i (affineArray T) = TensorProduct.map (rowEvaluation a i) (rowEvaluation a i) T := by
  induction T using TensorProduct.inductionOn with
  | tmul w z =>
    simp only [arrayEvaluation,LinearMap.coe_mk,AddHom.coe_mk,affineArray_tmul,
      Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,TensorProduct.map_tmul,
      rowEvaluation,TensorProduct.sum_tmul,TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  | add x y hx hy => simp [hx,hy]


-- @@ L59-68 verbatim
lemma spatialMultiply_affineArray {d : ℕ} (T : AffineVector d ⊗[ℚ] AffineVector d) (α β : Fin d) :
    spatialMultiply (affineArray T) α β =
      Algebra.TensorProduct.lmul' ℚ
        (TensorProduct.map (LinearMap.proj (some α)) (LinearMap.proj (some β)) T) := by
  induction T using TensorProduct.inductionOn with
  | tmul w z =>
    change Algebra.TensorProduct.lmul' ℚ (affineArray (w ⊗ₜ[ℚ] z) (some α) (some β)) = _
    rw [affineArray_tmul]
    rfl
  | add x y hx hy => simp [hx,hy]


-- @@ L70-74 verbatim
lemma affineArray_comm {d : ℕ} (T : AffineVector d ⊗[ℚ] AffineVector d) (α β : Option (Fin d)) :
    affineArray (TensorProduct.comm ℚ _ _ T) α β = TensorProduct.comm ℚ ℝ ℝ (affineArray T β α) := by
  induction T using TensorProduct.inductionOn with
  | tmul w z => simp
  | add x y hx hy => simp [hx,hy]


-- @@ L76-83 verbatim
lemma arrayEvaluation_comm {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (T : AffineVector d ⊗[ℚ] AffineVector d) :
    arrayEvaluation a i (affineArray (TensorProduct.comm ℚ _ _ T)) =
      TensorProduct.comm ℚ ℝ ℝ (arrayEvaluation a i (affineArray T)) := by
  simp only [arrayEvaluation_affineArray]
  induction T using TensorProduct.inductionOn with
  | tmul w z => simp
  | add x y hx hy => simp [hx,hy]


-- @@ L85-95 verbatim
lemma spatialMultiply_comm {d : ℕ} (T : AffineVector d ⊗[ℚ] AffineVector d) :
    spatialMultiply (affineArray (TensorProduct.comm ℚ _ _ T)) =
      (spatialMultiply (affineArray T)).transpose := by
  ext α β
  change Algebra.TensorProduct.lmul' ℚ (affineArray (TensorProduct.comm ℚ _ _ T) (some α) (some β)) =
    Algebra.TensorProduct.lmul' ℚ (affineArray T (some β) (some α))
  rw [affineArray_comm]
  generalize affineArray T (some β) (some α) = z
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx,hy]


-- @@ L97-97 verbatim
end EuclideanRamsey


-- @@ L99-99 verbatim
open scoped TensorProduct BigOperators

-- @@ L100-100 verbatim
namespace EuclideanRamsey


-- @@ L102-138 verbatim
theorem exists_symmetric_tensor_presentation {W : Type uVector} [AddCommGroup W] [Module ℚ W]
    (T : W ⊗[ℚ] W) :
    ∃ (k : ℕ) (w : Fin k → W) (C : Matrix (Fin k) (Fin k) ℚ), C.IsSymm ∧
      (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l)) =
        (1/2:ℚ) • (T + TensorProduct.comm ℚ W W T) := by
  classical
  obtain ⟨S,hS⟩ := TensorProduct.exists_finset T
  let w : (↥S ⊕ ↥S) → W := Sum.elim (fun z : ↥S => z.val.1) (fun z : ↥S => z.val.2)
  let C : (↥S ⊕ ↥S) → (↥S ⊕ ↥S) → ℚ := fun j l => match j,l with
    | .inl i,.inr j => if i=j then 1/2 else 0
    | .inr i,.inl j => if i=j then 1/2 else 0
    | _,_ => 0
  have hC : Matrix.IsSymm C := by
    ext j l
    change C l j = C j l
    cases j <;> cases l <;> dsimp only [C]
    all_goals simp only [eq_comm]
  have hs : (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l)) =
      (1/2:ℚ) • (T + TensorProduct.comm ℚ W W T) := by
    simp only [Fintype.sum_sum_type,C,w,zero_smul,Finset.sum_const_zero,zero_add,add_zero,
      ite_smul,Sum.elim_inl,Sum.elim_inr,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [hS]
    simp only [map_sum,TensorProduct.comm_tmul,smul_add,Finset.smul_sum]
    rw [Finset.sum_subtype S (p := fun z => z ∈ S) (F := inferInstance) (fun _ => Iff.rfl) (fun z => (1/2:ℚ) • (z.1 ⊗ₜ[ℚ] z.2)),
      Finset.sum_subtype S (p := fun z => z ∈ S) (F := inferInstance) (fun _ => Iff.rfl) (fun z => (1/2:ℚ) • (z.2 ⊗ₜ[ℚ] z.1))]
  let e := Fintype.equivFin (↥S ⊕ ↥S)
  refine ⟨Fintype.card (↥S ⊕ ↥S), fun j => w (e.symm j), fun j l => C (e.symm j) (e.symm l),?_,?_⟩
  · ext j l
    exact congrFun (congrFun hC (e.symm j)) (e.symm l)
  · change (∑ j,∑ l,C (e.symm j) (e.symm l) • (w (e.symm j) ⊗ₜ[ℚ] w (e.symm l))) = _
    calc
      _ = ∑ j : Fin (Fintype.card (↥S ⊕ ↥S)),∑ l : ↥S ⊕ ↥S,
          C (e.symm j) l • (w (e.symm j) ⊗ₜ[ℚ] w l) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Equiv.sum_comp e.symm (fun l => C (e.symm j) l • (w (e.symm j) ⊗ₜ[ℚ] w l))
      _ = _ := (Equiv.sum_comp e.symm (fun j => ∑ l,C j l • (w j ⊗ₜ[ℚ] w l))).trans hs


-- @@ L140-140 verbatim
end EuclideanRamsey


-- @@ L142-142 verbatim
open scoped TensorProduct

-- @@ L143-143 verbatim
namespace EuclideanRamsey


-- @@ L145-145 verbatim
end EuclideanRamsey

-- @@ L146-146 verbatim
namespace EuclideanRamsey

-- @@ L147-147 verbatim
open scoped TensorProduct


-- @@ L149-174 verbatim
lemma rational_lattice_kernel {k : ℕ} (f : RationalSpace k →ₗ[ℚ] ℝ) :
    latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) = f.ker := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨γ,hγ,rfl⟩
    exact hγ
  · intro x hx
    let A : Matrix Unit (Fin k) ℚ := fun _ j => x j
    let γ : Lattice k := fun j => A.num () j
    have hden : (A.den:ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
    have he : (rationalize γ : RationalSpace k) = (A.den:ℚ) • x := by
      ext j
      have hm := A.num_div_den () j
      change (A.num () j:ℚ)/(A.den:ℚ) = x j at hm
      change (A.num () j:ℚ) = (A.den:ℚ)*x j
      exact ((div_eq_iff hden).mp hm).trans (mul_comm _ _)
    have hγ : γ ∈ AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize) := by
      change f (rationalize γ) = 0
      rw [he,map_smul]
      exact smul_eq_zero_of_right _ hx
    have hm : rationalize γ ∈ latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) :=
      Submodule.subset_span ⟨γ,hγ,rfl⟩
    have := Submodule.smul_mem (latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)))
      (A.den:ℚ)⁻¹ hm
    simpa only [he,smul_smul,inv_mul_cancel₀ hden,one_smul] using this


-- @@ L176-193 verbatim
lemma quotientTensor_zero_of_evaluation {k : ℕ} (f : RationalSpace k →ₗ[ℚ] ℝ)
    (T : RationalSpace k ⊗[ℚ] RationalSpace k) (hT : TensorProduct.map f f T = 0) :
    quotientTensor (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) T = 0 := by
  classical
  change TensorProduct.map _ _ T = 0
  rw [rational_lattice_kernel]
  let e := f.quotKerEquivRange
  let j : (RationalSpace k ⧸ f.ker) →ₗ[ℚ] ℝ := f.range.subtype.comp e.toLinearMap
  have hj : Function.Injective j := f.range.subtype_injective.comp e.injective
  obtain ⟨r,hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hpre : j.comp f.ker.mkQ = f := by
    ext x
    rfl
  have htmp : TensorProduct.map j j (TensorProduct.map f.ker.mkQ f.ker.mkQ T) = 0 := by
    rw [← LinearMap.comp_apply,← TensorProduct.map_comp,hpre,hT]
  have hback := congrArg (TensorProduct.map r r) htmp
  simpa only [map_zero,← LinearMap.comp_apply,← TensorProduct.map_comp,← LinearMap.comp_assoc,hr,LinearMap.id_comp,TensorProduct.map_id,
    LinearMap.id_apply] using hback


-- @@ L195-195 verbatim
end EuclideanRamsey


-- @@ L197-197 verbatim
namespace EuclideanRamsey

-- @@ L198-198 verbatim
open scoped TensorProduct BigOperators


-- @@ L200-204 verbatim
lemma matrixTensor_map_family {k : ℕ} {W : Type uVector} [AddCommGroup W] [Module ℚ W]
    (w : Fin k → W) (C : Matrix (Fin k) (Fin k) ℚ) :
    TensorProduct.map (Fintype.linearCombination ℚ w) (Fintype.linearCombination ℚ w) (matrixTensor C) =
      ∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l) := by
  simp [matrixTensor,Fintype.linearCombination_apply,TensorProduct.map_tmul]


-- @@ L206-222 verbatim
lemma spatialMultiply_family {k d : ℕ} (w : Fin k → AffineVector d)
    (C : Matrix (Fin k) (Fin k) ℚ) :
    spatialMultiply (affineArray (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l))) =
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * (C.map (Rat.cast : ℚ → ℝ)) *
        (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose := by
  ext α β
  simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,spatialMultiply,
    LinearMap.coe_mk]
  change (∑ j, ∑ l, (C j l:ℝ)*(w j (some α)*w l (some β))) = _
  change _ = ∑ l, (∑ j, w j (some α) * (C j l : ℝ)) * w l (some β)
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring


-- @@ L224-255 verbatim
theorem realCriterion_lattice {s d : ℕ} (a : Fin s → Space d) (hd : 1 ≤ d)
    (h : RealCriterion a) :
    ∃ (k : ℕ) (w : Fin k → AffineVector d) (C : Matrix (Fin k) (Fin k) ℚ),
      1 ≤ k ∧ C.IsSymm ∧
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * (C.map (Rat.cast : ℚ → ℝ)) *
        (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose = (1 : Matrix (Fin d) (Fin d) ℝ) ∧
      ∀ i,quotientTensor
        (AddMonoidHom.ker (((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize))
        (matrixTensor C) = 0 := by
  classical
  obtain ⟨P,hP,hG⟩ := h
  let T : AffineVector d ⊗[ℚ] AffineVector d := affineArray.symm P
  have hT : affineArray T = P := affineArray.apply_symm_apply P
  obtain ⟨k,w,C,hC,hrep⟩ := exists_symmetric_tensor_presentation T
  have hs : spatialMultiply (affineArray (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l))) = 1 := by
    rw [hrep,map_smul,map_add,map_smul,map_add,spatialMultiply_comm,hT,hG]
    ext α β
    simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,Matrix.one_apply]
    by_cases hh : α = β <;> norm_num [hh,eq_comm,Rat.smul_def]
  have hU := (spatialMultiply_family w C).symm.trans hs
  have hk : 1 ≤ k := by
    by_contra hh
    have hk : k = 0 := by omega
    subst k
    have he := congrFun (congrFun hU ⟨0,by omega⟩) ⟨0,by omega⟩
    simp [Matrix.mul_apply] at he
  refine ⟨k,w,C,hk,hC,hU,?_⟩
  intro i
  apply quotientTensor_zero_of_evaluation
  rw [TensorProduct.map_comp,LinearMap.comp_apply,matrixTensor_map_family]
  rw [← arrayEvaluation_affineArray,hrep,map_smul,map_add,map_smul,map_add,
    arrayEvaluation_comm,hT,hP,map_zero,add_zero,smul_zero]


-- @@ L257-257 verbatim
end EuclideanRamsey


-- @@ L259-259 verbatim
end


-- @@ L261-261 verbatim
end OAI
