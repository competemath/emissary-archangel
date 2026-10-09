import OAI.Analysis.TracialSplitting.TensorExtension


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uA uB uE uH uN



-- @@ L8-8 verbatim
section


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L16-16 verbatim
open UniformSpace.Completion


-- @@ L18-18 verbatim
namespace NuclearTrace


-- @@ L20-20 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L22-22 verbatim
variable (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a*b) = f (b*a))


-- @@ L24-28 verbatim
include ht in
lemma norm_preGNS_star (a : A) : ‖f.toPreGNS (star a)‖ = ‖f.toPreGNS a‖ := by
  rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
  rw [ht]


-- @@ L30-42 verbatim
include ht in
lemma right_preGNS_norm (a : A) (x : f.PreGNS) :
    ‖f.toPreGNS (f.ofPreGNS x*a)‖ ≤ ‖a‖*‖x‖ := by
  rw [← norm_preGNS_star f ht]
  simp only [star_mul]
  have h := (f.leftMulMapPreGNS (star a)).le_opNorm
    (f.toPreGNS (star (f.ofPreGNS x)))
  have hb : ‖f.leftMulMapPreGNS (star a)‖ ≤ ‖star a‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  apply h.trans
  rw [norm_star] at hb
  rw [norm_preGNS_star f ht, PositiveLinearMap.toPreGNS_ofPreGNS]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)


-- @@ L44-46 verbatim
def rightPreGNS (a : A) : f.PreGNS →L[ℂ] f.PreGNS :=
  (f.toPreGNS.toLinearMap.comp ((LinearMap.mulRight ℂ a).comp f.ofPreGNS.toLinearMap)).mkContinuous
    ‖a‖ (right_preGNS_norm f ht a)


-- @@ L48-49 verbatim
@[simp] lemma rightPreGNS_apply (a : A) (x : f.PreGNS) :
    rightPreGNS f ht a x = f.toPreGNS (f.ofPreGNS x*a) := rfl


-- @@ L51-51 verbatim
def rightGNSMap (a : A) : f.GNS →L[ℂ] f.GNS := (rightPreGNS f ht a).completion


-- @@ L53-55 verbatim
@[simp] lemma rightGNSMap_coe (a : A) (x : f.PreGNS) :
    rightGNSMap f ht a (x : f.GNS) = (rightPreGNS f ht a x : f.GNS) :=
  ContinuousLinearMap.completion_apply_coe (rightPreGNS f ht a) x


-- @@ L57-63 verbatim
lemma rightGNSMap_mul (a b : A) :
    rightGNSMap f ht (a*b) = rightGNSMap f ht b * rightGNSMap f ht a := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using induction_on with
  | hp => exact isClosed_eq (map_continuous _) (map_continuous _)
  | ih x => simp [rightPreGNS_apply,mul_assoc]


-- @@ L65-74 verbatim
lemma rightGNSMap_star (a : A) : rightGNSMap f ht (star a) = star (rightGNSMap f ht a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    simp only [rightGNSMap_coe,UniformSpace.Completion.inner_coe,
      PositiveLinearMap.preGNS_inner_def,rightPreGNS_apply,
      PositiveLinearMap.ofPreGNS_toPreGNS,star_mul,star_star]
    simpa only [mul_assoc] using ht a (star (f.ofPreGNS x) * f.ofPreGNS y)


-- @@ L76-100 verbatim
def rightGNS : Aᵐᵒᵖ →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  toFun a := rightGNSMap f ht a.unop
  map_one' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (map_continuous _) continuous_id
    | ih x => simp
  map_mul' a b := rightGNSMap_mul f ht b.unop a.unop
  map_zero' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (map_continuous _) continuous_const
    | ih x => simp [UniformSpace.Completion.coe_zero]
  map_add' a b := by
    ext x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [mul_add,map_add,UniformSpace.Completion.coe_add]
  commutes' c := by
    ext x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      simp [Algebra.algebraMap_eq_smul_one,UniformSpace.Completion.coe_smul]
  map_star' a := rightGNSMap_star f ht a.unop


-- @@ L102-104 verbatim
@[simp] lemma rightGNS_coe (a : Aᵐᵒᵖ) (x : f.PreGNS) :
    rightGNS f ht a (x : f.GNS) = (f.toPreGNS (f.ofPreGNS x*a.unop) : f.GNS) :=
  rightGNSMap_coe f ht a.unop x


-- @@ L106-113 verbatim
lemma left_right_commute (a : A) (b : Aᵐᵒᵖ) :
    Commute (f.gnsStarAlgHom a) (rightGNS f ht b) := by
  change f.gnsStarAlgHom a * rightGNS f ht b = rightGNS f ht b * f.gnsStarAlgHom a
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (map_continuous _) (map_continuous _)
  | ih x =>
    simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS,mul_assoc]


-- @@ L115-115 verbatim
end NuclearTrace


-- @@ L117-117 verbatim
noncomputable section


-- @@ L119-119 verbatim
namespace Pureness


-- @@ L121-121 verbatim
open scoped TensorProduct


-- @@ L123-123 verbatim
variable {A : Type uA} {B : Type uB} {N : Type uN} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]


-- @@ L125-140 verbatim
def commutingStarTensorHom (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
    (hc : ∀ a b, Commute (φ a) (ψ b)) : A ⊗[ℂ] B →⋆ₐ[ℂ] N :=
  { Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom hc with
    map_star' := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        change φ (star a)*ψ (star b) = star (φ a*ψ b)
        rw [star_mul,← map_star,← map_star]
        exact (hc (star a) (star b)).eq
      | add z w hz hw =>
        let L := Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom hc
        change L (star z) = star (L z) at hz
        change L (star w) = star (L w) at hw
        change L (star (z+w)) = star (L (z+w))
        rw [star_add,map_add,map_add,hz,hw,star_add] }


-- @@ L142-144 verbatim
lemma commutingStarTensorHom_tmul (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    commutingStarTensorHom φ ψ hc (a ⊗ₜ[ℂ] b) = φ a*ψ b := rfl


-- @@ L146-146 verbatim
end Pureness


-- @@ L148-148 verbatim
namespace NuclearTrace


-- @@ L150-150 verbatim
open scoped TensorProduct ComplexOrder InnerProductSpace


-- @@ L152-152 verbatim
section VectorFunctional


-- @@ L154-154 verbatim
variable {E : Type uE} {H : Type uH} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]


-- @@ L156-156 verbatim
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


-- @@ L158-166 verbatim
def vectorFunctional (π : E →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : E →ₚ[ℂ] ℂ where
  toFun x := ⟪ξ, π x ξ⟫_ℂ
  map_add' x y := by simp
  map_smul' c x := by simp
  monotone' := by
    intro a b hab
    have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (map_nonneg π (sub_nonneg.mpr hab))).inner_nonneg_right ξ
    simpa only [map_sub,sub_apply,inner_sub_right,sub_nonneg] using h


-- @@ L168-169 verbatim
@[simp] lemma vectorFunctional_apply (π : E →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : E) :
    vectorFunctional π ξ a = ⟪ξ, π a ξ⟫_ℂ := rfl


-- @@ L171-171 verbatim
end VectorFunctional


-- @@ L173-173 verbatim
section DiagonalState


-- @@ L175-175 verbatim
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L177-177 verbatim
variable (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a*b) = f (b*a))


-- @@ L179-180 verbatim
def leftRightTensor : A ⊗[ℂ] Aᵐᵒᵖ →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  Pureness.commutingStarTensorHom f.gnsStarAlgHom (rightGNS f ht) (left_right_commute f ht)


-- @@ L182-186 verbatim
lemma leftRightTensor_vector (a b : A) :
    leftRightTensor f ht (a ⊗ₜ[ℂ] MulOpposite.op b) (f.toPreGNS 1 : f.GNS) =
      (f.toPreGNS (a*b) : f.GNS) := by
  change f.gnsStarAlgHom a (rightGNS f ht (MulOpposite.op b) (f.toPreGNS 1 : f.GNS)) = _
  simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS]


-- @@ L188-206 verbatim
include ht in
theorem nuclear_diagonal_state (hA : Pureness.IsNuclear.{0,0} A) (hf1 : f 1 = 1)
    {E : Type} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
    (j : A ⊗[ℂ] Aᵐᵒᵖ →⋆ₐ[ℂ] E) (hj : Function.Injective j) (hjd : DenseRange j) :
    ∃ σ : E →ₚ[ℂ] ℂ, σ 1 = 1 ∧ ∀ a b : A, σ (j (a ⊗ₜ[ℂ] MulOpposite.op b)) = f (a*b) := by
  let π := hA.extendRepresentation j (leftRightTensor f ht) hj hjd
  let ξ : f.GNS := f.toPreGNS 1
  refine ⟨vectorFunctional π ξ,?_,?_⟩
  · change ⟪ξ,π 1 ξ⟫_ℂ = 1
    simp only [map_one,one_apply_eq_self]
    simpa only [ξ,UniformSpace.Completion.inner_coe,PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS,star_one,one_mul] using hf1
  · intro a b
    change ⟪ξ,π (j (a ⊗ₜ[ℂ] MulOpposite.op b)) ξ⟫_ℂ = _
    rw [Pureness.IsNuclear.extendRepresentation_apply]
    dsimp only [ξ]
    rw [leftRightTensor_vector,UniformSpace.Completion.inner_coe,
      PositiveLinearMap.preGNS_inner_def]
    simp


-- @@ L208-208 verbatim
end DiagonalState


-- @@ L210-210 verbatim
end NuclearTrace


-- @@ L212-212 verbatim
end


-- @@ L214-214 verbatim
end


-- @@ L216-216 verbatim
end


-- @@ L218-218 verbatim
end


-- @@ L220-220 verbatim
end OAI
