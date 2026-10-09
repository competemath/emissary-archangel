import OAI.Analysis.TracialSplitting.StateExtension


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uA uB uE uF uH uK uι



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
noncomputable section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open scoped TensorProduct InnerProductSpace


-- @@ L30-30 verbatim
open UniformSpace.Completion


-- @@ L32-32 verbatim
namespace UnitalTomsWinter


-- @@ L34-35 verbatim
variable {H : Type uH} {K : Type uK} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]


-- @@ L37-39 verbatim
abbrev SpatialHilbert (H : Type uH) (K : Type uK) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  UniformSpace.Completion (H ⊗[ℂ] K)


-- @@ L41-43 verbatim
def spatialTensorOp (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    SpatialHilbert H K →L[ℂ] SpatialHilbert H K :=
  (TensorProduct.mapL S T).completion


-- @@ L45-47 verbatim
@[simp] lemma spatialTensorOp_coe (S : H →L[ℂ] H) (T : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    spatialTensorOp S T x = (TensorProduct.mapL S T x : SpatialHilbert H K) := by
  exact (TensorProduct.mapL S T).completion_apply_coe x


-- @@ L49-58 verbatim
lemma spatialTensorOp_ext {S T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K}
    (h : ∀ x : H, ∀ y : K, S (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) = T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)) : S = T := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add x y hx hy => simpa [coe_add] using congrArg₂ (· + ·) hx hy


-- @@ L60-61 verbatim
@[simp] lemma spatialTensorOp_zero_left (T : K →L[ℂ] K) : spatialTensorOp (0 : H →L[ℂ] H) T = 0 := by
  apply spatialTensorOp_ext; intro x y; simp


-- @@ L63-64 verbatim
@[simp] lemma spatialTensorOp_zero_right (S : H →L[ℂ] H) : spatialTensorOp S (0 : K →L[ℂ] K) = 0 := by
  apply spatialTensorOp_ext; intro x y; simp


-- @@ L66-68 verbatim
lemma spatialTensorOp_add_left (S₁ S₂ : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (S₁+S₂) T = spatialTensorOp S₁ T + spatialTensorOp S₂ T := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.add_tmul, coe_add]


-- @@ L70-72 verbatim
lemma spatialTensorOp_add_right (S : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp S (T₁+T₂) = spatialTensorOp S T₁ + spatialTensorOp S T₂ := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.tmul_add, coe_add]


-- @@ L74-77 verbatim
lemma spatialTensorOp_smul_left (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (c • S) T = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, smul_apply]
  rw [← TensorProduct.smul_tmul', coe_smul]


-- @@ L79-81 verbatim
lemma spatialTensorOp_smul_right (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp S (c • T) = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp


-- @@ L83-85 verbatim
lemma spatialTensorOp_mul (S₁ S₂ : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp (S₁*S₂) (T₁*T₂) = spatialTensorOp S₁ T₁ * spatialTensorOp S₂ T₂ := by
  apply spatialTensorOp_ext; intro x y; simp


-- @@ L87-93 verbatim
private lemma completion_opNorm_le {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) : ‖f.completion‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih z => simpa using f.le_opNorm z


-- @@ L95-97 verbatim
lemma spatialTensorOp_norm_le (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    ‖spatialTensorOp S T‖ ≤ ‖S‖ * ‖T‖ :=
  (completion_opNorm_le (TensorProduct.mapL S T)).trans (TensorProduct.norm_mapL_le S T)


-- @@ L99-99 verbatim
variable [CompleteSpace H] [CompleteSpace K]


-- @@ L101-113 verbatim
lemma spatialTensorOp_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (star S) (star T) = star (spatialTensorOp S T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
    | tmul x₁ x₂ =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
      | tmul y₁ y₂ => simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]


-- @@ L115-115 verbatim
end UnitalTomsWinter


-- @@ L117-117 verbatim
noncomputable section


-- @@ L119-119 verbatim
namespace Pureness


-- @@ L121-121 verbatim
open UnitalTomsWinter


-- @@ L123-123 verbatim
open scoped TensorProduct InnerProductSpace


-- @@ L125-125 verbatim
variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]


-- @@ L127-127 verbatim
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


-- @@ L129-129 verbatim
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]


-- @@ L131-131 verbatim
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))


-- @@ L133-137 verbatim
omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialTensorOp_one : spatialTensorOp (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply spatialTensorOp_ext
  intro x y
  simp


-- @@ L139-148 verbatim
def spatialLeftHom : A →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun a := spatialTensorOp (α a) 1
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_left]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_left,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' a := by rw [map_star,← spatialTensorOp_star,star_one]


-- @@ L150-159 verbatim
def spatialRightHom : B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun b := spatialTensorOp 1 (β b)
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_right]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_right,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' b := by rw [map_star,← spatialTensorOp_star,star_one]


-- @@ L161-166 verbatim
lemma spatialLeftRight_commute (a : A) (b : B) :
    Commute (spatialLeftHom (K := K) α a) (spatialRightHom (H := H) β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) =
    spatialTensorOp 1 (β b) * spatialTensorOp (α a) 1
  rw [← spatialTensorOp_mul,← spatialTensorOp_mul]
  simp


-- @@ L168-180 verbatim
lemma spatialRightHom_injective [Nontrivial H] (hβ : Function.Injective β) :
    Function.Injective (spatialRightHom (H := H) β) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro b hb
  apply (map_eq_zero_iff β hβ).mp
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x,hx⟩ := exists_ne (0 : H)
  have hz := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    ‖T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)‖) hb
  simp only [zero_apply,norm_zero] at hz
  have hn : ‖x‖ * ‖β b y‖=0 := by simpa [spatialRightHom] using hz
  exact norm_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left (norm_ne_zero_iff.mpr hx))


-- @@ L182-184 verbatim
def spatialStarTensorHom :
    A ⊗[ℂ] B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  commutingStarTensorHom (N := SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (spatialLeftHom (K := K) α) (spatialRightHom (H := H) β) (spatialLeftRight_commute α β)


-- @@ L186-189 verbatim
lemma spatialStarTensorHom_tmul (a : A) (b : B) :
    spatialStarTensorHom α β (a ⊗ₜ[ℂ] b)=spatialTensorOp (α a) (β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) = _
  rw [← spatialTensorOp_mul,mul_one,one_mul]


-- @@ L191-191 verbatim
end Pureness


-- @@ L193-193 verbatim
noncomputable section


-- @@ L195-195 verbatim
namespace Pureness


-- @@ L197-197 verbatim
open UnitalTomsWinter


-- @@ L199-199 verbatim
open scoped TensorProduct InnerProductSpace


-- @@ L201-201 verbatim
variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]


-- @@ L203-203 verbatim
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


-- @@ L205-205 verbatim
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]


-- @@ L207-207 verbatim
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))


-- @@ L209-236 verbatim
lemma spatial_relation_coefficients_zero
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {ι : Type uι} (b : ι → B) (hb : LinearIndependent ℂ b)
    (s : Finset ι) (a : ι → A)
    (hz : spatialStarTensorHom α β (∑ i ∈ s, a i ⊗ₜ[ℂ] b i) = 0) :
    ∀ i ∈ s, a i = 0 := by
  classical
  have hc (x x' : H) : ∑ i ∈ s, ⟪x', α (a i) x⟫_ℂ • b i = 0 := by
    apply (map_eq_zero_iff β hβ).mp
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro y'
    have he := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
      ⟪((x' ⊗ₜ[ℂ] y' : H ⊗[ℂ] K) : SpatialHilbert H K), T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)⟫_ℂ) hz
    simpa only [map_sum, map_smul, spatialStarTensorHom_tmul,
      sum_apply, smul_apply,
      zero_apply, inner_zero_right, inner_sum, inner_smul_right,
      spatialTensorOp_coe, TensorProduct.mapL_tmul, UniformSpace.Completion.inner_coe,
      TensorProduct.inner_tmul] using he
  intro i hi
  apply (map_eq_zero_iff α hα).mp
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro x'
  rw [zero_apply, inner_zero_right]
  exact (linearIndependent_iff'.mp hb) s _ (hc x x') i hi


-- @@ L238-250 verbatim
theorem spatialStarTensorHom_injective_of_faithful
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Injective (spatialStarTensorHom α β) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let b := Module.Free.chooseBasis ℂ B
  obtain ⟨a, rfl⟩ := TensorProduct.eq_repr_basis_right b z
  have ha := spatial_relation_coefficients_zero α β hα hβ b b.linearIndependent a.support a hz
  change ∑ i ∈ a.support, a i ⊗ₜ[ℂ] b i = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [ha i hi, TensorProduct.zero_tmul]


-- @@ L252-252 verbatim
end Pureness


-- @@ L254-254 verbatim
end


-- @@ L256-256 verbatim
end


-- @@ L258-258 verbatim
end


-- @@ L260-260 verbatim
end


-- @@ L262-262 verbatim
end


-- @@ L264-264 verbatim
end


-- @@ L266-266 verbatim
end


-- @@ L268-268 verbatim
end


-- @@ L270-270 verbatim
end


-- @@ L272-272 verbatim
end OAI
