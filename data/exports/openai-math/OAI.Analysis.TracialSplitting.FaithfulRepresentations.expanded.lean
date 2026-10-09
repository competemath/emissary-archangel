import OAI.Analysis.TracialSplitting.SpatialTensor


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uA uH uα uι



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
noncomputable section


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
namespace Pureness


-- @@ L40-40 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L42-42 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L44-44 verbatim
def stateGNSVector (f : A →ₚ[ℂ] ℂ) : f.GNS := f.toPreGNS 1


-- @@ L46-53 verbatim
lemma stateGNSVector_norm (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) :
    ‖stateGNSVector f‖ = 1 := by
  have h := f.preGNS_norm_sq (f.toPreGNS 1)
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, h1] at h
  have h' : ‖f.toPreGNS 1‖ ^ 2 = 1 := by exact_mod_cast h
  have hnorm : ‖f.toPreGNS 1‖ = 1 :=
    (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (h'.trans (one_pow 2).symm)
  simpa only [stateGNSVector, UniformSpace.Completion.norm_coe] using hnorm


-- @@ L55-57 verbatim
lemma stateGNS_apply_vector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (stateGNSVector f) = (f.toPreGNS a : f.GNS) := by
  simp [stateGNSVector, PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS]


-- @@ L59-62 verbatim
lemma stateGNS_vector_value (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪stateGNSVector f, f.gnsStarAlgHom a (stateGNSVector f)⟫_ℂ = f a := by
  rw [stateGNS_apply_vector]
  simp [stateGNSVector, UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]


-- @@ L64-64 verbatim
end Pureness


-- @@ L66-66 verbatim
noncomputable section


-- @@ L68-68 verbatim
namespace Pureness


-- @@ L70-70 verbatim
open scoped ComplexOrder


-- @@ L72-72 verbatim
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L74-88 verbatim
theorem exists_positiveState_norming [Nontrivial A] (a : A) (ha : 0 ≤ a) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
  have han : IsStarNormal a := (IsSelfAdjoint.of_nonneg ha).isStarNormal
  let s : spectrum ℂ a := ⟨(‖a‖ : ℂ), by
    exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg a ha)⟩
  let ev : C(spectrum ℂ a, ℂ) →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ (ContinuousMap.evalAlgHom ℂ ℂ s).toLinearMap (fun b hb => hb s)
  have hev : ev 1 = 1 := rfl
  obtain ⟨f, hf1, hf⟩ := CurrentMain.state_extension (cfcHom han)
    (cfcHom_injective han) ev hev
  refine ⟨f, hf1, ?_⟩
  calc
    f a = ev ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) := by
      simpa only [cfcHom_id] using hf ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
    _ = (‖a‖ : ℂ) := rfl


-- @@ L90-94 verbatim
theorem positive_eq_zero_of_states [Nontrivial A] (a : A) (ha : 0 ≤ a)
    (h : ∀ f : A →ₚ[ℂ] ℂ, f 1 = 1 → f a = 0) : a = 0 := by
  obtain ⟨f, hf1, hfa⟩ := exists_positiveState_norming a ha
  have hn : (‖a‖ : ℂ) = 0 := hfa.symm.trans (h f hf1)
  exact norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hn)


-- @@ L96-102 verbatim
theorem stateGNS_separates [Nontrivial A] (a : A)
    (h : ∀ f : A →ₚ[ℂ] ℂ, f 1 = 1 → f.gnsStarAlgHom a = 0) : a = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff a).mp
  apply positive_eq_zero_of_states (star a * a) (star_mul_self_nonneg a)
  intro f hf1
  rw [← stateGNS_vector_value f, map_mul, map_star, h f hf1, star_zero, mul_zero]
  simp


-- @@ L104-104 verbatim
end Pureness


-- @@ L106-106 verbatim
noncomputable section


-- @@ L108-108 verbatim
namespace Pureness


-- @@ L110-110 verbatim
open scoped InnerProductSpace ENNReal


-- @@ L112-112 verbatim
variable {A : Type uA} {ι : Type uι} [CStarAlgebra A] {H : ι → Type uH}


-- @@ L114-114 verbatim
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]


-- @@ L116-116 verbatim
variable [∀ i, CompleteSpace (H i)]


-- @@ L118-118 verbatim
variable (ρ : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))


-- @@ L120-123 verbatim
def hilbertSumAction (a : A) (x : lp H 2) : lp H 2 :=
  ⟨fun i => ρ i a (x i), ((lp.memℓp x).norm.const_mul ‖a‖).mono (fun i =>
    ((ρ i a).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le (ρ i).toNonUnitalStarAlgHom a) (norm_nonneg _)))⟩


-- @@ L125-137 verbatim
lemma hilbertSumAction_norm_le (a : A) (x : lp H 2) :
    ‖hilbertSumAction ρ a x‖ ≤ ‖a‖ * ‖x‖ := by
  let y : lp H 2 := (‖a‖ : ℂ) • x
  have hy : ∀ i, ‖hilbertSumAction ρ a x i‖ ≤ ‖y i‖ := by
    intro i
    change ‖ρ i a (x i)‖ ≤ ‖(‖a‖ : ℂ) • x i‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
    exact ((ρ i a).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le (ρ i).toNonUnitalStarAlgHom a) (norm_nonneg _))
  have hn := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hy
  change ‖hilbertSumAction ρ a x‖ ≤ ‖(‖a‖ : ℂ) • x‖ at hn
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)] at hn
  exact hn


-- @@ L139-144 verbatim
def hilbertSumOperator (a : A) : lp H 2 →L[ℂ] lp H 2 :=
  LinearMap.mkContinuous
    { toFun := hilbertSumAction ρ a
      map_add' := fun x y => by apply lp.ext; funext i; exact (ρ i a).map_add _ _
      map_smul' := fun c x => by apply lp.ext; funext i; exact (ρ i a).map_smul c _ }
    ‖a‖ (hilbertSumAction_norm_le ρ a)


-- @@ L146-147 verbatim
lemma hilbertSumOperator_apply (a : A) (x : lp H 2) (i : ι) :
    hilbertSumOperator ρ a x i = ρ i a (x i) := rfl


-- @@ L149-166 verbatim
def hilbertSumRepresentation : A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun := hilbertSumOperator ρ
  map_zero' := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_zero (ρ i))
  map_one' := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_one (ρ i))
  map_add' a b := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_add (ρ i) a b)
  map_mul' a b := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_mul (ρ i) a b)
  commutes' c := by
    ext x i
    exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) ((ρ i).commutes c)
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    change ⟪ρ i (star a) (x i), y i⟫_ℂ = ⟪x i, ρ i a (y i)⟫_ℂ
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _


-- @@ L168-169 verbatim
lemma hilbertSumRepresentation_apply (a : A) (x : lp H 2) (i : ι) :
    hilbertSumRepresentation ρ a x i = ρ i a (x i) := rfl


-- @@ L171-181 verbatim
lemma hilbertSumRepresentation_eq_iff (a b : A) :
    hilbertSumRepresentation ρ a = hilbertSumRepresentation ρ b ↔ ∀ i, ρ i a = ρ i b := by
  classical
  constructor
  · intro h i
    ext x
    have hh := congrArg (fun f : lp H 2 →L[ℂ] lp H 2 => f (lp.single 2 i x) i) h
    simpa only [hilbertSumRepresentation_apply, lp.single_apply, Pi.single_eq_same] using hh
  · intro h
    ext x i
    exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (h i)


-- @@ L183-183 verbatim
end Pureness


-- @@ L185-185 verbatim
noncomputable section


-- @@ L187-187 verbatim
namespace Pureness


-- @@ L189-189 verbatim
open scoped InnerProductSpace ComplexOrder


-- @@ L191-191 verbatim
local instance {α : Type uα} : DecidableEq α := Classical.decEq α


-- @@ L193-193 verbatim
variable (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L195-195 verbatim
def PositiveStateIndex := {f : A →ₚ[ℂ] ℂ // f 1 = 1}


-- @@ L197-197 verbatim
abbrev UniversalStateHilbert := lp (fun f : PositiveStateIndex A => f.1.GNS) 2


-- @@ L199-201 verbatim
def universalStateGNS : A →⋆ₐ[ℂ]
    (UniversalStateHilbert A →L[ℂ] UniversalStateHilbert A) :=
  hilbertSumRepresentation (fun f : PositiveStateIndex A => f.1.gnsStarAlgHom)


-- @@ L203-204 verbatim
lemma universalStateGNS_apply (a : A) (x : UniversalStateHilbert A) (f : PositiveStateIndex A) :
    universalStateGNS A a x f = f.1.gnsStarAlgHom a (x f) := rfl


-- @@ L206-218 verbatim
theorem universalStateGNS_injective : Function.Injective (universalStateGNS A) := by
  cases subsingleton_or_nontrivial A with
  | inl h => exact fun _ _ _ => Subsingleton.elim _ _
  | inr h =>
    apply (universalStateGNS A).toLinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply stateGNS_separates a
    intro f hf1
    have h := (hilbertSumRepresentation_eq_iff
      (fun g : PositiveStateIndex A => g.1.gnsStarAlgHom) a 0).mp
      (ha.trans (map_zero (universalStateGNS A)).symm) ⟨f, hf1⟩
    simpa only [map_zero] using h


-- @@ L220-220 verbatim
end Pureness


-- @@ L222-222 verbatim
noncomputable section


-- @@ L224-224 verbatim
namespace Pureness


-- @@ L226-226 verbatim
variable (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L228-230 verbatim
@[instance_reducible]
def universalStateHilbertNormedAddCommGroup :
    NormedAddCommGroup (UniversalStateHilbert A) := inferInstance


-- @@ L232-232 verbatim
attribute [local instance] universalStateHilbertNormedAddCommGroup


-- @@ L234-236 verbatim
@[instance_reducible]
def universalStateHilbertInnerProductSpace :
    InnerProductSpace ℂ (UniversalStateHilbert A) := inferInstance


-- @@ L238-239 verbatim
theorem universalStateHilbertCompleteSpace :
    CompleteSpace (UniversalStateHilbert A) := inferInstance


-- @@ L241-241 verbatim
end Pureness


-- @@ L243-243 verbatim
noncomputable section


-- @@ L245-245 verbatim
namespace Pureness


-- @@ L247-247 verbatim
variable (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L249-249 verbatim
def StateHilbertSpace := UniversalStateHilbert A


-- @@ L251-252 verbatim
instance stateHilbertNormedAddCommGroup : NormedAddCommGroup (StateHilbertSpace A) :=
  inferInstanceAs (NormedAddCommGroup (UniversalStateHilbert A))


-- @@ L254-255 verbatim
instance stateHilbertInnerProductSpace : InnerProductSpace ℂ (StateHilbertSpace A) :=
  inferInstanceAs (InnerProductSpace ℂ (UniversalStateHilbert A))


-- @@ L257-258 verbatim
instance stateHilbertCompleteSpace : CompleteSpace (StateHilbertSpace A) :=
  inferInstanceAs (CompleteSpace (UniversalStateHilbert A))


-- @@ L260-262 verbatim
def stateHilbertRepresentation : A →⋆ₐ[ℂ]
    (StateHilbertSpace A →L[ℂ] StateHilbertSpace A) :=
  universalStateGNS A


-- @@ L264-265 verbatim
theorem stateHilbertRepresentation_injective :
    Function.Injective (stateHilbertRepresentation A) := universalStateGNS_injective A


-- @@ L267-267 verbatim
end Pureness


-- @@ L269-269 verbatim
end


-- @@ L271-271 verbatim
end


-- @@ L273-273 verbatim
end


-- @@ L275-275 verbatim
end


-- @@ L277-277 verbatim
end


-- @@ L279-279 verbatim
end


-- @@ L281-281 verbatim
end


-- @@ L283-283 verbatim
end


-- @@ L285-285 verbatim
end


-- @@ L287-287 verbatim
end


-- @@ L289-289 verbatim
end


-- @@ L291-291 verbatim
end


-- @@ L293-293 verbatim
end


-- @@ L295-295 verbatim
end


-- @@ L297-297 verbatim
end


-- @@ L299-299 verbatim
end OAI
