import Mathlib
import OAI.Probability.Subsphere.Regression.Spheres


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
section

-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L8-8 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
namespace SubsphereCurrent.Mixture

-- @@ L11-11 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


-- @@ L13-14 verbatim
instance orthogonal_probability : IsProbabilityMeasure (orthogonalLaw (E := E)) :=
  ⟨Measure.haarMeasure_self⟩


-- @@ L16-18 verbatim
instance orthogonal_haar : (orthogonalLaw (E := E)).IsHaarMeasure := by
  unfold orthogonalLaw
  infer_instance


-- @@ L20-23 verbatim
instance orthogonal_right : (orthogonalLaw (E := E)).IsMulRightInvariant := by
  constructor
  intro u
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _


-- @@ L25-25 verbatim
def act (u : Orthogonal E) (x : E) : E := (u.val : E →L[ℝ] E) x


-- @@ L27-29 verbatim
lemma continuous_act : Continuous (fun z : Orthogonal E × E => act z.1 z.2) := by
  unfold act
  fun_prop


-- @@ L31-31 verbatim
lemma act_mul (u v : Orthogonal E) (x : E) : act (u*v) x = act u (act v x) := rfl


-- @@ L33-33 verbatim
lemma act_one (x : E) : act (1 : Orthogonal E) x = x := rfl


-- @@ L35-35 verbatim
lemma act_norm (u : Orthogonal E) (x : E) : ‖act u x‖ = ‖x‖ := Unitary.norm_map u x


-- @@ L37-42 verbatim
lemma exists_act {x y : E} (h : ‖x‖ = ‖y‖) : ∃ u : Orthogonal E, act u x = y := by
  let e := (ℝ ∙ (x-y))ᗮ.reflection
  refine ⟨Unitary.linearIsometryEquiv.symm e,?_⟩
  change Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm e) x = y
  rw [MulEquiv.apply_symm_apply]
  exact Submodule.reflection_sub h


-- @@ L44-44 verbatim
variable [MeasurableSpace E] [BorelSpace E]


-- @@ L46-53 verbatim
lemma haar_integral_independent {x y : E} (h : ‖x‖ = ‖y‖)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f (act u x) ∂orthogonalLaw) = ∫⁻ u, f (act u y) ∂orthogonalLaw := by
  obtain ⟨v,hv⟩ := exists_act h
  have hr := measurePreserving_mul_right (orthogonalLaw (E := E)) v
  have hf' : Measurable (fun u : Orthogonal E => f (act u x)) :=
    hf.comp (continuous_act.comp (continuous_id.prodMk continuous_const)).measurable
  simpa only [Function.comp_def,act_mul,hv] using (hr.lintegral_comp hf').symm


-- @@ L55-71 verbatim
lemma haar_eval_integral [Nontrivial E] {x : E} (hx : ‖x‖ = 1)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f (act u x) ∂orthogonalLaw) = ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw := by
  have hm : Measurable (fun z : E × Orthogonal E => f (act z.2 z.1)) :=
    hf.comp (continuous_act.comp continuous_swap).measurable
  have he : (∫⁻ y, ∫⁻ u, f (act u y) ∂orthogonalLaw ∂SubsphereRegression.ambientSphereLaw) =
      ∫⁻ _ : E, (∫⁻ u, f (act u x) ∂orthogonalLaw) ∂SubsphereRegression.ambientSphereLaw := by
    apply lintegral_congr_ae
    filter_upwards [SubsphereRegression.ambientSphereLaw_ae_norm] with y hy
    exact haar_integral_independent (hy.trans hx.symm) hf
  have hrot (u : Orthogonal E) :
      (∫⁻ y, f (act u y) ∂SubsphereRegression.ambientSphereLaw) =
      ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw :=
    (SubsphereRegression.ambientSphereLaw_isometry (Unitary.linearIsometryEquiv u)).lintegral_comp hf
  rw [lintegral_lintegral_swap hm.aemeasurable] at he
  simp_rw [hrot] at he
  simpa using he.symm


-- @@ L73-88 verbatim
lemma haar_eval_preserving [Nontrivial E] {x : E} (hx : ‖x‖ = 1) :
    MeasurePreserving (fun u : Orthogonal E => act u x) orthogonalLaw
      SubsphereRegression.ambientSphereLaw := by
  refine ⟨(continuous_act.comp (continuous_id.prodMk continuous_const)).measurable,?_⟩
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun u : Orthogonal E => act u x) :=
    (continuous_act.comp (continuous_id.prodMk continuous_const)).measurable
  rw [Measure.map_apply hm hs]
  have hi := haar_eval_integral hx ((measurable_const : Measurable (fun _ : E => (1 : ℝ≥0∞))).indicator hs)
  have he : (fun u : Orthogonal E => s.indicator (fun _ => (1 : ℝ≥0∞)) (act u x)) =
      ((fun u : Orthogonal E => act u x) ⁻¹' s).indicator (fun _ => 1) := by
    funext u
    by_cases h : act u x ∈ s <;> simp [Set.indicator,h]
  rw [he,lintegral_indicator_const (hs.preimage hm),lintegral_indicator_const hs] at hi
  simpa using hi


-- @@ L90-90 verbatim
end SubsphereCurrent.Mixture

-- @@ L91-91 verbatim
end

-- @@ L92-92 verbatim
end

-- @@ L93-93 verbatim
section

-- @@ L94-94 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L95-95 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L96-96 verbatim
noncomputable section

-- @@ L97-97 verbatim
namespace SubsphereCurrent.Mixture

-- @@ L98-98 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


-- @@ L100-105 verbatim
lemma blockIso_apply (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : E) :
    blockIso V u w x = (act (E := V) u (V.orthogonalProjectionOnto x) : E) +
      (act (E := Vᗮ) w (Vᗮ.orthogonalProjectionOnto x) : E) := by
  simp only [blockIso,LinearIsometryEquiv.trans_apply,Submodule.orthogonalDecomposition_symm_apply,
    Submodule.orthogonalDecomposition_apply,LinearIsometryEquiv.withLpProdCongr_apply]
  rfl


-- @@ L107-113 verbatim
lemma continuous_blockIso (V : Submodule ℝ E) :
    Continuous (fun z : (Orthogonal V × Orthogonal Vᗮ) × E => blockIso V z.1.1 z.1.2 z.2) := by
  simp only [blockIso_apply]
  exact ((continuous_subtype_val.comp (continuous_act.comp
      ((continuous_fst.comp continuous_fst).prodMk (V.orthogonalProjectionOnto.continuous.comp continuous_snd)))).add
    (continuous_subtype_val.comp (continuous_act.comp
      ((continuous_snd.comp continuous_fst).prodMk (Vᗮ.orthogonalProjectionOnto.continuous.comp continuous_snd)))))


-- @@ L115-117 verbatim
@[simp] lemma blockIso_one (V : Submodule ℝ E) (x : E) : blockIso V 1 1 x = x := by
  rw [blockIso_apply,act_one,act_one]
  exact V.starProjection_add_starProjection_orthogonal x


-- @@ L119-122 verbatim
@[simp] lemma blockIso_on_left (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : V) :
    blockIso V u w (x : E) = ((act (E := V) u x : V) : E) := by
  rw [blockIso_apply,Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp [act]


-- @@ L124-127 verbatim
@[simp] lemma blockIso_on_right (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : Vᗮ) :
    blockIso V u w (x : E) = ((act (E := Vᗮ) w x : Vᗮ) : E) := by
  rw [blockIso_apply,V.orthogonalProjectionOnto_apply_of_mem_orthogonal x.prop]
  simp [act]


-- @@ L129-132 verbatim
lemma blockIso_mul (V : Submodule ℝ E) (u u' : Orthogonal V) (w w' : Orthogonal Vᗮ) (x : E) :
    blockIso V (u*u') (w*w') x = blockIso V u w (blockIso V u' w' x) := by
  rw [blockIso_apply V u' w',map_add,blockIso_on_left,blockIso_on_right]
  rw [blockIso_apply,act_mul,act_mul]


-- @@ L134-137 verbatim
lemma blockIso_comp (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    blockIso V u w = (blockIso V u 1).trans (blockIso V 1 w) := by
  ext x
  simpa using (blockIso_mul V 1 u w 1 x)


-- @@ L139-139 verbatim
end SubsphereCurrent.Mixture

-- @@ L140-140 verbatim
end

-- @@ L141-141 verbatim
end

-- @@ L142-142 verbatim
section

-- @@ L143-143 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L144-144 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L145-145 verbatim
noncomputable section

-- @@ L146-146 verbatim
namespace SubsphereCurrent.Mixture

-- @@ L147-148 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


-- @@ L150-150 verbatim
end SubsphereCurrent.Mixture

-- @@ L151-151 verbatim
end

-- @@ L152-152 verbatim
end

-- @@ L153-153 verbatim
section

-- @@ L154-154 verbatim
noncomputable section

-- @@ L155-155 verbatim
universe u v w

-- @@ L156-156 verbatim
namespace SubsphereCurrent


-- @@ L158-158 verbatim
end SubsphereCurrent

-- @@ L159-159 verbatim
end

-- @@ L160-160 verbatim
end


-- @@ L162-162 verbatim
end OAI
