import OAI.Probability.ProjectionMoments.Asymptotics


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section


-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L8-8 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
namespace ProjectionMoments

-- @@ L11-11 verbatim
open NoiselessRegression

-- @@ L12-12 verbatim
variable {d : ℕ}


-- @@ L14-15 verbatim
def extendSphereWeight (f : UnitSphere d → ℝ≥0∞) : Vector d → ℝ≥0∞ :=
  Function.extend Subtype.val f (fun _ => 0)


-- @@ L17-19 verbatim
@[simp] lemma extendSphereWeight_val (f : UnitSphere d → ℝ≥0∞) (s : UnitSphere d) :
    extendSphereWeight f s.val = f s :=
  Subtype.val_injective.extend_apply f (fun _ => 0) s


-- @@ L21-23 verbatim
lemma measurable_extendSphereWeight {f : UnitSphere d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (extendSphereWeight f) :=
  (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).measurable_extend hf measurable_const


-- @@ L25-32 verbatim
lemma extendSphereWeight_le_one {f : UnitSphere d → ℝ≥0∞} (hf : ∀ s, f s ≤ 1) :
    ∀ x, extendSphereWeight f x ≤ 1 := by
  intro x
  by_cases hx : ∃ s : UnitSphere d, s.val = x
  · obtain ⟨s,rfl⟩ := hx
    simpa using hf s
  · rw [extendSphereWeight,Function.extend_apply' _ _ _ hx]
    exact zero_le_one


-- @@ L34-45 verbatim
lemma sphereWeight_measure (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    ambientSphereLaw.withDensity (extendSphereWeight f) =
      ((uniformSphere d).withDensity f).map Subtype.val := by
  ext S hS
  rw [withDensity_apply _ hS,Measure.map_apply measurable_subtype_coe hS,
    withDensity_apply _ (measurable_subtype_coe hS)]
  change (∫⁻ x in S, extendSphereWeight f x ∂(uniformSphere d).map Subtype.val) = _
  rw [← lintegral_indicator hS,lintegral_map ((measurable_extendSphereWeight hf).indicator hS)
      measurable_subtype_coe,← lintegral_indicator (measurable_subtype_coe hS)]
  apply lintegral_congr
  intro s
  by_cases hs : s.val ∈ S <;> simp [hs,extendSphereWeight_val]


-- @@ L47-58 verbatim
lemma sphereWeight_potential (α : ℝ) (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f) :
    rieszPotential α (extendSphereWeight f) =
      ⨆ z : Vector d, ∫⁻ s, f s * (ENNReal.ofReal ‖s.val-z‖)^(-α) ∂uniformSphere d := by
  unfold rieszPotential
  congr 1
  funext z
  change (∫⁻ x, extendSphereWeight f x*rieszKernel α z x ∂(uniformSphere d).map Subtype.val) = _
  rw [lintegral_map (show Measurable (fun x => extendSphereWeight f x*rieszKernel α z x) from
    (measurable_extendSphereWeight hf).mul (measurable_rieszKernel α z)) measurable_subtype_coe]
  apply lintegral_congr
  intro s
  simp only [extendSphereWeight_val,rieszKernel]


-- @@ L60-70 verbatim
lemma sphereWeight_restriction (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f)
    (H : Set (UnitSphere d)) (hH : MeasurableSet H) :
    sphereWeightedRestriction (extendSphereWeight f) (Subtype.val '' H) =
      (((uniformSphere d).withDensity f).restrict H).map Subtype.val := by
  have he := MeasurableEmbedding.subtype_coe (Metric.isClosed_sphere.measurableSet :
    MeasurableSet (Metric.sphere (0 : Vector d) 1))
  rw [sphereWeightedRestriction,sphereWeight_measure f hf,Measure.restrict_map measurable_subtype_coe
    (he.measurableSet_image.mpr hH)]
  congr 1
  congr 1
  exact Set.preimage_image_eq _ Subtype.val_injective


-- @@ L72-78 verbatim
lemma sphere_weight_representation (f : UnitSphere d → ℝ≥0∞) (hf : Measurable f)
    (hf1 : ∀ s, f s ≤ 1) :
    ∃ F : Vector d → ℝ≥0∞, Measurable F ∧ (∀ x, F x ≤ 1) ∧
      (∀ s : UnitSphere d, F s.val = f s) ∧
      ambientSphereLaw.withDensity F = ((uniformSphere d).withDensity f).map Subtype.val :=
  ⟨extendSphereWeight f,measurable_extendSphereWeight hf,extendSphereWeight_le_one hf1,
    extendSphereWeight_val f,sphereWeight_measure f hf⟩


-- @@ L80-80 verbatim
end ProjectionMoments

-- @@ L81-81 verbatim
end


-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end OAI
