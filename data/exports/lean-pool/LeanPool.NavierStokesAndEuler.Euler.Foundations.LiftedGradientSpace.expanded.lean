/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace


-- @@ L14-20 verbatim
/-!
An actual L² realization of the lifted pressure-gradient space on R³ × (R / period Z).
The generating vectors are L² representatives of Dφ, for smooth compactly supported
scalar test functions φ.  Smoothness is expressed through local lifts to R³ × R.
The angular measure here has total mass `period`; renormalizing it changes only a
fixed scalar in the L² norm and not the gradient subspace or projection.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace EulerLiftedGradientSpace


-- @@ L28-28 verbatim
open MeasureTheory InnerProductSpace

-- @@ L29-29 verbatim
open scoped ContDiff ENNReal Topology


-- @@ L31-32 verbatim
/-- Three dimensional real Euclidean vectors. -/
abbrev Vector3 := EuclideanSpace ℝ (Fin 3)

-- @@ L33-34 verbatim
/-- The spatial cylinder with one periodic angle coordinate. -/
abbrev LiftDomain (period : ℝ) := Vector3 × AddCircle period

-- @@ L35-36 verbatim
/-- The four dimensional real covering space of the cylinder. -/
abbrev LiftTangent := Vector3 × ℝ


-- @@ L38-38 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L40-42 verbatim
/-- Product Lebesgue and angle Haar measure on the cylinder. -/
def liftMeasure : Measure (LiftDomain period) :=
  (volume : Measure Vector3).prod (volume : Measure (AddCircle period))


-- @@ L44-46 verbatim
instance liftMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts (liftMeasure period) := by
  unfold liftMeasure
  infer_instance


-- @@ L48-49 verbatim
/-- The genuine Hilbert space of square integrable vector fields on the cylinder. -/
abbrev LiftL2 := Lp Vector3 2 (liftMeasure period)


-- @@ L51-53 verbatim
/-- The scalar field pulled back to covering coordinates centered at x. -/
def localLift (φ : LiftDomain period → ℝ) (x : LiftDomain period) : LiftTangent → ℝ :=
  fun h => φ (x.1 + h.1, x.2 + (h.2 : AddCircle period))


-- @@ L55-57 verbatim
/-- The quotient covering map from the real tangent space to the cylinder. -/
def coveringMap : LiftTangent → LiftDomain period :=
  fun z => (z.1, (z.2 : AddCircle period))


-- @@ L59-61 verbatim
omit [Fact (0 < period)] in
theorem coveringMap_isOpenQuotient : IsOpenQuotientMap (coveringMap period) :=
  IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk


-- @@ L63-67 verbatim
omit [Fact (0 < period)] in
theorem localLift_cover (φ : LiftDomain period → ℝ) (z : LiftTangent) :
    localLift period φ (coveringMap period z) = fun h => localLift period φ 0 (z + h) := by
  funext h
  simp [localLift, coveringMap]


-- @@ L69-73 verbatim
omit [Fact (0 < period)] in
theorem fderiv_localLift_cover (φ : LiftDomain period → ℝ) (z : LiftTangent) :
    fderiv ℝ (localLift period φ (coveringMap period z)) 0 =
      fderiv ℝ (localLift period φ 0) z := by
  rw [localLift_cover, fderiv_comp_add_left, add_zero]


-- @@ L75-80 verbatim
/-- The actual differential expression `κ ∇_y φ + m ∂_θ φ`. -/
def liftedGradient (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (x : LiftDomain period) : Vector3 :=
  WithLp.toLp 2 fun i =>
    κ * fderiv ℝ (localLift period φ x) 0 (EuclideanSpace.single i 1, 0) +
      m i * fderiv ℝ (localLift period φ x) 0 (0, 1)


-- @@ L82-100 verbatim
omit [Fact (0 < period)] in
theorem liftedGradient_continuous (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    Continuous (liftedGradient period κ m φ) := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have hd : Continuous (fderiv ℝ (localLift period φ 0)) :=
    (hφ 0).continuous_fderiv (by simp)
  have hcomp : liftedGradient period κ m φ ∘ coveringMap period =
      fun z => WithLp.toLp 2 fun i =>
        κ * fderiv ℝ (localLift period φ 0) z (EuclideanSpace.single i 1, 0) +
          m i * fderiv ℝ (localLift period φ 0) z (0, 1) := by
    funext z
    simp only [Function.comp_def, liftedGradient, fderiv_localLift_cover]
  rw [hcomp]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  exact (continuous_const.mul (hd.clm_apply continuous_const)).add
    (continuous_const.mul (hd.clm_apply continuous_const))


-- @@ L102-119 verbatim
omit [Fact (0 < period)] in
theorem liftedGradient_zero_of_notMem_tsupport (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (x : LiftDomain period) (hx : x ∉ tsupport φ) :
    liftedGradient period κ m φ x = 0 := by
  have hc : Continuous (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) :=
    (continuous_const.add continuous_fst).prodMk
      (continuous_const.add ((AddCircle.continuous_mk' period).comp continuous_snd))
  have ht : Filter.Tendsto (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto (0 : LiftTangent)
  have hz : localLift period φ x =ᶠ[𝓝 0] (fun _ : LiftTangent => (0 : ℝ)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto ht
  have hd : fderiv ℝ (localLift period φ x) 0 = 0 := by
    rw [hz.fderiv_eq]
    simp
  simp [liftedGradient, hd]
  rfl


-- @@ L121-125 verbatim
omit [Fact (0 < period)] in
theorem liftedGradient_hasCompactSupport (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (liftedGradient period κ m φ) :=
  HasCompactSupport.intro hφ (liftedGradient_zero_of_notMem_tsupport period κ m φ)


-- @@ L127-132 verbatim
/-- Every smooth compact test has an actual L² lifted gradient. -/
theorem liftedGradient_memLp (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    MemLp (liftedGradient period κ m φ) 2 (liftMeasure period) := by
  exact (liftedGradient_continuous period κ m φ hφ.2).memLp_of_hasCompactSupport
    (liftedGradient_hasCompactSupport period κ m φ hφ.1)


-- @@ L134-136 verbatim
/-- Translation of a scalar test function on the cylinder. -/
def translatedTest (a : LiftDomain period) (φ : LiftDomain period → ℝ) :
    LiftDomain period → ℝ := fun x => φ (x + a)


-- @@ L138-146 verbatim
omit [Fact (0 < period)] in
@[simp]
theorem localLift_translated (a x : LiftDomain period) (φ : LiftDomain period → ℝ) :
    localLift period (translatedTest period a φ) x = localLift period φ (x + a) := by
  funext h
  change φ (x.1 + h.1 + a.1, x.2 + (h.2 : AddCircle period) + a.2) =
    φ (x.1 + a.1 + h.1, x.2 + a.2 + (h.2 : AddCircle period))
  congr 1
  exact Prod.ext (add_right_comm _ _ _) (add_right_comm _ _ _)


-- @@ L148-155 verbatim
omit [Fact (0 < period)] in
theorem smoothCompactTest_translated (a : LiftDomain period) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    HasCompactSupport (translatedTest period a φ) ∧
      ∀ x, ContDiff ℝ ∞ (localLift period (translatedTest period a φ) x) := by
  refine ⟨hφ.1.comp_homeomorph (Homeomorph.addRight a), fun x => ?_⟩
  rw [localLift_translated]
  exact hφ.2 (x + a)


-- @@ L157-163 verbatim
omit [Fact (0 < period)] in
@[simp]
theorem liftedGradient_translated (κ : ℝ) (m : Vector3) (a x : LiftDomain period)
    (φ : LiftDomain period → ℝ) :
    liftedGradient period κ m (translatedTest period a φ) x =
      liftedGradient period κ m φ (x + a) := by
  simp only [liftedGradient, localLift_translated]


-- @@ L165-169 verbatim
theorem measurePreserving_translation (a : LiftDomain period) :
    MeasurePreserving (fun x : LiftDomain period => x + a)
      (liftMeasure period) (liftMeasure period) := by
  exact (measurePreserving_add_right (volume : Measure Vector3) a.1).prod
    (measurePreserving_add_right (volume : Measure (AddCircle period)) a.2)


-- @@ L171-174 verbatim
/-- The measure preserving translation isometry on the actual L² space. -/
def translation (a : LiftDomain period) : LiftL2 period →ₗᵢ[ℝ] LiftL2 period :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : LiftDomain period => x + a)
    (measurePreserving_translation period a)


-- @@ L176-178 verbatim
theorem translation_ae (a : LiftDomain period) (f : LiftL2 period) :
    translation period a f =ᵐ[liftMeasure period] fun x => f (x + a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_translation period a)


-- @@ L180-182 verbatim
theorem translation_norm (a : LiftDomain period) (f : LiftL2 period) :
    ‖translation period a f‖ = ‖f‖ :=
  (translation period a).norm_map f


-- @@ L184-190 verbatim
theorem translation_add (a b : LiftDomain period) (f : LiftL2 period) :
    translation period a (translation period b f) = translation period (a + b) f := by
  apply Lp.ext
  filter_upwards [translation_ae period a (translation period b f),
    (measurePreserving_translation period a).quasiMeasurePreserving.ae
      (translation_ae period b f), translation_ae period (a + b) f] with x hx₁ hx₂ hx₃
  rw [hx₁, hx₂, hx₃, add_assoc]


-- @@ L192-196 verbatim
@[simp]
theorem translation_zero (f : LiftL2 period) : translation period 0 f = f := by
  apply Lp.ext
  filter_upwards [translation_ae period 0 f] with x hx
  simpa only [add_zero] using hx


-- @@ L198-201 verbatim
/-- The L² element represented by an actual smooth compact test gradient. -/
def testGradientLp (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) : LiftL2 period :=
  (liftedGradient_memLp period κ m φ hφ).toLp (liftedGradient period κ m φ)


-- @@ L203-206 verbatim
theorem testGradientLp_ae (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    testGradientLp period κ m φ hφ =ᵐ[liftMeasure period] liftedGradient period κ m φ :=
  (liftedGradient_memLp period κ m φ hφ).coeFn_toLp


-- @@ L208-215 verbatim
theorem testGradientLp_mem_generators (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    testGradientLp period κ m φ hφ ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
        EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
            (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
                =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                    EulerLiftedGradientSpace.liftedGradient period κ m φ}) :=
  ⟨φ, hφ, testGradientLp_ae period κ m φ hφ⟩


-- @@ L217-223 verbatim
/-- Closure of the span of genuine smooth test gradients in the concrete L² space. -/
def gradientSpace (κ : ℝ) (m : Vector3) : Submodule ℝ (LiftL2 period) :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
      EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
          (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
              =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                  EulerLiftedGradientSpace.liftedGradient period κ m φ}))).topologicalClosure


-- @@ L225-232 verbatim
theorem gradientSpace_closed (κ : ℝ) (m : Vector3) :
    IsClosed (gradientSpace period κ m : Set (LiftL2 period)) :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
      EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
          (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
              =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                  EulerLiftedGradientSpace.liftedGradient period κ m
                      φ}))).isClosed_topologicalClosure


-- @@ L234-236 verbatim
instance gradientSpace_complete (κ : ℝ) (m : Vector3) :
    CompleteSpace (gradientSpace period κ m) :=
  (gradientSpace_closed period κ m).completeSpace_coe


-- @@ L238-240 verbatim
/-- Orthogonal projection onto the closed lifted gradient subspace. -/
def gradientProjection (κ : ℝ) (m : Vector3) : LiftL2 period →L[ℝ] LiftL2 period :=
  (gradientSpace period κ m).starProjection


-- @@ L242-245 verbatim
/-- The projection bound is independent of the frequency parameter κ. -/
theorem gradientProjection_norm_le (κ : ℝ) (m : Vector3) :
    ‖gradientProjection period κ m‖ ≤ 1 :=
  (gradientSpace period κ m).starProjection_norm_le


-- @@ L247-249 verbatim
theorem gradientProjection_apply_norm_le (κ : ℝ) (m : Vector3) (f : LiftL2 period) :
    ‖gradientProjection period κ m f‖ ≤ ‖f‖ :=
  (gradientSpace period κ m).norm_starProjection_apply_le f


-- @@ L251-263 verbatim
theorem testGradient_mem (κ : ℝ) (m : Vector3) {g : LiftL2 period}
    (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
        EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
            (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
                =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                    EulerLiftedGradientSpace.liftedGradient period κ m φ})) : g ∈ gradientSpace
                        period κ m :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
      EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
          (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
              =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                  EulerLiftedGradientSpace.liftedGradient period κ m φ}))).le_topologicalClosure
    (Submodule.subset_span hg)


-- @@ L265-280 verbatim
theorem gradientGenerators_translated (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    {g : LiftL2 period} (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
        EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
            (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
                =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                    EulerLiftedGradientSpace.liftedGradient period κ m φ})) :
    translation period a g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
        EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
            (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
                =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                    EulerLiftedGradientSpace.liftedGradient period κ m φ}) := by
  obtain ⟨φ, hφ, hgφ⟩ := hg
  refine ⟨translatedTest period a φ, smoothCompactTest_translated period a φ hφ, ?_⟩
  filter_upwards [translation_ae period a g,
    (measurePreserving_translation period a).quasiMeasurePreserving.ae hgφ] with x hx₁ hx₂
  rw [hx₁, hx₂, liftedGradient_translated]


-- @@ L282-297 verbatim
theorem gradientSpace_translation_mem (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    {g : LiftL2 period} (hg : g ∈ gradientSpace period κ m) :
    translation period a g ∈ gradientSpace period κ m := by
  let τ := (translation period a).toContinuousLinearMap
  have hspan : Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
      EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
          (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
              =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                  EulerLiftedGradientSpace.liftedGradient period κ m φ})) ≤
      (gradientSpace period κ m).comap τ.toLinearMap := by
    apply Submodule.span_le.2
    intro f hf
    exact testGradient_mem period κ m (gradientGenerators_translated period κ m a hf)
  have hclosed : IsClosed ((gradientSpace period κ m).comap τ.toLinearMap : Set (LiftL2 period)) :=
    (gradientSpace_closed period κ m).preimage τ.continuous
  exact (Submodule.topologicalClosure_minimal _ hspan hclosed) hg


-- @@ L299-308 verbatim
theorem gradientSpace_map_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period) :
    (gradientSpace period κ m).map (translation period a).toLinearMap =
      gradientSpace period κ m := by
  apply le_antisymm
  · rintro g ⟨f, hf, rfl⟩
    exact gradientSpace_translation_mem period κ m a hf
  · intro g hg
    refine ⟨translation period (-a) g, gradientSpace_translation_mem period κ m (-a) hg, ?_⟩
    change translation period a (translation period (-a) g) = g
    rw [translation_add, add_neg_cancel, translation_zero]


-- @@ L310-321 verbatim
/-- Orthogonal pressure projection commutes with every spatial or angular translation. -/
theorem gradientProjection_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    (f : LiftL2 period) :
    translation period a (gradientProjection period κ m f) =
      gradientProjection period κ m (translation period a f) := by
  have hmap := gradientSpace_map_translation period κ m a
  let : ((gradientSpace period κ m).map (translation period a).toLinearMap).HasOrthogonalProjection
      := by
    rw [hmap]
    infer_instance
  simpa only [gradientProjection, hmap] using
    (translation period a).map_starProjection (gradientSpace period κ m) f


-- @@ L323-325 verbatim
/-- The concrete L² weak divergence-free subspace. -/
def divergenceFreeSpace (κ : ℝ) (m : Vector3) : Submodule ℝ (LiftL2 period) :=
  (gradientSpace period κ m).orthogonal


-- @@ L327-330 verbatim
/-- Pressure cancellation in the concrete lifted L² space. -/
theorem pressure_pairing_zero (κ : ℝ) (m : Vector3) {p e : LiftL2 period}
    (hp : p ∈ gradientSpace period κ m) (he : e ∈ divergenceFreeSpace period κ m) :
    ⟪p, e⟫_ℝ = 0 := he p hp


-- @@ L332-340 verbatim
theorem testGradient_pairing_zero (κ : ℝ) (m : Vector3) {g e : LiftL2 period}
    (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ :
        EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞
            (EulerLiftedGradientSpace.localLift period φ x)) ∧ g
                =ᵐ[EulerLiftedGradientSpace.liftMeasure period]
                    EulerLiftedGradientSpace.liftedGradient period κ m φ})) (he : e ∈
                        divergenceFreeSpace period κ m) :
    ⟪g, e⟫_ℝ = 0 :=
  pressure_pairing_zero period κ m (testGradient_mem period κ m hg) he


-- @@ L342-353 verbatim
/-- Orthogonality is the actual weak-divergence integral against every smooth compact test. -/
theorem weak_divergence_test_integral (κ : ℝ) (m : Vector3) {e : LiftL2 period}
    (he : e ∈ divergenceFreeSpace period κ m) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    ∫ x, ⟪liftedGradient period κ m φ x, e x⟫_ℝ ∂liftMeasure period = 0 := by
  have hz := testGradient_pairing_zero period κ m
    (testGradientLp_mem_generators period κ m φ hφ) he
  rw [MeasureTheory.L2.inner_def] at hz
  rw [← hz]
  apply integral_congr_ae
  filter_upwards [testGradientLp_ae period κ m φ hφ] with x hx
  rw [hx]


-- @@ L355-355 verbatim
end EulerLiftedGradientSpace
