import Submission.ProductionMorseEventLocalGeometry


-- @@ L3-12 verbatim
/-!
# Embedded local charts for production Morse events

`StandardMorseEventAt` deliberately stores only the data needed to assemble a
Morse atlas.  Framed circle and splice arguments additionally need one smaller
ball on which the event parameter is an immersed embedding.  This file makes
that extra *local* input route-independent, proves the definite-circle orbit
package from it, and constructs it for the assumption-free shared-cutoff plus
critical-value-separation route.
-/


-- @@ L14-14 verbatim
set_option autoImplicit false

-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function Metric Filter

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
variable {n : ℕ}


-- @@ L24-24 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L26-26 verbatim
namespace StandardMorseEventAt


-- @@ L28-29 verbatim
variable {C : FramedLevelCobordism n}
  {center : EuclideanSpace ℝ (Fin (n + 2))}


-- @@ L31-44 verbatim
/-- A smaller event ball on which the ambient parameter is an immersed
embedding.  This is the precise common interface needed by the definite-circle
and transported-tangent arguments; it is not tied to either global
construction route. -/
structure EmbeddedShrink
    (M : StandardMorseEventAt (n := n) C center) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ M.radius
  param_differentiableAt : ∀ u : E₂, ‖u‖ < radius →
    DifferentiableAt ℝ M.param u
  fderiv_param_injective : ∀ u : E₂, ‖u‖ < radius →
    Injective (fderiv ℝ M.param u)
  param_injOn : Set.InjOn M.param (ball (0 : E₂) radius)


-- @@ L46-46 verbatim
namespace EmbeddedShrink


-- @@ L48-48 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L50-51 verbatim
theorem radius_le_event (T : M.EmbeddedShrink) : 0 < M.radius :=
  T.radius_pos.trans_le T.radius_le


-- @@ L53-65 verbatim
/-- The ambient once-around circle supplied by any embedded standard event. -/
def definiteCircleCurve (T : M.EmbeddedShrink)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius) :
    C(I, EuclideanSpace ℝ (Fin (n + 2))) where
  toFun u := M.definiteCircle a (2 * Real.pi * (u : ℝ))
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro u
    apply (T.param_differentiableAt _ ?_).continuousAt.comp'
      (definiteCircleParamCurve a).continuous.continuousAt
    change ‖definiteCircleParam a (2 * Real.pi * (u : ℝ))‖ < T.radius
    rw [norm_definiteCircleParam ha.le]
    exact har


-- @@ L67-73 verbatim
/-- Spatial projection of the embedded definite circle. -/
def definiteSpatialCircle (T : M.EmbeddedShrink)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius) :
    C(I, EuclideanSpace ℝ (Fin (n + 1))) where
  toFun u := spacePart (T.definiteCircleCurve a ha har u)
  continuous_toFun := continuous_spacePart.comp
    (T.definiteCircleCurve a ha har).continuous


-- @@ L75-81 verbatim
theorem definiteCircleCurve_closed (T : M.EmbeddedShrink)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius) :
    T.definiteCircleCurve a ha har 0 =
      T.definiteCircleCurve a ha har 1 := by
  change M.param (definiteCircleParamCurve a 0) =
    M.param (definiteCircleParamCurve a 1)
  rw [definiteCircleParamCurve_closed]


-- @@ L83-119 verbatim
/-- Spatial simple-closedness for an embedded minimum circle. -/
theorem minimumSpatialCircle_eq_cases (T : M.EmbeddedShrink)
    (hindex : M.index = .minimum)
    {a : ℝ} (ha : 0 < a) (har : a < T.radius)
    {u v : I}
    (huv : T.definiteSpatialCircle a ha har u =
      T.definiteSpatialCircle a ha har v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  let thetaU : ℝ := 2 * Real.pi * (u : ℝ)
  let thetaV : ℝ := 2 * Real.pi * (v : ℝ)
  change spacePart (M.definiteCircle a thetaU) =
    spacePart (M.definiteCircle a thetaV) at huv
  have hrad : a < M.radius := har.trans_le T.radius_le
  have htimeU := M.minimumCircle_time hindex
    (theta := thetaU) ha.le hrad
  have htimeV := M.minimumCircle_time hindex
    (theta := thetaV) ha.le hrad
  have hamb : M.definiteCircle a thetaU = M.definiteCircle a thetaV := by
    calc
      M.definiteCircle a thetaU =
          cobSpaceTime (spacePart (M.definiteCircle a thetaU))
            (tcoord (M.definiteCircle a thetaU)) :=
        (spaceTime_spacePart _).symm
      _ = cobSpaceTime (spacePart (M.definiteCircle a thetaV))
            (tcoord (M.definiteCircle a thetaV)) := by
        rw [huv, htimeU, htimeV]
      _ = M.definiteCircle a thetaV := spaceTime_spacePart _
  have hmemU : definiteCircleParam a thetaU ∈ ball (0 : E₂) T.radius := by
    rw [mem_ball, dist_zero_right, norm_definiteCircleParam ha.le]
    exact har
  have hmemV : definiteCircleParam a thetaV ∈ ball (0 : E₂) T.radius := by
    rw [mem_ball, dist_zero_right, norm_definiteCircleParam ha.le]
    exact har
  have hparam : definiteCircleParam a thetaU =
      definiteCircleParam a thetaV :=
    T.param_injOn hmemU hmemV hamb
  exact definiteCircleParamCurve_eq_cases ha.ne' hparam


-- @@ L121-157 verbatim
/-- Spatial simple-closedness for an embedded maximum circle. -/
theorem maximumSpatialCircle_eq_cases (T : M.EmbeddedShrink)
    (hindex : M.index = .maximum)
    {a : ℝ} (ha : 0 < a) (har : a < T.radius)
    {u v : I}
    (huv : T.definiteSpatialCircle a ha har u =
      T.definiteSpatialCircle a ha har v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  let thetaU : ℝ := 2 * Real.pi * (u : ℝ)
  let thetaV : ℝ := 2 * Real.pi * (v : ℝ)
  change spacePart (M.definiteCircle a thetaU) =
    spacePart (M.definiteCircle a thetaV) at huv
  have hrad : a < M.radius := har.trans_le T.radius_le
  have htimeU := M.maximumCircle_time hindex
    (theta := thetaU) ha.le hrad
  have htimeV := M.maximumCircle_time hindex
    (theta := thetaV) ha.le hrad
  have hamb : M.definiteCircle a thetaU = M.definiteCircle a thetaV := by
    calc
      M.definiteCircle a thetaU =
          cobSpaceTime (spacePart (M.definiteCircle a thetaU))
            (tcoord (M.definiteCircle a thetaU)) :=
        (spaceTime_spacePart _).symm
      _ = cobSpaceTime (spacePart (M.definiteCircle a thetaV))
            (tcoord (M.definiteCircle a thetaV)) := by
        rw [huv, htimeU, htimeV]
      _ = M.definiteCircle a thetaV := spaceTime_spacePart _
  have hmemU : definiteCircleParam a thetaU ∈ ball (0 : E₂) T.radius := by
    rw [mem_ball, dist_zero_right, norm_definiteCircleParam ha.le]
    exact har
  have hmemV : definiteCircleParam a thetaV ∈ ball (0 : E₂) T.radius := by
    rw [mem_ball, dist_zero_right, norm_definiteCircleParam ha.le]
    exact har
  have hparam : definiteCircleParam a thetaU =
      definiteCircleParam a thetaV :=
    T.param_injOn hmemU hmemV hamb
  exact definiteCircleParamCurve_eq_cases ha.ne' hparam


-- @@ L159-164 verbatim
/-- The actual regular slice just above an embedded minimum. -/
def minimumPositiveSlice (_T : M.EmbeddedShrink) (a : ℝ)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2)) :
    FramedLevelSet n :=
  SlabTamedField.sliceFLSAt C.toLevelCobordismData
    (tcoord center + a ^ 2) hreg


-- @@ L166-171 verbatim
/-- The actual regular slice just below an embedded maximum. -/
def maximumNegativeSlice (_T : M.EmbeddedShrink) (a : ℝ)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2)) :
    FramedLevelSet n :=
  SlabTamedField.sliceFLSAt C.toLevelCobordismData
    (tcoord center - a ^ 2) hreg


-- @@ L173-187 verbatim
theorem minimumSpatialCircle_mem_fiber (T : M.EmbeddedShrink)
    (hindex : M.index = .minimum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2)) (u : I) :
    T.definiteSpatialCircle a ha har u ∈
      (T.minimumPositiveSlice a hreg).fiber := by
  rw [minimumPositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (M.definiteCircle a (2 * Real.pi * (u : ℝ))))
    (tcoord center + a ^ 2)) = 0
  rw [← M.minimumCircle_time hindex
      (theta := 2 * Real.pi * (u : ℝ)) ha.le
      (har.trans_le T.radius_le),
    spaceTime_spacePart]
  exact M.definiteCircle_fiber ha.le (har.trans_le T.radius_le)


-- @@ L189-203 verbatim
theorem maximumSpatialCircle_mem_fiber (T : M.EmbeddedShrink)
    (hindex : M.index = .maximum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2)) (u : I) :
    T.definiteSpatialCircle a ha har u ∈
      (T.maximumNegativeSlice a hreg).fiber := by
  rw [maximumNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (M.definiteCircle a (2 * Real.pi * (u : ℝ))))
    (tcoord center - a ^ 2)) = 0
  rw [← M.maximumCircle_time hindex
      (theta := 2 * Real.pi * (u : ℝ)) ha.le
      (har.trans_le T.radius_le),
    spaceTime_spacePart]
  exact M.definiteCircle_fiber ha.le (har.trans_le T.radius_le)


-- @@ L205-214 verbatim
theorem minimumSpatialCircle_mem_same_orbit (T : M.EmbeddedShrink)
    (hindex : M.index = .minimum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.minimumPositiveSlice a hreg)) (u : I) :
    T.definiteSpatialCircle a ha har u ∈
      V.orbit (T.definiteSpatialCircle a ha har 0) := by
  apply V.continuousMap_mem_orbit (T.definiteSpatialCircle a ha har)
  intro v
  exact T.minimumSpatialCircle_mem_fiber hindex a ha har hreg v


-- @@ L216-225 verbatim
theorem maximumSpatialCircle_mem_same_orbit (T : M.EmbeddedShrink)
    (hindex : M.index = .maximum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.maximumNegativeSlice a hreg)) (u : I) :
    T.definiteSpatialCircle a ha har u ∈
      V.orbit (T.definiteSpatialCircle a ha har 0) := by
  apply V.continuousMap_mem_orbit (T.definiteSpatialCircle a ha har)
  intro v
  exact T.maximumSpatialCircle_mem_fiber hindex a ha har hreg v


-- @@ L227-244 verbatim
/-- Every sufficiently small born circle is a genuine once-around parameter
of its actual orbit component. -/
def minimumSimpleClosedOrbitParam (T : M.EmbeddedShrink)
    (hindex : M.index = .minimum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.minimumPositiveSlice a hreg)) :
    SimpleClosedOrbitParam (T.minimumPositiveSlice a hreg) V where
  p := T.definiteSpatialCircle a ha har 0
  hp := T.minimumSpatialCircle_mem_fiber hindex a ha har hreg 0
  curve := T.definiteSpatialCircle a ha har
  curve_zero := rfl
  curve_closed := congrArg spacePart
    (T.definiteCircleCurve_closed a ha har)
  curve_mem_orbit := fun u =>
    T.minimumSpatialCircle_mem_same_orbit hindex a ha har hreg V u
  curve_eq_cases := fun huv =>
    T.minimumSpatialCircle_eq_cases hindex ha har huv


-- @@ L246-263 verbatim
/-- Every sufficiently small pre-death circle is likewise a genuine
once-around parameter of its actual orbit component. -/
def maximumSimpleClosedOrbitParam (T : M.EmbeddedShrink)
    (hindex : M.index = .maximum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.maximumNegativeSlice a hreg)) :
    SimpleClosedOrbitParam (T.maximumNegativeSlice a hreg) V where
  p := T.definiteSpatialCircle a ha har 0
  hp := T.maximumSpatialCircle_mem_fiber hindex a ha har hreg 0
  curve := T.definiteSpatialCircle a ha har
  curve_zero := rfl
  curve_closed := congrArg spacePart
    (T.definiteCircleCurve_closed a ha har)
  curve_mem_orbit := fun u =>
    T.maximumSpatialCircle_mem_same_orbit hindex a ha har hreg V u
  curve_eq_cases := fun huv =>
    T.maximumSpatialCircle_eq_cases hindex ha har huv


-- @@ L265-265 verbatim
end EmbeddedShrink

-- @@ L266-266 verbatim
end StandardMorseEventAt


-- @@ L268-268 verbatim
/-! ## Embedded charts on the assumption-free production route -/


-- @@ L270-270 verbatim
namespace FiniteIFTSurfaceCover.SharedCutoffMorseData


-- @@ L272-272 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [instι : Fintype ι]

-- @@ L273-273 verbatim
variable {B : FiniteIFTSurfaceCover C ι}


-- @@ L275-299 verbatim
/-- The constructive Morse coordinate in the shared-cutoff route has
injective differential on a positive shrink of its production ball. -/
theorem exists_localMorseParam_injective_radius
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    {χ : SmoothCutoff K U}
    (R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ R.criticalParameters) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ u : E₂, ‖u‖ < r →
        Injective (fderiv ℝ (R.localMorseNormalForm p hp).param u) := by
  let P := B.chart p.1
  let f := P.cutoffAffineHeight χ R.covector
  let M := R.localMorseNormalForm p hp
  have hsmooth : ContDiff ℝ ∞ f :=
    P.contDiff_cutoffAffineHeight χ R.covector
  have hf : ContDiffAt ℝ 2 (recenter f p.2) 0 :=
    contDiffAt_infty.mp (contDiff_recenter hsmooth p.2).contDiffAt 2
  have hcrit : fderiv ℝ (recenter f p.2) 0 = 0 :=
    fderiv_eq_zero_of_chartGradient_eq_zero
      (nondegenerateCriticalAt_recenter hsmooth
        (R.critical_nondegenerate p hp)).1
  simpa [M, f, P] using
    M.exists_fderiv_param_injective_radius hf hcrit
      (R.criticalModelShrink p hp).radius_pos


-- @@ L301-409 verbatim
/-- Every installed event of the assumption-free shared-cutoff construction
admits one smaller ball on which its actual ambient parameter is an immersed
embedding. -/
theorem nonempty_installedEventEmbeddedShrink
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    {χ : SmoothCutoff K U}
    (R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ R.criticalParameters) :
    Nonempty ((R.installedStandardMorseEvent p hp).EmbeddedShrink) := by
  let M := R.localMorseNormalForm p hp
  let Q := R.criticalModelShrink p hp
  let P := B.chart p.1
  obtain ⟨r₀, hr₀, hr₀Q, hMderiv⟩ :=
    R.exists_localMorseParam_injective_radius p hp
  have hJinj : Injective (fderiv ℝ M.param 0) := by
    apply hMderiv 0
    simpa using hr₀
  obtain ⟨r, hr, hrr₀, hMinj⟩ :=
    M.exists_param_injOn_ball_of_fderiv_injective hJinj hr₀
  refine ⟨{
    radius := r
    radius_pos := hr
    radius_le := ?_
    param_differentiableAt := ?_
    fderiv_param_injective := ?_
    param_injOn := ?_ }⟩
  · change r ≤ Q.radius
    exact hrr₀.trans hr₀Q
  · intro u hu
    have huQ : ‖u‖ < Q.radius := hu.trans_le (hrr₀.trans hr₀Q)
    have hMdiff : DifferentiableAt ℝ M.param u :=
      LocalMorseNormalForm.SimultaneousShrink.param_differentiableAt_of_contDiffOn_one
        M Q (by simpa [M, Q] using R.criticalModelShrink_contDiffOn p hp) u huQ
    have hshift : DifferentiableAt ℝ
        (fun z : E₂ => p.2 + M.param z) u :=
      differentiableAt_const (c := p.2).add hMdiff
    have hchart : DifferentiableAt ℝ
        (fun z : E₂ => P.param (p.2 + M.param z)) u :=
      (P.param_smooth.differentiable (by simp) _).comp u hshift
    change DifferentiableAt ℝ
      (fun z : E₂ => R.forward.diffeomorph
        (P.param (p.2 + M.param z))) u
    exact (R.forward.diffeomorph.contDiff.differentiable (by simp) _).comp u hchart
  · intro u hu
    have huQ : ‖u‖ < Q.radius := hu.trans_le (hrr₀.trans hr₀Q)
    have hur₀ : ‖u‖ < r₀ := hu.trans_le hrr₀
    let q : E₂ := p.2 + M.param u
    let J : E₂ →L[ℝ] E₂ := fderiv ℝ M.param u
    have hMdiff : DifferentiableAt ℝ M.param u :=
      LocalMorseNormalForm.SimultaneousShrink.param_differentiableAt_of_contDiffOn_one
        M Q (by simpa [M, Q] using R.criticalModelShrink_contDiffOn p hp) u huQ
    have hshift : HasFDerivAt (fun z : E₂ => p.2 + M.param z) J u := by
      simpa [J] using hMdiff.hasFDerivAt.const_add p.2
    have hqdom : q ∈ P.domain :=
      LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
        (M := M) Q u huQ
    have hP : Injective (fderiv ℝ P.param q) :=
      P.fderiv_param_injective ((B.domain_open p.1).mem_nhds hqdom)
    have hchart : HasFDerivAt (fun z : E₂ => P.param (p.2 + M.param z))
        ((fderiv ℝ P.param q).comp J) u :=
      (P.param_smooth.differentiable (by simp) q).hasFDerivAt.comp u hshift
    have hout : HasFDerivAt
        (fun z : E₂ => R.forward.diffeomorph
          (P.param (p.2 + M.param z)))
        ((fderiv ℝ R.forward.diffeomorph (P.param q)).comp
          ((fderiv ℝ P.param q).comp J)) u := by
      exact (R.forward.diffeomorph.contDiff.differentiable (by simp)
        (P.param q)).hasFDerivAt.comp u hchart
    change Injective (fderiv ℝ
      (fun z : E₂ => R.forward.diffeomorph
        (P.param (p.2 + M.param z))) u)
    rw [hout.fderiv]
    have hforward : Injective
        (fderiv ℝ R.forward.diffeomorph (P.param q)) := by
      rw [← R.amplitude_diffeomorph_symm]
      exact R.amplitude.fderiv_equiv_symm_injective (P.param q)
    exact hforward.comp (hP.comp (hMderiv u hur₀))
  · intro u hu v hv huv
    apply hMinj hu hv
    have huQ : ‖u‖ < Q.radius := by
      have hur : ‖u‖ < r := by
        simpa [Metric.mem_ball, dist_zero_right] using hu
      exact hur.trans_le (hrr₀.trans hr₀Q)
    have hvQ : ‖v‖ < Q.radius := by
      have hvr : ‖v‖ < r := by
        simpa [Metric.mem_ball, dist_zero_right] using hv
      exact hvr.trans_le (hrr₀.trans hr₀Q)
    have huDom : p.2 + M.param u ∈ P.domain :=
      LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
        (M := M) Q u huQ
    have hvDom : p.2 + M.param v ∈ P.domain :=
      LocalMorseNormalForm.SimultaneousShrink.ift_param_mem_domain
        (M := M) Q v hvQ
    change R.criticalAmbientParam p hp u =
      R.criticalAmbientParam p hp v at huv
    have hparam : P.param (p.2 + M.param u) =
        P.param (p.2 + M.param v) := by
      have h := congrArg R.forward.diffeomorph.symm huv
      change R.forward.diffeomorph.symm
          (R.forward.diffeomorph (P.param (p.2 + M.param u))) =
        R.forward.diffeomorph.symm
          (R.forward.diffeomorph (P.param (p.2 + M.param v))) at h
      rw [R.forward.diffeomorph.symm_apply_apply,
        R.forward.diffeomorph.symm_apply_apply] at h
      exact h
    have hshift : p.2 + M.param u = p.2 + M.param v :=
      P.param_injOn_domain huDom hvDom hparam
    exact add_left_cancel hshift


-- @@ L411-419 verbatim
/-- A fixed embedded shrink for an installed shared-cutoff event. -/
def installedEventEmbeddedShrink
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    {χ : SmoothCutoff K U}
    (R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ R.criticalParameters) :
    (R.installedStandardMorseEvent p hp).EmbeddedShrink :=
  (R.nonempty_installedEventEmbeddedShrink p hp).some


-- @@ L421-421 verbatim
namespace CriticalValueShiftData


-- @@ L423-481 verbatim
/-- Concrete immersed-embedding shrink for the actual value-separated
production event.  The radius is the minimum of the installed chart shrink
and the protected-core transport shrink. -/
def productionEventEmbeddedShrink
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    {χ : SmoothCutoff K U}
    {R : @FiniteIFTSurfaceCover.SharedCutoffMorseData
      n C ι instι B K U χ}
    (S : @CriticalValueShiftData n C ι instι B K U χ R)
    (e : @GlobalCriticalEvent n C ι instι B K U χ R) :
    (S.productionEvent e).EmbeddedShrink := by
  let p := (R.criticalEventOwner e).1
  let hp : p ∈ R.criticalParameters := R.criticalEventOwner_mem e
  let T : (S.ownerModel e).EmbeddedShrink := by
    change (R.installedStandardMorseEvent p hp).EmbeddedShrink
    exact R.installedEventEmbeddedShrink p hp
  let r := min T.radius (S.eventTransportShrink e).radius
  refine {
    radius := r
    radius_pos := lt_min T.radius_pos (S.eventTransportShrink e).radius_pos
    radius_le := min_le_right _ _
    param_differentiableAt := ?_
    fderiv_param_injective := ?_
    param_injOn := ?_ }
  · intro u hu
    have huT : ‖u‖ < T.radius := hu.trans_le (min_le_left _ _)
    have hbase := T.param_differentiableAt u huT
    change DifferentiableAt ℝ (S.transportedParam e) u
    exact (S.forward.diffeomorph.contDiff.differentiable (by simp) _).comp u hbase
  · intro u hu
    have huT : ‖u‖ < T.radius := hu.trans_le (min_le_left _ _)
    have hbase := T.fderiv_param_injective u huT
    have hdiff := T.param_differentiableAt u huT
    have hcomp : HasFDerivAt (S.transportedParam e)
        ((fderiv ℝ S.forward.diffeomorph ((S.ownerModel e).param u)).comp
          (fderiv ℝ (S.ownerModel e).param u)) u := by
      exact (S.forward.diffeomorph.contDiff.differentiable (by simp)
        ((S.ownerModel e).param u)).hasFDerivAt.comp u hdiff.hasFDerivAt
    change Injective (fderiv ℝ (S.transportedParam e) u)
    rw [hcomp.fderiv]
    have hforward : Injective
        (fderiv ℝ S.forward.diffeomorph ((S.ownerModel e).param u)) := by
      rw [← S.amplitude_diffeomorph_symm]
      exact S.amplitude.fderiv_equiv_symm_injective
        ((S.ownerModel e).param u)
    exact hforward.comp hbase
  · intro u hu v hv huv
    apply T.param_injOn
    · exact Metric.ball_subset_ball (min_le_left _ _) hu
    · exact Metric.ball_subset_ball (min_le_left _ _) hv
    · change S.transportedParam e u = S.transportedParam e v at huv
      have h := congrArg S.forward.diffeomorph.symm huv
      change S.forward.diffeomorph.symm
          (S.forward.diffeomorph ((S.ownerModel e).param u)) =
        S.forward.diffeomorph.symm
          (S.forward.diffeomorph ((S.ownerModel e).param v)) at h
      rw [S.forward.diffeomorph.symm_apply_apply,
        S.forward.diffeomorph.symm_apply_apply] at h
      exact h


-- @@ L483-483 verbatim
end CriticalValueShiftData

-- @@ L484-484 verbatim
end FiniteIFTSurfaceCover.SharedCutoffMorseData


-- @@ L486-486 verbatim
end Submission
