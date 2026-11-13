import Submission.ProductionMorseSaddleAutomaticOrientedAdapter
import Submission.LocalIFTSurfaceChart


-- @@ L4-36 verbatim
/-!
# Existence of the endpoint-local fiber cover and flow compatibility

The short-flow adapter reduced the production saddle topology to one residual
chart contract: `ChronologicalSaddleEndpointLocalFiberCover`, an ambient
implicit-function cover of the zero fiber centered at each of the four marked
critical ends at the *fixed* chronological boundary radius.  This file
discharges that contract unconditionally.

The argument is the genuine inverse-function theorem at a noncentral chart
point.  At a marked end `M.param u₀` the complemented-kernel IFT package of
`LocalIFTSurfaceChart` recovers every nearby fiber point `x` as
`rawParam (ψ (x - M.param u₀))`, where `ψ` is a fixed ambient continuous
linear coordinate.  The composite `u ↦ ψ (M.param u - M.param u₀)` is `C¹`
near `u₀` (production full-radius `C¹` control, exposed here), and its
differential is injective, hence bijective in dimension two: its image of a
small parameter ball is a neighborhood of `0`.  Any fiber point close to the
end therefore has its `ψ`-coordinate hit by some parameter `u` of small norm,
and applying `rawParam` to both sides recovers `M.param u = v` exactly.

Consequences packaged at the end:

* `chronologicalSaddleEndpointLocalFiberCover` — the canonical unconditional
  endpoint-local fiber cover;
* `chronologicalSaddleShortMateArcFlowData_auto` — all eight short-scale
  endpoint captures with no chart hypothesis;
* `chronologicalSaddleChosenMateArcFlowCompatibility_of_smallness` — the
  fixed-window `ChronologicalSaddleChosenMateArcFlowCompatibility`, with the
  four scalar smallness inequalities as the single residual hypothesis;
* `chronologicalSaddleTopologyDichotomy_of_pairing_and_arcRecovery` — the
  production saddle topology dichotomy from only the punctured critical arc
  pairing and the regular-orbit arc recovery.
-/


-- @@ L38-38 verbatim
set_option autoImplicit false

-- @@ L39-39 verbatim
set_option maxHeartbeats 2400000


-- @@ L41-41 verbatim
noncomputable section


-- @@ L43-43 verbatim
open Set Function Metric Filter

-- @@ L44-44 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L46-46 verbatim
namespace Submission


-- @@ L48-48 verbatim
variable {n : ℕ}


-- @@ L50-50 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L51-51 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L52-52 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L54-54 verbatim
/-! ## The kernel projection of the complemented IFT package -/


-- @@ L56-56 verbatim
namespace LocalIFTSurfaceChart


-- @@ L58-65 verbatim
/-- The right coordinate of the complemented-kernel implicit-function package
restricts to the identity on the kernel itself. -/
theorem implicitData_rightDeriv_ker (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v))
    (x : (fderiv ℝ C.G v).ker) :
    (implicitData C hreg).rightDeriv (x : E') = x :=
  Classical.choose_spec
    ((fderiv ℝ C.G v).ker_closedComplemented_of_finiteDimensional_range) x


-- @@ L67-86 verbatim
/-- The ambient kernel coordinates are injective on the kernel of the
regular differential. -/
theorem eq_zero_of_ambientCoordinates_eq_zero
    (C : FramedLevelCobordism n) {v : E'}
    (hreg : Surjective (fderiv ℝ C.G v)) {x : E'}
    (hx : x ∈ (fderiv ℝ C.G v).ker)
    (h : ambientCoordinates C hreg x = 0) : x = 0 := by
  have h' : (kernelEquiv C hreg).symm ((implicitData C hreg).rightDeriv x) = 0 := by
    simpa [ambientCoordinates] using h
  have hrd : (implicitData C hreg).rightDeriv x = 0 := by
    have h0 : (kernelEquiv C hreg).symm ((implicitData C hreg).rightDeriv x) =
        (kernelEquiv C hreg).symm 0 := by
      rw [h']
      simp
    exact (kernelEquiv C hreg).symm.injective h0
  have hcoe := implicitData_rightDeriv_ker C hreg ⟨x, hx⟩
  have hzero : (⟨x, hx⟩ : (fderiv ℝ C.G v).ker) = 0 := by
    rw [← hcoe]
    exact hrd
  simpa using congrArg Subtype.val hzero


-- @@ L88-88 verbatim
end LocalIFTSurfaceChart


-- @@ L90-90 verbatim
/-! ## Full-radius `C¹` control of the actual production parameter -/


-- @@ L92-92 verbatim
namespace FiniteIFTSurfaceCover.SharedCutoffMorseData


-- @@ L94-94 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]

-- @@ L95-95 verbatim
variable {B : FiniteIFTSurfaceCover C ι}


-- @@ L97-119 verbatim
/-- The shared-cutoff ambient parameter is `C¹` at every point of the
complete normal-form radius, not merely differentiable there. -/
theorem criticalAmbientParam_contDiffAt_one
    {K U : Set E'} {χ : SmoothCutoff K U}
    (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ R.criticalParameters)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    ContDiffAt ℝ 1 (R.criticalAmbientParam p hp) u := by
  let M := R.localMorseNormalForm p hp
  let P := B.chart p.1
  have huball : u ∈ ball (0 : E₂) (R.criticalModelShrink p hp).radius := by
    simpa [mem_ball, dist_zero_right] using hu
  have hM : ContDiffAt ℝ 1 M.param u :=
    (R.criticalModelShrink_contDiffOn p hp).contDiffAt
      (isOpen_ball.mem_nhds huball)
  have hshift : ContDiffAt ℝ 1 (fun z : E₂ => p.2 + M.param z) u :=
    (contDiffAt_const (c := p.2)).add hM
  have hchart : ContDiffAt ℝ 1 (fun z : E₂ => P.param (p.2 + M.param z)) u :=
    ContDiffAt.comp u (P.param_smooth.contDiffAt.of_le (by simp)) hshift
  change ContDiffAt ℝ 1
    (fun z : E₂ => R.forward.diffeomorph (P.param (p.2 + M.param z))) u
  exact ContDiffAt.comp u
    (R.forward.diffeomorph.contDiff.contDiffAt.of_le (by simp)) hchart


-- @@ L121-121 verbatim
namespace CriticalValueShiftData


-- @@ L123-143 verbatim
/-- After value separation, the transported production parameter is still
`C¹` at every point of its complete-cover radius. -/
theorem transportedParam_contDiffAt_one
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : B.SharedCutoffMorseData χ}
    (S : CriticalValueShiftData R) (e : GlobalCriticalEvent R)
    (u : E₂) (hu : ‖u‖ < (S.productionEvent e).radius) :
    ContDiffAt ℝ 1 (S.productionEvent e).param u := by
  let p := (R.criticalEventOwner e).1
  let hp : p ∈ R.criticalParameters := R.criticalEventOwner_mem e
  have huOwner : ‖u‖ < (R.criticalModelShrink p hp).radius := by
    have hle := (S.eventTransportShrink e).radius_le
    change ‖u‖ < (S.eventTransportShrink e).radius at hu
    change (S.eventTransportShrink e).radius ≤
      (R.criticalModelShrink p hp).radius at hle
    exact hu.trans_le hle
  have hbase := R.criticalAmbientParam_contDiffAt_one p hp u huOwner
  change ContDiffAt ℝ 1
    (fun z : E₂ => S.forward.diffeomorph (R.criticalAmbientParam p hp z)) u
  exact ContDiffAt.comp u
    (S.forward.diffeomorph.contDiff.contDiffAt.of_le (by simp)) hbase


-- @@ L145-145 verbatim
end CriticalValueShiftData


-- @@ L147-147 verbatim
end FiniteIFTSurfaceCover.SharedCutoffMorseData


-- @@ L149-149 verbatim
namespace StandardMorseEventAt


-- @@ L151-158 verbatim
/-- Transporting the center index of a standard event does not change its
chart radius. -/
theorem castCenter_radius {C : FramedLevelCobordism n}
    {center center' : E'}
    (h : center = center') (M : StandardMorseEventAt C center) :
    (h ▸ M).radius = M.radius := by
  subst center'
  rfl


-- @@ L160-160 verbatim
end StandardMorseEventAt


-- @@ L162-162 verbatim
/-! ## The endpoint-local inverse function theorem -/


-- @@ L164-164 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L166-309 verbatim
/-- **Endpoint-local fiber cover.**  At any chart parameter `u₀` inside the
embedded injectivity radius, every zero-fiber point sufficiently close to
`M.param u₀` is realized by a chart parameter of norm smaller than any
prescribed radius `r` exceeding `‖u₀‖`.  This is the inverse-function theorem
for the composite of the event parameter with the ambient IFT kernel
coordinates at the noncentral point. -/
theorem exists_endpointLocalFiberCover
    {C : FramedLevelCobordism n} {center : E'}
    {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink)
    (hCD : ∀ u : E₂, ‖u‖ < M.radius → ContDiffAt ℝ 1 M.param u)
    (u₀ : E₂) (hu₀T : ‖u₀‖ < T.radius)
    {r : ℝ} (hu₀r : ‖u₀‖ < r) (hrM : r ≤ M.radius) :
    ∃ δ > 0, ∀ v : E', dist v (M.param u₀) < δ → C.G v = 0 →
      ∃ u : E₂, ‖u‖ < r ∧ M.param u = v := by
  classical
  have hu₀M : ‖u₀‖ < M.radius := hu₀r.trans_le hrM
  have hfib : C.G (M.param u₀) = 0 := M.param_fiber u₀ hu₀M
  -- `C¹` control and strict differentiability at the marked end
  have hpc : ContDiffAt ℝ 1 M.param u₀ := hCD u₀ hu₀M
  have hPdiff : DifferentiableAt ℝ M.param u₀ := hpc.differentiableAt (by simp)
  have hstrict : HasStrictFDerivAt M.param (fderiv ℝ M.param u₀) u₀ :=
    hpc.hasStrictFDerivAt (by simp)
  have hgstrict : HasStrictFDerivAt
      (fun u : E₂ => LocalIFTSurfaceChart.ambientCoordinates C
        (C.regular (M.param u₀) hfib) (M.param u - M.param u₀))
      ((LocalIFTSurfaceChart.ambientCoordinates C
        (C.regular (M.param u₀) hfib)).comp (fderiv ℝ M.param u₀)) u₀ :=
    (LocalIFTSurfaceChart.ambientCoordinates C
      (C.regular (M.param u₀) hfib)).hasStrictFDerivAt.comp u₀
      (hstrict.sub_const (M.param u₀))
  -- the differential of the parameter lands in the kernel of `fderiv G`
  have hball₀ : ball (0 : E₂) M.radius ∈ 𝓝 u₀ := by
    apply isOpen_ball.mem_nhds
    simpa [mem_ball, dist_zero_right] using hu₀M
  have hev : (C.G ∘ M.param) =ᶠ[𝓝 u₀]
      (fun _ : E₂ => (0 : EuclideanSpace ℝ (Fin n))) := by
    filter_upwards [hball₀] with u hu
    exact M.param_fiber u (by simpa [mem_ball, dist_zero_right] using hu)
  have hGdiff : DifferentiableAt ℝ C.G (M.param u₀) :=
    (C.smooth.differentiable (by simp)).differentiableAt
  have hcompzero : (fderiv ℝ C.G (M.param u₀)).comp (fderiv ℝ M.param u₀) = 0 := by
    have hcomp := fderiv_comp u₀ hGdiff hPdiff
    have hzero : fderiv ℝ (C.G ∘ M.param) u₀ = 0 :=
      (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev).trans (by simp)
    rw [← hcomp]
    exact hzero
  have hkermem : ∀ w : E₂,
      (fderiv ℝ M.param u₀) w ∈ (fderiv ℝ C.G (M.param u₀)).ker := by
    intro w
    rw [LinearMap.mem_ker]
    have happ : ((fderiv ℝ C.G (M.param u₀)).comp (fderiv ℝ M.param u₀)) w =
        (0 : E₂ →L[ℝ] EuclideanSpace ℝ (Fin n)) w := by
      rw [hcompzero]
    simpa using happ
  -- the composed differential is injective, hence surjective in dimension two
  have hdginj : Function.Injective
      ((LocalIFTSurfaceChart.ambientCoordinates C
        (C.regular (M.param u₀) hfib)).comp (fderiv ℝ M.param u₀)) := by
    intro w w' hww'
    have hz : ((LocalIFTSurfaceChart.ambientCoordinates C
        (C.regular (M.param u₀) hfib)).comp (fderiv ℝ M.param u₀)) (w - w') = 0 := by
      rw [map_sub, hww', sub_self]
    have hx0 : (fderiv ℝ M.param u₀) (w - w') = 0 := by
      apply LocalIFTSurfaceChart.eq_zero_of_ambientCoordinates_eq_zero C
        (C.regular (M.param u₀) hfib) (hkermem (w - w'))
      simpa using hz
    have hinj0 : (fderiv ℝ M.param u₀) (w - w') = (fderiv ℝ M.param u₀) 0 := by
      rw [hx0, map_zero]
    have hww0 : w - w' = 0 := T.fderiv_param_injective u₀ hu₀T hinj0
    exact sub_eq_zero.mp hww0
  have hrange : ((LocalIFTSurfaceChart.ambientCoordinates C
      (C.regular (M.param u₀) hfib)).comp (fderiv ℝ M.param u₀)).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    have hinjL : Function.Injective
        ((LocalIFTSurfaceChart.ambientCoordinates C
          (C.regular (M.param u₀) hfib)).comp
            (fderiv ℝ M.param u₀)).toLinearMap := hdginj
    exact LinearMap.injective_iff_surjective.mp hinjL
  -- inverse function theorem: the composite is open at `u₀`
  have hmap : Filter.map
      (fun u : E₂ => LocalIFTSurfaceChart.ambientCoordinates C
        (C.regular (M.param u₀) hfib) (M.param u - M.param u₀)) (𝓝 u₀) =
      𝓝 ((fun u : E₂ => LocalIFTSurfaceChart.ambientCoordinates C
        (C.regular (M.param u₀) hfib) (M.param u - M.param u₀)) u₀) :=
    hgstrict.map_nhds_eq_of_surj hrange
  -- a parameter ball small enough for the norm bound and the ambient chart
  have hcontP : ContinuousAt M.param u₀ := hPdiff.continuousAt
  have hopenA := LocalIFTSurfaceChart.isOpen_localAmbient C hfib
  have hmemA := LocalIFTSurfaceChart.center_mem_localAmbient C hfib
  have hpre : M.param ⁻¹' LocalIFTSurfaceChart.localAmbient C hfib ∈ 𝓝 u₀ :=
    hcontP.preimage_mem_nhds (hopenA.mem_nhds hmemA)
  obtain ⟨s₁, hs₁pos, hs₁sub⟩ := Metric.mem_nhds_iff.mp hpre
  have hspos : 0 < min s₁ (r - ‖u₀‖) := lt_min hs₁pos (by linarith)
  have hVnhds : ball u₀ (min s₁ (r - ‖u₀‖)) ∈ 𝓝 u₀ :=
    Metric.ball_mem_nhds _ hspos
  have himg : (fun u : E₂ => LocalIFTSurfaceChart.ambientCoordinates C
      (C.regular (M.param u₀) hfib) (M.param u - M.param u₀)) ''
        ball u₀ (min s₁ (r - ‖u₀‖)) ∈ 𝓝 (0 : E₂) := by
    have h0 : (fun u : E₂ => LocalIFTSurfaceChart.ambientCoordinates C
        (C.regular (M.param u₀) hfib) (M.param u - M.param u₀)) u₀ = 0 := by
      simp
    rw [← h0, ← hmap]
    exact Filter.image_mem_map hVnhds
  -- transfer the parameter neighborhood to an ambient radius at the end
  have hpre2 : (fun x : E' => LocalIFTSurfaceChart.ambientCoordinates C
      (C.regular (M.param u₀) hfib) (x - M.param u₀)) ⁻¹'
        ((fun u : E₂ => LocalIFTSurfaceChart.ambientCoordinates C
          (C.regular (M.param u₀) hfib) (M.param u - M.param u₀)) ''
            ball u₀ (min s₁ (r - ‖u₀‖))) ∈ 𝓝 (M.param u₀) := by
    apply ContinuousAt.preimage_mem_nhds
    · exact ((LocalIFTSurfaceChart.ambientCoordinates C
        (C.regular (M.param u₀) hfib)).continuous.comp
          (continuous_id.sub continuous_const)).continuousAt
    · simpa using himg
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hpre2
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ :=
    Metric.mem_nhds_iff.mp (hopenA.mem_nhds hmemA)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro v hv hGv
  have hvA : v ∈ LocalIFTSurfaceChart.localAmbient C hfib :=
    hδ₂sub (Metric.mem_ball.mpr (hv.trans_le (min_le_right _ _)))
  have hvw := hδ₁sub (Metric.mem_ball.mpr (hv.trans_le (min_le_left _ _)))
  obtain ⟨u, huV, hgu⟩ := hvw
  have hd : dist u u₀ < min s₁ (r - ‖u₀‖) := Metric.mem_ball.mp huV
  have hur : ‖u‖ < r := by
    have hnn := norm_sub_norm_le u u₀
    rw [dist_eq_norm] at hd
    have hd' : ‖u - u₀‖ < r - ‖u₀‖ := hd.trans_le (min_le_right _ _)
    linarith
  have huM : ‖u‖ < M.radius := hur.trans_le hrM
  have huA : M.param u ∈ LocalIFTSurfaceChart.localAmbient C hfib :=
    hs₁sub (Metric.mem_ball.mpr (hd.trans_le (min_le_left _ _)))
  refine ⟨u, hur, ?_⟩
  have h1 := LocalIFTSurfaceChart.rawParam_ambientCoordinates_eq C hfib
    (M.param_fiber u huM) huA
  have h2 := LocalIFTSurfaceChart.rawParam_ambientCoordinates_eq C hfib hGv hvA
  have hgu' : LocalIFTSurfaceChart.ambientCoordinates C
      (C.regular (M.param u₀) hfib) (M.param u - M.param u₀) =
        LocalIFTSurfaceChart.ambientCoordinates C
          (C.regular (M.param u₀) hfib) (v - M.param u₀) := hgu
  exact h1.symm.trans
    ((congrArg (LocalIFTSurfaceChart.rawParam C
      (C.regular (M.param u₀) hfib)) hgu').trans h2)


-- @@ L311-311 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L313-313 verbatim
/-! ## The canonical chronological endpoint-local fiber cover -/


-- @@ L315-315 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L316-316 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L317-317 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L319-319 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L321-321 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L322-322 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}


-- @@ L324-354 verbatim
/-- The chronological production event parameter is `C¹` on its whole chart
radius. -/
theorem eventModel_param_contDiffAt_one
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    ∀ u : E₂, ‖u‖ < (D.position.eventModel t ht).radius →
      ContDiffAt ℝ 1 (D.position.eventModel t ht).param u := by
  intro u hu
  let S := D.second.toCriticalValueShiftData
  let e := D.chronologicalGlobalEvent t ht
  have hparam : (D.position.eventModel t ht).param = S.transportedParam e := by
    rw [D.eventModel_eq_transportedStandardMorseEvent t ht]
    simpa [S, e,
      FiniteIFTSurfaceCover.SharedCutoffMorseData.CriticalValueShiftData.transportedStandardMorseEvent] using
      StandardMorseEventAt.castCenter_param
      (D.second.shiftedCenter_chronologicalGlobalEvent t ht)
      (D.second.toCriticalValueShiftData.transportedStandardMorseEvent
        (D.chronologicalGlobalEvent t ht))
  have hradius : (D.position.eventModel t ht).radius =
      (S.productionEvent e).radius := by
    rw [D.eventModel_eq_transportedStandardMorseEvent t ht]
    simpa [S, e,
      FiniteIFTSurfaceCover.SharedCutoffMorseData.CriticalValueShiftData.transportedStandardMorseEvent] using
      StandardMorseEventAt.castCenter_radius
      (D.second.shiftedCenter_chronologicalGlobalEvent t ht)
      (D.second.toCriticalValueShiftData.transportedStandardMorseEvent
        (D.chronologicalGlobalEvent t ht))
  have hu' : ‖u‖ < (S.productionEvent e).radius := hradius ▸ hu
  have h := S.transportedParam_contDiffAt_one e u hu'
  rw [hparam]
  exact h


-- @@ L356-390 verbatim
/-- **The endpoint-local fiber cover exists unconditionally.**  Every marked
critical end at the fixed chronological boundary radius has an ambient radius
within which all zero-fiber points are chart images at the endpoint parameter
radius. -/
theorem exists_chronologicalSaddleEndpointLocalCover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    ∃ δ > 0, ∀ v : E',
      dist v ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht)) < δ →
      D.signedOutput.cobordism.G v = 0 →
      ∃ u : E₂,
        ‖u‖ < D.chronologicalSaddleEndpointParamRadius t ht ∧
        (D.position.eventModel t ht).param u = v := by
  have h := StandardMorseEventAt.EmbeddedShrink.exists_endpointLocalFiberCover
    (T := D.chronologicalEventEmbeddedShrink t ht)
    (D.eventModel_param_contDiffAt_one t ht)
    (saddleCriticalBoundaryEndParam p (D.chronologicalSaddleBoundaryRadius t ht))
    (by
      rw [D.norm_chronologicalSaddleCriticalBoundaryEndParam t ht p]
      exact D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
    (r := D.chronologicalSaddleEndpointParamRadius t ht)
    (by
      rw [D.norm_chronologicalSaddleCriticalBoundaryEndParam t ht p]
      exact D.chronologicalSaddleBoundaryRadius_lt_endpointParamRadius t ht)
    (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
  obtain ⟨δ, hδ, hcov⟩ := h
  refine ⟨δ, hδ, ?_⟩
  intro v hv hGv
  apply hcov v ?_ hGv
  simpa [saddleCriticalBoundaryEndParam,
    StandardMorseEventAt.saddleCriticalBoundaryEnd,
    StandardMorseEventAt.saddlePositiveBoundaryEnd,
    StandardMorseEventAt.localPoint] using hv


-- @@ L392-404 verbatim
/-- The canonical unconditional endpoint-local fiber cover at the fixed
chronological boundary radius. -/
noncomputable def chronologicalSaddleEndpointLocalFiberCover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht) where
  radius p := (D.exists_chronologicalSaddleEndpointLocalCover t ht p).choose
  radius_pos p :=
    (D.exists_chronologicalSaddleEndpointLocalCover t ht p).choose_spec.1
  cover p v hv hGv :=
    (D.exists_chronologicalSaddleEndpointLocalCover t ht p).choose_spec.2
      v hv hGv


-- @@ L406-406 verbatim
/-! ## Unconditional consequences -/


-- @@ L408-419 verbatim
/-- All eight short-scale endpoint captures, with no residual chart
hypothesis. -/
noncomputable def chronologicalSaddleShortMateArcFlowData_auto
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    ChronologicalSaddleShortMateArcFlowData
      (D := D) (t := t) (ht := ht) A
      (D.chronologicalSaddleEndpointLocalFiberCover t ht) :=
  chronologicalSaddleShortMateArcFlowData_of_endpointLocalCover
    (D := D) (t := t) (ht := ht) hindex A
    (D.chronologicalSaddleEndpointLocalFiberCover t ht)


-- @@ L421-436 verbatim
/-- The fixed-window flow-compatibility package.  With the endpoint-local
fiber cover now canonical, the only residual hypothesis is the quadruple of
scalar smallness inequalities of the already fixed chronological
displacement against the arc-dependent compact time field. -/
noncomputable def chronologicalSaddleChosenMateArcFlowCompatibility_of_smallness
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (Q : ChronologicalSaddleFixedWindowShortFlowSmallness
      (D := D) (t := t) (ht := ht) A
      (D.chronologicalSaddleEndpointLocalFiberCover t ht)) :
    ChronologicalSaddleChosenMateArcFlowCompatibility
      (D := D) (t := t) (ht := ht) A :=
  chronologicalSaddleChosenMateArcFlowCompatibility_of_endpointLocalCover
    (D := D) (t := t) (ht := ht) hindex A
    (D.chronologicalSaddleEndpointLocalFiberCover t ht) Q


-- @@ L438-452 verbatim
/-- **Production saddle topology from the pairing alone.**  The
merge-or-split dichotomy now follows from the punctured critical arc pairing
and regular-orbit arc recovery; every chart, cover, scale, and endpoint
capture is chosen automatically. -/
theorem chronologicalSaddleTopologyDichotomy_of_pairing_and_arcRecovery
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (H : ChronologicalSaddleRegularOrbitArcRecovery
      (D := D) (t := t) (ht := ht) (hindex := hindex)) :
    D.ChronologicalSaddleMergeTopology t ht hindex ∨
      D.ChronologicalSaddleSplitTopology t ht hindex :=
  chronologicalSaddleTopologyDichotomy_of_endpointLocalFiberCover
    (D := D) (t := t) (ht := ht) hindex A
    (D.chronologicalSaddleEndpointLocalFiberCover t ht) H


-- @@ L454-454 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L456-456 verbatim
end Submission
