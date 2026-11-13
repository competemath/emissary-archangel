import Submission.ProductionMorseSaddleOrientedExteriorPairing
import Submission.ProductionMorseSaddleExteriorTransport
import Submission.ProductionMorseSaddleLocalExcision
import Submission.MorseEventSchedule
import Submission.ProductionMorseDefiniteCanonicalPairing


-- @@ L7-21 verbatim
/-!
# Regularity of the punctured production saddle slice

The critical time slice of a saddle is singular only at the saddle center.
This file proves that statement globally for an event selected from a
`MorsePosition`, using the already established injectivity of the critical
values.  It then upgrades every ordinary path in the punctured critical slice
to a `SpatiallyRegularZeroPath`.

Thus no additional analytic or ODE hypothesis is needed for the exterior
arcs in `SaddlePuncturedCriticalArcPairingData`: the residual input is purely
the one-dimensional topology saying that the compact critical slice, cut at
the four chart ends, is a union of intervals, together with its oriented
endpoint theorem.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false

-- @@ L24-24 verbatim
set_option maxHeartbeats 2400000

-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Set Function

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace unitInterval


-- @@ L30-30 verbatim
namespace Submission


-- @@ L32-32 verbatim
variable {n : ℕ}


-- @@ L34-34 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L35-35 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L36-36 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L38-38 verbatim
/-! ## Arbitrarily small production fiber covers -/


-- @@ L40-40 verbatim
namespace FiniteIFTSurfaceCover.SharedCutoffMorseData.CriticalValueShiftData


-- @@ L42-42 verbatim
variable {C₀ : FramedLevelCobordism n} {I₀ : Type*} [Fintype I₀]

-- @@ L43-43 verbatim
variable {B₀ : FiniteIFTSurfaceCover C₀ I₀}

-- @@ L44-44 verbatim
variable {K₀ U₀ : Set (EuclideanSpace ℝ (Fin (n + 2)))}

-- @@ L45-45 verbatim
variable {χ₀ : SmoothCutoff K₀ U₀}

-- @@ L46-46 verbatim
variable {R₀ : B₀.SharedCutoffMorseData χ₀}


-- @@ L48-93 verbatim
/-- The production transported event retains the stronger IFT cover with an
arbitrarily prescribed Morse-coordinate radius.  The public
`StandardMorseEventAt.covers_fiber` stores only one radius; this production
lemma exposes the smaller-radius form needed to isolate exterior cuts from a
ball around the saddle center. -/
theorem transportedParam_covers_fiber_within_morseRadius
    {R₀ : B₀.SharedCutoffMorseData χ₀}
    (S : CriticalValueShiftData R₀) (e : GlobalCriticalEvent R₀)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, ∀ v : EuclideanSpace ℝ (Fin (n + 2)),
      dist v (S.shiftedCenter e) < ε →
      S.output.G v = 0 →
      ∃ u : E₂, ‖u‖ < r ∧ S.transportedParam e u = v := by
  let p := (R₀.criticalEventOwner e).1
  let hp : p ∈ R₀.criticalParameters := R₀.criticalEventOwner_mem e
  obtain ⟨ε₀, hε₀, hcover⟩ :=
    R₀.covers_fiber_within_morseRadius p hp hr
  have hac : S.amplitude.diffeomorph (S.shiftedCenter e) = R₀.center p := by
    rw [S.amplitude_diffeomorph, shiftedCenter,
      ← R₀.criticalEventOwner_center e]
    exact S.forward.diffeomorph.symm_apply_apply _
  have htend : Filter.Tendsto (fun v => S.amplitude.diffeomorph v)
      (nhds (S.shiftedCenter e)) (nhds (R₀.center p)) := by
    rw [← hac]
    exact S.amplitude.diffeomorph.continuous.continuousAt
  have hnear : (fun v => S.amplitude.diffeomorph v) ⁻¹'
      Metric.ball (R₀.center p) ε₀ ∈ nhds (S.shiftedCenter e) :=
    htend (Metric.ball_mem_nhds _ hε₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_⟩
  intro v hv hzero
  have hvball : v ∈ Metric.ball (S.shiftedCenter e) ε := by
    simpa [Metric.mem_ball] using hv
  have haBall : S.amplitude.diffeomorph v ∈
      Metric.ball (R₀.center p) ε₀ := hball hvball
  have haDist : dist (S.amplitude.diffeomorph v) (R₀.center p) < ε₀ := by
    simpa [Metric.mem_ball] using haBall
  have haZero : R₀.output.G (S.amplitude.diffeomorph v) = 0 := by
    simpa [output, VerticalAmplitude.pullback_G,
      SmallVerticalAmplitude.diffeomorph_apply] using hzero
  obtain ⟨u, hu, hparam⟩ :=
    hcover (S.amplitude.diffeomorph v) haDist haZero
  refine ⟨u, hu, ?_⟩
  change S.forward.diffeomorph (R₀.criticalAmbientParam p hp u) = v
  rw [hparam, ← S.amplitude_diffeomorph_symm]
  exact S.amplitude.diffeomorph.symm_apply_apply v


-- @@ L95-95 verbatim
end FiniteIFTSurfaceCover.SharedCutoffMorseData.CriticalValueShiftData


-- @@ L97-97 verbatim
namespace StandardMorseEventAt


-- @@ L99-108 verbatim
/-- Transporting the center index of a standard event does not change its
ambient parametrization.  Keeping this elementary dependent-cast fact named
lets chronological production lemmas expose fields of the transported event
without unfolding the entire event package. -/
theorem castCenter_param {C : FramedLevelCobordism n}
    {center center' : EuclideanSpace ℝ (Fin (n + 2))}
    (h : center = center') (M : StandardMorseEventAt C center) :
    (h ▸ M).param = M.param := by
  subst center'
  rfl


-- @@ L110-110 verbatim
end StandardMorseEventAt


-- @@ L112-112 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L113-113 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L114-114 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L116-116 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L118-156 verbatim
/-- Chronological specialization of the arbitrarily small production fiber
cover.  This is stronger than the single `fiberCoverRadius` stored by the
event model and is available for every positive target parameter radius. -/
theorem eventModel_covers_fiber_within_morseRadius
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0,
      ∀ v : EuclideanSpace ℝ (Fin (n + 2)),
        dist v (D.position.eventCenter t ht) < ε →
        D.signedOutput.cobordism.G v = 0 →
        ∃ u : E₂, ‖u‖ < r ∧
          (D.position.eventModel t ht).param u = v := by
  let S := D.second.toCriticalValueShiftData
  let e := D.chronologicalGlobalEvent t ht
  have H := S.transportedParam_covers_fiber_within_morseRadius e hr
  have hc : S.shiftedCenter e = D.position.eventCenter t ht := by
    exact D.second.shiftedCenter_chronologicalGlobalEvent t ht
  have hparam : (D.position.eventModel t ht).param =
      S.transportedParam e := by
    rw [D.eventModel_eq_transportedStandardMorseEvent t ht]
    simpa [S, e,
      FiniteIFTSurfaceCover.SharedCutoffMorseData.CriticalValueShiftData.transportedStandardMorseEvent] using
      StandardMorseEventAt.castCenter_param
      (D.second.shiftedCenter_chronologicalGlobalEvent t ht)
      (D.second.toCriticalValueShiftData.transportedStandardMorseEvent
        (D.chronologicalGlobalEvent t ht))
  obtain ⟨ε, hε, hcover⟩ := H
  refine ⟨ε, hε, ?_⟩
  intro v hv hzero
  have hv' : dist v (S.shiftedCenter e) < ε := by
    rw [hc]
    exact hv
  have hzero' : S.output.G v = 0 := by
    simpa [S] using hzero
  obtain ⟨u, hu, huv⟩ := hcover v hv' hzero'
  refine ⟨u, hu, ?_⟩
  rw [hparam]
  exact huv


-- @@ L158-158 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L160-160 verbatim
/-! ## Radial transport of critical saddle ends -/


-- @@ L162-193 verbatim
/-- A convex interpolation between two scalars with the same strict signed
branch remains on that signed half-line. -/
theorem signedBranch_saddleAffineCoordinate_pos
    (e : SaddleBranch) {s₀ s₁ : ℝ}
    (hs₀ : 0 < signedBranch e s₀)
    (hs₁ : 0 < signedBranch e s₁) (q : I) :
    0 < signedBranch e (saddleAffineCoordinate s₀ s₁ q) := by
  cases e with
  | positive =>
      simp only [signedBranch] at hs₀ hs₁ ⊢
      by_cases hq : (q : ℝ) = 1
      · simpa [saddleAffineCoordinate, hq] using hs₁
      · have hq_lt : (q : ℝ) < 1 :=
          lt_of_le_of_ne q.property.2 hq
        have hleft : 0 < (1 - (q : ℝ)) * s₀ :=
          mul_pos (sub_pos.mpr hq_lt) hs₀
        have hright : 0 ≤ (q : ℝ) * s₁ :=
          mul_nonneg q.property.1 hs₁.le
        simp only [saddleAffineCoordinate]
        linarith
  | negative =>
      simp only [signedBranch] at hs₀ hs₁ ⊢
      by_cases hq : (q : ℝ) = 1
      · simpa [saddleAffineCoordinate, hq] using hs₁
      · have hq_lt : (q : ℝ) < 1 :=
          lt_of_le_of_ne q.property.2 hq
        have hleft : (1 - (q : ℝ)) * s₀ < 0 :=
          mul_neg_of_pos_of_neg (sub_pos.mpr hq_lt) (by linarith)
        have hright : (q : ℝ) * s₁ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos q.property.1 (by linarith)
        simp only [saddleAffineCoordinate]
        linarith


-- @@ L195-195 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L197-197 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L198-198 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L199-199 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L201-248 verbatim
/-- At critical level, the full-radius local branch arc stays away from the
saddle center when its starting point has the same second-coordinate end
label as its target. -/
theorem saddlePositiveArcToBoundaryFull_mem_puncturedCriticalSlice_zero
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (hindex : M.index = .saddle)
    (b e : SaddleBranch) (rho : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = (0 : ℝ) ^ 2)
    (hfirst : 0 < signedBranch b (u 0))
    (hsecond : 0 < signedBranch e (u 1))
    (hrho : 0 < rho) (hu : ‖u‖ < T.radius)
    (hrho_radius : rho < T.radius) (q : I) :
    M.saddlePositiveArcToBoundaryFull H b e rho 0 u
        hquad hfirst hrho (by nlinarith [sq_pos_of_pos hrho])
        (hu.trans_le T.radius_le) (hrho_radius.trans_le T.radius_le) q ∈
      puncturedCriticalSlice C center := by
  let z := saddlePositiveArcToBoundaryParam b e rho 0 u q
  have ha : (0 : ℝ) ^ 2 < rho ^ 2 := by
    nlinarith [sq_pos_of_pos hrho]
  have huM : ‖u‖ < M.radius := hu.trans_le T.radius_le
  have hrhoM : rho < M.radius := hrho_radius.trans_le T.radius_le
  refine ⟨M.saddlePositiveArcToBoundaryFull_fiber H b e rho 0 u
      hquad hfirst hrho ha huM hrhoM q, ?_, ?_⟩
  · simpa using M.saddlePositiveArcToBoundaryFull_time H hindex b e
      rho 0 u hquad hfirst hrho ha huM hrhoM q
  · intro hcenter
    have hzNorm : ‖z‖ < T.radius := by
      exact norm_saddlePositiveArcToBoundaryParam_lt b e u hquad hfirst
        hrho ha hu hrho_radius q
    have hzParam : M.param z = M.param 0 := by
      change M.param z = center at hcenter
      rw [M.param_zero]
      exact hcenter
    have hz0 : z = 0 := by
      apply T.param_injOn
      · simpa [Metric.mem_ball, dist_zero_right] using hzNorm
      · simpa [Metric.mem_ball] using T.radius_pos
      · exact hzParam
    have hsigma : 0 < saddleBoundaryParameter rho 0 :=
      saddleBoundaryParameter_pos_at_zero hrho
    have hendSign : 0 < signedBranch e
        (signedBranch e (saddleBoundaryParameter rho 0)) := by
      cases e <;> simp [signedBranch, hsigma]
    have hzSign : 0 < signedBranch e (z 1) := by
      simpa [z, saddlePositiveArcToBoundaryParam, saddlePositiveArc] using
        signedBranch_saddleAffineCoordinate_pos e hsecond hendSign q
    rw [hz0] at hzSign
    cases e <;> simp [signedBranch] at hzSign


-- @@ L250-271 verbatim
/-- The critical ray from an arbitrary locally labelled point to the fixed
chart-boundary end, regarded as an ordinary path. -/
noncomputable def saddleCriticalRayToBoundaryPath
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (b e : SaddleBranch) (rho : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = (0 : ℝ) ^ 2)
    (hfirst : 0 < signedBranch b (u 0))
    (hrho : 0 < rho) (hu : ‖u‖ < T.radius)
    (hrho_radius : rho < T.radius) :
    Path (M.param u) (M.saddleCriticalBoundaryEnd (b, e) rho) where
  toContinuousMap := M.saddlePositiveArcToBoundaryFull H b e rho 0 u
    hquad hfirst hrho (by nlinarith [sq_pos_of_pos hrho])
    (hu.trans_le T.radius_le) (hrho_radius.trans_le T.radius_le)
  source' := by
    exact M.saddlePositiveArcToBoundaryFull_zero H b e rho 0 u
      hquad hfirst hrho (by nlinarith [sq_pos_of_pos hrho])
      (hu.trans_le T.radius_le) (hrho_radius.trans_le T.radius_le)
  target' := by
    simpa [StandardMorseEventAt.saddleCriticalBoundaryEnd] using
      M.saddlePositiveArcToBoundaryFull_one H b e rho 0 u
        hquad hfirst hrho (by nlinarith [sq_pos_of_pos hrho])
        (hu.trans_le T.radius_le) (hrho_radius.trans_le T.radius_le)


-- @@ L273-286 verbatim
theorem saddleCriticalRayToBoundaryPath_mem_puncturedCriticalSlice
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (hindex : M.index = .saddle)
    (b e : SaddleBranch) (rho : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = (0 : ℝ) ^ 2)
    (hfirst : 0 < signedBranch b (u 0))
    (hsecond : 0 < signedBranch e (u 1))
    (hrho : 0 < rho) (hu : ‖u‖ < T.radius)
    (hrho_radius : rho < T.radius) (q : I) :
    T.saddleCriticalRayToBoundaryPath H b e rho u hquad
        hfirst hrho hu hrho_radius q ∈
      puncturedCriticalSlice C center := by
  exact T.saddlePositiveArcToBoundaryFull_mem_puncturedCriticalSlice_zero
    H hindex b e rho u hquad hfirst hsecond hrho hu hrho_radius q


-- @@ L288-299 verbatim
/-- The first coordinate of a positive-radius critical end has its declared
branch sign. -/
theorem saddleCriticalBoundaryEndParam_first_sign
    (p : SaddleBranch × SaddleBranch) {rho : ℝ} (hrho : 0 < rho) :
    0 < signedBranch p.1 ((saddleCriticalBoundaryEndParam p rho) 0) := by
  have hsigma : 0 < saddleBoundaryParameter rho 0 :=
    saddleBoundaryParameter_pos_at_zero hrho
  rcases p with ⟨b, e⟩
  cases b <;> cases e <;>
    simp [saddleCriticalBoundaryEndParam, saddlePositiveBoundaryEndParam,
      saddlePositiveArc, signedBranch, Real.sqrt_sq_eq_abs,
      abs_of_pos hsigma, hsigma]


-- @@ L301-311 verbatim
/-- The second coordinate of a positive-radius critical end has its declared
end sign. -/
theorem saddleCriticalBoundaryEndParam_second_sign
    (p : SaddleBranch × SaddleBranch) {rho : ℝ} (hrho : 0 < rho) :
    0 < signedBranch p.2 ((saddleCriticalBoundaryEndParam p rho) 1) := by
  have hsigma : 0 < saddleBoundaryParameter rho 0 :=
    saddleBoundaryParameter_pos_at_zero hrho
  rcases p with ⟨b, e⟩
  cases b <;> cases e <;>
    simp [saddleCriticalBoundaryEndParam, saddlePositiveBoundaryEndParam,
      saddlePositiveArc, signedBranch, hsigma]


-- @@ L313-341 verbatim
/-- Radial transport between two positive critical chart-boundary radii.
The path follows one labelled critical ray and hence never hits the saddle
center. -/
noncomputable def saddleCriticalBoundaryRadialPath
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (p : SaddleBranch × SaddleBranch) (rho sigma : ℝ)
    (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hrho_radius : rho < T.radius)
    (hsigma_radius : sigma < T.radius) :
    Path (M.saddleCriticalBoundaryEnd p rho)
      (M.saddleCriticalBoundaryEnd p sigma) := by
  let u := saddleCriticalBoundaryEndParam p rho
  have hquad : morseQuadratic .saddle (u 0, u 1) = (0 : ℝ) ^ 2 := by
    simp [u, saddleCriticalBoundaryEndParam,
      saddlePositiveBoundaryEndParam]
  have hfirst : 0 < signedBranch p.1 (u 0) := by
    exact saddleCriticalBoundaryEndParam_first_sign p hrho
  have hu : ‖u‖ < T.radius := by
    rw [show ‖u‖ = rho by
      exact norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho
        (by nlinarith [sq_pos_of_pos hrho])]
    exact hrho_radius
  let gamma := T.saddleCriticalRayToBoundaryPath H p.1 p.2 sigma u
    hquad hfirst hsigma hu hsigma_radius
  exact gamma.cast (by
      simp [u, StandardMorseEventAt.saddleCriticalBoundaryEnd,
        saddleCriticalBoundaryEndParam,
        StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint]) rfl


-- @@ L343-368 verbatim
theorem saddleCriticalBoundaryRadialPath_mem_puncturedCriticalSlice
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (hindex : M.index = .saddle)
    (p : SaddleBranch × SaddleBranch) (rho sigma : ℝ)
    (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hrho_radius : rho < T.radius)
    (hsigma_radius : sigma < T.radius) (q : I) :
    T.saddleCriticalBoundaryRadialPath H p rho sigma hrho hsigma
        hrho_radius hsigma_radius q ∈
      puncturedCriticalSlice C center := by
  let u := saddleCriticalBoundaryEndParam p rho
  have hquad : morseQuadratic .saddle (u 0, u 1) = (0 : ℝ) ^ 2 := by
    simp [u, saddleCriticalBoundaryEndParam,
      saddlePositiveBoundaryEndParam]
  have hfirst : 0 < signedBranch p.1 (u 0) :=
    saddleCriticalBoundaryEndParam_first_sign p hrho
  have hsecond : 0 < signedBranch p.2 (u 1) :=
    saddleCriticalBoundaryEndParam_second_sign p hrho
  have hu : ‖u‖ < T.radius := by
    rw [show ‖u‖ = rho by
      exact norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho
        (by nlinarith [sq_pos_of_pos hrho])]
    exact hrho_radius
  simpa [saddleCriticalBoundaryRadialPath] using
    T.saddleCriticalRayToBoundaryPath_mem_puncturedCriticalSlice H hindex
      p.1 p.2 sigma u hquad hfirst hsecond hsigma hu hsigma_radius q


-- @@ L370-370 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L372-372 verbatim
namespace SaddleCriticalExteriorArc


-- @@ L374-374 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L375-375 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L376-376 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L378-415 verbatim
/-- Change the chart-boundary radius of a punctured critical arc by attaching
the two local critical rays. -/
noncomputable def changeSaddleBoundaryRadius
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (hindex : M.index = .saddle)
    {rho sigma : ℝ} (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hrho_radius : rho < T.radius)
    (hsigma_radius : sigma < T.radius)
    {p q : SaddleBranch × SaddleBranch}
    (A : SaddleCriticalExteriorArc
      (fun r => M.saddleCriticalBoundaryEnd r rho)
      (StandardMorseEventAt.puncturedCriticalSlice C center) p q) :
    SaddleCriticalExteriorArc
      (fun r => M.saddleCriticalBoundaryEnd r sigma)
      (StandardMorseEventAt.puncturedCriticalSlice C center) p q := by
  let left := T.saddleCriticalBoundaryRadialPath H p sigma rho
    hsigma hrho hsigma_radius hrho_radius
  let right := T.saddleCriticalBoundaryRadialPath H q rho sigma
    hrho hsigma hrho_radius hsigma_radius
  refine {
    toPath := left.trans (A.toPath.trans right)
    mem_exterior := ?_ }
  intro u
  have hu : left.trans (A.toPath.trans right) u ∈
      Set.range (left.trans (A.toPath.trans right)) := ⟨u, rfl⟩
  rw [Path.trans_range, Path.trans_range] at hu
  rcases hu with hleft | hmiddle | hright
  · obtain ⟨v, hv⟩ := hleft
    rw [← hv]
    exact T.saddleCriticalBoundaryRadialPath_mem_puncturedCriticalSlice
      H hindex p sigma rho hsigma hrho hsigma_radius hrho_radius v
  · obtain ⟨v, hv⟩ := hmiddle
    rw [← hv]
    exact A.mem_exterior v
  · obtain ⟨v, hv⟩ := hright
    rw [← hv]
    exact T.saddleCriticalBoundaryRadialPath_mem_puncturedCriticalSlice
      H hindex q rho sigma hrho hsigma hrho_radius hsigma_radius v


-- @@ L417-417 verbatim
end SaddleCriticalExteriorArc


-- @@ L419-419 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L421-421 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L422-422 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L423-423 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L425-482 verbatim
/-- A center-based fiber cover into the embedded parameter ball yields one
smaller positive boundary radius with a uniform endpoint-local fiber cover at
all four critical ends. -/
theorem exists_smallSaddleBoundaryRadius_endpointCover
    (T : M.EmbeddedShrink)
    (hcover : ∃ ε > 0,
      ∀ v : EuclideanSpace ℝ (Fin (n + 2)),
        dist v center < ε → C.G v = 0 →
        ∃ u : E₂, ‖u‖ < T.radius ∧ M.param u = v) :
    ∃ rho > 0, rho < T.radius ∧ ∃ δ > 0,
      ∀ (p : SaddleBranch × SaddleBranch)
        (v : EuclideanSpace ℝ (Fin (n + 2))),
        dist v (M.saddleCriticalBoundaryEnd p rho) < δ →
        C.G v = 0 →
        ∃ u : E₂, ‖u‖ < T.radius ∧ M.param u = v := by
  obtain ⟨ε, hε, hcover⟩ := hcover
  have hzero : ‖(0 : E₂)‖ < T.radius := by
    simpa using T.radius_pos
  have hcont : ContinuousAt M.param 0 :=
    (T.param_differentiableAt 0 hzero).continuousAt
  obtain ⟨eta, heta, hclose⟩ := (Metric.continuousAt_iff.mp hcont)
    (ε / 2) (by positivity)
  let rho := min T.radius eta / 2
  have hmin : 0 < min T.radius eta := lt_min T.radius_pos heta
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  have hrhoT : rho < T.radius := by
    dsimp [rho]
    have hle := min_le_left T.radius eta
    nlinarith
  have hrhoEta : rho < eta := by
    dsimp [rho]
    have hle := min_le_right T.radius eta
    nlinarith
  refine ⟨rho, hrho, hrhoT, ε / 2, by positivity, ?_⟩
  intro p v hv hendFiber
  have hendClose : dist (M.saddleCriticalBoundaryEnd p rho) center <
      ε / 2 := by
    let u := saddleCriticalBoundaryEndParam p rho
    have huEta : dist u 0 < eta := by
      rw [dist_zero_right, show ‖u‖ = rho by
        exact norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho
          (by nlinarith [sq_pos_of_pos hrho])]
      exact hrhoEta
    have h := hclose huEta
    simpa [u, M.param_zero,
      StandardMorseEventAt.saddleCriticalBoundaryEnd,
      saddleCriticalBoundaryEndParam,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint] using h
  have hvCenter : dist v center < ε := by
    calc
      dist v center ≤ dist v (M.saddleCriticalBoundaryEnd p rho) +
          dist (M.saddleCriticalBoundaryEnd p rho) center :=
        dist_triangle _ _ _
      _ < ε := by linarith
  exact hcover v hvCenter hendFiber


-- @@ L484-521 verbatim
/-- Punctured critical-arc pairing data is independent of the positive chart
boundary radius, as long as both radii lie in one embedded Morse shrink. -/
theorem changeSaddlePuncturedCriticalArcPairingRadius
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (hindex : M.index = .saddle)
    {rho sigma : ℝ} (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hrho_radius : rho < T.radius)
    (hsigma_radius : sigma < T.radius)
    (A : M.SaddlePuncturedCriticalArcPairingData rho) :
    M.SaddlePuncturedCriticalArcPairingData sigma where
  paired := by
    intro p
    refine ⟨A.mate p, ⟨A.mate_ne p, ?_⟩, ?_⟩
    · exact (A.mate_arc p).map fun B =>
        B.changeSaddleBoundaryRadius T H hindex hrho hsigma
          hrho_radius hsigma_radius
    · intro q hq
      have hback : Nonempty (SaddleCriticalExteriorArc
          (fun r => M.saddleCriticalBoundaryEnd r rho)
          (StandardMorseEventAt.puncturedCriticalSlice C center) p q) :=
        hq.2.map fun B =>
          B.changeSaddleBoundaryRadius T H hindex hsigma hrho
            hsigma_radius hrho_radius
      exact A.eq_mate_of_ne_arc hq.1 hback
  orientation_opposite := by
    intro p q hne harc
    have hback : Nonempty (SaddleCriticalExteriorArc
        (fun r => M.saddleCriticalBoundaryEnd r rho)
        (StandardMorseEventAt.puncturedCriticalSlice C center) p q) :=
      harc.map fun B =>
        B.changeSaddleBoundaryRadius T H hindex hsigma hrho
          hsigma_radius hrho_radius
    have hold := A.orientation_opposite hne hback
    have hchecker : saddleBranchEndChecker p ≠ saddleBranchEndChecker q :=
      (saddleCriticalBoundaryOrientation_mul_neg_iff_checker_ne
        p q hrho).mp hold
    exact (saddleCriticalBoundaryOrientation_mul_neg_iff_checker_ne
      p q hsigma).mpr hchecker


-- @@ L523-523 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L525-525 verbatim
namespace StandardMorseEventAt


-- @@ L527-527 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L528-528 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L529-529 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L531-577 verbatim
/-- Candidate arcs plus the oriented endpoint law already force uniqueness
of the other labelled end.  Indeed, if `q` and `mate p` were two different
nontrivial endpoints reachable from `p`, concatenating the reverse candidate
arc with the arc to `q` would connect them.  All three checker values would
then have to be pairwise different, which is impossible for `Bool`.

This packages the remaining global proof in its shortest useful form: build
one candidate arc from every end and prove checker separation for an
arbitrary nontrivial punctured critical arc. -/
theorem saddlePuncturedCriticalArcPairingData_of_candidate
    {rho : ℝ} (hrho : 0 < rho)
    (mate : SaddleBranch × SaddleBranch →
      SaddleBranch × SaddleBranch)
    (mate_ne : ∀ p, mate p ≠ p)
    (mate_arc : ∀ p, Nonempty (SaddleCriticalExteriorArc
      (fun r => M.saddleCriticalBoundaryEnd r rho)
      (puncturedCriticalSlice C center) p (mate p)))
    (arc_checker_ne : ∀ {p q}, q ≠ p →
      Nonempty (SaddleCriticalExteriorArc
        (fun r => M.saddleCriticalBoundaryEnd r rho)
        (puncturedCriticalSlice C center) p q) →
      saddleBranchEndChecker p ≠ saddleBranchEndChecker q) :
    M.SaddlePuncturedCriticalArcPairingData rho := by
  apply SaddleCriticalExteriorArcPairingData.ofMate mate mate_ne mate_arc
  · intro p q hqp harc
    by_contra hqmate
    have hmateChecker : saddleBranchEndChecker p ≠
        saddleBranchEndChecker (mate p) :=
      arc_checker_ne (mate_ne p) (mate_arc p)
    have hqChecker : saddleBranchEndChecker p ≠
        saddleBranchEndChecker q :=
      arc_checker_ne hqp harc
    have hbridge : Nonempty (SaddleCriticalExteriorArc
        (fun r => M.saddleCriticalBoundaryEnd r rho)
        (puncturedCriticalSlice C center) (mate p) q) :=
      Nonempty.map2 (fun A B => A.symm.trans B) (mate_arc p) harc
    have hbridgeChecker : saddleBranchEndChecker (mate p) ≠
        saddleBranchEndChecker q :=
      arc_checker_ne hqmate hbridge
    cases hp : saddleBranchEndChecker p <;>
      cases hm : saddleBranchEndChecker (mate p) <;>
      cases hq : saddleBranchEndChecker q <;>
      simp_all
  · intro p
    exact (saddleCriticalBoundaryOrientation_mul_neg_iff_checker_ne
      p (mate p) hrho).mpr
        (arc_checker_ne (mate_ne p) (mate_arc p))


-- @@ L579-599 verbatim
/-- Positive-side candidate form: the second-label local matching supplies
the candidate arcs; arbitrary-arc checker separation supplies all global
uniqueness. -/
theorem saddlePuncturedCriticalArcPairingData_of_flipSecond
    {rho : ℝ} (hrho : 0 < rho)
    (mate_arc : ∀ p, Nonempty (SaddleCriticalExteriorArc
      (fun r => M.saddleCriticalBoundaryEnd r rho)
      (puncturedCriticalSlice C center) p (saddleBranchEndFlipSecond p)))
    (arc_checker_ne : ∀ {p q}, q ≠ p →
      Nonempty (SaddleCriticalExteriorArc
        (fun r => M.saddleCriticalBoundaryEnd r rho)
        (puncturedCriticalSlice C center) p q) →
      saddleBranchEndChecker p ≠ saddleBranchEndChecker q) :
    M.SaddlePuncturedCriticalArcPairingData rho := by
  apply M.saddlePuncturedCriticalArcPairingData_of_candidate hrho
    saddleBranchEndFlipSecond
  · rintro ⟨b, e⟩
    cases b <;> cases e <;>
      simp [saddleBranchEndFlipSecond, SaddleBranch.other]
  · exact mate_arc
  · exact arc_checker_ne


-- @@ L601-619 verbatim
/-- Negative-side candidate form, with the first-label local matching. -/
theorem saddlePuncturedCriticalArcPairingData_of_flipFirst
    {rho : ℝ} (hrho : 0 < rho)
    (mate_arc : ∀ p, Nonempty (SaddleCriticalExteriorArc
      (fun r => M.saddleCriticalBoundaryEnd r rho)
      (puncturedCriticalSlice C center) p (saddleBranchEndFlipFirst p)))
    (arc_checker_ne : ∀ {p q}, q ≠ p →
      Nonempty (SaddleCriticalExteriorArc
        (fun r => M.saddleCriticalBoundaryEnd r rho)
        (puncturedCriticalSlice C center) p q) →
      saddleBranchEndChecker p ≠ saddleBranchEndChecker q) :
    M.SaddlePuncturedCriticalArcPairingData rho := by
  apply M.saddlePuncturedCriticalArcPairingData_of_candidate hrho
    saddleBranchEndFlipFirst
  · rintro ⟨b, e⟩
    cases b <;> cases e <;>
      simp [saddleBranchEndFlipFirst, SaddleBranch.other]
  · exact mate_arc
  · exact arc_checker_ne


-- @@ L621-621 verbatim
end StandardMorseEventAt


-- @@ L623-623 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L625-643 verbatim
/-- The actual chronological production saddle admits a sufficiently small
chart-boundary radius with one uniform endpoint-local cover into its embedded
Morse ball. -/
theorem exists_smallSaddleBoundaryRadius_endpointCover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    let T := D.chronologicalEventEmbeddedShrink t ht
    ∃ rho > 0, rho < T.radius ∧ ∃ δ > 0,
      ∀ (p : SaddleBranch × SaddleBranch)
        (v : EuclideanSpace ℝ (Fin (n + 2))),
        dist v ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho) <
            δ →
        D.signedOutput.cobordism.G v = 0 →
        ∃ u : E₂, ‖u‖ < T.radius ∧
          (D.position.eventModel t ht).param u = v := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  have hcenterCover := D.eventModel_covers_fiber_within_morseRadius
    t ht T.radius_pos
  exact T.exists_smallSaddleBoundaryRadius_endpointCover hcenterCover


-- @@ L645-645 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L647-647 verbatim
namespace MorsePosition


-- @@ L649-649 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L651-677 verbatim
/-- Every sufficiently small nonzero positive quadratic displacement from an
event time is a regular slice, not only the one canonical chronological
window chosen elsewhere. -/
theorem sliceRegular_eventCenter_add_sq
    (P : MorsePosition C) (t : ℝ) (ht : t ∈ P.eventTimes)
    {a : ℝ} (ha : 0 < a)
    (haBracket : a < (P.eventBracket t ht).modelRadius) :
    sliceRegular C.G (tcoord (P.eventCenter t ht) + a ^ 2) := by
  let B := P.eventBracket t ht
  have haSq : a ^ 2 < B.modelRadius ^ 2 :=
    (sq_lt_sq₀ ha.le B.modelRadius_pos.le).2 haBracket
  apply (P.sliceRegular_iff_not_mem_eventTimes _).2
  intro hs
  let v := P.eventCenter
    (tcoord (P.eventCenter t ht) + a ^ 2) hs
  have hvcrit : v ∈ timeCritical C.G :=
    (P.eventCenter_mem_coreCriticalPoints _ hs).1
  have hvtime : tcoord v = tcoord (P.eventCenter t ht) + a ^ 2 := by
    exact P.eventCenter_time _ hs
  have hvIcc : tcoord v ∈ Set.Icc B.before B.after := by
    rw [hvtime, B.before_eq_center_sub_modelRadius_sq,
      B.after_eq_center_add_modelRadius_sq]
    constructor <;> linarith [sq_pos_of_pos ha]
  have hveq : v = P.eventCenter t ht := B.isolates v hvcrit hvIcc
  have htimeEq := congrArg tcoord hveq
  rw [hvtime] at htimeEq
  nlinarith [sq_pos_of_pos ha]


-- @@ L679-703 verbatim
/-- Negative quadratic displacement counterpart. -/
theorem sliceRegular_eventCenter_sub_sq
    (P : MorsePosition C) (t : ℝ) (ht : t ∈ P.eventTimes)
    {a : ℝ} (ha : 0 < a)
    (haBracket : a < (P.eventBracket t ht).modelRadius) :
    sliceRegular C.G (tcoord (P.eventCenter t ht) - a ^ 2) := by
  let B := P.eventBracket t ht
  have haSq : a ^ 2 < B.modelRadius ^ 2 :=
    (sq_lt_sq₀ ha.le B.modelRadius_pos.le).2 haBracket
  apply (P.sliceRegular_iff_not_mem_eventTimes _).2
  intro hs
  let v := P.eventCenter
    (tcoord (P.eventCenter t ht) - a ^ 2) hs
  have hvcrit : v ∈ timeCritical C.G :=
    (P.eventCenter_mem_coreCriticalPoints _ hs).1
  have hvtime : tcoord v = tcoord (P.eventCenter t ht) - a ^ 2 := by
    exact P.eventCenter_time _ hs
  have hvIcc : tcoord v ∈ Set.Icc B.before B.after := by
    rw [hvtime, B.before_eq_center_sub_modelRadius_sq,
      B.after_eq_center_add_modelRadius_sq]
    constructor <;> linarith [sq_pos_of_pos ha]
  have hveq : v = P.eventCenter t ht := B.isolates v hvcrit hvIcc
  have htimeEq := congrArg tcoord hveq
  rw [hvtime] at htimeEq
  nlinarith [sq_pos_of_pos ha]


-- @@ L705-705 verbatim
end MorsePosition


-- @@ L707-707 verbatim
/-! ## The four marked chart ends -/


-- @@ L709-712 verbatim
/-- Fixed two-element enumeration used to turn the two local ends of one
hyperbola branch into a `Fin 2` marking. -/
def saddleBranchOfFinTwo : Fin 2 → SaddleBranch :=
  fun i => if i = 0 then .negative else .positive


-- @@ L714-716 verbatim
@[simp] theorem saddleBranchOfFinTwo_zero :
    saddleBranchOfFinTwo 0 = .negative := by
  simp [saddleBranchOfFinTwo]


-- @@ L718-720 verbatim
@[simp] theorem saddleBranchOfFinTwo_one :
    saddleBranchOfFinTwo 1 = .positive := by
  simp [saddleBranchOfFinTwo]


-- @@ L722-725 verbatim
theorem saddleBranchOfFinTwo_injective : Injective saddleBranchOfFinTwo := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [saddleBranchOfFinTwo]


-- @@ L727-733 verbatim
/-- Fixed enumeration of the four critical end labels. -/
def saddleBranchPairOfFinFour : Fin 4 → SaddleBranch × SaddleBranch :=
  fun i =>
    if i = 0 then (.negative, .negative)
    else if i = 1 then (.negative, .positive)
    else if i = 2 then (.positive, .negative)
    else (.positive, .positive)


-- @@ L735-740 verbatim
/-- Explicit inverse label for the four branch/end pairs. -/
def finFourOfSaddleBranchPair : SaddleBranch × SaddleBranch → Fin 4
  | (.negative, .negative) => 0
  | (.negative, .positive) => 1
  | (.positive, .negative) => 2
  | (.positive, .positive) => 3


-- @@ L742-747 verbatim
@[simp] theorem saddleBranchPairOfFinFour_finFourOfSaddleBranchPair
    (p : SaddleBranch × SaddleBranch) :
    saddleBranchPairOfFinFour (finFourOfSaddleBranchPair p) = p := by
  rcases p with ⟨b, e⟩
  cases b <;> cases e <;>
    simp [finFourOfSaddleBranchPair, saddleBranchPairOfFinFour]


-- @@ L749-753 verbatim
@[simp] theorem finFourOfSaddleBranchPair_saddleBranchPairOfFinFour
    (i : Fin 4) :
    finFourOfSaddleBranchPair (saddleBranchPairOfFinFour i) = i := by
  fin_cases i <;>
    simp [finFourOfSaddleBranchPair, saddleBranchPairOfFinFour]


-- @@ L755-759 verbatim
theorem saddleBranchPairOfFinFour_injective :
    Injective saddleBranchPairOfFinFour := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [saddleBranchPairOfFinFour]


-- @@ L761-779 verbatim
/-- The four critical saddle parameters are pairwise distinct at every
positive chart radius. -/
theorem saddleCriticalBoundaryEndParam_injective
    {rho : ℝ} (hrho : 0 < rho) :
    Injective (fun p : SaddleBranch × SaddleBranch =>
      saddleCriticalBoundaryEndParam p rho) := by
  intro p q hpq
  rcases p with ⟨bp, ep⟩
  rcases q with ⟨bq, eq⟩
  have hs : 0 < saddleBoundaryParameter rho 0 :=
    saddleBoundaryParameter_pos_at_zero hrho
  have hzero := congrArg (fun u : E₂ => u 0) hpq
  have hone := congrArg (fun u : E₂ => u 1) hpq
  cases bp <;> cases ep <;> cases bq <;> cases eq <;>
    simp [saddleCriticalBoundaryEndParam,
      saddlePositiveBoundaryEndParam, saddlePositiveArc,
      pairToMorseParam, signedBranch,
    Real.sqrt_sq_eq_abs, abs_of_pos hs] at hzero hone ⊢ <;>
    linarith


-- @@ L781-803 verbatim
/-- The four ends remain pairwise distinct on every nearby positive regular
slice meeting the same parameter circle. -/
theorem saddlePositiveBoundaryEndParam_injective
    {rho a : ℝ} (ha : a ^ 2 < rho ^ 2) :
    Injective (fun p : SaddleBranch × SaddleBranch =>
      saddlePositiveBoundaryEndParam p.1 p.2 rho a) := by
  have hs : 0 < saddleBoundaryParameter rho a := by
    unfold saddleBoundaryParameter
    apply Real.sqrt_pos.2
    nlinarith
  have hsqrt : 0 < Real.sqrt
      (a ^ 2 + saddleBoundaryParameter rho a ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos hs]
  intro p q hpq
  rcases p with ⟨bp, ep⟩
  rcases q with ⟨bq, eq⟩
  have hzero := congrArg (fun u : E₂ => u 0) hpq
  have hone := congrArg (fun u : E₂ => u 1) hpq
  cases bp <;> cases ep <;> cases bq <;> cases eq <;>
    simp [saddlePositiveBoundaryEndParam, saddlePositiveArc,
      pairToMorseParam, signedBranch] at hzero hone ⊢ <;>
    nlinarith


-- @@ L805-828 verbatim
/-- Negative regular slices have the same four-end injectivity.  The input
labels use negative branch/end order here; the critical-label swap is applied
later when the two sides are compared. -/
theorem saddleNegativeBoundaryEndParam_injective
    {rho a : ℝ} (ha : a ^ 2 < rho ^ 2) :
    Injective (fun p : SaddleBranch × SaddleBranch =>
      saddleNegativeBoundaryEndParam p.1 p.2 rho a) := by
  have hs : 0 < saddleBoundaryParameter rho a := by
    unfold saddleBoundaryParameter
    apply Real.sqrt_pos.2
    nlinarith
  have hsqrt : 0 < Real.sqrt
      (a ^ 2 + saddleBoundaryParameter rho a ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos hs]
  intro p q hpq
  rcases p with ⟨bp, ep⟩
  rcases q with ⟨bq, eq⟩
  have hzero := congrArg (fun u : E₂ => u 0) hpq
  have hone := congrArg (fun u : E₂ => u 1) hpq
  cases bp <;> cases ep <;> cases bq <;> cases eq <;>
    simp [saddleNegativeBoundaryEndParam, saddleNegativeArc,
      pairToMorseParam, signedBranch] at hzero hone ⊢ <;>
    nlinarith


-- @@ L830-843 verbatim
/-- The affine coordinate along a truncated regular saddle segment is
injective whenever the boundary really meets that level. -/
theorem saddleSegmentCoordinate_injective
    {rho a : ℝ} (ha : a ^ 2 < rho ^ 2) :
    Injective (saddleSegmentCoordinate rho a) := by
  have hs : 0 < saddleBoundaryParameter rho a := by
    unfold saddleBoundaryParameter
    apply Real.sqrt_pos.2
    nlinarith
  intro u v huv
  apply Subtype.ext
  change (2 * (u : ℝ) - 1) * saddleBoundaryParameter rho a =
    (2 * (v : ℝ) - 1) * saddleBoundaryParameter rho a at huv
  nlinarith


-- @@ L845-851 verbatim
theorem saddlePositiveSegmentParam_injective
    (b : SaddleBranch) {rho a : ℝ} (ha : a ^ 2 < rho ^ 2) :
    Injective (saddlePositiveSegmentParam b rho a) := by
  intro u v huv
  apply saddleSegmentCoordinate_injective ha
  have hcoord := congrArg (fun z : E₂ => z 1) huv
  simpa [saddlePositiveSegmentParam, saddlePositiveArc] using hcoord


-- @@ L853-859 verbatim
theorem saddleNegativeSegmentParam_injective
    (b : SaddleBranch) {rho a : ℝ} (ha : a ^ 2 < rho ^ 2) :
    Injective (saddleNegativeSegmentParam b rho a) := by
  intro u v huv
  apply saddleSegmentCoordinate_injective ha
  have hcoord := congrArg (fun z : E₂ => z 0) huv
  simpa [saddleNegativeSegmentParam, saddleNegativeArc] using hcoord


-- @@ L861-865 verbatim
@[simp] theorem saddlePositiveSegmentParam_zero
    (b : SaddleBranch) (rho a : ℝ) :
    saddlePositiveSegmentParam b rho a 0 =
      saddlePositiveBoundaryEndParam b .negative rho a := by
  simp [saddlePositiveSegmentParam, saddlePositiveBoundaryEndParam]


-- @@ L867-871 verbatim
@[simp] theorem saddlePositiveSegmentParam_one
    (b : SaddleBranch) (rho a : ℝ) :
    saddlePositiveSegmentParam b rho a 1 =
      saddlePositiveBoundaryEndParam b .positive rho a := by
  simp [saddlePositiveSegmentParam, saddlePositiveBoundaryEndParam]


-- @@ L873-877 verbatim
@[simp] theorem saddleNegativeSegmentParam_zero
    (b : SaddleBranch) (rho a : ℝ) :
    saddleNegativeSegmentParam b rho a 0 =
      saddleNegativeBoundaryEndParam b .negative rho a := by
  simp [saddleNegativeSegmentParam, saddleNegativeBoundaryEndParam]


-- @@ L879-883 verbatim
@[simp] theorem saddleNegativeSegmentParam_one
    (b : SaddleBranch) (rho a : ℝ) :
    saddleNegativeSegmentParam b rho a 1 =
      saddleNegativeBoundaryEndParam b .positive rho a := by
  simp [saddleNegativeSegmentParam, saddleNegativeBoundaryEndParam]


-- @@ L885-910 verbatim
/-- Interior points of a positive local segment lie strictly inside its
boundary circle. -/
theorem norm_saddlePositiveSegmentParam_lt
    (b : SaddleBranch) {rho a : ℝ} (hrho : 0 < rho)
    (ha : a ^ 2 < rho ^ 2) {u : I} (hu : u ∈ Set.Ioo 0 1) :
    ‖saddlePositiveSegmentParam b rho a u‖ < rho := by
  have hs : 0 < saddleBoundaryParameter rho a := by
    unfold saddleBoundaryParameter
    apply Real.sqrt_pos.2
    nlinarith
  have hfactor : (2 * (u : ℝ) - 1) ^ 2 < 1 := by
    have hu0 : 0 < (u : ℝ) := hu.1
    have hu1 : (u : ℝ) < 1 := hu.2
    nlinarith [sq_nonneg (2 * (u : ℝ) - 1)]
  have hcoord : saddleSegmentCoordinate rho a u ^ 2 <
      saddleBoundaryParameter rho a ^ 2 := by
    rw [saddleSegmentCoordinate, mul_pow]
    nlinarith [sq_pos_of_pos hs]
  have hboundary := saddleBoundaryParameter_sq (le_of_lt ha)
  have hsq := norm_pairToMorseParam_saddlePositiveArc_sq b a
    (saddleSegmentCoordinate rho a u)
  change ‖saddlePositiveSegmentParam b rho a u‖ ^ 2 =
    a ^ 2 + 2 * saddleSegmentCoordinate rho a u ^ 2 at hsq
  have hnorm := norm_nonneg (saddlePositiveSegmentParam b rho a u)
  rw [hboundary] at hcoord
  nlinarith


-- @@ L912-937 verbatim
/-- Interior points of a negative local segment satisfy the same strict
boundary inequality. -/
theorem norm_saddleNegativeSegmentParam_lt
    (b : SaddleBranch) {rho a : ℝ} (hrho : 0 < rho)
    (ha : a ^ 2 < rho ^ 2) {u : I} (hu : u ∈ Set.Ioo 0 1) :
    ‖saddleNegativeSegmentParam b rho a u‖ < rho := by
  have hs : 0 < saddleBoundaryParameter rho a := by
    unfold saddleBoundaryParameter
    apply Real.sqrt_pos.2
    nlinarith
  have hfactor : (2 * (u : ℝ) - 1) ^ 2 < 1 := by
    have hu0 : 0 < (u : ℝ) := hu.1
    have hu1 : (u : ℝ) < 1 := hu.2
    nlinarith [sq_nonneg (2 * (u : ℝ) - 1)]
  have hcoord : saddleSegmentCoordinate rho a u ^ 2 <
      saddleBoundaryParameter rho a ^ 2 := by
    rw [saddleSegmentCoordinate, mul_pow]
    nlinarith [sq_pos_of_pos hs]
  have hboundary := saddleBoundaryParameter_sq (le_of_lt ha)
  have hsq := norm_pairToMorseParam_saddleNegativeArc_sq b a
    (saddleSegmentCoordinate rho a u)
  change ‖saddleNegativeSegmentParam b rho a u‖ ^ 2 =
    a ^ 2 + 2 * saddleSegmentCoordinate rho a u ^ 2 at hsq
  have hnorm := norm_nonneg (saddleNegativeSegmentParam b rho a u)
  rw [hboundary] at hcoord
  nlinarith


-- @@ L939-968 verbatim
/-- A positive local segment meets its cutting circle only at its two marked
ends. -/
theorem norm_saddlePositiveSegmentParam_eq_rho_iff
    (b : SaddleBranch) {rho a : ℝ} (hrho : 0 < rho)
    (ha : a ^ 2 < rho ^ 2) (u : I) :
    ‖saddlePositiveSegmentParam b rho a u‖ = rho ↔ u = 0 ∨ u = 1 := by
  constructor
  · intro hnorm
    by_contra hends
    simp only [not_or] at hends
    have hu0 : (0 : ℝ) < (u : ℝ) := by
      refine lt_of_le_of_ne u.property.1 ?_
      intro hu
      apply hends.1
      apply Subtype.ext
      exact hu.symm
    have hu1 : (u : ℝ) < 1 := by
      refine lt_of_le_of_ne u.property.2 ?_
      intro hu
      apply hends.2
      apply Subtype.ext
      exact hu
    have hlt := norm_saddlePositiveSegmentParam_lt b hrho ha
      (u := u) ⟨hu0, hu1⟩
    linarith
  · rintro (rfl | rfl)
    · simpa using norm_saddlePositiveBoundaryEndParam
        b .negative hrho ha
    · simpa using norm_saddlePositiveBoundaryEndParam
        b .positive hrho ha


-- @@ L970-999 verbatim
/-- A negative local segment likewise meets its cutting circle only at the
two marked ends. -/
theorem norm_saddleNegativeSegmentParam_eq_rho_iff
    (b : SaddleBranch) {rho a : ℝ} (hrho : 0 < rho)
    (ha : a ^ 2 < rho ^ 2) (u : I) :
    ‖saddleNegativeSegmentParam b rho a u‖ = rho ↔ u = 0 ∨ u = 1 := by
  constructor
  · intro hnorm
    by_contra hends
    simp only [not_or] at hends
    have hu0 : (0 : ℝ) < (u : ℝ) := by
      refine lt_of_le_of_ne u.property.1 ?_
      intro hu
      apply hends.1
      apply Subtype.ext
      exact hu.symm
    have hu1 : (u : ℝ) < 1 := by
      refine lt_of_le_of_ne u.property.2 ?_
      intro hu
      apply hends.2
      apply Subtype.ext
      exact hu
    have hlt := norm_saddleNegativeSegmentParam_lt b hrho ha
      (u := u) ⟨hu0, hu1⟩
    linarith
  · rintro (rfl | rfl)
    · simpa using norm_saddleNegativeBoundaryEndParam
        b .negative hrho ha
    · simpa using norm_saddleNegativeBoundaryEndParam
        b .positive hrho ha


-- @@ L1001-1030 verbatim
/-- Every scalar between the two cutting-circle coordinates occurs on the
affine segment parameter. -/
theorem exists_saddleSegmentCoordinate_eq
    {rho a z : ℝ} (ha : a ^ 2 < rho ^ 2)
    (hz : z ^ 2 ≤ saddleBoundaryParameter rho a ^ 2) :
    ∃ u : I, saddleSegmentCoordinate rho a u = z := by
  have hs : 0 < saddleBoundaryParameter rho a := by
    unfold saddleBoundaryParameter
    apply Real.sqrt_pos.2
    nlinarith
  have hzlo : -saddleBoundaryParameter rho a ≤ z := by
    nlinarith [sq_nonneg (z + saddleBoundaryParameter rho a)]
  have hzhi : z ≤ saddleBoundaryParameter rho a := by
    nlinarith [sq_nonneg (z - saddleBoundaryParameter rho a)]
  let q : ℝ :=
    (z + saddleBoundaryParameter rho a) /
      (2 * saddleBoundaryParameter rho a)
  have hden : 0 < 2 * saddleBoundaryParameter rho a := by positivity
  have hq0 : 0 ≤ q := by
    apply div_nonneg
    · linarith
    · exact hden.le
  have hq1 : q ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  let u : I := ⟨q, hq0, hq1⟩
  refine ⟨u, ?_⟩
  simp only [saddleSegmentCoordinate, u, q]
  field_simp
  ring


-- @@ L1032-1054 verbatim
/-- A positive-saddle chart point on a fixed signed branch and inside the
cutting circle lies on the explicit local segment for that branch. -/
theorem exists_saddlePositiveSegmentParam_eq_of_norm_le
    (b : SaddleBranch) {rho a : ℝ} (hrho : 0 < rho)
    (ha : a ^ 2 < rho ^ 2) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0)) (hnorm : ‖u‖ ≤ rho) :
    ∃ q : I, saddlePositiveSegmentParam b rho a q = u := by
  have hnormsq := StandardMorseEventAt.norm_sq_eq_coordinates u
  have hnormsq_le : ‖u‖ ^ 2 ≤ rho ^ 2 := by
    nlinarith [norm_nonneg u, sq_nonneg (‖u‖ - rho)]
  have hboundary := saddleBoundaryParameter_sq (le_of_lt ha)
  have hcoord : (u 1) ^ 2 ≤ saddleBoundaryParameter rho a ^ 2 := by
    simp only [morseQuadratic] at hquad
    nlinarith
  obtain ⟨q, hq⟩ := exists_saddleSegmentCoordinate_eq ha hcoord
  refine ⟨q, ?_⟩
  rw [saddlePositiveSegmentParam]
  change pairToMorseParam
      (saddlePositiveArc b a (saddleSegmentCoordinate rho a q)) = u
  rw [hq]
  exact (eq_pairToMorseParam_saddlePositiveArc_of_signedBranch
    b a u hquad hsign).symm


-- @@ L1056-1078 verbatim
/-- Negative-level counterpart of the complete local-segment
classification. -/
theorem exists_saddleNegativeSegmentParam_eq_of_norm_le
    (b : SaddleBranch) {rho a : ℝ} (hrho : 0 < rho)
    (ha : a ^ 2 < rho ^ 2) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1)) (hnorm : ‖u‖ ≤ rho) :
    ∃ q : I, saddleNegativeSegmentParam b rho a q = u := by
  have hnormsq := StandardMorseEventAt.norm_sq_eq_coordinates u
  have hnormsq_le : ‖u‖ ^ 2 ≤ rho ^ 2 := by
    nlinarith [norm_nonneg u, sq_nonneg (‖u‖ - rho)]
  have hboundary := saddleBoundaryParameter_sq (le_of_lt ha)
  have hcoord : (u 0) ^ 2 ≤ saddleBoundaryParameter rho a ^ 2 := by
    simp only [morseQuadratic] at hquad
    nlinarith
  obtain ⟨q, hq⟩ := exists_saddleSegmentCoordinate_eq ha hcoord
  refine ⟨q, ?_⟩
  rw [saddleNegativeSegmentParam]
  change pairToMorseParam
      (saddleNegativeArc b a (saddleSegmentCoordinate rho a q)) = u
  rw [hq]
  exact (eq_pairToMorseParam_saddleNegativeArc_of_signedBranch
    b a u hquad hsign).symm


-- @@ L1080-1100 verbatim
/-- The two positive-level hyperbola segments have disjoint parameter
images. -/
theorem saddlePositiveSegmentParam_negative_ne_positive
    {rho a : ℝ} (ha0 : 0 < a) (u v : I) :
    saddlePositiveSegmentParam .negative rho a u ≠
      saddlePositiveSegmentParam .positive rho a v := by
  intro huv
  have hzero := congrArg (fun z : E₂ => z 0) huv
  have huPos : 0 < Real.sqrt
      (a ^ 2 + saddleSegmentCoordinate rho a u ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos ha0,
      sq_nonneg (saddleSegmentCoordinate rho a u)]
  have hvPos : 0 < Real.sqrt
      (a ^ 2 + saddleSegmentCoordinate rho a v ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos ha0,
      sq_nonneg (saddleSegmentCoordinate rho a v)]
  simp only [saddlePositiveSegmentParam, ContinuousMap.coe_mk,
    saddlePositiveArc, signedBranch, pairToMorseParam_apply_zero] at hzero
  linarith


-- @@ L1102-1122 verbatim
/-- The two negative-level hyperbola segments likewise have disjoint
parameter images. -/
theorem saddleNegativeSegmentParam_negative_ne_positive
    {rho a : ℝ} (ha0 : 0 < a) (u v : I) :
    saddleNegativeSegmentParam .negative rho a u ≠
      saddleNegativeSegmentParam .positive rho a v := by
  intro huv
  have hone := congrArg (fun z : E₂ => z 1) huv
  have huPos : 0 < Real.sqrt
      (a ^ 2 + saddleSegmentCoordinate rho a u ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos ha0,
      sq_nonneg (saddleSegmentCoordinate rho a u)]
  have hvPos : 0 < Real.sqrt
      (a ^ 2 + saddleSegmentCoordinate rho a v ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos ha0,
      sq_nonneg (saddleSegmentCoordinate rho a v)]
  simp only [saddleNegativeSegmentParam, ContinuousMap.coe_mk,
    saddleNegativeArc, signedBranch, pairToMorseParam_apply_one] at hone
  linarith


-- @@ L1124-1124 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L1126-1126 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L1128-1157 verbatim
/-- Injectivity of the embedded chart promotes the four distinct Morse
parameters to four distinct ambient critical-slice ends. -/
theorem saddleCriticalBoundaryEnd_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) {rho : ℝ}
    (hrho : 0 < rho) (hrho_radius : rho < T.radius) :
    Injective (fun p : SaddleBranch × SaddleBranch =>
      M.saddleCriticalBoundaryEnd p rho) := by
  intro p q hpq
  have hrho_sq : (0 : ℝ) ^ 2 < rho ^ 2 := by
    nlinarith [sq_pos_of_pos hrho]
  have hp_mem : saddleCriticalBoundaryEndParam p rho ∈
      Metric.ball (0 : E₂) T.radius := by
    simpa only [Metric.mem_ball, dist_zero_right,
      saddleCriticalBoundaryEndParam,
      norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho hrho_sq] using
        hrho_radius
  have hq_mem : saddleCriticalBoundaryEndParam q rho ∈
      Metric.ball (0 : E₂) T.radius := by
    simpa only [Metric.mem_ball, dist_zero_right,
      saddleCriticalBoundaryEndParam,
      norm_saddlePositiveBoundaryEndParam q.1 q.2 hrho hrho_sq] using
        hrho_radius
  have hparam : saddleCriticalBoundaryEndParam p rho =
      saddleCriticalBoundaryEndParam q rho := T.param_injOn hp_mem hq_mem (by
    simpa [StandardMorseEventAt.saddleCriticalBoundaryEnd,
      saddleCriticalBoundaryEndParam,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint] using hpq)
  exact saddleCriticalBoundaryEndParam_injective hrho hparam


-- @@ L1159-1183 verbatim
/-- Embedded-chart injectivity for the four positive regular-slice ends. -/
theorem saddlePositiveBoundaryEnd_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) {rho a : ℝ}
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Injective (fun p : SaddleBranch × SaddleBranch =>
      M.saddlePositiveBoundaryEnd p.1 p.2 rho a) := by
  intro p q hpq
  have hp_mem : saddlePositiveBoundaryEndParam p.1 p.2 rho a ∈
      Metric.ball (0 : E₂) T.radius := by
    simpa only [Metric.mem_ball, dist_zero_right,
      norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho ha] using
        hrho_radius
  have hq_mem : saddlePositiveBoundaryEndParam q.1 q.2 rho a ∈
      Metric.ball (0 : E₂) T.radius := by
    simpa only [Metric.mem_ball, dist_zero_right,
      norm_saddlePositiveBoundaryEndParam q.1 q.2 hrho ha] using
        hrho_radius
  have hparam : saddlePositiveBoundaryEndParam p.1 p.2 rho a =
      saddlePositiveBoundaryEndParam q.1 q.2 rho a :=
    T.param_injOn hp_mem hq_mem (by
      simpa [StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint] using hpq)
  exact saddlePositiveBoundaryEndParam_injective ha hparam


-- @@ L1185-1209 verbatim
/-- Embedded-chart injectivity for the four negative regular-slice ends. -/
theorem saddleNegativeBoundaryEnd_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) {rho a : ℝ}
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Injective (fun p : SaddleBranch × SaddleBranch =>
      M.saddleNegativeBoundaryEnd p.1 p.2 rho a) := by
  intro p q hpq
  have hp_mem : saddleNegativeBoundaryEndParam p.1 p.2 rho a ∈
      Metric.ball (0 : E₂) T.radius := by
    simpa only [Metric.mem_ball, dist_zero_right,
      norm_saddleNegativeBoundaryEndParam p.1 p.2 hrho ha] using
        hrho_radius
  have hq_mem : saddleNegativeBoundaryEndParam q.1 q.2 rho a ∈
      Metric.ball (0 : E₂) T.radius := by
    simpa only [Metric.mem_ball, dist_zero_right,
      norm_saddleNegativeBoundaryEndParam q.1 q.2 hrho ha] using
        hrho_radius
  have hparam : saddleNegativeBoundaryEndParam p.1 p.2 rho a =
      saddleNegativeBoundaryEndParam q.1 q.2 rho a :=
    T.param_injOn hp_mem hq_mem (by
      simpa [StandardMorseEventAt.saddleNegativeBoundaryEnd,
        StandardMorseEventAt.localPoint] using hpq)
  exact saddleNegativeBoundaryEndParam_injective ha hparam


-- @@ L1211-1239 verbatim
/-- Dropping the common time coordinate preserves injectivity of the four
positive ends. -/
theorem saddlePositiveSpatialBoundaryEnd_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    {rho a : ℝ} (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Injective (fun p : SaddleBranch × SaddleBranch =>
      spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a)) := by
  intro p q hpq
  change spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a) =
    spacePart (M.saddlePositiveBoundaryEnd q.1 q.2 rho a) at hpq
  apply T.saddlePositiveBoundaryEnd_injective hrho ha hrho_radius
  calc
    M.saddlePositiveBoundaryEnd p.1 p.2 rho a =
        cobSpaceTime
          (spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a))
          (tcoord (M.saddlePositiveBoundaryEnd p.1 p.2 rho a)) :=
      (spaceTime_spacePart _).symm
    _ = cobSpaceTime
          (spacePart (M.saddlePositiveBoundaryEnd q.1 q.2 rho a))
          (tcoord (M.saddlePositiveBoundaryEnd q.1 q.2 rho a)) := by
      rw [hpq,
        M.saddlePositiveBoundaryEnd_time hindex p.1 p.2 hrho ha
          (hrho_radius.trans_le T.radius_le),
        M.saddlePositiveBoundaryEnd_time hindex q.1 q.2 hrho ha
          (hrho_radius.trans_le T.radius_le)]
    _ = M.saddlePositiveBoundaryEnd q.1 q.2 rho a :=
      spaceTime_spacePart _


-- @@ L1241-1268 verbatim
/-- Negative-slice spatial endpoint injectivity. -/
theorem saddleNegativeSpatialBoundaryEnd_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    {rho a : ℝ} (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Injective (fun p : SaddleBranch × SaddleBranch =>
      spacePart (M.saddleNegativeBoundaryEnd p.1 p.2 rho a)) := by
  intro p q hpq
  change spacePart (M.saddleNegativeBoundaryEnd p.1 p.2 rho a) =
    spacePart (M.saddleNegativeBoundaryEnd q.1 q.2 rho a) at hpq
  apply T.saddleNegativeBoundaryEnd_injective hrho ha hrho_radius
  calc
    M.saddleNegativeBoundaryEnd p.1 p.2 rho a =
        cobSpaceTime
          (spacePart (M.saddleNegativeBoundaryEnd p.1 p.2 rho a))
          (tcoord (M.saddleNegativeBoundaryEnd p.1 p.2 rho a)) :=
      (spaceTime_spacePart _).symm
    _ = cobSpaceTime
          (spacePart (M.saddleNegativeBoundaryEnd q.1 q.2 rho a))
          (tcoord (M.saddleNegativeBoundaryEnd q.1 q.2 rho a)) := by
      rw [hpq,
        M.saddleNegativeBoundaryEnd_time hindex p.1 p.2 hrho ha
          (hrho_radius.trans_le T.radius_le),
        M.saddleNegativeBoundaryEnd_time hindex q.1 q.2 hrho ha
          (hrho_radius.trans_le T.radius_le)]
    _ = M.saddleNegativeBoundaryEnd q.1 q.2 rho a :=
      spaceTime_spacePart _


-- @@ L1270-1270 verbatim
/-! ### The two exact local regular-slice segments -/


-- @@ L1272-1285 verbatim
/-- The embedded image of one complete truncated positive hyperbola branch. -/
def saddlePositiveSegment
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) : C(I, E') where
  toFun u := M.param (saddlePositiveSegmentParam b rho a u)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro u
    apply (T.param_differentiableAt _ ?_).continuousAt.comp'
      (saddlePositiveSegmentParam b rho a).continuous.continuousAt
    exact (norm_saddlePositiveSegmentParam_le b hrho ha u).trans_lt
      hrho_radius


-- @@ L1287-1300 verbatim
/-- Negative-level counterpart. -/
def saddleNegativeSegment
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) : C(I, E') where
  toFun u := M.param (saddleNegativeSegmentParam b rho a u)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro u
    apply (T.param_differentiableAt _ ?_).continuousAt.comp'
      (saddleNegativeSegmentParam b rho a).continuous.continuousAt
    exact (norm_saddleNegativeSegmentParam_le b hrho ha u).trans_lt
      hrho_radius


-- @@ L1302-1311 verbatim
/-- Spatial projection of the positive local segment. -/
def saddlePositiveSpatialSegment
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) : C(I, E₁) where
  toFun u := spacePart (T.saddlePositiveSegment b rho a hrho ha
    hrho_radius u)
  continuous_toFun := continuous_spacePart.comp
    (T.saddlePositiveSegment b rho a hrho ha hrho_radius).continuous


-- @@ L1313-1322 verbatim
/-- Spatial projection of the negative local segment. -/
def saddleNegativeSpatialSegment
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) : C(I, E₁) where
  toFun u := spacePart (T.saddleNegativeSegment b rho a hrho ha
    hrho_radius u)
  continuous_toFun := continuous_spacePart.comp
    (T.saddleNegativeSegment b rho a hrho ha hrho_radius).continuous


-- @@ L1324-1334 verbatim
@[simp] theorem saddlePositiveSegment_zero
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    T.saddlePositiveSegment b rho a hrho ha hrho_radius 0 =
      M.saddlePositiveBoundaryEnd b .negative rho a := by
  simp [saddlePositiveSegment, saddlePositiveSegmentParam,
    saddleSegmentCoordinate, StandardMorseEventAt.saddlePositiveBoundaryEnd,
    saddlePositiveBoundaryEndParam, signedBranch,
    StandardMorseEventAt.localPoint]


-- @@ L1336-1347 verbatim
@[simp] theorem saddlePositiveSegment_one
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    T.saddlePositiveSegment b rho a hrho ha hrho_radius 1 =
      M.saddlePositiveBoundaryEnd b .positive rho a := by
  simp [saddlePositiveSegment, saddlePositiveSegmentParam,
    saddleSegmentCoordinate, StandardMorseEventAt.saddlePositiveBoundaryEnd,
    saddlePositiveBoundaryEndParam, signedBranch,
    StandardMorseEventAt.localPoint]
  norm_num


-- @@ L1349-1359 verbatim
@[simp] theorem saddleNegativeSegment_zero
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    T.saddleNegativeSegment b rho a hrho ha hrho_radius 0 =
      M.saddleNegativeBoundaryEnd b .negative rho a := by
  simp [saddleNegativeSegment, saddleNegativeSegmentParam,
    saddleSegmentCoordinate, StandardMorseEventAt.saddleNegativeBoundaryEnd,
    saddleNegativeBoundaryEndParam, signedBranch,
    StandardMorseEventAt.localPoint]


-- @@ L1361-1372 verbatim
@[simp] theorem saddleNegativeSegment_one
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    T.saddleNegativeSegment b rho a hrho ha hrho_radius 1 =
      M.saddleNegativeBoundaryEnd b .positive rho a := by
  simp [saddleNegativeSegment, saddleNegativeSegmentParam,
    saddleSegmentCoordinate, StandardMorseEventAt.saddleNegativeBoundaryEnd,
    saddleNegativeBoundaryEndParam, signedBranch,
    StandardMorseEventAt.localPoint]
  norm_num


-- @@ L1374-1382 verbatim
theorem saddlePositiveSegment_fiber
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : I) :
    C.G (T.saddlePositiveSegment b rho a hrho ha hrho_radius u) = 0 := by
  apply M.param_fiber
  exact ((norm_saddlePositiveSegmentParam_le b hrho ha u).trans_lt
    hrho_radius).trans_le T.radius_le


-- @@ L1384-1392 verbatim
theorem saddleNegativeSegment_fiber
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : I) :
    C.G (T.saddleNegativeSegment b rho a hrho ha hrho_radius u) = 0 := by
  apply M.param_fiber
  exact ((norm_saddleNegativeSegmentParam_le b hrho ha u).trans_lt
    hrho_radius).trans_le T.radius_le


-- @@ L1394-1405 verbatim
theorem saddlePositiveSegment_time
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : I) :
    tcoord (T.saddlePositiveSegment b rho a hrho ha hrho_radius u) =
      tcoord center + a ^ 2 := by
  change tcoord (M.param (saddlePositiveSegmentParam b rho a u)) = _
  rw [M.time_model _ (((norm_saddlePositiveSegmentParam_le b hrho ha u).trans_lt
    hrho_radius).trans_le T.radius_le), hindex]
  simp [saddlePositiveSegmentParam]


-- @@ L1407-1419 verbatim
theorem saddleNegativeSegment_time
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : I) :
    tcoord (T.saddleNegativeSegment b rho a hrho ha hrho_radius u) =
      tcoord center - a ^ 2 := by
  change tcoord (M.param (saddleNegativeSegmentParam b rho a u)) = _
  rw [M.time_model _ (((norm_saddleNegativeSegmentParam_le b hrho ha u).trans_lt
    hrho_radius).trans_le T.radius_le), hindex]
  simp [saddleNegativeSegmentParam]
  ring


-- @@ L1421-1436 verbatim
theorem saddlePositiveSpatialSegment_mem_fiber
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2)) (u : I) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u ∈
      (T.saddlePositiveSlice a hreg).fiber := by
  rw [saddlePositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (T.saddlePositiveSegment b rho a hrho ha hrho_radius u))
    (tcoord center + a ^ 2)) = 0
  rw [← T.saddlePositiveSegment_time hindex b rho a hrho ha hrho_radius u,
    spaceTime_spacePart]
  exact T.saddlePositiveSegment_fiber b rho a hrho ha hrho_radius u


-- @@ L1438-1453 verbatim
theorem saddleNegativeSpatialSegment_mem_fiber
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2)) (u : I) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u ∈
      (T.saddleNegativeSlice a hreg).fiber := by
  rw [saddleNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (T.saddleNegativeSegment b rho a hrho ha hrho_radius u))
    (tcoord center - a ^ 2)) = 0
  rw [← T.saddleNegativeSegment_time hindex b rho a hrho ha hrho_radius u,
    spaceTime_spacePart]
  exact T.saddleNegativeSegment_fiber b rho a hrho ha hrho_radius u


-- @@ L1455-1465 verbatim
/-- Positive local segment with its actual spatial boundary endpoints. -/
def saddlePositiveSpatialSegmentPath
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Path (spacePart (M.saddlePositiveBoundaryEnd b .negative rho a))
      (spacePart (M.saddlePositiveBoundaryEnd b .positive rho a)) where
  toContinuousMap := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  source' := by simp [saddlePositiveSpatialSegment]
  target' := by simp [saddlePositiveSpatialSegment]


-- @@ L1467-1477 verbatim
/-- Negative local segment with its actual spatial boundary endpoints. -/
def saddleNegativeSpatialSegmentPath
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Path (spacePart (M.saddleNegativeBoundaryEnd b .negative rho a))
      (spacePart (M.saddleNegativeBoundaryEnd b .positive rho a)) where
  toContinuousMap := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  source' := by simp [saddleNegativeSpatialSegment]
  target' := by simp [saddleNegativeSpatialSegment]


-- @@ L1479-1494 verbatim
theorem saddlePositiveSegment_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Injective (T.saddlePositiveSegment b rho a hrho ha hrho_radius) := by
  intro u v huv
  apply saddlePositiveSegmentParam_injective b ha
  apply T.param_injOn
  · rw [Metric.mem_ball, dist_zero_right]
    exact (norm_saddlePositiveSegmentParam_le b hrho ha u).trans_lt
      hrho_radius
  · rw [Metric.mem_ball, dist_zero_right]
    exact (norm_saddlePositiveSegmentParam_le b hrho ha v).trans_lt
      hrho_radius
  · exact huv


-- @@ L1496-1511 verbatim
theorem saddleNegativeSegment_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Injective (T.saddleNegativeSegment b rho a hrho ha hrho_radius) := by
  intro u v huv
  apply saddleNegativeSegmentParam_injective b ha
  apply T.param_injOn
  · rw [Metric.mem_ball, dist_zero_right]
    exact (norm_saddleNegativeSegmentParam_le b hrho ha u).trans_lt
      hrho_radius
  · rw [Metric.mem_ball, dist_zero_right]
    exact (norm_saddleNegativeSegmentParam_le b hrho ha v).trans_lt
      hrho_radius
  · exact huv


-- @@ L1513-1539 verbatim
theorem saddlePositiveSpatialSegment_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Injective (T.saddlePositiveSpatialSegment b rho a hrho ha
      hrho_radius) := by
  intro u v huv
  apply T.saddlePositiveSegment_injective b rho a hrho ha hrho_radius
  change spacePart (T.saddlePositiveSegment b rho a hrho ha
    hrho_radius u) = spacePart (T.saddlePositiveSegment b rho a hrho ha
      hrho_radius v) at huv
  calc
    T.saddlePositiveSegment b rho a hrho ha hrho_radius u =
        cobSpaceTime
          (spacePart (T.saddlePositiveSegment b rho a hrho ha hrho_radius u))
          (tcoord (T.saddlePositiveSegment b rho a hrho ha hrho_radius u)) :=
      (spaceTime_spacePart _).symm
    _ = cobSpaceTime
          (spacePart (T.saddlePositiveSegment b rho a hrho ha hrho_radius v))
          (tcoord (T.saddlePositiveSegment b rho a hrho ha hrho_radius v)) := by
      rw [huv,
        T.saddlePositiveSegment_time hindex b rho a hrho ha hrho_radius u,
        T.saddlePositiveSegment_time hindex b rho a hrho ha hrho_radius v]
    _ = T.saddlePositiveSegment b rho a hrho ha hrho_radius v :=
      spaceTime_spacePart _


-- @@ L1541-1567 verbatim
theorem saddleNegativeSpatialSegment_injective
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) :
    Injective (T.saddleNegativeSpatialSegment b rho a hrho ha
      hrho_radius) := by
  intro u v huv
  apply T.saddleNegativeSegment_injective b rho a hrho ha hrho_radius
  change spacePart (T.saddleNegativeSegment b rho a hrho ha
    hrho_radius u) = spacePart (T.saddleNegativeSegment b rho a hrho ha
      hrho_radius v) at huv
  calc
    T.saddleNegativeSegment b rho a hrho ha hrho_radius u =
        cobSpaceTime
          (spacePart (T.saddleNegativeSegment b rho a hrho ha hrho_radius u))
          (tcoord (T.saddleNegativeSegment b rho a hrho ha hrho_radius u)) :=
      (spaceTime_spacePart _).symm
    _ = cobSpaceTime
          (spacePart (T.saddleNegativeSegment b rho a hrho ha hrho_radius v))
          (tcoord (T.saddleNegativeSegment b rho a hrho ha hrho_radius v)) := by
      rw [huv,
        T.saddleNegativeSegment_time hindex b rho a hrho ha hrho_radius u,
        T.saddleNegativeSegment_time hindex b rho a hrho ha hrho_radius v]
    _ = T.saddleNegativeSegment b rho a hrho ha hrho_radius v :=
      spaceTime_spacePart _


-- @@ L1569-1586 verbatim
/-- Parameter-level chart classification lifted to the actual embedded
positive spatial slice. -/
theorem spacePart_param_mem_range_saddlePositiveSpatialSegment_of_norm_le
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0)) (hnorm : ‖u‖ ≤ rho) :
    spacePart (M.param u) ∈ Set.range
      (T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius) := by
  obtain ⟨q, hq⟩ :=
    exists_saddlePositiveSegmentParam_eq_of_norm_le b hrho ha u
      hquad hsign hnorm
  refine ⟨q, ?_⟩
  simp only [saddlePositiveSpatialSegment, saddlePositiveSegment,
    ContinuousMap.coe_mk]
  rw [hq]


-- @@ L1588-1604 verbatim
/-- Negative spatial-slice counterpart of the chart range theorem. -/
theorem spacePart_param_mem_range_saddleNegativeSpatialSegment_of_norm_le
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1)) (hnorm : ‖u‖ ≤ rho) :
    spacePart (M.param u) ∈ Set.range
      (T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius) := by
  obtain ⟨q, hq⟩ :=
    exists_saddleNegativeSegmentParam_eq_of_norm_le b hrho ha u
      hquad hsign hnorm
  refine ⟨q, ?_⟩
  simp only [saddleNegativeSpatialSegment, saddleNegativeSegment,
    ContinuousMap.coe_mk]
  rw [hq]


-- @@ L1606-1634 verbatim
/-- The portion of a positive regular saddle level inside the cutting
circle is exactly covered by the two explicit local branch segments. -/
theorem spacePart_param_mem_union_saddlePositiveSpatialSegments_of_norm_le
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (rho a : ℝ)
    (hrho : 0 < rho) (ha0 : 0 < a) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hnorm : ‖u‖ ≤ rho) :
    spacePart (M.param u) ∈
      Set.range (T.saddlePositiveSpatialSegment .negative rho a
        hrho ha hrho_radius) ∪
      Set.range (T.saddlePositiveSpatialSegment .positive rho a
        hrho ha hrho_radius) := by
  have hu0 : u 0 ≠ 0 := by
    intro hu
    simp only [morseQuadratic, hu] at hquad
    nlinarith [sq_nonneg (u 1), sq_pos_of_pos ha0]
  rcases lt_or_gt_of_ne hu0 with hu0 | hu0
  · left
    apply T.spacePart_param_mem_range_saddlePositiveSpatialSegment_of_norm_le
      .negative rho a hrho ha hrho_radius u hquad
    · simpa [signedBranch] using neg_pos.mpr hu0
    · exact hnorm
  · right
    apply T.spacePart_param_mem_range_saddlePositiveSpatialSegment_of_norm_le
      .positive rho a hrho ha hrho_radius u hquad
    · simpa [signedBranch] using hu0
    · exact hnorm


-- @@ L1636-1664 verbatim
/-- The negative regular saddle level has the analogous exact two-segment
local classification. -/
theorem spacePart_param_mem_union_saddleNegativeSpatialSegments_of_norm_le
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (rho a : ℝ)
    (hrho : 0 < rho) (ha0 : 0 < a) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hnorm : ‖u‖ ≤ rho) :
    spacePart (M.param u) ∈
      Set.range (T.saddleNegativeSpatialSegment .negative rho a
        hrho ha hrho_radius) ∪
      Set.range (T.saddleNegativeSpatialSegment .positive rho a
        hrho ha hrho_radius) := by
  have hu1 : u 1 ≠ 0 := by
    intro hu
    simp only [morseQuadratic, hu] at hquad
    nlinarith [sq_nonneg (u 0), sq_pos_of_pos ha0]
  rcases lt_or_gt_of_ne hu1 with hu1 | hu1
  · left
    apply T.spacePart_param_mem_range_saddleNegativeSpatialSegment_of_norm_le
      .negative rho a hrho ha hrho_radius u hquad
    · simpa [signedBranch] using neg_pos.mpr hu1
    · exact hnorm
  · right
    apply T.spacePart_param_mem_range_saddleNegativeSpatialSegment_of_norm_le
      .positive rho a hrho ha hrho_radius u hquad
    · simpa [signedBranch] using hu1
    · exact hnorm


-- @@ L1666-1731 verbatim
/-- A positive local segment meets the full four-point chart boundary only at
its own two labelled ends. -/
theorem saddlePositiveSpatialSegment_eq_boundaryEnd_iff
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (p : SaddleBranch × SaddleBranch)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : I) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u =
        spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a) ↔
      (u = 0 ∧ p = (b, .negative)) ∨
        (u = 1 ∧ p = (b, .positive)) := by
  constructor
  · intro hspace
    change spacePart (T.saddlePositiveSegment b rho a hrho ha
      hrho_radius u) =
        spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a) at hspace
    have hambient :
        T.saddlePositiveSegment b rho a hrho ha hrho_radius u =
          M.saddlePositiveBoundaryEnd p.1 p.2 rho a := by
      calc
        T.saddlePositiveSegment b rho a hrho ha hrho_radius u =
            cobSpaceTime
              (spacePart (T.saddlePositiveSegment b rho a hrho ha
                hrho_radius u))
              (tcoord (T.saddlePositiveSegment b rho a hrho ha
                hrho_radius u)) := (spaceTime_spacePart _).symm
        _ = cobSpaceTime
              (spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a))
              (tcoord (M.saddlePositiveBoundaryEnd p.1 p.2 rho a)) := by
          rw [hspace,
            T.saddlePositiveSegment_time hindex b rho a hrho ha
              hrho_radius u,
            M.saddlePositiveBoundaryEnd_time hindex p.1 p.2 hrho ha
              (hrho_radius.trans_le T.radius_le)]
        _ = M.saddlePositiveBoundaryEnd p.1 p.2 rho a :=
          spaceTime_spacePart _
    have hparam : saddlePositiveSegmentParam b rho a u =
        saddlePositiveBoundaryEndParam p.1 p.2 rho a := by
      apply T.param_injOn
      · rw [Metric.mem_ball, dist_zero_right]
        exact (norm_saddlePositiveSegmentParam_le b hrho ha u).trans_lt
          hrho_radius
      · rw [Metric.mem_ball, dist_zero_right,
          norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho ha]
        exact hrho_radius
      · simpa [saddlePositiveSegment,
          StandardMorseEventAt.saddlePositiveBoundaryEnd,
          StandardMorseEventAt.localPoint] using hambient
    have hnorm : ‖saddlePositiveSegmentParam b rho a u‖ = rho := by
      rw [hparam]
      exact norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho ha
    rcases (norm_saddlePositiveSegmentParam_eq_rho_iff b hrho ha u).mp
      hnorm with hu | hu
    · left
      refine ⟨hu, ?_⟩
      have hpairs := T.saddlePositiveSpatialBoundaryEnd_injective hindex
        hrho ha hrho_radius
      exact (hpairs (by simpa [hu] using hspace)).symm
    · right
      refine ⟨hu, ?_⟩
      have hpairs := T.saddlePositiveSpatialBoundaryEnd_injective hindex
        hrho ha hrho_radius
      exact (hpairs (by simpa [hu] using hspace)).symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [saddlePositiveSpatialSegment]


-- @@ L1733-1797 verbatim
/-- Negative-side analogue of the four-point boundary-intersection theorem. -/
theorem saddleNegativeSpatialSegment_eq_boundaryEnd_iff
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (p : SaddleBranch × SaddleBranch)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : I) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u =
        spacePart (M.saddleNegativeBoundaryEnd p.1 p.2 rho a) ↔
      (u = 0 ∧ p = (b, .negative)) ∨
        (u = 1 ∧ p = (b, .positive)) := by
  constructor
  · intro hspace
    change spacePart (T.saddleNegativeSegment b rho a hrho ha
      hrho_radius u) =
        spacePart (M.saddleNegativeBoundaryEnd p.1 p.2 rho a) at hspace
    have hambient :
        T.saddleNegativeSegment b rho a hrho ha hrho_radius u =
          M.saddleNegativeBoundaryEnd p.1 p.2 rho a := by
      calc
        T.saddleNegativeSegment b rho a hrho ha hrho_radius u =
            cobSpaceTime
              (spacePart (T.saddleNegativeSegment b rho a hrho ha
                hrho_radius u))
              (tcoord (T.saddleNegativeSegment b rho a hrho ha
                hrho_radius u)) := (spaceTime_spacePart _).symm
        _ = cobSpaceTime
              (spacePart (M.saddleNegativeBoundaryEnd p.1 p.2 rho a))
              (tcoord (M.saddleNegativeBoundaryEnd p.1 p.2 rho a)) := by
          rw [hspace,
            T.saddleNegativeSegment_time hindex b rho a hrho ha
              hrho_radius u,
            M.saddleNegativeBoundaryEnd_time hindex p.1 p.2 hrho ha
              (hrho_radius.trans_le T.radius_le)]
        _ = M.saddleNegativeBoundaryEnd p.1 p.2 rho a :=
          spaceTime_spacePart _
    have hparam : saddleNegativeSegmentParam b rho a u =
        saddleNegativeBoundaryEndParam p.1 p.2 rho a := by
      apply T.param_injOn
      · rw [Metric.mem_ball, dist_zero_right]
        exact (norm_saddleNegativeSegmentParam_le b hrho ha u).trans_lt
          hrho_radius
      · rw [Metric.mem_ball, dist_zero_right,
          norm_saddleNegativeBoundaryEndParam p.1 p.2 hrho ha]
        exact hrho_radius
      · simpa [saddleNegativeSegment,
          StandardMorseEventAt.saddleNegativeBoundaryEnd,
          StandardMorseEventAt.localPoint] using hambient
    have hnorm : ‖saddleNegativeSegmentParam b rho a u‖ = rho := by
      rw [hparam]
      exact norm_saddleNegativeBoundaryEndParam p.1 p.2 hrho ha
    rcases (norm_saddleNegativeSegmentParam_eq_rho_iff b hrho ha u).mp
      hnorm with hu | hu
    · left
      refine ⟨hu, ?_⟩
      have hpairs := T.saddleNegativeSpatialBoundaryEnd_injective hindex
        hrho ha hrho_radius
      exact (hpairs (by simpa [hu] using hspace)).symm
    · right
      refine ⟨hu, ?_⟩
      have hpairs := T.saddleNegativeSpatialBoundaryEnd_injective hindex
        hrho ha hrho_radius
      exact (hpairs (by simpa [hu] using hspace)).symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [saddleNegativeSpatialSegment]


-- @@ L1799-1841 verbatim
/-- A point strictly inside the positive cutting circle cannot be one of the
four positive chart-boundary marks. -/
theorem spacePart_param_ne_saddlePositiveBoundaryEnd_of_norm_lt
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (p : SaddleBranch × SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hnorm : ‖u‖ < rho) :
    spacePart (M.param u) ≠
      spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a) := by
  intro hspace
  have hu_radius : ‖u‖ < M.radius :=
    (hnorm.trans hrho_radius).trans_le T.radius_le
  have hutime : tcoord (M.param u) = tcoord center + a ^ 2 := by
    rw [M.time_model u hu_radius, hindex, hquad]
  have hambient : M.param u =
      M.saddlePositiveBoundaryEnd p.1 p.2 rho a := by
    calc
      M.param u = cobSpaceTime (spacePart (M.param u))
          (tcoord (M.param u)) := (spaceTime_spacePart _).symm
      _ = cobSpaceTime
          (spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a))
          (tcoord (M.saddlePositiveBoundaryEnd p.1 p.2 rho a)) := by
        rw [hspace, hutime,
          M.saddlePositiveBoundaryEnd_time hindex p.1 p.2 hrho ha
            (hrho_radius.trans_le T.radius_le)]
      _ = M.saddlePositiveBoundaryEnd p.1 p.2 rho a :=
        spaceTime_spacePart _
  have hparam : u = saddlePositiveBoundaryEndParam p.1 p.2 rho a := by
    apply T.param_injOn
    · rw [Metric.mem_ball, dist_zero_right]
      exact hnorm.trans hrho_radius
    · rw [Metric.mem_ball, dist_zero_right,
        norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho ha]
      exact hrho_radius
    · simpa [StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint] using hambient
  have hendnorm :=
    norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho ha
  rw [← hparam] at hendnorm
  linarith


-- @@ L1843-1886 verbatim
/-- A point strictly inside the negative cutting circle likewise avoids all
four negative chart-boundary marks. -/
theorem spacePart_param_ne_saddleNegativeBoundaryEnd_of_norm_lt
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (p : SaddleBranch × SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hnorm : ‖u‖ < rho) :
    spacePart (M.param u) ≠
      spacePart (M.saddleNegativeBoundaryEnd p.1 p.2 rho a) := by
  intro hspace
  have hu_radius : ‖u‖ < M.radius :=
    (hnorm.trans hrho_radius).trans_le T.radius_le
  have hutime : tcoord (M.param u) = tcoord center - a ^ 2 := by
    rw [M.time_model u hu_radius, hindex, hquad]
    ring
  have hambient : M.param u =
      M.saddleNegativeBoundaryEnd p.1 p.2 rho a := by
    calc
      M.param u = cobSpaceTime (spacePart (M.param u))
          (tcoord (M.param u)) := (spaceTime_spacePart _).symm
      _ = cobSpaceTime
          (spacePart (M.saddleNegativeBoundaryEnd p.1 p.2 rho a))
          (tcoord (M.saddleNegativeBoundaryEnd p.1 p.2 rho a)) := by
        rw [hspace, hutime,
          M.saddleNegativeBoundaryEnd_time hindex p.1 p.2 hrho ha
            (hrho_radius.trans_le T.radius_le)]
      _ = M.saddleNegativeBoundaryEnd p.1 p.2 rho a :=
        spaceTime_spacePart _
  have hparam : u = saddleNegativeBoundaryEndParam p.1 p.2 rho a := by
    apply T.param_injOn
    · rw [Metric.mem_ball, dist_zero_right]
      exact hnorm.trans hrho_radius
    · rw [Metric.mem_ball, dist_zero_right,
        norm_saddleNegativeBoundaryEndParam p.1 p.2 hrho ha]
      exact hrho_radius
    · simpa [StandardMorseEventAt.saddleNegativeBoundaryEnd,
        StandardMorseEventAt.localPoint] using hambient
  have hendnorm :=
    norm_saddleNegativeBoundaryEndParam p.1 p.2 hrho ha
  rw [← hparam] at hendnorm
  linarith


-- @@ L1888-1910 verbatim
/-- Both positive boundary ends of a fixed local branch lie on its actual
intrinsic regular-slice orbit. -/
theorem saddlePositiveSpatialBoundaryEnd_mem_branchOrbit
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b e : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    spacePart (M.saddlePositiveBoundaryEnd b e rho a) ∈
      V.orbit (spacePart (T.saddlePositiveBranchBase b rho a)) := by
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  have hgamma : ∀ u, gamma u ∈ (T.saddlePositiveSlice a hreg).fiber :=
    fun u => T.saddlePositiveSpatialSegment_mem_fiber hindex b rho a
      hrho ha hrho_radius hreg u
  cases e with
  | positive =>
      simpa [gamma, saddlePositiveSpatialSegment, saddlePositiveBranchBase]
        using V.continuousMap_mem_orbit gamma hgamma 1
  | negative =>
      simpa [gamma, saddlePositiveSpatialSegment, saddlePositiveBranchBase]
        using V.continuousMap_mem_orbit gamma hgamma 0


-- @@ L1912-1934 verbatim
/-- Both negative boundary ends of a fixed local branch lie on its actual
intrinsic regular-slice orbit. -/
theorem saddleNegativeSpatialBoundaryEnd_mem_branchOrbit
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b e : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    spacePart (M.saddleNegativeBoundaryEnd b e rho a) ∈
      V.orbit (spacePart (T.saddleNegativeBranchBase b rho a)) := by
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  have hgamma : ∀ u, gamma u ∈ (T.saddleNegativeSlice a hreg).fiber :=
    fun u => T.saddleNegativeSpatialSegment_mem_fiber hindex b rho a
      hrho ha hrho_radius hreg u
  cases e with
  | positive =>
      simpa [gamma, saddleNegativeSpatialSegment, saddleNegativeBranchBase]
        using V.continuousMap_mem_orbit gamma hgamma 1
  | negative =>
      simpa [gamma, saddleNegativeSpatialSegment, saddleNegativeBranchBase]
        using V.continuousMap_mem_orbit gamma hgamma 0


-- @@ L1936-1962 verbatim
/-- Every point of the positive local branch segment lies on the same actual
intrinsic orbit as its two marked ends. -/
theorem saddlePositiveSpatialSegment_mem_branchOrbit
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) (u : I) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u ∈
      V.orbit (V.orbitPoint
        (T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
          hrho_radius hreg V)) := by
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  let O := T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
    hrho_radius hreg V
  have hgamma : ∀ v, gamma v ∈ (T.saddlePositiveSlice a hreg).fiber :=
    fun v => T.saddlePositiveSpatialSegment_mem_fiber hindex b rho a
      hrho ha hrho_radius hreg v
  have hu := V.continuousMap_mem_orbit gamma hgamma u
  change gamma u ∈ V.orbit (V.orbitPoint O)
  rw [← V.orbitPoint_orbit O]
  change gamma u ∈
    V.orbit (spacePart (T.saddlePositiveBranchBase b rho a))
  simpa [gamma, saddlePositiveSpatialSegment, saddlePositiveBranchBase]
    using hu


-- @@ L1964-1990 verbatim
/-- Every point of the negative local branch segment lies on its actual
intrinsic orbit as well. -/
theorem saddleNegativeSpatialSegment_mem_branchOrbit
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) (u : I) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u ∈
      V.orbit (V.orbitPoint
        (T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
          hrho_radius hreg V)) := by
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  let O := T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
    hrho_radius hreg V
  have hgamma : ∀ v, gamma v ∈ (T.saddleNegativeSlice a hreg).fiber :=
    fun v => T.saddleNegativeSpatialSegment_mem_fiber hindex b rho a
      hrho ha hrho_radius hreg v
  have hu := V.continuousMap_mem_orbit gamma hgamma u
  change gamma u ∈ V.orbit (V.orbitPoint O)
  rw [← V.orbitPoint_orbit O]
  change gamma u ∈
    V.orbit (spacePart (T.saddleNegativeBranchBase b rho a))
  simpa [gamma, saddleNegativeSpatialSegment, saddleNegativeBranchBase]
    using hu


-- @@ L1992-2042 verbatim
/-- The two actual positive local branch segments are disjoint on every
noncritical regular saddle level. -/
theorem saddlePositiveSpatialSegments_disjoint
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha0 : 0 < a)
    (ha : a ^ 2 < rho ^ 2) (hrho_radius : rho < T.radius) :
    Disjoint
      (Set.range (T.saddlePositiveSpatialSegment .negative rho a
        hrho ha hrho_radius))
      (Set.range (T.saddlePositiveSpatialSegment .positive rho a
        hrho ha hrho_radius)) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  have hspace :
      spacePart (T.saddlePositiveSegment .negative rho a hrho ha
        hrho_radius u) =
      spacePart (T.saddlePositiveSegment .positive rho a hrho ha
        hrho_radius v) := by
    simpa [saddlePositiveSpatialSegment] using hv.symm
  have hambient :
      T.saddlePositiveSegment .negative rho a hrho ha hrho_radius u =
      T.saddlePositiveSegment .positive rho a hrho ha hrho_radius v := by
    calc
      T.saddlePositiveSegment .negative rho a hrho ha hrho_radius u =
          cobSpaceTime
            (spacePart (T.saddlePositiveSegment .negative rho a hrho ha
              hrho_radius u))
            (tcoord (T.saddlePositiveSegment .negative rho a hrho ha
              hrho_radius u)) := (spaceTime_spacePart _).symm
      _ = cobSpaceTime
            (spacePart (T.saddlePositiveSegment .positive rho a hrho ha
              hrho_radius v))
            (tcoord (T.saddlePositiveSegment .positive rho a hrho ha
              hrho_radius v)) := by
        rw [hspace,
          T.saddlePositiveSegment_time hindex .negative rho a hrho ha
            hrho_radius u,
          T.saddlePositiveSegment_time hindex .positive rho a hrho ha
            hrho_radius v]
      _ = T.saddlePositiveSegment .positive rho a hrho ha
          hrho_radius v := spaceTime_spacePart _
  apply saddlePositiveSegmentParam_negative_ne_positive ha0 u v
  apply T.param_injOn
  · rw [Metric.mem_ball, dist_zero_right]
    exact (norm_saddlePositiveSegmentParam_le .negative hrho ha u).trans_lt
      hrho_radius
  · rw [Metric.mem_ball, dist_zero_right]
    exact (norm_saddlePositiveSegmentParam_le .positive hrho ha v).trans_lt
      hrho_radius
  · simpa [saddlePositiveSegment] using hambient


-- @@ L2044-2093 verbatim
/-- Negative regular-level local segments are disjoint as well. -/
theorem saddleNegativeSpatialSegments_disjoint
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha0 : 0 < a)
    (ha : a ^ 2 < rho ^ 2) (hrho_radius : rho < T.radius) :
    Disjoint
      (Set.range (T.saddleNegativeSpatialSegment .negative rho a
        hrho ha hrho_radius))
      (Set.range (T.saddleNegativeSpatialSegment .positive rho a
        hrho ha hrho_radius)) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  have hspace :
      spacePart (T.saddleNegativeSegment .negative rho a hrho ha
        hrho_radius u) =
      spacePart (T.saddleNegativeSegment .positive rho a hrho ha
        hrho_radius v) := by
    simpa [saddleNegativeSpatialSegment] using hv.symm
  have hambient :
      T.saddleNegativeSegment .negative rho a hrho ha hrho_radius u =
      T.saddleNegativeSegment .positive rho a hrho ha hrho_radius v := by
    calc
      T.saddleNegativeSegment .negative rho a hrho ha hrho_radius u =
          cobSpaceTime
            (spacePart (T.saddleNegativeSegment .negative rho a hrho ha
              hrho_radius u))
            (tcoord (T.saddleNegativeSegment .negative rho a hrho ha
              hrho_radius u)) := (spaceTime_spacePart _).symm
      _ = cobSpaceTime
            (spacePart (T.saddleNegativeSegment .positive rho a hrho ha
              hrho_radius v))
            (tcoord (T.saddleNegativeSegment .positive rho a hrho ha
              hrho_radius v)) := by
        rw [hspace,
          T.saddleNegativeSegment_time hindex .negative rho a hrho ha
            hrho_radius u,
          T.saddleNegativeSegment_time hindex .positive rho a hrho ha
            hrho_radius v]
      _ = T.saddleNegativeSegment .positive rho a hrho ha
          hrho_radius v := spaceTime_spacePart _
  apply saddleNegativeSegmentParam_negative_ne_positive ha0 u v
  apply T.param_injOn
  · rw [Metric.mem_ball, dist_zero_right]
    exact (norm_saddleNegativeSegmentParam_le .negative hrho ha u).trans_lt
      hrho_radius
  · rw [Metric.mem_ball, dist_zero_right]
    exact (norm_saddleNegativeSegmentParam_le .positive hrho ha v).trans_lt
      hrho_radius
  · simpa [saddleNegativeSegment] using hambient


-- @@ L2095-2131 verbatim
/-- Distinct positive branch indices force the corresponding intrinsic orbit
and local segment to be disjoint. -/
theorem saddlePositiveBranchOrbit_disjoint_spatialSegment_of_ne
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b c : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (hne : T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
        hrho_radius hreg V ≠
      T.saddlePositiveBranchOrbitIndex hindex c rho a hrho ha
        hrho_radius hreg V) :
    Disjoint
      ((T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
        hrho_radius hreg V : V.OrbitIndex) : Set E₁)
      (Set.range (T.saddlePositiveSpatialSegment c rho a hrho ha
        hrho_radius)) := by
  let Ob := T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
    hrho_radius hreg V
  let Oc := T.saddlePositiveBranchOrbitIndex hindex c rho a hrho ha
    hrho_radius hreg V
  have hneSet : (Ob : Set E₁) ≠ (Oc : Set E₁) := by
    intro hset
    apply hne
    exact Subtype.ext hset
  have hdisj : Disjoint (Ob : Set E₁) (Oc : Set E₁) :=
    V.orbitFinset_pairwise_disjoint (Ob : Set E₁) Ob.property
      (Oc : Set E₁) Oc.property hneSet
  rw [Set.disjoint_left]
  intro x hxb hxc
  obtain ⟨u, rfl⟩ := hxc
  apply Set.disjoint_left.mp hdisj hxb
  rw [V.orbitPoint_orbit Oc]
  exact T.saddlePositiveSpatialSegment_mem_branchOrbit hindex c rho a
    hrho ha hrho_radius hreg V u


-- @@ L2133-2169 verbatim
/-- Negative-side disjointness of a distinct branch orbit and local
segment. -/
theorem saddleNegativeBranchOrbit_disjoint_spatialSegment_of_ne
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b c : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (hne : T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
        hrho_radius hreg V ≠
      T.saddleNegativeBranchOrbitIndex hindex c rho a hrho ha
        hrho_radius hreg V) :
    Disjoint
      ((T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
        hrho_radius hreg V : V.OrbitIndex) : Set E₁)
      (Set.range (T.saddleNegativeSpatialSegment c rho a hrho ha
        hrho_radius)) := by
  let Ob := T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
    hrho_radius hreg V
  let Oc := T.saddleNegativeBranchOrbitIndex hindex c rho a hrho ha
    hrho_radius hreg V
  have hneSet : (Ob : Set E₁) ≠ (Oc : Set E₁) := by
    intro hset
    apply hne
    exact Subtype.ext hset
  have hdisj : Disjoint (Ob : Set E₁) (Oc : Set E₁) :=
    V.orbitFinset_pairwise_disjoint (Ob : Set E₁) Ob.property
      (Oc : Set E₁) Oc.property hneSet
  rw [Set.disjoint_left]
  intro x hxb hxc
  obtain ⟨u, rfl⟩ := hxc
  apply Set.disjoint_left.mp hdisj hxb
  rw [V.orbitPoint_orbit Oc]
  exact T.saddleNegativeSpatialSegment_mem_branchOrbit hindex c rho a
    hrho ha hrho_radius hreg V u


-- @@ L2171-2210 verbatim
/-- On distinct positive branch orbits, every chart point of a given orbit
belongs to that branch's own explicit local segment. -/
theorem spacePart_param_mem_own_saddlePositiveSpatialSegment
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha0 : 0 < a) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (hne : T.saddlePositiveBranchOrbitIndex hindex .negative rho a hrho ha
        hrho_radius hreg V ≠
      T.saddlePositiveBranchOrbitIndex hindex .positive rho a hrho ha
        hrho_radius hreg V)
    (u : E₂) (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hnorm : ‖u‖ ≤ rho)
    (horbit : spacePart (M.param u) ∈
      ((T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
        hrho_radius hreg V : V.OrbitIndex) : Set E₁)) :
    spacePart (M.param u) ∈ Set.range
      (T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius) := by
  have hlocal :=
    T.spacePart_param_mem_union_saddlePositiveSpatialSegments_of_norm_le
      rho a hrho ha0 ha hrho_radius u hquad hnorm
  cases b with
  | negative =>
      rcases hlocal with hlocal | hlocal
      · exact hlocal
      · exact (Set.disjoint_left.mp
          (T.saddlePositiveBranchOrbit_disjoint_spatialSegment_of_ne
            hindex .negative .positive rho a hrho ha hrho_radius hreg V hne)
          horbit hlocal).elim
  | positive =>
      rcases hlocal with hlocal | hlocal
      · exact (Set.disjoint_left.mp
          (T.saddlePositiveBranchOrbit_disjoint_spatialSegment_of_ne
            hindex .positive .negative rho a hrho ha hrho_radius hreg V
              hne.symm)
          horbit hlocal).elim
      · exact hlocal


-- @@ L2212-2251 verbatim
/-- Negative-side counterpart: a chart point on a distinguished orbit lies
on its own local segment whenever the two branch orbits are distinct. -/
theorem spacePart_param_mem_own_saddleNegativeSpatialSegment
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha0 : 0 < a) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (hne : T.saddleNegativeBranchOrbitIndex hindex .negative rho a hrho ha
        hrho_radius hreg V ≠
      T.saddleNegativeBranchOrbitIndex hindex .positive rho a hrho ha
        hrho_radius hreg V)
    (u : E₂) (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hnorm : ‖u‖ ≤ rho)
    (horbit : spacePart (M.param u) ∈
      ((T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
        hrho_radius hreg V : V.OrbitIndex) : Set E₁)) :
    spacePart (M.param u) ∈ Set.range
      (T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius) := by
  have hlocal :=
    T.spacePart_param_mem_union_saddleNegativeSpatialSegments_of_norm_le
      rho a hrho ha0 ha hrho_radius u hquad hnorm
  cases b with
  | negative =>
      rcases hlocal with hlocal | hlocal
      · exact hlocal
      · exact (Set.disjoint_left.mp
          (T.saddleNegativeBranchOrbit_disjoint_spatialSegment_of_ne
            hindex .negative .positive rho a hrho ha hrho_radius hreg V hne)
          horbit hlocal).elim
  | positive =>
      rcases hlocal with hlocal | hlocal
      · exact (Set.disjoint_left.mp
          (T.saddleNegativeBranchOrbit_disjoint_spatialSegment_of_ne
            hindex .positive .negative rho a hrho ha hrho_radius hreg V
              hne.symm)
          horbit hlocal).elim
      · exact hlocal


-- @@ L2253-2253 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L2255-2255 verbatim
/-! ## Cutting an intrinsic orbit at finitely many marked ends -/


-- @@ L2257-2257 verbatim
namespace SimpleClosedOrbitParam


-- @@ L2259-2259 verbatim
variable {m : ℕ}

-- @@ L2260-2260 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 1))

-- @@ L2261-2261 verbatim
variable {X : FramedLevelSet m} {V : TamedField X}


-- @@ L2263-2295 verbatim
/-- Arithmetic normal form for a target representative lying less than one
positive period ahead of a source representative in `[0,T)`. -/
theorem int_translate_forward_normal_form
    {T x y : ℝ} (hT : 0 < T)
    (hx0 : 0 ≤ x) (hxT : x < T) (hy0 : 0 ≤ y) (hyT : y < T)
    (z : ℤ) (hlo : x < y - (z : ℝ) * T)
    (hhi : y - (z : ℝ) * T < x + T) :
    (z = 0 ∧ x < y) ∨ (z = -1 ∧ y < x) := by
  have hzltR : (z : ℝ) < 1 := by
    by_contra hnot
    have hzge : (1 : ℝ) ≤ (z : ℝ) := le_of_not_gt hnot
    have hmul : T ≤ (z : ℝ) * T := by
      simpa using mul_le_mul_of_nonneg_right hzge hT.le
    linarith
  have hzgtR : (-2 : ℝ) < (z : ℝ) := by
    by_contra hnot
    have hzle : (z : ℝ) ≤ -2 := le_of_not_gt hnot
    have hmul : (z : ℝ) * T ≤ -2 * T :=
      mul_le_mul_of_nonneg_right hzle hT.le
    linarith
  have hzlt : z < 1 := by exact_mod_cast hzltR
  have hzgt : (-2 : ℤ) < z := by exact_mod_cast hzgtR
  have hz : z = 0 ∨ z = -1 := by omega
  rcases hz with rfl | rfl
  · left
    constructor
    · rfl
    · simpa using hlo
  · right
    constructor
    · rfl
    · norm_num at hhi ⊢
      linarith


-- @@ L2297-2329 verbatim
/-- Backward counterpart: a representative less than one period behind has
translate index `0` or `1`. -/
theorem int_translate_backward_normal_form
    {T x y : ℝ} (hT : 0 < T)
    (hx0 : 0 ≤ x) (hxT : x < T) (hy0 : 0 ≤ y) (hyT : y < T)
    (z : ℤ) (hlo : x - T < y - (z : ℝ) * T)
    (hhi : y - (z : ℝ) * T < x) :
    (z = 0 ∧ y < x) ∨ (z = 1 ∧ x < y) := by
  have hzgtR : (-1 : ℝ) < (z : ℝ) := by
    by_contra hnot
    have hzle : (z : ℝ) ≤ -1 := le_of_not_gt hnot
    have hmul : (z : ℝ) * T ≤ -1 * T :=
      mul_le_mul_of_nonneg_right hzle hT.le
    linarith
  have hzltR : (z : ℝ) < 2 := by
    by_contra hnot
    have hzge : (2 : ℝ) ≤ (z : ℝ) := le_of_not_gt hnot
    have hmul : 2 * T ≤ (z : ℝ) * T :=
      mul_le_mul_of_nonneg_right hzge hT.le
    linarith
  have hzgt : (-1 : ℤ) < z := by exact_mod_cast hzgtR
  have hzlt : z < 2 := by exact_mod_cast hzltR
  have hz : z = 0 ∨ z = 1 := by omega
  rcases hz with rfl | rfl
  · left
    constructor
    · rfl
    · simpa using hhi
  · right
    constructor
    · rfl
    · norm_num at hlo ⊢
      linarith


-- @@ L2331-2331 verbatim
/-! ### Lifting an arbitrary embedded arc on a simple orbit -/


-- @@ L2333-2342 verbatim
/-- The phase of any continuous path whose image stays on the orbit
parametrized by `P`. -/
def phaseOfOrbitPath
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) :
    C(I, AddCircle (V.fundamentalPeriod P.hp)) where
  toFun u := (V.orbitCircleHomeomorph P.hp).symm ⟨gamma u, hgamma u⟩
  continuous_toFun :=
    (V.orbitCircleHomeomorph P.hp).symm.continuous.comp
      (Continuous.subtype_mk gamma.continuous hgamma)


-- @@ L2344-2350 verbatim
/-- Applying the orbit-circle homeomorphism recovers the original path. -/
theorem orbitCircleHomeomorph_phaseOfOrbitPath
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (u : I) :
    V.orbitCircleHomeomorph P.hp (P.phaseOfOrbitPath gamma hgamma u) =
      ⟨gamma u, hgamma u⟩ := by
  exact (V.orbitCircleHomeomorph P.hp).apply_symm_apply _


-- @@ L2352-2361 verbatim
theorem phaseOfOrbitPath_eq_phase_of_eq
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) {u v : I}
    (huv : gamma u = P.curve v) :
    P.phaseOfOrbitPath gamma hgamma u = P.phase v := by
  apply (V.orbitCircleHomeomorph P.hp).injective
  rw [P.orbitCircleHomeomorph_phaseOfOrbitPath gamma hgamma,
    P.orbitCircleHomeomorph_phase]
  apply Subtype.ext
  exact huv


-- @@ L2363-2374 verbatim
/-- Lift the phase of an orbit path, anchored at any chosen real preimage of
its source phase. -/
def phaseLiftOfOrbitPath
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (r : ℝ)
    (hr : P.phaseOfOrbitPath gamma hgamma 0 =
      (r : AddCircle (V.fundamentalPeriod P.hp))) : C(I, ℝ) := by
  let T := V.fundamentalPeriod P.hp
  letI : Fact (0 < T) := ⟨V.fundamentalPeriod_pos P.hp⟩
  exact (AddCircle.isCoveringMap_coe T).liftPath
    (P.phaseOfOrbitPath gamma hgamma) r hr


-- @@ L2376-2384 verbatim
@[simp] theorem phaseLiftOfOrbitPath_zero
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (r : ℝ)
    (hr : P.phaseOfOrbitPath gamma hgamma 0 =
      (r : AddCircle (V.fundamentalPeriod P.hp))) :
    P.phaseLiftOfOrbitPath gamma hgamma r hr 0 = r := by
  unfold phaseLiftOfOrbitPath
  apply IsCoveringMap.liftPath_zero


-- @@ L2386-2400 verbatim
theorem phaseLiftOfOrbitPath_coe
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (r : ℝ)
    (hr : P.phaseOfOrbitPath gamma hgamma 0 =
      (r : AddCircle (V.fundamentalPeriod P.hp))) (u : I) :
    ((P.phaseLiftOfOrbitPath gamma hgamma r hr u : ℝ) :
        AddCircle (V.fundamentalPeriod P.hp)) =
      P.phaseOfOrbitPath gamma hgamma u := by
  let T := V.fundamentalPeriod P.hp
  letI : Fact (0 < T) := ⟨V.fundamentalPeriod_pos P.hp⟩
  have h := congrFun
    ((AddCircle.isCoveringMap_coe T).liftPath_lifts
      (P.phaseOfOrbitPath gamma hgamma) r hr) u
  simpa [phaseLiftOfOrbitPath, T] using h


-- @@ L2402-2420 verbatim
/-- An embedded orbit arc has an injective real phase lift.  This converts
the circle-order question into ordinary interval order. -/
theorem phaseLiftOfOrbitPath_injective
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma)
    (r : ℝ)
    (hr : P.phaseOfOrbitPath gamma hgamma 0 =
      (r : AddCircle (V.fundamentalPeriod P.hp))) :
    Injective (P.phaseLiftOfOrbitPath gamma hgamma r hr) := by
  intro u v huv
  apply hgamma_inj
  have hphase : P.phaseOfOrbitPath gamma hgamma u =
      P.phaseOfOrbitPath gamma hgamma v := by
    rw [← P.phaseLiftOfOrbitPath_coe gamma hgamma r hr u,
      ← P.phaseLiftOfOrbitPath_coe gamma hgamma r hr v, huv]
  have horbit := congrArg (V.orbitCircleHomeomorph P.hp) hphase
  simpa only [P.orbitCircleHomeomorph_phaseOfOrbitPath gamma hgamma,
    Subtype.mk.injEq] using horbit


-- @@ L2422-2435 verbatim
/-- Consequently every embedded orbit arc has a consistently increasing or
decreasing lifted phase. -/
theorem phaseLiftOfOrbitPath_strictMono_or_strictAnti
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma)
    (r : ℝ)
    (hr : P.phaseOfOrbitPath gamma hgamma 0 =
      (r : AddCircle (V.fundamentalPeriod P.hp))) :
    StrictMono (P.phaseLiftOfOrbitPath gamma hgamma r hr) ∨
      StrictAnti (P.phaseLiftOfOrbitPath gamma hgamma r hr) :=
  (P.phaseLiftOfOrbitPath gamma hgamma r hr).continuous
    |>.strictMono_of_inj_boundedOrder'
      (P.phaseLiftOfOrbitPath_injective gamma hgamma hgamma_inj r hr)


-- @@ L2437-2445 verbatim
/-- Canonical anchoring when the source of the new arc is already presented
as a point of the once-around curve. -/
def phaseLiftOfOrbitPathAtCurve
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v : I)
    (hsource : gamma 0 = P.curve v) : C(I, ℝ) :=
  P.phaseLiftOfOrbitPath gamma hgamma (P.phaseLift v)
    ((P.phaseOfOrbitPath_eq_phase_of_eq gamma hgamma hsource).trans
      (P.phaseLift_coe v).symm)


-- @@ L2447-2453 verbatim
@[simp] theorem phaseLiftOfOrbitPathAtCurve_zero
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v : I)
    (hsource : gamma 0 = P.curve v) :
    P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource 0 =
      P.phaseLift v := by
  exact P.phaseLiftOfOrbitPath_zero gamma hgamma (P.phaseLift v) _


-- @@ L2455-2462 verbatim
theorem phaseLiftOfOrbitPathAtCurve_coe
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v : I)
    (hsource : gamma 0 = P.curve v) (u : I) :
    ((P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource u : ℝ) :
        AddCircle (V.fundamentalPeriod P.hp)) =
      P.phaseOfOrbitPath gamma hgamma u :=
  P.phaseLiftOfOrbitPath_coe gamma hgamma (P.phaseLift v) _ u


-- @@ L2464-2484 verbatim
/-- The endpoint of an anchored arc lift differs from the chosen lift of its
target curve parameter by an integral period. -/
theorem phaseLiftOfOrbitPathAtCurve_target_eq_add_zsmul
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v w : I)
    (hsource : gamma 0 = P.curve v)
    (htarget : gamma 1 = P.curve w) :
    ∃ z : ℤ, P.phaseLift w =
      P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource 1 +
        z • V.fundamentalPeriod P.hp := by
  apply AddCommGroup.modEq_iff_eq_add_zsmul.mp
  apply AddCommGroup.modEq_iff_eq_mod_zmultiples.mpr
  calc
    ((P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource 1 : ℝ) :
        AddCircle (V.fundamentalPeriod P.hp)) =
        P.phaseOfOrbitPath gamma hgamma 1 :=
      P.phaseLiftOfOrbitPathAtCurve_coe gamma hgamma v hsource 1
    _ = P.phase w :=
      P.phaseOfOrbitPath_eq_phase_of_eq gamma hgamma htarget
    _ = ((P.phaseLift w : ℝ) :
        AddCircle (V.fundamentalPeriod P.hp)) := (P.phaseLift_coe w).symm


-- @@ L2486-2493 verbatim
theorem phaseLiftOfOrbitPathAtCurve_injective
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (v : I)
    (hsource : gamma 0 = P.curve v) :
    Injective (P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource) :=
  P.phaseLiftOfOrbitPath_injective gamma hgamma hgamma_inj
    (P.phaseLift v) _


-- @@ L2495-2503 verbatim
theorem phaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (v : I)
    (hsource : gamma 0 = P.curve v) :
    StrictMono (P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource) ∨
      StrictAnti (P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource) :=
  P.phaseLiftOfOrbitPath_strictMono_or_strictAnti gamma hgamma hgamma_inj
    (P.phaseLift v) _


-- @@ L2505-2528 verbatim
/-- Equality of lifted phases modulo an integral period is equality of the
underlying orbit points. -/
theorem eq_curve_of_phaseLiftOfOrbitPathAtCurve_eq_add_zsmul
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v w u : I)
    (hsource : gamma 0 = P.curve v) (z : ℤ)
    (hphase : P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource u =
      P.phaseLift w + z • V.fundamentalPeriod P.hp) :
    gamma u = P.curve w := by
  have hcoe :
      ((P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource u : ℝ) :
          AddCircle (V.fundamentalPeriod P.hp)) =
        ((P.phaseLift w : ℝ) :
          AddCircle (V.fundamentalPeriod P.hp)) := by
    rw [hphase]
    simp
  have hphase' : P.phaseOfOrbitPath gamma hgamma u = P.phase w := by
    rw [← P.phaseLiftOfOrbitPathAtCurve_coe gamma hgamma v hsource u,
      ← P.phaseLift_coe w]
    exact hcoe
  have horbit := congrArg (V.orbitCircleHomeomorph P.hp) hphase'
  rw [P.orbitCircleHomeomorph_phaseOfOrbitPath gamma hgamma,
    P.orbitCircleHomeomorph_phase] at horbit
  exact congrArg Subtype.val horbit


-- @@ L2530-2530 verbatim
/-! ### A uniformly increasing choice of orientation -/


-- @@ L2532-2538 verbatim
/-- Reverse the real phase lift precisely when the once-around curve uses
the negative fundamental period.  The result always increases from `0` to
the positive period. -/
noncomputable def forwardPhaseLift
    (P : SimpleClosedOrbitParam X V) : C(I, ℝ) :=
  if P.phaseLift 1 = V.fundamentalPeriod P.hp then
    P.phaseLift else -P.phaseLift


-- @@ L2540-2543 verbatim
@[simp] theorem forwardPhaseLift_zero
    (P : SimpleClosedOrbitParam X V) : P.forwardPhaseLift 0 = 0 := by
  rw [forwardPhaseLift]
  split_ifs <;> simp


-- @@ L2545-2552 verbatim
@[simp] theorem forwardPhaseLift_one
    (P : SimpleClosedOrbitParam X V) :
    P.forwardPhaseLift 1 = V.fundamentalPeriod P.hp := by
  rw [forwardPhaseLift]
  split_ifs with hpositive
  · exact hpositive
  · have hnegative := P.phaseLift_one_eq_period_or_neg.resolve_left hpositive
    simp [hnegative]


-- @@ L2554-2576 verbatim
theorem forwardPhaseLift_strictMono
    (P : SimpleClosedOrbitParam X V) : StrictMono P.forwardPhaseLift := by
  have hperiod : 0 < V.fundamentalPeriod P.hp :=
    V.fundamentalPeriod_pos P.hp
  have hmonoanti := P.phaseLift.continuous.strictMono_of_inj_boundedOrder'
    P.phaseLift_injective
  rw [forwardPhaseLift]
  split_ifs with hpositive
  · rcases hmonoanti with hmono | hanti
    · exact hmono
    · exfalso
      have hbad := hanti (show (0 : I) < 1 by norm_num)
      rw [P.phaseLift_zero, hpositive] at hbad
      linarith
  · have hnegative := P.phaseLift_one_eq_period_or_neg.resolve_left hpositive
    rcases hmonoanti with hmono | hanti
    · exfalso
      have hbad := hmono (show (0 : I) < 1 by norm_num)
      rw [P.phaseLift_zero, hnegative] at hbad
      linarith
    · intro u v huv
      have h := hanti huv
      simpa only [ContinuousMap.neg_apply, neg_lt_neg_iff] using h


-- @@ L2578-2586 verbatim
/-- Apply the same global orientation choice to the lift of a second orbit
arc. -/
noncomputable def forwardPhaseLiftOfOrbitPathAtCurve
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v : I)
    (hsource : gamma 0 = P.curve v) : C(I, ℝ) :=
  if P.phaseLift 1 = V.fundamentalPeriod P.hp then
    P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource
  else -P.phaseLiftOfOrbitPathAtCurve gamma hgamma v hsource


-- @@ L2588-2595 verbatim
@[simp] theorem forwardPhaseLiftOfOrbitPathAtCurve_zero
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v : I)
    (hsource : gamma 0 = P.curve v) :
    P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource 0 =
      P.forwardPhaseLift v := by
  rw [forwardPhaseLiftOfOrbitPathAtCurve, forwardPhaseLift]
  split_ifs <;> simp


-- @@ L2597-2618 verbatim
theorem forwardPhaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (v : I)
    (hsource : gamma 0 = P.curve v) :
    StrictMono (P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource) ∨
      StrictAnti
        (P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource) := by
  have hmonoanti := P.phaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
    gamma hgamma hgamma_inj v hsource
  rw [forwardPhaseLiftOfOrbitPathAtCurve]
  split_ifs
  · exact hmonoanti
  · rcases hmonoanti with hmono | hanti
    · right
      intro u w huw
      have h := hmono huw
      simpa only [ContinuousMap.neg_apply, neg_lt_neg_iff] using h
    · left
      intro u w huw
      have h := hanti huw
      simpa only [ContinuousMap.neg_apply, neg_lt_neg_iff] using h


-- @@ L2620-2637 verbatim
/-- In forward coordinates, the target mark still differs from the endpoint
of the lifted arc by an integral *positive* period. -/
theorem forwardPhaseLift_target_eq_add_zsmul
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v w : I)
    (hsource : gamma 0 = P.curve v)
    (htarget : gamma 1 = P.curve w) :
    ∃ z : ℤ, P.forwardPhaseLift w =
      P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource 1 +
        z • V.fundamentalPeriod P.hp := by
  obtain ⟨z, hz⟩ := P.phaseLiftOfOrbitPathAtCurve_target_eq_add_zsmul
    gamma hgamma v w hsource htarget
  rw [forwardPhaseLift, forwardPhaseLiftOfOrbitPathAtCurve]
  split_ifs
  · exact ⟨z, hz⟩
  · refine ⟨-z, ?_⟩
    rw [ContinuousMap.neg_apply, ContinuousMap.neg_apply, hz]
    simp [add_comm]


-- @@ L2639-2660 verbatim
/-- The same point-recovery statement in forward coordinates. -/
theorem eq_curve_of_forwardPhaseLift_eq_add_zsmul
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p) (v w u : I)
    (hsource : gamma 0 = P.curve v) (z : ℤ)
    (hphase :
      P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource u =
        P.forwardPhaseLift w + z • V.fundamentalPeriod P.hp) :
    gamma u = P.curve w := by
  by_cases hpositive :
      P.phaseLift 1 = V.fundamentalPeriod P.hp
  · apply P.eq_curve_of_phaseLiftOfOrbitPathAtCurve_eq_add_zsmul
      gamma hgamma v w u hsource z
    simpa [forwardPhaseLiftOfOrbitPathAtCurve, forwardPhaseLift,
      hpositive] using hphase
  · apply P.eq_curve_of_phaseLiftOfOrbitPathAtCurve_eq_add_zsmul
      gamma hgamma v w u hsource (-z)
    simp only [forwardPhaseLiftOfOrbitPathAtCurve, forwardPhaseLift,
      hpositive, if_false, ContinuousMap.neg_apply] at hphase
    simp only [zsmul_eq_mul, Int.cast_neg]
    simp only [zsmul_eq_mul] at hphase
    linarith


-- @@ L2662-2752 verbatim
/-- If the endpoint of an embedded arc lift is the chosen (untranslated)
forward lift of its target curve parameter, the arc has exactly the same
range as the corresponding ordinary curve subinterval. -/
theorem range_eq_curve_image_uIcc_of_forward_endpoint
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (v w : I)
    (hvw : v ≠ w) (hsource : gamma 0 = P.curve v)
    (hend :
      P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource 1 =
        P.forwardPhaseLift w) :
    Set.range gamma = P.curve '' Set.uIcc v w := by
  let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource
  have hF0 : F 0 = P.forwardPhaseLift v :=
    P.forwardPhaseLiftOfOrbitPathAtCurve_zero gamma hgamma v hsource
  have hmonoanti :=
    P.forwardPhaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
      gamma hgamma hgamma_inj v hsource
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · have htheta : P.forwardPhaseLift v < P.forwardPhaseLift w :=
      P.forwardPhaseLift_strictMono hvwlt
    have hFmono : StrictMono F := by
      rcases hmonoanti with hmono | hanti
      · exact hmono
      · have hbad := hanti (show (0 : I) < 1 by norm_num)
        rw [hF0, hend] at hbad
        exact (not_lt_of_ge htheta.le hbad).elim
    rw [Set.uIcc_of_le hvwlt.le]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      have hFu : F u ∈ Set.Icc (P.forwardPhaseLift v)
          (P.forwardPhaseLift w) := by
        rw [← hF0, ← hend]
        exact ⟨hFmono.monotone u.property.1,
          hFmono.monotone u.property.2⟩
      obtain ⟨q, hqI, hq⟩ := intermediate_value_Icc hvwlt.le
        P.forwardPhaseLift.continuous.continuousOn hFu
      refine ⟨q, hqI, ?_⟩
      symm
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 0
      simpa using hq.symm
    · rintro ⟨q, hqI, rfl⟩
      have hqtheta : P.forwardPhaseLift q ∈
          Set.Icc (F 0) (F 1) := by
        rw [hF0, hend]
        exact ⟨P.forwardPhaseLift_strictMono.monotone hqI.1,
          P.forwardPhaseLift_strictMono.monotone hqI.2⟩
      obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) (1 : I)
        F.continuous hqtheta
      refine ⟨u, ?_⟩
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 0
      simpa using hu
  · have htheta : P.forwardPhaseLift w < P.forwardPhaseLift v :=
      P.forwardPhaseLift_strictMono hwvlt
    have hFanti : StrictAnti F := by
      rcases hmonoanti with hmono | hanti
      · have hbad := hmono (show (0 : I) < 1 by norm_num)
        rw [hF0, hend] at hbad
        exact (not_lt_of_ge htheta.le hbad).elim
      · exact hanti
    rw [Set.uIcc_of_ge hwvlt.le]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      have hFu : F u ∈ Set.Icc (P.forwardPhaseLift w)
          (P.forwardPhaseLift v) := by
        rw [← hend, ← hF0]
        exact ⟨hFanti.antitone u.property.2,
          hFanti.antitone u.property.1⟩
      obtain ⟨q, hqI, hq⟩ := intermediate_value_Icc hwvlt.le
        P.forwardPhaseLift.continuous.continuousOn hFu
      refine ⟨q, hqI, ?_⟩
      symm
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 0
      simpa using hq.symm
    · rintro ⟨q, hqI, rfl⟩
      have hqtheta : P.forwardPhaseLift q ∈
          Set.Icc (F 1) (F 0) := by
        rw [hF0, hend]
        exact ⟨P.forwardPhaseLift_strictMono.monotone hqI.1,
          P.forwardPhaseLift_strictMono.monotone hqI.2⟩
      obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) (0 : I)
        F.continuous hqtheta
      refine ⟨u, ?_⟩
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 0
      simpa using hu


-- @@ L2754-2862 verbatim
/-- Forward wrap case: the endpoint lift is one period above the target
representative, so the arc is exactly the suffix-plus-prefix curve cut. -/
theorem range_eq_curve_image_wrap_of_forward_endpoint_add_period
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (v w : I)
    (hv1 : v ≠ 1) (hsource : gamma 0 = P.curve v)
    (hend :
      P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource 1 =
        P.forwardPhaseLift w + V.fundamentalPeriod P.hp) :
    Set.range gamma =
      P.curve '' (Set.Icc v 1 ∪ Set.Icc 0 w) := by
  let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource
  let T := V.fundamentalPeriod P.hp
  have hT : 0 < T := V.fundamentalPeriod_pos P.hp
  have hF0 : F 0 = P.forwardPhaseLift v :=
    P.forwardPhaseLiftOfOrbitPathAtCurve_zero gamma hgamma v hsource
  have hvT : P.forwardPhaseLift v < T := by
    simpa [T] using P.forwardPhaseLift_strictMono
      (lt_of_le_of_ne v.property.2 hv1)
  have hw0 : 0 ≤ P.forwardPhaseLift w := by
    rw [← P.forwardPhaseLift_zero]
    exact P.forwardPhaseLift_strictMono.monotone w.property.1
  have hendsOrder : F 0 < F 1 := by
    rw [hF0, hend]
    linarith
  have hFmono : StrictMono F := by
    rcases P.forwardPhaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
      gamma hgamma hgamma_inj v hsource with hmono | hanti
    · exact hmono
    · have hbad := hanti (show (0 : I) < 1 by norm_num)
      exact (not_lt_of_ge hendsOrder.le hbad).elim
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hFu : F u ∈ Set.Icc (F 0) (F 1) :=
      ⟨hFmono.monotone u.property.1,
        hFmono.monotone u.property.2⟩
    by_cases huT : F u ≤ T
    · have huRange : F u ∈ Set.Icc (P.forwardPhaseLift v)
          (P.forwardPhaseLift 1) := by
        rw [P.forwardPhaseLift_one]
        exact ⟨by simpa [hF0] using hFu.1, huT⟩
      have hIV : Set.Icc (P.forwardPhaseLift v)
          (P.forwardPhaseLift 1) ⊆
          P.forwardPhaseLift '' Set.Icc v 1 :=
        intermediate_value_Icc (show v ≤ (1 : I) from v.property.2)
          (show ContinuousOn (fun q : I => P.forwardPhaseLift q)
            (Set.Icc v 1) from P.forwardPhaseLift.continuous.continuousOn)
      obtain ⟨q, hqI, hq⟩ := hIV huRange
      refine ⟨q, Or.inl hqI, ?_⟩
      symm
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 0
      simpa using hq.symm
    · have hTu : T < F u := lt_of_not_ge huT
      have huRange : F u - T ∈ Set.Icc (P.forwardPhaseLift 0)
          (P.forwardPhaseLift w) := by
        rw [P.forwardPhaseLift_zero]
        constructor
        · linarith
        · rw [hend] at hFu
          change F u - V.fundamentalPeriod P.hp ≤ P.forwardPhaseLift w
          have hupper := hFu.2
          linarith
      have hIV : Set.Icc (P.forwardPhaseLift 0)
          (P.forwardPhaseLift w) ⊆
          P.forwardPhaseLift '' Set.Icc 0 w :=
        intermediate_value_Icc (show (0 : I) ≤ w from w.property.1)
          (show ContinuousOn (fun q : I => P.forwardPhaseLift q)
            (Set.Icc 0 w) from P.forwardPhaseLift.continuous.continuousOn)
      obtain ⟨q, hqI, hq⟩ := hIV huRange
      refine ⟨q, Or.inr hqI, ?_⟩
      symm
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 1
      norm_num
      linarith
  · rintro ⟨q, hqI | hqI, rfl⟩
    · have htheta : P.forwardPhaseLift q ∈ Set.Icc (F 0) (F 1) := by
        rw [hF0, hend]
        constructor
        · exact P.forwardPhaseLift_strictMono.monotone hqI.1
        · have hqT : P.forwardPhaseLift q ≤ T := by
            simpa [T] using
              P.forwardPhaseLift_strictMono.monotone hqI.2
          linarith
      obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) (1 : I)
        F.continuous htheta
      refine ⟨u, ?_⟩
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 0
      simpa using hu
    · have htheta : P.forwardPhaseLift q + T ∈
          Set.Icc (F 0) (F 1) := by
        rw [hF0, hend]
        constructor
        · have hq0 : 0 ≤ P.forwardPhaseLift q := by
            rw [← P.forwardPhaseLift_zero]
            exact P.forwardPhaseLift_strictMono.monotone hqI.1
          linarith
        · simpa [T, add_comm] using add_le_add_right
            (P.forwardPhaseLift_strictMono.monotone hqI.2) T
      obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) (1 : I)
        F.continuous htheta
      refine ⟨u, ?_⟩
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 1
      simpa using hu


-- @@ L2864-2975 verbatim
/-- Backward wrap case: the endpoint lift is one period below the target
representative. -/
theorem range_eq_curve_image_wrap_of_forward_endpoint_sub_period
    (P : SimpleClosedOrbitParam X V) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (v w : I)
    (hw1 : w ≠ 1) (hsource : gamma 0 = P.curve v)
    (hend :
      P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource 1 =
        P.forwardPhaseLift w - V.fundamentalPeriod P.hp) :
    Set.range gamma =
      P.curve '' (Set.Icc w 1 ∪ Set.Icc 0 v) := by
  let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource
  let T := V.fundamentalPeriod P.hp
  have hT : 0 < T := V.fundamentalPeriod_pos P.hp
  have hF0 : F 0 = P.forwardPhaseLift v :=
    P.forwardPhaseLiftOfOrbitPathAtCurve_zero gamma hgamma v hsource
  have hwT : P.forwardPhaseLift w < T := by
    simpa [T] using P.forwardPhaseLift_strictMono
      (lt_of_le_of_ne w.property.2 hw1)
  have hv0 : 0 ≤ P.forwardPhaseLift v := by
    rw [← P.forwardPhaseLift_zero]
    exact P.forwardPhaseLift_strictMono.monotone v.property.1
  have hendsOrder : F 1 < F 0 := by
    rw [hF0, hend]
    linarith
  have hFanti : StrictAnti F := by
    rcases P.forwardPhaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
      gamma hgamma hgamma_inj v hsource with hmono | hanti
    · have hbad := hmono (show (0 : I) < 1 by norm_num)
      exact (not_lt_of_ge hendsOrder.le hbad).elim
    · exact hanti
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hFu : F u ∈ Set.Icc (F 1) (F 0) :=
      ⟨hFanti.antitone u.property.2,
        hFanti.antitone u.property.1⟩
    by_cases h0u : 0 ≤ F u
    · have huRange : F u ∈ Set.Icc (P.forwardPhaseLift 0)
          (P.forwardPhaseLift v) := by
        rw [P.forwardPhaseLift_zero]
        exact ⟨h0u, by simpa [hF0] using hFu.2⟩
      have hIV : Set.Icc (P.forwardPhaseLift 0)
          (P.forwardPhaseLift v) ⊆
          P.forwardPhaseLift '' Set.Icc 0 v :=
        intermediate_value_Icc (show (0 : I) ≤ v from v.property.1)
          (show ContinuousOn (fun q : I => P.forwardPhaseLift q)
            (Set.Icc 0 v) from P.forwardPhaseLift.continuous.continuousOn)
      obtain ⟨q, hqI, hq⟩ := hIV huRange
      refine ⟨q, Or.inr hqI, ?_⟩
      symm
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 0
      simpa using hq.symm
    · have hu0 : F u < 0 := lt_of_not_ge h0u
      have huRange : F u + T ∈ Set.Icc (P.forwardPhaseLift w)
          (P.forwardPhaseLift 1) := by
        rw [P.forwardPhaseLift_one]
        constructor
        · rw [hend] at hFu
          have hlower := hFu.1
          change P.forwardPhaseLift w ≤ F u +
            V.fundamentalPeriod P.hp
          linarith
        · linarith
      have hIV : Set.Icc (P.forwardPhaseLift w)
          (P.forwardPhaseLift 1) ⊆
          P.forwardPhaseLift '' Set.Icc w 1 :=
        intermediate_value_Icc (show w ≤ (1 : I) from w.property.2)
          (show ContinuousOn (fun q : I => P.forwardPhaseLift q)
            (Set.Icc w 1) from P.forwardPhaseLift.continuous.continuousOn)
      obtain ⟨q, hqI, hq⟩ := hIV huRange
      refine ⟨q, Or.inl hqI, ?_⟩
      symm
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource (-1)
      norm_num
      linarith
  · rintro ⟨q, hqI | hqI, rfl⟩
    · have htheta : P.forwardPhaseLift q - T ∈
          Set.Icc (F 1) (F 0) := by
        rw [hF0, hend]
        constructor
        · exact sub_le_sub_right
            (P.forwardPhaseLift_strictMono.monotone hqI.1) T
        · have hqT : P.forwardPhaseLift q ≤ T := by
            simpa [T] using
              P.forwardPhaseLift_strictMono.monotone hqI.2
          linarith
      obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) (0 : I)
        F.continuous htheta
      refine ⟨u, ?_⟩
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource (-1)
      norm_num
      linarith
    · have htheta : P.forwardPhaseLift q ∈
          Set.Icc (F 1) (F 0) := by
        rw [hF0, hend]
        constructor
        · have hq0 : 0 ≤ P.forwardPhaseLift q := by
            rw [← P.forwardPhaseLift_zero]
            exact P.forwardPhaseLift_strictMono.monotone hqI.1
          linarith
        · exact P.forwardPhaseLift_strictMono.monotone hqI.2
      obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) (0 : I)
        F.continuous htheta
      refine ⟨u, ?_⟩
      apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
        v q u hsource 0
      simpa using hu


-- @@ L2977-2983 verbatim
/-- Choose a preimage of an orbit point, normalising the duplicated terminal
parameter `1` to `0`. -/
noncomputable def normalizedCurvePreimage
    (P : SimpleClosedOrbitParam X V) (x : E)
    (hx : x ∈ V.orbit P.p) : I :=
  let u := (P.exists_curve_eq_of_mem_orbit hx).choose
  if u = 1 then 0 else u


-- @@ L2985-2994 verbatim
theorem curve_normalizedCurvePreimage
    (P : SimpleClosedOrbitParam X V) (x : E)
    (hx : x ∈ V.orbit P.p) :
    P.curve (P.normalizedCurvePreimage x hx) = x := by
  rw [normalizedCurvePreimage]
  split_ifs with hu
  · have hchosen := (P.exists_curve_eq_of_mem_orbit hx).choose_spec
    rw [hu] at hchosen
    exact P.curve_closed.trans hchosen
  · exact (P.exists_curve_eq_of_mem_orbit hx).choose_spec


-- @@ L2996-3003 verbatim
theorem normalizedCurvePreimage_ne_one
    (P : SimpleClosedOrbitParam X V) (x : E)
    (hx : x ∈ V.orbit P.p) :
    P.normalizedCurvePreimage x hx ≠ 1 := by
  rw [normalizedCurvePreimage]
  split_ifs with hu
  · exact zero_ne_one
  · exact hu


-- @@ L3005-3011 verbatim
/-- A finite family of distinct marked points on one intrinsic simple closed
orbit.  The number is written `k + 1` so adjacent linear subarcs are indexed
by `Fin k`. -/
structure CyclicMarking (P : SimpleClosedOrbitParam X V) (k : ℕ) where
  point : Fin (k + 1) → E
  point_injective : Injective point
  point_mem_orbit : ∀ i, point i ∈ V.orbit P.p


-- @@ L3013-3013 verbatim
namespace CyclicMarking


-- @@ L3015-3015 verbatim
variable {P : SimpleClosedOrbitParam X V} {k : ℕ}


-- @@ L3017-3019 verbatim
/-- The normalised parameter of a marked point. -/
noncomputable def mark (A : P.CyclicMarking k) (i : Fin (k + 1)) : I :=
  P.normalizedCurvePreimage (A.point i) (A.point_mem_orbit i)


-- @@ L3021-3023 verbatim
@[simp] theorem curve_mark (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    P.curve (A.mark i) = A.point i :=
  P.curve_normalizedCurvePreimage _ _


-- @@ L3025-3027 verbatim
theorem mark_ne_one (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    A.mark i ≠ 1 :=
  P.normalizedCurvePreimage_ne_one _ _


-- @@ L3029-3032 verbatim
theorem mark_injective (A : P.CyclicMarking k) : Injective A.mark := by
  intro i j hij
  apply A.point_injective
  rw [← A.curve_mark i, ← A.curve_mark j, hij]


-- @@ L3034-3109 verbatim
/-- No integral translate of any marked phase can lie strictly between the
endpoint lifts of an embedded arc whose interior avoids all marks. -/
theorem forwardMarkTranslate_not_between
    (A : P.CyclicMarking k) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (v : I) (hsource : gamma 0 = P.curve v)
    (havoid : ∀ {u : I}, u ∈ Set.Ioo 0 1 →
      ∀ i, gamma u ≠ A.point i)
    (i : Fin (k + 1)) (z : ℤ) :
    let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource
    let x := P.forwardPhaseLift (A.mark i) +
      z • V.fundamentalPeriod P.hp
    ¬(F 0 < x ∧ x < F 1) ∧ ¬(F 1 < x ∧ x < F 0) := by
  dsimp only
  let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma v hsource
  let x := P.forwardPhaseLift (A.mark i) +
    z • V.fundamentalPeriod P.hp
  constructor
  · rintro ⟨hx0, hx1⟩
    have hxmem : x ∈ Set.Icc (F 0) (F 1) := ⟨hx0.le, hx1.le⟩
    obtain ⟨u, hu⟩ := intermediate_value_univ (0 : I) (1 : I)
      F.continuous hxmem
    have hu_ne_zero : u ≠ 0 := by
      intro hu0
      rw [hu0] at hu
      linarith
    have hu_ne_one : u ≠ 1 := by
      intro hu1
      rw [hu1] at hu
      linarith
    have hu0 : (0 : ℝ) < (u : ℝ) := by
      refine lt_of_le_of_ne u.property.1 ?_
      intro heq
      apply hu_ne_zero
      apply Subtype.ext
      exact heq.symm
    have hu1 : (u : ℝ) < 1 := by
      refine lt_of_le_of_ne u.property.2 ?_
      intro heq
      apply hu_ne_one
      apply Subtype.ext
      exact heq
    apply havoid ⟨hu0, hu1⟩ i
    rw [← A.curve_mark i]
    apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
      v (A.mark i) u hsource z
    exact hu
  · rintro ⟨hx1, hx0⟩
    have hxmem : x ∈ Set.Icc (F 1) (F 0) := ⟨hx1.le, hx0.le⟩
    obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) (0 : I)
      F.continuous hxmem
    have hu_ne_zero : u ≠ 0 := by
      intro hu0
      rw [hu0] at hu
      linarith
    have hu_ne_one : u ≠ 1 := by
      intro hu1
      rw [hu1] at hu
      linarith
    have hu0 : (0 : ℝ) < (u : ℝ) := by
      refine lt_of_le_of_ne u.property.1 ?_
      intro heq
      apply hu_ne_zero
      apply Subtype.ext
      exact heq.symm
    have hu1 : (u : ℝ) < 1 := by
      refine lt_of_le_of_ne u.property.2 ?_
      intro heq
      apply hu_ne_one
      apply Subtype.ext
      exact heq
    apply havoid ⟨hu0, hu1⟩ i
    rw [← A.curve_mark i]
    apply P.eq_curve_of_forwardPhaseLift_eq_add_zsmul gamma hgamma
      v (A.mark i) u hsource z
    exact hu


-- @@ L3111-3179 verbatim
/-- An embedded mark-avoiding arc spans strictly less than one period in
either direction. -/
theorem forwardArc_endpoint_within_one_period
    (A : P.CyclicMarking k) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (i : Fin (k + 1))
    (hsource : gamma 0 = P.curve (A.mark i))
    (havoid : ∀ {u : I}, u ∈ Set.Ioo 0 1 →
      ∀ j, gamma u ≠ A.point j) :
    let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma
      (A.mark i) hsource
    (F 0 < F 1 → F 1 < F 0 + V.fundamentalPeriod P.hp) ∧
      (F 1 < F 0 → F 0 - V.fundamentalPeriod P.hp < F 1) := by
  dsimp only
  let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma
    (A.mark i) hsource
  have hT : 0 < V.fundamentalPeriod P.hp :=
    V.fundamentalPeriod_pos P.hp
  have hF0 : F 0 = P.forwardPhaseLift (A.mark i) := by
    exact P.forwardPhaseLiftOfOrbitPathAtCurve_zero gamma hgamma
      (A.mark i) hsource
  constructor
  · intro hinc
    have hle : F 1 ≤ F 0 + V.fundamentalPeriod P.hp := by
      by_contra hnot
      have hgt : F 0 + V.fundamentalPeriod P.hp < F 1 :=
        lt_of_not_ge hnot
      have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
        (A.mark i) hsource havoid i 1
      apply hbarrier.1
      constructor
      · rw [hF0]
        simpa using hT
      · simpa [hF0] using hgt
    have hne : F 1 ≠ F 0 + V.fundamentalPeriod P.hp := by
      intro heq
      have hpoint := P.eq_curve_of_forwardPhaseLift_eq_add_zsmul
        gamma hgamma (A.mark i) (A.mark i) 1 hsource 1 (by
          simpa [F, hF0] using heq)
      have hends : gamma 1 = gamma 0 := hpoint.trans hsource.symm
      have honezero : (1 : I) = 0 := hgamma_inj hends
      norm_num at honezero
    exact lt_of_le_of_ne hle hne
  · intro hdec
    have hle : F 0 - V.fundamentalPeriod P.hp ≤ F 1 := by
      by_contra hnot
      have hlt : F 1 < F 0 - V.fundamentalPeriod P.hp :=
        lt_of_not_ge hnot
      have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
        (A.mark i) hsource havoid i (-1)
      apply hbarrier.2
      constructor
      · norm_num at ⊢
        rw [← hF0]
        linarith
      · rw [hF0]
        norm_num
        linarith
    have hne : F 0 - V.fundamentalPeriod P.hp ≠ F 1 := by
      intro heq
      have hpoint := P.eq_curve_of_forwardPhaseLift_eq_add_zsmul
        gamma hgamma (A.mark i) (A.mark i) 1 hsource (-1) (by
          rw [hF0] at heq
          norm_num at ⊢
          linarith)
      have hends : gamma 1 = gamma 0 := hpoint.trans hsource.symm
      have honezero : (1 : I) = 0 := hgamma_inj hends
      norm_num at honezero
    exact lt_of_le_of_ne hle hne


-- @@ L3181-3184 verbatim
/-- Permutation which lists the marked labels in increasing parameter order. -/
noncomputable def sortedLabel (A : P.CyclicMarking k) :
    Equiv.Perm (Fin (k + 1)) :=
  Tuple.sort A.mark


-- @@ L3186-3189 verbatim
/-- Increasing tuple of marked parameters. -/
noncomputable def sortedMark (A : P.CyclicMarking k) :
    Fin (k + 1) → I :=
  A.mark ∘ A.sortedLabel


-- @@ L3191-3194 verbatim
theorem sortedMark_strictMono (A : P.CyclicMarking k) :
    StrictMono A.sortedMark := by
  exact (Tuple.monotone_sort A.mark).strictMono_of_injective
    (A.mark_injective.comp A.sortedLabel.injective)


-- @@ L3196-3199 verbatim
/-- Mark coordinates in the uniformly forward real lift. -/
noncomputable def forwardSortedMark
    (A : P.CyclicMarking k) (i : Fin (k + 1)) : ℝ :=
  P.forwardPhaseLift (A.sortedMark i)


-- @@ L3201-3204 verbatim
@[simp] theorem forwardPhaseLift_mark_sortedLabel
    (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    P.forwardPhaseLift (A.mark (A.sortedLabel i)) =
      A.forwardSortedMark i := rfl


-- @@ L3206-3208 verbatim
theorem forwardSortedMark_strictMono (A : P.CyclicMarking k) :
    StrictMono A.forwardSortedMark :=
  P.forwardPhaseLift_strictMono.comp A.sortedMark_strictMono


-- @@ L3210-3215 verbatim
theorem forwardSortedMark_nonneg
    (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    0 ≤ A.forwardSortedMark i := by
  rw [forwardSortedMark, ← P.forwardPhaseLift_zero]
  exact P.forwardPhaseLift_strictMono.monotone
    (A.sortedMark i).property.1


-- @@ L3217-3224 verbatim
theorem forwardSortedMark_lt_period
    (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    A.forwardSortedMark i < V.fundamentalPeriod P.hp := by
  rw [forwardSortedMark, ← P.forwardPhaseLift_one]
  apply P.forwardPhaseLift_strictMono
  have hne : A.sortedMark i ≠ 1 := by
    exact A.mark_ne_one (A.sortedLabel i)
  exact lt_of_le_of_ne (A.sortedMark i).property.2 hne


-- @@ L3226-3234 verbatim
/-- Two labels are adjacent in the cyclic order determined by the sorted
marks: either linearly consecutive, or the largest and smallest marks. -/
def CyclicAdjacent (A : P.CyclicMarking k)
    (i j : Fin (k + 1)) : Prop :=
  (∃ r : Fin k,
    (i = A.sortedLabel r.castSucc ∧ j = A.sortedLabel r.succ) ∨
      (j = A.sortedLabel r.castSucc ∧ i = A.sortedLabel r.succ)) ∨
  (i = A.sortedLabel (Fin.last k) ∧ j = A.sortedLabel 0) ∨
  (j = A.sortedLabel (Fin.last k) ∧ i = A.sortedLabel 0)


-- @@ L3236-3526 verbatim
/-- An embedded arc on a four-marked simple orbit whose interior meets no
mark must join cyclically adjacent marks. -/
theorem cyclicAdjacent_of_embedded_arc_four
    (A : P.CyclicMarking 3) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (i j : Fin 4)
    (hsource : gamma 0 = A.point i)
    (htarget : gamma 1 = A.point j)
    (havoid : ∀ {u : I}, u ∈ Set.Ioo 0 1 →
      ∀ l, gamma u ≠ A.point l) :
    A.CyclicAdjacent i j := by
  let r : Fin 4 := A.sortedLabel.symm i
  let s : Fin 4 := A.sortedLabel.symm j
  let x : ℝ := A.forwardSortedMark r
  let y : ℝ := A.forwardSortedMark s
  let T : ℝ := V.fundamentalPeriod P.hp
  have hT : 0 < T := V.fundamentalPeriod_pos P.hp
  have hmarkr : A.sortedMark r = A.mark i := by
    simp [r, sortedMark]
  have hmarks : A.sortedMark s = A.mark j := by
    simp [s, sortedMark]
  have hsource' : gamma 0 = P.curve (A.mark i) :=
    hsource.trans (A.curve_mark i).symm
  have htarget' : gamma 1 = P.curve (A.mark j) :=
    htarget.trans (A.curve_mark j).symm
  let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma
    (A.mark i) hsource'
  have hF0 : F 0 = x := by
    calc
      F 0 = P.forwardPhaseLift (A.mark i) :=
        P.forwardPhaseLiftOfOrbitPathAtCurve_zero gamma hgamma
          (A.mark i) hsource'
      _ = P.forwardPhaseLift (A.sortedMark r) := by rw [hmarkr]
      _ = x := rfl
  obtain ⟨z, hz⟩ := P.forwardPhaseLift_target_eq_add_zsmul
    gamma hgamma (A.mark i) (A.mark j) hsource' htarget'
  have hyz : y = F 1 + (z : ℝ) * T := by
    calc
      y = P.forwardPhaseLift (A.sortedMark s) := rfl
      _ = P.forwardPhaseLift (A.mark j) := by rw [hmarks]
      _ = F 1 + (z : ℝ) * T := by
        simpa [F, T, zsmul_eq_mul] using hz
  have hF1 : F 1 = y - (z : ℝ) * T := by linarith
  have hx0 : 0 ≤ x := A.forwardSortedMark_nonneg r
  have hxT : x < T := A.forwardSortedMark_lt_period r
  have hy0 : 0 ≤ y := A.forwardSortedMark_nonneg s
  have hyT : y < T := A.forwardSortedMark_lt_period s
  have hspan := A.forwardArc_endpoint_within_one_period gamma hgamma
    hgamma_inj i hsource' havoid
  have hmonoanti :=
    P.forwardPhaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
      gamma hgamma hgamma_inj (A.mark i) hsource'
  rcases hmonoanti with hmono | hanti
  · have hFinc : F 0 < F 1 := hmono (show (0 : I) < 1 by norm_num)
    have hFhi : F 1 < F 0 + T := hspan.1 hFinc
    have hnormal := int_translate_forward_normal_form hT hx0 hxT hy0 hyT
      z (by simpa [hF0, hF1] using hFinc)
      (by simpa [hF0, hF1] using hFhi)
    rcases hnormal with ⟨hz0, hxy⟩ | ⟨hzm1, hyx⟩
    · subst z
      have hrs : r < s := A.forwardSortedMark_strictMono.lt_iff_lt.mp hxy
      have hsuc : s.val = r.val + 1 := by
        by_contra hne
        have hgap : r.val + 1 < s.val := by
          change r.val < s.val at hrs
          omega
        let l : Fin 4 := ⟨r.val + 1, by omega⟩
        have hrl : r < l := by
          change r.val < r.val + 1
          omega
        have hls : l < s := by
          change r.val + 1 < s.val
          exact hgap
        have hxl : x < A.forwardSortedMark l :=
          A.forwardSortedMark_strictMono hrl
        have hly : A.forwardSortedMark l < y :=
          A.forwardSortedMark_strictMono hls
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 0
        apply hbarrier.1
        constructor
        · have h : F 0 < A.forwardSortedMark l := by
            rw [hF0]
            exact hxl
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
        · have h : A.forwardSortedMark l < F 1 := by
            rw [hF1]
            norm_num
            exact hly
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
      left
      let q : Fin 3 := ⟨r.val, by
        change r.val < s.val at hrs
        omega⟩
      refine ⟨q, Or.inl ⟨?_, ?_⟩⟩
      · calc
          i = A.sortedLabel r := by simp [r]
          _ = A.sortedLabel q.castSucc := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            rfl
      · calc
          j = A.sortedLabel s := by simp [s]
          _ = A.sortedLabel q.succ := by
            congr 1
            apply Fin.ext
            exact hsuc
    · subst z
      have hyr : s < r := A.forwardSortedMark_strictMono.lt_iff_lt.mp hyx
      have hrLast : r.val = 3 := by
        by_contra hne
        have hrlt : r.val < 3 := by omega
        let l : Fin 4 := ⟨r.val + 1, by omega⟩
        have hrl : r < l := by
          change r.val < r.val + 1
          omega
        have hxl : x < A.forwardSortedMark l :=
          A.forwardSortedMark_strictMono hrl
        have hlT : A.forwardSortedMark l < T :=
          A.forwardSortedMark_lt_period l
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 0
        apply hbarrier.1
        constructor
        · have h : F 0 < A.forwardSortedMark l := by
            rw [hF0]
            exact hxl
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
        · rw [hF1]
          norm_num
          linarith
      have hsZero : s.val = 0 := by
        by_contra hne
        have hspos : 0 < s.val := by omega
        let l : Fin 4 := 0
        have hls : l < s := by
          change 0 < s.val
          exact hspos
        have h0y : A.forwardSortedMark l < y :=
          A.forwardSortedMark_strictMono hls
        have hxT' : x < A.forwardSortedMark l + T := by
          have hl0 := A.forwardSortedMark_nonneg l
          linarith
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 1
        apply hbarrier.1
        constructor
        · have h : F 0 < A.forwardSortedMark l + T := by
            rw [hF0]
            exact hxT'
          simpa only [F, T, one_zsmul,
            forwardPhaseLift_mark_sortedLabel] using h
        · rw [hF1]
          norm_num
          linarith
      right
      left
      constructor
      · calc
          i = A.sortedLabel r := by simp [r]
          _ = A.sortedLabel (Fin.last 3) := by
            congr 1
            apply Fin.ext
            exact hrLast
      · calc
          j = A.sortedLabel s := by simp [s]
          _ = A.sortedLabel 0 := by
            congr 1
            apply Fin.ext
            exact hsZero
  · have hFdec : F 1 < F 0 := hanti (show (0 : I) < 1 by norm_num)
    have hFlo : F 0 - T < F 1 := hspan.2 hFdec
    have hnormal := int_translate_backward_normal_form hT hx0 hxT hy0 hyT
      z (by simpa [hF0, hF1] using hFlo)
      (by simpa [hF0, hF1] using hFdec)
    rcases hnormal with ⟨hz0, hyx⟩ | ⟨hz1, hxy⟩
    · subst z
      have hsr : s < r := A.forwardSortedMark_strictMono.lt_iff_lt.mp hyx
      have hsuc : r.val = s.val + 1 := by
        by_contra hne
        have hgap : s.val + 1 < r.val := by
          change s.val < r.val at hsr
          omega
        let l : Fin 4 := ⟨s.val + 1, by omega⟩
        have hsl : s < l := by
          change s.val < s.val + 1
          omega
        have hlr : l < r := by
          change s.val + 1 < r.val
          exact hgap
        have hyl : y < A.forwardSortedMark l :=
          A.forwardSortedMark_strictMono hsl
        have hlx : A.forwardSortedMark l < x :=
          A.forwardSortedMark_strictMono hlr
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 0
        apply hbarrier.2
        constructor
        · have h : F 1 < A.forwardSortedMark l := by
            rw [hF1]
            norm_num
            exact hyl
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
        · have h : A.forwardSortedMark l < F 0 := by
            rw [hF0]
            exact hlx
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
      left
      let q : Fin 3 := ⟨s.val, by
        change s.val < r.val at hsr
        omega⟩
      refine ⟨q, Or.inr ⟨?_, ?_⟩⟩
      · calc
          j = A.sortedLabel s := by simp [s]
          _ = A.sortedLabel q.castSucc := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            rfl
      · calc
          i = A.sortedLabel r := by simp [r]
          _ = A.sortedLabel q.succ := by
            congr 1
            apply Fin.ext
            exact hsuc
    · subst z
      have hrs : r < s := A.forwardSortedMark_strictMono.lt_iff_lt.mp hxy
      have hrZero : r.val = 0 := by
        by_contra hne
        have hrpos : 0 < r.val := by omega
        let l : Fin 4 := ⟨r.val - 1, by omega⟩
        have hlr : l < r := by
          change r.val - 1 < r.val
          omega
        have hlx : A.forwardSortedMark l < x :=
          A.forwardSortedMark_strictMono hlr
        have hl0 : 0 ≤ A.forwardSortedMark l :=
          A.forwardSortedMark_nonneg l
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 0
        apply hbarrier.2
        constructor
        · rw [hF1]
          norm_num
          linarith
        · have h : A.forwardSortedMark l < F 0 := by
            rw [hF0]
            exact hlx
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
      have hsLast : s.val = 3 := by
        by_contra hne
        have hslt : s.val < 3 := by omega
        let l : Fin 4 := Fin.last 3
        have hsl : s < l := by
          change s.val < 3
          exact hslt
        have hyl : y < A.forwardSortedMark l :=
          A.forwardSortedMark_strictMono hsl
        have hlT : A.forwardSortedMark l < T :=
          A.forwardSortedMark_lt_period l
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) (-1)
        apply hbarrier.2
        constructor
        · rw [hF1]
          norm_num
          linarith
        · rw [hF0]
          norm_num
          have hx0' := hx0
          linarith
      right
      right
      constructor
      · calc
          j = A.sortedLabel s := by simp [s]
          _ = A.sortedLabel (Fin.last 3) := by
            congr 1
            apply Fin.ext
            exact hsLast
      · calc
          i = A.sortedLabel r := by simp [r]
          _ = A.sortedLabel 0 := by
            congr 1
            apply Fin.ext
            exact hrZero


-- @@ L3528-3533 verbatim
/-- Regard the closed orbit parameter as a path before taking subpaths. -/
def curvePath (P : SimpleClosedOrbitParam X V) :
    Path (P.curve 0) (P.curve 1) where
  toContinuousMap := P.curve
  source' := rfl
  target' := rfl


-- @@ L3535-3541 verbatim
/-- The subarc between two consecutive marks in the linear ordering. -/
noncomputable def adjacentSubpath (A : P.CyclicMarking k) (i : Fin k) :
    Path (A.point (A.sortedLabel i.castSucc))
      (A.point (A.sortedLabel i.succ)) :=
  ((curvePath P).subpath (A.sortedMark i.castSucc) (A.sortedMark i.succ)).cast
    (A.curve_mark (A.sortedLabel i.castSucc)).symm
    (A.curve_mark (A.sortedLabel i.succ)).symm


-- @@ L3543-3552 verbatim
theorem range_adjacentSubpath
    (A : P.CyclicMarking k) (i : Fin k) :
    Set.range (A.adjacentSubpath i) =
      (curvePath P) '' Set.Icc (A.sortedMark i.castSucc)
        (A.sortedMark i.succ) := by
  rw [adjacentSubpath]
  simpa only [Path.cast_coe] using
    Path.range_subpath_of_le (curvePath P)
      (A.sortedMark i.castSucc) (A.sortedMark i.succ)
      (A.sortedMark_strictMono Fin.castSucc_lt_succ).le


-- @@ L3554-3562 verbatim
/-- Concatenate all linearly adjacent marked subpaths, retaining their common
parametrization by the original orbit curve.  Its endpoints are left in
`P.curve` form so `Path.Homotopy.concatSubpath` applies definitionally. -/
noncomputable def linearMarkedConcat (A : P.CyclicMarking k) :
    Path (P.curve (A.sortedMark 0))
      (P.curve (A.sortedMark (Fin.last k))) :=
  Path.concat (P.curve ∘ A.sortedMark)
    (fun i => (curvePath P).subpath
      (A.sortedMark i.castSucc) (A.sortedMark i.succ))


-- @@ L3564-3570 verbatim
/-- The concatenation of all adjacent cuts reconstructs the subpath from the
smallest to the largest marked parameter. -/
noncomputable def linearMarkedConcatHomotopy (A : P.CyclicMarking k) :
    Path.Homotopy A.linearMarkedConcat
      ((curvePath P).subpath (A.sortedMark 0)
        (A.sortedMark (Fin.last k))) :=
  Path.Homotopy.concatSubpath (curvePath P) A.sortedMark


-- @@ L3572-3575 verbatim
/-- Initial piece of the orbit before the smallest marked parameter. -/
noncomputable def curveCutPrefix (A : P.CyclicMarking k) :
    Path (P.curve 0) (P.curve (A.sortedMark 0)) :=
  (curvePath P).subpath 0 (A.sortedMark 0)


-- @@ L3577-3580 verbatim
/-- Final piece of the orbit after the largest marked parameter. -/
noncomputable def curveCutSuffix (A : P.CyclicMarking k) :
    Path (P.curve (A.sortedMark (Fin.last k))) (P.curve 1) :=
  (curvePath P).subpath (A.sortedMark (Fin.last k)) 1


-- @@ L3582-3587 verbatim
/-- Wrap-around piece, joining the largest mark back to the smallest through
the identified terminal and initial parameters of the closed curve. -/
noncomputable def curveCutWrap (A : P.CyclicMarking k) :
    Path (P.curve (A.sortedMark (Fin.last k)))
      (P.curve (A.sortedMark 0)) :=
  (A.curveCutSuffix.cast rfl P.curve_closed).trans A.curveCutPrefix


-- @@ L3589-3593 verbatim
/-- All adjacent marked pieces followed by the wrap piece, based at the
smallest marked point. -/
noncomputable def cyclicMarkedConcat (A : P.CyclicMarking k) :
    Path (P.curve (A.sortedMark 0)) (P.curve (A.sortedMark 0)) :=
  A.linearMarkedConcat.trans A.curveCutWrap


-- @@ L3595-3599 verbatim
/-- The corresponding cyclic rotation of the original curve. -/
noncomputable def rotatedCurvePath (A : P.CyclicMarking k) :
    Path (P.curve (A.sortedMark 0)) (P.curve (A.sortedMark 0)) :=
  ((curvePath P).subpath (A.sortedMark 0)
    (A.sortedMark (Fin.last k))).trans A.curveCutWrap


-- @@ L3601-3605 verbatim
/-- Adjacent pieces plus the wrap reconstruct the same based, rotated loop. -/
noncomputable def cyclicMarkedConcatHomotopy (A : P.CyclicMarking k) :
    Path.Homotopy A.cyclicMarkedConcat A.rotatedCurvePath :=
  A.linearMarkedConcatHomotopy.hcomp
    (Path.Homotopy.refl A.curveCutWrap)


-- @@ L3607-3612 verbatim
/-- The full orbit cut at all marked parameters: prefix, all adjacent marked
pieces, and suffix.  Keeping this path (rather than only the existence of its
pieces) lets later frame-splicing arguments reuse the same circle cut. -/
noncomputable def curveCutDecomposition (A : P.CyclicMarking k) :
    Path (P.curve 0) (P.curve 1) :=
  (A.curveCutPrefix.trans A.linearMarkedConcat).trans A.curveCutSuffix


-- @@ L3614-3626 verbatim
/-- Strong reconstruction witness for the cut curve. -/
noncomputable def curveCutDecompositionHomotopy (A : P.CyclicMarking k) :
    Path.Homotopy A.curveCutDecomposition
      ((curvePath P).subpath 0 1) :=
  let gamma := curvePath P
  (((Path.Homotopy.refl A.curveCutPrefix).hcomp
      A.linearMarkedConcatHomotopy).hcomp
        (Path.Homotopy.refl A.curveCutSuffix)).trans
    (((Path.Homotopy.subpathTransSubpath gamma 0
      (A.sortedMark 0) (A.sortedMark (Fin.last k))).hcomp
        (Path.Homotopy.refl A.curveCutSuffix)).trans
      (Path.Homotopy.subpathTransSubpath gamma 0
        (A.sortedMark (Fin.last k)) 1))


-- @@ L3628-3637 verbatim
/-- Consequently the explicit cut-and-concatenate path is homotopic, relative
to endpoints, to the original once-around orbit curve. -/
theorem curveCutDecomposition_homotopic_curvePath
    (A : P.CyclicMarking k) :
    Path.Homotopic A.curveCutDecomposition (curvePath P) := by
  have hfull : (curvePath P).subpath 0 1 = curvePath P := by
    ext u
    simp [Path.subpath]
    rfl
  exact ⟨A.curveCutDecompositionHomotopy.cast rfl hfull⟩


-- @@ L3639-3705 verbatim
/-- No third marked point occurs on an adjacent linear subarc.  This is the
finite-order fact needed to recognize an exterior arc after proving that all
entries into the local chart cross one of the marked ends. -/
theorem point_mem_range_adjacentSubpath
    (A : P.CyclicMarking k) (i : Fin k) (j : Fin (k + 1))
    (hj : A.point j ∈ Set.range (A.adjacentSubpath i)) :
    j = A.sortedLabel i.castSucc ∨ j = A.sortedLabel i.succ := by
  have hmono := A.sortedMark_strictMono
  have hle : A.sortedMark i.castSucc ≤ A.sortedMark i.succ :=
    (hmono Fin.castSucc_lt_succ).le
  have hj' : A.point j ∈
      Set.range ((curvePath P).subpath
        (A.sortedMark i.castSucc) (A.sortedMark i.succ)) := by
    simpa [adjacentSubpath] using hj
  rw [Path.range_subpath_of_le _ _ _ hle] at hj'
  obtain ⟨s, hs, hsj⟩ := hj'
  change P.curve s = A.point j at hsj
  rw [← A.curve_mark j] at hsj
  rcases P.curve_eq_cases hsj with hsame | hends | hends
  · let r : Fin (k + 1) := A.sortedLabel.symm j
    have hmarkr : A.sortedMark r = A.mark j := by
      simp [r, sortedMark]
    have hlo : A.sortedMark i.castSucc ≤ A.sortedMark r := by
      rw [hmarkr, ← hsame]
      exact hs.1
    have hhi : A.sortedMark r ≤ A.sortedMark i.succ := by
      rw [hmarkr, ← hsame]
      exact hs.2
    have hrlo : i.castSucc ≤ r := hmono.le_iff_le.mp hlo
    have hrhi : r ≤ i.succ := hmono.le_iff_le.mp hhi
    have hr : r = i.castSucc ∨ r = i.succ := by
      change i.val ≤ r.val at hrlo
      change r.val ≤ i.val + 1 at hrhi
      have hval : r.val = i.val ∨ r.val = i.val + 1 := by omega
      rcases hval with hval | hval
      · left
        apply Fin.ext
        simpa using hval
      · right
        apply Fin.ext
        simpa using hval
    rcases hr with hr | hr
    · left
      calc
        j = A.sortedLabel r := by simp [r]
        _ = A.sortedLabel i.castSucc := by rw [hr]
    · right
      calc
        j = A.sortedLabel r := by simp [r]
        _ = A.sortedLabel i.succ := by rw [hr]
  · exact (A.mark_ne_one j hends.2).elim
  · have hupperNe : A.sortedMark i.succ ≠ 1 := by
      exact A.mark_ne_one (A.sortedLabel i.succ)
    have hupperLt : (A.sortedMark i.succ : ℝ) < 1 := by
      have hupperLe : (A.sortedMark i.succ : ℝ) ≤ 1 :=
        (A.sortedMark i.succ).property.2
      have hupperNeReal : (A.sortedMark i.succ : ℝ) ≠ 1 := by
        intro h
        apply hupperNe
        apply Subtype.ext
        exact h
      exact lt_of_le_of_ne hupperLe hupperNeReal
    have hsle : (s : ℝ) ≤ A.sortedMark i.succ := hs.2
    rw [hends.1] at hsle
    have hsle' : (1 : ℝ) ≤ A.sortedMark i.succ := by
      simpa using hsle
    linarith


-- @@ L3707-3714 verbatim
/-- The cyclic subarc from the largest mark through the identified endpoint
`1 = 0` to the smallest mark. -/
noncomputable def wrapSubpath (A : P.CyclicMarking k) :
    Path (A.point (A.sortedLabel (Fin.last k)))
      (A.point (A.sortedLabel 0)) :=
  A.curveCutWrap.cast
    (A.curve_mark (A.sortedLabel (Fin.last k))).symm
    (A.curve_mark (A.sortedLabel 0)).symm


-- @@ L3716-3729 verbatim
theorem range_wrapSubpath (A : P.CyclicMarking k) :
    Set.range A.wrapSubpath =
      (curvePath P) '' (Set.Icc (A.sortedMark (Fin.last k)) 1 ∪
        Set.Icc 0 (A.sortedMark 0)) := by
  rw [wrapSubpath]
  simp only [Path.cast_coe, curveCutWrap, Path.trans_range,
    curveCutSuffix, curveCutPrefix]
  have hsuffix := Path.range_subpath_of_le (curvePath P)
    (A.sortedMark (Fin.last k)) 1
    (A.sortedMark (Fin.last k)).property.2
  have hprefix := Path.range_subpath_of_le (curvePath P)
    0 (A.sortedMark 0) (A.sortedMark 0).property.1
  rw [Set.image_union]
  exact congrArg₂ (· ∪ ·) hsuffix hprefix


-- @@ L3731-3741 verbatim
/-- Every point of a linear cyclic cut remains on the parametrized intrinsic
orbit. -/
theorem adjacentSubpath_mem_orbit
    (A : P.CyclicMarking k) (i : Fin k) (u : I) :
    A.adjacentSubpath i u ∈ V.orbit P.p := by
  have hu : A.adjacentSubpath i u ∈
      Set.range (A.adjacentSubpath i) := ⟨u, rfl⟩
  rw [A.range_adjacentSubpath i] at hu
  obtain ⟨s, -, hs⟩ := hu
  rw [← hs]
  exact P.curve_mem_orbit s


-- @@ L3743-3752 verbatim
/-- Every point of the wrap cyclic cut remains on the same intrinsic
orbit. -/
theorem wrapSubpath_mem_orbit
    (A : P.CyclicMarking k) (u : I) :
    A.wrapSubpath u ∈ V.orbit P.p := by
  have hu : A.wrapSubpath u ∈ Set.range A.wrapSubpath := ⟨u, rfl⟩
  rw [A.range_wrapSubpath] at hu
  obtain ⟨s, -, hs⟩ := hu
  rw [← hs]
  exact P.curve_mem_orbit s


-- @@ L3754-3929 verbatim
/-- For a two-marked orbit, every embedded arc with those endpoints and no
interior marked re-entry is exactly one of the two cyclic cuts. -/
theorem range_eq_adjacentSubpath_or_wrap_of_embedded_arc_two
    (A : P.CyclicMarking 1) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (i j : Fin 2)
    (hsource : gamma 0 = A.point i)
    (htarget : gamma 1 = A.point j)
    (havoid : ∀ {u : I}, u ∈ Set.Ioo 0 1 →
      ∀ l, gamma u ≠ A.point l) :
    Set.range gamma = Set.range (A.adjacentSubpath 0) ∨
      Set.range gamma = Set.range A.wrapSubpath := by
  let r : Fin 2 := A.sortedLabel.symm i
  let s : Fin 2 := A.sortedLabel.symm j
  let x : ℝ := A.forwardSortedMark r
  let y : ℝ := A.forwardSortedMark s
  let T : ℝ := V.fundamentalPeriod P.hp
  have hT : 0 < T := V.fundamentalPeriod_pos P.hp
  have hmarkr : A.sortedMark r = A.mark i := by
    simp [r, sortedMark]
  have hmarks : A.sortedMark s = A.mark j := by
    simp [s, sortedMark]
  have hsource' : gamma 0 = P.curve (A.mark i) :=
    hsource.trans (A.curve_mark i).symm
  have htarget' : gamma 1 = P.curve (A.mark j) :=
    htarget.trans (A.curve_mark j).symm
  let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma
    (A.mark i) hsource'
  have hF0 : F 0 = x := by
    calc
      F 0 = P.forwardPhaseLift (A.mark i) :=
        P.forwardPhaseLiftOfOrbitPathAtCurve_zero gamma hgamma
          (A.mark i) hsource'
      _ = P.forwardPhaseLift (A.sortedMark r) := by rw [hmarkr]
      _ = x := rfl
  obtain ⟨z, hz⟩ := P.forwardPhaseLift_target_eq_add_zsmul
    gamma hgamma (A.mark i) (A.mark j) hsource' htarget'
  have hyz : y = F 1 + (z : ℝ) * T := by
    calc
      y = P.forwardPhaseLift (A.sortedMark s) := rfl
      _ = P.forwardPhaseLift (A.mark j) := by rw [hmarks]
      _ = F 1 + (z : ℝ) * T := by
        simpa [F, T, zsmul_eq_mul] using hz
  have hy : y = P.forwardPhaseLift (A.mark j) := by
    calc
      y = P.forwardPhaseLift (A.sortedMark s) := rfl
      _ = P.forwardPhaseLift (A.mark j) := by rw [hmarks]
  have hF1 : F 1 = y - (z : ℝ) * T := by linarith
  have hx0 : 0 ≤ x := A.forwardSortedMark_nonneg r
  have hxT : x < T := A.forwardSortedMark_lt_period r
  have hy0 : 0 ≤ y := A.forwardSortedMark_nonneg s
  have hyT : y < T := A.forwardSortedMark_lt_period s
  have hspan := A.forwardArc_endpoint_within_one_period gamma hgamma
    hgamma_inj i hsource' havoid
  have hmonoanti :=
    P.forwardPhaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
      gamma hgamma hgamma_inj (A.mark i) hsource'
  have finishDirect (horder : r < s ∨ s < r)
      (hend0 : F 1 = P.forwardPhaseLift (A.mark j)) :
      Set.range gamma = Set.range (A.adjacentSubpath 0) := by
    have hmarksNe : A.mark i ≠ A.mark j := by
      intro heq
      have heqrs : r = s := by
        apply A.sortedMark_strictMono.injective
        rw [hmarkr, hmarks, heq]
      rcases horder with hrs | hsr
      · exact (ne_of_lt hrs) heqrs
      · exact (ne_of_gt hsr) heqrs
    have hrange := P.range_eq_curve_image_uIcc_of_forward_endpoint
      gamma hgamma hgamma_inj (A.mark i) (A.mark j) hmarksNe hsource'
      hend0
    have hr0s1 : (r = 0 ∧ s = 1) ∨ (s = 0 ∧ r = 1) := by
      rcases horder with hrs | hsr
      · left
        constructor <;> apply Fin.ext <;> omega
      · right
        constructor <;> apply Fin.ext <;> omega
    have hinterval : Set.uIcc (A.mark i) (A.mark j) =
        Set.Icc (A.sortedMark 0) (A.sortedMark 1) := by
      rcases hr0s1 with ⟨hr0, hs1⟩ | ⟨hs0, hr1⟩
      · rw [← hmarkr, ← hmarks, hr0, hs1,
          Set.uIcc_of_le (A.sortedMark_strictMono (by norm_num)).le]
      · rw [← hmarkr, ← hmarks, hs0, hr1,
          Set.uIcc_of_ge (A.sortedMark_strictMono (by norm_num)).le]
    calc
      Set.range gamma = P.curve '' Set.uIcc (A.mark i) (A.mark j) :=
        hrange
      _ = (curvePath P) '' Set.Icc (A.sortedMark 0)
          (A.sortedMark 1) := by rw [hinterval]; rfl
      _ = Set.range (A.adjacentSubpath 0) :=
        (A.range_adjacentSubpath 0).symm
  rcases hmonoanti with hmono | hanti
  · have hFinc : F 0 < F 1 := hmono (show (0 : I) < 1 by norm_num)
    have hFhi : F 1 < F 0 + T := hspan.1 hFinc
    rcases int_translate_forward_normal_form hT hx0 hxT hy0 hyT z
      (by simpa [hF0, hF1] using hFinc)
      (by simpa [hF0, hF1] using hFhi) with
      ⟨hz0, hxy⟩ | ⟨hzm1, hyx⟩
    · left
      subst z
      apply finishDirect (Or.inl
        (A.forwardSortedMark_strictMono.lt_iff_lt.mp hxy))
      rw [hF1, hy]
      norm_num
    · right
      subst z
      have hsr : s < r :=
        A.forwardSortedMark_strictMono.lt_iff_lt.mp hyx
      have hr1 : r = 1 := by
        apply Fin.ext
        change r.val = 1
        change s.val < r.val at hsr
        omega
      have hs0 : s = 0 := by
        apply Fin.ext
        change s.val = 0
        change s.val < r.val at hsr
        omega
      have hv1 : A.mark i ≠ 1 := A.mark_ne_one i
      have hrange :=
        P.range_eq_curve_image_wrap_of_forward_endpoint_add_period
          gamma hgamma hgamma_inj (A.mark i) (A.mark j) hv1 hsource' (by
            rw [hF1, hy]
            norm_num
            rfl)
      calc
        Set.range gamma = P.curve ''
            (Set.Icc (A.mark i) 1 ∪ Set.Icc 0 (A.mark j)) := hrange
        _ = (curvePath P) ''
            (Set.Icc (A.sortedMark 1) 1 ∪
              Set.Icc 0 (A.sortedMark 0)) := by
          rw [← hmarkr, ← hmarks, hr1, hs0]
          rfl
        _ = Set.range A.wrapSubpath := A.range_wrapSubpath.symm
  · have hFdec : F 1 < F 0 := hanti (show (0 : I) < 1 by norm_num)
    have hFlo : F 0 - T < F 1 := hspan.2 hFdec
    rcases int_translate_backward_normal_form hT hx0 hxT hy0 hyT z
      (by simpa [hF0, hF1] using hFlo)
      (by simpa [hF0, hF1] using hFdec) with
      ⟨hz0, hyx⟩ | ⟨hz1, hxy⟩
    · left
      subst z
      apply finishDirect (Or.inr
        (A.forwardSortedMark_strictMono.lt_iff_lt.mp hyx))
      rw [hF1, hy]
      norm_num
    · right
      subst z
      have hrs : r < s :=
        A.forwardSortedMark_strictMono.lt_iff_lt.mp hxy
      have hr0 : r = 0 := by
        apply Fin.ext
        change r.val = 0
        change r.val < s.val at hrs
        omega
      have hs1 : s = 1 := by
        apply Fin.ext
        change s.val = 1
        change r.val < s.val at hrs
        omega
      have hw1 : A.mark j ≠ 1 := A.mark_ne_one j
      have hrange :=
        P.range_eq_curve_image_wrap_of_forward_endpoint_sub_period
          gamma hgamma hgamma_inj (A.mark i) (A.mark j) hw1 hsource' (by
            rw [hF1, hy]
            norm_num
            rfl)
      calc
        Set.range gamma = P.curve ''
            (Set.Icc (A.mark j) 1 ∪ Set.Icc 0 (A.mark i)) := hrange
        _ = (curvePath P) ''
            (Set.Icc (A.sortedMark 1) 1 ∪
              Set.Icc 0 (A.sortedMark 0)) := by
          rw [← hmarkr, ← hmarks, hr0, hs1]
          rfl
        _ = Set.range A.wrapSubpath := A.range_wrapSubpath.symm


-- @@ L3931-4294 verbatim
/-- Four-mark range refinement of `cyclicAdjacent_of_embedded_arc_four`: the
embedded mark-avoiding arc is exactly one adjacent cut or the wrap cut. -/
theorem range_eq_adjacentSubpath_or_wrap_of_embedded_arc_four
    (A : P.CyclicMarking 3) (gamma : C(I, E))
    (hgamma : ∀ u, gamma u ∈ V.orbit P.p)
    (hgamma_inj : Injective gamma) (i j : Fin 4)
    (hsource : gamma 0 = A.point i)
    (htarget : gamma 1 = A.point j)
    (havoid : ∀ {u : I}, u ∈ Set.Ioo 0 1 →
      ∀ l, gamma u ≠ A.point l) :
    (∃ q : Fin 3,
      Set.range gamma = Set.range (A.adjacentSubpath q)) ∨
      Set.range gamma = Set.range A.wrapSubpath := by
  let r : Fin 4 := A.sortedLabel.symm i
  let s : Fin 4 := A.sortedLabel.symm j
  let x : ℝ := A.forwardSortedMark r
  let y : ℝ := A.forwardSortedMark s
  let T : ℝ := V.fundamentalPeriod P.hp
  have hT : 0 < T := V.fundamentalPeriod_pos P.hp
  have hmarkr : A.sortedMark r = A.mark i := by
    simp [r, sortedMark]
  have hmarks : A.sortedMark s = A.mark j := by
    simp [s, sortedMark]
  have hsource' : gamma 0 = P.curve (A.mark i) :=
    hsource.trans (A.curve_mark i).symm
  have htarget' : gamma 1 = P.curve (A.mark j) :=
    htarget.trans (A.curve_mark j).symm
  let F := P.forwardPhaseLiftOfOrbitPathAtCurve gamma hgamma
    (A.mark i) hsource'
  have hF0 : F 0 = x := by
    calc
      F 0 = P.forwardPhaseLift (A.mark i) :=
        P.forwardPhaseLiftOfOrbitPathAtCurve_zero gamma hgamma
          (A.mark i) hsource'
      _ = P.forwardPhaseLift (A.sortedMark r) := by rw [hmarkr]
      _ = x := rfl
  obtain ⟨z, hz⟩ := P.forwardPhaseLift_target_eq_add_zsmul
    gamma hgamma (A.mark i) (A.mark j) hsource' htarget'
  have hyz : y = F 1 + (z : ℝ) * T := by
    calc
      y = P.forwardPhaseLift (A.sortedMark s) := rfl
      _ = P.forwardPhaseLift (A.mark j) := by rw [hmarks]
      _ = F 1 + (z : ℝ) * T := by
        simpa [F, T, zsmul_eq_mul] using hz
  have hy : y = P.forwardPhaseLift (A.mark j) := by
    calc
      y = P.forwardPhaseLift (A.sortedMark s) := rfl
      _ = P.forwardPhaseLift (A.mark j) := by rw [hmarks]
  have hF1 : F 1 = y - (z : ℝ) * T := by linarith
  have hx0 : 0 ≤ x := A.forwardSortedMark_nonneg r
  have hxT : x < T := A.forwardSortedMark_lt_period r
  have hy0 : 0 ≤ y := A.forwardSortedMark_nonneg s
  have hyT : y < T := A.forwardSortedMark_lt_period s
  have hspan := A.forwardArc_endpoint_within_one_period gamma hgamma
    hgamma_inj i hsource' havoid
  have hmonoanti :=
    P.forwardPhaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti
      gamma hgamma hgamma_inj (A.mark i) hsource'
  have finishDirect (q : Fin 3)
      (hlabels :
        (i = A.sortedLabel q.castSucc ∧ j = A.sortedLabel q.succ) ∨
        (j = A.sortedLabel q.castSucc ∧ i = A.sortedLabel q.succ))
      (hend0 : F 1 = P.forwardPhaseLift (A.mark j)) :
      Set.range gamma = Set.range (A.adjacentSubpath q) := by
    have hmarksNe : A.mark i ≠ A.mark j := by
      intro heq
      have hij : i ≠ j := by
        intro hij
        rcases hlabels with ⟨hi, hj⟩ | ⟨hj, hi⟩
        · apply ne_of_lt Fin.castSucc_lt_succ
          apply A.sortedLabel.injective
          exact hi.symm.trans (hij.trans hj)
        · apply ne_of_lt Fin.castSucc_lt_succ
          apply A.sortedLabel.injective
          exact hj.symm.trans (hij.symm.trans hi)
      exact hij (A.mark_injective heq)
    have hrange := P.range_eq_curve_image_uIcc_of_forward_endpoint
      gamma hgamma hgamma_inj (A.mark i) (A.mark j) hmarksNe hsource'
      hend0
    have hinterval : Set.uIcc (A.mark i) (A.mark j) =
        Set.Icc (A.sortedMark q.castSucc) (A.sortedMark q.succ) := by
      rcases hlabels with ⟨hi, hj⟩ | ⟨hj, hi⟩
      · rw [hi, hj]
        change Set.uIcc (A.sortedMark q.castSucc) (A.sortedMark q.succ) = _
        rw [Set.uIcc_of_le
          (A.sortedMark_strictMono Fin.castSucc_lt_succ).le]
      · rw [hi, hj]
        change Set.uIcc (A.sortedMark q.succ) (A.sortedMark q.castSucc) = _
        rw [Set.uIcc_of_ge
          (A.sortedMark_strictMono Fin.castSucc_lt_succ).le]
    calc
      Set.range gamma = P.curve '' Set.uIcc (A.mark i) (A.mark j) :=
        hrange
      _ = (curvePath P) '' Set.Icc (A.sortedMark q.castSucc)
          (A.sortedMark q.succ) := by rw [hinterval]; rfl
      _ = Set.range (A.adjacentSubpath q) :=
        (A.range_adjacentSubpath q).symm
  have finishWrapAdd
      (hi : i = A.sortedLabel (Fin.last 3))
      (hj : j = A.sortedLabel 0)
      (hendAdd : F 1 = P.forwardPhaseLift (A.mark j) + T) :
      Set.range gamma = Set.range A.wrapSubpath := by
    have hrange := P.range_eq_curve_image_wrap_of_forward_endpoint_add_period
      gamma hgamma hgamma_inj (A.mark i) (A.mark j)
      (A.mark_ne_one i) hsource' (by simpa [T] using hendAdd)
    calc
      Set.range gamma = P.curve ''
          (Set.Icc (A.mark i) 1 ∪ Set.Icc 0 (A.mark j)) := hrange
      _ = (curvePath P) ''
          (Set.Icc (A.sortedMark (Fin.last 3)) 1 ∪
            Set.Icc 0 (A.sortedMark 0)) := by
        rw [hi, hj]
        rfl
      _ = Set.range A.wrapSubpath := A.range_wrapSubpath.symm
  have finishWrapSub
      (hi : i = A.sortedLabel 0)
      (hj : j = A.sortedLabel (Fin.last 3))
      (hendSub : F 1 = P.forwardPhaseLift (A.mark j) - T) :
      Set.range gamma = Set.range A.wrapSubpath := by
    have hrange := P.range_eq_curve_image_wrap_of_forward_endpoint_sub_period
      gamma hgamma hgamma_inj (A.mark i) (A.mark j)
      (A.mark_ne_one j) hsource' (by simpa [T] using hendSub)
    calc
      Set.range gamma = P.curve ''
          (Set.Icc (A.mark j) 1 ∪ Set.Icc 0 (A.mark i)) := hrange
      _ = (curvePath P) ''
          (Set.Icc (A.sortedMark (Fin.last 3)) 1 ∪
            Set.Icc 0 (A.sortedMark 0)) := by
        rw [hi, hj]
        rfl
      _ = Set.range A.wrapSubpath := A.range_wrapSubpath.symm
  rcases hmonoanti with hmono | hanti
  · have hFinc : F 0 < F 1 := hmono (show (0 : I) < 1 by norm_num)
    have hFhi : F 1 < F 0 + T := hspan.1 hFinc
    rcases int_translate_forward_normal_form hT hx0 hxT hy0 hyT z
      (by simpa [hF0, hF1] using hFinc)
      (by simpa [hF0, hF1] using hFhi) with
      ⟨hz0, hxy⟩ | ⟨hzm1, hyx⟩
    · subst z
      have hrs : r < s := A.forwardSortedMark_strictMono.lt_iff_lt.mp hxy
      have hsuc : s.val = r.val + 1 := by
        by_contra hne
        have hgap : r.val + 1 < s.val := by
          change r.val < s.val at hrs
          omega
        let l : Fin 4 := ⟨r.val + 1, by omega⟩
        have hrl : r < l := by
          change r.val < r.val + 1
          omega
        have hls : l < s := by
          change r.val + 1 < s.val
          exact hgap
        have hxl := A.forwardSortedMark_strictMono hrl
        have hly := A.forwardSortedMark_strictMono hls
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 0
        apply hbarrier.1
        constructor
        · have h : F 0 < A.forwardSortedMark l := by
            rw [hF0]
            exact hxl
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
        · have h : A.forwardSortedMark l < F 1 := by
            rw [hF1]
            norm_num
            exact hly
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
      let q : Fin 3 := ⟨r.val, by
        change r.val < s.val at hrs
        omega⟩
      left
      refine ⟨q, finishDirect q (Or.inl ⟨?_, ?_⟩) ?_⟩
      · calc
          i = A.sortedLabel r := by simp [r]
          _ = A.sortedLabel q.castSucc := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            rfl
      · calc
          j = A.sortedLabel s := by simp [s]
          _ = A.sortedLabel q.succ := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            exact hsuc
      · rw [hF1, hy]
        norm_num
    · subst z
      have hsr : s < r := A.forwardSortedMark_strictMono.lt_iff_lt.mp hyx
      have hrLast : r.val = 3 := by
        by_contra hne
        have hrlt : r.val < 3 := by omega
        let l : Fin 4 := ⟨r.val + 1, by omega⟩
        have hrl : r < l := by
          change r.val < r.val + 1
          omega
        have hxl := A.forwardSortedMark_strictMono hrl
        have hlT := A.forwardSortedMark_lt_period l
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 0
        apply hbarrier.1
        constructor
        · have h : F 0 < A.forwardSortedMark l := by
            rw [hF0]
            exact hxl
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
        · rw [hF1]
          norm_num
          linarith
      have hsZero : s.val = 0 := by
        by_contra hne
        have hspos : 0 < s.val := by omega
        let l : Fin 4 := 0
        have hls : l < s := by
          change 0 < s.val
          exact hspos
        have h0y := A.forwardSortedMark_strictMono hls
        have hxT' : x < A.forwardSortedMark l + T := by
          have hl0 := A.forwardSortedMark_nonneg l
          linarith
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 1
        apply hbarrier.1
        constructor
        · have h : F 0 < A.forwardSortedMark l + T := by
            rw [hF0]
            exact hxT'
          simpa only [F, T, one_zsmul,
            forwardPhaseLift_mark_sortedLabel] using h
        · rw [hF1]
          norm_num
          linarith
      right
      apply finishWrapAdd
      · calc
          i = A.sortedLabel r := by simp [r]
          _ = A.sortedLabel (Fin.last 3) := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            exact hrLast
      · calc
          j = A.sortedLabel s := by simp [s]
          _ = A.sortedLabel 0 := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            exact hsZero
      · rw [hF1, hy]
        norm_num
  · have hFdec : F 1 < F 0 := hanti (show (0 : I) < 1 by norm_num)
    have hFlo : F 0 - T < F 1 := hspan.2 hFdec
    rcases int_translate_backward_normal_form hT hx0 hxT hy0 hyT z
      (by simpa [hF0, hF1] using hFlo)
      (by simpa [hF0, hF1] using hFdec) with
      ⟨hz0, hyx⟩ | ⟨hz1, hxy⟩
    · subst z
      have hsr : s < r := A.forwardSortedMark_strictMono.lt_iff_lt.mp hyx
      have hsuc : r.val = s.val + 1 := by
        by_contra hne
        have hgap : s.val + 1 < r.val := by
          change s.val < r.val at hsr
          omega
        let l : Fin 4 := ⟨s.val + 1, by omega⟩
        have hsl : s < l := by
          change s.val < s.val + 1
          omega
        have hlr : l < r := by
          change s.val + 1 < r.val
          exact hgap
        have hyl := A.forwardSortedMark_strictMono hsl
        have hlx := A.forwardSortedMark_strictMono hlr
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 0
        apply hbarrier.2
        constructor
        · have h : F 1 < A.forwardSortedMark l := by
            rw [hF1]
            norm_num
            exact hyl
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
        · have h : A.forwardSortedMark l < F 0 := by
            rw [hF0]
            exact hlx
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
      let q : Fin 3 := ⟨s.val, by
        change s.val < r.val at hsr
        omega⟩
      left
      refine ⟨q, finishDirect q (Or.inr ⟨?_, ?_⟩) ?_⟩
      · calc
          j = A.sortedLabel s := by simp [s]
          _ = A.sortedLabel q.castSucc := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            rfl
      · calc
          i = A.sortedLabel r := by simp [r]
          _ = A.sortedLabel q.succ := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            exact hsuc
      · rw [hF1, hy]
        norm_num
    · subst z
      have hrs : r < s := A.forwardSortedMark_strictMono.lt_iff_lt.mp hxy
      have hrZero : r.val = 0 := by
        by_contra hne
        have hrpos : 0 < r.val := by omega
        let l : Fin 4 := ⟨r.val - 1, by omega⟩
        have hlr : l < r := by
          change r.val - 1 < r.val
          omega
        have hlx := A.forwardSortedMark_strictMono hlr
        have hl0 := A.forwardSortedMark_nonneg l
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) 0
        apply hbarrier.2
        constructor
        · rw [hF1]
          norm_num
          linarith
        · have h : A.forwardSortedMark l < F 0 := by
            rw [hF0]
            exact hlx
          simpa only [F, zero_zsmul, add_zero,
            forwardPhaseLift_mark_sortedLabel] using h
      have hsLast : s.val = 3 := by
        by_contra hne
        have hslt : s.val < 3 := by omega
        let l : Fin 4 := Fin.last 3
        have hsl : s < l := by
          change s.val < 3
          exact hslt
        have hyl := A.forwardSortedMark_strictMono hsl
        have hlT := A.forwardSortedMark_lt_period l
        have hbarrier := A.forwardMarkTranslate_not_between gamma hgamma
          (A.mark i) hsource' havoid (A.sortedLabel l) (-1)
        apply hbarrier.2
        constructor
        · rw [hF1]
          norm_num
          linarith
        · rw [hF0]
          norm_num
          linarith
      right
      apply finishWrapSub
      · calc
          i = A.sortedLabel r := by simp [r]
          _ = A.sortedLabel 0 := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            exact hrZero
      · calc
          j = A.sortedLabel s := by simp [s]
          _ = A.sortedLabel (Fin.last 3) := by
            apply congrArg A.sortedLabel
            apply Fin.ext
            exact hsLast
      · rw [hF1, hy]
        norm_num


-- @@ L4296-4369 verbatim
/-- The wrap-around subarc likewise contains no marked point other than its
largest and smallest endpoints. -/
theorem point_mem_range_wrapSubpath
    (A : P.CyclicMarking k) (j : Fin (k + 1))
    (hj : A.point j ∈ Set.range A.wrapSubpath) :
    j = A.sortedLabel (Fin.last k) ∨ j = A.sortedLabel 0 := by
  have hj0 : A.point j ∈ Set.range A.curveCutWrap := by
    simpa only [wrapSubpath, Path.cast_coe] using hj
  rw [curveCutWrap, Path.trans_range] at hj0
  let r : Fin (k + 1) := A.sortedLabel.symm j
  have hmono := A.sortedMark_strictMono
  have hmarkr : A.sortedMark r = A.mark j := by
    simp [r, sortedMark]
  rcases hj0 with hjMax | hjMin
  · have hle : A.sortedMark (Fin.last k) ≤ (1 : I) :=
      (A.sortedMark (Fin.last k)).property.2
    change A.point j ∈ Set.range ((curvePath P).subpath
      (A.sortedMark (Fin.last k)) 1) at hjMax
    rw [Path.range_subpath_of_le _ _ _ hle] at hjMax
    obtain ⟨s, hs, hsj⟩ := hjMax
    change P.curve s = A.point j at hsj
    rw [← A.curve_mark j] at hsj
    rcases P.curve_eq_cases hsj with hsame | hends | hends
    · left
      have hlo : A.sortedMark (Fin.last k) ≤ A.sortedMark r := by
        rw [hmarkr, ← hsame]
        exact hs.1
      have hrlo : Fin.last k ≤ r := hmono.le_iff_le.mp hlo
      have hr : r = Fin.last k := le_antisymm (Fin.le_last r) hrlo
      calc
        j = A.sortedLabel r := by simp [r]
        _ = A.sortedLabel (Fin.last k) := by rw [hr]
    · exact (A.mark_ne_one j hends.2).elim
    · right
      have hrzero : r ≤ 0 := by
        apply hmono.le_iff_le.mp
        rw [hmarkr, hends.2]
        exact (A.sortedMark 0).property.1
      have hr : r = 0 := le_antisymm hrzero (Fin.zero_le r)
      calc
        j = A.sortedLabel r := by simp [r]
        _ = A.sortedLabel 0 := by rw [hr]
  · have hle : (0 : I) ≤ A.sortedMark 0 :=
      (A.sortedMark 0).property.1
    change A.point j ∈ Set.range ((curvePath P).subpath
      0 (A.sortedMark 0)) at hjMin
    rw [Path.range_subpath_of_le _ _ _ hle] at hjMin
    obtain ⟨s, hs, hsj⟩ := hjMin
    change P.curve s = A.point j at hsj
    rw [← A.curve_mark j] at hsj
    rcases P.curve_eq_cases hsj with hsame | hends | hends
    · right
      have hrzero : r ≤ 0 := by
        apply hmono.le_iff_le.mp
        rw [hmarkr, ← hsame]
        exact hs.2
      have hr : r = 0 := le_antisymm hrzero (Fin.zero_le r)
      calc
        j = A.sortedLabel r := by simp [r]
        _ = A.sortedLabel 0 := by rw [hr]
    · exact (A.mark_ne_one j hends.2).elim
    · have hminNe : A.sortedMark 0 ≠ 1 :=
        A.mark_ne_one (A.sortedLabel 0)
      have hminNeReal : (A.sortedMark 0 : ℝ) ≠ 1 := by
        intro h
        apply hminNe
        apply Subtype.ext
        exact h
      have hminLt : (A.sortedMark 0 : ℝ) < 1 :=
        lt_of_le_of_ne (A.sortedMark 0).property.2 hminNeReal
      have hsle : (s : ℝ) ≤ A.sortedMark 0 := hs.2
      rw [hends.1] at hsle
      have hsle' : (1 : ℝ) ≤ A.sortedMark 0 := by simpa using hsle
      linarith


-- @@ L4371-4430 verbatim
/-- Two distinct linear cyclic cuts can meet only at one of the marked
points.  The statement deliberately forgets which common end occurs: that
coarser form is exactly what is needed to exclude an unmarked point in the
open Morse chart from every nonlocal cut. -/
theorem mem_inter_adjacentSubpath_is_mark
    (A : P.CyclicMarking k) {i j : Fin k} (hij : i ≠ j) {x : E}
    (hxi : x ∈ Set.range (A.adjacentSubpath i))
    (hxj : x ∈ Set.range (A.adjacentSubpath j)) :
    ∃ l : Fin (k + 1), x = A.point l := by
  rw [A.range_adjacentSubpath i] at hxi
  rw [A.range_adjacentSubpath j] at hxj
  obtain ⟨s, hs, rfl⟩ := hxi
  obtain ⟨v, hv, hvs⟩ := hxj
  change P.curve v = P.curve s at hvs
  have hmono := A.sortedMark_strictMono
  rcases P.curve_eq_cases hvs with hsame | hends | hends
  · subst v
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hidx : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        omega
      have horder : A.sortedMark i.succ ≤
          A.sortedMark j.castSucc := hmono.monotone hidx
      have heq : s = A.sortedMark i.succ := by
        apply le_antisymm hs.2
        exact horder.trans hv.1
      refine ⟨A.sortedLabel i.succ, ?_⟩
      rw [heq]
      change P.curve (A.sortedMark i.succ) = _
      simpa [sortedMark] using A.curve_mark (A.sortedLabel i.succ)
    · have hidx : j.succ ≤ i.castSucc := by
        change j.val + 1 ≤ i.val
        omega
      have horder : A.sortedMark j.succ ≤
          A.sortedMark i.castSucc := hmono.monotone hidx
      have heq : s = A.sortedMark j.succ := by
        apply le_antisymm hv.2
        exact horder.trans hs.1
      refine ⟨A.sortedLabel j.succ, ?_⟩
      rw [heq]
      change P.curve (A.sortedMark j.succ) = _
      simpa [sortedMark] using A.curve_mark (A.sortedLabel j.succ)
  · have hsOne : (A.sortedMark i.succ : ℝ) = 1 := by
      have hsOneI : (1 : I) ≤ A.sortedMark i.succ := by
        simpa [hends.2] using hs.2
      apply le_antisymm (A.sortedMark i.succ).property.2
      change (1 : ℝ) ≤ (A.sortedMark i.succ : ℝ) at hsOneI
      exact hsOneI
    exact (A.mark_ne_one (A.sortedLabel i.succ) (by
      apply Subtype.ext
      simpa [sortedMark] using hsOne)).elim
  · have hvOne : (A.sortedMark j.succ : ℝ) = 1 := by
      have hvOneI : (1 : I) ≤ A.sortedMark j.succ := by
        simpa [hends.1] using hv.2
      apply le_antisymm (A.sortedMark j.succ).property.2
      change (1 : ℝ) ≤ (A.sortedMark j.succ : ℝ) at hvOneI
      exact hvOneI
    exact (A.mark_ne_one (A.sortedLabel j.succ) (by
      apply Subtype.ext
      simpa [sortedMark] using hvOne)).elim


-- @@ L4432-4507 verbatim
/-- A linear cyclic cut and the wrap cut can meet only at a marked point. -/
theorem mem_inter_adjacentSubpath_wrapSubpath_is_mark
    (A : P.CyclicMarking k) (i : Fin k) {x : E}
    (hxi : x ∈ Set.range (A.adjacentSubpath i))
    (hxw : x ∈ Set.range A.wrapSubpath) :
    ∃ l : Fin (k + 1), x = A.point l := by
  rw [A.range_adjacentSubpath i] at hxi
  rw [A.range_wrapSubpath] at hxw
  obtain ⟨s, hs, rfl⟩ := hxi
  obtain ⟨v, hv, hvs⟩ := hxw
  change P.curve v = P.curve s at hvs
  have hmono := A.sortedMark_strictMono
  rcases hv with hv | hv
  · rcases P.curve_eq_cases hvs with hsame | hends | hends
    · subst v
      have hidx : i.succ ≤ Fin.last k := Fin.le_last _
      have horder : A.sortedMark i.succ ≤
          A.sortedMark (Fin.last k) := hmono.monotone hidx
      have heq : s = A.sortedMark (Fin.last k) := by
        apply le_antisymm (hs.2.trans horder)
        exact hv.1
      refine ⟨A.sortedLabel (Fin.last k), ?_⟩
      rw [heq]
      change P.curve (A.sortedMark (Fin.last k)) = _
      simpa [sortedMark] using A.curve_mark
        (A.sortedLabel (Fin.last k))
    · have hsOne : (A.sortedMark i.succ : ℝ) = 1 := by
        have hsOneI : (1 : I) ≤ A.sortedMark i.succ := by
          simpa [hends.2] using hs.2
        apply le_antisymm (A.sortedMark i.succ).property.2
        change (1 : ℝ) ≤ (A.sortedMark i.succ : ℝ) at hsOneI
        exact hsOneI
      exact (A.mark_ne_one (A.sortedLabel i.succ) (by
        apply Subtype.ext
        simpa [sortedMark] using hsOne)).elim
    · have hsZero : s = 0 := hends.2
      have hminZero : A.sortedMark 0 = 0 := by
        apply le_antisymm
        · rw [← hsZero]
          exact (hmono.monotone (Fin.zero_le i.castSucc)).trans hs.1
        · exact (A.sortedMark 0).property.1
      refine ⟨A.sortedLabel 0, ?_⟩
      rw [hsZero]
      change P.curve 0 = _
      rw [← hminZero]
      simpa [sortedMark] using A.curve_mark (A.sortedLabel 0)
  · rcases P.curve_eq_cases hvs with hsame | hends | hends
    · subst v
      have hidx : (0 : Fin (k + 1)) ≤ i.castSucc := Fin.zero_le _
      have horder : A.sortedMark 0 ≤
          A.sortedMark i.castSucc := hmono.monotone hidx
      have heq : s = A.sortedMark 0 := by
        apply le_antisymm hv.2
        exact horder.trans hs.1
      refine ⟨A.sortedLabel 0, ?_⟩
      rw [heq]
      change P.curve (A.sortedMark 0) = _
      simpa [sortedMark] using A.curve_mark (A.sortedLabel 0)
    · have hsOne : (A.sortedMark i.succ : ℝ) = 1 := by
        have hsOneI : (1 : I) ≤ A.sortedMark i.succ := by
          simpa [hends.2] using hs.2
        apply le_antisymm (A.sortedMark i.succ).property.2
        change (1 : ℝ) ≤ (A.sortedMark i.succ : ℝ) at hsOneI
        exact hsOneI
      exact (A.mark_ne_one (A.sortedLabel i.succ) (by
        apply Subtype.ext
        simpa [sortedMark] using hsOne)).elim
    · have hvOne : (A.sortedMark 0 : ℝ) = 1 := by
        have hvOneI : (1 : I) ≤ A.sortedMark 0 := by
          simpa [hends.1] using hv.2
        apply le_antisymm (A.sortedMark 0).property.2
        change (1 : ℝ) ≤ (A.sortedMark 0 : ℝ) at hvOneI
        exact hvOneI
      exact (A.mark_ne_one (A.sortedLabel 0) (by
        apply Subtype.ext
        simpa [sortedMark] using hvOne)).elim


-- @@ L4509-4533 verbatim
/-- For a two-marked orbit, once one cyclic cut is known to be the local
segment, its complementary cut avoids every unmarked point of that local
segment. -/
theorem two_cut_complement_avoids_local_unmarked_point
    (A : P.CyclicMarking 1) (gamma : C(I, E)) {x : E}
    (hlocal : Set.range gamma = Set.range (A.adjacentSubpath 0) ∨
      Set.range gamma = Set.range A.wrapSubpath)
    (hx : x ∈ Set.range gamma) (hnotmark : ∀ l, x ≠ A.point l) :
    (Set.range gamma = Set.range (A.adjacentSubpath 0) ∧
        x ∉ Set.range A.wrapSubpath) ∨
      (Set.range gamma = Set.range A.wrapSubpath ∧
        x ∉ Set.range (A.adjacentSubpath 0)) := by
  rcases hlocal with hlocal | hlocal
  · left
    refine ⟨hlocal, ?_⟩
    intro hxwrap
    obtain ⟨l, hl⟩ := A.mem_inter_adjacentSubpath_wrapSubpath_is_mark
      0 (hlocal ▸ hx) hxwrap
    exact hnotmark l hl
  · right
    refine ⟨hlocal, ?_⟩
    intro hxadj
    obtain ⟨l, hl⟩ := A.mem_inter_adjacentSubpath_wrapSubpath_is_mark
      0 hxadj (hlocal ▸ hx)
    exact hnotmark l hl


-- @@ L4535-4559 verbatim
/-- Uniform two-cut form: after deciding which cut is local, the other cut
avoids every unmarked point of the local arc. -/
theorem two_cut_complement_avoids_all_local_unmarked
    (A : P.CyclicMarking 1) (gamma : C(I, E))
    (hlocal : Set.range gamma = Set.range (A.adjacentSubpath 0) ∨
      Set.range gamma = Set.range A.wrapSubpath) :
    (Set.range gamma = Set.range (A.adjacentSubpath 0) ∧
        ∀ {x : E}, x ∈ Set.range gamma → (∀ l, x ≠ A.point l) →
          x ∉ Set.range A.wrapSubpath) ∨
      (Set.range gamma = Set.range A.wrapSubpath ∧
        ∀ {x : E}, x ∈ Set.range gamma → (∀ l, x ≠ A.point l) →
          x ∉ Set.range (A.adjacentSubpath 0)) := by
  rcases hlocal with hlocal | hlocal
  · left
    refine ⟨hlocal, ?_⟩
    intro x hx hnotmark hxwrap
    obtain ⟨l, hl⟩ := A.mem_inter_adjacentSubpath_wrapSubpath_is_mark
      0 (hlocal ▸ hx) hxwrap
    exact hnotmark l hl
  · right
    refine ⟨hlocal, ?_⟩
    intro x hx hnotmark hxadj
    obtain ⟨l, hl⟩ := A.mem_inter_adjacentSubpath_wrapSubpath_is_mark
      0 hxadj (hlocal ▸ hx)
    exact hnotmark l hl


-- @@ L4561-4566 verbatim
/-- Uniform set-valued enumeration of all cyclic cuts: the first `k` values
are the linearly adjacent cuts and the last value is the wrap cut. -/
noncomputable def cyclicCutRange
    (A : P.CyclicMarking k) (i : Fin (k + 1)) : Set E :=
  Fin.lastCases (Set.range A.wrapSubpath)
    (fun j => Set.range (A.adjacentSubpath j)) i


-- @@ L4568-4572 verbatim
/-- Source label of a uniformly indexed cyclic cut. -/
noncomputable def cyclicCutSourceLabel
    (A : P.CyclicMarking k) (i : Fin (k + 1)) : Fin (k + 1) :=
  Fin.lastCases (A.sortedLabel (Fin.last k))
    (fun j => A.sortedLabel j.castSucc) i


-- @@ L4574-4578 verbatim
/-- Target label of a uniformly indexed cyclic cut. -/
noncomputable def cyclicCutTargetLabel
    (A : P.CyclicMarking k) (i : Fin (k + 1)) : Fin (k + 1) :=
  Fin.lastCases (A.sortedLabel 0)
    (fun j => A.sortedLabel j.succ) i


-- @@ L4580-4584 verbatim
/-- Continuous representative of a uniformly indexed cyclic cut. -/
noncomputable def cyclicCutMap
    (A : P.CyclicMarking k) (i : Fin (k + 1)) : C(I, E) :=
  Fin.lastCases A.wrapSubpath.toContinuousMap
    (fun j => (A.adjacentSubpath j).toContinuousMap) i


-- @@ L4586-4591 verbatim
theorem cyclicCutMap_zero
    (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    A.cyclicCutMap i 0 = A.point (A.cyclicCutSourceLabel i) := by
  induction i using Fin.lastCases with
  | last => simp [cyclicCutMap, cyclicCutSourceLabel]
  | cast i => simp [cyclicCutMap, cyclicCutSourceLabel]


-- @@ L4593-4598 verbatim
theorem cyclicCutMap_one
    (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    A.cyclicCutMap i 1 = A.point (A.cyclicCutTargetLabel i) := by
  induction i using Fin.lastCases with
  | last => simp [cyclicCutMap, cyclicCutTargetLabel]
  | cast i => simp [cyclicCutMap, cyclicCutTargetLabel]


-- @@ L4600-4607 verbatim
/-- The indexed cut as a path with its marked endpoint labels exposed. -/
noncomputable def cyclicCutPath
    (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    Path (A.point (A.cyclicCutSourceLabel i))
      (A.point (A.cyclicCutTargetLabel i)) where
  toContinuousMap := A.cyclicCutMap i
  source' := A.cyclicCutMap_zero i
  target' := A.cyclicCutMap_one i


-- @@ L4609-4614 verbatim
theorem range_cyclicCutPath
    (A : P.CyclicMarking k) (i : Fin (k + 1)) :
    Set.range (A.cyclicCutPath i) = A.cyclicCutRange i := by
  induction i using Fin.lastCases with
  | last => simp [cyclicCutPath, cyclicCutMap, cyclicCutRange]
  | cast i => simp [cyclicCutPath, cyclicCutMap, cyclicCutRange]


-- @@ L4616-4632 verbatim
theorem cyclicCutPath_mem_orbit
    (A : P.CyclicMarking k) (i : Fin (k + 1)) (u : I) :
    A.cyclicCutPath i u ∈ V.orbit P.p := by
  have hu : A.cyclicCutPath i u ∈ A.cyclicCutRange i := by
    rw [← A.range_cyclicCutPath i]
    exact ⟨u, rfl⟩
  induction i using Fin.lastCases with
  | last =>
      simp only [cyclicCutRange, Fin.lastCases_last] at hu
      rcases hu with ⟨v, hv⟩
      rw [← hv]
      exact A.wrapSubpath_mem_orbit v
  | cast i =>
      simp only [cyclicCutRange, Fin.lastCases_castSucc] at hu
      rcases hu with ⟨v, hv⟩
      rw [← hv]
      exact A.adjacentSubpath_mem_orbit i v


-- @@ L4634-4637 verbatim
@[simp] theorem cyclicCutRange_castSucc
    (A : P.CyclicMarking k) (i : Fin k) :
    A.cyclicCutRange i.castSucc = Set.range (A.adjacentSubpath i) := by
  simp [cyclicCutRange]


-- @@ L4639-4642 verbatim
@[simp] theorem cyclicCutRange_last
    (A : P.CyclicMarking k) :
    A.cyclicCutRange (Fin.last k) = Set.range A.wrapSubpath := by
  simp [cyclicCutRange]


-- @@ L4644-4672 verbatim
/-- Distinct values of the uniform cyclic-cut enumeration meet only at
marked points. -/
theorem mem_inter_cyclicCutRange_is_mark
    (A : P.CyclicMarking k) {i j : Fin (k + 1)} (hij : i ≠ j) {x : E}
    (hxi : x ∈ A.cyclicCutRange i)
    (hxj : x ∈ A.cyclicCutRange j) :
    ∃ l : Fin (k + 1), x = A.point l := by
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j =>
          rw [A.cyclicCutRange_last] at hxi
          rw [A.cyclicCutRange_castSucc] at hxj
          exact A.mem_inter_adjacentSubpath_wrapSubpath_is_mark j hxj hxi
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          rw [A.cyclicCutRange_castSucc] at hxi
          rw [A.cyclicCutRange_last] at hxj
          exact A.mem_inter_adjacentSubpath_wrapSubpath_is_mark i hxi hxj
      | cast j =>
          rw [A.cyclicCutRange_castSucc] at hxi
          rw [A.cyclicCutRange_castSucc] at hxj
          apply A.mem_inter_adjacentSubpath_is_mark
            (i := i) (j := j) ?_ hxi hxj
          intro hij'
          apply hij
          exact congrArg Fin.castSucc hij'


-- @@ L4674-4684 verbatim
/-- The old adjacent-or-wrap presentation of a local arc is equivalent to
saying that it is one value of the uniform cyclic-cut enumeration. -/
theorem exists_cyclicCutRange_eq_of_adjacent_or_wrap
    (A : P.CyclicMarking k) (gamma : C(I, E))
    (hcut : (∃ q : Fin k,
        Set.range gamma = Set.range (A.adjacentSubpath q)) ∨
      Set.range gamma = Set.range A.wrapSubpath) :
    ∃ i : Fin (k + 1), Set.range gamma = A.cyclicCutRange i := by
  rcases hcut with ⟨q, hq⟩ | hwrap
  · exact ⟨q.castSucc, by simpa using hq⟩
  · exact ⟨Fin.last k, by simpa using hwrap⟩


-- @@ L4686-4721 verbatim
/-- Two disjoint local arcs occupying cyclic cuts have distinct cut indices;
every other cut avoids any unmarked point lying on one of the two local
arcs. -/
theorem exists_distinct_localCutRanges_and_excludes_other
    (A : P.CyclicMarking k) (gamma delta : C(I, E))
    (hdisj : Disjoint (Set.range gamma) (Set.range delta))
    (hgamma : ∃ i : Fin (k + 1),
      Set.range gamma = A.cyclicCutRange i)
    (hdelta : ∃ j : Fin (k + 1),
      Set.range delta = A.cyclicCutRange j)
    {x : E} (hx : x ∈ Set.range gamma ∪ Set.range delta)
    (hnotmark : ∀ l, x ≠ A.point l) :
    ∃ i j : Fin (k + 1),
      i ≠ j ∧ Set.range gamma = A.cyclicCutRange i ∧
        Set.range delta = A.cyclicCutRange j ∧
        ∀ r, r ≠ i → r ≠ j → x ∉ A.cyclicCutRange r := by
  obtain ⟨i, hi⟩ := hgamma
  obtain ⟨j, hj⟩ := hdelta
  have hij : i ≠ j := by
    intro hij
    subst j
    have hgamma0 : gamma 0 ∈ Set.range gamma := ⟨0, rfl⟩
    have hcut0 : gamma 0 ∈ A.cyclicCutRange i := hi ▸ hgamma0
    have hdelta0 : gamma 0 ∈ Set.range delta := by
      rw [hj]
      exact hcut0
    exact Set.disjoint_left.mp hdisj hgamma0 hdelta0
  refine ⟨i, j, hij, hi, hj, ?_⟩
  intro r hri hrj hxr
  rcases hx with hxgamma | hxdelta
  · obtain ⟨l, hl⟩ := A.mem_inter_cyclicCutRange_is_mark hri.symm
      (hi ▸ hxgamma) hxr
    exact hnotmark l hl
  · obtain ⟨l, hl⟩ := A.mem_inter_cyclicCutRange_is_mark hrj.symm
      (hj ▸ hxdelta) hxr
    exact hnotmark l hl


-- @@ L4723-4757 verbatim
/-- Uniform version of the preceding theorem: the two local cut indices are
chosen once, before quantifying over unmarked local points. -/
theorem exists_distinct_localCutRanges_and_otherCuts_avoid_unmarkedLocal
    (A : P.CyclicMarking k) (gamma delta : C(I, E))
    (hdisj : Disjoint (Set.range gamma) (Set.range delta))
    (hgamma : ∃ i : Fin (k + 1),
      Set.range gamma = A.cyclicCutRange i)
    (hdelta : ∃ j : Fin (k + 1),
      Set.range delta = A.cyclicCutRange j) :
    ∃ i j : Fin (k + 1),
      i ≠ j ∧ Set.range gamma = A.cyclicCutRange i ∧
        Set.range delta = A.cyclicCutRange j ∧
        ∀ {x : E}, x ∈ Set.range gamma ∪ Set.range delta →
          (∀ l, x ≠ A.point l) →
          ∀ r, r ≠ i → r ≠ j → x ∉ A.cyclicCutRange r := by
  obtain ⟨i, hi⟩ := hgamma
  obtain ⟨j, hj⟩ := hdelta
  have hij : i ≠ j := by
    intro hij
    subst j
    have hgamma0 : gamma 0 ∈ Set.range gamma := ⟨0, rfl⟩
    have hcut0 : gamma 0 ∈ A.cyclicCutRange i := hi ▸ hgamma0
    have hdelta0 : gamma 0 ∈ Set.range delta := by
      rw [hj]
      exact hcut0
    exact Set.disjoint_left.mp hdisj hgamma0 hdelta0
  refine ⟨i, j, hij, hi, hj, ?_⟩
  intro x hx hnotmark r hri hrj hxr
  rcases hx with hxgamma | hxdelta
  · obtain ⟨l, hl⟩ := A.mem_inter_cyclicCutRange_is_mark hri.symm
      (hi ▸ hxgamma) hxr
    exact hnotmark l hl
  · obtain ⟨l, hl⟩ := A.mem_inter_cyclicCutRange_is_mark hrj.symm
      (hj ▸ hxdelta) hxr
    exact hnotmark l hl


-- @@ L4759-4759 verbatim
end CyclicMarking

-- @@ L4760-4760 verbatim
end SimpleClosedOrbitParam


-- @@ L4762-4762 verbatim
/-! ## Ambient regular-zero realization of indexed cuts -/


-- @@ L4764-4764 verbatim
namespace SimpleClosedOrbitParam.CyclicMarking


-- @@ L4766-4766 verbatim
variable {C₀ : LevelCobordismData n} {s : ℝ}

-- @@ L4767-4767 verbatim
variable {hreg : sliceRegular C₀.G s}

-- @@ L4768-4768 verbatim
variable {V₀ : TamedField (SlabTamedField.sliceFLSAt C₀ s hreg)}

-- @@ L4769-4770 verbatim
variable {P₀ : SimpleClosedOrbitParam
  (SlabTamedField.sliceFLSAt C₀ s hreg) V₀}

-- @@ L4771-4771 verbatim
variable {k₀ : ℕ}


-- @@ L4773-4787 verbatim
/-- Put one indexed spatial cyclic cut back into its ambient regular time
slice. -/
noncomputable def cyclicCutAmbientPath
    (A : P₀.CyclicMarking k₀) (i : Fin (k₀ + 1)) :
    Path (cobSpaceTime (A.point (A.cyclicCutSourceLabel i)) s)
      (cobSpaceTime (A.point (A.cyclicCutTargetLabel i)) s) where
  toFun u := cobSpaceTime (A.cyclicCutPath i u) s
  continuous_toFun := by
    have hcob : Continuous (fun x : E₁ => cobSpaceTime x s) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (hasFDerivAt_cobSpaceTime s x).continuousAt
    exact hcob.comp (A.cyclicCutPath i).continuous
  source' := by simp [cyclicCutPath]
  target' := by simp [cyclicCutPath]


-- @@ L4789-4795 verbatim
theorem cyclicCutAmbientPath_fiber
    (A : P₀.CyclicMarking k₀) (i : Fin (k₀ + 1)) (u : I) :
    C₀.G (A.cyclicCutAmbientPath i u) = 0 := by
  have hu : A.cyclicCutPath i u ∈
      (SlabTamedField.sliceFLSAt C₀ s hreg).fiber :=
    V₀.orbit_subset_fiber P₀.hp (A.cyclicCutPath_mem_orbit i u)
  rwa [SlabTamedField.sliceFLSAt_fiber] at hu


-- @@ L4797-4802 verbatim
theorem cyclicCutAmbientPath_regular
    (A : P₀.CyclicMarking k₀) (i : Fin (k₀ + 1)) (u : I) :
    Surjective (spatialDeriv C₀.G (A.cyclicCutAmbientPath i u)) := by
  apply hreg (A.cyclicCutAmbientPath i u)
  · exact A.cyclicCutAmbientPath_fiber i u
  · simp [cyclicCutAmbientPath]


-- @@ L4804-4815 verbatim
/-- Every indexed regular-slice cut therefore carries the exact
`SpatiallyRegularZeroPath` structure consumed by compact time flow. -/
noncomputable def cyclicCutRegularZeroPath
    (A : P₀.CyclicMarking k₀) (i : Fin (k₀ + 1)) :
    SpatiallyRegularZeroPath C₀.G
      (cobSpaceTime (A.point (A.cyclicCutSourceLabel i)) s)
      (cobSpaceTime (A.point (A.cyclicCutTargetLabel i)) s) where
  toPath := A.cyclicCutAmbientPath i
  range_subset := by
    rintro z ⟨u, rfl⟩
    exact ⟨A.cyclicCutAmbientPath_fiber i u,
      A.cyclicCutAmbientPath_regular i u⟩


-- @@ L4817-4817 verbatim
end SimpleClosedOrbitParam.CyclicMarking


-- @@ L4819-4819 verbatim
/-! ## Safe-flow realization as an actual punctured critical arc -/


-- @@ L4821-4821 verbatim
namespace StandardMorseEventAt


-- @@ L4823-4823 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L4824-4824 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L4825-4825 verbatim
variable {M : StandardMorseEventAt (n := n) C center}


-- @@ L4827-4870 verbatim
/-- A compact-core regular path on a nearby slice gives an actual path in
the punctured critical slice as soon as one safe flow time sends its two
endpoints to the requested critical ends.  Avoidance of the saddle center is
automatic: the compact-core flow remains spatially regular, whereas the
event center is time-critical. -/
noncomputable def saddleCriticalExteriorArcOfSafeFlow
    {K : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (R : CompactTimeTamedField C.toLevelCobordismData K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (gamma : SpatiallyRegularZeroPath C.G x y)
    (hgammaK : ∀ u : I, gamma.toPath u ∈ K)
    (d : ℝ) (hd : |d| ≤ R.safeTime)
    (htime : ∀ u : I,
      tcoord (gamma.toPath u) + d = tcoord center)
    (rho : ℝ) (p q : SaddleBranch × SaddleBranch)
    (hsource : R.base.flow x d = M.saddleCriticalBoundaryEnd p rho)
    (htarget : R.base.flow y d = M.saddleCriticalBoundaryEnd q rho) :
    SaddleCriticalExteriorArc
      (fun r => M.saddleCriticalBoundaryEnd r rho)
      (puncturedCriticalSlice C center) p q where
  toPath := {
    toFun := fun u => R.base.flow (gamma.toPath u) d
    continuous_toFun := R.base.continuous_flow_uncurry.comp
      (gamma.toPath.continuous.prodMk continuous_const)
    source' := by rw [gamma.toPath.source, hsource]
    target' := by rw [gamma.toPath.target, htarget]
  }
  mem_exterior := by
    intro u
    change C.G (R.base.flow (gamma.toPath u) d) = 0 ∧
      tcoord (R.base.flow (gamma.toPath u) d) = tcoord center ∧
      R.base.flow (gamma.toPath u) d ≠ center
    constructor
    · exact R.flow_mem_fiber (gamma.fiber u) d
    constructor
    · exact (R.tcoord_flow (hgammaK u) hd).trans (htime u)
    · intro hcenter
      have hshort : |d| < 2 * R.safeTime := by
        calc
          |d| ≤ R.safeTime := hd
          _ < 2 * R.safeTime := by linarith [R.safeTime_pos]
      have hsurj := R.flow_spatialDeriv_surjective (hgammaK u) hshort
      rw [hcenter] at hsurj
      exact M.center_mem_timeCritical.2 hsurj


-- @@ L4872-4872 verbatim
namespace EmbeddedShrink


-- @@ L4874-4953 verbatim
/-- Safe flow need not hit the preselected chart-boundary ends literally.
It is enough that the two flowed endpoints have local critical parameters in
the declared quadrants: the two critical rays then attach them to the fixed
boundary ends without meeting the saddle center. -/
noncomputable def saddleCriticalExteriorArcOfSafeFlowWithLocalCaptures
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (hindex : M.index = .saddle)
    {K : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (R : CompactTimeTamedField C.toLevelCobordismData K)
    {x y : EuclideanSpace ℝ (Fin (n + 2))}
    (gamma : SpatiallyRegularZeroPath C.G x y)
    (hgammaK : ∀ w : I, gamma.toPath w ∈ K)
    (d : ℝ) (hd : |d| ≤ R.safeTime)
    (htime : ∀ w : I,
      tcoord (gamma.toPath w) + d = tcoord center)
    (rho : ℝ) (hrho : 0 < rho) (hrho_radius : rho < T.radius)
    (p q : SaddleBranch × SaddleBranch)
    (u v : E₂)
    (hu : ‖u‖ < T.radius) (hv : ‖v‖ < T.radius)
    (huquad : morseQuadratic .saddle (u 0, u 1) = (0 : ℝ) ^ 2)
    (hvquad : morseQuadratic .saddle (v 0, v 1) = (0 : ℝ) ^ 2)
    (hufirst : 0 < signedBranch p.1 (u 0))
    (husecond : 0 < signedBranch p.2 (u 1))
    (hvfirst : 0 < signedBranch q.1 (v 0))
    (hvsecond : 0 < signedBranch q.2 (v 1))
    (hsource : R.base.flow x d = M.param u)
    (htarget : R.base.flow y d = M.param v) :
    SaddleCriticalExteriorArc
      (fun r => M.saddleCriticalBoundaryEnd r rho)
      (puncturedCriticalSlice C center) p q := by
  let left := T.saddleCriticalRayToBoundaryPath H p.1 p.2 rho u
    huquad hufirst hrho hu hrho_radius
  let right := T.saddleCriticalRayToBoundaryPath H q.1 q.2 rho v
    hvquad hvfirst hrho hv hrho_radius
  let middle : Path (M.param u) (M.param v) := {
    toFun := fun w => R.base.flow (gamma.toPath w) d
    continuous_toFun := R.base.continuous_flow_uncurry.comp
      (gamma.toPath.continuous.prodMk continuous_const)
    source' := by rw [gamma.toPath.source, hsource]
    target' := by rw [gamma.toPath.target, htarget]
  }
  have hmiddle : ∀ w : I,
      middle w ∈ puncturedCriticalSlice C center := by
    intro w
    change C.G (R.base.flow (gamma.toPath w) d) = 0 ∧
      tcoord (R.base.flow (gamma.toPath w) d) = tcoord center ∧
      R.base.flow (gamma.toPath w) d ≠ center
    constructor
    · exact R.flow_mem_fiber (gamma.fiber w) d
    constructor
    · exact (R.tcoord_flow (hgammaK w) hd).trans (htime w)
    · intro hcenter
      have hshort : |d| < 2 * R.safeTime := by
        calc
          |d| ≤ R.safeTime := hd
          _ < 2 * R.safeTime := by linarith [R.safeTime_pos]
      have hsurj := R.flow_spatialDeriv_surjective (hgammaK w) hshort
      rw [hcenter] at hsurj
      exact M.center_mem_timeCritical.2 hsurj
  refine {
    toPath := left.symm.trans (middle.trans right)
    mem_exterior := ?_ }
  intro w
  have hw : left.symm.trans (middle.trans right) w ∈
      Set.range (left.symm.trans (middle.trans right)) := ⟨w, rfl⟩
  rw [Path.trans_range, Path.trans_range, Path.symm_range] at hw
  rcases hw with hleft | hmiddle' | hright
  · obtain ⟨z, hz⟩ := hleft
    rw [← hz]
    exact T.saddleCriticalRayToBoundaryPath_mem_puncturedCriticalSlice
      H hindex p.1 p.2 rho u huquad hufirst husecond hrho hu
        hrho_radius z
  · obtain ⟨z, hz⟩ := hmiddle'
    rw [← hz]
    exact hmiddle z
  · obtain ⟨z, hz⟩ := hright
    rw [← hz]
    exact T.saddleCriticalRayToBoundaryPath_mem_puncturedCriticalSlice
      H hindex q.1 q.2 rho v hvquad hvfirst hvsecond hrho hv
        hrho_radius z


-- @@ L4955-4955 verbatim
end EmbeddedShrink


-- @@ L4957-4957 verbatim
end StandardMorseEventAt


-- @@ L4959-4959 verbatim
namespace SimpleClosedOrbitParam.CyclicMarking


-- @@ L4961-4961 verbatim
variable {C₁ : FramedLevelCobordism n}

-- @@ L4962-4962 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L4963-4963 verbatim
variable {M₁ : StandardMorseEventAt (n := n) C₁ center}

-- @@ L4964-4964 verbatim
variable {s₁ : ℝ} {hreg₁ : sliceRegular C₁.G s₁}

-- @@ L4965-4966 verbatim
variable {V₁ : TamedField
  (SlabTamedField.sliceFLSAt C₁.toLevelCobordismData s₁ hreg₁)}

-- @@ L4967-4968 verbatim
variable {P₁ : SimpleClosedOrbitParam
  (SlabTamedField.sliceFLSAt C₁.toLevelCobordismData s₁ hreg₁) V₁}

-- @@ L4969-4969 verbatim
variable {k₁ : ℕ}


-- @@ L4971-4977 verbatim
/-- A single compact core containing every ambient indexed cut of one cyclic
marking.  Choosing the union, rather than a separate core for each cut, gives
one common flow with which endpoint pairings can later be compared. -/
def cyclicCutFamilyAmbientCore
    (A : P₁.CyclicMarking k₁) :
    Set (EuclideanSpace ℝ (Fin (n + 2))) :=
  ⋃ i : Fin (k₁ + 1), Set.range (A.cyclicCutAmbientPath i)


-- @@ L4979-4983 verbatim
theorem cyclicCutAmbientPath_mem_familyCore
    (A : P₁.CyclicMarking k₁) (i : Fin (k₁ + 1)) (u : I) :
    A.cyclicCutAmbientPath i u ∈ A.cyclicCutFamilyAmbientCore := by
  apply Set.mem_iUnion.2
  exact ⟨i, ⟨u, rfl⟩⟩


-- @@ L4985-4990 verbatim
theorem isCompact_cyclicCutFamilyAmbientCore
    (A : P₁.CyclicMarking k₁) :
    IsCompact A.cyclicCutFamilyAmbientCore := by
  apply isCompact_iUnion
  intro i
  exact isCompact_range (A.cyclicCutAmbientPath i).continuous


-- @@ L4992-5000 verbatim
theorem cyclicCutFamilyAmbientCore_subset_slabRegularSet
    (A : P₁.CyclicMarking k₁) :
    A.cyclicCutFamilyAmbientCore ⊆
      slabRegularSet C₁.toLevelCobordismData.G := by
  intro z hz
  obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp hz
  apply mem_slabRegularSet_of_spatial_surjective
  · exact C₁.regular _ (A.cyclicCutAmbientPath_fiber i u)
  · exact A.cyclicCutAmbientPath_regular i u


-- @@ L5002-5010 verbatim
/-- The canonical common compact time field attached to all cuts of the
marking.  Its safe time is positive by construction. -/
noncomputable def cyclicCutFamilyTimeField
    (A : P₁.CyclicMarking k₁) :
    CompactTimeTamedField C₁.toLevelCobordismData
      A.cyclicCutFamilyAmbientCore :=
  (exists_compactTimeTamedField C₁.toLevelCobordismData
    A.isCompact_cyclicCutFamilyAmbientCore
    A.cyclicCutFamilyAmbientCore_subset_slabRegularSet).some


-- @@ L5012-5040 verbatim
/-- Specialized safe-flow bridge for one uniformly indexed cyclic cut.  The
only remaining inputs are the quantitative core/safe-time facts and the two
endpoint captures; the path, zero-fiber condition, and spatial regularity are
already supplied by the cyclic marking. -/
noncomputable def cyclicCutCriticalExteriorArc
    (A : P₁.CyclicMarking k₁) (i : Fin (k₁ + 1))
    {K : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (R : CompactTimeTamedField C₁.toLevelCobordismData K)
    (hcutK : ∀ u : I, A.cyclicCutAmbientPath i u ∈ K)
    (d : ℝ) (hd : |d| ≤ R.safeTime)
    (htime : s₁ + d = tcoord center)
    (rho : ℝ) (p q : SaddleBranch × SaddleBranch)
    (hsource : R.base.flow
      (cobSpaceTime (A.point (A.cyclicCutSourceLabel i)) s₁) d =
        M₁.saddleCriticalBoundaryEnd p rho)
    (htarget : R.base.flow
      (cobSpaceTime (A.point (A.cyclicCutTargetLabel i)) s₁) d =
        M₁.saddleCriticalBoundaryEnd q rho) :
    SaddleCriticalExteriorArc
      (fun r => M₁.saddleCriticalBoundaryEnd r rho)
      (StandardMorseEventAt.puncturedCriticalSlice C₁ center) p q :=
  M₁.saddleCriticalExteriorArcOfSafeFlow R
    (A.cyclicCutRegularZeroPath i) hcutK d hd
    (fun u => by
      change tcoord (A.cyclicCutAmbientPath i u) + d = tcoord center
      rw [show tcoord (A.cyclicCutAmbientPath i u) = s₁ by
        simp [cyclicCutAmbientPath]]
      exact htime)
    rho p q hsource htarget


-- @@ L5042-5061 verbatim
/-- Canonical-core version of `cyclicCutCriticalExteriorArc`: all core
membership and field-existence obligations are discharged for the entire cut
family at once. -/
noncomputable def cyclicCutCriticalExteriorArcOfFamilyFlow
    (A : P₁.CyclicMarking k₁) (i : Fin (k₁ + 1))
    (d : ℝ) (hd : |d| ≤ A.cyclicCutFamilyTimeField.safeTime)
    (htime : s₁ + d = tcoord center)
    (rho : ℝ) (p q : SaddleBranch × SaddleBranch)
    (hsource : A.cyclicCutFamilyTimeField.base.flow
      (cobSpaceTime (A.point (A.cyclicCutSourceLabel i)) s₁) d =
        M₁.saddleCriticalBoundaryEnd p rho)
    (htarget : A.cyclicCutFamilyTimeField.base.flow
      (cobSpaceTime (A.point (A.cyclicCutTargetLabel i)) s₁) d =
        M₁.saddleCriticalBoundaryEnd q rho) :
    SaddleCriticalExteriorArc
      (fun r => M₁.saddleCriticalBoundaryEnd r rho)
      (StandardMorseEventAt.puncturedCriticalSlice C₁ center) p q :=
  A.cyclicCutCriticalExteriorArc i A.cyclicCutFamilyTimeField
    (A.cyclicCutAmbientPath_mem_familyCore i) d hd htime
    rho p q hsource htarget


-- @@ L5063-5063 verbatim
end SimpleClosedOrbitParam.CyclicMarking


-- @@ L5065-5065 verbatim
/-! ## Actual two-end markings on the regular saddle branch orbits -/


-- @@ L5067-5067 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L5069-5069 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L5071-5084 verbatim
/-- Intrinsic once-around parametrization of one actual positive branch
orbit. -/
noncomputable def saddlePositiveBranchOrbitParam
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    SimpleClosedOrbitParam (T.saddlePositiveSlice a hreg) V :=
  V.intrinsicSimpleClosedOrbitParam
    (T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
      hrho_radius hreg V)


-- @@ L5086-5124 verbatim
/-- The two actual chart-boundary ends of one positive local branch, marked
on the intrinsic once-around parametrization of its complete orbit. -/
noncomputable def saddlePositiveBranchCyclicMarking
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    (T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
      hrho_radius hreg V).CyclicMarking 1 where
  point i := spacePart (M.saddlePositiveBoundaryEnd b
    (saddleBranchOfFinTwo i) rho a)
  point_injective := by
    intro i j hij
    change spacePart (M.saddlePositiveBoundaryEnd b
      (saddleBranchOfFinTwo i) rho a) =
        spacePart (M.saddlePositiveBoundaryEnd b
          (saddleBranchOfFinTwo j) rho a) at hij
    apply saddleBranchOfFinTwo_injective
    have hinj := T.saddlePositiveSpatialBoundaryEnd_injective hindex
      hrho ha hrho_radius
    have hpairs : (b, saddleBranchOfFinTwo i) =
        (b, saddleBranchOfFinTwo j) := hinj hij
    exact congrArg Prod.snd hpairs
  point_mem_orbit := by
    intro i
    let O := T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
      hrho_radius hreg V
    have hmem := T.saddlePositiveSpatialBoundaryEnd_mem_branchOrbit
      hindex b (saddleBranchOfFinTwo i) rho a hrho ha hrho_radius hreg V
    change spacePart (M.saddlePositiveBoundaryEnd b
      (saddleBranchOfFinTwo i) rho a) ∈ V.orbit (V.orbitPoint O)
    rw [← V.orbitPoint_orbit O]
    change spacePart (M.saddlePositiveBoundaryEnd b
      (saddleBranchOfFinTwo i) rho a) ∈
        V.orbit (spacePart (T.saddlePositiveBranchBase b rho a))
    exact hmem


-- @@ L5126-5138 verbatim
theorem saddlePositiveSpatialSegment_mem_paramOrbit
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) (u : I) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u ∈
      V.orbit ((T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
        hrho_radius hreg V).p) := by
  exact T.saddlePositiveSpatialSegment_mem_branchOrbit hindex b rho a
    hrho ha hrho_radius hreg V u


-- @@ L5140-5165 verbatim
/-- The source of the actual positive local arc is the negative-end mark on
its intrinsic orbit parameter. -/
theorem saddlePositiveSpatialSegment_zero_eq_curve_mark
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius 0 =
      (T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
        hrho_radius hreg V).curve
        ((T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
          hrho_radius hreg V).mark 0) := by
  let P := T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  calc
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius 0 =
        spacePart (M.saddlePositiveBoundaryEnd b .negative rho a) := by
      simp [saddlePositiveSpatialSegment]
    _ = A.point 0 := by
      simp [A, saddlePositiveBranchCyclicMarking]
    _ = P.curve (A.mark 0) := (A.curve_mark 0).symm


-- @@ L5167-5191 verbatim
/-- The target is the positive-end mark. -/
theorem saddlePositiveSpatialSegment_one_eq_curve_mark
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius 1 =
      (T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
        hrho_radius hreg V).curve
        ((T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
          hrho_radius hreg V).mark 1) := by
  let P := T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  calc
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius 1 =
        spacePart (M.saddlePositiveBoundaryEnd b .positive rho a) := by
      simp [saddlePositiveSpatialSegment]
    _ = A.point 1 := by
      simp [A, saddlePositiveBranchCyclicMarking]
    _ = P.curve (A.mark 1) := (A.curve_mark 1).symm


-- @@ L5193-5213 verbatim
/-- Real phase lift of the actual positive local saddle branch, anchored at
its negative boundary mark. -/
noncomputable def saddlePositiveSegmentPhaseLift
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) : C(I, ℝ) := by
  let P := T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  let hgamma : ∀ u, gamma u ∈ V.orbit P.p :=
    fun u => T.saddlePositiveSpatialSegment_mem_paramOrbit hindex b rho a
      hrho ha hrho_radius hreg V u
  let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  exact P.phaseLiftOfOrbitPathAtCurve gamma hgamma (A.mark 0)
    (T.saddlePositiveSpatialSegment_zero_eq_curve_mark hindex b rho a
      hrho ha hrho_radius hreg V)


-- @@ L5215-5229 verbatim
@[simp] theorem saddlePositiveSegmentPhaseLift_zero
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    T.saddlePositiveSegmentPhaseLift hindex b rho a hrho ha
      hrho_radius hreg V 0 =
    (T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
      hrho_radius hreg V).phaseLift
      ((T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
        hrho_radius hreg V).mark 0) := by
  simp [saddlePositiveSegmentPhaseLift]


-- @@ L5231-5270 verbatim
theorem saddlePositiveSegmentPhaseLift_one_coe
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    ((T.saddlePositiveSegmentPhaseLift hindex b rho a hrho ha
        hrho_radius hreg V 1 : ℝ) :
      AddCircle (V.fundamentalPeriod
        (T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
          hrho_radius hreg V).hp)) =
    (T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
      hrho_radius hreg V).phase
      ((T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
        hrho_radius hreg V).mark 1) := by
  let P := T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  let hgamma : ∀ u, gamma u ∈ V.orbit P.p :=
    fun u => T.saddlePositiveSpatialSegment_mem_paramOrbit hindex b rho a
      hrho ha hrho_radius hreg V u
  let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  let hsource : gamma 0 = P.curve (A.mark 0) :=
    T.saddlePositiveSpatialSegment_zero_eq_curve_mark hindex b rho a
      hrho ha hrho_radius hreg V
  have hcoe := P.phaseLiftOfOrbitPathAtCurve_coe gamma hgamma
    (A.mark 0) hsource 1
  have htarget := P.phaseOfOrbitPath_eq_phase_of_eq gamma hgamma
    (T.saddlePositiveSpatialSegment_one_eq_curve_mark hindex b rho a
      hrho ha hrho_radius hreg V)
  calc
    ((T.saddlePositiveSegmentPhaseLift hindex b rho a hrho ha
          hrho_radius hreg V 1 : ℝ) :
        AddCircle (V.fundamentalPeriod P.hp)) =
        P.phaseOfOrbitPath gamma hgamma 1 := by
      simpa only [saddlePositiveSegmentPhaseLift] using hcoe
    _ = P.phase (A.mark 1) := htarget


-- @@ L5272-5297 verbatim
theorem saddlePositiveSegmentPhaseLift_strictMono_or_strictAnti
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    StrictMono (T.saddlePositiveSegmentPhaseLift hindex b rho a hrho ha
      hrho_radius hreg V) ∨
    StrictAnti (T.saddlePositiveSegmentPhaseLift hindex b rho a hrho ha
      hrho_radius hreg V) := by
  let P := T.saddlePositiveBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  let hgamma : ∀ u, gamma u ∈ V.orbit P.p :=
    fun u => T.saddlePositiveSpatialSegment_mem_paramOrbit hindex b rho a
      hrho ha hrho_radius hreg V u
  let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  simpa only [saddlePositiveSegmentPhaseLift] using
    P.phaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti gamma hgamma
      (T.saddlePositiveSpatialSegment_injective hindex b rho a hrho ha
        hrho_radius) (A.mark 0)
      (T.saddlePositiveSpatialSegment_zero_eq_curve_mark hindex b rho a
        hrho ha hrho_radius hreg V)


-- @@ L5299-5323 verbatim
/-- No marked boundary point occurs in the interior of the actual positive
local branch arc. -/
theorem saddlePositiveSpatialSegment_ne_branchMark_of_mem_Ioo
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    {u : I} (hu : u ∈ Set.Ioo 0 1) (i : Fin 2) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u ≠
      (T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
        hrho_radius hreg V).point i := by
  intro heq
  have hboundary :
      T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u =
        spacePart (M.saddlePositiveBoundaryEnd b
          (saddleBranchOfFinTwo i) rho a) := by
    simpa [saddlePositiveBranchCyclicMarking] using heq
  rcases (T.saddlePositiveSpatialSegment_eq_boundaryEnd_iff hindex b
    (b, saddleBranchOfFinTwo i) rho a hrho ha hrho_radius u).mp hboundary with
    hzero | hone
  · exact (ne_of_gt hu.1) hzero.1
  · exact (ne_of_lt hu.2) hone.1


-- @@ L5325-5356 verbatim
/-- On a two-mark branch orbit, the actual positive local segment is exactly
one of the two explicit cyclic cuts. -/
theorem saddlePositiveBranch_localSegment_range_eq_cut
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
      hrho_radius hreg V
    Set.range (T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius) =
        Set.range (A.adjacentSubpath 0) ∨
      Set.range (T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius) =
        Set.range A.wrapSubpath := by
  dsimp only
  let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  apply A.range_eq_adjacentSubpath_or_wrap_of_embedded_arc_two gamma
    (fun u => T.saddlePositiveSpatialSegment_mem_paramOrbit hindex b rho a
      hrho ha hrho_radius hreg V u)
    (T.saddlePositiveSpatialSegment_injective hindex b rho a hrho ha
      hrho_radius) 0 1
  · simp [gamma, A, saddlePositiveSpatialSegment,
      saddlePositiveBranchCyclicMarking]
  · simp [gamma, A, saddlePositiveSpatialSegment,
      saddlePositiveBranchCyclicMarking]
  · intro u hu i
    exact T.saddlePositiveSpatialSegment_ne_branchMark_of_mem_Ioo hindex
      b rho a hrho ha hrho_radius hreg V hu i


-- @@ L5358-5371 verbatim
/-- Intrinsic once-around parametrization of one actual negative branch
orbit. -/
noncomputable def saddleNegativeBranchOrbitParam
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    SimpleClosedOrbitParam (T.saddleNegativeSlice a hreg) V :=
  V.intrinsicSimpleClosedOrbitParam
    (T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
      hrho_radius hreg V)


-- @@ L5373-5411 verbatim
/-- The two actual chart-boundary ends of one negative local branch, marked
on its complete orbit. -/
noncomputable def saddleNegativeBranchCyclicMarking
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    (T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
      hrho_radius hreg V).CyclicMarking 1 where
  point i := spacePart (M.saddleNegativeBoundaryEnd b
    (saddleBranchOfFinTwo i) rho a)
  point_injective := by
    intro i j hij
    change spacePart (M.saddleNegativeBoundaryEnd b
      (saddleBranchOfFinTwo i) rho a) =
        spacePart (M.saddleNegativeBoundaryEnd b
          (saddleBranchOfFinTwo j) rho a) at hij
    apply saddleBranchOfFinTwo_injective
    have hinj := T.saddleNegativeSpatialBoundaryEnd_injective hindex
      hrho ha hrho_radius
    have hpairs : (b, saddleBranchOfFinTwo i) =
        (b, saddleBranchOfFinTwo j) := hinj hij
    exact congrArg Prod.snd hpairs
  point_mem_orbit := by
    intro i
    let O := T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
      hrho_radius hreg V
    have hmem := T.saddleNegativeSpatialBoundaryEnd_mem_branchOrbit
      hindex b (saddleBranchOfFinTwo i) rho a hrho ha hrho_radius hreg V
    change spacePart (M.saddleNegativeBoundaryEnd b
      (saddleBranchOfFinTwo i) rho a) ∈ V.orbit (V.orbitPoint O)
    rw [← V.orbitPoint_orbit O]
    change spacePart (M.saddleNegativeBoundaryEnd b
      (saddleBranchOfFinTwo i) rho a) ∈
        V.orbit (spacePart (T.saddleNegativeBranchBase b rho a))
    exact hmem


-- @@ L5413-5425 verbatim
theorem saddleNegativeSpatialSegment_mem_paramOrbit
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) (u : I) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u ∈
      V.orbit ((T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
        hrho_radius hreg V).p) := by
  exact T.saddleNegativeSpatialSegment_mem_branchOrbit hindex b rho a
    hrho ha hrho_radius hreg V u


-- @@ L5427-5450 verbatim
theorem saddleNegativeSpatialSegment_zero_eq_curve_mark
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius 0 =
      (T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
        hrho_radius hreg V).curve
        ((T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
          hrho_radius hreg V).mark 0) := by
  let P := T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  calc
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius 0 =
        spacePart (M.saddleNegativeBoundaryEnd b .negative rho a) := by
      simp [saddleNegativeSpatialSegment]
    _ = A.point 0 := by
      simp [A, saddleNegativeBranchCyclicMarking]
    _ = P.curve (A.mark 0) := (A.curve_mark 0).symm


-- @@ L5452-5475 verbatim
theorem saddleNegativeSpatialSegment_one_eq_curve_mark
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius 1 =
      (T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
        hrho_radius hreg V).curve
        ((T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
          hrho_radius hreg V).mark 1) := by
  let P := T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  calc
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius 1 =
        spacePart (M.saddleNegativeBoundaryEnd b .positive rho a) := by
      simp [saddleNegativeSpatialSegment]
    _ = A.point 1 := by
      simp [A, saddleNegativeBranchCyclicMarking]
    _ = P.curve (A.mark 1) := (A.curve_mark 1).symm


-- @@ L5477-5496 verbatim
/-- Real phase lift of the actual negative local saddle branch. -/
noncomputable def saddleNegativeSegmentPhaseLift
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) : C(I, ℝ) := by
  let P := T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  let hgamma : ∀ u, gamma u ∈ V.orbit P.p :=
    fun u => T.saddleNegativeSpatialSegment_mem_paramOrbit hindex b rho a
      hrho ha hrho_radius hreg V u
  let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  exact P.phaseLiftOfOrbitPathAtCurve gamma hgamma (A.mark 0)
    (T.saddleNegativeSpatialSegment_zero_eq_curve_mark hindex b rho a
      hrho ha hrho_radius hreg V)


-- @@ L5498-5512 verbatim
@[simp] theorem saddleNegativeSegmentPhaseLift_zero
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    T.saddleNegativeSegmentPhaseLift hindex b rho a hrho ha
      hrho_radius hreg V 0 =
    (T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
      hrho_radius hreg V).phaseLift
      ((T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
        hrho_radius hreg V).mark 0) := by
  simp [saddleNegativeSegmentPhaseLift]


-- @@ L5514-5539 verbatim
theorem saddleNegativeSegmentPhaseLift_strictMono_or_strictAnti
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    StrictMono (T.saddleNegativeSegmentPhaseLift hindex b rho a hrho ha
      hrho_radius hreg V) ∨
    StrictAnti (T.saddleNegativeSegmentPhaseLift hindex b rho a hrho ha
      hrho_radius hreg V) := by
  let P := T.saddleNegativeBranchOrbitParam hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  let hgamma : ∀ u, gamma u ∈ V.orbit P.p :=
    fun u => T.saddleNegativeSpatialSegment_mem_paramOrbit hindex b rho a
      hrho ha hrho_radius hreg V u
  let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  simpa only [saddleNegativeSegmentPhaseLift] using
    P.phaseLiftOfOrbitPathAtCurve_strictMono_or_strictAnti gamma hgamma
      (T.saddleNegativeSpatialSegment_injective hindex b rho a hrho ha
        hrho_radius) (A.mark 0)
      (T.saddleNegativeSpatialSegment_zero_eq_curve_mark hindex b rho a
        hrho ha hrho_radius hreg V)


-- @@ L5541-5563 verbatim
theorem saddleNegativeSpatialSegment_ne_branchMark_of_mem_Ioo
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    {u : I} (hu : u ∈ Set.Ioo 0 1) (i : Fin 2) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u ≠
      (T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
        hrho_radius hreg V).point i := by
  intro heq
  have hboundary :
      T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u =
        spacePart (M.saddleNegativeBoundaryEnd b
          (saddleBranchOfFinTwo i) rho a) := by
    simpa [saddleNegativeBranchCyclicMarking] using heq
  rcases (T.saddleNegativeSpatialSegment_eq_boundaryEnd_iff hindex b
    (b, saddleBranchOfFinTwo i) rho a hrho ha hrho_radius u).mp hboundary with
    hzero | hone
  · exact (ne_of_gt hu.1) hzero.1
  · exact (ne_of_lt hu.2) hone.1


-- @@ L5565-5595 verbatim
/-- Negative two-mark branch-orbit cut identification. -/
theorem saddleNegativeBranch_localSegment_range_eq_cut
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
      hrho_radius hreg V
    Set.range (T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius) =
        Set.range (A.adjacentSubpath 0) ∨
      Set.range (T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius) =
        Set.range A.wrapSubpath := by
  dsimp only
  let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  apply A.range_eq_adjacentSubpath_or_wrap_of_embedded_arc_two gamma
    (fun u => T.saddleNegativeSpatialSegment_mem_paramOrbit hindex b rho a
      hrho ha hrho_radius hreg V u)
    (T.saddleNegativeSpatialSegment_injective hindex b rho a hrho ha
      hrho_radius) 0 1
  · simp [gamma, A, saddleNegativeSpatialSegment,
      saddleNegativeBranchCyclicMarking]
  · simp [gamma, A, saddleNegativeSpatialSegment,
      saddleNegativeBranchCyclicMarking]
  · intro u hu i
    exact T.saddleNegativeSpatialSegment_ne_branchMark_of_mem_Ioo hindex
      b rho a hrho ha hrho_radius hreg V hu i


-- @@ L5597-5637 verbatim
/-- If the two positive branch orbits are distinct, the cyclic cut
complementary to the local segment contains no strictly interior chart point
of that orbit.  The disjunction records which of the two explicit cuts is
the local one. -/
theorem saddlePositiveBranch_complementCut_avoids_openChartPoint
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha0 : 0 < a) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (hne : T.saddlePositiveBranchOrbitIndex hindex .negative rho a hrho ha
        hrho_radius hreg V ≠
      T.saddlePositiveBranchOrbitIndex hindex .positive rho a hrho ha
        hrho_radius hreg V)
    (u : E₂) (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hnorm : ‖u‖ < rho)
    (horbit : spacePart (M.param u) ∈
      ((T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
        hrho_radius hreg V : V.OrbitIndex) : Set E₁)) :
    let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
      hrho_radius hreg V
    (Set.range (T.saddlePositiveSpatialSegment b rho a hrho ha
          hrho_radius) = Set.range (A.adjacentSubpath 0) ∧
        spacePart (M.param u) ∉ Set.range A.wrapSubpath) ∨
      (Set.range (T.saddlePositiveSpatialSegment b rho a hrho ha
          hrho_radius) = Set.range A.wrapSubpath ∧
        spacePart (M.param u) ∉ Set.range (A.adjacentSubpath 0)) := by
  dsimp only
  let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  apply A.two_cut_complement_avoids_local_unmarked_point gamma
  · exact T.saddlePositiveBranch_localSegment_range_eq_cut hindex b rho a
      hrho ha hrho_radius hreg V
  · exact T.spacePart_param_mem_own_saddlePositiveSpatialSegment hindex b
      rho a hrho ha0 ha hrho_radius hreg V hne u hquad hnorm.le horbit
  · intro l
    apply T.spacePart_param_ne_saddlePositiveBoundaryEnd_of_norm_lt hindex
      (b, saddleBranchOfFinTwo l) rho a hrho ha hrho_radius u hquad hnorm


-- @@ L5639-5676 verbatim
/-- Negative-side distinct-orbit complementary-cut exclusion. -/
theorem saddleNegativeBranch_complementCut_avoids_openChartPoint
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha0 : 0 < a) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (hne : T.saddleNegativeBranchOrbitIndex hindex .negative rho a hrho ha
        hrho_radius hreg V ≠
      T.saddleNegativeBranchOrbitIndex hindex .positive rho a hrho ha
        hrho_radius hreg V)
    (u : E₂) (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hnorm : ‖u‖ < rho)
    (horbit : spacePart (M.param u) ∈
      ((T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
        hrho_radius hreg V : V.OrbitIndex) : Set E₁)) :
    let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
      hrho_radius hreg V
    (Set.range (T.saddleNegativeSpatialSegment b rho a hrho ha
          hrho_radius) = Set.range (A.adjacentSubpath 0) ∧
        spacePart (M.param u) ∉ Set.range A.wrapSubpath) ∨
      (Set.range (T.saddleNegativeSpatialSegment b rho a hrho ha
          hrho_radius) = Set.range A.wrapSubpath ∧
        spacePart (M.param u) ∉ Set.range (A.adjacentSubpath 0)) := by
  dsimp only
  let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  apply A.two_cut_complement_avoids_local_unmarked_point gamma
  · exact T.saddleNegativeBranch_localSegment_range_eq_cut hindex b rho a
      hrho ha hrho_radius hreg V
  · exact T.spacePart_param_mem_own_saddleNegativeSpatialSegment hindex b
      rho a hrho ha0 ha hrho_radius hreg V hne u hquad hnorm.le horbit
  · intro l
    apply T.spacePart_param_ne_saddleNegativeBoundaryEnd_of_norm_lt hindex
      (b, saddleBranchOfFinTwo l) rho a hrho ha hrho_radius u hquad hnorm


-- @@ L5678-5735 verbatim
/-- Uniform distinct-positive-orbit exterior cut: decide the local cut once,
then its complement avoids every open-chart point on that branch orbit. -/
theorem saddlePositiveBranch_exists_uniformExteriorCut
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha0 : 0 < a) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (hne : T.saddlePositiveBranchOrbitIndex hindex .negative rho a hrho ha
        hrho_radius hreg V ≠
      T.saddlePositiveBranchOrbitIndex hindex .positive rho a hrho ha
        hrho_radius hreg V) :
    let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
      hrho_radius hreg V
    (Set.range (T.saddlePositiveSpatialSegment b rho a hrho ha
          hrho_radius) = Set.range (A.adjacentSubpath 0) ∧
        ∀ u : E₂, morseQuadratic .saddle (u 0, u 1) = a ^ 2 →
          ‖u‖ < rho →
          spacePart (M.param u) ∈
            ((T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
              hrho_radius hreg V : V.OrbitIndex) : Set E₁) →
          spacePart (M.param u) ∉ Set.range A.wrapSubpath) ∨
      (Set.range (T.saddlePositiveSpatialSegment b rho a hrho ha
          hrho_radius) = Set.range A.wrapSubpath ∧
        ∀ u : E₂, morseQuadratic .saddle (u 0, u 1) = a ^ 2 →
          ‖u‖ < rho →
          spacePart (M.param u) ∈
            ((T.saddlePositiveBranchOrbitIndex hindex b rho a hrho ha
              hrho_radius hreg V : V.OrbitIndex) : Set E₁) →
          spacePart (M.param u) ∉ Set.range (A.adjacentSubpath 0)) := by
  dsimp only
  let A := T.saddlePositiveBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  have H := A.two_cut_complement_avoids_all_local_unmarked gamma
    (T.saddlePositiveBranch_localSegment_range_eq_cut hindex b rho a hrho ha
      hrho_radius hreg V)
  rcases H with ⟨hlocal, havoid⟩ | ⟨hlocal, havoid⟩
  · left
    refine ⟨hlocal, ?_⟩
    intro u hquad hnorm horbit
    apply havoid
    · exact T.spacePart_param_mem_own_saddlePositiveSpatialSegment hindex b
        rho a hrho ha0 ha hrho_radius hreg V hne u hquad hnorm.le horbit
    · intro l
      apply T.spacePart_param_ne_saddlePositiveBoundaryEnd_of_norm_lt hindex
        (b, saddleBranchOfFinTwo l) rho a hrho ha hrho_radius u hquad hnorm
  · right
    refine ⟨hlocal, ?_⟩
    intro u hquad hnorm horbit
    apply havoid
    · exact T.spacePart_param_mem_own_saddlePositiveSpatialSegment hindex b
        rho a hrho ha0 ha hrho_radius hreg V hne u hquad hnorm.le horbit
    · intro l
      apply T.spacePart_param_ne_saddlePositiveBoundaryEnd_of_norm_lt hindex
        (b, saddleBranchOfFinTwo l) rho a hrho ha hrho_radius u hquad hnorm


-- @@ L5737-5793 verbatim
/-- Uniform distinct-negative-orbit exterior cut. -/
theorem saddleNegativeBranch_exists_uniformExteriorCut
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (b : SaddleBranch) (rho a : ℝ)
    (hrho : 0 < rho) (ha0 : 0 < a) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (hne : T.saddleNegativeBranchOrbitIndex hindex .negative rho a hrho ha
        hrho_radius hreg V ≠
      T.saddleNegativeBranchOrbitIndex hindex .positive rho a hrho ha
        hrho_radius hreg V) :
    let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
      hrho_radius hreg V
    (Set.range (T.saddleNegativeSpatialSegment b rho a hrho ha
          hrho_radius) = Set.range (A.adjacentSubpath 0) ∧
        ∀ u : E₂, morseQuadratic .saddle (u 0, u 1) = -(a ^ 2) →
          ‖u‖ < rho →
          spacePart (M.param u) ∈
            ((T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
              hrho_radius hreg V : V.OrbitIndex) : Set E₁) →
          spacePart (M.param u) ∉ Set.range A.wrapSubpath) ∨
      (Set.range (T.saddleNegativeSpatialSegment b rho a hrho ha
          hrho_radius) = Set.range A.wrapSubpath ∧
        ∀ u : E₂, morseQuadratic .saddle (u 0, u 1) = -(a ^ 2) →
          ‖u‖ < rho →
          spacePart (M.param u) ∈
            ((T.saddleNegativeBranchOrbitIndex hindex b rho a hrho ha
              hrho_radius hreg V : V.OrbitIndex) : Set E₁) →
          spacePart (M.param u) ∉ Set.range (A.adjacentSubpath 0)) := by
  dsimp only
  let A := T.saddleNegativeBranchCyclicMarking hindex b rho a hrho ha
    hrho_radius hreg V
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  have H := A.two_cut_complement_avoids_all_local_unmarked gamma
    (T.saddleNegativeBranch_localSegment_range_eq_cut hindex b rho a hrho ha
      hrho_radius hreg V)
  rcases H with ⟨hlocal, havoid⟩ | ⟨hlocal, havoid⟩
  · left
    refine ⟨hlocal, ?_⟩
    intro u hquad hnorm horbit
    apply havoid
    · exact T.spacePart_param_mem_own_saddleNegativeSpatialSegment hindex b
        rho a hrho ha0 ha hrho_radius hreg V hne u hquad hnorm.le horbit
    · intro l
      apply T.spacePart_param_ne_saddleNegativeBoundaryEnd_of_norm_lt hindex
        (b, saddleBranchOfFinTwo l) rho a hrho ha hrho_radius u hquad hnorm
  · right
    refine ⟨hlocal, ?_⟩
    intro u hquad hnorm horbit
    apply havoid
    · exact T.spacePart_param_mem_own_saddleNegativeSpatialSegment hindex b
        rho a hrho ha0 ha hrho_radius hreg V hne u hquad hnorm.le horbit
    · intro l
      apply T.spacePart_param_ne_saddleNegativeBoundaryEnd_of_norm_lt hindex
        (b, saddleBranchOfFinTwo l) rho a hrho ha hrho_radius u hquad hnorm


-- @@ L5795-5841 verbatim
/-- If the two positive local branches belong to one global orbit, mark all
four chart ends on that single intrinsic circle. -/
noncomputable def saddlePositiveCommonOrbitCyclicMarking
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (horbit : T.saddlePositiveBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddlePositiveBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V) :
    (T.saddlePositiveBranchOrbitParam hindex .negative rho a hrho ha
      hrho_radius hreg V).CyclicMarking 3 where
  point i :=
    let p := saddleBranchPairOfFinFour i
    spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a)
  point_injective := by
    intro i j hij
    apply saddleBranchPairOfFinFour_injective
    have hinj := T.saddlePositiveSpatialBoundaryEnd_injective hindex
      hrho ha hrho_radius
    exact hinj hij
  point_mem_orbit := by
    intro i
    let p := saddleBranchPairOfFinFour i
    let Ominus := T.saddlePositiveBranchOrbitIndex hindex .negative
      rho a hrho ha hrho_radius hreg V
    let Obranch := T.saddlePositiveBranchOrbitIndex hindex p.1
      rho a hrho ha hrho_radius hreg V
    have hmem := T.saddlePositiveSpatialBoundaryEnd_mem_branchOrbit
      hindex p.1 p.2 rho a hrho ha hrho_radius hreg V
    have hmem' : spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a) ∈
        (Obranch : Set E₁) := by
      change spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a) ∈
        V.orbit (spacePart (T.saddlePositiveBranchBase p.1 rho a))
      exact hmem
    have hO : Obranch = Ominus := by
      cases hp : p.1 with
      | positive =>
          simpa only [Obranch, Ominus, hp] using horbit.symm
      | negative => simp only [Obranch, Ominus, hp]
    change spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a) ∈
      V.orbit (V.orbitPoint Ominus)
    rw [← V.orbitPoint_orbit Ominus, ← hO]
    exact hmem'


-- @@ L5843-5896 verbatim
/-- If the two negative local branches belong to one global orbit, mark all
four ends using the critical-label swap `(branch,end) = (p.2,p.1)`. -/
noncomputable def saddleNegativeCommonOrbitCyclicMarking
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (horbit : T.saddleNegativeBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddleNegativeBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V) :
    (T.saddleNegativeBranchOrbitParam hindex .negative rho a hrho ha
      hrho_radius hreg V).CyclicMarking 3 where
  point i :=
    let p := saddleBranchPairOfFinFour i
    spacePart (M.saddleNegativeBoundaryEnd p.2 p.1 rho a)
  point_injective := by
    intro i j hij
    apply saddleBranchPairOfFinFour_injective
    have hinj := T.saddleNegativeSpatialBoundaryEnd_injective hindex
      hrho ha hrho_radius
    have hswap :
        ((saddleBranchPairOfFinFour i).2,
          (saddleBranchPairOfFinFour i).1) =
        ((saddleBranchPairOfFinFour j).2,
          (saddleBranchPairOfFinFour j).1) := hinj hij
    apply Prod.ext
    · exact congrArg Prod.snd hswap
    · exact congrArg Prod.fst hswap
  point_mem_orbit := by
    intro i
    let p := saddleBranchPairOfFinFour i
    let Ominus := T.saddleNegativeBranchOrbitIndex hindex .negative
      rho a hrho ha hrho_radius hreg V
    let Obranch := T.saddleNegativeBranchOrbitIndex hindex p.2
      rho a hrho ha hrho_radius hreg V
    have hmem := T.saddleNegativeSpatialBoundaryEnd_mem_branchOrbit
      hindex p.2 p.1 rho a hrho ha hrho_radius hreg V
    have hmem' : spacePart (M.saddleNegativeBoundaryEnd p.2 p.1 rho a) ∈
        (Obranch : Set E₁) := by
      change spacePart (M.saddleNegativeBoundaryEnd p.2 p.1 rho a) ∈
        V.orbit (spacePart (T.saddleNegativeBranchBase p.2 rho a))
      exact hmem
    have hO : Obranch = Ominus := by
      cases hp : p.2 with
      | positive =>
          simpa only [Obranch, Ominus, hp] using horbit.symm
      | negative => simp only [Obranch, Ominus, hp]
    change spacePart (M.saddleNegativeBoundaryEnd p.2 p.1 rho a) ∈
      V.orbit (V.orbitPoint Ominus)
    rw [← V.orbitPoint_orbit Ominus, ← hO]
    exact hmem'


-- @@ L5898-5923 verbatim
theorem saddlePositiveSpatialSegment_mem_commonParamOrbit
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (horbit : T.saddlePositiveBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddlePositiveBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (b : SaddleBranch) (u : I) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u ∈
      V.orbit ((T.saddlePositiveBranchOrbitParam hindex .negative rho a
        hrho ha hrho_radius hreg V).p) := by
  have hmem := T.saddlePositiveSpatialSegment_mem_paramOrbit hindex b
    rho a hrho ha hrho_radius hreg V u
  cases b with
  | negative => exact hmem
  | positive =>
      change T.saddlePositiveSpatialSegment .positive rho a hrho ha
        hrho_radius u ∈ V.orbit
          (V.orbitPoint (T.saddlePositiveBranchOrbitIndex hindex .negative
            rho a hrho ha hrho_radius hreg V))
      rw [horbit]
      exact hmem


-- @@ L5925-5950 verbatim
theorem saddleNegativeSpatialSegment_mem_commonParamOrbit
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (horbit : T.saddleNegativeBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddleNegativeBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (b : SaddleBranch) (u : I) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u ∈
      V.orbit ((T.saddleNegativeBranchOrbitParam hindex .negative rho a
        hrho ha hrho_radius hreg V).p) := by
  have hmem := T.saddleNegativeSpatialSegment_mem_paramOrbit hindex b
    rho a hrho ha hrho_radius hreg V u
  cases b with
  | negative => exact hmem
  | positive =>
      change T.saddleNegativeSpatialSegment .positive rho a hrho ha
        hrho_radius u ∈ V.orbit
          (V.orbitPoint (T.saddleNegativeBranchOrbitIndex hindex .negative
            rho a hrho ha hrho_radius hreg V))
      rw [horbit]
      exact hmem


-- @@ L5952-5978 verbatim
/-- In the one-orbit positive case, the interior of either local branch arc
avoids all four common-orbit marks. -/
theorem saddlePositiveSpatialSegment_ne_commonMark_of_mem_Ioo
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (horbit : T.saddlePositiveBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddlePositiveBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (b : SaddleBranch) {u : I} (hu : u ∈ Set.Ioo 0 1) (i : Fin 4) :
    T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u ≠
      (T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
        hrho_radius hreg V horbit).point i := by
  intro heq
  let p := saddleBranchPairOfFinFour i
  have hboundary :
      T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius u =
        spacePart (M.saddlePositiveBoundaryEnd p.1 p.2 rho a) := by
    simpa [p, saddlePositiveCommonOrbitCyclicMarking] using heq
  rcases (T.saddlePositiveSpatialSegment_eq_boundaryEnd_iff hindex b p
    rho a hrho ha hrho_radius u).mp hboundary with hzero | hone
  · exact (ne_of_gt hu.1) hzero.1
  · exact (ne_of_lt hu.2) hone.1


-- @@ L5980-6006 verbatim
/-- The swapped negative common marking has the same four-mark avoidance
property. -/
theorem saddleNegativeSpatialSegment_ne_commonMark_of_mem_Ioo
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (horbit : T.saddleNegativeBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddleNegativeBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (b : SaddleBranch) {u : I} (hu : u ∈ Set.Ioo 0 1) (i : Fin 4) :
    T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u ≠
      (T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
        hrho_radius hreg V horbit).point i := by
  intro heq
  let p := saddleBranchPairOfFinFour i
  have hboundary :
      T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius u =
        spacePart (M.saddleNegativeBoundaryEnd p.2 p.1 rho a) := by
    simpa [p, saddleNegativeCommonOrbitCyclicMarking] using heq
  rcases (T.saddleNegativeSpatialSegment_eq_boundaryEnd_iff hindex b
    (p.2, p.1) rho a hrho ha hrho_radius u).mp hboundary with hzero | hone
  · exact (ne_of_gt hu.1) hzero.1
  · exact (ne_of_lt hu.2) hone.1


-- @@ L6008-6043 verbatim
/-- In the common positive orbit, the two ends of each actual local branch
are adjacent among the four cyclic marks. -/
theorem saddlePositiveCommonOrbit_localBranch_cyclicAdjacent
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (horbit : T.saddlePositiveBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddlePositiveBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (b : SaddleBranch) :
    let A := T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
      hrho_radius hreg V horbit
    A.CyclicAdjacent (finFourOfSaddleBranchPair (b, .negative))
      (finFourOfSaddleBranchPair (b, .positive)) := by
  dsimp only
  let P := T.saddlePositiveBranchOrbitParam hindex .negative rho a hrho ha
    hrho_radius hreg V
  let A := T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
    hrho_radius hreg V horbit
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  apply A.cyclicAdjacent_of_embedded_arc_four gamma
    (fun u => T.saddlePositiveSpatialSegment_mem_commonParamOrbit hindex
      rho a hrho ha hrho_radius hreg V horbit b u)
    (T.saddlePositiveSpatialSegment_injective hindex b rho a hrho ha
      hrho_radius)
  · simp [gamma, A, saddlePositiveSpatialSegment,
      saddlePositiveCommonOrbitCyclicMarking]
  · simp [gamma, A, saddlePositiveSpatialSegment,
      saddlePositiveCommonOrbitCyclicMarking]
  · intro u hu i
    exact T.saddlePositiveSpatialSegment_ne_commonMark_of_mem_Ioo hindex
      rho a hrho ha hrho_radius hreg V horbit b hu i


-- @@ L6045-6079 verbatim
/-- Negative common-orbit analogue, with the built-in label transpose. -/
theorem saddleNegativeCommonOrbit_localBranch_cyclicAdjacent
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (horbit : T.saddleNegativeBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddleNegativeBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (b : SaddleBranch) :
    let A := T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
      hrho_radius hreg V horbit
    A.CyclicAdjacent (finFourOfSaddleBranchPair (.negative, b))
      (finFourOfSaddleBranchPair (.positive, b)) := by
  dsimp only
  let P := T.saddleNegativeBranchOrbitParam hindex .negative rho a hrho ha
    hrho_radius hreg V
  let A := T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
    hrho_radius hreg V horbit
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  apply A.cyclicAdjacent_of_embedded_arc_four gamma
    (fun u => T.saddleNegativeSpatialSegment_mem_commonParamOrbit hindex
      rho a hrho ha hrho_radius hreg V horbit b u)
    (T.saddleNegativeSpatialSegment_injective hindex b rho a hrho ha
      hrho_radius)
  · simp [gamma, A, saddleNegativeSpatialSegment,
      saddleNegativeCommonOrbitCyclicMarking]
  · simp [gamma, A, saddleNegativeSpatialSegment,
      saddleNegativeCommonOrbitCyclicMarking]
  · intro u hu i
    exact T.saddleNegativeSpatialSegment_ne_commonMark_of_mem_Ioo hindex
      rho a hrho ha hrho_radius hreg V horbit b hu i


-- @@ L6081-6119 verbatim
/-- Exact cut-range identification for each positive local branch in the
four-mark common-orbit case. -/
theorem saddlePositiveCommonOrbit_localBranch_range_eq_cut
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (horbit : T.saddlePositiveBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddlePositiveBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (b : SaddleBranch) :
    let A := T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
      hrho_radius hreg V horbit
    (∃ q : Fin 3,
      Set.range (T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius) =
        Set.range (A.adjacentSubpath q)) ∨
      Set.range (T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius) =
        Set.range A.wrapSubpath := by
  dsimp only
  let A := T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
    hrho_radius hreg V horbit
  let gamma := T.saddlePositiveSpatialSegment b rho a hrho ha hrho_radius
  apply A.range_eq_adjacentSubpath_or_wrap_of_embedded_arc_four gamma
    (fun u => T.saddlePositiveSpatialSegment_mem_commonParamOrbit hindex
      rho a hrho ha hrho_radius hreg V horbit b u)
    (T.saddlePositiveSpatialSegment_injective hindex b rho a hrho ha
      hrho_radius)
    (finFourOfSaddleBranchPair (b, .negative))
    (finFourOfSaddleBranchPair (b, .positive))
  · simp [gamma, A, saddlePositiveSpatialSegment,
      saddlePositiveCommonOrbitCyclicMarking]
  · simp [gamma, A, saddlePositiveSpatialSegment,
      saddlePositiveCommonOrbitCyclicMarking]
  · intro u hu i
    exact T.saddlePositiveSpatialSegment_ne_commonMark_of_mem_Ioo hindex
      rho a hrho ha hrho_radius hreg V horbit b hu i


-- @@ L6121-6159 verbatim
/-- Negative four-mark exact cut-range identification, retaining the label
transpose. -/
theorem saddleNegativeCommonOrbit_localBranch_range_eq_cut
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha : a ^ 2 < rho ^ 2)
    (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (horbit : T.saddleNegativeBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddleNegativeBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (b : SaddleBranch) :
    let A := T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
      hrho_radius hreg V horbit
    (∃ q : Fin 3,
      Set.range (T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius) =
        Set.range (A.adjacentSubpath q)) ∨
      Set.range (T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius) =
        Set.range A.wrapSubpath := by
  dsimp only
  let A := T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
    hrho_radius hreg V horbit
  let gamma := T.saddleNegativeSpatialSegment b rho a hrho ha hrho_radius
  apply A.range_eq_adjacentSubpath_or_wrap_of_embedded_arc_four gamma
    (fun u => T.saddleNegativeSpatialSegment_mem_commonParamOrbit hindex
      rho a hrho ha hrho_radius hreg V horbit b u)
    (T.saddleNegativeSpatialSegment_injective hindex b rho a hrho ha
      hrho_radius)
    (finFourOfSaddleBranchPair (.negative, b))
    (finFourOfSaddleBranchPair (.positive, b))
  · simp [gamma, A, saddleNegativeSpatialSegment,
      saddleNegativeCommonOrbitCyclicMarking]
  · simp [gamma, A, saddleNegativeSpatialSegment,
      saddleNegativeCommonOrbitCyclicMarking]
  · intro u hu i
    exact T.saddleNegativeSpatialSegment_ne_commonMark_of_mem_Ioo hindex
      rho a hrho ha hrho_radius hreg V horbit b hu i


-- @@ L6161-6207 verbatim
/-- In the common positive orbit, the two local branches occupy two distinct
values of the four-cut enumeration, and every other cut avoids every
strictly interior chart point. -/
theorem saddlePositiveCommonOrbit_otherCuts_avoid_openChartPoint
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha0 : 0 < a)
    (ha : a ^ 2 < rho ^ 2) (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (horbit : T.saddlePositiveBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddlePositiveBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (u : E₂) (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hnorm : ‖u‖ < rho) :
    let A := T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
      hrho_radius hreg V horbit
    ∃ i j : Fin 4,
      i ≠ j ∧
        Set.range (T.saddlePositiveSpatialSegment .negative rho a hrho ha
          hrho_radius) = A.cyclicCutRange i ∧
        Set.range (T.saddlePositiveSpatialSegment .positive rho a hrho ha
          hrho_radius) = A.cyclicCutRange j ∧
        ∀ r, r ≠ i → r ≠ j →
          spacePart (M.param u) ∉ A.cyclicCutRange r := by
  dsimp only
  let A := T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
    hrho_radius hreg V horbit
  let gamma := T.saddlePositiveSpatialSegment .negative rho a hrho ha
    hrho_radius
  let delta := T.saddlePositiveSpatialSegment .positive rho a hrho ha
    hrho_radius
  apply A.exists_distinct_localCutRanges_and_excludes_other gamma delta
  · exact T.saddlePositiveSpatialSegments_disjoint hindex rho a hrho ha0
      ha hrho_radius
  · apply A.exists_cyclicCutRange_eq_of_adjacent_or_wrap gamma
    exact T.saddlePositiveCommonOrbit_localBranch_range_eq_cut hindex rho a
      hrho ha hrho_radius hreg V horbit .negative
  · apply A.exists_cyclicCutRange_eq_of_adjacent_or_wrap delta
    exact T.saddlePositiveCommonOrbit_localBranch_range_eq_cut hindex rho a
      hrho ha hrho_radius hreg V horbit .positive
  · exact T.spacePart_param_mem_union_saddlePositiveSpatialSegments_of_norm_le
      rho a hrho ha0 ha hrho_radius u hquad hnorm.le
  · intro l
    apply T.spacePart_param_ne_saddlePositiveBoundaryEnd_of_norm_lt hindex
      (saddleBranchPairOfFinFour l) rho a hrho ha hrho_radius u hquad hnorm


-- @@ L6209-6255 verbatim
/-- Negative common-orbit four-cut exterior exclusion, with the critical
label transpose retained in the marking. -/
theorem saddleNegativeCommonOrbit_otherCuts_avoid_openChartPoint
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha0 : 0 < a)
    (ha : a ^ 2 < rho ^ 2) (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (horbit : T.saddleNegativeBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddleNegativeBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V)
    (u : E₂) (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hnorm : ‖u‖ < rho) :
    let A := T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
      hrho_radius hreg V horbit
    ∃ i j : Fin 4,
      i ≠ j ∧
        Set.range (T.saddleNegativeSpatialSegment .negative rho a hrho ha
          hrho_radius) = A.cyclicCutRange i ∧
        Set.range (T.saddleNegativeSpatialSegment .positive rho a hrho ha
          hrho_radius) = A.cyclicCutRange j ∧
        ∀ r, r ≠ i → r ≠ j →
          spacePart (M.param u) ∉ A.cyclicCutRange r := by
  dsimp only
  let A := T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
    hrho_radius hreg V horbit
  let gamma := T.saddleNegativeSpatialSegment .negative rho a hrho ha
    hrho_radius
  let delta := T.saddleNegativeSpatialSegment .positive rho a hrho ha
    hrho_radius
  apply A.exists_distinct_localCutRanges_and_excludes_other gamma delta
  · exact T.saddleNegativeSpatialSegments_disjoint hindex rho a hrho ha0
      ha hrho_radius
  · apply A.exists_cyclicCutRange_eq_of_adjacent_or_wrap gamma
    exact T.saddleNegativeCommonOrbit_localBranch_range_eq_cut hindex rho a
      hrho ha hrho_radius hreg V horbit .negative
  · apply A.exists_cyclicCutRange_eq_of_adjacent_or_wrap delta
    exact T.saddleNegativeCommonOrbit_localBranch_range_eq_cut hindex rho a
      hrho ha hrho_radius hreg V horbit .positive
  · exact T.spacePart_param_mem_union_saddleNegativeSpatialSegments_of_norm_le
      rho a hrho ha0 ha hrho_radius u hquad hnorm.le
  · intro l
    let p := saddleBranchPairOfFinFour l
    apply T.spacePart_param_ne_saddleNegativeBoundaryEnd_of_norm_lt hindex
      (p.2, p.1) rho a hrho ha hrho_radius u hquad hnorm


-- @@ L6257-6311 verbatim
/-- Uniform positive common-orbit exterior-cut classification.  The two
local cut indices are independent of the chart point; both remaining cuts
avoid the entire open chart. -/
theorem saddlePositiveCommonOrbit_exists_uniformExteriorCuts
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha0 : 0 < a)
    (ha : a ^ 2 < rho ^ 2) (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg))
    (horbit : T.saddlePositiveBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddlePositiveBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V) :
    let A := T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
      hrho_radius hreg V horbit
    ∃ i j : Fin 4,
      i ≠ j ∧
        Set.range (T.saddlePositiveSpatialSegment .negative rho a hrho ha
          hrho_radius) = A.cyclicCutRange i ∧
        Set.range (T.saddlePositiveSpatialSegment .positive rho a hrho ha
          hrho_radius) = A.cyclicCutRange j ∧
        ∀ r, r ≠ i → r ≠ j → ∀ u : E₂,
          morseQuadratic .saddle (u 0, u 1) = a ^ 2 → ‖u‖ < rho →
          spacePart (M.param u) ∉ A.cyclicCutRange r := by
  dsimp only
  let A := T.saddlePositiveCommonOrbitCyclicMarking hindex rho a hrho ha
    hrho_radius hreg V horbit
  let gamma := T.saddlePositiveSpatialSegment .negative rho a hrho ha
    hrho_radius
  let delta := T.saddlePositiveSpatialSegment .positive rho a hrho ha
    hrho_radius
  have hgamma : ∃ i : Fin 4, Set.range gamma = A.cyclicCutRange i := by
    apply A.exists_cyclicCutRange_eq_of_adjacent_or_wrap gamma
    exact T.saddlePositiveCommonOrbit_localBranch_range_eq_cut hindex rho a
      hrho ha hrho_radius hreg V horbit .negative
  have hdelta : ∃ j : Fin 4, Set.range delta = A.cyclicCutRange j := by
    apply A.exists_cyclicCutRange_eq_of_adjacent_or_wrap delta
    exact T.saddlePositiveCommonOrbit_localBranch_range_eq_cut hindex rho a
      hrho ha hrho_radius hreg V horbit .positive
  obtain ⟨i, j, hij, hi, hj, hother⟩ :=
    A.exists_distinct_localCutRanges_and_otherCuts_avoid_unmarkedLocal
      gamma delta
      (T.saddlePositiveSpatialSegments_disjoint hindex rho a hrho ha0 ha
        hrho_radius) hgamma hdelta
  refine ⟨i, j, hij, hi, hj, ?_⟩
  intro r hri hrj u hquad hnorm
  apply hother
  · exact T.spacePart_param_mem_union_saddlePositiveSpatialSegments_of_norm_le
      rho a hrho ha0 ha hrho_radius u hquad hnorm.le
  · intro l
    apply T.spacePart_param_ne_saddlePositiveBoundaryEnd_of_norm_lt hindex
      (saddleBranchPairOfFinFour l) rho a hrho ha hrho_radius u hquad hnorm
  · exact hri
  · exact hrj


-- @@ L6313-6366 verbatim
/-- Uniform negative common-orbit exterior-cut classification. -/
theorem saddleNegativeCommonOrbit_exists_uniformExteriorCuts
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (hindex : M.index = .saddle)
    (rho a : ℝ) (hrho : 0 < rho) (ha0 : 0 < a)
    (ha : a ^ 2 < rho ^ 2) (hrho_radius : rho < T.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg))
    (horbit : T.saddleNegativeBranchOrbitIndex hindex .negative
        rho a hrho ha hrho_radius hreg V =
      T.saddleNegativeBranchOrbitIndex hindex .positive
        rho a hrho ha hrho_radius hreg V) :
    let A := T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
      hrho_radius hreg V horbit
    ∃ i j : Fin 4,
      i ≠ j ∧
        Set.range (T.saddleNegativeSpatialSegment .negative rho a hrho ha
          hrho_radius) = A.cyclicCutRange i ∧
        Set.range (T.saddleNegativeSpatialSegment .positive rho a hrho ha
          hrho_radius) = A.cyclicCutRange j ∧
        ∀ r, r ≠ i → r ≠ j → ∀ u : E₂,
          morseQuadratic .saddle (u 0, u 1) = -(a ^ 2) → ‖u‖ < rho →
          spacePart (M.param u) ∉ A.cyclicCutRange r := by
  dsimp only
  let A := T.saddleNegativeCommonOrbitCyclicMarking hindex rho a hrho ha
    hrho_radius hreg V horbit
  let gamma := T.saddleNegativeSpatialSegment .negative rho a hrho ha
    hrho_radius
  let delta := T.saddleNegativeSpatialSegment .positive rho a hrho ha
    hrho_radius
  have hgamma : ∃ i : Fin 4, Set.range gamma = A.cyclicCutRange i := by
    apply A.exists_cyclicCutRange_eq_of_adjacent_or_wrap gamma
    exact T.saddleNegativeCommonOrbit_localBranch_range_eq_cut hindex rho a
      hrho ha hrho_radius hreg V horbit .negative
  have hdelta : ∃ j : Fin 4, Set.range delta = A.cyclicCutRange j := by
    apply A.exists_cyclicCutRange_eq_of_adjacent_or_wrap delta
    exact T.saddleNegativeCommonOrbit_localBranch_range_eq_cut hindex rho a
      hrho ha hrho_radius hreg V horbit .positive
  obtain ⟨i, j, hij, hi, hj, hother⟩ :=
    A.exists_distinct_localCutRanges_and_otherCuts_avoid_unmarkedLocal
      gamma delta
      (T.saddleNegativeSpatialSegments_disjoint hindex rho a hrho ha0 ha
        hrho_radius) hgamma hdelta
  refine ⟨i, j, hij, hi, hj, ?_⟩
  intro r hri hrj u hquad hnorm
  apply hother
  · exact T.spacePart_param_mem_union_saddleNegativeSpatialSegments_of_norm_le
      rho a hrho ha0 ha hrho_radius u hquad hnorm.le
  · intro l
    let p := saddleBranchPairOfFinFour l
    apply T.spacePart_param_ne_saddleNegativeBoundaryEnd_of_norm_lt hindex
      (p.2, p.1) rho a hrho ha hrho_radius u hquad hnorm
  · exact hri
  · exact hrj


-- @@ L6368-6368 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L6370-6370 verbatim
namespace MorsePosition


-- @@ L6372-6372 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L6374-6386 verbatim
/-- An event center is the only time-critical point on its critical slice.
This is the global form of critical-value separation needed by the punctured
saddle argument. -/
theorem eq_eventCenter_of_timeCritical_of_same_time
    (P : MorsePosition C) (t : ℝ) (ht : t ∈ P.eventTimes)
    {x : E'} (hx : x ∈ timeCritical C.G)
    (hxt : tcoord x = tcoord (P.eventCenter t ht)) :
    x = P.eventCenter t ht := by
  apply P.eq_eventCenter_of_mem_of_time t ht
  · change x ∈ (P.centers : Set E')
    rw [P.centers_exact]
    exact C.timeCritical_subset_coreCriticalPoints hx
  · rw [hxt, P.eventCenter_time t ht]


-- @@ L6388-6388 verbatim
end MorsePosition


-- @@ L6390-6390 verbatim
namespace StandardMorseEventAt


-- @@ L6392-6392 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L6393-6393 verbatim
variable {P : MorsePosition C}

-- @@ L6394-6394 verbatim
variable {t : ℝ} {ht : t ∈ P.eventTimes}


-- @@ L6396-6408 verbatim
/-- Every point of the punctured critical slice is spatially regular.  The
proof is global: a failure of spatial regularity would give a second
time-critical point at the event time, contradicting critical-value
separation. -/
theorem puncturedCriticalSlice_spatialDeriv_surjective
    {x : E'}
    (hx : x ∈ puncturedCriticalSlice C (P.eventCenter t ht)) :
    Surjective (spatialDeriv C.G x) := by
  by_contra hsurj
  have hxcrit : x ∈ timeCritical C.G := ⟨hx.1, hsurj⟩
  have hxeq : x = P.eventCenter t ht :=
    P.eq_eventCenter_of_timeCritical_of_same_time t ht hxcrit hx.2.1
  exact hx.2.2 hxeq


-- @@ L6410-6418 verbatim
/-- Set-theoretic version: the punctured critical slice is contained in the
spatially regular zero locus. -/
theorem puncturedCriticalSlice_subset_spatialRegularZeroSet :
    puncturedCriticalSlice C (P.eventCenter t ht) ⊆
      {x : E' | C.G x = 0 ∧ Surjective (spatialDeriv C.G x)} := by
  intro x hx
  exact ⟨hx.1,
    puncturedCriticalSlice_spatialDeriv_surjective
      (P := P) (ht := ht) hx⟩


-- @@ L6420-6432 verbatim
/-- An ordinary path in the punctured critical slice is automatically a
spatially regular zero path.  This is the exact bridge from the topological
arc problem to the existing Morse frame-transport API. -/
def spatiallyRegularZeroPathOfPuncturedCriticalPath
    {x y : E'} (gamma : Path x y)
    (hgamma : ∀ u : I,
      gamma u ∈ puncturedCriticalSlice C (P.eventCenter t ht)) :
    SpatiallyRegularZeroPath C.G x y where
  toPath := gamma
  range_subset := by
    rintro z ⟨u, rfl⟩
    exact puncturedCriticalSlice_subset_spatialRegularZeroSet
      (P := P) (ht := ht) (hgamma u)


-- @@ L6434-6443 verbatim
/-- Every `SaddleCriticalExteriorArc` in the actual punctured critical slice
therefore carries the stronger regular-zero structure used by frame
transport. -/
def SaddleCriticalExteriorArc.toSpatiallyRegularZeroPath
    {Q : Type*} {endpoint : Q → E'} {p q : Q}
    (A : SaddleCriticalExteriorArc endpoint
      (puncturedCriticalSlice C (P.eventCenter t ht)) p q) :
    SpatiallyRegularZeroPath C.G (endpoint p) (endpoint q) :=
  spatiallyRegularZeroPathOfPuncturedCriticalPath
    (P := P) (ht := ht) A.toPath A.mem_exterior


-- @@ L6445-6445 verbatim
end StandardMorseEventAt


-- @@ L6447-6447 verbatim
end Submission
