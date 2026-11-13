import Submission.ProductionMorseSaddleExteriorTransport


-- @@ L3-17 verbatim
/-!
# Complete local excision for production saddle events

The complete-cover radius of a production event can be larger than the
auxiliary embedded radius used for injectivity.  For saddle excision we only
need continuity of the event parameter along a fixed hyperbola branch.  The
underlying shared-cutoff construction is differentiable on the *whole* event
radius, so the smaller injectivity radius is unnecessary here.

This file first exposes that production-specific full-radius smoothness.  It
then ports the fixed-level branch arcs to the common `StandardMorseEventAt`
interface.  The resulting orbit lemmas are the local input needed to show
that every component meeting the complete-cover ball is one of the two
distinguished saddle components.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false

-- @@ L20-20 verbatim
set_option maxHeartbeats 2400000


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function Metric

-- @@ L25-25 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L27-27 verbatim
namespace Submission


-- @@ L29-29 verbatim
variable {n : ℕ}


-- @@ L31-31 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L32-32 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L33-33 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L35-35 verbatim
/-! ## Full-radius smoothness of the actual production parameter -/


-- @@ L37-37 verbatim
namespace FiniteIFTSurfaceCover.SharedCutoffMorseData


-- @@ L39-39 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]

-- @@ L40-40 verbatim
variable {B : FiniteIFTSurfaceCover C ι}


-- @@ L42-66 verbatim
/-- The shared-cutoff ambient parameter is differentiable on the complete
normal-form radius, not merely on the later embedding shrink. -/
theorem criticalAmbientParam_differentiableAt_full
    {K U : Set E'} {χ : SmoothCutoff K U}
    (R : B.SharedCutoffMorseData χ)
    (p : Σ _ : ι, E₂) (hp : p ∈ R.criticalParameters)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    DifferentiableAt ℝ (R.criticalAmbientParam p hp) u := by
  let M := R.localMorseNormalForm p hp
  let Q := R.criticalModelShrink p hp
  let P := B.chart p.1
  have hM : DifferentiableAt ℝ M.param u :=
    LocalMorseNormalForm.SimultaneousShrink.param_differentiableAt_of_contDiffOn_one
      M Q (by simpa [M, Q] using R.criticalModelShrink_contDiffOn p hp) u hu
  have hshift : DifferentiableAt ℝ
      (fun z : E₂ => p.2 + M.param z) u :=
    differentiableAt_const (c := p.2).add hM
  have hchart : DifferentiableAt ℝ
      (fun z : E₂ => P.param (p.2 + M.param z)) u :=
    (P.param_smooth.differentiable (by simp) _).comp u hshift
  change DifferentiableAt ℝ
    (fun z : E₂ => R.forward.diffeomorph
      (P.param (p.2 + M.param z))) u
  exact (R.forward.diffeomorph.contDiff.differentiable (by simp) _).comp
    u hchart


-- @@ L68-68 verbatim
namespace CriticalValueShiftData


-- @@ L70-91 verbatim
/-- After value separation, the transported parameter is still
differentiable on its full complete-cover radius. -/
theorem transportedParam_differentiableAt_full
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : B.SharedCutoffMorseData χ}
    (S : CriticalValueShiftData R) (e : GlobalCriticalEvent R)
    (u : E₂) (hu : ‖u‖ < (S.productionEvent e).radius) :
    DifferentiableAt ℝ (S.productionEvent e).param u := by
  let p := (R.criticalEventOwner e).1
  let hp : p ∈ R.criticalParameters := R.criticalEventOwner_mem e
  have huOwner : ‖u‖ < (R.criticalModelShrink p hp).radius := by
    have hle := (S.eventTransportShrink e).radius_le
    change ‖u‖ < (S.eventTransportShrink e).radius at hu
    change (S.eventTransportShrink e).radius ≤
      (R.criticalModelShrink p hp).radius at hle
    exact hu.trans_le hle
  have hbase := R.criticalAmbientParam_differentiableAt_full p hp u huOwner
  change DifferentiableAt ℝ
    (fun z : E₂ => S.forward.diffeomorph
      (R.criticalAmbientParam p hp z)) u
  exact (S.forward.diffeomorph.contDiff.differentiable (by simp) _).comp
    u hbase


-- @@ L93-93 verbatim
end CriticalValueShiftData

-- @@ L94-94 verbatim
end FiniteIFTSurfaceCover.SharedCutoffMorseData


-- @@ L96-96 verbatim
/-! ## Fixed-level arcs on any full-smooth standard event -/


-- @@ L98-98 verbatim
namespace StandardMorseEventAt


-- @@ L100-100 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L102-110 verbatim
/-- Smoothness on the whole complete-cover radius.  The center equality is
included explicitly so this production strengthening retains the dependent
event center in its public type. -/
structure FullRadiusSmooth
    {C : FramedLevelCobordism n} {center : E'}
    (M : StandardMorseEventAt (n := n) C center) where
  center_eq : M.param 0 = center
  differentiableAt : ∀ u : E₂, ‖u‖ < M.radius →
    DifferentiableAt ℝ M.param u


-- @@ L112-112 verbatim
namespace FullRadiusSmooth


-- @@ L114-120 verbatim
/-- Transport full-radius smoothness together with the center-indexed event. -/
theorem castCenter {C : FramedLevelCobordism n}
    {center center' : E'} (h : center = center')
    (M : StandardMorseEventAt (n := n) C center)
    (H : M.FullRadiusSmooth) : (h ▸ M).FullRadiusSmooth := by
  subst center'
  exact H


-- @@ L122-122 verbatim
end FullRadiusSmooth


-- @@ L124-142 verbatim
/-- The positive saddle branch arc from an arbitrary local point to a chosen
end on the smaller boundary circle. -/
def saddlePositiveArcToBoundaryFull
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) : C(I, E') where
  toFun q := (fun _ : E' =>
    M.param (saddlePositiveArcToBoundaryParam b e ρ a u q)) center
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro q
    have hnorm := norm_saddlePositiveArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q
    exact (H.differentiableAt _ hnorm).continuousAt.comp'
      (saddlePositiveArcToBoundaryParam b e ρ a u).continuous.continuousAt


-- @@ L144-161 verbatim
/-- Negative-level counterpart of `saddlePositiveArcToBoundaryFull`. -/
def saddleNegativeArcToBoundaryFull
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) : C(I, E') where
  toFun q := (fun _ : E' =>
    M.param (saddleNegativeArcToBoundaryParam b e ρ a u q)) center
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro q
    have hnorm := norm_saddleNegativeArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q
    exact (H.differentiableAt _ hnorm).continuousAt.comp'
      (saddleNegativeArcToBoundaryParam b e ρ a u).continuous.continuousAt


-- @@ L163-177 verbatim
@[simp] theorem saddlePositiveArcToBoundaryFull_zero
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) :
    M.saddlePositiveArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad 0 = M.param u := by
  rw [saddlePositiveArcToBoundaryFull]
  simp only [saddlePositiveArcToBoundaryParam,
    saddleAffineCoordinate_zero, ContinuousMap.coe_mk]
  rw [← eq_pairToMorseParam_saddlePositiveArc_of_signedBranch
    b a u hquad hsign]


-- @@ L179-193 verbatim
@[simp] theorem saddlePositiveArcToBoundaryFull_one
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) :
    M.saddlePositiveArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad 1 =
        M.saddlePositiveBoundaryEnd b e ρ a := by
  simp [saddlePositiveArcToBoundaryFull,
    saddlePositiveArcToBoundaryParam,
    saddlePositiveBoundaryEnd, saddlePositiveBoundaryEndParam,
    localPoint]


-- @@ L195-209 verbatim
@[simp] theorem saddleNegativeArcToBoundaryFull_zero
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) :
    M.saddleNegativeArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad 0 = M.param u := by
  rw [saddleNegativeArcToBoundaryFull]
  simp only [saddleNegativeArcToBoundaryParam,
    saddleAffineCoordinate_zero, ContinuousMap.coe_mk]
  rw [← eq_pairToMorseParam_saddleNegativeArc_of_signedBranch
    b a u hquad hsign]


-- @@ L211-225 verbatim
@[simp] theorem saddleNegativeArcToBoundaryFull_one
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) :
    M.saddleNegativeArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad 1 =
        M.saddleNegativeBoundaryEnd b e ρ a := by
  simp [saddleNegativeArcToBoundaryFull,
    saddleNegativeArcToBoundaryParam,
    saddleNegativeBoundaryEnd, saddleNegativeBoundaryEndParam,
    localPoint]


-- @@ L227-241 verbatim
/-- Spatial projection of the full-radius positive branch arc. -/
def saddlePositiveSpatialArcToBoundaryFull
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) : C(I, E₁) where
  toFun q := spacePart
    (M.saddlePositiveArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad q)
  continuous_toFun := continuous_spacePart.comp
    (M.saddlePositiveArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad).continuous


-- @@ L243-257 verbatim
/-- Spatial projection of the full-radius negative branch arc. -/
def saddleNegativeSpatialArcToBoundaryFull
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) : C(I, E₁) where
  toFun q := spacePart
    (M.saddleNegativeArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad q)
  continuous_toFun := continuous_spacePart.comp
    (M.saddleNegativeArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad).continuous


-- @@ L259-271 verbatim
theorem saddlePositiveArcToBoundaryFull_fiber
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) (q : I) :
    C.G (M.saddlePositiveArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad q) = 0 := by
  apply M.param_fiber
  exact norm_saddlePositiveArcToBoundaryParam_lt b e u hquad hsign
    hρ ha hu hρrad q


-- @@ L273-285 verbatim
theorem saddleNegativeArcToBoundaryFull_fiber
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) (q : I) :
    C.G (M.saddleNegativeArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad q) = 0 := by
  apply M.param_fiber
  exact norm_saddleNegativeArcToBoundaryParam_lt b e u hquad hsign
    hρ ha hu hρrad q


-- @@ L287-303 verbatim
theorem saddlePositiveArcToBoundaryFull_time
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (hindex : M.index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) (q : I) :
    tcoord (M.saddlePositiveArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad q) = tcoord center + a ^ 2 := by
  change tcoord (M.param
    (saddlePositiveArcToBoundaryParam b e ρ a u q)) = _
  rw [M.time_model _
    (norm_saddlePositiveArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q), hindex]
  simp [saddlePositiveArcToBoundaryParam]


-- @@ L305-322 verbatim
theorem saddleNegativeArcToBoundaryFull_time
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (H : FullRadiusSmooth (center := center) M)
    (hindex : M.index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius) (q : I) :
    tcoord (M.saddleNegativeArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad q) = tcoord center - a ^ 2 := by
  change tcoord (M.param
    (saddleNegativeArcToBoundaryParam b e ρ a u q)) = _
  rw [M.time_model _
    (norm_saddleNegativeArcToBoundaryParam_lt b e u hquad hsign
      hρ ha hu hρrad q), hindex]
  simp [saddleNegativeArcToBoundaryParam]
  ring


-- @@ L324-324 verbatim
namespace EmbeddedShrink


-- @@ L326-348 verbatim
theorem saddlePositiveSpatialArcToBoundaryFull_mem_fiber
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink)
    (H : FullRadiusSmooth (center := center) M)
    (hindex : M.index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2)) (q : I) :
    M.saddlePositiveSpatialArcToBoundaryFull H b e ρ a u
        hquad hsign hρ ha hu hρrad q ∈
      (T.saddlePositiveSlice a hreg).fiber := by
  rw [saddlePositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (M.saddlePositiveArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad q))
    (tcoord center + a ^ 2)) = 0
  rw [← M.saddlePositiveArcToBoundaryFull_time H hindex b e ρ a u
    hquad hsign hρ ha hu hρrad q, spaceTime_spacePart]
  exact M.saddlePositiveArcToBoundaryFull_fiber H b e ρ a u
    hquad hsign hρ ha hu hρrad q


-- @@ L350-372 verbatim
theorem saddleNegativeSpatialArcToBoundaryFull_mem_fiber
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink)
    (H : FullRadiusSmooth (center := center) M)
    (hindex : M.index = .saddle)
    (b e : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2)) (q : I) :
    M.saddleNegativeSpatialArcToBoundaryFull H b e ρ a u
        hquad hsign hρ ha hu hρrad q ∈
      (T.saddleNegativeSlice a hreg).fiber := by
  rw [saddleNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (M.saddleNegativeArcToBoundaryFull H b e ρ a u
      hquad hsign hρ ha hu hρrad q))
    (tcoord center - a ^ 2)) = 0
  rw [← M.saddleNegativeArcToBoundaryFull_time H hindex b e ρ a u
    hquad hsign hρ ha hu hρrad q, spaceTime_spacePart]
  exact M.saddleNegativeArcToBoundaryFull_fiber H b e ρ a u
    hquad hsign hρ ha hu hρrad q


-- @@ L374-399 verbatim
theorem saddlePositiveParam_mem_branch_orbit_full
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink)
    (H : FullRadiusSmooth (center := center) M)
    (hindex : M.index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2)
    (hsign : 0 < signedBranch b (u 0))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    spacePart (M.param u) ∈
      V.orbit (spacePart (T.saddlePositiveBranchBase b ρ a)) := by
  let γ := M.saddlePositiveSpatialArcToBoundaryFull H b .negative ρ a u
    hquad hsign hρ ha hu hρrad
  have hγfiber : ∀ q, γ q ∈ (T.saddlePositiveSlice a hreg).fiber := by
    intro q
    exact T.saddlePositiveSpatialArcToBoundaryFull_mem_fiber H hindex
      b .negative ρ a u hquad hsign hρ ha hu hρrad hreg q
  have hend := V.continuousMap_mem_orbit γ hγfiber 1
  have hresult : γ 0 ∈ V.orbit (γ 1) := by
    rw [V.orbit_eq_of_mem hend]
    exact V.mem_orbit_self _
  simpa [γ, saddlePositiveSpatialArcToBoundaryFull,
    saddlePositiveBranchBase] using hresult


-- @@ L401-426 verbatim
theorem saddleNegativeParam_mem_branch_orbit_full
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink)
    (H : FullRadiusSmooth (center := center) M)
    (hindex : M.index = .saddle)
    (b : SaddleBranch) (ρ a : ℝ) (u : E₂)
    (hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2))
    (hsign : 0 < signedBranch b (u 1))
    (hρ : 0 < ρ) (ha : a ^ 2 < ρ ^ 2)
    (hu : ‖u‖ < M.radius) (hρrad : ρ < M.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    spacePart (M.param u) ∈
      V.orbit (spacePart (T.saddleNegativeBranchBase b ρ a)) := by
  let γ := M.saddleNegativeSpatialArcToBoundaryFull H b .negative ρ a u
    hquad hsign hρ ha hu hρrad
  have hγfiber : ∀ q, γ q ∈ (T.saddleNegativeSlice a hreg).fiber := by
    intro q
    exact T.saddleNegativeSpatialArcToBoundaryFull_mem_fiber H hindex
      b .negative ρ a u hquad hsign hρ ha hu hρrad hreg q
  have hend := V.continuousMap_mem_orbit γ hγfiber 1
  have hresult : γ 0 ∈ V.orbit (γ 1) := by
    rw [V.orbit_eq_of_mem hend]
    exact V.mem_orbit_self _
  simpa [γ, saddleNegativeSpatialArcToBoundaryFull,
    saddleNegativeBranchBase] using hresult


-- @@ L428-473 verbatim
/-- Every covered point on a positive saddle slice lies on one of the two
distinguished positive-branch orbits. -/
theorem saddlePositive_coveredSliceFiber_subset_union_orbits_full
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (hindex : M.index = .saddle)
    (ρ a : ℝ) (hρ : 0 < ρ) (ha0 : 0 < a)
    (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < M.radius)
    (hreg : sliceRegular C.G (tcoord center + a ^ 2))
    (V : TamedField (T.saddlePositiveSlice a hreg)) :
    M.coveredSliceFiber (tcoord center + a ^ 2) ⊆
      V.orbit (spacePart (T.saddlePositiveBranchBase .positive ρ a)) ∪
      V.orbit (spacePart (T.saddlePositiveBranchBase .negative ρ a)) := by
  intro x hx
  obtain ⟨u, hu, huv⟩ := M.exists_param_of_mem_coveredSliceFiber hx
  have htime := M.time_model u hu
  have hs : tcoord (M.param u) = tcoord center + a ^ 2 := by
    rw [huv, tcoord_spaceTime]
  have hquad : morseQuadratic .saddle (u 0, u 1) = a ^ 2 := by
    rw [hindex] at htime
    linarith
  have hu0 : u 0 ≠ 0 := by
    intro hz
    simp only [morseQuadratic, hz] at hquad
    nlinarith [sq_nonneg (u 1), sq_nonneg a]
  have hxEq : x = spacePart (M.param u) := by
    rw [huv, spacePart_spaceTime]
  rw [hxEq]
  rcases lt_or_gt_of_ne hu0 with hneg | hpos
  · right
    apply T.saddlePositiveParam_mem_branch_orbit_full H hindex .negative
      ρ a u hquad
    · simpa [signedBranch] using neg_pos.mpr hneg
    · exact hρ
    · exact ha
    · exact hu
    · exact hρrad
  · left
    apply T.saddlePositiveParam_mem_branch_orbit_full H hindex .positive
      ρ a u hquad
    · simpa [signedBranch] using hpos
    · exact hρ
    · exact ha
    · exact hu
    · exact hρrad


-- @@ L475-520 verbatim
/-- Every covered point on a negative saddle slice lies on one of the two
distinguished negative-branch orbits. -/
theorem saddleNegative_coveredSliceFiber_subset_union_orbits_full
    {center : E'} {M : StandardMorseEventAt (n := n) C center}
    (T : M.EmbeddedShrink) (H : M.FullRadiusSmooth)
    (hindex : M.index = .saddle)
    (ρ a : ℝ) (hρ : 0 < ρ) (ha0 : 0 < a)
    (ha : a ^ 2 < ρ ^ 2)
    (hρrad : ρ < M.radius)
    (hreg : sliceRegular C.G (tcoord center - a ^ 2))
    (V : TamedField (T.saddleNegativeSlice a hreg)) :
    M.coveredSliceFiber (tcoord center - a ^ 2) ⊆
      V.orbit (spacePart (T.saddleNegativeBranchBase .positive ρ a)) ∪
      V.orbit (spacePart (T.saddleNegativeBranchBase .negative ρ a)) := by
  intro x hx
  obtain ⟨u, hu, huv⟩ := M.exists_param_of_mem_coveredSliceFiber hx
  have htime := M.time_model u hu
  have hs : tcoord (M.param u) = tcoord center - a ^ 2 := by
    rw [huv, tcoord_spaceTime]
  have hquad : morseQuadratic .saddle (u 0, u 1) = -(a ^ 2) := by
    rw [hindex] at htime
    linarith
  have hu1 : u 1 ≠ 0 := by
    intro hz
    simp only [morseQuadratic, hz] at hquad
    nlinarith [sq_nonneg (u 0), sq_nonneg a]
  have hxEq : x = spacePart (M.param u) := by
    rw [huv, spacePart_spaceTime]
  rw [hxEq]
  rcases lt_or_gt_of_ne hu1 with hneg | hpos
  · right
    apply T.saddleNegativeParam_mem_branch_orbit_full H hindex .negative
      ρ a u hquad
    · simpa [signedBranch] using neg_pos.mpr hneg
    · exact hρ
    · exact ha
    · exact hu
    · exact hρrad
  · left
    apply T.saddleNegativeParam_mem_branch_orbit_full H hindex .positive
      ρ a u hquad
    · simpa [signedBranch] using hpos
    · exact hρ
    · exact ha
    · exact hu
    · exact hρrad


-- @@ L522-522 verbatim
end EmbeddedShrink


-- @@ L524-524 verbatim
end StandardMorseEventAt


-- @@ L526-526 verbatim
/-! ## Automatic full-radius witnesses for production events -/


-- @@ L528-528 verbatim
namespace FiniteIFTSurfaceCover.SharedCutoffMorseData.CriticalValueShiftData


-- @@ L530-530 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]

-- @@ L531-531 verbatim
variable {B : FiniteIFTSurfaceCover C ι}


-- @@ L533-541 verbatim
/-- The actual value-separated production event carries the strengthened
full-radius smoothness used by saddle local excision. -/
theorem productionEventFullRadiusSmooth
    {K U : Set E'} {χ : SmoothCutoff K U}
    {R : B.SharedCutoffMorseData χ}
    (S : CriticalValueShiftData R) (e : GlobalCriticalEvent R) :
    (S.productionEvent e).FullRadiusSmooth where
  center_eq := (S.productionEvent e).param_zero
  differentiableAt := S.transportedParam_differentiableAt_full e


-- @@ L543-543 verbatim
end FiniteIFTSurfaceCover.SharedCutoffMorseData.CriticalValueShiftData


-- @@ L545-545 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L547-547 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L548-548 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L549-549 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L551-560 verbatim
/-- Chronological specialization of the production full-radius witness. -/
theorem chronologicalEventFullRadiusSmooth
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    (D.position.eventModel t ht).FullRadiusSmooth := by
  rw [D.eventModel_eq_transportedStandardMorseEvent t ht]
  exact
    (D.second.toCriticalValueShiftData.productionEventFullRadiusSmooth
      (D.chronologicalGlobalEvent t ht)).castCenter
        (D.second.shiftedCenter_chronologicalGlobalEvent t ht)


-- @@ L562-588 verbatim
/-- The complete local part of the chronological outgoing saddle slice is
exactly covered by its two distinguished branch components. -/
theorem chronologicalSaddleAfterCovered_subset_union_orbits
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    (D.position.eventModel t ht).coveredSliceFiber
        (D.chronologicalAfterTime t ht) ⊆
      (D.chronologicalSaddlePositiveOrbit t ht hindex .positive : Set E₁) ∪
      (D.chronologicalSaddlePositiveOrbit t ht hindex .negative : Set E₁) := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let ρ := D.chronologicalSaddleBoundaryRadius t ht
  let a := D.chronologicalWindowRadius t ht
  let V := D.chronologicalAfterField t ht
  have h := T.saddlePositive_coveredSliceFiber_subset_union_orbits_full
    H hindex ρ a
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
        T.radius_le)
      (D.chronologicalAfterTime_regular t ht) V
  simpa [M, T, ρ, a, V, chronologicalAfterTime,
    chronologicalSaddlePositiveOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchOrbitIndex] using h


-- @@ L590-616 verbatim
/-- The complete local part of the chronological incoming saddle slice is
exactly covered by its two distinguished branch components. -/
theorem chronologicalSaddleBeforeCovered_subset_union_orbits
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    (D.position.eventModel t ht).coveredSliceFiber
        (D.chronologicalBeforeTime t ht) ⊆
      (D.chronologicalSaddleNegativeOrbit t ht hindex .positive : Set E₁) ∪
      (D.chronologicalSaddleNegativeOrbit t ht hindex .negative : Set E₁) := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let ρ := D.chronologicalSaddleBoundaryRadius t ht
  let a := D.chronologicalWindowRadius t ht
  let V := D.chronologicalBeforeField t ht
  have h := T.saddleNegative_coveredSliceFiber_subset_union_orbits_full
    H hindex ρ a
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalWindowRadius_pos t ht)
      (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
      ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
        T.radius_le)
      (D.chronologicalBeforeTime_regular t ht) V
  simpa [M, T, ρ, a, V, chronologicalBeforeTime,
    chronologicalSaddleNegativeOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchOrbitIndex] using h


-- @@ L618-618 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L620-620 verbatim
end Submission
