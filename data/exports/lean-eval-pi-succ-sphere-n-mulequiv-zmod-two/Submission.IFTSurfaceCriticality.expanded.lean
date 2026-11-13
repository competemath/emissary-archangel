import Mathlib
import Submission.LocalIFTSurfaceChart
import Submission.MorseNondegenerateBridge


-- @@ L5-19 verbatim
/-!
# Critical points detected in an IFT surface parameter

An `IFTSurfaceChart` is more than a convenient parametrization of the zero
surface.  On every parameter neighborhood on which its fiber and lifted
coordinate identities hold, its differential identifies the two-dimensional
parameter space with the kernel of the ambient defining-map differential.

This file makes that rank statement explicit and uses it to identify ambient
time-critical points with zeros of the ordinary two-dimensional chart
gradient.  It removes the local rank half of the `critical_model` obligation
from the Morse installation pipeline: after a normal-form radius has been
shrunk into the chart domain, the ambient critical-point statement follows
from the scalar normal form.
-/


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Function Filter

-- @@ L24-24 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-28 verbatim
variable {n : ℕ}


-- @@ L30-30 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L31-31 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L32-32 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L34-34 verbatim
/-! ## An intrinsic criticality criterion on a regular zero surface -/


-- @@ L36-61 verbatim
/-- At a regular zero of `G`, failure of spatial surjectivity is equivalent to
the time coordinate vanishing on the whole kernel of the full differential.
This is the coordinate-free form of criticality of time restricted to the
zero surface. -/
theorem mem_timeCritical_iff_tcoord_eq_zero_on_ker
    {G : E' → F} {v : E'} (hv : G v = 0)
    (hregular : Surjective (fderiv ℝ G v)) :
    v ∈ timeCritical G ↔
      ∀ w : E', fderiv ℝ G v w = 0 → tcoord w = 0 := by
  rw [timeCritical]
  simp only [Set.mem_setOf_eq, hv, true_and]
  rw [← kerProj_timeVec_eq_zero_iff hregular]
  constructor
  · intro hproj w hw
    rw [← inner_timeVec]
    calc
      ⟪timeVec, w⟫ = ⟪kerProj G v timeVec, w⟫ := by
        rw [inner_kerProj_left hregular, kerProj_of_fderiv_eq_zero hw]
      _ = 0 := by simp [hproj]
  · intro hker
    have hzero : tcoord (kerProj G v timeVec) = 0 :=
      hker _ (fderiv_kerProj hregular timeVec)
    have hnorm : ‖kerProj G v timeVec‖ ^ 2 = 0 := by
      rw [← inner_timeVec_kerProj_timeVec hregular, inner_timeVec]
      exact hzero
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)


-- @@ L63-63 verbatim
/-! ## A general two-dimensional surface parameter -/


-- @@ L65-99 verbatim
/-- A locally fiber-valued injective two-dimensional parameter has tangent
range exactly equal to the kernel of the defining-map differential. -/
theorem surfaceParam_fderiv_range_eq_ker
    (C : FramedLevelCobordism n) (param : E₂ → E') (u : E₂)
    (hsmooth : ContDiff ℝ ∞ param)
    (hfiber : ∀ᶠ z in 𝓝 u, C.G (param z) = 0)
    (hinjective : Injective (fderiv ℝ param u)) :
    LinearMap.range ((fderiv ℝ param u).toLinearMap) =
      LinearMap.ker ((fderiv ℝ C.G (param u)).toLinearMap) := by
  have hpu : C.G (param u) = 0 := hfiber.self_of_nhds
  have hregular : Surjective (fderiv ℝ C.G (param u)) :=
    C.regular (param u) hpu
  have hcomp : fderiv ℝ (C.G ∘ param) u =
      (fderiv ℝ C.G (param u)).comp (fderiv ℝ param u) := by
    exact ((C.smooth.differentiable (by simp) (param u)).hasFDerivAt.comp u
      ((hsmooth.differentiable (by simp) u).hasFDerivAt)).fderiv
  have hzero : fderiv ℝ (C.G ∘ param) u = 0 := by
    calc
      fderiv ℝ (C.G ∘ param) u = fderiv ℝ (fun _ : E₂ => (0 : F)) u := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [hfiber] with z hz
        exact hz
      _ = 0 := by simp
  have hrange_le :
      LinearMap.range ((fderiv ℝ param u).toLinearMap) ≤
        LinearMap.ker ((fderiv ℝ C.G (param u)).toLinearMap) := by
    rintro w ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    have happ := congrArg
      (fun L : E₂ →L[ℝ] F => L z) (hcomp.symm.trans hzero)
    simpa [ContinuousLinearMap.comp_apply] using happ
  apply Submodule.eq_of_le_of_finrank_eq hrange_le
  rw [LinearMap.finrank_range_of_inj hinjective,
    finrank_euclideanSpace_fin,
    LocalIFTSurfaceChart.finrank_ker_fderiv C hregular]


-- @@ L101-115 verbatim
/-- Differential of ambient time along a smooth surface parameter. -/
theorem fderiv_surfaceTime_apply
    (param : E₂ → E') (hsmooth : ContDiff ℝ ∞ param) (u w : E₂) :
    fderiv ℝ (fun z => tcoord (param z)) u w =
      tcoord (fderiv ℝ param u w) := by
  let proj : E' →L[ℝ] ℝ :=
    EuclideanSpace.proj (Fin.last (n + 1))
  have hcomp : fderiv ℝ (proj ∘ param) u =
      proj.comp (fderiv ℝ param u) := by
    exact (proj.hasFDerivAt.comp u
      ((hsmooth.differentiable (by simp) u).hasFDerivAt)).fderiv
  change fderiv ℝ (proj ∘ param) u w =
    proj (fderiv ℝ param u w)
  rw [hcomp]
  rfl


-- @@ L117-154 verbatim
/-- A locally fiber-valued injective surface parameter detects ambient
time-critical points exactly by vanishing of the scalar differential of its
time coordinate. -/
theorem surfaceParam_mem_timeCritical_iff_fderiv_time_eq_zero
    (C : FramedLevelCobordism n) (param : E₂ → E') (u : E₂)
    (hsmooth : ContDiff ℝ ∞ param)
    (hfiber : ∀ᶠ z in 𝓝 u, C.G (param z) = 0)
    (hinjective : Injective (fderiv ℝ param u)) :
    param u ∈ timeCritical C.G ↔
      fderiv ℝ (fun z => tcoord (param z)) u = 0 := by
  have hpu : C.G (param u) = 0 := hfiber.self_of_nhds
  have hregular : Surjective (fderiv ℝ C.G (param u)) :=
    C.regular (param u) hpu
  have hrange := surfaceParam_fderiv_range_eq_ker C param u hsmooth
    hfiber hinjective
  rw [mem_timeCritical_iff_tcoord_eq_zero_on_ker hpu hregular]
  constructor
  · intro hcrit
    apply ContinuousLinearMap.ext
    intro w
    rw [fderiv_surfaceTime_apply param hsmooth]
    apply hcrit
    have hwker : fderiv ℝ param u w ∈ LinearMap.ker
        ((fderiv ℝ C.G (param u)).toLinearMap) := by
      rw [← hrange]
      exact ⟨w, rfl⟩
    exact LinearMap.mem_ker.mp hwker
  · intro htime w hw
    have hwker : w ∈ LinearMap.ker
        ((fderiv ℝ C.G (param u)).toLinearMap) := by
      exact LinearMap.mem_ker.mpr hw
    rw [← hrange] at hwker
    obtain ⟨z, hz⟩ := hwker
    calc
      tcoord w = tcoord (fderiv ℝ param u z) := congrArg tcoord hz.symm
      _ = fderiv ℝ (fun q => tcoord (param q)) u z :=
        (fderiv_surfaceTime_apply param hsmooth u z).symm
      _ = 0 := by rw [htime]; rfl


-- @@ L156-165 verbatim
/-- For a smooth scalar function on `E₂`, vanishing chart gradient is
equivalent to vanishing Fréchet differential. -/
theorem chartGradient_eq_zero_iff_fderiv_eq_zero
    {f : E₂ → ℝ} {u : E₂} :
    chartGradient f u = 0 ↔ fderiv ℝ f u = 0 := by
  constructor
  · exact fderiv_eq_zero_of_chartGradient_eq_zero
  · intro h
    rw [chartGradient, h]
    simp [scalarAdjointCLM]


-- @@ L167-178 verbatim
/-- The ambient time-critical locus pulled back by a regular two-dimensional
surface parameter is exactly its ordinary chart-critical locus. -/
theorem surfaceParam_mem_timeCritical_iff_chartGradient_eq_zero
    (C : FramedLevelCobordism n) (param : E₂ → E') (u : E₂)
    (hsmooth : ContDiff ℝ ∞ param)
    (hfiber : ∀ᶠ z in 𝓝 u, C.G (param z) = 0)
    (hinjective : Injective (fderiv ℝ param u)) :
    param u ∈ timeCritical C.G ↔
      chartGradient (fun z => tcoord (param z)) u = 0 := by
  rw [surfaceParam_mem_timeCritical_iff_fderiv_time_eq_zero C param u
    hsmooth hfiber hinjective,
    chartGradient_eq_zero_iff_fderiv_eq_zero]


-- @@ L180-180 verbatim
/-! ## Specialization to the existing IFT chart interface -/


-- @@ L182-182 verbatim
namespace IFTSurfaceChart


-- @@ L184-184 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L186-222 verbatim
/-- The lifted-coordinate identity forces the surface parameter differential
to be injective at every point having a full chart-domain neighborhood. -/
theorem fderiv_param_injective (P : IFTSurfaceChart C) {u : E₂}
    (hdom : P.domain ∈ 𝓝 u) : Injective (fderiv ℝ P.param u) := by
  intro x y hxy
  have hlift (q : E₂) :
      fderiv ℝ (fun z => P.liftCovector q (P.param z - P.center)) u =
        innerSL ℝ q := by
    calc
      fderiv ℝ (fun z => P.liftCovector q (P.param z - P.center)) u =
          fderiv ℝ (fun z => (innerSL ℝ q) z) u := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [hdom] with z hz
        exact P.lift_param q z hz
      _ = innerSL ℝ q := by
        exact (innerSL ℝ q).hasFDerivAt.fderiv
  have hchain (q : E₂) :
      fderiv ℝ (fun z => P.liftCovector q (P.param z - P.center)) u =
        (P.liftCovector q).comp (fderiv ℝ P.param u) := by
    exact ((P.liftCovector q).hasFDerivAt.comp u
      (((P.param_smooth.differentiable (by simp) u).hasFDerivAt).sub_const
        P.center)).fderiv
  let w : E₂ := x - y
  have hw : fderiv ℝ P.param u w = 0 := by
    dsimp [w]
    rw [map_sub, hxy, sub_self]
  have hinner : (innerSL ℝ w) w = 0 := by
    have hEq := (hchain w).symm.trans (hlift w)
    calc
      (innerSL ℝ w) w =
          P.liftCovector w (fderiv ℝ P.param u w) := by
        exact (congrArg (fun L : E₂ →L[ℝ] ℝ => L w) hEq).symm
      _ = 0 := by rw [hw]; simp
  have hnorm : ‖w‖ ^ 2 = 0 := by
    simpa [innerSL_apply_apply] using hinner
  have hwzero : w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  exact sub_eq_zero.mp hwzero


-- @@ L224-233 verbatim
/-- On a genuine local domain of an `IFTSurfaceChart`, ambient criticality is
exactly chart-gradient criticality. -/
theorem mem_timeCritical_iff_chartGradient_eq_zero
    (P : IFTSurfaceChart C) {u : E₂} (hdom : P.domain ∈ 𝓝 u) :
    P.param u ∈ timeCritical C.G ↔ chartGradient P.time u = 0 := by
  apply surfaceParam_mem_timeCritical_iff_chartGradient_eq_zero
    C P.param u P.param_smooth
  · filter_upwards [hdom] with z hz
    exact P.param_fiber z hz
  · exact P.fderiv_param_injective hdom


-- @@ L235-235 verbatim
end IFTSurfaceChart


-- @@ L237-237 verbatim
/-! ## Pulling an IFT parameter through a small vertical diffeomorphism -/


-- @@ L239-239 verbatim
namespace SmallVerticalAmplitude


-- @@ L241-272 verbatim
/-- The derivative of the smooth global inverse of a small vertical shift is
injective at every point.  This is proved directly by differentiating the
global inverse identity, so no manifold-coordinate API is needed. -/
theorem fderiv_equiv_symm_injective
    (a : SmallVerticalAmplitude (n := n)) (y : E') :
    Injective (fderiv ℝ a.equiv.symm y) := by
  have hchain :
      fderiv ℝ (verticalShift a ∘ a.equiv.symm) y =
        (fderiv ℝ (verticalShift a) (a.equiv.symm y)).comp
          (fderiv ℝ a.equiv.symm y) := by
    exact (((contDiff_verticalShift a.smooth).differentiable (by simp)
      (a.equiv.symm y)).hasFDerivAt.comp y
        ((a.contDiff_equiv_symm.differentiable (by simp) y).hasFDerivAt)).fderiv
  have hfun : verticalShift a ∘ a.equiv.symm = id := by
    funext z
    change a.equiv (a.equiv.symm z) = z
    exact a.equiv.apply_symm_apply z
  have hid : fderiv ℝ (verticalShift a ∘ a.equiv.symm) y =
      ContinuousLinearMap.id ℝ E' := by
    rw [hfun]
    exact hasFDerivAt_id y |>.fderiv
  have hcomp :
      (fderiv ℝ (verticalShift a) (a.equiv.symm y)).comp
          (fderiv ℝ a.equiv.symm y) =
        ContinuousLinearMap.id ℝ E' :=
    hchain.symm.trans hid
  intro x z hxz
  apply sub_eq_zero.mp
  have hzero : fderiv ℝ a.equiv.symm y (x - z) = 0 := by
    rw [map_sub, hxz, sub_self]
  have happ := congrArg (fun L : E' →L[ℝ] E' => L (x - z)) hcomp
  simpa [ContinuousLinearMap.comp_apply, hzero] using happ.symm


-- @@ L274-274 verbatim
end SmallVerticalAmplitude


-- @@ L276-276 verbatim
namespace IFTSurfaceChart


-- @@ L278-278 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L280-310 verbatim
/-- Pulling an IFT surface parameter through the inverse vertical
diffeomorphism gives a valid local parameter of the pulled-back zero surface.
Its ambient time-critical points are therefore exactly the zeros of the
gradient of its installed scalar time.

The sole locality hypothesis is that the original chart domain is a
neighborhood of the parameter under consideration. -/
theorem pullbackParam_mem_timeCritical_iff_chartGradient_eq_zero
    (P : IFTSurfaceChart C) (a : SmallVerticalAmplitude (n := n))
    {u : E₂} (hdom : P.domain ∈ 𝓝 u) :
    a.diffeomorph.symm (P.param u) ∈
        timeCritical (a.toVerticalAmplitude.pullback C).G ↔
      chartGradient
        (fun z => tcoord (a.diffeomorph.symm (P.param z))) u = 0 := by
  let param' : E₂ → E' := fun z => a.diffeomorph.symm (P.param z)
  apply surfaceParam_mem_timeCritical_iff_chartGradient_eq_zero
    (a.toVerticalAmplitude.pullback C) param' u
  · exact a.contDiff_equiv_symm.comp P.param_smooth
  · filter_upwards [hdom] with z hz
    change C.G (verticalShift a (a.diffeomorph.symm (P.param z))) = 0
    rw [← a.diffeomorph_apply, a.diffeomorph.apply_symm_apply]
    exact P.param_fiber z hz
  · have hchain : fderiv ℝ param' u =
        (fderiv ℝ a.equiv.symm (P.param u)).comp
          (fderiv ℝ P.param u) := by
      exact ((a.contDiff_equiv_symm.differentiable (by simp)
        (P.param u)).hasFDerivAt.comp u
          ((P.param_smooth.differentiable (by simp) u).hasFDerivAt)).fderiv
    rw [hchain]
    exact (a.fderiv_equiv_symm_injective (P.param u)).comp
      (P.fderiv_param_injective hdom)


-- @@ L312-312 verbatim
end IFTSurfaceChart


-- @@ L314-314 verbatim
end Submission
