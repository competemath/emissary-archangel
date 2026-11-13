import Mathlib
import Submission.MorseSharedGenericity
import Submission.MorseGenericity2D


-- @@ L5-17 verbatim
/-!
# One shared ambient affine height on all IFT charts

An ambient covector `A : E' →L[ℝ] ℝ` defines one honest global height
perturbation.  Its restriction to an IFT chart is

`u ↦ P.time u + A (P.param u)`.

This file packages the jointly smooth gradient and Hessian of that restriction.
It is the analytic state space for the finite sequential Sard construction:
changing `A` by `-P.liftCovector q` is exactly a chart-linear tilt (up to an
irrelevant constant), while compact Morse-goodness is open in `A`.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Set Function Filter

-- @@ L22-22 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L24-24 verbatim
namespace Submission


-- @@ L26-26 verbatim
variable {n : ℕ}


-- @@ L28-28 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L29-29 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L30-30 verbatim
local notation "Cov" => E' →L[ℝ] ℝ


-- @@ L32-32 verbatim
/-! ## Partial derivatives in the second product variable -/


-- @@ L34-41 verbatim
/-- Restrict the total derivative of a function on a product to directions in
the second factor. -/
def rightFDeriv {A B D : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (F : A × B → D) (z : A × B) : B →L[ℝ] D :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inr ℝ A B)


-- @@ L43-50 verbatim
theorem contDiff_rightFDeriv
    {A B D : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {F : A × B → D} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (rightFDeriv F) := by
  exact ContDiff.clm_comp (hF.fderiv_right (by simp)) contDiff_const


-- @@ L52-60 verbatim
theorem fderiv_section_eq_rightFDeriv
    {A B D : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {F : A × B → D} (hF : ContDiff ℝ ∞ F) (a : A) (b : B) :
    fderiv ℝ (fun y => F (a, y)) b = rightFDeriv F (a, b) := by
  exact ((hF.differentiable (by simp) (a, b)).hasFDerivAt.comp b
    (hasFDerivAt_prodMk_right a b)).fderiv


-- @@ L62-62 verbatim
/-! ## The shared affine chart jet -/


-- @@ L64-64 verbatim
namespace IFTSurfaceChart


-- @@ L66-66 verbatim
variable {C : FramedLevelCobordism n}


-- @@ L68-70 verbatim
/-- The restriction of one shared ambient affine height to a surface chart. -/
def sharedAffineHeight (P : IFTSurfaceChart C) (A : Cov) (u : E₂) : ℝ :=
  P.time u + A (P.param u)


-- @@ L72-74 verbatim
/-- Uncurried form used for joint parameter derivatives. -/
def sharedAffineHeightUncurried (P : IFTSurfaceChart C) : Cov × E₂ → ℝ :=
  fun z => P.sharedAffineHeight z.1 z.2


-- @@ L76-79 verbatim
theorem contDiff_sharedAffineHeightUncurried (P : IFTSurfaceChart C) :
    ContDiff ℝ ∞ P.sharedAffineHeightUncurried := by
  exact (P.contDiff_time.comp contDiff_snd).add
    (contDiff_fst.clm_apply (P.param_smooth.comp contDiff_snd))


-- @@ L81-84 verbatim
theorem contDiff_sharedAffineHeight (P : IFTSurfaceChart C) (A : Cov) :
    ContDiff ℝ ∞ (P.sharedAffineHeight A) := by
  exact P.contDiff_sharedAffineHeightUncurried.comp
    (contDiff_const.prodMk contDiff_id)


-- @@ L86-88 verbatim
/-- Joint Euclidean gradient of the shared affine chart height. -/
def sharedAffineGradient (P : IFTSurfaceChart C) (z : Cov × E₂) : E₂ :=
  scalarAdjointCLM (rightFDeriv P.sharedAffineHeightUncurried z) 1


-- @@ L90-94 verbatim
theorem contDiff_sharedAffineGradient (P : IFTSurfaceChart C) :
    ContDiff ℝ ∞ P.sharedAffineGradient := by
  exact (scalarAdjointCLM.contDiff.comp
    (contDiff_rightFDeriv P.contDiff_sharedAffineHeightUncurried)).clm_apply
      contDiff_const


-- @@ L96-104 verbatim
theorem sharedAffineGradient_eq_chartGradient
    (P : IFTSurfaceChart C) (A : Cov) (u : E₂) :
    P.sharedAffineGradient (A, u) = chartGradient (P.sharedAffineHeight A) u := by
  unfold sharedAffineGradient chartGradient
  have h := fderiv_section_eq_rightFDeriv
    P.contDiff_sharedAffineHeightUncurried A u
  change fderiv ℝ (P.sharedAffineHeight A) u =
    rightFDeriv P.sharedAffineHeightUncurried (A, u) at h
  rw [h]


-- @@ L106-110 verbatim
/-- Joint Hessian, represented as the derivative of the chart gradient in the
chart direction. -/
def sharedAffineHessian (P : IFTSurfaceChart C)
    (z : Cov × E₂) : E₂ →L[ℝ] E₂ :=
  rightFDeriv P.sharedAffineGradient z


-- @@ L112-114 verbatim
theorem contDiff_sharedAffineHessian (P : IFTSurfaceChart C) :
    ContDiff ℝ ∞ P.sharedAffineHessian :=
  contDiff_rightFDeriv P.contDiff_sharedAffineGradient


-- @@ L116-128 verbatim
theorem sharedAffineHessian_eq_fderiv_chartGradient
    (P : IFTSurfaceChart C) (A : Cov) (u : E₂) :
    P.sharedAffineHessian (A, u) =
      fderiv ℝ (chartGradient (P.sharedAffineHeight A)) u := by
  have h := fderiv_section_eq_rightFDeriv
    P.contDiff_sharedAffineGradient A u
  change fderiv ℝ (fun y => P.sharedAffineGradient (A, y)) u =
    P.sharedAffineHessian (A, u) at h
  have heq : (fun y => P.sharedAffineGradient (A, y)) =
      chartGradient (P.sharedAffineHeight A) := by
    funext y
    exact P.sharedAffineGradient_eq_chartGradient A y
  rw [← heq, h]


-- @@ L130-133 verbatim
/-- The jointly smooth first/second derivative jet. -/
def sharedAffineMorseJet (P : IFTSurfaceChart C)
    (z : Cov × E₂) : E₂ × (E₂ →L[ℝ] E₂) :=
  (P.sharedAffineGradient z, P.sharedAffineHessian z)


-- @@ L135-137 verbatim
theorem contDiff_sharedAffineMorseJet (P : IFTSurfaceChart C) :
    ContDiff ℝ ∞ P.sharedAffineMorseJet :=
  P.contDiff_sharedAffineGradient.prodMk P.contDiff_sharedAffineHessian


-- @@ L139-142 verbatim
/-- Morse-goodness of the shared affine height on a parameter subset. -/
def SharedAffineMorseOn (P : IFTSurfaceChart C)
    (A : Cov) (K : Set E₂) : Prop :=
  ∀ u ∈ K, P.sharedAffineMorseJet (A, u) ∈ MorseJetGood


-- @@ L144-152 verbatim
/-- Once a shared covector is Morse-good on a compact chart core, all nearby
shared covectors remain Morse-good on that entire core. -/
theorem eventually_sharedAffineMorseOn
    (P : IFTSurfaceChart C) {K : Set E₂} (hK : IsCompact K)
    (A : Cov) (hA : P.SharedAffineMorseOn A K) :
    ∀ᶠ B in 𝓝 A, P.SharedAffineMorseOn B K := by
  exact eventually_uniform_morseJetGood hK
    (fun B u => P.sharedAffineMorseJet (B, u))
    P.contDiff_sharedAffineMorseJet.continuous hA


-- @@ L154-154 verbatim
/-! ## Exact update by one chart Sard tilt -/


-- @@ L156-159 verbatim
/-- The stored chart covector lift, bundled as a continuous linear map in its
finite-dimensional source. -/
def liftCovectorCLM (P : IFTSurfaceChart C) : E₂ →L[ℝ] Cov :=
  P.liftCovector.toContinuousLinearMap


-- @@ L161-163 verbatim
@[simp] theorem liftCovectorCLM_apply
    (P : IFTSurfaceChart C) (q : E₂) :
    P.liftCovectorCLM q = P.liftCovector q := rfl


-- @@ L165-168 verbatim
/-- Update the one shared ambient covector by the tilt requested in chart
`P`. -/
def updateSharedCovector (P : IFTSurfaceChart C) (A : Cov) (q : E₂) : Cov :=
  A - P.liftCovectorCLM q


-- @@ L170-173 verbatim
theorem continuous_updateSharedCovector
    (P : IFTSurfaceChart C) (A : Cov) :
    Continuous (P.updateSharedCovector A) := by
  exact continuous_const.sub P.liftCovectorCLM.continuous


-- @@ L175-178 verbatim
theorem updateSharedCovector_zero
    (P : IFTSurfaceChart C) (A : Cov) :
    P.updateSharedCovector A 0 = A := by
  simp [updateSharedCovector]


-- @@ L180-201 verbatim
/-- On the valid chart domain, updating the ambient covector is exactly the
ordinary chart-linear tilt, up to one constant independent of `u`. -/
theorem sharedAffineHeight_update
    (P : IFTSurfaceChart C) (A : Cov) (q u : E₂)
    (hu : u ∈ P.domain) :
    P.sharedAffineHeight (P.updateSharedCovector A q) u =
      chartLinearTilt (P.sharedAffineHeight A) q u -
        P.liftCovector q P.center := by
  have hlift : P.liftCovector q (P.param u) =
      (innerSL ℝ q) u + P.liftCovector q P.center := by
    calc
      P.liftCovector q (P.param u) =
          P.liftCovector q ((P.param u - P.center) + P.center) := by
            rw [sub_add_cancel]
      _ = P.liftCovector q (P.param u - P.center) +
          P.liftCovector q P.center := by rw [map_add]
      _ = (innerSL ℝ q) u + P.liftCovector q P.center := by
        rw [P.lift_param q u hu]
  simp only [sharedAffineHeight, updateSharedCovector,
    liftCovectorCLM_apply, ContinuousLinearMap.sub_apply, chartLinearTilt]
  rw [hlift]
  ring


-- @@ L203-211 verbatim
/-- Germ form of the exact update identity. -/
theorem eventuallyEq_sharedAffineHeight_update
    (P : IFTSurfaceChart C) (A : Cov) (q : E₂) {u : E₂}
    (hdom : P.domain ∈ 𝓝 u) :
    P.sharedAffineHeight (P.updateSharedCovector A q) =ᶠ[𝓝 u]
      (fun z => chartLinearTilt (P.sharedAffineHeight A) q z -
        P.liftCovector q P.center) := by
  filter_upwards [hdom] with z hz
  exact P.sharedAffineHeight_update A q z hz


-- @@ L213-240 verbatim
/-- The chart gradient is shifted by exactly `q`. -/
theorem sharedAffineGradient_update
    (P : IFTSurfaceChart C) (A : Cov) (q : E₂) {u : E₂}
    (hdom : P.domain ∈ 𝓝 u) :
    P.sharedAffineGradient (P.updateSharedCovector A q, u) =
      P.sharedAffineGradient (A, u) - q := by
  rw [P.sharedAffineGradient_eq_chartGradient,
    P.sharedAffineGradient_eq_chartGradient]
  let f : E₂ → ℝ := P.sharedAffineHeight A
  let c : ℝ := P.liftCovector q P.center
  have heq := P.eventuallyEq_sharedAffineHeight_update A q hdom
  have htilt : ContDiff ℝ ∞ (chartLinearTilt f q) :=
    contDiff_chartLinearTilt (P.contDiff_sharedAffineHeight A) q
  have hfdconst :
      fderiv ℝ (fun z => chartLinearTilt f q z - c) u =
        fderiv ℝ (chartLinearTilt f q) u := by
    exact ((htilt.differentiable (by simp) u).hasFDerivAt.sub_const c).fderiv
  calc
    chartGradient (P.sharedAffineHeight (P.updateSharedCovector A q)) u =
        chartGradient (fun z => chartLinearTilt f q z - c) u := by
          unfold chartGradient
          rw [heq.fderiv_eq]
    _ = chartGradient (chartLinearTilt f q) u := by
      unfold chartGradient
      rw [hfdconst]
    _ = chartGradient f u - q :=
      chartGradient_chartLinearTilt
        ((P.contDiff_sharedAffineHeight A).differentiable (by simp)) q u


-- @@ L242-250 verbatim
/-- The exact gradient update holds throughout a neighborhood of every point
of the open chart domain. -/
theorem eventuallyEq_sharedAffineGradient_update
    (P : IFTSurfaceChart C) (hopen : IsOpen P.domain)
    (A : Cov) (q : E₂) {u : E₂} (hu : u ∈ P.domain) :
    (fun z => P.sharedAffineGradient (P.updateSharedCovector A q, z)) =ᶠ[𝓝 u]
      (fun z => P.sharedAffineGradient (A, z) - q) := by
  filter_upwards [hopen.mem_nhds hu] with z hz
  exact P.sharedAffineGradient_update A q (hopen.mem_nhds hz)


-- @@ L252-278 verbatim
/-- A chart Sard update translates the gradient but leaves the Hessian
unchanged on the open chart domain. -/
theorem sharedAffineHessian_update
    (P : IFTSurfaceChart C) (hopen : IsOpen P.domain)
    (A : Cov) (q : E₂) {u : E₂} (hu : u ∈ P.domain) :
    P.sharedAffineHessian (P.updateSharedCovector A q, u) =
      P.sharedAffineHessian (A, u) := by
  rw [P.sharedAffineHessian_eq_fderiv_chartGradient,
    P.sharedAffineHessian_eq_fderiv_chartGradient]
  have hnew :
      chartGradient (P.sharedAffineHeight (P.updateSharedCovector A q)) =
        fun z => P.sharedAffineGradient (P.updateSharedCovector A q, z) := by
    funext z
    exact (P.sharedAffineGradient_eq_chartGradient
      (P.updateSharedCovector A q) z).symm
  have hold :
      chartGradient (P.sharedAffineHeight A) =
        fun z => P.sharedAffineGradient (A, z) := by
    funext z
    exact (P.sharedAffineGradient_eq_chartGradient A z).symm
  rw [hnew, hold]
  have heq := P.eventuallyEq_sharedAffineGradient_update hopen A q hu
  rw [heq.fderiv_eq]
  have hsmooth : ContDiff ℝ ∞ (fun z => P.sharedAffineGradient (A, z)) :=
    P.contDiff_sharedAffineGradient.comp
      (contDiff_const.prodMk contDiff_id)
  exact (((hsmooth.differentiable (by simp)) u).hasFDerivAt.sub_const q).fderiv


-- @@ L280-313 verbatim
/-- A regular value of the current chart gradient makes the updated shared
ambient height Morse-good on every chosen subset of that chart domain. -/
theorem sharedAffineMorseOn_update_of_regularValue
    (P : IFTSurfaceChart C) (hopen : IsOpen P.domain)
    (A : Cov) (q : E₂)
    (hq : IsRegularValue (chartGradient (P.sharedAffineHeight A)) q)
    {K : Set E₂} (hK : K ⊆ P.domain) :
    P.SharedAffineMorseOn (P.updateSharedCovector A q) K := by
  intro u hu
  change P.sharedAffineGradient (P.updateSharedCovector A q, u) ≠ 0 ∨
    Bijective (P.sharedAffineHessian (P.updateSharedCovector A q, u))
  have huDom : u ∈ P.domain := hK hu
  by_cases hgrad :
      P.sharedAffineGradient (P.updateSharedCovector A q, u) ≠ 0
  · exact Or.inl hgrad
  · right
    have hshift := P.sharedAffineGradient_update A q
      (hopen.mem_nhds huDom)
    have hold : P.sharedAffineGradient (A, u) = q := by
      apply sub_eq_zero.mp
      rw [← hshift]
      exact not_ne_iff.mp hgrad
    have hvalue : chartGradient (P.sharedAffineHeight A) u = q := by
      rw [← P.sharedAffineGradient_eq_chartGradient]
      exact hold
    have hsurjOld : Surjective (P.sharedAffineHessian (A, u)) := by
      rw [P.sharedAffineHessian_eq_fderiv_chartGradient]
      exact hq u hvalue
    have hsurj :
        Surjective (P.sharedAffineHessian
          (P.updateSharedCovector A q, u)) := by
      rw [P.sharedAffineHessian_update hopen A q huDom]
      exact hsurjOld
    exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩


-- @@ L315-315 verbatim
end IFTSurfaceChart


-- @@ L317-317 verbatim
end Submission
