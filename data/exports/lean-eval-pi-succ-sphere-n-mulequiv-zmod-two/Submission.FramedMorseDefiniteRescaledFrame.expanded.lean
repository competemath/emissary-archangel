import Mathlib
import Submission.FramedMorseDefiniteFrameClass


-- @@ L4-19 verbatim
/-!
# Rescaled tangent row at an installed definite Morse event

The raw slice frame is singular at the critical radius.  Its tangent row,
however, has a canonical nonsingular replacement: differentiate the installed
surface parameter in the *unit* angular direction rather than the radius-`a`
angular direction.  This file proves that this replacement

* extends jointly continuously to radius zero;
* spans the same oriented tangent line as the actual `tauField` at every
  positive radius; and
* has a canonical, nonzero scalar coefficient against the unit `tauField`.

These are the tangent-row ingredients of the positive raw-matrix
linearization used to compute the class of an actual birth/death circle.
-/


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Function Metric Filter InnerProductSpace

-- @@ L24-24 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-28 verbatim
set_option autoImplicit false


-- @@ L30-30 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L32-32 verbatim
/-! ## Polar scaling identities -/


-- @@ L34-37 verbatim
theorem definiteCircleParam_eq_smul_unit (a theta : ℝ) :
    definiteCircleParam a theta = a • definiteCircleParam 1 theta := by
  ext i
  fin_cases i <;> simp [definiteCircleParam, pairToMorseParam]


-- @@ L39-43 verbatim
theorem definiteCircleTangentParam_eq_smul_unit (a theta : ℝ) :
    definiteCircleTangentParam a theta =
      a • definiteCircleTangentParam 1 theta := by
  ext i
  fin_cases i <;> simp [definiteCircleTangentParam, pairToMorseParam]


-- @@ L45-54 verbatim
theorem definiteCircleTangentParam_unit_ne_zero (theta : ℝ) :
    definiteCircleTangentParam 1 theta ≠ 0 := by
  intro hzero
  have hsq := congrArg (fun u : E₂ => ‖u‖ ^ 2) hzero
  have hnorm : ‖definiteCircleTangentParam 1 theta‖ ^ 2 = 1 := by
    rw [definiteCircleTangentParam]
    simp only [norm_pairToMorseParam_sq]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [hnorm, norm_zero] at hsq
  norm_num at hsq


-- @@ L56-56 verbatim
/-! ## The installed parameter is `C¹` at the critical center -/


-- @@ L58-58 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L60-60 verbatim
variable {n : ℕ}

-- @@ L61-61 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]

-- @@ L62-62 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L63-63 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L65-65 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L66-66 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L68-83 verbatim
/-- Although the production shrink only records smoothness on a ball, the
original Morse parameter is smooth at zero.  Composition with the IFT chart
and the inverse vertical diffeomorphism therefore makes the actual installed
surface parameter smooth at its critical coordinate. -/
theorem criticalSurfaceParam_contDiffAt_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ContDiffAt ℝ ∞ (R.criticalSurfaceParam p hp) 0 := by
  have hshift : ContDiffAt ℝ ∞
      (fun u : E₂ => p.2 + (G.localMorseNormalForm p hp).param u) 0 :=
    contDiffAt_const.add (G.localMorseNormalForm p hp).param_contDiffAt
  have hchart : ContDiffAt ℝ ∞
      (fun u : E₂ => (B.chart p.1).param
        (p.2 + (G.localMorseNormalForm p hp).param u)) 0 :=
    (B.chart p.1).param_smooth.contDiffAt.comp 0 hshift
  exact R.amplitude.contDiff_equiv_symm.contDiffAt.comp 0 hchart


-- @@ L85-91 verbatim
/-- The differential of the installed parameter varies continuously at the
critical coordinate. -/
theorem continuousAt_fderiv_criticalSurfaceParam_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ContinuousAt (fderiv ℝ (R.criticalSurfaceParam p hp)) 0 :=
  (R.criticalSurfaceParam_contDiffAt_zero p hp).continuousAt_fderiv (by simp)


-- @@ L93-102 verbatim
/-- Spatial derivative of the installed parameter in the unit
counterclockwise angular direction.  Unlike the derivative in the literal
radius-`a` angular direction, this vector does not carry a vanishing factor
`a`. -/
def criticalDefiniteUnitTangent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a theta : ℝ) : E₁ :=
  spacePart (fderiv ℝ (R.criticalSurfaceParam p hp)
    (definiteCircleParam a theta) (definiteCircleTangentParam 1 theta))


-- @@ L104-109 verbatim
/-- Clockwise version used at a maximum. -/
def criticalDefiniteUnitTangentRev
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a theta : ℝ) : E₁ :=
  -R.criticalDefiniteUnitTangent p hp a theta


-- @@ L111-164 verbatim
/-- The rescaled tangent row is jointly continuous at every point of the
radius-zero circle.  Thus all angular dependence at radius zero is carried by
the critical jet, with no division-by-radius singularity. -/
theorem continuousAt_criticalDefiniteUnitTangent_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (theta₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ =>
      R.criticalDefiniteUnitTangent p hp q.1 q.2) (0, theta₀) := by
  have hparam : Continuous (fun q : ℝ × ℝ =>
      definiteCircleParam q.1 q.2) := by
    have heq : (fun q : ℝ × ℝ => definiteCircleParam q.1 q.2) =
        fun q => (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i =>
          if i = 0 then q.1 * Real.cos q.2 else q.1 * Real.sin q.2) := by
      funext q
      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
      ext i
      fin_cases i <;> simp [definiteCircleParam, pairToMorseParam]
    rw [heq]
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · convert continuous_fst.mul (Real.continuous_cos.comp continuous_snd) using 1 <;>
        funext q <;> simp [Function.comp_apply]
    · convert continuous_fst.mul (Real.continuous_sin.comp continuous_snd) using 1 <;>
        funext q <;> simp [Function.comp_apply]
  have htangent : Continuous (fun q : ℝ × ℝ =>
      definiteCircleTangentParam 1 q.2) := by
    have heq : (fun q : ℝ × ℝ => definiteCircleTangentParam 1 q.2) =
        fun q => (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i =>
          if i = 0 then -Real.sin q.2 else Real.cos q.2) := by
      funext q
      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
      ext i
      fin_cases i <;> simp [definiteCircleTangentParam, pairToMorseParam]
    rw [heq]
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · convert (Real.continuous_sin.comp continuous_snd).neg using 1 <;>
        funext q <;> simp [Function.comp_apply]
    · convert Real.continuous_cos.comp continuous_snd using 1 <;>
        funext q <;> simp [Function.comp_apply]
  have hparam0 : definiteCircleParam (0 : ℝ) theta₀ = 0 := by
    ext i
    fin_cases i <;> simp [definiteCircleParam, pairToMorseParam]
  have hD : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ (R.criticalSurfaceParam p hp)
        (definiteCircleParam q.1 q.2)) (0, theta₀) :=
    (R.continuousAt_fderiv_criticalSurfaceParam_zero p hp).comp_of_eq
      hparam.continuousAt hparam0
  exact continuous_spacePart.continuousAt.comp
    (hD.clm_apply htangent.continuousAt)


-- @@ L166-171 verbatim
theorem continuousAt_criticalDefiniteUnitTangentRev_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (theta₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ =>
      R.criticalDefiniteUnitTangentRev p hp q.1 q.2) (0, theta₀) :=
  (R.continuousAt_criticalDefiniteUnitTangent_zero p hp theta₀).neg


-- @@ L173-192 verbatim
/-- Restoring the radius factor recovers the literal transported angular
tangent used by the installed definite circle. -/
theorem smul_criticalDefiniteUnitTangent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a theta : ℝ) :
    a • R.criticalDefiniteUnitTangent p hp a theta =
      spacePart (fderiv ℝ (R.criticalSurfaceParam p hp)
        (definiteCircleParam a theta)
        (definiteCircleTangentParam a theta)) := by
  rw [definiteCircleTangentParam_eq_smul_unit, map_smul]
  change a • spacePart
      ((fderiv ℝ (R.criticalSurfaceParam p hp) (definiteCircleParam a theta))
        (definiteCircleTangentParam 1 theta)) =
    spacePart (a •
      (fderiv ℝ (R.criticalSurfaceParam p hp) (definiteCircleParam a theta))
        (definiteCircleTangentParam 1 theta))
  unfold spacePart
  ext i
  rfl


-- @@ L194-194 verbatim
/-! ## Canonical scalar against the actual oriented slice tangent -/


-- @@ L196-206 verbatim
/-- The explicit coefficient of the rescaled transported tangent along the
actual unit `tauField`. -/
def criticalMinimumTangentScale
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a theta : ℝ) : ℝ :=
  ⟪R.criticalDefiniteUnitTangent p hp a theta,
    tauField
      (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
        (tcoord (R.criticalDefiniteCircle p hp a theta)))
      (spacePart (R.criticalDefiniteCircle p hp a theta))⟫_ℝ


-- @@ L208-241 verbatim
/-- The unit transported tangent lies in the same line as `tauField` on every
positive minimum circle. -/
theorem criticalDefiniteUnitTangent_mem_span_tauField
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    {a theta : ℝ} (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius) :
    R.criticalDefiniteUnitTangent p hp a theta ∈
      Submodule.span ℝ {
        tauField
          (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
            (tcoord (R.criticalDefiniteCircle p hp a theta)))
          (spacePart (R.criticalDefiniteCircle p hp a theta))} := by
  let u := definiteCircleParam a theta
  have hu : ‖u‖ < (R.criticalModelShrink p hp).radius := by
    rw [show ‖u‖ = a by
      dsimp [u]
      exact norm_definiteCircleParam ha.le]
    exact hrad
  have hreg := R.criticalDefiniteCircle_regular p hp
    (theta := theta) ha hrad
  have hmem :=
    R.spacePart_fderiv_criticalSurfaceParam_morseLevelTangent_mem_span_tauField
      p hp u hu hreg
  rw [hindex, morseLevelTangent_minimum_definiteCircleParam] at hmem
  have hscaled := (Submodule.span ℝ {
      tauField
        (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
          (tcoord (R.criticalDefiniteCircle p hp a theta)))
        (spacePart (R.criticalDefiniteCircle p hp a theta))}).smul_mem
          a⁻¹ hmem
  rw [← R.smul_criticalDefiniteUnitTangent p hp a theta] at hscaled
  simpa [inv_smul_smul₀ ha.ne'] using hscaled


-- @@ L243-274 verbatim
/-- The rescaled transported tangent cannot vanish once the local chart
differential is injective. -/
theorem criticalDefiniteUnitTangent_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    {r a theta : ℝ} (ha : 0 < a) (har : a < r)
    (hradius : r ≤ (R.criticalModelShrink p hp).radius)
    (hinj : ∀ u : E₂, ‖u‖ < r →
      Injective (fderiv ℝ (R.criticalSurfaceParam p hp) u)) :
    R.criticalDefiniteUnitTangent p hp a theta ≠ 0 := by
  let u := definiteCircleParam a theta
  have hu : ‖u‖ < r := by
    rw [show ‖u‖ = a by
      dsimp [u]
      exact norm_definiteCircleParam ha.le]
    exact har
  have huShrink : ‖u‖ < (R.criticalModelShrink p hp).radius :=
    hu.trans_le hradius
  have hquad : morseQuadratic (G.localMorseNormalForm p hp).index
      (u 0, u 1) ≠ 0 := by
    rw [hindex]
    dsimp [u]
    rw [morseQuadratic_minimum_definiteCircleParam]
    exact pow_ne_zero 2 ha.ne'
  have hnonzero :=
    R.spacePart_fderiv_criticalSurfaceParam_morseLevelTangent_ne_zero
      p hp u huShrink (hinj u hu) hquad
  rw [hindex, morseLevelTangent_minimum_definiteCircleParam] at hnonzero
  intro hzero
  apply hnonzero
  rw [← R.smul_criticalDefiniteUnitTangent p hp a theta, hzero, smul_zero]


-- @@ L276-313 verbatim
/-- The inner-product coefficient reconstructs the rescaled tangent exactly.
In particular, it is a canonical continuous choice of the scalar whose mere
existence was previously known. -/
theorem criticalMinimumTangentScale_smul_tauField
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    {a theta : ℝ} (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius) :
    R.criticalMinimumTangentScale p hp a theta •
        tauField
          (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
            (tcoord (R.criticalDefiniteCircle p hp a theta)))
          (spacePart (R.criticalDefiniteCircle p hp a theta)) =
      R.criticalDefiniteUnitTangent p hp a theta := by
  let τ := tauField
    (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
      (tcoord (R.criticalDefiniteCircle p hp a theta)))
    (spacePart (R.criticalDefiniteCircle p hp a theta))
  have hmem := R.criticalDefiniteUnitTangent_mem_span_tauField
    p hp hindex (theta := theta) ha hrad
  change R.criticalDefiniteUnitTangent p hp a theta ∈
    Submodule.span ℝ {τ} at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hreg := R.criticalDefiniteCircle_regular p hp
    (theta := theta) ha hrad
  have hxreg : spacePart (R.criticalDefiniteCircle p hp a theta) ∈
      regularSet (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
        (tcoord (R.criticalDefiniteCircle p hp a theta))) :=
    spacePart_mem_regularSet_of_spatialDeriv_surjective
      (R.amplitude.toVerticalAmplitude.pullback C).smooth hreg
  have hτnorm : ‖τ‖ = 1 := norm_tauField hxreg
  have hcinner := congrArg (fun v : E₁ => ⟪v, τ⟫_ℝ) hc
  have hcscale : c = R.criticalMinimumTangentScale p hp a theta := by
    simpa [criticalMinimumTangentScale, τ, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hτnorm] using hcinner
  rw [← hcscale]
  exact hc


-- @@ L315-329 verbatim
theorem criticalMinimumTangentScale_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    {r a theta : ℝ} (ha : 0 < a) (har : a < r)
    (hradius : r ≤ (R.criticalModelShrink p hp).radius)
    (hinj : ∀ u : E₂, ‖u‖ < r →
      Injective (fderiv ℝ (R.criticalSurfaceParam p hp) u)) :
    R.criticalMinimumTangentScale p hp a theta ≠ 0 := by
  intro hzero
  have heq := R.criticalMinimumTangentScale_smul_tauField
    p hp hindex (theta := theta) ha (har.trans_le hradius)
  rw [hzero, zero_smul] at heq
  exact R.criticalDefiniteUnitTangent_ne_zero
    p hp hindex ha har hradius hinj heq.symm


-- @@ L331-331 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L333-333 verbatim
end Submission
