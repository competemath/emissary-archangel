import Mathlib
import Submission.PolarHadamardExtension
import Submission.FramedMorseCriticalSpatialRank
import Submission.FramedMorseDefiniteRescaledFrame


-- @@ L6-16 verbatim
/-!
# The rescaled normal row at an installed definite Morse event

At the critical center the spatial derivative loses exactly one output
direction.  We choose the canonical cokernel vector supplied by
`FramedMorseCriticalSpatialRank`, keep that output vector fixed, and pull it
back by the adjoint spatial derivative along the installed surface parameter.
The resulting map `criticalDefiniteNormalMap` vanishes at the Morse origin and
is smooth there.  Its polar first quotient therefore has the continuous
Hadamard extension supplied by `PolarHadamardExtension`.
-/


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Set Function Filter

-- @@ L21-21 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L23-23 verbatim
namespace Submission


-- @@ L25-25 verbatim
set_option autoImplicit false


-- @@ L27-27 verbatim
variable {n : ℕ}

-- @@ L28-28 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]

-- @@ L29-29 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L30-30 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L32-32 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L33-33 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L34-34 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L35-35 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L37-37 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L39-39 verbatim
/-! ## The actual critical center and its missing output direction -/


-- @@ L41-48 verbatim
/-- Taking adjoints of the spatial operators as a continuous linear map. -/
def spatialAdjointCLM :
    (E₁ →L[ℝ] F) →L[ℝ] (F →L[ℝ] E₁) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => map_add ContinuousLinearMap.adjoint A B
      map_smul' := fun c A => by
        rw [RingHom.id_apply, map_smulₛₗ, starRingEnd_apply, star_trivial] }


-- @@ L50-51 verbatim
@[simp] theorem spatialAdjointCLM_apply (A : E₁ →L[ℝ] F) :
    spatialAdjointCLM A = ContinuousLinearMap.adjoint A := rfl


-- @@ L53-60 verbatim
/-- The installed surface parameter sends its Morse origin to the actual
critical center in the pulled-back cobordism. -/
@[simp] theorem criticalSurfaceParam_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalSurfaceParam p hp 0 = R.criticalCenter p := by
  rw [criticalSurfaceParam, criticalCenter,
    (G.localMorseNormalForm p hp).param_zero, add_zero]


-- @@ L62-72 verbatim
/-- The actual installed center is time-critical. -/
theorem criticalCenter_mem_timeCritical
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalCenter p ∈
      timeCritical (R.amplitude.toVerticalAmplitude.pullback C).G := by
  have hzero : ‖(0 : E₂)‖ < (R.criticalModelShrink p hp).radius := by
    simpa using (R.criticalModelShrink p hp).radius_pos
  have hcritical := (R.critical_model p hp 0 hzero).mpr rfl
  rw [← R.criticalSurfaceParam_zero p hp]
  exact hcritical


-- @@ L74-81 verbatim
/-- A fixed nonzero vector in the one-dimensional missing output-normal line
at the actual installed center. -/
def criticalDefiniteCokernelVector
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) : F :=
  criticalOutputCokernelVector
    (R.amplitude.toVerticalAmplitude.pullback C)
    (R.criticalCenter p) (R.criticalCenter_mem_timeCritical p hp)


-- @@ L83-89 verbatim
theorem criticalDefiniteCokernelVector_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalDefiniteCokernelVector p hp ≠ 0 := by
  exact criticalOutputCokernelVector_ne_zero
    (R.amplitude.toVerticalAmplitude.pullback C)
    (R.criticalCenter p) (R.criticalCenter_mem_timeCritical p hp)


-- @@ L91-100 verbatim
theorem criticalDefiniteCokernelVector_mem_orthogonal
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalDefiniteCokernelVector p hp ∈
      (LinearMap.range
        ((spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
          (R.criticalCenter p)).toLinearMap))ᗮ := by
  exact criticalOutputCokernelVector_mem
    (R.amplitude.toVerticalAmplitude.pullback C)
    (R.criticalCenter p) (R.criticalCenter_mem_timeCritical p hp)


-- @@ L102-102 verbatim
/-! ## The vanishing normal map -/


-- @@ L104-113 verbatim
/-- Pull the fixed missing output vector back by the adjoint spatial
derivative along the actual installed critical surface. -/
def criticalDefiniteNormalMap
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) : E₁ :=
  ContinuousLinearMap.adjoint
      (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalSurfaceParam p hp u))
    (R.criticalDefiniteCokernelVector p hp)


-- @@ L115-122 verbatim
@[simp] theorem criticalDefiniteNormalMap_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalDefiniteNormalMap p hp 0 = 0 := by
  rw [criticalDefiniteNormalMap, R.criticalSurfaceParam_zero p hp]
  exact adjoint_spatialDeriv_criticalOutputCokernelVector
    (R.amplitude.toVerticalAmplitude.pullback C)
    (R.criticalCenter p) (R.criticalCenter_mem_timeCritical p hp)


-- @@ L124-143 verbatim
/-- The pulled-back normal map is smooth at the Morse origin. -/
theorem criticalDefiniteNormalMap_contDiffAt_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    ContDiffAt ℝ ∞ (R.criticalDefiniteNormalMap p hp) 0 := by
  let C' := R.amplitude.toVerticalAmplitude.pullback C
  have hspatial : ContDiff ℝ ∞ (spatialDeriv C'.G) := by
    change ContDiff ℝ ∞
      (fun z => (fderiv ℝ C'.G z).comp spaceInclL)
    exact ContDiff.clm_comp (contDiff_fderivCLM C'.smooth) contDiff_const
  have hadjoint : ContDiff ℝ ∞
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C'.G z)) := by
    simpa [Function.comp_def] using
      (spatialAdjointCLM (n := n)).contDiff.comp hspatial
  have happly : ContDiff ℝ ∞
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C'.G z)
        (R.criticalDefiniteCokernelVector p hp)) :=
    hadjoint.clm_apply contDiff_const
  exact happly.contDiffAt.comp 0
    (R.criticalSurfaceParam_contDiffAt_zero p hp)


-- @@ L145-149 verbatim
theorem criticalDefiniteNormalMap_differentiableAt_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    DifferentiableAt ℝ (R.criticalDefiniteNormalMap p hp) 0 :=
  (R.criticalDefiniteNormalMap_contDiffAt_zero p hp).differentiableAt (by simp)


-- @@ L151-151 verbatim
/-! ## The continuously filled polar normal row -/


-- @@ L153-157 verbatim
/-- The derivative which fills the normal row at polar radius zero. -/
def criticalDefiniteNormalLinearization
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) : E₂ →L[ℝ] E₁ :=
  fderiv ℝ (R.criticalDefiniteNormalMap p hp) 0


-- @@ L159-164 verbatim
theorem hasFDerivAt_criticalDefiniteNormalMap_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    HasFDerivAt (R.criticalDefiniteNormalMap p hp)
      (R.criticalDefiniteNormalLinearization p hp) 0 :=
  (R.criticalDefiniteNormalMap_differentiableAt_zero p hp).hasFDerivAt


-- @@ L166-175 verbatim
/-- The actual rescaled normal row.  At nonzero radius this is `a⁻¹` times
the pulled-back normal map; at radius zero it is filled by its derivative. -/
def criticalDefiniteNormalRow
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a theta : ℝ) : E₁ :=
  polarFirstQuotient
    (R.criticalDefiniteNormalMap p hp)
    (R.criticalDefiniteNormalLinearization p hp)
    (fun theta => definiteCircleParam 1 theta) (a, theta)


-- @@ L177-183 verbatim
@[simp] theorem criticalDefiniteNormalRow_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (theta : ℝ) :
    R.criticalDefiniteNormalRow p hp 0 theta =
      R.criticalDefiniteNormalLinearization p hp
        (definiteCircleParam 1 theta) := by
  simp [criticalDefiniteNormalRow, polarFirstQuotient]


-- @@ L185-195 verbatim
theorem criticalDefiniteNormalRow_eq_inv_smul
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    {a theta : ℝ} (ha : a ≠ 0) :
    R.criticalDefiniteNormalRow p hp a theta =
      a⁻¹ • R.criticalDefiniteNormalMap p hp
        (definiteCircleParam a theta) := by
  rw [criticalDefiniteNormalRow, polarFirstQuotient, if_neg ha]
  change a⁻¹ • R.criticalDefiniteNormalMap p hp
      (a • definiteCircleParam 1 theta) = _
  rw [← definiteCircleParam_eq_smul_unit a theta]


-- @@ L197-215 verbatim
/-- The rescaled actual normal row extends jointly continuously through every
point of the radius-zero angular circle. -/
theorem continuousAt_criticalDefiniteNormalRow_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) (theta₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ =>
      R.criticalDefiniteNormalRow p hp q.1 q.2) (0, theta₀) := by
  have hdirection : ContinuousAt
      (fun theta : ℝ => definiteCircleParam 1 theta) theta₀ := by
    apply Continuous.continuousAt
    unfold definiteCircleParam pairToMorseParam
    fun_prop
  simpa [criticalDefiniteNormalRow] using
    (continuousAt_polarFirstQuotient
      (R.criticalDefiniteNormalMap p hp)
      (R.criticalDefiniteNormalLinearization p hp)
      (fun theta : ℝ => definiteCircleParam 1 theta) theta₀
      (R.hasFDerivAt_criticalDefiniteNormalMap_zero p hp)
      (R.criticalDefiniteNormalMap_zero p hp) hdirection)


-- @@ L217-217 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L219-219 verbatim
end Submission
