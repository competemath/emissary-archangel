import Mathlib
import Submission.FramedMorseDefiniteNormalRow


-- @@ L4-11 verbatim
/-!
# Center pairing of the rescaled definite normal row

This file computes the center value of the polar normal row against the two
transported tangent directions.  The coefficient is the Hessian of the local
Morse quadratic times the nonzero time-normal coefficient of the defining
map at the actual critical center.
-/


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
open Set Function Filter InnerProductSpace

-- @@ L16-16 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L18-18 verbatim
namespace Submission


-- @@ L20-20 verbatim
set_option autoImplicit false


-- @@ L22-22 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L24-30 verbatim
/-- The constant Hessian pairing of the standard two-dimensional Morse
quadratic. -/
def morseHessianPairing (e : MorseIndexTwo) (u w : E₂) : ℝ :=
  match e with
  | .minimum => 2 * (u 0 * w 0 + u 1 * w 1)
  | .saddle => 2 * (u 0 * w 0 - u 1 * w 1)
  | .maximum => -2 * (u 0 * w 0 + u 1 * w 1)


-- @@ L32-71 verbatim
/-- The derivative of a Morse quadratic is its Hessian pairing with the base
point. -/
theorem fderiv_const_add_morseQuadratic_apply
    (e : MorseIndexTwo) (c : ℝ) (u w : E₂) :
    fderiv ℝ (fun z : E₂ => c + morseQuadratic e (z 0, z 1)) u w =
      morseHessianPairing e u w := by
  let p0 : E₂ →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E₂ →L[ℝ] ℝ := EuclideanSpace.proj 1
  have h0 := (p0.hasFDerivAt : HasFDerivAt p0 p0 u).pow 2
  have h1 := (p1.hasFDerivAt : HasFDerivAt p1 p1 u).pow 2
  have hc : HasFDerivAt (fun _ : E₂ => c) (0 : E₂ →L[ℝ] ℝ) u :=
    hasFDerivAt_const c u
  cases e with
  | minimum =>
      have h := hc.add (h0.add h1)
      change HasFDerivAt
        (fun z : E₂ => c + (z 0 ^ 2 + z 1 ^ 2)) _ u at h
      change (fderiv ℝ
        (fun z : E₂ => c + (z 0 ^ 2 + z 1 ^ 2)) u) w = _
      rw [h.fderiv]
      simp [morseHessianPairing, p0, p1]
      ring
  | saddle =>
      have h := hc.add (h0.sub h1)
      change HasFDerivAt
        (fun z : E₂ => c + (z 0 ^ 2 - z 1 ^ 2)) _ u at h
      change (fderiv ℝ
        (fun z : E₂ => c + (z 0 ^ 2 - z 1 ^ 2)) u) w = _
      rw [h.fderiv]
      simp [morseHessianPairing, p0, p1]
      ring
  | maximum =>
      have h := hc.add (h0.neg.sub h1)
      change HasFDerivAt
        (fun z : E₂ => c + (-(z 0 ^ 2) - z 1 ^ 2)) _ u at h
      change (fderiv ℝ
        (fun z : E₂ => c + (-(z 0 ^ 2) - z 1 ^ 2)) u) w = _
      rw [h.fderiv]
      simp [morseHessianPairing, p0, p1]
      ring


-- @@ L73-83 verbatim
/-- The Hessian pairing, regarded as a continuous linear functional in its
first argument. -/
def morseHessianPairingLeft (e : MorseIndexTwo) (w : E₂) : E₂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => morseHessianPairing e u w
      map_add' := by
        intro u v
        cases e <;> simp [morseHessianPairing] <;> ring
      map_smul' := by
        intro a u
        cases e <;> simp [morseHessianPairing] <;> ring }


-- @@ L85-87 verbatim
@[simp] theorem morseHessianPairingLeft_apply
    (e : MorseIndexTwo) (u w : E₂) :
    morseHessianPairingLeft e w u = morseHessianPairing e u w := rfl


-- @@ L89-104 verbatim
/-- Differentiating the varying Morse differential recovers the constant
Hessian pairing. -/
theorem fderiv_morseDifferential_apply
    (e : MorseIndexTwo) (c : ℝ) (v w : E₂) :
    fderiv ℝ
        (fun u : E₂ =>
          fderiv ℝ (fun z : E₂ => c + morseQuadratic e (z 0, z 1)) u w)
        0 v = morseHessianPairing e v w := by
  have heq :
      (fun u : E₂ =>
        fderiv ℝ (fun z : E₂ => c + morseQuadratic e (z 0, z 1)) u w) =
      morseHessianPairingLeft e w := by
    funext u
    exact fderiv_const_add_morseQuadratic_apply e c u w
  rw [heq, (morseHessianPairingLeft e w).hasFDerivAt.fderiv]
  rfl


-- @@ L106-110 verbatim
@[simp] theorem morseHessianPairing_minimum_circle_self (theta : ℝ) :
    morseHessianPairing .minimum
      (definiteCircleParam 1 theta) (definiteCircleParam 1 theta) = 2 := by
  simp [morseHessianPairing]
  nlinarith [Real.sin_sq_add_cos_sq theta]


-- @@ L112-116 verbatim
@[simp] theorem morseHessianPairing_maximum_circle_self (theta : ℝ) :
    morseHessianPairing .maximum
      (definiteCircleParam 1 theta) (definiteCircleParam 1 theta) = -2 := by
  simp [morseHessianPairing]
  nlinarith [Real.sin_sq_add_cos_sq theta]


-- @@ L118-123 verbatim
@[simp] theorem morseHessianPairing_minimum_circle_tangent (theta : ℝ) :
    morseHessianPairing .minimum
      (definiteCircleParam 1 theta)
      (definiteCircleTangentParam 1 theta) = 0 := by
  simp [morseHessianPairing]
  ring


-- @@ L125-130 verbatim
@[simp] theorem morseHessianPairing_maximum_circle_tangent (theta : ℝ) :
    morseHessianPairing .maximum
      (definiteCircleParam 1 theta)
      (definiteCircleTangentParam 1 theta) = 0 := by
  simp [morseHessianPairing]
  ring


-- @@ L132-132 verbatim
variable {n : ℕ}

-- @@ L133-133 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]

-- @@ L134-134 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L135-135 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L137-137 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L138-138 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L139-139 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L141-141 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L143-154 verbatim
/-- Spatial projection as a continuous linear map. -/
def criticalSpacePartCLM : E' →L[ℝ] E₁ :=
  LinearMap.toContinuousLinearMap
    { toFun := spacePart
      map_add' := by
        intro x y
        ext i
        rfl
      map_smul' := by
        intro a x
        ext i
        rfl }


-- @@ L156-157 verbatim
@[simp] theorem criticalSpacePartCLM_apply (z : E') :
    criticalSpacePartCLM z = spacePart z := rfl


-- @@ L159-166 verbatim
/-- Pairing of the fixed cokernel vector with the full derivative in the
ambient time direction. -/
def criticalDefiniteTimeNormalCoefficient
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) : ℝ :=
  ⟪R.criticalDefiniteCokernelVector p hp,
    fderiv ℝ (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalCenter p) timeVec⟫_ℝ


-- @@ L168-210 verbatim
/-- Regularity of the full defining map forces the time-normal coefficient
to be nonzero: the fixed cokernel vector annihilates every spatial derivative,
so the time derivative is the only remaining direction that can detect it. -/
theorem criticalDefiniteTimeNormalCoefficient_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalDefiniteTimeNormalCoefficient p hp ≠ 0 := by
  let C' := R.amplitude.toVerticalAmplitude.pullback C
  let center := R.criticalCenter p
  let c := R.criticalDefiniteCokernelVector p hp
  let L := fderiv ℝ C'.G center
  let A := spatialDeriv C'.G center
  intro htime
  have hcenter : center ∈ timeCritical C'.G :=
    R.criticalCenter_mem_timeCritical p hp
  have hsurj : Surjective L := C'.regular center hcenter.1
  obtain ⟨z, hz⟩ := hsurj c
  have hadjoint : ContinuousLinearMap.adjoint A c = 0 := by
    exact adjoint_spatialDeriv_criticalOutputCokernelVector
      C' center hcenter
  have hdecomp :
      L z = A (spacePart z) + tcoord z • L timeVec := by
    calc
      L z = L (cobSpaceTime (spacePart z) (tcoord z)) := by
        rw [spaceTime_spacePart]
      _ = L (spaceInclL (spacePart z) + tcoord z • timeVec) := by
        rw [spaceTime_eq]
      _ = A (spacePart z) + tcoord z • L timeVec := by
        rw [map_add, map_smul]
        rfl
  have hspace : ⟪c, A (spacePart z)⟫_ℝ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hadjoint, inner_zero_left]
  have htime' : ⟪c, tcoord z • L timeVec⟫_ℝ = 0 := by
    rw [real_inner_smul_right]
    change tcoord z * R.criticalDefiniteTimeNormalCoefficient p hp = 0
    rw [htime, mul_zero]
  have hself : ⟪c, c⟫_ℝ = 0 := by
    calc
      ⟪c, c⟫_ℝ = ⟪c, L z⟫_ℝ := by rw [hz]
      _ = ⟪c, A (spacePart z) + tcoord z • L timeVec⟫_ℝ := by rw [hdecomp]
      _ = 0 := by rw [inner_add_right, hspace, htime', add_zero]
  exact (R.criticalDefiniteCokernelVector_ne_zero p hp)
    (inner_self_eq_zero.mp hself)


-- @@ L212-218 verbatim
/-- Spatial part of a parameter tangent along the actual installed critical
surface. -/
def criticalSurfaceSpatialTangent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u w : E₂) : E₁ :=
  spacePart (fderiv ℝ (R.criticalSurfaceParam p hp) u w)


-- @@ L220-228 verbatim
/-- The same time-normal coefficient, allowed to vary along the installed
surface parameter. -/
def criticalDefiniteTimeNormalCoefficientAt
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) : ℝ :=
  ⟪R.criticalDefiniteCokernelVector p hp,
    fderiv ℝ (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSurfaceParam p hp u) timeVec⟫_ℝ


-- @@ L230-236 verbatim
@[simp] theorem criticalDefiniteTimeNormalCoefficientAt_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalDefiniteTimeNormalCoefficientAt p hp 0 =
      R.criticalDefiniteTimeNormalCoefficient p hp := by
  simp [criticalDefiniteTimeNormalCoefficientAt,
    criticalDefiniteTimeNormalCoefficient]


-- @@ L238-290 verbatim
/-- Exact first-order pairing identity along the installed zero surface.  It
is the differentiated zero-fiber equation, split into spatial and time
components and paired with the fixed cokernel vector. -/
theorem inner_criticalDefiniteNormalMap_criticalSurfaceSpatialTangent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (w : E₂) :
    ⟪R.criticalDefiniteNormalMap p hp u,
      R.criticalSurfaceSpatialTangent p hp u w⟫_ℝ =
      -(fderiv ℝ (fun z : E₂ =>
          G.localSeparatedTime p p.2 +
            morseQuadratic (G.localMorseNormalForm p hp).index (z 0, z 1))
        u w * R.criticalDefiniteTimeNormalCoefficientAt p hp u) := by
  let C' := R.amplitude.toVerticalAmplitude.pullback C
  let Φ := R.criticalSurfaceParam p hp
  let c := R.criticalDefiniteCokernelVector p hp
  let z := fderiv ℝ Φ u w
  let A := spatialDeriv C'.G (Φ u)
  let L := fderiv ℝ C'.G (Φ u)
  have hzero : L z = 0 := by
    exact R.fderiv_criticalSurfaceParam_mem_ker p hp u hu w
  have hdecomp :
      A (spacePart z) + tcoord z • L timeVec = 0 := by
    calc
      A (spacePart z) + tcoord z • L timeVec =
          L (spaceInclL (spacePart z) + tcoord z • timeVec) := by
            rw [map_add, map_smul]
            rfl
      _ = L (cobSpaceTime (spacePart z) (tcoord z)) := by
            rw [spaceTime_eq]
      _ = L z := by rw [spaceTime_spacePart]
      _ = 0 := hzero
  have hspatial : A (spacePart z) = -(tcoord z • L timeVec) :=
    eq_neg_of_add_eq_zero_left hdecomp
  have htime := R.fderiv_criticalSurfaceParam_time_apply p hp u hu w
  have hmodel := congrArg (fun D : E₂ →L[ℝ] ℝ => D w)
    (R.fderiv_criticalSurfaceParam_time p hp u hu)
  calc
    ⟪R.criticalDefiniteNormalMap p hp u,
        R.criticalSurfaceSpatialTangent p hp u w⟫_ℝ =
        ⟪c, A (spacePart z)⟫_ℝ := by
          exact ContinuousLinearMap.adjoint_inner_left A (spacePart z) c
    _ = ⟪c, -(tcoord z • L timeVec)⟫_ℝ := by rw [hspatial]
    _ = -(tcoord z * ⟪c, L timeVec⟫_ℝ) := by
          rw [inner_neg_right, real_inner_smul_right]
    _ = -(fderiv ℝ (fun z : E₂ =>
          G.localSeparatedTime p p.2 +
            morseQuadratic (G.localMorseNormalForm p hp).index (z 0, z 1))
        u w * R.criticalDefiniteTimeNormalCoefficientAt p hp u) := by
          congr 1
          rw [← htime, hmodel]
          rfl


-- @@ L292-299 verbatim
/-- Scalar pairing whose derivative at the origin records the center normal
row against a transported parameter tangent. -/
def criticalNormalTangentPairing
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (w u : E₂) : ℝ :=
  ⟪R.criticalDefiniteNormalMap p hp u,
    R.criticalSurfaceSpatialTangent p hp u w⟫_ℝ


-- @@ L301-396 verbatim
/-- Center linearization formula: pairing the derivative of the vanishing
normal map with a center tangent is exactly minus the local Morse Hessian,
times the nonzero time-normal coefficient. -/
theorem inner_criticalDefiniteNormalLinearization_surfaceTangent_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (v w : E₂) :
    ⟪R.criticalDefiniteNormalLinearization p hp v,
      R.criticalSurfaceSpatialTangent p hp 0 w⟫_ℝ =
      -(morseHessianPairing
          (G.localMorseNormalForm p hp).index v w *
        R.criticalDefiniteTimeNormalCoefficient p hp) := by
  let Φ := R.criticalSurfaceParam p hp
  let e := (G.localMorseNormalForm p hp).index
  let c₀ := G.localSeparatedTime p p.2
  let qdiff : E₂ → ℝ := fun u =>
    fderiv ℝ (fun z : E₂ => c₀ + morseQuadratic e (z 0, z 1)) u w
  let k : E₂ → ℝ := R.criticalDefiniteTimeNormalCoefficientAt p hp
  let pair : E₂ → ℝ := R.criticalNormalTangentPairing p hp w
  have hΦ : ContDiffAt ℝ ∞ Φ 0 :=
    R.criticalSurfaceParam_contDiffAt_zero p hp
  have hDΦ : ContDiffAt ℝ ∞ (fderiv ℝ Φ) 0 :=
    hΦ.fderiv_right (by simp)
  have htangentCD : ContDiffAt ℝ ∞
      (R.criticalSurfaceSpatialTangent p hp · w) 0 := by
    have heval : ContDiffAt ℝ ∞ (fun u => fderiv ℝ Φ u w) 0 :=
      hDΦ.clm_apply contDiffAt_const
    have hproj := (criticalSpacePartCLM (n := n)).contDiff.contDiffAt.comp 0 heval
    simpa [criticalSurfaceSpatialTangent, Φ, Function.comp_def] using hproj
  have htangent : DifferentiableAt ℝ
      (R.criticalSurfaceSpatialTangent p hp · w) 0 :=
    htangentCD.differentiableAt (by simp)
  have hnormal : DifferentiableAt ℝ
      (R.criticalDefiniteNormalMap p hp) 0 :=
    R.criticalDefiniteNormalMap_differentiableAt_zero p hp
  have hleft :
      fderiv ℝ pair 0 v =
        ⟪R.criticalDefiniteNormalLinearization p hp v,
          R.criticalSurfaceSpatialTangent p hp 0 w⟫_ℝ := by
    change fderiv ℝ (fun u =>
      ⟪R.criticalDefiniteNormalMap p hp u,
        R.criticalSurfaceSpatialTangent p hp u w⟫_ℝ) 0 v = _
    rw [fderiv_inner_apply ℝ hnormal htangent v]
    simp [criticalDefiniteNormalLinearization]
  have hqeq : qdiff = morseHessianPairingLeft e w := by
    funext u
    exact fderiv_const_add_morseQuadratic_apply e c₀ u w
  have hq : DifferentiableAt ℝ qdiff 0 := by
    rw [hqeq]
    exact (morseHessianPairingLeft e w).differentiableAt
  have hqzero : qdiff 0 = 0 := by
    rw [hqeq]
    cases e <;> simp [morseHessianPairing]
  have hqderiv : fderiv ℝ qdiff 0 v = morseHessianPairing e v w := by
    exact fderiv_morseDifferential_apply e c₀ v w
  have hkCD : ContDiffAt ℝ ∞ k 0 := by
    let C' := R.amplitude.toVerticalAmplitude.pullback C
    have hDG : ContDiff ℝ ∞ (fderiv ℝ C'.G) := contDiff_fderivCLM C'.smooth
    have hcomp : ContDiffAt ℝ ∞ (fun u => fderiv ℝ C'.G (Φ u)) 0 :=
      hDG.contDiffAt.comp 0 hΦ
    have heval : ContDiffAt ℝ ∞
        (fun u => fderiv ℝ C'.G (Φ u) timeVec) 0 :=
      hcomp.clm_apply contDiffAt_const
    have hinner := (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _u : E₂ => R.criticalDefiniteCokernelVector p hp) 0).inner ℝ heval
    change ContDiffAt ℝ ∞ (fun u : E₂ =>
      ⟪R.criticalDefiniteCokernelVector p hp,
        fderiv ℝ C'.G (Φ u) timeVec⟫_ℝ) 0
    exact hinner
  have hk : DifferentiableAt ℝ k 0 := hkCD.differentiableAt (by simp)
  have hkzero : k 0 = R.criticalDefiniteTimeNormalCoefficient p hp := by
    exact R.criticalDefiniteTimeNormalCoefficientAt_zero p hp
  have hevent :
      pair =ᶠ[nhds 0] fun u => -(qdiff u * k u) := by
    have hball : Metric.ball (0 : E₂) (R.criticalModelShrink p hp).radius ∈
        nhds 0 := Metric.ball_mem_nhds 0
          (R.criticalModelShrink p hp).radius_pos
    filter_upwards [hball] with u hu
    have hu' : ‖u‖ < (R.criticalModelShrink p hp).radius := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    exact R.inner_criticalDefiniteNormalMap_criticalSurfaceSpatialTangent
      p hp u hu' w
  have hright :
      fderiv ℝ (fun u => -(qdiff u * k u)) 0 v =
        -(morseHessianPairing e v w *
          R.criticalDefiniteTimeNormalCoefficient p hp) := by
    have hderiv := (hq.hasFDerivAt.mul hk.hasFDerivAt).neg.fderiv
    change (fderiv ℝ (-(qdiff * k)) 0) v = _
    rw [hderiv]
    simp only [neg_apply, smul_apply, hqzero, zero_smul, zero_add,
      hqderiv, hkzero]
    ring
  have hfdEq := congrArg (fun D : E₂ →L[ℝ] ℝ => D v) hevent.fderiv_eq
  rw [hleft] at hfdEq
  rw [hright] at hfdEq
  exact hfdEq


-- @@ L398-398 verbatim
/-! ## Radial and angular center pairings for definite events -/


-- @@ L400-405 verbatim
/-- The transported radial tangent at the actual critical center. -/
def criticalDefiniteRadialTangent
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) : E₁ :=
  R.criticalSurfaceSpatialTangent p hp 0 (definiteCircleParam 1 theta)


-- @@ L407-417 verbatim
theorem criticalSurfaceSpatialTangent_zero_tangent_eq
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (theta : ℝ) :
    R.criticalSurfaceSpatialTangent p hp 0
        (definiteCircleTangentParam 1 theta) =
      R.criticalDefiniteUnitTangent p hp 0 theta := by
  have hzero : definiteCircleParam 0 theta = (0 : E₂) := by
    ext i
    fin_cases i <;> simp
  rw [criticalSurfaceSpatialTangent, criticalDefiniteUnitTangent, hzero]


-- @@ L419-433 verbatim
/-- At a minimum, the center normal/radial pairing is the nonzero scalar
`-2κ`. -/
theorem inner_criticalDefiniteNormalRow_zero_radial_minimum
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalDefiniteRadialTangent p hp theta⟫_ℝ =
      -(2 * R.criticalDefiniteTimeNormalCoefficient p hp) := by
  rw [R.criticalDefiniteNormalRow_zero p hp theta]
  unfold criticalDefiniteRadialTangent
  rw [R.inner_criticalDefiniteNormalLinearization_surfaceTangent_zero
    p hp (definiteCircleParam 1 theta) (definiteCircleParam 1 theta), hindex]
  simp


-- @@ L435-444 verbatim
theorem inner_criticalDefiniteNormalRow_zero_radial_minimum_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalDefiniteRadialTangent p hp theta⟫_ℝ ≠ 0 := by
  rw [R.inner_criticalDefiniteNormalRow_zero_radial_minimum p hp hindex theta]
  exact neg_ne_zero.mpr (mul_ne_zero (by norm_num)
    (R.criticalDefiniteTimeNormalCoefficient_ne_zero p hp))


-- @@ L446-460 verbatim
/-- At a maximum, the sign of the Morse Hessian reverses and the center
normal/radial pairing is `2κ`. -/
theorem inner_criticalDefiniteNormalRow_zero_radial_maximum
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalDefiniteRadialTangent p hp theta⟫_ℝ =
      2 * R.criticalDefiniteTimeNormalCoefficient p hp := by
  rw [R.criticalDefiniteNormalRow_zero p hp theta]
  unfold criticalDefiniteRadialTangent
  rw [R.inner_criticalDefiniteNormalLinearization_surfaceTangent_zero
    p hp (definiteCircleParam 1 theta) (definiteCircleParam 1 theta), hindex]
  simp


-- @@ L462-471 verbatim
theorem inner_criticalDefiniteNormalRow_zero_radial_maximum_ne_zero
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalDefiniteRadialTangent p hp theta⟫_ℝ ≠ 0 := by
  rw [R.inner_criticalDefiniteNormalRow_zero_radial_maximum p hp hindex theta]
  exact mul_ne_zero (by norm_num)
    (R.criticalDefiniteTimeNormalCoefficient_ne_zero p hp)


-- @@ L473-486 verbatim
/-- The minimum Hessian has no mixed radial/angular term. -/
theorem inner_criticalDefiniteNormalRow_zero_unitTangent_minimum
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalDefiniteUnitTangent p hp 0 theta⟫_ℝ = 0 := by
  rw [← R.criticalSurfaceSpatialTangent_zero_tangent_eq p hp theta,
    R.criticalDefiniteNormalRow_zero p hp theta,
    R.inner_criticalDefiniteNormalLinearization_surfaceTangent_zero
      p hp (definiteCircleParam 1 theta)
        (definiteCircleTangentParam 1 theta), hindex]
  simp


-- @@ L488-501 verbatim
/-- The maximum Hessian likewise has no mixed radial/angular term. -/
theorem inner_criticalDefiniteNormalRow_zero_unitTangent_maximum
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (theta : ℝ) :
    ⟪R.criticalDefiniteNormalRow p hp 0 theta,
      R.criticalDefiniteUnitTangent p hp 0 theta⟫_ℝ = 0 := by
  rw [← R.criticalSurfaceSpatialTangent_zero_tangent_eq p hp theta,
    R.criticalDefiniteNormalRow_zero p hp theta,
    R.inner_criticalDefiniteNormalLinearization_surfaceTangent_zero
      p hp (definiteCircleParam 1 theta)
        (definiteCircleTangentParam 1 theta), hindex]
  simp


-- @@ L503-503 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L505-505 verbatim
end Submission
