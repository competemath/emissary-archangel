import Submission.FramedMorseDefiniteCenterClass


-- @@ L3-12 verbatim
/-!
# The definite center class for production Morse events

The first center-class calculation was tied to
`ExactFiniteMorseJetInstallation`.  The production construction instead
ends in a `StandardMorseEventAt`, together with a small ball on which its
parameter has injective differential.  This file rebuilds the center jet from
precisely that common interface.  In particular, none of the shared-cutoff or
critical-value-shift implementation is used in the local linear algebra below.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Set Function Filter InnerProductSpace Matrix Metric

-- @@ L17-17 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
set_option autoImplicit false

-- @@ L22-22 verbatim
set_option maxHeartbeats 1600000


-- @@ L24-24 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L26-26 verbatim
namespace StandardMorseEventAt


-- @@ L28-28 verbatim
open ExactFiniteMorseJetInstallation


-- @@ L30-30 verbatim
variable {a : ℕ}

-- @@ L31-31 verbatim
variable {C : FramedLevelCobordism (a + 2)}

-- @@ L32-32 verbatim
variable {center : EuclideanSpace ℝ (Fin (a + 4))}

-- @@ L33-33 verbatim
variable {M : StandardMorseEventAt C center}


-- @@ L35-35 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (a + 3))

-- @@ L36-36 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (a + 4))

-- @@ L37-37 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (a + 2))


-- @@ L39-50 verbatim
/-- The portion of a production event's embedded-shrink witness needed by
the center-jet calculation.  It is kept independent of the later orbit-chart
packaging, so the analytic center calculation and the embedding construction
can be built in parallel. -/
structure CenterImmersion (M : StandardMorseEventAt C center) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ M.radius
  param_differentiableAt : ∀ u : E₂, ‖u‖ < radius →
    DifferentiableAt ℝ M.param u
  fderiv_param_injective : ∀ u : E₂, ‖u‖ < radius →
    Injective (fderiv ℝ M.param u)


-- @@ L52-52 verbatim
/-! ## Differential identities supplied by an embedded standard event -/


-- @@ L54-57 verbatim
/-- Spatial part of the event-parameter differential. -/
def centerSpatialTangent (M : StandardMorseEventAt C center)
    (u w : E₂) : E₁ :=
  spacePart (fderiv ℝ M.param u w)


-- @@ L59-76 verbatim
/-- Differentiating the exact time model inside the event ball. -/
theorem fderiv_param_time (T : M.CenterImmersion)
    (u : E₂) (hu : ‖u‖ < T.radius) :
    fderiv ℝ (fun z : E₂ => tcoord (M.param z)) u =
      fderiv ℝ (fun z : E₂ =>
        tcoord center + morseQuadratic M.index (z 0, z 1)) u := by
  have huball : u ∈ ball (0 : E₂) T.radius := by
    simpa [mem_ball, dist_zero_right] using hu
  have heq :
      (fun z : E₂ => tcoord (M.param z)) =ᶠ[nhds u]
        (fun z : E₂ =>
          tcoord center + morseQuadratic M.index (z 0, z 1)) := by
    filter_upwards [isOpen_ball.mem_nhds huball] with z hz
    apply M.time_model z
    have hzr : ‖z‖ < T.radius := by
      simpa [mem_ball, dist_zero_right] using hz
    exact hzr.trans_le T.radius_le
  exact heq.fderiv_eq


-- @@ L78-93 verbatim
/-- Local chain rule for the time coordinate of the event parameter. -/
theorem fderiv_param_time_apply (T : M.CenterImmersion)
    (u : E₂) (hu : ‖u‖ < T.radius) (w : E₂) :
    fderiv ℝ (fun z : E₂ => tcoord (M.param z)) u w =
      tcoord (fderiv ℝ M.param u w) := by
  let proj : E' →L[ℝ] ℝ :=
    EuclideanSpace.proj (Fin.last (a + 3)) (𝕜 := ℝ)
  have h := proj.hasFDerivAt.comp u
    (T.param_differentiableAt u hu).hasFDerivAt
  have hfd := h.fderiv
  change fderiv ℝ (proj ∘ M.param) u =
      proj.comp (fderiv ℝ M.param u) at hfd
  change (fderiv ℝ (proj ∘ M.param) u) w =
    proj (fderiv ℝ M.param u w)
  rw [hfd]
  rfl


-- @@ L95-122 verbatim
/-- The event-parameter differential is killed by the full defining-map
differential throughout the embedded ball. -/
theorem fderiv_param_mem_ker (T : M.CenterImmersion)
    (u : E₂) (hu : ‖u‖ < T.radius) (w : E₂) :
    fderiv ℝ C.G (M.param u) (fderiv ℝ M.param u w) = 0 := by
  have huball : u ∈ ball (0 : E₂) T.radius := by
    simpa [mem_ball, dist_zero_right] using hu
  have hzeroEventually :
      (fun z : E₂ => C.G (M.param z)) =ᶠ[nhds u]
        (fun _ : E₂ => (0 : F)) := by
    filter_upwards [isOpen_ball.mem_nhds huball] with z hz
    apply M.param_fiber z
    have hzr : ‖z‖ < T.radius := by
      simpa [mem_ball, dist_zero_right] using hz
    exact hzr.trans_le T.radius_le
  have hzero : fderiv ℝ (fun z : E₂ => C.G (M.param z)) u = 0 := by
    rw [hzeroEventually.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : F) u).fderiv
  have hchain : fderiv ℝ (fun z : E₂ => C.G (M.param z)) u =
      (fderiv ℝ C.G (M.param u)).comp (fderiv ℝ M.param u) := by
    exact ((C.smooth.differentiable (by simp) (M.param u)).hasFDerivAt.comp u
      (T.param_differentiableAt u hu).hasFDerivAt).fderiv
  have hcomp :
      (fderiv ℝ C.G (M.param u)).comp (fderiv ℝ M.param u) = 0 := by
    rw [← hchain]
    exact hzero
  have happ := congrArg (fun L : E₂ →L[ℝ] F => L w) hcomp
  simpa using happ


-- @@ L124-132 verbatim
/-- Every center parameter tangent has zero time component. -/
theorem tcoord_fderiv_param_zero (T : M.CenterImmersion) (w : E₂) :
    tcoord (fderiv ℝ M.param 0 w) = 0 := by
  have hzero : ‖(0 : E₂)‖ < T.radius := by
    simpa using T.radius_pos
  rw [← fderiv_param_time_apply T 0 hzero w,
    fderiv_param_time T 0 hzero]
  rw [fderiv_const_add_morseQuadratic_apply]
  cases M.index <;> simp [morseHessianPairing]


-- @@ L134-157 verbatim
/-- Spatial projection of the center differential is injective. -/
theorem centerSpatialTangent_zero_ne_zero (T : M.CenterImmersion)
    {w : E₂} (hw : w ≠ 0) :
    M.centerSpatialTangent 0 w ≠ 0 := by
  have hzero : ‖(0 : E₂)‖ < T.radius := by
    simpa using T.radius_pos
  have hfullinj := T.fderiv_param_injective 0 hzero
  intro hspace
  let z := fderiv ℝ M.param 0 w
  have htime : tcoord z = 0 := tcoord_fderiv_param_zero T w
  have hz : z = 0 := by
    calc
      z = cobSpaceTime (spacePart z) (tcoord z) :=
        (spaceTime_spacePart z).symm
      _ = cobSpaceTime 0 0 := by
        rw [show spacePart z = 0 by exact hspace, htime]
      _ = 0 := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [spaceTime_apply_last]
          rfl
        · rw [spaceTime_apply_castSucc]
          rfl
  exact hw (hfullinj (by simpa [z] using hz))


-- @@ L159-159 verbatim
/-! ## The missing output direction and its center normal jet -/


-- @@ L161-164 verbatim
/-- Fixed nonzero vector in the missing output-normal line at the event
center. -/
def centerCokernelVector (M : StandardMorseEventAt C center) : F :=
  criticalOutputCokernelVector C center M.center_mem_timeCritical


-- @@ L166-168 verbatim
theorem centerCokernelVector_ne_zero (M : StandardMorseEventAt C center) :
    M.centerCokernelVector ≠ 0 :=
  criticalOutputCokernelVector_ne_zero C center M.center_mem_timeCritical


-- @@ L170-173 verbatim
/-- Pull the fixed missing output vector back along the spatial derivative. -/
def centerNormalMap (M : StandardMorseEventAt C center) (u : E₂) : E₁ :=
  ContinuousLinearMap.adjoint (spatialDeriv C.G (M.param u))
    M.centerCokernelVector


-- @@ L175-179 verbatim
@[simp] theorem centerNormalMap_zero (M : StandardMorseEventAt C center) :
    M.centerNormalMap 0 = 0 := by
  rw [centerNormalMap, M.param_zero]
  exact adjoint_spatialDeriv_criticalOutputCokernelVector
    C center M.center_mem_timeCritical


-- @@ L181-196 verbatim
theorem centerNormalMap_contDiffAt_zero
    (M : StandardMorseEventAt C center) :
    ContDiffAt ℝ ∞ M.centerNormalMap 0 := by
  have hspatial : ContDiff ℝ ∞ (spatialDeriv C.G) := by
    change ContDiff ℝ ∞ (fun z => (fderiv ℝ C.G z).comp spaceInclL)
    exact ContDiff.clm_comp (contDiff_fderivCLM C.smooth) contDiff_const
  have hadjoint : ContDiff ℝ ∞
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C.G z)) := by
    simpa [Function.comp_def] using
      (ExactFiniteMorseJetInstallation.spatialAdjointCLM
        (n := a + 2)).contDiff.comp hspatial
  have happly : ContDiff ℝ ∞
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C.G z)
        M.centerCokernelVector) :=
    hadjoint.clm_apply contDiff_const
  exact happly.contDiffAt.comp 0 M.param_smooth


-- @@ L198-200 verbatim
def centerNormalLinearization (M : StandardMorseEventAt C center) :
    E₂ →L[ℝ] E₁ :=
  fderiv ℝ M.centerNormalMap 0


-- @@ L202-205 verbatim
theorem hasFDerivAt_centerNormalMap_zero
    (M : StandardMorseEventAt C center) :
    HasFDerivAt M.centerNormalMap M.centerNormalLinearization 0 :=
  (M.centerNormalMap_contDiffAt_zero.differentiableAt (by simp)).hasFDerivAt


-- @@ L207-211 verbatim
/-- Polar Hadamard extension of the vanishing normal row. -/
def centerNormalRow (M : StandardMorseEventAt C center)
    (r theta : ℝ) : E₁ :=
  polarFirstQuotient M.centerNormalMap M.centerNormalLinearization
    (fun theta => definiteCircleParam 1 theta) (r, theta)


-- @@ L213-217 verbatim
@[simp] theorem centerNormalRow_zero
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerNormalRow 0 theta =
      M.centerNormalLinearization (definiteCircleParam 1 theta) := by
  simp [centerNormalRow, polarFirstQuotient]


-- @@ L219-232 verbatim
theorem continuousAt_centerNormalRow_zero
    (M : StandardMorseEventAt C center) (theta₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => M.centerNormalRow q.1 q.2)
      (0, theta₀) := by
  have hdirection : ContinuousAt
      (fun theta : ℝ => definiteCircleParam 1 theta) theta₀ := by
    apply Continuous.continuousAt
    unfold definiteCircleParam pairToMorseParam
    fun_prop
  simpa [centerNormalRow] using
    (continuousAt_polarFirstQuotient M.centerNormalMap
      M.centerNormalLinearization
      (fun theta : ℝ => definiteCircleParam 1 theta) theta₀
      M.hasFDerivAt_centerNormalMap_zero M.centerNormalMap_zero hdirection)


-- @@ L234-237 verbatim
/-- Pairing of the fixed cokernel vector with the full ambient-time
derivative. -/
def centerTimeNormalCoefficient (M : StandardMorseEventAt C center) : ℝ :=
  ⟪M.centerCokernelVector, fderiv ℝ C.G center timeVec⟫_ℝ


-- @@ L239-272 verbatim
theorem centerTimeNormalCoefficient_ne_zero
    (M : StandardMorseEventAt C center) :
    M.centerTimeNormalCoefficient ≠ 0 := by
  let c := M.centerCokernelVector
  let L := fderiv ℝ C.G center
  let A := spatialDeriv C.G center
  intro htime
  have hsurj : Surjective L := C.regular center M.center_mem_timeCritical.1
  obtain ⟨z, hz⟩ := hsurj c
  have hadjoint : ContinuousLinearMap.adjoint A c = 0 :=
    adjoint_spatialDeriv_criticalOutputCokernelVector
      C center M.center_mem_timeCritical
  have hdecomp : L z = A (spacePart z) + tcoord z • L timeVec := by
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
    change tcoord z * M.centerTimeNormalCoefficient = 0
    rw [htime, mul_zero]
  have hself : ⟪c, c⟫_ℝ = 0 := by
    calc
      ⟪c, c⟫_ℝ = ⟪c, L z⟫_ℝ := by rw [hz]
      _ = ⟪c, A (spacePart z) + tcoord z • L timeVec⟫_ℝ := by
        rw [hdecomp]
      _ = 0 := by rw [inner_add_right, hspace, htime', add_zero]
  exact M.centerCokernelVector_ne_zero (inner_self_eq_zero.mp hself)


-- @@ L274-277 verbatim
def centerTimeNormalCoefficientAt
    (M : StandardMorseEventAt C center) (u : E₂) : ℝ :=
  ⟪M.centerCokernelVector,
    fderiv ℝ C.G (M.param u) timeVec⟫_ℝ


-- @@ L279-283 verbatim
@[simp] theorem centerTimeNormalCoefficientAt_zero
    (M : StandardMorseEventAt C center) :
    M.centerTimeNormalCoefficientAt 0 = M.centerTimeNormalCoefficient := by
  simp [centerTimeNormalCoefficientAt, centerTimeNormalCoefficient,
    M.param_zero]


-- @@ L285-285 verbatim
/-! ## Center Hessian pairing -/


-- @@ L287-327 verbatim
theorem inner_centerNormalMap_centerSpatialTangent
    (T : M.CenterImmersion) (u : E₂) (hu : ‖u‖ < T.radius)
    (w : E₂) :
    ⟪M.centerNormalMap u, M.centerSpatialTangent u w⟫_ℝ =
      -(fderiv ℝ (fun z : E₂ =>
          tcoord center + morseQuadratic M.index (z 0, z 1)) u w *
        M.centerTimeNormalCoefficientAt u) := by
  let z := fderiv ℝ M.param u w
  let A := spatialDeriv C.G (M.param u)
  let L := fderiv ℝ C.G (M.param u)
  have hzero : L z = 0 := fderiv_param_mem_ker T u hu w
  have hdecomp : A (spacePart z) + tcoord z • L timeVec = 0 := by
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
  have htime := fderiv_param_time_apply T u hu w
  have hmodel := congrArg (fun D : E₂ →L[ℝ] ℝ => D w)
    (fderiv_param_time T u hu)
  calc
    ⟪M.centerNormalMap u, M.centerSpatialTangent u w⟫_ℝ =
        ⟪M.centerCokernelVector, A (spacePart z)⟫_ℝ := by
          exact ContinuousLinearMap.adjoint_inner_left A (spacePart z)
            M.centerCokernelVector
    _ = ⟪M.centerCokernelVector, -(tcoord z • L timeVec)⟫_ℝ := by
          rw [hspatial]
    _ = -(tcoord z * ⟪M.centerCokernelVector, L timeVec⟫_ℝ) := by
          rw [inner_neg_right, real_inner_smul_right]
    _ = -(fderiv ℝ (fun z : E₂ =>
          tcoord center + morseQuadratic M.index (z 0, z 1)) u w *
        M.centerTimeNormalCoefficientAt u) := by
          congr 1
          rw [← htime, hmodel]
          rfl


-- @@ L329-331 verbatim
def centerNormalTangentPairing
    (M : StandardMorseEventAt C center) (w u : E₂) : ℝ :=
  ⟪M.centerNormalMap u, M.centerSpatialTangent u w⟫_ℝ


-- @@ L333-406 verbatim
theorem inner_centerNormalLinearization_centerSpatialTangent_zero
    (T : M.CenterImmersion) (v w : E₂) :
    ⟪M.centerNormalLinearization v, M.centerSpatialTangent 0 w⟫_ℝ =
      -(morseHessianPairing M.index v w *
        M.centerTimeNormalCoefficient) := by
  let Φ := M.param
  let e := M.index
  let c₀ := tcoord center
  let qdiff : E₂ → ℝ := fun u =>
    fderiv ℝ (fun z : E₂ => c₀ + morseQuadratic e (z 0, z 1)) u w
  let k : E₂ → ℝ := M.centerTimeNormalCoefficientAt
  let pair : E₂ → ℝ := M.centerNormalTangentPairing w
  have hDΦ : ContDiffAt ℝ ∞ (fderiv ℝ Φ) 0 :=
    M.param_smooth.fderiv_right (by simp)
  have htangentCD : ContDiffAt ℝ ∞
      (M.centerSpatialTangent · w) 0 := by
    have heval : ContDiffAt ℝ ∞ (fun u => fderiv ℝ Φ u w) 0 :=
      hDΦ.clm_apply contDiffAt_const
    have hproj :=
      (ExactFiniteMorseJetInstallation.criticalSpacePartCLM
        (n := a + 2)).contDiff.contDiffAt.comp 0 heval
    simpa [centerSpatialTangent, Φ, Function.comp_def] using hproj
  have htangent : DifferentiableAt ℝ (M.centerSpatialTangent · w) 0 :=
    htangentCD.differentiableAt (by simp)
  have hnormal : DifferentiableAt ℝ M.centerNormalMap 0 :=
    M.centerNormalMap_contDiffAt_zero.differentiableAt (by simp)
  have hleft : fderiv ℝ pair 0 v =
      ⟪M.centerNormalLinearization v, M.centerSpatialTangent 0 w⟫_ℝ := by
    change fderiv ℝ (fun u =>
      ⟪M.centerNormalMap u, M.centerSpatialTangent u w⟫_ℝ) 0 v = _
    rw [fderiv_inner_apply ℝ hnormal htangent v]
    simp [centerNormalLinearization]
  have hqeq : qdiff = morseHessianPairingLeft e w := by
    funext u
    exact fderiv_const_add_morseQuadratic_apply e c₀ u w
  have hq : DifferentiableAt ℝ qdiff 0 := by
    rw [hqeq]
    exact (morseHessianPairingLeft e w).differentiableAt
  have hqzero : qdiff 0 = 0 := by
    rw [hqeq]
    cases e <;> simp [morseHessianPairing]
  have hqderiv : fderiv ℝ qdiff 0 v = morseHessianPairing e v w :=
    fderiv_morseDifferential_apply e c₀ v w
  have hkCD : ContDiffAt ℝ ∞ k 0 := by
    have hDG : ContDiff ℝ ∞ (fderiv ℝ C.G) := contDiff_fderivCLM C.smooth
    have hcomp : ContDiffAt ℝ ∞ (fun u => fderiv ℝ C.G (Φ u)) 0 :=
      hDG.contDiffAt.comp 0 M.param_smooth
    have heval : ContDiffAt ℝ ∞
        (fun u => fderiv ℝ C.G (Φ u) timeVec) 0 :=
      hcomp.clm_apply contDiffAt_const
    have hinner := (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _u : E₂ => M.centerCokernelVector) 0).inner ℝ heval
    exact hinner
  have hk : DifferentiableAt ℝ k 0 := hkCD.differentiableAt (by simp)
  have hkzero : k 0 = M.centerTimeNormalCoefficient :=
    M.centerTimeNormalCoefficientAt_zero
  have hevent : pair =ᶠ[nhds 0] fun u => -(qdiff u * k u) := by
    have hball : ball (0 : E₂) T.radius ∈ nhds 0 :=
      ball_mem_nhds 0 T.radius_pos
    filter_upwards [hball] with u hu
    exact inner_centerNormalMap_centerSpatialTangent T u
      (by simpa [mem_ball, dist_zero_right] using hu) w
  have hright : fderiv ℝ (fun u => -(qdiff u * k u)) 0 v =
      -(morseHessianPairing e v w * M.centerTimeNormalCoefficient) := by
    have hderiv := (hq.hasFDerivAt.mul hk.hasFDerivAt).neg.fderiv
    change (fderiv ℝ (-(qdiff * k)) 0) v = _
    rw [hderiv]
    simp only [hqzero, zero_smul, zero_add, hkzero]
    change -(M.centerTimeNormalCoefficient * fderiv ℝ qdiff 0 v) = _
    rw [hqderiv]
    ring
  have hfdEq := congrArg (fun D : E₂ →L[ℝ] ℝ => D v) hevent.fderiv_eq
  rw [hleft, hright] at hfdEq
  exact hfdEq


-- @@ L408-408 verbatim
/-! ## The complete center frame for a production event -/


-- @@ L410-420 verbatim
/-- A basis of the persistent spatial range at the critical center. -/
def centerTransverseRangeBasis
    (M : StandardMorseEventAt C center) :
    OrthonormalBasis (Fin (a + 1)) ℝ
      (LinearMap.range (spatialDeriv C.G center).toLinearMap) := by
  let K := LinearMap.range (spatialDeriv C.G center).toLinearMap
  have hdim : Module.finrank ℝ K = a + 1 := by
    simpa [K] using
      (finrank_range_spatialDeriv_of_mem_timeCritical C
        M.center_mem_timeCritical)
  exact (stdOrthonormalBasis ℝ K).reindex (finCongr hdim)


-- @@ L422-428 verbatim
/-- The adjoint of the center spatial derivative, restricted to its range. -/
def centerAdjointOnRange
    (_M : StandardMorseEventAt C center) :
    (LinearMap.range (spatialDeriv C.G center).toLinearMap) →ₗ[ℝ] E₁ where
  toFun y := ContinuousLinearMap.adjoint (spatialDeriv C.G center) y.1
  map_add' y z := by simp
  map_smul' r y := by simp


-- @@ L430-432 verbatim
def centerTransverseNormal
    (M : StandardMorseEventAt C center) (i : Fin (a + 1)) : E₁ :=
  M.centerAdjointOnRange (M.centerTransverseRangeBasis i)


-- @@ L434-454 verbatim
theorem centerAdjointOnRange_injective
    (M : StandardMorseEventAt C center) :
    Injective M.centerAdjointOnRange := by
  let A := spatialDeriv C.G center
  intro y z hyz
  have hadj : ContinuousLinearMap.adjoint A (y.1 - z.1) = 0 := by
    change M.centerAdjointOnRange (y - z) = 0
    rw [map_sub, hyz, sub_self]
  have hyrange : y.1 - z.1 ∈ LinearMap.range A.toLinearMap :=
    sub_mem y.2 z.2
  obtain ⟨x, hx⟩ := hyrange
  have hself : ⟪y.1 - z.1, y.1 - z.1⟫_ℝ = 0 := by
    calc
      ⟪y.1 - z.1, y.1 - z.1⟫_ℝ = ⟪y.1 - z.1, A x⟫_ℝ := by
        congr 1
        exact hx.symm
      _ = ⟪ContinuousLinearMap.adjoint A (y.1 - z.1), x⟫_ℝ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ = 0 := by rw [hadj, inner_zero_left]
  apply Subtype.ext
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)


-- @@ L456-467 verbatim
theorem linearIndependent_centerTransverseNormal
    (M : StandardMorseEventAt C center) :
    LinearIndependent ℝ M.centerTransverseNormal := by
  let b := M.centerTransverseRangeBasis
  have hb : LinearIndependent ℝ (fun i => b i) :=
    b.toBasis.linearIndependent
  have hker : M.centerAdjointOnRange.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr M.centerAdjointOnRange_injective
  have hmapped := hb.map' M.centerAdjointOnRange hker
  change LinearIndependent ℝ (fun i =>
    M.centerAdjointOnRange (M.centerTransverseRangeBasis i))
  simpa [b, Function.comp_def] using hmapped


-- @@ L469-492 verbatim
theorem spatialDeriv_centerSpatialTangent_zero
    (T : M.CenterImmersion) (w : E₂) :
    spatialDeriv C.G center (M.centerSpatialTangent 0 w) = 0 := by
  have hzero : ‖(0 : E₂)‖ < T.radius := by
    simpa using T.radius_pos
  have hfull := fderiv_param_mem_ker T 0 hzero w
  rw [M.param_zero] at hfull
  let z := fderiv ℝ M.param 0 w
  let A := spatialDeriv C.G center
  let L := fderiv ℝ C.G center
  have hdecomp : A (spacePart z) + tcoord z • L timeVec = 0 := by
    calc
      A (spacePart z) + tcoord z • L timeVec =
          L (spaceInclL (spacePart z) + tcoord z • timeVec) := by
            rw [map_add, map_smul]
            rfl
      _ = L (cobSpaceTime (spacePart z) (tcoord z)) := by
            rw [spaceTime_eq]
      _ = L z := by rw [spaceTime_spacePart]
      _ = 0 := by simpa [L, z] using hfull
  have htime : tcoord z = 0 := by
    simpa [z] using tcoord_fderiv_param_zero T w
  rw [htime, zero_smul, add_zero] at hdecomp
  simpa [A, z, centerSpatialTangent] using hdecomp


-- @@ L494-502 verbatim
theorem inner_centerTransverseNormal_spatialTangent_zero
    (T : M.CenterImmersion) (i : Fin (a + 1)) (w : E₂) :
    ⟪M.centerTransverseNormal i, M.centerSpatialTangent 0 w⟫_ℝ = 0 := by
  let A := spatialDeriv C.G center
  change ⟪ContinuousLinearMap.adjoint A
      (M.centerTransverseRangeBasis i : F),
    M.centerSpatialTangent 0 w⟫_ℝ = 0
  rw [ContinuousLinearMap.adjoint_inner_left,
    spatialDeriv_centerSpatialTangent_zero T w, inner_zero_right]


-- @@ L504-506 verbatim
def centerUnitTangent
    (M : StandardMorseEventAt C center) (theta : ℝ) : E₁ :=
  M.centerSpatialTangent 0 (definiteCircleTangentParam 1 theta)


-- @@ L508-510 verbatim
def centerUnitTangentRev
    (M : StandardMorseEventAt C center) (theta : ℝ) : E₁ :=
  -M.centerUnitTangent theta


-- @@ L512-514 verbatim
def centerRadialTangent
    (M : StandardMorseEventAt C center) (theta : ℝ) : E₁ :=
  M.centerSpatialTangent 0 (definiteCircleParam 1 theta)


-- @@ L516-520 verbatim
theorem centerUnitTangent_ne_zero
    (T : M.CenterImmersion) (theta : ℝ) :
    M.centerUnitTangent theta ≠ 0 := by
  exact centerSpatialTangent_zero_ne_zero T
    (definiteCircleTangentParam_unit_ne_zero theta)


-- @@ L522-526 verbatim
theorem inner_centerTransverseNormal_unitTangent_zero
    (T : M.CenterImmersion) (i : Fin (a + 1)) (theta : ℝ) :
    ⟪M.centerTransverseNormal i, M.centerUnitTangent theta⟫_ℝ = 0 :=
  inner_centerTransverseNormal_spatialTangent_zero T i
    (definiteCircleTangentParam 1 theta)


-- @@ L528-532 verbatim
theorem inner_centerTransverseNormal_radialTangent_zero
    (T : M.CenterImmersion) (i : Fin (a + 1)) (theta : ℝ) :
    ⟪M.centerTransverseNormal i, M.centerRadialTangent theta⟫_ℝ = 0 :=
  inner_centerTransverseNormal_spatialTangent_zero T i
    (definiteCircleParam 1 theta)


-- @@ L534-543 verbatim
theorem inner_centerNormalRow_radial_minimum
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (theta : ℝ) :
    ⟪M.centerNormalRow 0 theta, M.centerRadialTangent theta⟫_ℝ =
      -(2 * M.centerTimeNormalCoefficient) := by
  rw [M.centerNormalRow_zero]
  unfold centerRadialTangent
  rw [inner_centerNormalLinearization_centerSpatialTangent_zero T,
    hindex]
  simp


-- @@ L545-554 verbatim
theorem inner_centerNormalRow_radial_maximum
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (theta : ℝ) :
    ⟪M.centerNormalRow 0 theta, M.centerRadialTangent theta⟫_ℝ =
      2 * M.centerTimeNormalCoefficient := by
  rw [M.centerNormalRow_zero]
  unfold centerRadialTangent
  rw [inner_centerNormalLinearization_centerSpatialTangent_zero T,
    hindex]
  simp


-- @@ L556-564 verbatim
theorem inner_centerNormalRow_unitTangent_minimum
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (theta : ℝ) :
    ⟪M.centerNormalRow 0 theta, M.centerUnitTangent theta⟫_ℝ = 0 := by
  rw [M.centerNormalRow_zero]
  unfold centerUnitTangent
  rw [inner_centerNormalLinearization_centerSpatialTangent_zero T,
    hindex]
  simp


-- @@ L566-574 verbatim
theorem inner_centerNormalRow_unitTangent_maximum
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (theta : ℝ) :
    ⟪M.centerNormalRow 0 theta, M.centerUnitTangent theta⟫_ℝ = 0 := by
  rw [M.centerNormalRow_zero]
  unfold centerUnitTangent
  rw [inner_centerNormalLinearization_centerSpatialTangent_zero T,
    hindex]
  simp


-- @@ L576-576 verbatim
/-! ## Nonsingular deformation from the center normal to the radial row -/


-- @@ L578-581 verbatim
def centerMinimumRadialTest
    (M : StandardMorseEventAt C center) (theta : ℝ) : E₁ :=
  tangentOrthogonalRadial
    (M.centerUnitTangent theta) (M.centerRadialTangent theta)


-- @@ L583-586 verbatim
def centerMaximumRadialTest
    (M : StandardMorseEventAt C center) (theta : ℝ) : E₁ :=
  tangentOrthogonalRadial
    (M.centerUnitTangentRev theta) (M.centerRadialTangent theta)


-- @@ L588-592 verbatim
theorem inner_centerUnitTangent_minimumRadialTest
    (T : M.CenterImmersion) (theta : ℝ) :
    ⟪M.centerUnitTangent theta, M.centerMinimumRadialTest theta⟫_ℝ = 0 :=
  inner_tangent_tangentOrthogonalRadial _ _
    (centerUnitTangent_ne_zero T theta)


-- @@ L594-598 verbatim
theorem inner_centerUnitTangentRev_maximumRadialTest
    (T : M.CenterImmersion) (theta : ℝ) :
    ⟪M.centerUnitTangentRev theta, M.centerMaximumRadialTest theta⟫_ℝ = 0 :=
  inner_tangent_tangentOrthogonalRadial _ _
    (neg_ne_zero.mpr (centerUnitTangent_ne_zero T theta))


-- @@ L600-606 verbatim
theorem inner_centerTransverseNormal_minimumRadialTest
    (T : M.CenterImmersion) (i : Fin (a + 1)) (theta : ℝ) :
    ⟪M.centerTransverseNormal i, M.centerMinimumRadialTest theta⟫_ℝ = 0 := by
  rw [centerMinimumRadialTest,
    inner_left_tangentOrthogonalRadial_eq _ _ _
      (inner_centerTransverseNormal_unitTangent_zero T i theta),
    inner_centerTransverseNormal_radialTangent_zero T i theta]


-- @@ L608-617 verbatim
theorem inner_centerTransverseNormal_maximumRadialTest
    (T : M.CenterImmersion) (i : Fin (a + 1)) (theta : ℝ) :
    ⟪M.centerTransverseNormal i, M.centerMaximumRadialTest theta⟫_ℝ = 0 := by
  have htan : ⟪M.centerTransverseNormal i,
      M.centerUnitTangentRev theta⟫_ℝ = 0 := by
    rw [centerUnitTangentRev, inner_neg_right,
      inner_centerTransverseNormal_unitTangent_zero T i theta, neg_zero]
  rw [centerMaximumRadialTest,
    inner_left_tangentOrthogonalRadial_eq _ _ _ htan,
    inner_centerTransverseNormal_radialTangent_zero T i theta]


-- @@ L619-621 verbatim
def centerMinimumPairingScalar
    (M : StandardMorseEventAt C center) : ℝ :=
  -(2 * M.centerTimeNormalCoefficient)


-- @@ L623-625 verbatim
def centerMaximumPairingScalar
    (M : StandardMorseEventAt C center) : ℝ :=
  2 * M.centerTimeNormalCoefficient


-- @@ L627-631 verbatim
theorem centerMinimumPairingScalar_ne_zero
    (M : StandardMorseEventAt C center) :
    M.centerMinimumPairingScalar ≠ 0 :=
  neg_ne_zero.mpr (mul_ne_zero (by norm_num)
    M.centerTimeNormalCoefficient_ne_zero)


-- @@ L633-636 verbatim
theorem centerMaximumPairingScalar_ne_zero
    (M : StandardMorseEventAt C center) :
    M.centerMaximumPairingScalar ≠ 0 :=
  mul_ne_zero (by norm_num) M.centerTimeNormalCoefficient_ne_zero


-- @@ L638-646 verbatim
theorem inner_centerNormalRow_minimumRadialTest
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (theta : ℝ) :
    ⟪M.centerNormalRow 0 theta, M.centerMinimumRadialTest theta⟫_ℝ =
      M.centerMinimumPairingScalar := by
  rw [centerMinimumRadialTest,
    inner_left_tangentOrthogonalRadial_eq _ _ _
      (inner_centerNormalRow_unitTangent_minimum T hindex theta)]
  exact inner_centerNormalRow_radial_minimum T hindex theta


-- @@ L648-659 verbatim
theorem inner_centerNormalRow_maximumRadialTest
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (theta : ℝ) :
    ⟪M.centerNormalRow 0 theta, M.centerMaximumRadialTest theta⟫_ℝ =
      M.centerMaximumPairingScalar := by
  have htan : ⟪M.centerNormalRow 0 theta,
      M.centerUnitTangentRev theta⟫_ℝ = 0 := by
    rw [centerUnitTangentRev, inner_neg_right,
      inner_centerNormalRow_unitTangent_maximum T hindex theta, neg_zero]
  rw [centerMaximumRadialTest,
    inner_left_tangentOrthogonalRadial_eq _ _ _ htan]
  exact inner_centerNormalRow_radial_maximum T hindex theta


-- @@ L661-667 verbatim
theorem centerMinimumRadialTest_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (theta : ℝ) : M.centerMinimumRadialTest theta ≠ 0 := by
  intro hzero
  have hpair := inner_centerNormalRow_minimumRadialTest T hindex theta
  rw [hzero, inner_zero_right] at hpair
  exact M.centerMinimumPairingScalar_ne_zero hpair.symm


-- @@ L669-675 verbatim
theorem centerMaximumRadialTest_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (theta : ℝ) : M.centerMaximumRadialTest theta ≠ 0 := by
  intro hzero
  have hpair := inner_centerNormalRow_maximumRadialTest T hindex theta
  rw [hzero, inner_zero_right] at hpair
  exact M.centerMaximumPairingScalar_ne_zero hpair.symm


-- @@ L677-687 verbatim
theorem inner_centerRadialTangent_minimumRadialTest_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (theta : ℝ) :
    ⟪M.centerRadialTangent theta,
      M.centerMinimumRadialTest theta⟫_ℝ ≠ 0 := by
  rw [centerMinimumRadialTest,
    inner_radial_tangentOrthogonalRadial_eq_self _ _
      (centerUnitTangent_ne_zero T theta)]
  intro hzero
  exact centerMinimumRadialTest_ne_zero T hindex theta
    (inner_self_eq_zero.mp hzero)


-- @@ L689-699 verbatim
theorem inner_centerRadialTangent_maximumRadialTest_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (theta : ℝ) :
    ⟪M.centerRadialTangent theta,
      M.centerMaximumRadialTest theta⟫_ℝ ≠ 0 := by
  rw [centerMaximumRadialTest, centerUnitTangentRev,
    inner_radial_tangentOrthogonalRadial_eq_self _ _
      (neg_ne_zero.mpr (centerUnitTangent_ne_zero T theta))]
  intro hzero
  exact centerMaximumRadialTest_ne_zero T hindex theta
    (inner_self_eq_zero.mp hzero)


-- @@ L701-706 verbatim
def centerMinimumNormalRadialLast
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) : E₁ :=
  (1 - (s : ℝ)) •
      (nonzeroOrientationSign M.centerMinimumPairingScalar •
        M.centerNormalRow 0 theta) +
    (s : ℝ) • M.centerRadialTangent theta


-- @@ L708-713 verbatim
def centerMaximumNormalRadialLast
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) : E₁ :=
  (1 - (s : ℝ)) •
      (nonzeroOrientationSign M.centerMaximumPairingScalar •
        M.centerNormalRow 0 theta) +
    (s : ℝ) • M.centerRadialTangent theta


-- @@ L715-720 verbatim
def centerMinimumOrientedNormalRadialRows
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal
    (StandardBirth.orientationSign a • M.centerUnitTangent theta)
    (M.centerMinimumNormalRadialLast s theta)


-- @@ L722-727 verbatim
def centerMaximumOrientedNormalRadialRows
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal
    ((-StandardBirth.orientationSign a) • M.centerUnitTangentRev theta)
    (M.centerMaximumNormalRadialLast s theta)


-- @@ L729-757 verbatim
theorem inner_centerMinimumNormalRadialLast_radialTest_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    0 < ⟪M.centerMinimumNormalRadialLast s theta,
      M.centerMinimumRadialTest theta⟫_ℝ := by
  have hpair := inner_centerNormalRow_minimumRadialTest T hindex theta
  have hnormal : 0 <
      nonzeroOrientationSign M.centerMinimumPairingScalar *
        M.centerMinimumPairingScalar :=
    nonzeroOrientationSign_mul_pos M.centerMinimumPairingScalar_ne_zero
  have hradialEq := inner_radial_tangentOrthogonalRadial_eq_self
    (M.centerUnitTangent theta) (M.centerRadialTangent theta)
    (centerUnitTangent_ne_zero T theta)
  have hradial : 0 < ⟪M.centerRadialTangent theta,
      M.centerMinimumRadialTest theta⟫_ℝ := by
    rw [centerMinimumRadialTest, hradialEq]
    exact real_inner_self_pos.mpr
      (centerMinimumRadialTest_ne_zero T hindex theta)
  rw [centerMinimumNormalRadialLast, inner_add_left,
    real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, hpair]
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simpa [hsone] using hradial
  have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hsone
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hslt) hnormal)
    (mul_nonneg hs0 hradial.le)


-- @@ L759-787 verbatim
theorem inner_centerMaximumNormalRadialLast_radialTest_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    0 < ⟪M.centerMaximumNormalRadialLast s theta,
      M.centerMaximumRadialTest theta⟫_ℝ := by
  have hpair := inner_centerNormalRow_maximumRadialTest T hindex theta
  have hnormal : 0 <
      nonzeroOrientationSign M.centerMaximumPairingScalar *
        M.centerMaximumPairingScalar :=
    nonzeroOrientationSign_mul_pos M.centerMaximumPairingScalar_ne_zero
  have hradialEq := inner_radial_tangentOrthogonalRadial_eq_self
    (M.centerUnitTangentRev theta) (M.centerRadialTangent theta)
    (neg_ne_zero.mpr (centerUnitTangent_ne_zero T theta))
  have hradial : 0 < ⟪M.centerRadialTangent theta,
      M.centerMaximumRadialTest theta⟫_ℝ := by
    rw [centerMaximumRadialTest, hradialEq]
    exact real_inner_self_pos.mpr
      (centerMaximumRadialTest_ne_zero T hindex theta)
  rw [centerMaximumNormalRadialLast, inner_add_left,
    real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, hpair]
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simpa [hsone] using hradial
  have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hsone
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr hslt) hnormal)
    (mul_nonneg hs0 hradial.le)


-- @@ L789-806 verbatim
theorem linearIndependent_centerMinimumOrientedNormalRadialRows
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    LinearIndependent ℝ (M.centerMinimumOrientedNormalRadialRows s theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact M.linearIndependent_centerTransverseNormal
  · exact smul_ne_zero (StandardBirth.orientationSign_ne_zero a)
      (centerUnitTangent_ne_zero T theta)
  · intro i
    rw [real_inner_smul_right,
      inner_centerTransverseNormal_unitTangent_zero T i theta, mul_zero]
  · intro i
    exact inner_centerTransverseNormal_minimumRadialTest T i theta
  · rw [real_inner_smul_left,
      inner_centerUnitTangent_minimumRadialTest T theta, mul_zero]
  · exact ne_of_gt
      (inner_centerMinimumNormalRadialLast_radialTest_pos
        T hindex s theta)


-- @@ L808-827 verbatim
theorem linearIndependent_centerMaximumOrientedNormalRadialRows
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    LinearIndependent ℝ (M.centerMaximumOrientedNormalRadialRows s theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact M.linearIndependent_centerTransverseNormal
  · exact smul_ne_zero
      (neg_ne_zero.mpr (StandardBirth.orientationSign_ne_zero a))
      (neg_ne_zero.mpr (centerUnitTangent_ne_zero T theta))
  · intro i
    rw [real_inner_smul_right, centerUnitTangentRev, inner_neg_right,
      inner_centerTransverseNormal_unitTangent_zero T i theta,
      neg_zero, mul_zero]
  · intro i
    exact inner_centerTransverseNormal_maximumRadialTest T i theta
  · rw [real_inner_smul_left,
      inner_centerUnitTangentRev_maximumRadialTest T theta, mul_zero]
  · exact ne_of_gt
      (inner_centerMaximumNormalRadialLast_radialTest_pos
        T hindex s theta)


-- @@ L829-832 verbatim
def centerMinimumOrientedNormalRadialMatrix
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerMinimumOrientedNormalRadialRows s theta)


-- @@ L834-837 verbatim
def centerMaximumOrientedNormalRadialMatrix
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerMaximumOrientedNormalRadialRows s theta)


-- @@ L839-851 verbatim
theorem det_centerMinimumOrientedNormalRadialMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    (M.centerMinimumOrientedNormalRadialMatrix s theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (M.centerMinimumOrientedNormalRadialMatrix s theta).row :=
    (linearIndependent_rowsMatrix_iff
      (M.centerMinimumOrientedNormalRadialRows s theta)).mpr
      (linearIndependent_centerMinimumOrientedNormalRadialRows
        T hindex s theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L853-865 verbatim
theorem det_centerMaximumOrientedNormalRadialMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    (M.centerMaximumOrientedNormalRadialMatrix s theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (M.centerMaximumOrientedNormalRadialMatrix s theta).row :=
    (linearIndependent_rowsMatrix_iff
      (M.centerMaximumOrientedNormalRadialRows s theta)).mpr
      (linearIndependent_centerMaximumOrientedNormalRadialRows
        T hindex s theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L867-867 verbatim
/-! ## Exact factorization of the radial endpoint -/


-- @@ L869-881 verbatim
theorem centerUnitTangent_rotation
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerUnitTangent theta =
      Real.cos theta • M.centerUnitTangent 0 -
        Real.sin theta • M.centerRadialTangent 0 := by
  let L : E₂ →L[ℝ] E₁ :=
    (ExactFiniteMorseJetInstallation.criticalSpacePartCLM
      (n := a + 2)).comp (fderiv ℝ M.param 0)
  change L (definiteCircleTangentParam 1 theta) =
    Real.cos theta • L (definiteCircleTangentParam 1 0) -
      Real.sin theta • L (definiteCircleParam 1 0)
  rw [definiteCircleTangentParam_unit_rotation, map_sub,
    map_smul, map_smul]


-- @@ L883-894 verbatim
theorem centerRadialTangent_rotation
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerRadialTangent theta =
      Real.sin theta • M.centerUnitTangent 0 +
        Real.cos theta • M.centerRadialTangent 0 := by
  let L : E₂ →L[ℝ] E₁ :=
    (ExactFiniteMorseJetInstallation.criticalSpacePartCLM
      (n := a + 2)).comp (fderiv ℝ M.param 0)
  change L (definiteCircleParam 1 theta) =
    Real.sin theta • L (definiteCircleTangentParam 1 0) +
      Real.cos theta • L (definiteCircleParam 1 0)
  rw [definiteCircleParam_unit_rotation, map_add, map_smul, map_smul]


-- @@ L896-910 verbatim
theorem centerOrientedTangent_rotation
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    StandardBirth.orientationSign a • M.centerUnitTangent theta =
      Real.cos (StandardBirth.orientationSign a * theta) •
          (StandardBirth.orientationSign a • M.centerUnitTangent 0) -
        Real.sin (StandardBirth.orientationSign a * theta) •
          M.centerRadialTangent 0 := by
  rcases StandardBirth.orientationSign_eq_one_or_neg_one a with h | h
  · rw [h]
    simp only [one_mul, one_smul]
    exact M.centerUnitTangent_rotation theta
  · rw [h]
    simp only [neg_mul, neg_smul, Real.cos_neg, Real.sin_neg, one_mul]
    rw [M.centerUnitTangent_rotation theta]
    module


-- @@ L912-926 verbatim
theorem centerOrientedRadial_rotation
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerRadialTangent theta =
      Real.sin (StandardBirth.orientationSign a * theta) •
          (StandardBirth.orientationSign a • M.centerUnitTangent 0) +
        Real.cos (StandardBirth.orientationSign a * theta) •
          M.centerRadialTangent 0 := by
  rcases StandardBirth.orientationSign_eq_one_or_neg_one a with h | h
  · rw [h]
    simp only [one_mul, one_smul]
    exact M.centerRadialTangent_rotation theta
  · rw [h]
    simp only [neg_mul, neg_smul, Real.cos_neg, Real.sin_neg, one_mul]
    rw [M.centerRadialTangent_rotation theta]
    module


-- @@ L928-932 verbatim
@[simp] theorem centerMinimumOrientedNormalRadialRows_zero
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    M.centerMinimumOrientedNormalRadialRows s theta 0 =
      StandardBirth.orientationSign a • M.centerUnitTangent theta := by
  simp [centerMinimumOrientedNormalRadialRows, centerRowsWith]


-- @@ L934-938 verbatim
@[simp] theorem centerMinimumOrientedNormalRadialRows_last
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    M.centerMinimumOrientedNormalRadialRows s theta (Fin.last (a + 2)) =
      M.centerMinimumNormalRadialLast s theta := by
  simp [centerMinimumOrientedNormalRadialRows, centerRowsWith]


-- @@ L940-945 verbatim
@[simp] theorem centerMinimumOrientedNormalRadialRows_middle
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ)
    (i : Fin (a + 1)) :
    M.centerMinimumOrientedNormalRadialRows s theta i.castSucc.succ =
      M.centerTransverseNormal i := by
  simp [centerMinimumOrientedNormalRadialRows, centerRowsWith]


-- @@ L947-988 verbatim
theorem centerMinimumOrientedRadialMatrix_rotation
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerMinimumOrientedNormalRadialMatrix 1 theta =
      twistMat a (StandardBirth.orientationSign a * theta) *
        M.centerMinimumOrientedNormalRadialMatrix 1 0 := by
  ext i j
  rw [StandardBirth.twistMat_mul_apply_birth]
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    simp only [centerMinimumOrientedNormalRadialMatrix, rowsMatrix,
      Matrix.of_apply, M.centerMinimumOrientedNormalRadialRows_zero,
      M.centerMinimumOrientedNormalRadialRows_last]
    simp only [centerMinimumNormalRadialLast, Set.Icc.coe_one]
    simp
    have h := congrArg (fun v : E₁ => v j)
      (M.centerOrientedTangent_rotation theta)
    simpa [sub_eq_add_neg] using h
  · rw [if_neg hi0]
    by_cases hil : i = Fin.last (a + 2)
    · subst i
      rw [if_pos rfl]
      simp only [centerMinimumOrientedNormalRadialMatrix, rowsMatrix,
        Matrix.of_apply, M.centerMinimumOrientedNormalRadialRows_zero,
        M.centerMinimumOrientedNormalRadialRows_last]
      simp [centerMinimumNormalRadialLast]
      have h := congrArg (fun v : E₁ => v j)
        (M.centerOrientedRadial_rotation theta)
      simpa using h
    · rw [if_neg hil]
      simp only [centerMinimumOrientedNormalRadialMatrix, rowsMatrix,
        Matrix.of_apply]
      obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
      induction k using Fin.lastCases with
      | last =>
          exfalso
          apply hil
          apply Fin.ext
          simp
      | cast k =>
          rw [M.centerMinimumOrientedNormalRadialRows_middle,
            M.centerMinimumOrientedNormalRadialRows_middle]


-- @@ L990-1005 verbatim
theorem centerMaximumOrientedRadialMatrix_rotation
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerMaximumOrientedNormalRadialMatrix 1 theta =
      twistMat a (StandardBirth.orientationSign a * theta) *
        M.centerMaximumOrientedNormalRadialMatrix 1 0 := by
  have hrows (x : ℝ) : M.centerMaximumOrientedNormalRadialRows 1 x =
      M.centerMinimumOrientedNormalRadialRows 1 x := by
    funext i
    simp [centerMaximumOrientedNormalRadialRows,
      centerMinimumOrientedNormalRadialRows, centerUnitTangentRev,
      centerMaximumNormalRadialLast, centerMinimumNormalRadialLast]
  rw [centerMaximumOrientedNormalRadialMatrix,
    centerMaximumOrientedNormalRadialMatrix, hrows theta, hrows 0,
    ← centerMinimumOrientedNormalRadialMatrix,
    ← centerMinimumOrientedNormalRadialMatrix]
  exact M.centerMinimumOrientedRadialMatrix_rotation theta


-- @@ L1007-1014 verbatim
def centerMinimumOrientedRadialBaseUnit
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    (Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det
      (M.centerMinimumOrientedNormalRadialMatrix 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (det_centerMinimumOrientedNormalRadialMatrix_ne_zero
        T hindex 1 0))).unit


-- @@ L1016-1023 verbatim
def centerMaximumOrientedRadialBaseUnit
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    (Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det
      (M.centerMaximumOrientedNormalRadialMatrix 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (det_centerMaximumOrientedNormalRadialMatrix_ne_zero
        T hindex 1 0))).unit


-- @@ L1025-1034 verbatim
@[simp] theorem coe_centerMinimumOrientedRadialBaseUnit
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    (centerMinimumOrientedRadialBaseUnit T hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      M.centerMinimumOrientedNormalRadialMatrix 1 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det
      (M.centerMinimumOrientedNormalRadialMatrix 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (det_centerMinimumOrientedNormalRadialMatrix_ne_zero
        T hindex 1 0))).unit_spec


-- @@ L1036-1045 verbatim
@[simp] theorem coe_centerMaximumOrientedRadialBaseUnit
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    (centerMaximumOrientedRadialBaseUnit T hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      M.centerMaximumOrientedNormalRadialMatrix 1 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det
      (M.centerMaximumOrientedNormalRadialMatrix 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (det_centerMaximumOrientedNormalRadialMatrix_ne_zero
        T hindex 1 0))).unit_spec


-- @@ L1047-1052 verbatim
def centerMinimumNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  M.centerMinimumOrientedNormalRadialMatrix s theta *
    (↑(centerMinimumOrientedRadialBaseUnit T hindex)⁻¹ :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L1054-1059 verbatim
def centerMaximumNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  M.centerMaximumOrientedNormalRadialMatrix s theta *
    (↑(centerMaximumOrientedRadialBaseUnit T hindex)⁻¹ :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L1061-1069 verbatim
theorem centerMinimumNormalizedMatrix_one
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (theta : ℝ) :
    centerMinimumNormalizedMatrix T hindex 1 theta =
      twistMat a (StandardBirth.orientationSign a * theta) := by
  rw [centerMinimumNormalizedMatrix,
    M.centerMinimumOrientedRadialMatrix_rotation theta,
    ← coe_centerMinimumOrientedRadialBaseUnit T hindex]
  rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]


-- @@ L1071-1079 verbatim
theorem centerMaximumNormalizedMatrix_one
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (theta : ℝ) :
    centerMaximumNormalizedMatrix T hindex 1 theta =
      twistMat a (StandardBirth.orientationSign a * theta) := by
  rw [centerMaximumNormalizedMatrix,
    M.centerMaximumOrientedRadialMatrix_rotation theta,
    ← coe_centerMaximumOrientedRadialBaseUnit T hindex]
  rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]


-- @@ L1081-1081 verbatim
/-! ## Continuity, periodicity, and positive determinant -/


-- @@ L1083-1092 verbatim
theorem continuous_centerUnitTangent
    (M : StandardMorseEventAt C center) :
    Continuous M.centerUnitTangent := by
  have heq : M.centerUnitTangent = fun theta =>
      Real.cos theta • M.centerUnitTangent 0 -
        Real.sin theta • M.centerRadialTangent 0 := by
    funext theta
    exact M.centerUnitTangent_rotation theta
  rw [heq]
  fun_prop


-- @@ L1094-1098 verbatim
theorem continuous_centerUnitTangentRev
    (M : StandardMorseEventAt C center) :
    Continuous M.centerUnitTangentRev := by
  unfold centerUnitTangentRev
  exact M.continuous_centerUnitTangent.neg


-- @@ L1100-1109 verbatim
theorem continuous_centerRadialTangent
    (M : StandardMorseEventAt C center) :
    Continuous M.centerRadialTangent := by
  have heq : M.centerRadialTangent = fun theta =>
      Real.sin theta • M.centerUnitTangent 0 +
        Real.cos theta • M.centerRadialTangent 0 := by
    funext theta
    exact M.centerRadialTangent_rotation theta
  rw [heq]
  fun_prop


-- @@ L1111-1117 verbatim
theorem continuous_centerNormalRow_zero
    (M : StandardMorseEventAt C center) :
    Continuous fun theta : ℝ => M.centerNormalRow 0 theta := by
  rw [continuous_iff_continuousAt]
  intro theta
  exact (M.continuousAt_centerNormalRow_zero theta).comp
    (continuous_const.prodMk continuous_id).continuousAt


-- @@ L1119-1133 verbatim
theorem continuous_centerMinimumNormalRadialLast
    (M : StandardMorseEventAt C center) :
    Continuous fun q : I × ℝ =>
      M.centerMinimumNormalRadialLast q.1 q.2 := by
  have hs : Continuous fun q : I × ℝ => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hn : Continuous fun q : I × ℝ => M.centerNormalRow 0 q.2 :=
    M.continuous_centerNormalRow_zero.comp continuous_snd
  have hr : Continuous fun q : I × ℝ => M.centerRadialTangent q.2 :=
    M.continuous_centerRadialTangent.comp continuous_snd
  have hsign : Continuous fun _ : I × ℝ =>
      (nonzeroOrientationSign M.centerMinimumPairingScalar : ℝ) :=
    continuous_const
  unfold centerMinimumNormalRadialLast
  exact ((continuous_const.sub hs).smul (hsign.smul hn)).add (hs.smul hr)


-- @@ L1135-1149 verbatim
theorem continuous_centerMaximumNormalRadialLast
    (M : StandardMorseEventAt C center) :
    Continuous fun q : I × ℝ =>
      M.centerMaximumNormalRadialLast q.1 q.2 := by
  have hs : Continuous fun q : I × ℝ => (q.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hn : Continuous fun q : I × ℝ => M.centerNormalRow 0 q.2 :=
    M.continuous_centerNormalRow_zero.comp continuous_snd
  have hr : Continuous fun q : I × ℝ => M.centerRadialTangent q.2 :=
    M.continuous_centerRadialTangent.comp continuous_snd
  have hsign : Continuous fun _ : I × ℝ =>
      (nonzeroOrientationSign M.centerMaximumPairingScalar : ℝ) :=
    continuous_const
  unfold centerMaximumNormalRadialLast
  exact ((continuous_const.sub hs).smul (hsign.smul hn)).add (hs.smul hr)


-- @@ L1151-1179 verbatim
theorem continuous_centerMinimumOrientedNormalRadialMatrix
    (M : StandardMorseEventAt C center) :
    Continuous fun q : I × ℝ =>
      M.centerMinimumOrientedNormalRadialMatrix q.1 q.2 := by
  have ht : Continuous fun q : I × ℝ =>
      StandardBirth.orientationSign a • M.centerUnitTangent q.2 :=
    (continuous_const : Continuous fun _ : I × ℝ =>
      (StandardBirth.orientationSign a : ℝ)).smul
      (M.continuous_centerUnitTangent.comp continuous_snd)
  have hl := M.continuous_centerMinimumNormalRadialLast
  apply continuous_matrix
  intro i j
  have hrow : Continuous fun q : I × ℝ =>
      M.centerMinimumOrientedNormalRadialRows q.1 q.2 i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simpa only [M.centerMinimumOrientedNormalRadialRows_zero] using ht
    · induction i using Fin.lastCases with
      | last =>
          have hlast : (Fin.last (a + 1)).succ =
              (Fin.last (a + 2) : Fin (a + 3)) := by
            apply Fin.ext
            simp
          rw [hlast]
          simpa only [M.centerMinimumOrientedNormalRadialRows_last] using hl
      | cast i =>
          simpa only [M.centerMinimumOrientedNormalRadialRows_middle] using
            (continuous_const : Continuous fun _ : I × ℝ =>
              M.centerTransverseNormal i)
  exact (EuclideanSpace.proj j).continuous.comp hrow


-- @@ L1181-1207 verbatim
theorem continuous_centerMaximumOrientedNormalRadialMatrix
    (M : StandardMorseEventAt C center) :
    Continuous fun q : I × ℝ =>
      M.centerMaximumOrientedNormalRadialMatrix q.1 q.2 := by
  have ht : Continuous fun q : I × ℝ =>
      (-StandardBirth.orientationSign a) • M.centerUnitTangentRev q.2 :=
    (continuous_const : Continuous fun _ : I × ℝ =>
      (-StandardBirth.orientationSign a : ℝ)).smul
      (M.continuous_centerUnitTangentRev.comp continuous_snd)
  have hl := M.continuous_centerMaximumNormalRadialLast
  apply continuous_matrix
  intro i j
  have hrow : Continuous fun q : I × ℝ =>
      M.centerMaximumOrientedNormalRadialRows q.1 q.2 i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simpa [centerMaximumOrientedNormalRadialRows,
        centerRowsWith] using ht
    · induction i using Fin.lastCases with
      | last =>
          simpa [centerMaximumOrientedNormalRadialRows,
            centerRowsWith] using hl
      | cast i =>
          simpa [centerMaximumOrientedNormalRadialRows,
            centerRowsWith] using
            (continuous_const : Continuous fun _ : I × ℝ =>
              M.centerTransverseNormal i)
  exact (EuclideanSpace.proj j).continuous.comp hrow


-- @@ L1209-1215 verbatim
theorem continuous_centerMinimumNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    Continuous fun q : I × ℝ =>
      centerMinimumNormalizedMatrix T hindex q.1 q.2 := by
  unfold centerMinimumNormalizedMatrix
  exact M.continuous_centerMinimumOrientedNormalRadialMatrix.matrix_mul
    continuous_const


-- @@ L1217-1223 verbatim
theorem continuous_centerMaximumNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    Continuous fun q : I × ℝ =>
      centerMaximumNormalizedMatrix T hindex q.1 q.2 := by
  unfold centerMaximumNormalizedMatrix
  exact M.continuous_centerMaximumOrientedNormalRadialMatrix.matrix_mul
    continuous_const


-- @@ L1225-1229 verbatim
theorem centerUnitTangent_two_pi
    (M : StandardMorseEventAt C center) :
    M.centerUnitTangent (2 * Real.pi) = M.centerUnitTangent 0 := by
  rw [M.centerUnitTangent_rotation]
  simp [Real.cos_two_pi, Real.sin_two_pi]


-- @@ L1231-1235 verbatim
theorem centerRadialTangent_two_pi
    (M : StandardMorseEventAt C center) :
    M.centerRadialTangent (2 * Real.pi) = M.centerRadialTangent 0 := by
  rw [M.centerRadialTangent_rotation]
  simp [Real.cos_two_pi, Real.sin_two_pi]


-- @@ L1237-1244 verbatim
theorem centerNormalRow_zero_two_pi
    (M : StandardMorseEventAt C center) :
    M.centerNormalRow 0 (2 * Real.pi) = M.centerNormalRow 0 0 := by
  rw [M.centerNormalRow_zero, M.centerNormalRow_zero]
  congr 1
  ext i
  fin_cases i <;> simp [definiteCircleParam, pairToMorseParam,
    Real.cos_two_pi, Real.sin_two_pi]


-- @@ L1246-1253 verbatim
theorem centerMinimumNormalizedMatrix_two_pi
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (s : I) :
    centerMinimumNormalizedMatrix T hindex s (2 * Real.pi) =
      centerMinimumNormalizedMatrix T hindex s 0 := by
  unfold centerMinimumNormalizedMatrix centerMinimumOrientedNormalRadialMatrix
    centerMinimumOrientedNormalRadialRows centerMinimumNormalRadialLast
  rw [M.centerUnitTangent_two_pi, M.centerNormalRow_zero_two_pi,
    M.centerRadialTangent_two_pi]


-- @@ L1255-1263 verbatim
theorem centerMaximumNormalizedMatrix_two_pi
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (s : I) :
    centerMaximumNormalizedMatrix T hindex s (2 * Real.pi) =
      centerMaximumNormalizedMatrix T hindex s 0 := by
  unfold centerMaximumNormalizedMatrix centerMaximumOrientedNormalRadialMatrix
    centerMaximumOrientedNormalRadialRows centerMaximumNormalRadialLast
    centerUnitTangentRev
  rw [M.centerUnitTangent_two_pi, M.centerNormalRow_zero_two_pi,
    M.centerRadialTangent_two_pi]


-- @@ L1265-1276 verbatim
theorem det_centerMinimumNormalizedMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    (centerMinimumNormalizedMatrix T hindex s theta).det ≠ 0 := by
  rw [centerMinimumNormalizedMatrix, Matrix.det_mul]
  apply mul_ne_zero
  · exact det_centerMinimumOrientedNormalRadialMatrix_ne_zero
      T hindex s theta
  · have hu : IsUnit
        (↑(centerMinimumOrientedRadialBaseUnit T hindex)⁻¹ :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) := Units.isUnit _
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)


-- @@ L1278-1289 verbatim
theorem det_centerMaximumNormalizedMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    (centerMaximumNormalizedMatrix T hindex s theta).det ≠ 0 := by
  rw [centerMaximumNormalizedMatrix, Matrix.det_mul]
  apply mul_ne_zero
  · exact det_centerMaximumOrientedNormalRadialMatrix_ne_zero
      T hindex s theta
  · have hu : IsUnit
        (↑(centerMaximumOrientedRadialBaseUnit T hindex)⁻¹ :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) := Units.isUnit _
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)


-- @@ L1291-1314 verbatim
theorem det_centerMinimumNormalizedMatrix_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    0 < (centerMinimumNormalizedMatrix T hindex s theta).det := by
  let d : I → ℝ := fun u =>
    (centerMinimumNormalizedMatrix T hindex u theta).det
  change 0 < d s
  have hd : Continuous d := by
    exact ((continuous_centerMinimumNormalizedMatrix T hindex).comp
      (continuous_id.prodMk continuous_const)).matrix_det
  have hdne : ∀ u, d u ≠ 0 := fun u =>
    det_centerMinimumNormalizedMatrix_ne_zero T hindex u theta
  have hd1 : d 1 = 1 := by
    dsimp [d]
    rw [centerMinimumNormalizedMatrix_one T hindex theta,
      StandardBirth.det_twistMat]
  by_contra hpos
  have hsneg : d s < 0 :=
    lt_of_le_of_ne (le_of_not_gt hpos) (hdne s)
  have hmem : (0 : ℝ) ∈ Set.Icc (d s) (d 1) := by
    rw [hd1]
    exact ⟨hsneg.le, by norm_num⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ s 1 hd hmem
  exact hdne u hu


-- @@ L1316-1339 verbatim
theorem det_centerMaximumNormalizedMatrix_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    0 < (centerMaximumNormalizedMatrix T hindex s theta).det := by
  let d : I → ℝ := fun u =>
    (centerMaximumNormalizedMatrix T hindex u theta).det
  change 0 < d s
  have hd : Continuous d := by
    exact ((continuous_centerMaximumNormalizedMatrix T hindex).comp
      (continuous_id.prodMk continuous_const)).matrix_det
  have hdne : ∀ u, d u ≠ 0 := fun u =>
    det_centerMaximumNormalizedMatrix_ne_zero T hindex u theta
  have hd1 : d 1 = 1 := by
    dsimp [d]
    rw [centerMaximumNormalizedMatrix_one T hindex theta,
      StandardBirth.det_twistMat]
  by_contra hpos
  have hsneg : d s < 0 :=
    lt_of_le_of_ne (le_of_not_gt hpos) (hdne s)
  have hmem : (0 : ℝ) ∈ Set.Icc (d s) (d 1) := by
    rw [hd1]
    exact ⟨hsneg.le, by norm_num⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ s 1 hd hmem
  exact hdne u hu


-- @@ L1341-1341 verbatim
/-! ## Closed center loops and their class -/


-- @@ L1343-1347 verbatim
def centerMinimumNormalizedMatrixMap
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    C(I × ℝ, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun q := centerMinimumNormalizedMatrix T hindex q.1 q.2
  continuous_toFun := continuous_centerMinimumNormalizedMatrix T hindex


-- @@ L1349-1353 verbatim
def centerMaximumNormalizedMatrixMap
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    C(I × ℝ, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun q := centerMaximumNormalizedMatrix T hindex q.1 q.2
  continuous_toFun := continuous_centerMaximumNormalizedMatrix T hindex


-- @@ L1355-1358 verbatim
def centerMinimumNormalizedLoop
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  (centerMinimumNormalizedMatrixMap T hindex).comp definiteCenterLoopParam


-- @@ L1360-1363 verbatim
def centerMaximumNormalizedLoop
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  (centerMaximumNormalizedMatrixMap T hindex).comp definiteCenterLoopParam


-- @@ L1365-1371 verbatim
theorem centerMinimumNormalizedLoop_closed
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    centerMinimumNormalizedLoop T hindex 0 =
      centerMinimumNormalizedLoop T hindex 1 := by
  simpa [centerMinimumNormalizedLoop, centerMinimumNormalizedMatrixMap,
    definiteCenterLoopParam] using
      (centerMinimumNormalizedMatrix_two_pi T hindex 0).symm


-- @@ L1373-1379 verbatim
theorem centerMaximumNormalizedLoop_closed
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    centerMaximumNormalizedLoop T hindex 0 =
      centerMaximumNormalizedLoop T hindex 1 := by
  simpa [centerMaximumNormalizedLoop, centerMaximumNormalizedMatrixMap,
    definiteCenterLoopParam] using
      (centerMaximumNormalizedMatrix_two_pi T hindex 0).symm


-- @@ L1381-1385 verbatim
theorem centerMinimumNormalizedLoop_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (u : I) :
    0 < (centerMinimumNormalizedLoop T hindex u).det :=
  det_centerMinimumNormalizedMatrix_pos T hindex 0
    (2 * Real.pi * (u : ℝ))


-- @@ L1387-1391 verbatim
theorem centerMaximumNormalizedLoop_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (u : I) :
    0 < (centerMaximumNormalizedLoop T hindex u).det :=
  det_centerMaximumNormalizedMatrix_pos T hindex 0
    (2 * Real.pi * (u : ℝ))


-- @@ L1393-1404 verbatim
theorem centerMinimumNormalizedMatrix_one_eq_birthPlaneMatrixLoop
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (u : I) :
    centerMinimumNormalizedMatrix T hindex 1
        (2 * Real.pi * (u : ℝ)) =
      StandardBirth.birthPlaneMatrixLoop a u := by
  rw [centerMinimumNormalizedMatrix_one T hindex]
  change twistMat a
      (StandardBirth.orientationSign a * (2 * Real.pi * (u : ℝ))) =
    (StandardBirth.birthPlaneLoop a u :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
  rw [StandardBirth.birthPlaneLoop_coe]
  rfl


-- @@ L1406-1417 verbatim
theorem centerMaximumNormalizedMatrix_one_eq_birthPlaneMatrixLoop
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (u : I) :
    centerMaximumNormalizedMatrix T hindex 1
        (2 * Real.pi * (u : ℝ)) =
      StandardBirth.birthPlaneMatrixLoop a u := by
  rw [centerMaximumNormalizedMatrix_one T hindex]
  change twistMat a
      (StandardBirth.orientationSign a * (2 * Real.pi * (u : ℝ))) =
    (StandardBirth.birthPlaneLoop a u :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
  rw [StandardBirth.birthPlaneLoop_coe]
  rfl


-- @@ L1419-1429 verbatim
def centerMinimumBirthMatrixHomotopy
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    ContinuousMap.Homotopy
      (centerMinimumNormalizedLoop T hindex)
      (StandardBirth.birthPlaneMatrixLoop a) where
  toContinuousMap :=
    (centerMinimumNormalizedMatrixMap T hindex).comp
      definiteCenterHomotopyParam
  map_zero_left _u := rfl
  map_one_left u :=
    centerMinimumNormalizedMatrix_one_eq_birthPlaneMatrixLoop T hindex u


-- @@ L1431-1441 verbatim
def centerMaximumBirthMatrixHomotopy
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    ContinuousMap.Homotopy
      (centerMaximumNormalizedLoop T hindex)
      (StandardBirth.birthPlaneMatrixLoop a) where
  toContinuousMap :=
    (centerMaximumNormalizedMatrixMap T hindex).comp
      definiteCenterHomotopyParam
  map_zero_left _u := rfl
  map_one_left u :=
    centerMaximumNormalizedMatrix_one_eq_birthPlaneMatrixLoop T hindex u


-- @@ L1443-1448 verbatim
@[simp] theorem centerMinimumBirthMatrixHomotopy_apply
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (q : I × I) :
    centerMinimumBirthMatrixHomotopy T hindex q =
      centerMinimumNormalizedMatrix T hindex q.1
        (2 * Real.pi * (q.2 : ℝ)) :=
  rfl


-- @@ L1450-1455 verbatim
@[simp] theorem centerMaximumBirthMatrixHomotopy_apply
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (q : I × I) :
    centerMaximumBirthMatrixHomotopy T hindex q =
      centerMaximumNormalizedMatrix T hindex q.1
        (2 * Real.pi * (q.2 : ℝ)) :=
  rfl


-- @@ L1457-1461 verbatim
theorem centerMinimumBirthMatrixHomotopy_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (q : I × I) :
    0 < (centerMinimumBirthMatrixHomotopy T hindex q).det :=
  det_centerMinimumNormalizedMatrix_pos T hindex q.1
    (2 * Real.pi * (q.2 : ℝ))


-- @@ L1463-1467 verbatim
theorem centerMaximumBirthMatrixHomotopy_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (q : I × I) :
    0 < (centerMaximumBirthMatrixHomotopy T hindex q).det :=
  det_centerMaximumNormalizedMatrix_pos T hindex q.1
    (2 * Real.pi * (q.2 : ℝ))


-- @@ L1469-1473 verbatim
theorem centerMinimumBirthMatrixHomotopy_closed
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (s : I) :
    centerMinimumBirthMatrixHomotopy T hindex (s, 0) =
      centerMinimumBirthMatrixHomotopy T hindex (s, 1) := by
  simpa using (centerMinimumNormalizedMatrix_two_pi T hindex s).symm


-- @@ L1475-1479 verbatim
theorem centerMaximumBirthMatrixHomotopy_closed
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (s : I) :
    centerMaximumBirthMatrixHomotopy T hindex (s, 0) =
      centerMaximumBirthMatrixHomotopy T hindex (s, 1) := by
  simpa using (centerMaximumNormalizedMatrix_two_pi T hindex s).symm


-- @@ L1481-1502 verbatim
/-- The normalized center frame of every immersed production minimum has the
nontrivial stable class. -/
theorem loopClassZ2_centerMinimumNormalized_eq_one
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    loopClassZ2
        (positiveMatrixSOMap
          (centerMinimumNormalizedLoop T hindex)
          (centerMinimumNormalizedLoop_det_pos T hindex))
        (positiveMatrixSOMap_closed
          (centerMinimumNormalizedLoop T hindex)
          (centerMinimumNormalizedLoop_det_pos T hindex)
          (centerMinimumNormalizedLoop_closed T hindex)) = 1 := by
  have hclass := loopClassZ2_positiveMatrixHomotopy_congr
    (centerMinimumBirthMatrixHomotopy T hindex)
    (centerMinimumNormalizedLoop_det_pos T hindex)
    (StandardBirth.birthPlaneMatrixLoop_det_pos a)
    (centerMinimumBirthMatrixHomotopy_det_pos T hindex)
    (centerMinimumNormalizedLoop_closed T hindex)
    (StandardBirth.birthPlaneMatrixLoop_closed a)
    (centerMinimumBirthMatrixHomotopy_closed T hindex)
  exact hclass.trans
    (StandardBirth.loopClassZ2_positiveMatrixSOMap_birthPlaneMatrixLoop a)


-- @@ L1504-1525 verbatim
/-- The clockwise boundary orientation at a production maximum gives the
same nontrivial normalized stable class. -/
theorem loopClassZ2_centerMaximumNormalized_eq_one
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    loopClassZ2
        (positiveMatrixSOMap
          (centerMaximumNormalizedLoop T hindex)
          (centerMaximumNormalizedLoop_det_pos T hindex))
        (positiveMatrixSOMap_closed
          (centerMaximumNormalizedLoop T hindex)
          (centerMaximumNormalizedLoop_det_pos T hindex)
          (centerMaximumNormalizedLoop_closed T hindex)) = 1 := by
  have hclass := loopClassZ2_positiveMatrixHomotopy_congr
    (centerMaximumBirthMatrixHomotopy T hindex)
    (centerMaximumNormalizedLoop_det_pos T hindex)
    (StandardBirth.birthPlaneMatrixLoop_det_pos a)
    (centerMaximumBirthMatrixHomotopy_det_pos T hindex)
    (centerMaximumNormalizedLoop_closed T hindex)
    (StandardBirth.birthPlaneMatrixLoop_closed a)
    (centerMaximumBirthMatrixHomotopy_closed T hindex)
  exact hclass.trans
    (StandardBirth.loopClassZ2_positiveMatrixSOMap_birthPlaneMatrixLoop a)


-- @@ L1527-1527 verbatim
end StandardMorseEventAt


-- @@ L1529-1529 verbatim
end Submission
