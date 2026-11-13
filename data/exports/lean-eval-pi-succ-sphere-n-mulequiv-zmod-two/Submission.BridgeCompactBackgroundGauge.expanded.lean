import Mathlib
import Submission.BridgeFlatConfiguration
import Submission.ConcreteConfigurationMorseReduction
import Submission.SOSmoothPath


-- @@ L6-21 verbatim
/-!
# Orientation-preserving harmonization of bridge backgrounds

Every bridge defining map is exactly the nonzero vector `-B.y` outside a
fixed ball, whereas the compact Morse models use `compactBackground m`.
The older `backgroundEquiv` sends one vector to the other by a positive scale
and one Householder reflection.  That map can reverse orientation and hence
need not be joined to the identity through invertible gauges.

Here we instead normalize both vectors, rotate the first unit vector to the
second by an element of `SO`, and correct the norm by a positive scalar.  The
bridge axis condition rules out the only exceptional (antipodal) pair.  The
smooth `SO` path constructed in `SOSmoothPath` then gives an actual
common-fiber defining-map homotopy and signed framed cobordism, while carrying
the spatial background literally to the compact-model background.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Set Function

-- @@ L28-28 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L30-30 verbatim
namespace Submission

-- @@ L31-31 verbatim
namespace BridgeCompactBackgroundGauge


-- @@ L33-33 verbatim
open ConcreteConfigurationMorseReduction


-- @@ L35-35 verbatim
variable {n : ℕ}


-- @@ L37-37 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)

-- @@ L38-38 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L40-42 verbatim
/-- The unit vector in the direction of a nonzero Euclidean vector. -/
def unitVector (c : F) (hc : c ≠ 0) : UnitSphere F :=
  ⟨‖c‖⁻¹ • c, mem_sphere_zero_iff_norm.mpr (norm_normalize hc)⟩


-- @@ L44-46 verbatim
@[simp] theorem unitVector_coe (c : F) (hc : c ≠ 0) :
    ((unitVector c hc : UnitSphere F) : F) = ‖c‖⁻¹ • c :=
  rfl


-- @@ L48-51 verbatim
/-- Multiplying the normalized vector back by its norm recovers the vector. -/
theorem norm_smul_unitVector (c : F) (hc : c ≠ 0) :
    ‖c‖ • ((unitVector c hc : UnitSphere F) : F) = c := by
  rw [unitVector_coe, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_smul]


-- @@ L53-56 verbatim
/-- The short special-orthogonal rotation between two non-antipodal
background directions. -/
def rotation (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) : SOGroup n :=
  rotTo (unitVector c₁ h₁) (unitVector c₂ h₂)


-- @@ L58-72 verbatim
/-- The `SO` rotation acts on normalized vectors as prescribed. -/
theorem rotation_unitVector
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hne : unitVector c₁ h₁ ≠ -unitVector c₂ h₂) :
    SOFrameGauge.toCLM (rotation c₁ c₂ h₁ h₂)
        ((unitVector c₁ h₁ : UnitSphere F) : F) =
      ((unitVector c₂ h₂ : UnitSphere F) : F) := by
  have hdist : dist (unitVector c₁ h₁) (unitVector c₂ h₂) < 2 :=
    dist_lt_two_of_ne_neg _ _ hne
  have hdot : -1 <
      coords (unitVector c₁ h₁) ⬝ᵥ coords (unitVector c₂ h₂) :=
    neg_one_lt_coords_dot_of_dist_lt_two hdist
  ext i
  have hi := congrFun (rotTo_mulVec hdot) i
  simpa [rotation, SOFrameGauge.toCLM_apply_coord, Matrix.mulVec, coords] using hi


-- @@ L74-99 verbatim
/-- Positive rescaling followed by the special-orthogonal rotation sends the
first background literally to the second. -/
theorem scaledRotation_apply
    (c₁ c₂ : F) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (hne : unitVector c₁ h₁ ≠ -unitVector c₂ h₂) :
    SOFrameGauge.toCLM (rotation c₁ c₂ h₁ h₂)
        (backgroundScale c₁ c₂ • c₁) = c₂ := by
  calc
    SOFrameGauge.toCLM (rotation c₁ c₂ h₁ h₂)
        (backgroundScale c₁ c₂ • c₁) =
        backgroundScale c₁ c₂ •
          SOFrameGauge.toCLM (rotation c₁ c₂ h₁ h₂) c₁ := by
            rw [map_smul]
    _ = backgroundScale c₁ c₂ •
          SOFrameGauge.toCLM (rotation c₁ c₂ h₁ h₂)
            (‖c₁‖ • ((unitVector c₁ h₁ : UnitSphere F) : F)) := by
          rw [norm_smul_unitVector c₁ h₁]
    _ = (backgroundScale c₁ c₂ * ‖c₁‖) •
          SOFrameGauge.toCLM (rotation c₁ c₂ h₁ h₂)
            ((unitVector c₁ h₁ : UnitSphere F) : F) := by
          rw [map_smul, smul_smul]
    _ = ‖c₂‖ • ((unitVector c₂ h₂ : UnitSphere F) : F) := by
          rw [rotation_unitVector c₁ c₂ h₁ h₂ hne]
          congr 1
          exact div_mul_cancel₀ ‖c₂‖ (norm_ne_zero_iff.mpr h₁)
    _ = c₂ := norm_smul_unitVector c₂ h₂


-- @@ L101-107 verbatim
/-- A smooth positive-scale and `SO` gauge path carrying `c₁` to `c₂`. -/
structure Data (c₁ c₂ : F) where
  source_ne_zero : c₁ ≠ 0
  target_ne_zero : c₂ ≠ 0
  nonantipodal : unitVector c₁ source_ne_zero ≠ -unitVector c₂ target_ne_zero
  soPath : SmoothSOPath
    (rotation c₁ c₂ source_ne_zero target_ne_zero)


-- @@ L109-109 verbatim
namespace Data


-- @@ L111-111 verbatim
variable {n : ℕ}

-- @@ L112-112 verbatim
variable {c₁ c₂ : EuclideanSpace ℝ (Fin n)}


-- @@ L114-116 verbatim
/-- The positive scalar at time `s`, flattened outside the unit interval. -/
def scalar (_D : Data (n := n) c₁ c₂) (s : ℝ) : ℝ :=
  slideScale (backgroundScale c₁ c₂) (normRamp s)


-- @@ L118-121 verbatim
theorem backgroundScale_pos (D : Data (n := n) c₁ c₂) :
    0 < backgroundScale c₁ c₂ :=
  div_pos (norm_pos_iff.mpr D.target_ne_zero)
    (norm_pos_iff.mpr D.source_ne_zero)


-- @@ L123-124 verbatim
theorem scalar_pos (D : Data (n := n) c₁ c₂) (s : ℝ) : 0 < D.scalar s :=
  slideScale_pos D.backgroundScale_pos (normRamp_nonneg s) (normRamp_le_one s)


-- @@ L126-127 verbatim
@[simp] theorem scalar_zero (D : Data (n := n) c₁ c₂) : D.scalar 0 = 1 := by
  rw [scalar, normRamp_of_le_quarter (by norm_num), slideScale_zero]


-- @@ L129-131 verbatim
@[simp] theorem scalar_one (D : Data (n := n) c₁ c₂) :
    D.scalar 1 = backgroundScale c₁ c₂ := by
  rw [scalar, normRamp_of_three_quarter_le (by norm_num), slideScale_one]


-- @@ L133-137 verbatim
/-- The spatially constant codomain gauge. -/
def gauge (D : Data (n := n) c₁ c₂) (s : ℝ)
    (_x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  D.scalar s • SOFrameGauge.toCLM (D.soPath.Q s)


-- @@ L139-148 verbatim
theorem gauge_smooth (D : Data (n := n) c₁ c₂) :
    ContDiff ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) =>
      D.gauge p.1 p.2) := by
  have hr : ContDiff ℝ ∞ (fun s : ℝ => normRamp s) := contDiff_normRamp
  have hs : ContDiff ℝ ∞ (fun s : ℝ => D.scalar s) := by
    exact (contDiff_const.sub hr).add (hr.mul contDiff_const)
  have hQ : ContDiff ℝ ∞
      (fun s : ℝ => SOFrameGauge.toCLM (D.soPath.Q s)) :=
    SOFrameGauge.contDiff_toCLM D.soPath.smooth
  exact (hs.comp contDiff_fst).smul (hQ.comp contDiff_fst)


-- @@ L150-153 verbatim
@[simp] theorem gauge_zero (D : Data (n := n) c₁ c₂)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    D.gauge 0 x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  simp [gauge, D.soPath.zero, SOFrameGauge.toCLM_one]


-- @@ L155-169 verbatim
theorem gauge_bijective (D : Data (n := n) c₁ c₂) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    Bijective (D.gauge s x) := by
  have ha : D.scalar s ≠ 0 := (D.scalar_pos s).ne'
  have hA := SOFrameGauge.toCLM_bijective (D.soPath.Q s)
  constructor
  · intro u v huv
    apply hA.1
    apply smul_right_injective (EuclideanSpace ℝ (Fin n)) ha
    simpa [gauge] using huv
  · intro y
    obtain ⟨u, hu⟩ := hA.2 ((D.scalar s)⁻¹ • y)
    refine ⟨u, ?_⟩
    change D.scalar s • SOFrameGauge.toCLM (D.soPath.Q s) u = y
    rw [hu, smul_smul, mul_inv_cancel₀ ha, one_smul]


-- @@ L171-180 verbatim
/-- At the endpoint the gauge sends the first background exactly to the
second. -/
theorem gauge_one_apply_source (D : Data (n := n) c₁ c₂)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    D.gauge 1 x c₁ = c₂ := by
  change D.scalar 1 • SOFrameGauge.toCLM (D.soPath.Q 1) c₁ = c₂
  rw [D.scalar_one, D.soPath.one]
  rw [← map_smul]
  exact scaledRotation_apply c₁ c₂ D.source_ne_zero D.target_ne_zero
    D.nonantipodal


-- @@ L182-190 verbatim
/-- The actual common-fiber defining-map homotopy supplied by the background
gauge. -/
def homotopy (D : Data (n := n) c₁ c₂) (X : FramedLevelSet n) :
    DefiningMapHomotopy X
      (X.gaugeTransform (D.gauge 1)
        (contDiff_gauge_slice D.gauge_smooth 1)
        (fun x => D.gauge_bijective 1 x)) :=
  DefiningMapHomotopy.ofGauge X D.gauge D.gauge_smooth D.gauge_zero
    (fun s _hs x => D.gauge_bijective s x)


-- @@ L192-206 verbatim
/-- Package the endpoint presentation as a flat signed configuration with the
new literal background. -/
def targetFlat (D : Data (n := n) c₁ c₂)
    (A : FlatSignedConfiguration n c₁) :
    FlatSignedConfiguration n c₂ where
  X := (D.homotopy A.X).toCobordism.X₁
  sign := A.sign.restrict (D.homotopy A.X).fiber_subset
  center := A.center
  radius := A.radius
  radius_nonneg := A.radius_nonneg
  flatOutside := by
    intro x hx
    change D.gauge 1 x (A.X.g x) = c₂
    rw [A.flatOutside x hx]
    exact D.gauge_one_apply_source x


-- @@ L208-213 verbatim
/-- The background change is an actual signed framed cobordism, not merely a
postcomposition equivalence. -/
def signedCobordism (D : Data (n := n) c₁ c₂)
    (A : FlatSignedConfiguration n c₁) :
    SignedFramedLevelCobordism A.sign (D.targetFlat A).sign :=
  (D.homotopy A.X).signedCobordism A.sign


-- @@ L215-215 verbatim
end Data


-- @@ L217-217 verbatim
/-! ## The bridge-specific non-antipodality certificate -/


-- @@ L219-219 verbatim
variable {m : ℕ} {z : StableSpherePi (m + 2)}


-- @@ L221-221 verbatim
local notation "FB" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L223-247 verbatim
/-- The bridge axis condition prevents its native background direction from
being antipodal to the last-coordinate compact background. -/
theorem bridge_nonantipodal (B : BridgeData (m + 2) z) :
    unitVector (-B.y) B.nativeBackground_ne_zero ≠
      -unitVector (compactBackground m)
        (CompactBirth.background_ne_zero (m + 1)) := by
  let i0 : Fin (m + 2) := ⟨0, by omega⟩
  let j0 : Fin (m + 1) := ⟨0, by omega⟩
  intro h
  have hcoord := congrArg
    (fun q : UnitSphere FB => ((q : FB) i0)) h
  have hcompact : compactBackground m i0 = 0 := by
    change CompactBirth.background (m + 1) i0 = 0
    simpa [i0, j0] using
      (CompactBirth.background_apply_castSucc (m + 1) j0)
  have hypos : 0 < B.y i0 := by
    simpa [i0] using B.axis_pos (by omega : 0 < m + 2)
  have hinv : 0 < ‖-B.y‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr B.nativeBackground_ne_zero)
  have hneg : ‖-B.y‖⁻¹ * (-B.y i0) < 0 := by
    have : -B.y i0 < 0 := by simpa using neg_lt_zero.mpr hypos
    exact mul_neg_of_pos_of_neg hinv this
  have hzero : ‖-B.y‖⁻¹ * (-B.y i0) = 0 := by
    simpa [unitVector, hcompact] using hcoord
  linarith


-- @@ L249-262 verbatim
/-- Every bridge admits an orientation-preserving smooth gauge which carries
its native flat background to the compact-Morse background. -/
theorem nonempty_bridgeData (B : BridgeData (m + 2) z) :
    Nonempty (Data (-B.y) (compactBackground m)) := by
  let A := rotation (-B.y) (compactBackground m)
    B.nativeBackground_ne_zero
    (CompactBirth.background_ne_zero (m + 1))
  obtain ⟨P⟩ := SmoothSOPath.nonempty (by omega : 0 < m + 2) A
  exact ⟨{
    source_ne_zero := B.nativeBackground_ne_zero
    target_ne_zero := CompactBirth.background_ne_zero (m + 1)
    nonantipodal := bridge_nonantipodal B
    soPath := P
  }⟩


-- @@ L264-273 verbatim
/-- The bridge itself, harmonized to the compact background and equipped with
the signed cobordism realizing the change. -/
theorem nonempty_targetFlat_and_cobordism (B : BridgeData (m + 2) z) :
    Nonempty
      {A : FlatSignedConfiguration (m + 2) (compactBackground m) //
        Nonempty (SignedFramedLevelCobordism B.fiberSign A.sign)} := by
  obtain ⟨D⟩ := nonempty_bridgeData B
  let A := D.targetFlat B.flatSignedConfiguration
  refine ⟨⟨A, ?_⟩⟩
  exact ⟨D.signedCobordism B.flatSignedConfiguration⟩


-- @@ L275-275 verbatim
end BridgeCompactBackgroundGauge

-- @@ L276-276 verbatim
end Submission
