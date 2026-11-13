import Mathlib
import Submission.AmbientNormalizationPrimitive


-- @@ L4-12 verbatim
/-!
# Concrete affine ambient isotopies

This file turns the scale-and-translate positioning move into an actual
`SmoothAmbientIsotopy`.  For `c > 0` and translation vector `b`, the endpoint
diffeomorphism is `x ↦ c • x + b`.  The positive scale is interpolated with
the global collar-flat switch, so the forward and inverse families are smooth
on all of `ℝ`, not merely on the geometric interval.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Set Function

-- @@ L17-17 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
variable {n : ℕ}


-- @@ L23-23 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L25-25 verbatim
namespace SmoothAmbientIsotopy


-- @@ L27-29 verbatim
/-- The positive scale used by the global affine isotopy. -/
def ambientAffineScale (c s : ℝ) : ℝ :=
  slideScale c (normRamp s)


-- @@ L31-33 verbatim
lemma ambientAffineScale_pos {c : ℝ} (hc : 0 < c) (s : ℝ) :
    0 < ambientAffineScale c s :=
  slideScale_pos hc (normRamp_nonneg s) (normRamp_le_one s)


-- @@ L35-37 verbatim
@[simp] theorem ambientAffineScale_zero (c : ℝ) :
    ambientAffineScale c 0 = 1 := by
  rw [ambientAffineScale, normRamp_of_le_quarter (by norm_num), slideScale_zero]


-- @@ L39-41 verbatim
@[simp] theorem ambientAffineScale_one (c : ℝ) :
    ambientAffineScale c 1 = c := by
  rw [ambientAffineScale, normRamp_of_three_quarter_le (by norm_num), slideScale_one]


-- @@ L43-45 verbatim
/-- Forward affine track. -/
def affineForward (c : ℝ) (b : E) (s : ℝ) (x : E) : E :=
  ambientAffineScale c s • x + normRamp s • b


-- @@ L47-49 verbatim
/-- Inverse affine track. -/
def affineInverse (c : ℝ) (b : E) (s : ℝ) (x : E) : E :=
  (ambientAffineScale c s)⁻¹ • (x - normRamp s • b)


-- @@ L51-57 verbatim
theorem contDiff_affineForward (c : ℝ) (b : E) :
    ContDiff ℝ ∞ (fun p : ℝ × E => affineForward c b p.1 p.2) := by
  have hr : ContDiff ℝ ∞ (fun p : ℝ × E => normRamp p.1) :=
    contDiff_normRamp.comp contDiff_fst
  have ha : ContDiff ℝ ∞ (fun p : ℝ × E => ambientAffineScale c p.1) :=
    (contDiff_const.sub hr).add (hr.mul contDiff_const)
  exact (ha.smul contDiff_snd).add (hr.smul contDiff_const)


-- @@ L59-68 verbatim
theorem contDiff_affineInverse (c : ℝ) (hc : 0 < c) (b : E) :
    ContDiff ℝ ∞ (fun p : ℝ × E => affineInverse c b p.1 p.2) := by
  have hr : ContDiff ℝ ∞ (fun p : ℝ × E => normRamp p.1) :=
    contDiff_normRamp.comp contDiff_fst
  have ha : ContDiff ℝ ∞ (fun p : ℝ × E => ambientAffineScale c p.1) :=
    (contDiff_const.sub hr).add (hr.mul contDiff_const)
  have hainv : ContDiff ℝ ∞
      (fun p : ℝ × E => (ambientAffineScale c p.1)⁻¹) :=
    ha.inv fun p => (ambientAffineScale_pos hc p.1).ne'
  exact hainv.smul (contDiff_snd.sub (hr.smul contDiff_const))


-- @@ L70-72 verbatim
@[simp] theorem affineForward_zero (c : ℝ) (b x : E) :
    affineForward c b 0 x = x := by
  simp [affineForward, normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num)]


-- @@ L74-76 verbatim
@[simp] theorem affineInverse_zero (c : ℝ) (b x : E) :
    affineInverse c b 0 x = x := by
  simp [affineInverse, normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num)]


-- @@ L78-81 verbatim
@[simp] theorem affineForward_one (c : ℝ) (b x : E) :
    affineForward c b 1 x = c • x + b := by
  simp [affineForward,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num)]


-- @@ L83-86 verbatim
@[simp] theorem affineInverse_one (c : ℝ) (b x : E) :
    affineInverse c b 1 x = c⁻¹ • (x - b) := by
  simp [affineInverse,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num)]


-- @@ L88-130 verbatim
/-- The global smooth ambient isotopy from the identity to
`x ↦ c • x + b`. -/
def affine (c : ℝ) (hc : 0 < c) (b : E) : SmoothAmbientIsotopy n where
  forward := affineForward c b
  inverse := affineInverse c b
  forward_smooth := contDiff_affineForward c b
  inverse_smooth := contDiff_affineInverse c hc b
  forward_zero := by
    funext x
    exact affineForward_zero c b x
  left_inv := by
    intro s hs x
    change (ambientAffineScale c s)⁻¹ •
      (ambientAffineScale c s • x + normRamp s • b - normRamp s • b) = x
    rw [add_sub_cancel_right, smul_smul,
      inv_mul_cancel₀ (ambientAffineScale_pos hc s).ne', one_smul]
  right_inv := by
    intro s hs x
    change ambientAffineScale c s •
      ((ambientAffineScale c s)⁻¹ • (x - normRamp s • b)) +
        normRamp s • b = x
    rw [smul_smul, mul_inv_cancel₀ (ambientAffineScale_pos hc s).ne', one_smul]
    abel
  inverse_fderiv_surjective := by
    intro s hs x
    let a : ℝ := ambientAffineScale c s
    let w : E := normRamp s • b
    have ha : a ≠ 0 := (ambientAffineScale_pos hc s).ne'
    have hderiv : fderiv ℝ (affineInverse c b s) x =
        a⁻¹ • ContinuousLinearMap.id ℝ E := by
      have hbase : HasFDerivAt (fun y : E => y - w)
          (ContinuousLinearMap.id ℝ E) x :=
        (hasFDerivAt_id x).sub_const w
      have h : HasFDerivAt (fun y : E => a⁻¹ • (y - w))
          (a⁻¹ • ContinuousLinearMap.id ℝ E) x :=
        hbase.const_smul (R := ℝ) a⁻¹
      change fderiv ℝ (fun y : E => a⁻¹ • (y - w)) x = _
      exact h.fderiv
    rw [hderiv]
    intro y
    refine ⟨a • y, ?_⟩
    rw [smul_apply, ContinuousLinearMap.id_apply, smul_smul,
      inv_mul_cancel₀ ha, one_smul]


-- @@ L132-134 verbatim
@[simp] theorem affine_forward (c : ℝ) (hc : 0 < c) (b : E) (s : ℝ) (x : E) :
    (affine c hc b).forward s x = affineForward c b s x :=
  rfl


-- @@ L136-138 verbatim
@[simp] theorem affine_inverse (c : ℝ) (hc : 0 < c) (b : E) (s : ℝ) (x : E) :
    (affine c hc b).inverse s x = affineInverse c b s x :=
  rfl


-- @@ L140-142 verbatim
@[simp] theorem affine_forward_endpoint (c : ℝ) (hc : 0 < c) (b x : E) :
    (affine c hc b).forward 1 x = c • x + b :=
  affineForward_one c b x


-- @@ L144-146 verbatim
@[simp] theorem affine_inverse_endpoint (c : ℝ) (hc : 0 < c) (b x : E) :
    (affine c hc b).inverse 1 x = c⁻¹ • (x - b) :=
  affineInverse_one c b x


-- @@ L148-150 verbatim
/-- Translation as a concrete ambient isotopy. -/
def translation (b : E) : SmoothAmbientIsotopy n :=
  affine 1 zero_lt_one b


-- @@ L152-154 verbatim
@[simp] theorem translation_forward_endpoint (b x : E) :
    (translation b).forward 1 x = x + b := by
  simp [translation]


-- @@ L156-158 verbatim
@[simp] theorem translation_inverse_endpoint (b x : E) :
    (translation b).inverse 1 x = x - b := by
  simp [translation]


-- @@ L160-162 verbatim
/-- Positive dilation as a concrete ambient isotopy. -/
def positiveDilation (c : ℝ) (hc : 0 < c) : SmoothAmbientIsotopy n :=
  affine c hc 0


-- @@ L164-167 verbatim
@[simp] theorem positiveDilation_forward_endpoint
    (c : ℝ) (hc : 0 < c) (x : E) :
    (positiveDilation c hc).forward 1 x = c • x := by
  simp [positiveDilation]


-- @@ L169-172 verbatim
@[simp] theorem positiveDilation_inverse_endpoint
    (c : ℝ) (hc : 0 < c) (x : E) :
    (positiveDilation c hc).inverse 1 x = c⁻¹ • x := by
  simp [positiveDilation]


-- @@ L174-174 verbatim
end SmoothAmbientIsotopy


-- @@ L176-176 verbatim
end Submission
