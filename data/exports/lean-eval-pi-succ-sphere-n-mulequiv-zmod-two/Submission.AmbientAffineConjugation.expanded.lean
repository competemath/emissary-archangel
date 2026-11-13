import Mathlib
import Submission.AmbientLocalizedRotation


-- @@ L4-11 verbatim
/-!
# Affine conjugation of ambient isotopies

The explicit local rotation is initially centered at the origin.  Conjugating
an ambient isotopy by a fixed affine diffeomorphism moves its support to an
arbitrary translated linear chart.  This is the positioning operation needed
to apply local normalization moves independently in disjoint neighborhoods.
-/


-- @@ L13-13 verbatim
set_option autoImplicit false


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function

-- @@ L18-18 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L20-20 verbatim
namespace Submission

-- @@ L21-21 verbatim
namespace SmoothAmbientIsotopy


-- @@ L23-23 verbatim
variable {n : ℕ}


-- @@ L25-25 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L27-30 verbatim
/-- Forward map obtained by conjugating an ambient move by `x ↦ b + L x`. -/
def affineConjugateForward (A : SmoothAmbientIsotopy n) (L : E ≃L[ℝ] E)
    (b : E) (s : ℝ) (x : E) : E :=
  b + L (A.forward s (L.symm (x - b)))


-- @@ L32-35 verbatim
/-- Inverse map of the affine conjugate. -/
def affineConjugateInverse (A : SmoothAmbientIsotopy n) (L : E ≃L[ℝ] E)
    (b : E) (s : ℝ) (x : E) : E :=
  b + L (A.inverse s (L.symm (x - b)))


-- @@ L37-46 verbatim
theorem contDiff_affineConjugateForward (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) :
    ContDiff ℝ ∞
      (fun p : ℝ × E => affineConjugateForward A L b p.1 p.2) := by
  have hinner : ContDiff ℝ ∞ (fun p : ℝ × E => L.symm (p.2 - b)) :=
    L.symm.contDiff.comp (contDiff_snd.sub contDiff_const)
  have hmove : ContDiff ℝ ∞
      (fun p : ℝ × E => A.forward p.1 (L.symm (p.2 - b))) :=
    A.forward_smooth.comp (contDiff_fst.prodMk hinner)
  exact contDiff_const.add (L.contDiff.comp hmove)


-- @@ L48-57 verbatim
theorem contDiff_affineConjugateInverse (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) :
    ContDiff ℝ ∞
      (fun p : ℝ × E => affineConjugateInverse A L b p.1 p.2) := by
  have hinner : ContDiff ℝ ∞ (fun p : ℝ × E => L.symm (p.2 - b)) :=
    L.symm.contDiff.comp (contDiff_snd.sub contDiff_const)
  have hmove : ContDiff ℝ ∞
      (fun p : ℝ × E => A.inverse p.1 (L.symm (p.2 - b))) :=
    A.inverse_smooth.comp (contDiff_fst.prodMk hinner)
  exact contDiff_const.add (L.contDiff.comp hmove)


-- @@ L59-68 verbatim
theorem affineConjugate_leftInverse (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    LeftInverse (affineConjugateInverse A L b s)
      (affineConjugateForward A L b s) := by
  intro x
  change b + L (A.inverse s
    (L.symm (b + L (A.forward s (L.symm (x - b))) - b))) = x
  rw [add_sub_cancel_left, L.symm_apply_apply, A.left_inv s hs,
    L.apply_symm_apply]
  abel


-- @@ L70-79 verbatim
theorem affineConjugate_rightInverse (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    RightInverse (affineConjugateInverse A L b s)
      (affineConjugateForward A L b s) := by
  intro x
  change b + L (A.forward s
    (L.symm (b + L (A.inverse s (L.symm (x - b))) - b))) = x
  rw [add_sub_cancel_left, L.symm_apply_apply, A.right_inv s hs,
    L.apply_symm_apply]
  abel


-- @@ L81-123 verbatim
/-- Conjugation by an arbitrary continuous linear equivalence and translation
preserves the full smooth ambient-isotopy structure. -/
def conjugateAffine (A : SmoothAmbientIsotopy n) (L : E ≃L[ℝ] E) (b : E) :
    SmoothAmbientIsotopy n where
  forward := affineConjugateForward A L b
  inverse := affineConjugateInverse A L b
  forward_smooth := contDiff_affineConjugateForward A L b
  inverse_smooth := contDiff_affineConjugateInverse A L b
  forward_zero := by
    funext x
    simp [affineConjugateForward, A.forward_zero]
  left_inv := affineConjugate_leftInverse A L b
  right_inv := affineConjugate_rightInverse A L b
  inverse_fderiv_surjective := by
    intro s hs x
    let f : E → E := affineConjugateForward A L b s
    let g : E → E := affineConjugateInverse A L b s
    have hf : ContDiff ℝ ∞ f := by
      exact (contDiff_affineConjugateForward A L b).comp
        (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ ∞ g := by
      exact (contDiff_affineConjugateInverse A L b).comp
        (contDiff_const.prodMk contDiff_id)
    let y : E := g x
    have hfy : f y = x := affineConjugate_rightInverse A L b s hs x
    have hgf : (fun z => g (f z)) = id := by
      funext z
      exact affineConjugate_leftInverse A L b s hs z
    have hcomp : HasFDerivAt (fun z => g (f z))
        ((fderiv ℝ g (f y)).comp (fderiv ℝ f y)) y :=
      ((hg.differentiable (by simp) (f y)).hasFDerivAt.comp y
        (hf.differentiable (by simp) y).hasFDerivAt)
    rw [hgf] at hcomp
    have hderiv0 : (fderiv ℝ g (f y)).comp (fderiv ℝ f y) =
        ContinuousLinearMap.id ℝ E :=
      hcomp.fderiv.symm.trans (hasFDerivAt_id y).fderiv
    have hderiv : (fderiv ℝ g x).comp (fderiv ℝ f y) =
        ContinuousLinearMap.id ℝ E := by
      rwa [hfy] at hderiv0
    intro z
    refine ⟨fderiv ℝ f y z, ?_⟩
    have hz := congrArg (fun M : E →L[ℝ] E => M z) hderiv
    simpa [ContinuousLinearMap.comp_apply] using hz


-- @@ L125-129 verbatim
@[simp] theorem conjugateAffine_forward (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) (s : ℝ) (x : E) :
    (A.conjugateAffine L b).forward s x =
      b + L (A.forward s (L.symm (x - b))) :=
  rfl


-- @@ L131-135 verbatim
@[simp] theorem conjugateAffine_inverse (A : SmoothAmbientIsotopy n)
    (L : E ≃L[ℝ] E) (b : E) (s : ℝ) (x : E) :
    (A.conjugateAffine L b).inverse s x =
      b + L (A.inverse s (L.symm (x - b))) :=
  rfl


-- @@ L137-145 verbatim
/-- Affine conjugation transports the relative fixed set by the same affine
chart. -/
theorem FixedOn.conjugateAffine {A : SmoothAmbientIsotopy n} {K : Set E}
    (hA : A.FixedOn K) (L : E ≃L[ℝ] E) (b : E) :
    (A.conjugateAffine L b).FixedOn
      {x | L.symm (x - b) ∈ K} := by
  intro s hs x hx
  rw [conjugateAffine_forward, hA s hs _ hx]
  simp


-- @@ L147-147 verbatim
/-! ## Positioned local rotations -/


-- @@ L149-149 verbatim
variable {m : ℕ}


-- @@ L151-151 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L153-160 verbatim
/-- The local squared-radius function scales quadratically. -/
theorem localRadialSq_smul (r : ℝ) (x : E₂) :
    localRadialSq (r • x) = r ^ 2 * localRadialSq x := by
  unfold localRadialSq
  simp only [PiLp.smul_apply, smul_eq_mul]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  ring


-- @@ L162-165 verbatim
/-- Scalar dilation by a nonzero real number as a continuous linear
equivalence. -/
def dilationCLE (r : ℝ) (hr : r ≠ 0) : E₂ ≃L[ℝ] E₂ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)


-- @@ L167-171 verbatim
@[simp] theorem dilationCLE_apply (r : ℝ) (hr : r ≠ 0) (x : E₂) :
    dilationCLE r hr x = r • x := by
  rw [dilationCLE, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def]
  have hval : (↑(Units.mk0 r hr) : ℝ) = r := rfl
  rw [hval]


-- @@ L173-180 verbatim
@[simp] theorem dilationCLE_symm_apply (r : ℝ) (hr : r ≠ 0) (x : E₂) :
    (dilationCLE r hr).symm x = r⁻¹ • x := by
  rw [dilationCLE]
  change (ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)⁻¹) x = r⁻¹ • x
  rw [ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def,
    Units.val_inv_eq_inv_val]
  have hval : (↑(Units.mk0 r hr) : ℝ) = r := rfl
  rw [hval]


-- @@ L182-186 verbatim
/-- The explicit local plane rotation, transported to the affine chart
`x = b + L u`. -/
def affineLocalizedPlaneRotation (θ : ℝ) (L : E₂ ≃L[ℝ] E₂) (b : E₂) :
    SmoothAmbientIsotopy (m + 1) :=
  (localizedPlaneRotation (m := m) θ).conjugateAffine L b


-- @@ L188-194 verbatim
/-- The positioned move fixes every point whose affine-chart coordinate lies
outside the squared-radius-two support ball. -/
theorem affineLocalizedPlaneRotation_fixedOn (θ : ℝ)
    (L : E₂ ≃L[ℝ] E₂) (b : E₂) :
    (affineLocalizedPlaneRotation (m := m) θ L b).FixedOn
      {x | 2 ≤ localRadialSq (L.symm (x - b))} := by
  exact (localizedPlaneRotation_fixedOn (m := m) θ).conjugateAffine L b


-- @@ L196-204 verbatim
/-- On the transported inner ball, the endpoint is the corresponding affine
conjugate of the full plane rotation. -/
theorem affineLocalizedPlaneRotation_endpoint_of_le_one (θ : ℝ)
    (L : E₂ ≃L[ℝ] E₂) (b : E₂) {x : E₂}
    (hx : localRadialSq (L.symm (x - b)) ≤ 1) :
    (affineLocalizedPlaneRotation (m := m) θ L b).forward 1 x =
      b + L (SO2FrameGauge.rotate θ (L.symm (x - b))) := by
  rw [affineLocalizedPlaneRotation, conjugateAffine_forward,
    localizedPlaneRotation_endpoint_of_le_one θ hx]


-- @@ L206-210 verbatim
/-- A local rotation supported near the Euclidean ball of radius `r` centered
at `b`. -/
def ballLocalizedPlaneRotation (θ r : ℝ) (hr : 0 < r) (b : E₂) :
    SmoothAmbientIsotopy (m + 1) :=
  affineLocalizedPlaneRotation θ (dilationCLE r hr.ne') b


-- @@ L212-229 verbatim
/-- The ball-positioned rotation is stationary outside squared radius
`2 * r²`. -/
theorem ballLocalizedPlaneRotation_fixedOn (θ r : ℝ) (hr : 0 < r)
    (b : E₂) :
    (ballLocalizedPlaneRotation (m := m) θ r hr b).FixedOn
      {x | 2 * r ^ 2 ≤ localRadialSq (x - b)} := by
  apply (affineLocalizedPlaneRotation_fixedOn θ
    (dilationCLE r hr.ne') b).mono
  intro x hx
  change 2 ≤ localRadialSq ((dilationCLE r hr.ne').symm (x - b))
  rw [dilationCLE_symm_apply, localRadialSq_smul]
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hdiv : 2 ≤ localRadialSq (x - b) / r ^ 2 :=
    (le_div_iff₀ hrsq).2 hx
  have hscale : r⁻¹ ^ 2 * localRadialSq (x - b) =
      localRadialSq (x - b) / r ^ 2 := by
    field_simp
  rwa [hscale]


-- @@ L231-247 verbatim
/-- On the ball of radius `r`, the endpoint is the full prescribed affine
rotation. -/
theorem ballLocalizedPlaneRotation_endpoint_of_sq_le (θ r : ℝ) (hr : 0 < r)
    (b : E₂) {x : E₂} (hx : localRadialSq (x - b) ≤ r ^ 2) :
    (ballLocalizedPlaneRotation (m := m) θ r hr b).forward 1 x =
      b + dilationCLE r hr.ne'
        (SO2FrameGauge.rotate θ
          ((dilationCLE r hr.ne').symm (x - b))) := by
  apply affineLocalizedPlaneRotation_endpoint_of_le_one
  rw [dilationCLE_symm_apply, localRadialSq_smul]
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hdiv : localRadialSq (x - b) / r ^ 2 ≤ 1 :=
    (div_le_one hrsq).2 hx
  have hscale : r⁻¹ ^ 2 * localRadialSq (x - b) =
      localRadialSq (x - b) / r ^ 2 := by
    field_simp
  rwa [hscale]


-- @@ L249-249 verbatim
end SmoothAmbientIsotopy

-- @@ L250-250 verbatim
end Submission
