import Mathlib
import Submission.AmbientNormalizationPrimitive


-- @@ L4-21 verbatim
/-!
# Ambient isotopies from small displacement fields

A normal-graph presentation is stronger than what is needed to move one
parametrized circle to a nearby one.  This file records the weaker and more
flexible primitive.  If a smooth ambient displacement field is globally
Lipschitz with constant strictly below one, then

`x ↦ x + normRamp s • d x`

is a global smooth ambient isotopy.  The inverse is the canonical Banach fixed
point of `z ↦ y - normRamp s • d z`.  A parameterized implicit-function
argument proves joint smoothness of that inverse.

This is the analytic engine used by the finite small-step extension of an
embedded-circle track.  In particular it does not require a target curve to
be written as a normal graph or to retain the source phase coordinate.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false

-- @@ L24-24 verbatim
set_option maxHeartbeats 500000


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open Set Function Metric

-- @@ L29-29 verbatim
open scoped Topology ContDiff NNReal RealInnerProductSpace


-- @@ L31-31 verbatim
namespace Submission


-- @@ L33-33 verbatim
variable {n : ℕ}


-- @@ L35-35 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L37-46 verbatim
/-- A globally small smooth displacement field.  No support condition is
needed for invertibility; orbit-normalization callers will separately arrange
compact support and vanishing on the relative obstacle set. -/
structure SmallAmbientDisplacement (n : ℕ) where
  field : EuclideanSpace ℝ (Fin (n + 1)) →
    EuclideanSpace ℝ (Fin (n + 1))
  smooth : ContDiff ℝ ∞ field
  K : ℝ≥0
  K_lt_one : K < 1
  lipschitz : LipschitzWith K field


-- @@ L48-48 verbatim
namespace SmallAmbientDisplacement


-- @@ L50-50 verbatim
variable (D : SmallAmbientDisplacement n)


-- @@ L52-54 verbatim
/-- Time-scaled displacement. -/
def perturbation (s : ℝ) (x : E) : E :=
  normRamp s • D.field x


-- @@ L56-58 verbatim
/-- The forward ambient map. -/
def forward (s : ℝ) (x : E) : E :=
  x + D.perturbation s x


-- @@ L60-63 verbatim
theorem contDiff_joint_perturbation :
    ContDiff ℝ ∞ (fun p : ℝ × E => D.perturbation p.1 p.2) := by
  exact (contDiff_normRamp.comp contDiff_fst).smul
    (D.smooth.comp contDiff_snd)


-- @@ L65-67 verbatim
theorem contDiff_joint_forward :
    ContDiff ℝ ∞ (fun p : ℝ × E => D.forward p.1 p.2) := by
  exact contDiff_snd.add D.contDiff_joint_perturbation


-- @@ L69-85 verbatim
theorem perturbation_lipschitz (s : ℝ) :
    LipschitzWith D.K (D.perturbation s) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hD := D.lipschitz.dist_le_mul x y
  rw [perturbation, perturbation, dist_eq_norm, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (normRamp_nonneg s)]
  calc
    normRamp s * ‖D.field x - D.field y‖ =
        normRamp s * dist (D.field x) (D.field y) := by
      rw [dist_eq_norm]
    _ ≤ normRamp s * ((D.K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left hD (normRamp_nonneg s)
    _ ≤ 1 * ((D.K : ℝ) * dist x y) := by
      exact mul_le_mul_of_nonneg_right (normRamp_le_one s)
        (mul_nonneg D.K.coe_nonneg dist_nonneg)
    _ = (D.K : ℝ) * dist x y := one_mul _


-- @@ L87-89 verbatim
/-- Fixed-point operator whose fixed point is the inverse image of `y`. -/
def inverseOperator (s : ℝ) (y x : E) : E :=
  y - D.perturbation s x


-- @@ L91-98 verbatim
theorem inverseOperator_contracting (s : ℝ) (y : E) :
    ContractingWith D.K (D.inverseOperator s y) := by
  refine ⟨D.K_lt_one, ?_⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro x z
  simpa [inverseOperator, dist_eq_norm, sub_sub_sub_cancel_left,
    norm_neg, norm_sub_rev] using
    (D.perturbation_lipschitz s).dist_le_mul z x


-- @@ L100-103 verbatim
/-- Explicit inverse, chosen as the Banach fixed point. -/
def inverse (s : ℝ) (y : E) : E :=
  (D.inverseOperator_contracting s y).fixedPoint
    (D.inverseOperator s y)


-- @@ L105-107 verbatim
theorem inverse_fixed (s : ℝ) (y : E) :
    D.inverseOperator s y (D.inverse s y) = D.inverse s y :=
  (D.inverseOperator_contracting s y).fixedPoint_isFixedPt


-- @@ L109-114 verbatim
theorem forward_inverse (s : ℝ) (y : E) :
    D.forward s (D.inverse s y) = y := by
  have h := D.inverse_fixed s y
  simp only [inverseOperator] at h
  rw [forward]
  exact (sub_eq_iff_eq_add.mp h).symm


-- @@ L116-121 verbatim
theorem inverse_forward (s : ℝ) (x : E) :
    D.inverse s (D.forward s x) = x := by
  symm
  exact (D.inverseOperator_contracting s (D.forward s x)).fixedPoint_unique (by
    change x + D.perturbation s x - D.perturbation s x = x
    abel)


-- @@ L123-126 verbatim
theorem forward_bijective (s : ℝ) : Bijective (D.forward s) :=
  ⟨fun x y hxy => by
      rw [← D.inverse_forward s x, ← D.inverse_forward s y, hxy],
    fun y => ⟨D.inverse s y, D.forward_inverse s y⟩⟩


-- @@ L128-131 verbatim
theorem contDiff_perturbation_slice (s : ℝ) :
    ContDiff ℝ ∞ (D.perturbation s) := by
  simpa [Function.comp_def] using D.contDiff_joint_perturbation.comp
    (contDiff_const.prodMk contDiff_id)


-- @@ L133-136 verbatim
theorem contDiff_forward_slice (s : ℝ) :
    ContDiff ℝ ∞ (D.forward s) := by
  simpa [Function.comp_def] using D.contDiff_joint_forward.comp
    (contDiff_const.prodMk contDiff_id)


-- @@ L138-143 verbatim
theorem norm_fderiv_perturbation_lt_one (s : ℝ) (x : E) :
    ‖fderiv ℝ (D.perturbation s) x‖ < 1 := by
  calc
    ‖fderiv ℝ (D.perturbation s) x‖ ≤ (D.K : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ (D.perturbation_lipschitz s)
    _ < 1 := by exact_mod_cast D.K_lt_one


-- @@ L145-151 verbatim
theorem fderiv_forward_eq (s : ℝ) (x : E) :
    fderiv ℝ (D.forward s) x =
      ContinuousLinearMap.id ℝ E + fderiv ℝ (D.perturbation s) x := by
  have hp : DifferentiableAt ℝ (D.perturbation s) x :=
    (D.contDiff_perturbation_slice s).differentiable (by simp) x
  change fderiv ℝ (fun y : E => y + D.perturbation s y) x = _
  exact ((hasFDerivAt_id x).add hp.hasFDerivAt).fderiv


-- @@ L153-161 verbatim
theorem fderiv_forward_bijective (s : ℝ) (x : E) :
    Bijective (fderiv ℝ (D.forward s) x) := by
  let L : E →L[ℝ] E := fderiv ℝ (D.perturbation s) x
  have hL : ‖L‖ < 1 := D.norm_fderiv_perturbation_lt_one s x
  have hu : IsUnit (1 - (-L)) := (Units.oneSub (-L) (by simpa)).isUnit
  rw [D.fderiv_forward_eq]
  change Bijective ((1 : E →L[ℝ] E) + L)
  simpa [sub_neg_eq_add] using
    (ContinuousLinearMap.isUnit_iff_bijective.mp hu)


-- @@ L163-171 verbatim
theorem fderiv_forward_isInvertible (s : ℝ) (x : E) :
    (fderiv ℝ (D.forward s) x).IsInvertible := by
  have hb := D.fderiv_forward_bijective s x
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective
    (fderiv ℝ (D.forward s) x)
    (LinearMap.ker_eq_bot.mpr hb.1)
    (LinearMap.range_eq_top.mpr hb.2)
  refine ⟨e, ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _


-- @@ L173-175 verbatim
/-- Implicit equation for the inverse, with `(time,target)` as parameters. -/
def inverseEquation (q : ((ℝ × E) × E)) : E :=
  D.forward q.1.1 q.2 - q.1.2


-- @@ L177-180 verbatim
theorem contDiff_inverseEquation : ContDiff ℝ ∞ D.inverseEquation := by
  exact (D.contDiff_joint_forward.comp
    ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).sub
      (contDiff_snd.comp contDiff_fst)


-- @@ L182-184 verbatim
/-- The inverse as one jointly parameterized section. -/
def inverseSection (q : ℝ × E) : E :=
  D.inverse q.1 q.2


-- @@ L186-201 verbatim
theorem fderiv_inverseEquation_comp_inr (q : ℝ × E) (z : E) :
    (fderiv ℝ D.inverseEquation (q, z)).comp
        (ContinuousLinearMap.inr ℝ (ℝ × E) E) =
      fderiv ℝ (D.forward q.1) z := by
  have htotal :=
    (D.contDiff_inverseEquation.differentiable (by simp) (q, z)).hasFDerivAt
  have hinc : HasFDerivAt (fun w : E => (q, w))
      (ContinuousLinearMap.inr ℝ (ℝ × E) E) z :=
    (hasFDerivAt_const (x := z) q).prodMk (hasFDerivAt_id z)
  have hcomp := htotal.comp z hinc
  have hslice : fderiv ℝ (fun w : E => D.inverseEquation (q, w)) z =
      fderiv ℝ (D.forward q.1) z := by
    simpa [inverseEquation] using
      (fderiv_sub_const (𝕜 := ℝ) (f := D.forward q.1) (x := z) q.2)
  rw [← hslice]
  exact hcomp.fderiv.symm


-- @@ L203-207 verbatim
theorem inverseEquation_partial_isInvertible (q : ℝ × E) (z : E) :
    ((fderiv ℝ D.inverseEquation (q, z)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × E) E)).IsInvertible := by
  rw [D.fderiv_inverseEquation_comp_inr q z]
  exact D.fderiv_forward_isInvertible q.1 z


-- @@ L209-233 verbatim
/-- The Banach inverse is jointly smooth in time and target. -/
theorem contDiff_inverseSection : ContDiff ℝ ∞ D.inverseSection := by
  rw [contDiff_iff_contDiffAt]
  intro q
  let z : E := D.inverseSection q
  let b : ((ℝ × E) × E) := (q, z)
  let cdf : ContDiffAt ℝ ∞ D.inverseEquation b :=
    D.contDiff_inverseEquation.contDiffAt
  have hi : ((fderiv ℝ D.inverseEquation b).comp
      (ContinuousLinearMap.inr ℝ (ℝ × E) E)).IsInvertible := by
    simpa [b] using D.inverseEquation_partial_isInvertible q z
  let ψ : ℝ × E → E := cdf.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ q := by
    simpa [ψ, b] using cdf.contDiffAt_implicitFunction (by simp) hi
  have hbzero : D.inverseEquation b = 0 := by
    simp [b, z, inverseSection, inverseEquation, D.forward_inverse]
  have heq : D.inverseSection =ᶠ[nhds q] ψ := by
    have himp := cdf.eventually_apply_implicitFunction (by simp) hi
    filter_upwards [himp] with q' hq'
    have hz' : D.inverseEquation (q', ψ q') = 0 := by
      rw [hq', hbzero]
    have hfwd : D.forward q'.1 (ψ q') = q'.2 := sub_eq_zero.mp hz'
    show D.inverse q'.1 q'.2 = ψ q'
    rw [← hfwd, D.inverse_forward]
  exact hψ.congr_of_eventuallyEq heq


-- @@ L235-238 verbatim
theorem contDiff_inverse_slice (s : ℝ) :
    ContDiff ℝ ∞ (D.inverse s) := by
  simpa [inverseSection, Function.comp_def] using
    D.contDiff_inverseSection.comp (contDiff_const.prodMk contDiff_id)


-- @@ L240-267 verbatim
/-- The derivative of the inverse is surjective, obtained by differentiating
`inverse s ∘ forward s = id`. -/
theorem inverse_fderiv_surjective (s : ℝ) (x : E) :
    Surjective (fderiv ℝ (D.inverse s) x) := by
  let f : E → E := D.forward s
  let g : E → E := D.inverse s
  have hf : ContDiff ℝ ∞ f := D.contDiff_forward_slice s
  have hg : ContDiff ℝ ∞ g := D.contDiff_inverse_slice s
  let y : E := g x
  have hfy : f y = x := D.forward_inverse s x
  have hgf : (fun z => g (f z)) = id := by
    funext z
    exact D.inverse_forward s z
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
  have hz := congrArg (fun L : E →L[ℝ] E => L z) hderiv
  simpa [ContinuousLinearMap.comp_apply] using hz


-- @@ L269-272 verbatim
theorem forward_zero : D.forward 0 = id := by
  funext x
  simp [forward, perturbation,
    normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num)]


-- @@ L274-283 verbatim
/-- The resulting genuine smooth ambient isotopy. -/
def toSmoothAmbientIsotopy : SmoothAmbientIsotopy n where
  forward := D.forward
  inverse := D.inverse
  forward_smooth := D.contDiff_joint_forward
  inverse_smooth := D.contDiff_inverseSection
  forward_zero := D.forward_zero
  left_inv := fun s _ x => D.inverse_forward s x
  right_inv := fun s _ x => D.forward_inverse s x
  inverse_fderiv_surjective := fun s _ x => D.inverse_fderiv_surjective s x


-- @@ L285-286 verbatim
@[simp] theorem toSmoothAmbientIsotopy_forward (s : ℝ) (x : E) :
    D.toSmoothAmbientIsotopy.forward s x = D.forward s x := rfl


-- @@ L288-289 verbatim
@[simp] theorem toSmoothAmbientIsotopy_inverse (s : ℝ) (x : E) :
    D.toSmoothAmbientIsotopy.inverse s x = D.inverse s x := rfl


-- @@ L291-295 verbatim
/-- Endpoint action is the prescribed displacement. -/
theorem toSmoothAmbientIsotopy_forward_one (x : E) :
    D.toSmoothAmbientIsotopy.forward 1 x = x + D.field x := by
  simp [toSmoothAmbientIsotopy, forward, perturbation,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num)]


-- @@ L297-302 verbatim
/-- Vanishing of the field on a set gives literal relative fixedness. -/
theorem fixedOn_of_field_eq_zero {K : Set E}
    (hzero : ∀ x ∈ K, D.field x = 0) :
    D.toSmoothAmbientIsotopy.FixedOn K := by
  intro s hs x hx
  simp [toSmoothAmbientIsotopy, forward, perturbation, hzero x hx]


-- @@ L304-346 verbatim
/-- Every compactly supported smooth displacement can be uniformly scaled
into the small regime.  Downstream finite-subdivision arguments apply this to
a divided difference, so the scale is the actual time-step length. -/
theorem exists_scaled (raw : E → E) (hraw : ContDiff ℝ ∞ raw)
    (hsupp : HasCompactSupport raw) :
    ∃ ε : ℝ, ε > 0 ∧ ∃ D : SmallAmbientDisplacement n,
      D.field = fun x => ε • raw x := by
  obtain ⟨K, hK⟩ :=
    hraw.lipschitzWith_of_hasCompactSupport hsupp (by simp)
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hK0 : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
  have hε : 0 < ε := one_div_pos.mpr hden
  have hεK : ε * (K : ℝ) < 1 := by
    change (1 / (2 * ((K : ℝ) + 1))) * (K : ℝ) < 1
    rw [one_div, inv_mul_eq_div]
    exact (div_lt_one hden).2 (by linarith)
  let κ : ℝ≥0 := ⟨ε * (K : ℝ), mul_nonneg hε.le hK0⟩
  have hκ : κ < 1 := by exact_mod_cast hεK
  let scaled : E → E := fun x => ε • raw x
  have hscaled : ContDiff ℝ ∞ scaled := hraw.const_smul ε
  have hscaledLip : LipschitzWith κ scaled := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x z
    have h := hK.dist_le_mul x z
    change dist (ε • raw x) (ε • raw z) ≤ (κ : ℝ) * dist x z
    rw [dist_eq_norm, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hε]
    calc
      ε * ‖raw x - raw z‖ = ε * dist (raw x) (raw z) := by
        rw [dist_eq_norm]
      _ ≤ ε * ((K : ℝ) * dist x z) :=
        mul_le_mul_of_nonneg_left h hε.le
      _ = (κ : ℝ) * dist x z := by
        change ε * ((K : ℝ) * dist x z) =
          (ε * (K : ℝ)) * dist x z
        ring
  refine ⟨ε, hε, {
    field := scaled
    smooth := hscaled
    K := κ
    K_lt_one := hκ
    lipschitz := hscaledLip }, rfl⟩


-- @@ L348-348 verbatim
end SmallAmbientDisplacement


-- @@ L350-350 verbatim
end Submission
