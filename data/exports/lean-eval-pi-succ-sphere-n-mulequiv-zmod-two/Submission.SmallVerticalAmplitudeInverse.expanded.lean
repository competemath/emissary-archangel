import Mathlib
import Submission.MorsePerturb


-- @@ L4-10 verbatim
/-!
# Inverting a small vertical amplitude

The inverse of `v ↦ v + a(v) eₜ` is again a vertical shift.  Under the
slightly stronger bound `2 * a.K < 1`, its amplitude has Lipschitz constant
`2 * a.K`, hence is itself a `SmallVerticalAmplitude`.
-/


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
open Set Function Metric

-- @@ L15-15 verbatim
open scoped RealInnerProductSpace ContDiff Topology Manifold


-- @@ L17-17 verbatim
namespace Submission


-- @@ L19-19 verbatim
variable {n : ℕ}


-- @@ L21-21 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L23-23 verbatim
namespace SmallVerticalAmplitude


-- @@ L25-25 verbatim
variable (a : SmallVerticalAmplitude (n := n))


-- @@ L27-29 verbatim
/-- The scalar amplitude of the inverse vertical shift. -/
def inverseRaw (v : E') : ℝ :=
  -a (a.diffeomorph.symm v)


-- @@ L31-33 verbatim
theorem contDiff_inverseRaw : ContDiff ℝ ∞ a.inverseRaw := by
  change ContDiff ℝ ∞ (fun v => -a.toFun (a.diffeomorph.symm v))
  exact (a.smooth.comp a.diffeomorph.symm.contDiff).neg


-- @@ L35-47 verbatim
theorem inverseRaw_collar_zero (v : E')
    (hv : tcoord v ≤ 1 / 4 ∨ 3 / 4 ≤ tcoord v) :
    a.inverseRaw v = 0 := by
  have ha : a v = 0 := a.toVerticalAmplitude.collar_zero v hv
  have hfix : a.diffeomorph v = v := by
    rw [a.diffeomorph_apply]
    simp [verticalShift, ha]
  have hinv : a.diffeomorph.symm v = v := by
    calc
      a.diffeomorph.symm v =
          a.diffeomorph.symm (a.diffeomorph v) := congrArg _ hfix.symm
      _ = v := a.diffeomorph.symm_apply_apply v
  simp [inverseRaw, hinv, ha]


-- @@ L49-62 verbatim
/-- The inverse diffeomorphism is literally the vertical shift by `inverseRaw`. -/
theorem verticalShift_inverseRaw (v : E') :
    verticalShift a.inverseRaw v = a.diffeomorph.symm v := by
  let x : E' := a.diffeomorph.symm v
  have hx : verticalShift a x = v := by
    change a.diffeomorph x = v
    exact a.diffeomorph.apply_symm_apply v
  calc
    verticalShift a.inverseRaw v = v - a x • timeVec := by
      simp [verticalShift, inverseRaw, x, sub_eq_add_neg]
    _ = x := by
      rw [← hx]
      simp only [verticalShift]
      abel


-- @@ L64-93 verbatim
/-- With `2K < 1`, the forward vertical shift is `2`-antilipschitz. -/
theorem antilipschitzWith_two_verticalShift (hsmall : 2 * a.K < 1) :
    AntilipschitzWith 2 (verticalShift a) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x z
  have hsub : x - z =
      (verticalShift a x - verticalShift a z) -
        ((a x - a z) • timeVec) := by
    simp only [verticalShift]
    rw [sub_smul]
    abel
  have htriangle : dist x z ≤
      dist (verticalShift a x) (verticalShift a z) + dist (a x) (a z) := by
    rw [dist_eq_norm, dist_eq_norm, Real.dist_eq, hsub]
    calc
      ‖(verticalShift a x - verticalShift a z) -
          (a x - a z) • timeVec‖ ≤
          ‖verticalShift a x - verticalShift a z‖ +
            ‖(a x - a z) • timeVec‖ := norm_sub_le _ _
      _ = ‖verticalShift a x - verticalShift a z‖ + |a x - a z| := by
        rw [norm_smul, norm_timeVec, mul_one, Real.norm_eq_abs]
  have ha := a.lipschitz.dist_le_mul x z
  have hsmallR : 2 * (a.K : ℝ) < 1 := by
    exact_mod_cast hsmall
  have hKnonneg : 0 ≤ (a.K : ℝ) := a.K.coe_nonneg
  have hdistnonneg : 0 ≤ dist x z := dist_nonneg
  have hprod : 0 ≤ (1 - 2 * (a.K : ℝ)) * dist x z :=
    mul_nonneg (by linarith) hdistnonneg
  norm_num
  nlinarith


-- @@ L95-100 verbatim
theorem lipschitzWith_two_diffeomorph_symm (hsmall : 2 * a.K < 1) :
    LipschitzWith 2 a.diffeomorph.symm := by
  apply (a.antilipschitzWith_two_verticalShift hsmall).to_rightInverse
  intro v
  change a.diffeomorph (a.diffeomorph.symm v) = v
  exact a.diffeomorph.apply_symm_apply v


-- @@ L102-117 verbatim
theorem lipschitzWith_inverseRaw (hsmall : 2 * a.K < 1) :
    LipschitzWith (2 * a.K) a.inverseRaw := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x z
  have ha := a.lipschitz.dist_le_mul
    (a.diffeomorph.symm x) (a.diffeomorph.symm z)
  have hinv := (a.lipschitzWith_two_diffeomorph_symm hsmall).dist_le_mul x z
  rw [inverseRaw, inverseRaw, dist_neg_neg]
  calc
    dist (a (a.diffeomorph.symm x)) (a (a.diffeomorph.symm z)) ≤
        (a.K : ℝ) * dist (a.diffeomorph.symm x) (a.diffeomorph.symm z) := ha
    _ ≤ (a.K : ℝ) * (2 * dist x z) :=
      mul_le_mul_of_nonneg_left hinv a.K.coe_nonneg
    _ = ((2 * a.K : NNReal) : ℝ) * dist x z := by
      push_cast
      ring


-- @@ L119-133 verbatim
/-- The inverse shift, packaged as a small vertical amplitude. -/
def inverse (hsmall : 2 * a.K < 1) : SmallVerticalAmplitude (n := n) := by
  let base : VerticalAmplitude (n := n) :=
    VerticalAmplitude.ofNormFDerivLtOne a.inverseRaw a.contDiff_inverseRaw
      a.inverseRaw_collar_zero (fun v => by
        have hderiv : ‖fderiv ℝ a.inverseRaw v‖ ≤ ((2 * a.K : NNReal) : ℝ) :=
          norm_fderiv_le_of_lipschitz ℝ (a.lipschitzWith_inverseRaw hsmall)
        have hsmallR : ((2 * a.K : NNReal) : ℝ) < 1 := by
          exact_mod_cast hsmall
        exact hderiv.trans_lt hsmallR)
  exact {
    toVerticalAmplitude := base
    K := 2 * a.K
    K_lt_one := hsmall
    lipschitz := a.lipschitzWith_inverseRaw hsmall }


-- @@ L135-136 verbatim
@[simp] theorem inverse_apply (hsmall : 2 * a.K < 1) (v : E') :
    a.inverse hsmall v = a.inverseRaw v := rfl


-- @@ L138-146 verbatim
/-- The diffeomorphism packaged from the inverse amplitude is the inverse
diffeomorphism of the original amplitude. -/
theorem inverse_diffeomorph (hsmall : 2 * a.K < 1) :
    (a.inverse hsmall).diffeomorph = a.diffeomorph.symm := by
  apply Diffeomorph.ext
  intro v
  rw [diffeomorph_apply]
  change verticalShift a.inverseRaw v = a.diffeomorph.symm v
  exact a.verticalShift_inverseRaw v


-- @@ L148-148 verbatim
end SmallVerticalAmplitude


-- @@ L150-150 verbatim
end Submission
