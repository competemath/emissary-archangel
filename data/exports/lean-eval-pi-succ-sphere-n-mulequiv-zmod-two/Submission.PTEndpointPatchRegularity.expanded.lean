import Mathlib
import Submission.PTEndpointRegularSlabAdapter


-- @@ L4-19 verbatim
/-!
# Spatial regularity criterion for the PT endpoint patch

The relative Sard theorem used by `patchSignedCobordism` controls the full
space-time derivative.  Endpoint-ledger stability needs the stronger statement
that every *spatial* slice derivative is onto.  This file separates those two
conditions without hiding the remaining analytic input.

The map on the slice with ramp parameter `s` is

`(1 + s * κ(x)) • g(x) - (s * P(x)) • y`.

The main theorem proves that pointwise surjectivity of this explicit family
for `s ∈ [0,1]` supplies the exact `regularSlab` field consumed by the Cassini
endpoint contract.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
open Set Function

-- @@ L28-28 verbatim
open scoped Topology RealInnerProductSpace ContDiff


-- @@ L30-30 verbatim
variable {n : ℕ}


-- @@ L32-32 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L33-33 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L35-35 verbatim
/-! ## A quantitative perturbation lemma -/


-- @@ L37-66 verbatim
/-- A surjective continuous linear map stays surjective after a perturbation
whose composition with one fixed right inverse has norm less than one.  This
is the precise Neumann-series estimate needed after the rank-one formula
below. -/
theorem surjective_add_of_norm_comp_rightInverse_lt_one
    (L Q : E →L[ℝ] F) (hL : Surjective L)
    (hsmall : ‖Q.comp
      (ContinuousLinearMap.HasRightInverse.rightInverse
        (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
          hL))‖ < 1) :
    Surjective (L + Q) := by
  let hR : L.HasRightInverse :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hL
  let R : F →L[ℝ] E := hR.rightInverse
  let A : F →L[ℝ] F := -(Q.comp R)
  have hA : ‖A‖ < 1 := by
    simpa [A, R, hR, norm_neg] using hsmall
  have hunit : IsUnit (1 - A) := isUnit_one_sub_of_norm_lt_one hA
  let U : (F →L[ℝ] F)ˣ := IsUnit.unit hunit
  intro z
  refine ⟨R ((↑(U⁻¹) : F →L[ℝ] F) z), ?_⟩
  have hLR : Function.RightInverse R L := hR.rightInverse_rightInverse
  have hU : (↑U : F →L[ℝ] F) = 1 - A := IsUnit.unit_spec hunit
  have hcomp : (L + Q).comp R = (↑U : F →L[ℝ] F) := by
    ext w
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      hLR w, hU]
    simp [A]
  rw [← ContinuousLinearMap.comp_apply, hcomp]
  rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]


-- @@ L68-95 verbatim
/-- Surjective continuous linear maps between the finite-dimensional spaces
used here form an open subset of the operator-norm space.  We keep this local
lemma explicit because the endpoint compactness argument below needs the
closedness of the complementary bad-derivative locus. -/
theorem isOpen_surjective_continuousLinearMap :
    IsOpen {L : E →L[ℝ] F | Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L hL
  let R : F →L[ℝ] E :=
    ContinuousLinearMap.HasRightInverse.rightInverse
      (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
        hL)
  let q : (E →L[ℝ] F) → E →L[ℝ] F := fun M => M - L
  have hc : Continuous (fun M : E →L[ℝ] F => ‖(q M).comp R‖) :=
    ((continuous_id.sub continuous_const).clm_comp continuous_const).norm
  have hlim0 : Filter.Tendsto
      (fun M : E →L[ℝ] F => ‖(q M).comp R‖) (𝓝 L)
        (𝓝 ‖(q L).comp R‖) :=
    hc.continuousAt
  have hlim : Filter.Tendsto
      (fun M : E →L[ℝ] F => ‖(q M).comp R‖) (𝓝 L) (𝓝 0) := by
    simpa [q] using hlim0
  have hsmall : ∀ᶠ M in 𝓝 L, ‖(q M).comp R‖ < 1 :=
    hlim.eventually_lt_const zero_lt_one
  filter_upwards [hsmall] with M hM
  have hsurj := surjective_add_of_norm_comp_rightInverse_lt_one
    L (q M) hL (by simpa [R] using hM)
  simpa [q] using hsurj


-- @@ L97-122 verbatim
/-- Surjectivity of the derivative is open around a regular point of a smooth
map.  The proof is quantitative: freeze one right inverse at the base point
and apply the preceding Neumann estimate to the varying derivative. -/
theorem eventually_surjective_fderiv_of_surjective
    (g : E → F) (hg : ContDiff ℝ ∞ g) {x : E}
    (hx : Surjective (fderiv ℝ g x)) :
    ∀ᶠ z in 𝓝 x, Surjective (fderiv ℝ g z) := by
  let L : E →L[ℝ] F := fderiv ℝ g x
  let R : F →L[ℝ] E :=
    ContinuousLinearMap.HasRightInverse.rightInverse
      (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
        hx)
  let q : E → E →L[ℝ] F := fun z => fderiv ℝ g z - L
  have hq : Continuous q :=
    (hg.continuous_fderiv (by simp)).sub continuous_const
  have hc : Continuous (fun z => (q z).comp R) :=
    hq.clm_comp continuous_const
  have hlim : Filter.Tendsto (fun z => ‖(q z).comp R‖) (𝓝 x) (𝓝 0) := by
    apply hc.norm.tendsto'
    simp [q, L]
  have hsmall : ∀ᶠ z in 𝓝 x, ‖(q z).comp R‖ < 1 :=
    hlim.eventually_lt_const zero_lt_one
  filter_upwards [hsmall] with z hz
  have hsurj := surjective_add_of_norm_comp_rightInverse_lt_one
    L (q z) hx (by simpa [R, L] using hz)
  simpa [q, L] using hsurj


-- @@ L124-148 verbatim
/-- On any prescribed compact set, the derivative of a framed-level defining
map is surjective throughout a uniform small-value neighborhood of zero.  No
special Cassini calculation is needed for this part: compactness upgrades the
pointwise regularity axiom of `FramedLevelSet` to one common target radius. -/
theorem FramedLevelSet.exists_regularValueRadiusOnCompact
    (X : FramedLevelSet n) {K : Set E} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ‖X.g x‖ < ε →
      Surjective (fderiv ℝ X.g x) := by
  let U : Set E := {x | Surjective (fderiv ℝ X.g x)}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact eventually_surjective_fderiv_of_surjective X.g X.smooth hx
  have hC : IsCompact (K \ U) := hK.diff hU
  have hpos : ∀ x ∈ K \ U, 0 < ‖X.g x‖ := by
    intro x hx
    rw [norm_pos_iff]
    intro hg
    exact hx.2 (X.regular x hg)
  obtain ⟨ε, hε, hbound⟩ :=
    hC.exists_forall_le' X.smooth.continuous.norm.continuousOn hpos
  refine ⟨ε, hε, ?_⟩
  intro x hxK hxsmall
  by_contra hnot
  exact (not_lt_of_ge (hbound x ⟨hxK, hnot⟩)) hxsmall


-- @@ L150-150 verbatim
namespace FiberSign.PTCutoff


-- @@ L152-152 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X) (κ : PTCutoff S)

-- @@ L153-153 verbatim
variable (P : EndpointPatchLocalizer S κ)


-- @@ L155-157 verbatim
/-- The literal spatial member of the endpoint-patch family. -/
def patchSliceMap (y : F) (s : ℝ) (x : E) : F :=
  (1 + s * κ x) • X.g x - (s * P x) • y


-- @@ L159-162 verbatim
lemma contDiff_patchSliceMap (y : F) (s : ℝ) :
    ContDiff ℝ ∞ (patchSliceMap S κ P y s) := by
  exact (contDiff_const.add (contDiff_const.mul κ.smooth)).smul X.smooth |>.sub
    ((contDiff_const.mul P.smooth).smul contDiff_const)


-- @@ L164-177 verbatim
/-- Joint continuity of the patched value in the target, slice parameter,
and spatial point. -/
theorem continuous_patchSliceMap :
    Continuous (fun q : F × (ℝ × E) =>
      patchSliceMap S κ P q.1 q.2.1 q.2.2) := by
  have hκ : Continuous (fun q : F × (ℝ × E) => κ q.2.2) :=
    κ.smooth.continuous.comp (continuous_snd.comp continuous_snd)
  have hP : Continuous (fun q : F × (ℝ × E) => P q.2.2) :=
    P.smooth.continuous.comp (continuous_snd.comp continuous_snd)
  have hg : Continuous (fun q : F × (ℝ × E) => X.g q.2.2) :=
    X.smooth.continuous.comp (continuous_snd.comp continuous_snd)
  exact
    (continuous_const.add ((continuous_fst.comp continuous_snd).mul hκ)).smul hg
      |>.sub (((continuous_fst.comp continuous_snd).mul hP).smul continuous_fst)


-- @@ L179-179 verbatim
/-! ## Pointwise first-jet formula -/


-- @@ L181-230 verbatim
/-- The derivative of the endpoint patch is the old derivative, multiplied by
the positive slice scale, plus two rank-one terms.  This is the useful form
for quantitative openness of surjectivity: all new terms have image in the
line generated by either `X.g x` or the small target `y`. -/
theorem fderiv_patchSliceMap_apply (y : F) (s : ℝ) (x h : E) :
    fderiv ℝ (patchSliceMap S κ P y s) x h =
      (1 + s * κ x) • fderiv ℝ X.g x h +
        (s * fderiv ℝ (fun z : E => κ z) x h) • X.g x -
          (s * fderiv ℝ (fun z : E => P z) x h) • y := by
  let a : E → ℝ := fun z => 1 + s * κ z
  let b : E → ℝ := fun z => s * P z
  have ha : DifferentiableAt ℝ a x :=
    (contDiff_const.add (contDiff_const.mul κ.smooth)).differentiable
      infty_ne_zero |>.differentiableAt
  have hb : DifferentiableAt ℝ b x :=
    (contDiff_const.mul P.smooth).differentiable
      infty_ne_zero |>.differentiableAt
  have hg : DifferentiableAt ℝ X.g x :=
    X.smooth.differentiable infty_ne_zero |>.differentiableAt
  have hy : DifferentiableAt ℝ (fun _z : E => y) x :=
    differentiableAt_const (c := y)
  have hleft : DifferentiableAt ℝ (fun z => a z • X.g z) x := ha.smul hg
  have hright : DifferentiableAt ℝ (fun z => b z • y) x := hb.smul hy
  have hfun : patchSliceMap S κ P y s =
      fun z => a z • X.g z - b z • y := by
    funext z
    rfl
  rw [hfun, fderiv_fun_sub hleft hright,
    fderiv_fun_smul ha hg, fderiv_fun_smul hb hy,
    fderiv_const_apply]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.zero_apply, smul_zero, zero_add]
  dsimp only [a, b]
  change
    (1 + s * κ x) • fderiv ℝ X.g x h +
          (fderiv ℝ (fun z : E => 1 + s * κ z) x h) • X.g x -
        (fderiv ℝ (fun z : E => s * P z) x h) • y = _
  have hκ : DifferentiableAt ℝ (fun z : E => κ z) x :=
    κ.smooth.differentiable infty_ne_zero |>.differentiableAt
  have hP : DifferentiableAt ℝ (fun z : E => P z) x :=
    P.smooth.differentiable infty_ne_zero |>.differentiableAt
  have hfa : fderiv ℝ (fun z : E => 1 + s * κ z) x =
      s • fderiv ℝ (fun z : E => κ z) x := by
    rw [fderiv_const_add (1 : ℝ), fderiv_const_mul hκ s]
  have hfb : fderiv ℝ (fun z : E => s * P z) x =
      s • fderiv ℝ (fun z : E => P z) x := by
    rw [fderiv_const_mul hP s]
  rw [hfa, hfb]
  simp [smul_apply, smul_eq_mul]


-- @@ L232-236 verbatim
/-- The first-jet formula packaged as a continuously varying operator. -/
def patchSliceDerivative (y : F) (s : ℝ) (x : E) : E →L[ℝ] F :=
  (1 + s * κ x) • fderiv ℝ X.g x +
    (s • fderiv ℝ (fun z : E => κ z) x).smulRight (X.g x) -
      (s • fderiv ℝ (fun z : E => P z) x).smulRight y


-- @@ L238-242 verbatim
theorem patchSliceDerivative_apply (y : F) (s : ℝ) (x h : E) :
    patchSliceDerivative S κ P y s x h =
      fderiv ℝ (patchSliceMap S κ P y s) x h := by
  rw [fderiv_patchSliceMap_apply S κ P y s x h]
  simp [patchSliceDerivative, smul_apply]


-- @@ L244-281 verbatim
/-- Joint continuity in the target, slice parameter, and spatial point of the
whole spatial derivative family. -/
theorem continuous_patchSliceDerivative :
    Continuous (fun q : F × (ℝ × E) =>
      patchSliceDerivative S κ P q.1 q.2.1 q.2.2) := by
  have hDg : Continuous (fun q : F × (ℝ × E) =>
      fderiv ℝ X.g q.2.2) :=
    (X.smooth.continuous_fderiv (by simp)).comp
      (continuous_snd.comp continuous_snd)
  have hDκ : Continuous (fun q : F × (ℝ × E) =>
      q.2.1 • fderiv ℝ (fun z : E => κ z) q.2.2) :=
    (continuous_fst.comp continuous_snd).smul
      ((κ.smooth.continuous_fderiv (by simp)).comp
        (continuous_snd.comp continuous_snd))
  have hDP : Continuous (fun q : F × (ℝ × E) =>
      q.2.1 • fderiv ℝ (fun z : E => P z) q.2.2) :=
    (continuous_fst.comp continuous_snd).smul
      ((P.smooth.continuous_fderiv (by simp)).comp
        (continuous_snd.comp continuous_snd))
  have hg : Continuous (fun q : F × (ℝ × E) => X.g q.2.2) :=
    X.smooth.continuous.comp (continuous_snd.comp continuous_snd)
  have hfirst : Continuous (fun q : F × (ℝ × E) =>
      (1 + q.2.1 * κ q.2.2) • fderiv ℝ X.g q.2.2) := by
    have ha : Continuous (fun q : F × (ℝ × E) =>
        1 + q.2.1 * κ q.2.2) := by
      exact continuous_const.add
        ((continuous_fst.comp continuous_snd).mul
          (κ.smooth.continuous.comp
            (continuous_snd.comp continuous_snd)))
    exact ha.smul hDg
  have hκrank : Continuous (fun q : F × (ℝ × E) =>
      (q.2.1 • fderiv ℝ (fun z : E => κ z) q.2.2).smulRight
        (X.g q.2.2)) :=
    (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp₂ hDκ hg
  have hPrank : Continuous (fun q : F × (ℝ × E) =>
      (q.2.1 • fderiv ℝ (fun z : E => P z) q.2.2).smulRight q.1) :=
    (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp₂ hDP continuous_fst
  exact (hfirst.add hκrank).sub hPrank


-- @@ L283-290 verbatim
/-- The packaged derivative agrees with the literal derivative as an
operator, not merely pointwise. -/
theorem patchSliceDerivative_eq_fderiv (y : F) (s : ℝ) (x : E) :
    patchSliceDerivative S κ P y s x =
      fderiv ℝ (patchSliceMap S κ P y s) x := by
  apply ContinuousLinearMap.ext
  intro h
  exact patchSliceDerivative_apply S κ P y s x h


-- @@ L292-309 verbatim
/-- At a zero of a patch slice, the old defining-map value is itself a scalar
multiple of the target.  The denominator is strictly positive for every
`s ∈ [0,1]`. -/
theorem g_eq_smul_target_of_patchSliceMap_eq_zero
    (y : F) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : E}
    (hx : patchSliceMap S κ P y s x = 0) :
    X.g x = ((1 + s * κ x)⁻¹ * (s * P x)) • y := by
  have hscale : 0 < 1 + s * κ x := by
    have hκ : 0 ≤ κ x := (κ.range x).1
    nlinarith [hs.1]
  have heq : (1 + s * κ x) • X.g x = (s * P x) • y := by
    change (1 + s * κ x) • X.g x - (s * P x) • y = 0 at hx
    exact sub_eq_zero.mp hx
  calc
    X.g x = (1 + s * κ x)⁻¹ • ((1 + s * κ x) • X.g x) := by
      rw [smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]
    _ = (1 + s * κ x)⁻¹ • ((s * P x) • y) := by rw [heq]
    _ = ((1 + s * κ x)⁻¹ * (s * P x)) • y := by rw [smul_smul]


-- @@ L311-339 verbatim
/-- A patch zero can only occur over an old defining-map value no larger than
the target value.  Thus a uniform regular neighborhood of the old zero fiber
immediately contains every zero of all sufficiently small patch targets. -/
theorem norm_g_le_norm_target_of_patchSliceMap_eq_zero
    (y : F) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : E}
    (hx : patchSliceMap S κ P y s x = 0) :
    ‖X.g x‖ ≤ ‖y‖ := by
  let a : ℝ := (1 + s * κ x)⁻¹ * (s * P x)
  have hscale : 1 ≤ 1 + s * κ x := by
    have hκ : 0 ≤ κ x := (κ.range x).1
    nlinarith [hs.1]
  have hscalePos : 0 < 1 + s * κ x := lt_of_lt_of_le zero_lt_one hscale
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (inv_nonneg.mpr hscalePos.le)
      (mul_nonneg hs.1 (EndpointPatchLocalizer.nonneg S κ P x))
  have hnum : s * P x ≤ 1 + s * κ x := by
    have hP1 : P x ≤ 1 := EndpointPatchLocalizer.le_one S κ P x
    have hs1 : s ≤ 1 := hs.2
    have hnum1 : s * P x ≤ 1 := by
      nlinarith [EndpointPatchLocalizer.nonneg S κ P x]
    exact hnum1.trans hscale
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [inv_mul_le_one₀ hscalePos]
    exact hnum
  rw [g_eq_smul_target_of_patchSliceMap_eq_zero S κ P y hs hx,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
  exact mul_le_of_le_one_left (norm_nonneg y) ha1


-- @@ L341-358 verbatim
/-- Every patch zero lies either on the old zero fiber or in the compact
support of the endpoint localizer.  This is the spatial compactness input for
the uniform parameter argument. -/
theorem mem_fiber_union_tsupport_of_patchSliceMap_eq_zero
    (y : F) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : E}
    (hx : patchSliceMap S κ P y s x = 0) :
    x ∈ X.fiber ∪ tsupport (fun z : E => P z) := by
  by_cases hP : x ∈ tsupport (fun z : E => P z)
  · exact Or.inr hP
  · apply Or.inl
    have hP0 : P x = 0 := image_eq_zero_of_notMem_tsupport hP
    have hscale : 0 < 1 + s * κ x := by
      have hκ : 0 ≤ κ x := (κ.range x).1
      nlinarith [hs.1]
    change X.g x = 0
    change (1 + s * κ x) • X.g x - (s * P x) • y = 0 at hx
    rw [hP0] at hx
    simpa using (smul_eq_zero.mp (by simpa using hx)).resolve_left hscale.ne'


-- @@ L360-373 verbatim
/-- On a zero slice the whole perturbation of the scaled old derivative has
rank at most one: its image is contained in the line spanned by `y`. -/
theorem fderiv_patchSliceMap_apply_of_eq_zero
    (y : F) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : E}
    (hx : patchSliceMap S κ P y s x = 0) (h : E) :
    fderiv ℝ (patchSliceMap S κ P y s) x h =
      (1 + s * κ x) • fderiv ℝ X.g x h +
        ((s * fderiv ℝ (fun z : E => κ z) x h) *
            ((1 + s * κ x)⁻¹ * (s * P x)) -
          s * fderiv ℝ (fun z : E => P z) x h) • y := by
  rw [fderiv_patchSliceMap_apply S κ P y s x h,
    g_eq_smul_target_of_patchSliceMap_eq_zero S κ P y hs hx,
    smul_smul]
  module


-- @@ L375-385 verbatim
/-- Restricting the space-time patch at time `t` is exactly the spatial family
at the collar-flat parameter `normRamp t`. -/
lemma sliceMap_patchCobMap (y : F) (t : ℝ) :
    sliceMap (patchCobMap S κ P y) t =
      patchSliceMap S κ P y (normRamp t) := by
  funext x
  change patchCobMap S κ P y (cobSpaceTime x t) = _
  have hspace : cobSpaceTime x t = spaceTime x t := rfl
  rw [hspace]
  simp [patchCobMap, patchBase, patchScale, patchWeight, patchSliceMap,
    vertC_spaceTime, initCLM_spaceTime]


-- @@ L387-392 verbatim
/-- Pointwise spatial regularity of every member of the explicit patch family.
This is the analytic condition absent from the relative Sard construction. -/
def PatchSpatiallyRegular (y : F) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : E,
    patchSliceMap S κ P y s x = 0 →
      Surjective (fderiv ℝ (patchSliceMap S κ P y s) x)


-- @@ L394-423 verbatim
/-- At target value zero the whole family is spatially regular.  This is the
unperturbed base point for the remaining uniform-small-value argument: every
slice is merely a positive scalar multiple of the original defining map. -/
theorem patchSpatiallyRegular_zero :
    PatchSpatiallyRegular S κ P (0 : F) := by
  intro s hs x hx
  have hscale : 0 < 1 + s * κ x := by
    have hκ : 0 ≤ κ x := (κ.range x).1
    nlinarith [hs.1]
  have hg : X.g x = 0 := by
    change (1 + s * κ x) • X.g x - (s * P x) • (0 : F) = 0 at hx
    simp only [smul_zero, sub_zero] at hx
    exact (smul_eq_zero.mp hx).resolve_left hscale.ne'
  have hfun : patchSliceMap S κ P (0 : F) s =
      fun z => (1 + s * κ z) • X.g z := by
    funext z
    simp [patchSliceMap]
  rw [hfun]
  have ha : DifferentiableAt ℝ (fun z : E => 1 + s * κ z) x :=
    (contDiff_const.add (contDiff_const.mul κ.smooth)).differentiable
      infty_ne_zero |>.differentiableAt
  have hgdiff : DifferentiableAt ℝ X.g x :=
    X.smooth.differentiable infty_ne_zero |>.differentiableAt
  rw [fderiv_fun_smul ha hgdiff, hg]
  simp only [ContinuousLinearMap.smulRight_zero, add_zero]
  intro z
  obtain ⟨u, hu⟩ := X.regular x hg ((1 + s * κ x)⁻¹ • z)
  refine ⟨u, ?_⟩
  rw [smul_apply, hu, smul_smul,
    mul_inv_cancel₀ hscale.ne', one_smul]


-- @@ L425-498 verbatim
/-- Spatial regularity persists uniformly for every sufficiently small target
value.  The proof is by compactness of the simultaneous bad-parameter locus:
all patch zeros lie in the old compact fiber or the localizer support, the
value and derivative depend continuously on `(y,s,x)`, and at `y = 0` the
derivative is always onto. -/
theorem exists_patchSpatiallyRegular_radius :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : F, ‖y‖ < ε →
      PatchSpatiallyRegular S κ P y := by
  let K : Set E := X.fiber ∪ tsupport (fun z : E => P z)
  have hK : IsCompact K := by
    exact X.isCompact_fiber.union P.compact_support
  let C : Set (F × (ℝ × E)) :=
    Metric.closedBall (0 : F) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ K)
  have hC : IsCompact C := by
    exact (isCompact_closedBall (0 : F) 1).prod (isCompact_Icc.prod hK)
  let Z : Set (F × (ℝ × E)) := {q |
    patchSliceMap S κ P q.1 q.2.1 q.2.2 = 0}
  have hZ : IsClosed Z := by
    change IsClosed ((fun q : F × (ℝ × E) =>
      patchSliceMap S κ P q.1 q.2.1 q.2.2) ⁻¹' ({0} : Set F))
    exact isClosed_singleton.preimage (continuous_patchSliceMap S κ P)
  let N : Set (F × (ℝ × E)) := {q |
    ¬ Surjective (patchSliceDerivative S κ P q.1 q.2.1 q.2.2)}
  have hNS : IsClosed {L : E →L[ℝ] F | ¬ Surjective L} := by
    simpa only [Set.compl_setOf] using
      (isOpen_surjective_continuousLinearMap (n := n)).isClosed_compl
  have hN : IsClosed N := by
    change IsClosed ((fun q : F × (ℝ × E) =>
      patchSliceDerivative S κ P q.1 q.2.1 q.2.2) ⁻¹'
        {L : E →L[ℝ] F | ¬ Surjective L})
    exact hNS.preimage (continuous_patchSliceDerivative S κ P)
  let B : Set (F × (ℝ × E)) := (C ∩ Z) ∩ N
  have hB : IsCompact B := by
    exact (hC.inter_right hZ).inter_right hN
  have hpos : ∀ q ∈ B, 0 < ‖q.1‖ := by
    intro q hq
    rcases hq with ⟨⟨hqC, hqZ⟩, hqN⟩
    rw [norm_pos_iff]
    intro hy0
    have hs : q.2.1 ∈ Icc (0 : ℝ) 1 := by
      exact hqC.2.1
    have hz : patchSliceMap S κ P (0 : F) q.2.1 q.2.2 = 0 := by
      change patchSliceMap S κ P q.1 q.2.1 q.2.2 = 0 at hqZ
      simpa [hy0] using hqZ
    have hsurj : Surjective
        (fderiv ℝ (patchSliceMap S κ P (0 : F) q.2.1) q.2.2) :=
      patchSpatiallyRegular_zero S κ P q.2.1 hs q.2.2 hz
    have hsurj' : Surjective
        (patchSliceDerivative S κ P q.1 q.2.1 q.2.2) := by
      rw [patchSliceDerivative_eq_fderiv S κ P]
      simpa [hy0] using hsurj
    exact hqN hsurj'
  obtain ⟨ε, hε, hmin⟩ :=
    hB.exists_forall_le' continuous_fst.norm.continuousOn hpos
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro y hy s hs x hx
  by_contra hnot
  have hxK : x ∈ K :=
    mem_fiber_union_tsupport_of_patchSliceMap_eq_zero S κ P y hs hx
  have hyBall : y ∈ Metric.closedBall (0 : F) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hy.le.trans (min_le_right ε 1)
  have hqC : (y, (s, x)) ∈ C := by
    exact ⟨hyBall, hs, hxK⟩
  have hqZ : (y, (s, x)) ∈ Z := by
    exact hx
  have hqN : (y, (s, x)) ∈ N := by
    change ¬ Surjective (patchSliceDerivative S κ P y s x)
    rw [patchSliceDerivative_eq_fderiv S κ P]
    exact hnot
  have hqB : (y, (s, x)) ∈ B := ⟨⟨hqC, hqZ⟩, hqN⟩
  have hlower : ε ≤ ‖y‖ := by
    simpa using hmin (y, (s, x)) hqB
  exact (not_lt_of_ge hlower) (hy.trans_le (min_le_left ε 1))


-- @@ L500-523 verbatim
/-- The pointwise spatial condition supplies a regular slab for the unsigned
endpoint patch cobordism. -/
theorem patchCobMap_regularSlab_of_patchSpatiallyRegular
    (y : F) (hsp : PatchSpatiallyRegular S κ P y) :
    regularSlab (patchCobMap S κ P y) 0 1 := by
  rw [regularSlab]
  intro t ht htcrit
  obtain ⟨v, hvcrit, hvt⟩ := htcrit
  apply hvcrit.2
  let x : E := spacePart v
  have hvrepr : cobSpaceTime x t = v := by
    rw [← hvt]
    exact spaceTime_spacePart v
  have hs : normRamp t ∈ Icc (0 : ℝ) 1 :=
    ⟨normRamp_nonneg t, normRamp_le_one t⟩
  have hz : patchSliceMap S κ P y (normRamp t) x = 0 := by
    have hz' := hvcrit.1
    rw [← hvrepr] at hz'
    change sliceMap (patchCobMap S κ P y) t x = 0 at hz'
    rwa [sliceMap_patchCobMap S κ P y t] at hz'
  have hsurj := hsp (normRamp t) hs x hz
  rw [← hvrepr]
  rw [← fderiv_sliceMap (contDiff_patchCobMap S κ P y) t x]
  rwa [sliceMap_patchCobMap S κ P y t]


-- @@ L525-533 verbatim
/-- Signed wrapper: only the underlying patched defining map matters for
`regularSlab`. -/
theorem patchSignedCobordism_regularSlab_of_patchSpatiallyRegular
    (y : F)
    (hreg : IsRegularValueOn (patchQuotient S κ P)
      (patchTransition S κ P) y)
    (hsp : PatchSpatiallyRegular S κ P y) :
    regularSlab (patchSignedCobordism S κ P y hreg).cobordism.G 0 1 :=
  patchCobMap_regularSlab_of_patchSpatiallyRegular S κ P y hsp


-- @@ L535-542 verbatim
/-- Exact time-parametrized form.  This is equivalent to `regularSlab` and is
occasionally more convenient when an estimate is naturally stated using
`normRamp t` rather than every `s ∈ [0,1]`. -/
def PatchSpatiallyRegularOnRamp (y : F) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : E,
    patchSliceMap S κ P y (normRamp t) x = 0 →
      Surjective
        (fderiv ℝ (patchSliceMap S κ P y (normRamp t)) x)


-- @@ L544-574 verbatim
theorem regularSlab_patchCobMap_iff_patchSpatiallyRegularOnRamp (y : F) :
    regularSlab (patchCobMap S κ P y) 0 1 ↔
      PatchSpatiallyRegularOnRamp S κ P y := by
  constructor
  · intro hreg t ht x hx
    have hslice := hreg.sliceRegular ht
    have hs := hslice (cobSpaceTime x t)
    have hzero : patchCobMap S κ P y (cobSpaceTime x t) = 0 := by
      change sliceMap (patchCobMap S κ P y) t x = 0
      rwa [sliceMap_patchCobMap S κ P y t]
    have hsurj := hs hzero (tcoord_spaceTime x t)
    rw [← fderiv_sliceMap (contDiff_patchCobMap S κ P y) t x] at hsurj
    rwa [sliceMap_patchCobMap S κ P y t] at hsurj
  · intro hsp
    rw [regularSlab]
    intro t ht htcrit
    obtain ⟨v, hvcrit, hvt⟩ := htcrit
    apply hvcrit.2
    let x : E := spacePart v
    have hvrepr : cobSpaceTime x t = v := by
      rw [← hvt]
      exact spaceTime_spacePart v
    have hz : patchSliceMap S κ P y (normRamp t) x = 0 := by
      have hz' := hvcrit.1
      rw [← hvrepr] at hz'
      change sliceMap (patchCobMap S κ P y) t x = 0 at hz'
      rwa [sliceMap_patchCobMap S κ P y t] at hz'
    have hsurj := hsp t ht x hz
    rw [← hvrepr]
    rw [← fderiv_sliceMap (contDiff_patchCobMap S κ P y) t x]
    rwa [sliceMap_patchCobMap S κ P y t]


-- @@ L576-576 verbatim
end FiberSign.PTCutoff


-- @@ L578-578 verbatim
end Submission
