import Mathlib
import Submission.ConcreteConfigurationStraightLineAdmissibilityExistence


-- @@ L4-43 verbatim
/-!
# Sard-regularized interpolation between same-fiber presentations

The straight-line certificate `SameFiberSegmentComparison.Data` demands that
the affine interpolation of two same-fiber defining maps keeps the zero set
literally fixed (no antiparallel values anywhere off the fiber) and that all
interior convex combinations of the endpoint derivatives stay surjective on
the fiber.  Both fields are analytic statements about `Classical.choice`-
opaque maps, and neither is available at the bridge entry.

This file removes both fields.  A signed framed level **cobordism** — the
actual currency of the bridge argument — does not need a fixed zero set: its
interior fiber may be any regular level set.  We therefore interpolate the
two defining maps affinely and *shift* the interpolation in the interior by a
small Sard-regular value of the associated quotient map.  Regularity of the
interior fiber is then automatic (`sard_dense_regular_values_on`), however
the interpolation behaves; no convex-combination hypothesis remains.

What cannot be regularized away is the *sheet label*: the sign function of
the cobordism must extend both end labels without vanishing on the interior
fiber, and interior fiber components created by far-away antiparallel values
can be labelled freely only if they never connect to the label-carrying tube
around the common fiber.  The exact residual is therefore a **shell
hypothesis**: an open neighborhood `W₁` of the common fiber, contained with
its closure in a bounded open `W₂` on whose closure the two labels strictly
agree in sign near the fiber, such that the closed shell `closure W₂ \ W₁`
contains no zero of any convex combination of the two defining maps.  Inside
`W₁` the interpolated label works; beyond `W₂` every interior zero is
uniformly separated from the collar times, so a constant label patch applies;
the shell separates the two regions.

`Data` records exactly this residual (plus the trivial outer bound expressing
that both maps plateau compatibly at spatial infinity), and
`Data.nonempty_signedCobordism` produces the connector.  The comparison
constructor `Data.ofNoAntiparallel` shows the residual is implied by the
off-fiber no-antiparallelism field of the straight-line certificate alone —
the convex-regularity field of `SameFiberSegmentComparison.Data` has been
eliminated, and the antiparallelism field has been localized to one compact
shell of the caller's choosing.
-/


-- @@ L45-45 verbatim
set_option autoImplicit false

-- @@ L46-46 verbatim
set_option maxHeartbeats 1600000


-- @@ L48-48 verbatim
noncomputable section


-- @@ L50-50 verbatim
namespace Submission

-- @@ L51-51 verbatim
namespace SameFiberSardInterpolation


-- @@ L53-53 verbatim
open Set Function Metric

-- @@ L54-54 verbatim
open SameFiberSegmentComparison

-- @@ L55-55 verbatim
open scoped Topology ContDiff


-- @@ L57-57 verbatim
variable {n : ℕ}


-- @@ L59-59 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L60-60 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)

-- @@ L61-61 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))


-- @@ L63-63 verbatim
/-! ## The residual data -/


-- @@ L65-104 verbatim
/-- **The Sard-interpolation residual.**  Two same-fiber signed presentations
are connected by an actual signed framed level cobordism as soon as

* their defining maps admit one uniform outer bound along all convex
  combinations (true whenever both plateau at a common nonzero background,
  as at the bridge entry);
* there is a *shell*: an open neighborhood `W₁` of the common fiber, on whose
  closure the two labels strictly agree in sign, contained with its closure
  in a bounded open `W₂`, such that no convex combination of the two
  defining maps vanishes on the closed shell `closure W₂ \ W₁`.

No convex-combination regularity is requested (Sard supplies interior
regularity), and no antiparallelism control is requested outside the shell. -/
structure Data (X Y : FramedLevelSet n) (S : FiberSign X) (T : FiberSign Y) where
  /-- The two presentations share their zero fiber. -/
  fiber_eq : Y.fiber = X.fiber
  /-- Spatial radius beyond which the outer bound holds. -/
  R : ℝ
  /-- The uniform outer bound. -/
  eps : ℝ
  eps_pos : 0 < eps
  /-- Outside the ball of radius `R`, every convex combination of the two
  defining maps is uniformly bounded away from zero. -/
  outer : ∀ x : E, R ≤ ‖x‖ → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
    eps ≤ ‖segMap X Y r x‖
  /-- Inner region of the shell: a neighborhood of the common fiber. -/
  W₁ : Set E
  /-- Outer region of the shell. -/
  W₂ : Set E
  isOpen_W₁ : IsOpen W₁
  isOpen_W₂ : IsOpen W₂
  fiber_subset : X.fiber ⊆ W₁
  /-- The two labels strictly agree in sign near the fiber. -/
  agree : ∀ x ∈ closure W₁, 0 < S x * T x
  closure_subset : closure W₁ ⊆ W₂
  isBounded_W₂ : Bornology.IsBounded W₂
  /-- **The shell condition**: no convex combination of the two defining maps
  vanishes on the closed shell. -/
  shell : ∀ x ∈ closure W₂ \ W₁, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
    segMap X Y r x ≠ 0


-- @@ L106-106 verbatim
variable {X Y : FramedLevelSet n} {S : FiberSign X} {T : FiberSign Y}


-- @@ L108-108 verbatim
/-! ## Elementary time and space weights -/


-- @@ L110-111 verbatim
/-- The collar-flat time ramp on space-time. -/
def tR (v : A) : ℝ := normRamp (vertC v)


-- @@ L113-114 verbatim
/-- The interior time weight `r · (1 - r)`, vanishing on both collars. -/
def tW (v : A) : ℝ := tR v * (1 - tR v)


-- @@ L116-116 verbatim
lemma tR_nonneg (v : A) : 0 ≤ tR v := normRamp_nonneg _


-- @@ L118-118 verbatim
lemma tR_le_one (v : A) : tR v ≤ 1 := normRamp_le_one _


-- @@ L120-121 verbatim
lemma tW_nonneg (v : A) : 0 ≤ tW v :=
  mul_nonneg (tR_nonneg v) (by linarith [tR_le_one v])


-- @@ L123-126 verbatim
lemma tW_le_quarter (v : A) : tW v ≤ 1 / 4 := by
  have h := sq_nonneg (2 * tR v - 1)
  unfold tW
  nlinarith


-- @@ L128-129 verbatim
lemma contDiff_tR : ContDiff ℝ ∞ (tR (n := n)) :=
  contDiff_normRamp.comp contDiff_vertC


-- @@ L131-132 verbatim
lemma contDiff_tW : ContDiff ℝ ∞ (tW (n := n)) :=
  contDiff_tR.mul (contDiff_const.sub contDiff_tR)


-- @@ L134-135 verbatim
lemma tR_spaceTime (x : E) (t : ℝ) : tR (spaceTime x t) = normRamp t := by
  rw [tR, vertC_spaceTime]


-- @@ L137-138 verbatim
lemma tR_eq_zero {v : A} (h : vertC v ≤ 1 / 4) : tR v = 0 :=
  normRamp_of_le_quarter h


-- @@ L140-141 verbatim
lemma tR_eq_one {v : A} (h : 3 / 4 ≤ vertC v) : tR v = 1 :=
  normRamp_of_three_quarter_le h


-- @@ L143-146 verbatim
/-- The smooth radial localizer: identically one on the closed ball of
radius `R`, vanishing where `‖x‖ ^ 2 ≥ R ^ 2 + 1`. -/
def bump (R : ℝ) (x : E) : ℝ :=
  Real.smoothTransition (R ^ 2 + 1 - ‖x‖ ^ 2)


-- @@ L148-150 verbatim
lemma contDiff_bump (R : ℝ) : ContDiff ℝ ∞ (bump (n := n) R) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_norm_sq ℝ))


-- @@ L152-153 verbatim
lemma bump_nonneg (R : ℝ) (x : E) : 0 ≤ bump R x :=
  Real.smoothTransition.nonneg _


-- @@ L155-156 verbatim
lemma bump_le_one (R : ℝ) (x : E) : bump R x ≤ 1 :=
  Real.smoothTransition.le_one _


-- @@ L158-160 verbatim
lemma bump_eq_one {R : ℝ} {x : E} (h : ‖x‖ ≤ R) : bump R x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  nlinarith [norm_nonneg x]


-- @@ L162-162 verbatim
/-! ## The shifted interpolation map -/


-- @@ L164-164 verbatim
variable (D : Data X Y S T)


-- @@ L166-170 verbatim
/-- The shifted space-time interpolation: the affine segment between the two
defining maps, displaced in the interior times by the localized target `y`. -/
def cobMap (y : F) (v : A) : F :=
  segMap X Y (tR v) (initCLM (n + 1) v) -
    (tW v * bump D.R (initCLM (n + 1) v)) • y


-- @@ L172-178 verbatim
lemma contDiff_cobMap (y : F) : ContDiff ℝ ∞ (cobMap D y) := by
  have hseg : ContDiff ℝ ∞ fun v : A =>
      segMap X Y (tR v) (initCLM (n + 1) v) :=
    (segMap_smooth X Y).comp (contDiff_tR.prodMk (initCLM (n + 1)).contDiff)
  exact hseg.sub
    ((contDiff_tW.mul ((contDiff_bump D.R).comp
      (initCLM (n + 1)).contDiff)).smul contDiff_const)


-- @@ L180-186 verbatim
lemma cobMap_collar_zero (y : F) (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    cobMap D y (spaceTime x t) = X.g x := by
  have h0 : tR (spaceTime x t) = 0 := by
    rw [tR_spaceTime]
    exact normRamp_of_le_quarter ht
  rw [cobMap, h0, initCLM_spaceTime, tW, h0]
  simp [segMap]


-- @@ L188-194 verbatim
lemma cobMap_collar_one (y : F) (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    cobMap D y (spaceTime x t) = Y.g x := by
  have h1 : tR (spaceTime x t) = 1 := by
    rw [tR_spaceTime]
    exact normRamp_of_three_quarter_le ht
  rw [cobMap, h1, initCLM_spaceTime, tW, h1]
  simp [segMap]


-- @@ L196-211 verbatim
/-- At every zero of the shifted interpolation, the unshifted segment value is
bounded by the target norm. -/
lemma seg_norm_le_of_zero {y : F} {v : A} (hv : cobMap D y v = 0) :
    ‖segMap X Y (tR v) (initCLM (n + 1) v)‖ ≤ ‖y‖ := by
  have hEq : segMap X Y (tR v) (initCLM (n + 1) v) =
      (tW v * bump D.R (initCLM (n + 1) v)) • y :=
    sub_eq_zero.mp hv
  rw [hEq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (tW_nonneg v) (bump_nonneg _ _))]
  have h1 : tW v * bump D.R (initCLM (n + 1) v) ≤ 1 := by
    have := tW_le_quarter v
    have := bump_le_one D.R (initCLM (n + 1) v)
    have := tW_nonneg v
    have := bump_nonneg D.R (initCLM (n + 1) v)
    nlinarith
  nlinarith [norm_nonneg y]


-- @@ L213-220 verbatim
/-- Zeros with vanishing time ramp lie on the source fiber. -/
lemma mem_fiber_of_zero_ramp {y : F} {v : A} (hv : cobMap D y v = 0)
    (h0 : tR v = 0) : initCLM (n + 1) v ∈ X.fiber := by
  have h : segMap X Y (tR v) (initCLM (n + 1) v) -
      (tW v * bump D.R (initCLM (n + 1) v)) • y = 0 := hv
  rw [h0, tW, h0] at h
  have hg : X.g (initCLM (n + 1) v) = 0 := by simpa [segMap] using h
  exact hg


-- @@ L222-229 verbatim
/-- Zeros with time ramp one lie on the target fiber. -/
lemma mem_fiberY_of_one_ramp {y : F} {v : A} (hv : cobMap D y v = 0)
    (h1 : tR v = 1) : initCLM (n + 1) v ∈ Y.fiber := by
  have h : segMap X Y (tR v) (initCLM (n + 1) v) -
      (tW v * bump D.R (initCLM (n + 1) v)) • y = 0 := hv
  rw [h1, tW, h1] at h
  have hg : Y.g (initCLM (n + 1) v) = 0 := by simpa [segMap] using h
  exact hg


-- @@ L231-231 verbatim
/-! ## The interior quotient and its Sard domain -/


-- @@ L233-235 verbatim
/-- The interior region on which the time weight is positive and the
localizer is identically one. -/
def U : Set A := {v | 0 < tW v ∧ ‖initCLM (n + 1) v‖ < D.R}


-- @@ L237-239 verbatim
lemma isOpen_U : IsOpen (U D) := by
  exact (isOpen_lt continuous_const contDiff_tW.continuous).inter
    (isOpen_lt ((initCLM (n + 1)).continuous.norm) continuous_const)


-- @@ L241-244 verbatim
/-- The interior quotient whose Sard-regular values regularize the shifted
interpolation. -/
def quotMap (X Y : FramedLevelSet n) (v : A) : F :=
  (tW v)⁻¹ • segMap X Y (tR v) (initCLM (n + 1) v)


-- @@ L246-251 verbatim
lemma contDiffOn_quotMap : ContDiffOn ℝ ∞ (quotMap X Y) (U D) := by
  have hseg : ContDiff ℝ ∞ fun v : A =>
      segMap X Y (tR v) (initCLM (n + 1) v) :=
    (segMap_smooth X Y).comp (contDiff_tR.prodMk (initCLM (n + 1)).contDiff)
  exact (contDiff_tW.contDiffOn.inv fun v hv => hv.1.ne').smul
    hseg.contDiffOn


-- @@ L253-260 verbatim
/-- On the interior region the shifted interpolation factors through the
quotient. -/
lemma cobMap_eq_on_U (y : F) : ∀ v ∈ U D,
    cobMap D y v = tW v • (quotMap X Y v - y) := by
  intro v hv
  have hb : bump D.R (initCLM (n + 1) v) = 1 := bump_eq_one hv.2.le
  rw [cobMap, hb, mul_one, quotMap, smul_sub, smul_smul,
    mul_inv_cancel₀ hv.1.ne', one_smul]


-- @@ L262-268 verbatim
lemma quotMap_eq_of_zero {y : F} {v : A} (hv : cobMap D y v = 0)
    (hvU : v ∈ U D) : quotMap X Y v = y := by
  have h := cobMap_eq_on_U D y v hvU
  rw [hv] at h
  have h2 : quotMap X Y v - y = 0 :=
    (smul_eq_zero.mp h.symm).resolve_left hvU.1.ne'
  exact sub_eq_zero.mp h2


-- @@ L270-270 verbatim
/-! ## The witness: shell separation constants, label patch, Sard value -/


-- @@ L272-297 verbatim
/-- All auxiliary choices needed to run the construction, packaged with the
inequalities actually used downstream.  `Witness.nonempty` constructs one
from the residual data alone. -/
structure Witness (D : Data X Y S T) where
  /-- The Sard-regular interior target. -/
  y : F
  /-- The interior separation constant of the danger bound. -/
  rho : ℝ
  rho_pos : 0 < rho
  /-- Sard regularity of the interior quotient at `y`. -/
  hreg : IsRegularValueOn (quotMap X Y) (U D) y
  /-- The target is smaller than the outer bound. -/
  small_outer : ‖y‖ < D.eps
  /-- The target is smaller than the shell separation. -/
  shell_lt : ∀ x ∈ closure D.W₂ \ D.W₁, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
    ‖y‖ < ‖segMap X Y r x‖
  /-- The danger bound: interior zeros away from `W₁` occur only at times
  uniformly separated from the collars. -/
  danger : ∀ x : E, ‖x‖ ≤ D.R → x ∉ D.W₁ → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
    ‖segMap X Y r x‖ ≤ ‖y‖ → rho ≤ r * (1 - r)
  /-- The continuous spatial patch selector. -/
  chi : E → ℝ
  chi_continuous : Continuous chi
  chi_mem : ∀ x : E, chi x ∈ Set.Icc (0 : ℝ) 1
  chi_zero : ∀ x ∈ closure D.W₁, chi x = 0
  chi_one : ∀ x ∉ D.W₂, chi x = 1


-- @@ L299-299 verbatim
namespace Witness


-- @@ L301-301 verbatim
variable {D}


-- @@ L303-303 verbatim
/-! ### Zero location lemmas -/


-- @@ L305-316 verbatim
/-- Every zero of the shifted interpolation is strictly inside the outer
ball. -/
lemma zero_spatial (W : Witness D) {v : A} (hv : cobMap D W.y v = 0) :
    ‖initCLM (n + 1) v‖ < D.R := by
  rcases lt_or_ge ‖initCLM (n + 1) v‖ D.R with h | h
  · exact h
  · exfalso
    have houter := D.outer (initCLM (n + 1) v) h (tR v) (tR_nonneg v)
      (tR_le_one v)
    have hle := seg_norm_le_of_zero D hv
    have := W.small_outer
    linarith


-- @@ L318-326 verbatim
/-- No zero of the shifted interpolation has its spatial part in the closed
shell. -/
lemma zero_not_shell (W : Witness D) {v : A} (hv : cobMap D W.y v = 0) :
    initCLM (n + 1) v ∉ closure D.W₂ \ D.W₁ := by
  intro hmem
  have hlt := W.shell_lt (initCLM (n + 1) v) hmem (tR v) (tR_nonneg v)
    (tR_le_one v)
  have hle := seg_norm_le_of_zero D hv
  linarith


-- @@ L328-328 verbatim
/-! ### Regularity of the shifted interpolation -/


-- @@ L330-336 verbatim
/-- Interior zeros lie in the Sard domain. -/
lemma zero_mem_U (W : Witness D) {v : A} (hv : cobMap D W.y v = 0)
    (h0 : tR v ≠ 0) (h1 : tR v ≠ 1) : v ∈ U D := by
  refine ⟨?_, W.zero_spatial hv⟩
  have hr0 : 0 < tR v := lt_of_le_of_ne (tR_nonneg v) (Ne.symm h0)
  have hr1 : tR v < 1 := lt_of_le_of_ne (tR_le_one v) h1
  exact mul_pos hr0 (by linarith)


-- @@ L338-403 verbatim
/-- **Regularity.**  Every zero of the shifted interpolation has surjective
derivative: collar-time zeros restrict to the regular end presentations, and
interior zeros are Sard-regular. -/
theorem cobMap_regular (W : Witness D) :
    ∀ v : A, cobMap D W.y v = 0 →
      Function.Surjective (fderiv ℝ (cobMap D W.y) v) := by
  intro v hv
  by_cases h0 : tR v = 0
  · -- collar case: the time slice is the source presentation
    have hx : initCLM (n + 1) v ∈ X.fiber := mem_fiber_of_zero_ramp D hv h0
    apply surjective_fderiv_of_slice (contDiff_cobMap D W.y)
    have h0' : normRamp (vertC v) = 0 := h0
    have hslice : (fun x' : E => cobMap D W.y (spaceTime x' (vertC v))) =
        X.g := by
      funext x'
      rw [cobMap, tW, tR_spaceTime, h0', initCLM_spaceTime]
      simp [segMap]
    rw [hslice]
    exact X.regular _ hx
  · by_cases h1 : tR v = 1
    · -- collar case: the time slice is the target presentation
      have hx : initCLM (n + 1) v ∈ Y.fiber := mem_fiberY_of_one_ramp D hv h1
      apply surjective_fderiv_of_slice (contDiff_cobMap D W.y)
      have h1' : normRamp (vertC v) = 1 := h1
      have hslice : (fun x' : E => cobMap D W.y (spaceTime x' (vertC v))) =
          Y.g := by
        funext x'
        rw [cobMap, tW, tR_spaceTime, h1', initCLM_spaceTime]
        simp [segMap]
      rw [hslice]
      exact Y.regular _ hx
    · -- interior case: Sard regularity of the quotient
      have hvU : v ∈ U D := W.zero_mem_U hv h0 h1
      have hEv : cobMap D W.y =ᶠ[𝓝 v]
          fun v' => tW v' • (quotMap X Y v' - W.y) :=
        Filter.eventuallyEq_of_mem ((isOpen_U D).mem_nhds hvU)
          (cobMap_eq_on_U D W.y)
      have hqv : quotMap X Y v = W.y := quotMap_eq_of_zero D hv hvU
      have hqDiff : DifferentiableAt ℝ (quotMap X Y) v :=
        (((contDiffOn_quotMap D).contDiffAt
          ((isOpen_U D).mem_nhds hvU)).differentiableAt infty_ne_zero)
      have hwDiff : HasFDerivAt tW (fderiv ℝ tW v) v :=
        (contDiff_tW.differentiable infty_ne_zero v).hasFDerivAt
      have hprod : HasFDerivAt
          (fun v' => tW v' • (quotMap X Y v' - W.y))
          (tW v • fderiv ℝ (quotMap X Y) v +
            (fderiv ℝ tW v).smulRight (quotMap X Y v - W.y)) v :=
        hwDiff.smul (hqDiff.hasFDerivAt.sub_const W.y)
      have hfd : fderiv ℝ (cobMap D W.y) v =
          tW v • fderiv ℝ (quotMap X Y) v +
            (fderiv ℝ tW v).smulRight (quotMap X Y v - W.y) := by
        rw [hEv.fderiv_eq]
        exact hprod.fderiv
      have hsurjq : Function.Surjective (fderiv ℝ (quotMap X Y) v) := by
        have h := W.hreg v hvU hqv
        rwa [fderivWithin_of_isOpen (isOpen_U D) hvU] at h
      intro z
      obtain ⟨u, hu⟩ := hsurjq ((tW v)⁻¹ • z)
      refine ⟨u, ?_⟩
      rw [hfd]
      have hzero : quotMap X Y v - W.y = 0 := by
        rw [hqv, sub_self]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, hzero, smul_zero, add_zero, hu,
        smul_smul]
      rw [mul_inv_cancel₀ hvU.1.ne', one_smul]


-- @@ L405-414 verbatim
/-- The underlying framed level cobordism. -/
def cobordism (W : Witness D) : FramedLevelCobordism n where
  X₀ := X
  X₁ := Y
  G := cobMap D W.y
  smooth := contDiff_cobMap D W.y
  spatial_bounded := ⟨D.R, fun v hv => (W.zero_spatial hv).le⟩
  regular := W.cobMap_regular
  collar_zero := fun x t ht => cobMap_collar_zero D W.y x ht
  collar_one := fun x t ht => cobMap_collar_one D W.y x ht


-- @@ L416-416 verbatim
/-! ### The sheet label -/


-- @@ L418-420 verbatim
/-- The convex interpolation of the two end labels. -/
def combo (S : FiberSign X) (T : FiberSign Y) (v : A) : ℝ :=
  (1 - tR v) * S (initCLM (n + 1) v) + tR v * T (initCLM (n + 1) v)


-- @@ L422-426 verbatim
lemma continuous_combo : Continuous (combo S T) := by
  have hR : Continuous (tR (n := n)) := contDiff_tR.continuous
  exact ((continuous_const.sub hR).mul
      (S.continuous.comp (initCLM (n + 1)).continuous)).add
    (hR.mul (T.continuous.comp (initCLM (n + 1)).continuous))


-- @@ L428-429 verbatim
/-- The continuous collar-safe patch ramp. -/
def tauRamp (rho s : ℝ) : ℝ := max 0 (min 1 ((2 * s - rho) / rho))


-- @@ L431-436 verbatim
lemma continuous_tauRamp_comp (rho : ℝ) :
    Continuous fun v : A => tauRamp rho (tW v) := by
  have h : Continuous fun v : A => (2 * tW v - rho) / rho :=
    ((continuous_const.mul contDiff_tW.continuous).sub
      continuous_const).div_const rho
  exact continuous_const.max (continuous_const.min h)


-- @@ L438-445 verbatim
lemma tauRamp_zero {rho : ℝ} (h : 0 < rho) : tauRamp rho 0 = 0 := by
  rw [tauRamp]
  have hneg : (2 * 0 - rho) / rho = -1 := by
    rw [show (2 : ℝ) * 0 - rho = -rho by ring, neg_div, div_self h.ne']
  rw [hneg]
  have hmin : min (1 : ℝ) (-1) = -1 := min_eq_right (by norm_num)
  rw [hmin]
  exact max_eq_left (by norm_num)


-- @@ L447-454 verbatim
lemma tauRamp_one {rho s : ℝ} (h : 0 < rho) (hs : rho ≤ s) :
    tauRamp rho s = 1 := by
  rw [tauRamp]
  have hone : (1 : ℝ) ≤ (2 * s - rho) / rho := by
    rw [le_div_iff₀ h]
    linarith
  rw [min_eq_left hone]
  exact max_eq_right (by norm_num)


-- @@ L456-460 verbatim
/-- The complete label: interpolate the two sheet labels near the fiber and
patch to the constant one on interior zeros away from the shell. -/
def label (W : Witness D) (v : A) : ℝ :=
  combo S T v +
    tauRamp W.rho (tW v) * W.chi (initCLM (n + 1) v) * (1 - combo S T v)


-- @@ L462-466 verbatim
lemma continuous_label (W : Witness D) : Continuous (W.label) := by
  exact (continuous_combo).add
    (((continuous_tauRamp_comp W.rho).mul
        (W.chi_continuous.comp (initCLM (n + 1)).continuous)).mul
      (continuous_const.sub continuous_combo))


-- @@ L468-477 verbatim
lemma label_collar_zero (W : Witness D) (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    W.label (spaceTime x t) = S x := by
  have h0 : tR (spaceTime x t) = 0 := by
    rw [tR_spaceTime]
    exact normRamp_of_le_quarter ht
  have htW : tW (spaceTime x t) = 0 := by
    rw [tW, h0]
    ring
  rw [label, htW, tauRamp_zero W.rho_pos, combo, h0, initCLM_spaceTime]
  ring


-- @@ L479-488 verbatim
lemma label_collar_one (W : Witness D) (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    W.label (spaceTime x t) = T x := by
  have h1 : tR (spaceTime x t) = 1 := by
    rw [tR_spaceTime]
    exact normRamp_of_three_quarter_le ht
  have htW : tW (spaceTime x t) = 0 := by
    rw [tW, h1]
    ring
  rw [label, htW, tauRamp_zero W.rho_pos, combo, h1, initCLM_spaceTime]
  ring


-- @@ L490-524 verbatim
/-- The interpolated label does not vanish where the two labels strictly
agree in sign. -/
lemma combo_ne_zero_of_agree {v : A}
    (hagree : 0 < S (initCLM (n + 1) v) * T (initCLM (n + 1) v)) :
    combo S T v ≠ 0 := by
  have hr0 := tR_nonneg v
  have hr1 := tR_le_one v
  rcases mul_pos_iff.mp hagree with ⟨hS, hT⟩ | ⟨hS, hT⟩
  · -- both labels positive
    have h1 : 0 ≤ (1 - tR v) * S (initCLM (n + 1) v) :=
      mul_nonneg (by linarith) hS.le
    have h2 : 0 ≤ tR v * T (initCLM (n + 1) v) := mul_nonneg hr0 hT.le
    rcases lt_or_ge (tR v) 1 with hlt | hge
    · have : 0 < (1 - tR v) * S (initCLM (n + 1) v) :=
        mul_pos (by linarith) hS
      exact ne_of_gt (by rw [combo]; linarith)
    · have h1' : tR v = 1 := le_antisymm hr1 hge
      have : 0 < tR v * T (initCLM (n + 1) v) := by
        rw [h1']
        simpa using hT
      exact ne_of_gt (by rw [combo]; linarith)
  · -- both labels negative
    have h1 : (1 - tR v) * S (initCLM (n + 1) v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hS.le
    have h2 : tR v * T (initCLM (n + 1) v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hr0 hT.le
    rcases lt_or_ge (tR v) 1 with hlt | hge
    · have : (1 - tR v) * S (initCLM (n + 1) v) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) hS
      exact ne_of_lt (by rw [combo]; linarith)
    · have h1' : tR v = 1 := le_antisymm hr1 hge
      have : tR v * T (initCLM (n + 1) v) < 0 := by
        rw [h1']
        simpa using hT
      exact ne_of_lt (by rw [combo]; linarith)


-- @@ L526-579 verbatim
/-- **The label never vanishes on the shifted fiber.** -/
theorem label_ne_zero (W : Witness D) :
    ∀ v : A, cobMap D W.y v = 0 → W.label v ≠ 0 := by
  intro v hv
  by_cases h0 : tR v = 0
  · -- source collar: the label is the source label on the source fiber
    have hx : initCLM (n + 1) v ∈ X.fiber := mem_fiber_of_zero_ramp D hv h0
    have htW : tW v = 0 := by
      rw [tW, h0]
      ring
    have hL : W.label v = S (initCLM (n + 1) v) := by
      rw [label, htW, tauRamp_zero W.rho_pos, combo, h0]
      ring
    rw [hL]
    exact S.nonzero _ hx
  · by_cases h1 : tR v = 1
    · have hx : initCLM (n + 1) v ∈ Y.fiber := mem_fiberY_of_one_ramp D hv h1
      have htW : tW v = 0 := by
        rw [tW, h1]
        ring
      have hL : W.label v = T (initCLM (n + 1) v) := by
        rw [label, htW, tauRamp_zero W.rho_pos, combo, h1]
        ring
      rw [hL]
      exact T.nonzero _ hx
    · -- interior times
      by_cases hx2 : initCLM (n + 1) v ∈ closure D.W₂
      · by_cases hx1 : initCLM (n + 1) v ∈ D.W₁
        · -- near the fiber: the interpolated label works, the patch is off
          have hchi : W.chi (initCLM (n + 1) v) = 0 :=
            W.chi_zero _ (subset_closure hx1)
          have hL : W.label v = combo S T v := by
            rw [label, hchi]
            ring
          rw [hL]
          exact combo_ne_zero_of_agree
            (D.agree _ (subset_closure hx1))
        · -- the shell carries no zeros
          exact absurd ⟨hx2, hx1⟩ (W.zero_not_shell hv)
      · -- beyond the shell: the patch is fully on and the label is one
        have hxW₂ : initCLM (n + 1) v ∉ D.W₂ := fun h => hx2 (subset_closure h)
        have hxW₁ : initCLM (n + 1) v ∉ D.W₁ := fun h =>
          hx2 (subset_closure (D.closure_subset (subset_closure h)))
        have hchi : W.chi (initCLM (n + 1) v) = 1 := W.chi_one _ hxW₂
        have hrho : W.rho ≤ tW v := by
          have := W.danger (initCLM (n + 1) v) (W.zero_spatial hv).le hxW₁
            (tR v) (tR_nonneg v) (tR_le_one v) (seg_norm_le_of_zero D hv)
          exact this
        have htau : tauRamp W.rho (tW v) = 1 := tauRamp_one W.rho_pos hrho
        have hL : W.label v = 1 := by
          rw [label, htau, hchi]
          ring
        rw [hL]
        exact one_ne_zero


-- @@ L581-581 verbatim
/-! ### The signed cobordism -/


-- @@ L583-593 verbatim
/-- **The Sard-regularized signed framed level cobordism** between the two
same-fiber signed presentations. -/
def signedCobordism (W : Witness D) : SignedFramedLevelCobordism S T where
  cobordism := W.cobordism
  source_eq := rfl
  target_eq := rfl
  toFun := W.label
  continuous := W.continuous_label
  nonzero := fun v hv => W.label_ne_zero v hv
  collar_zero := fun x t ht => W.label_collar_zero x ht
  collar_one := fun x t ht => W.label_collar_one x ht


-- @@ L595-595 verbatim
end Witness


-- @@ L597-597 verbatim
/-! ## Existence of a witness -/


-- @@ L599-630 verbatim
/-- The uniform shell separation constant. -/
lemma exists_shell_bound :
    ∃ eps₂ : ℝ, 0 < eps₂ ∧ ∀ x ∈ closure D.W₂ \ D.W₁, ∀ r : ℝ,
      0 ≤ r → r ≤ 1 → eps₂ ≤ ‖segMap X Y r x‖ := by
  classical
  have hKclosed : IsClosed (closure D.W₂ \ D.W₁) := by
    rw [Set.diff_eq]
    exact isClosed_closure.inter D.isOpen_W₁.isClosed_compl
  have hKcompact : IsCompact (closure D.W₂ \ D.W₁) :=
    Metric.isCompact_of_isClosed_isBounded hKclosed
      (D.isBounded_W₂.closure.subset Set.diff_subset)
  have hQcompact : IsCompact
      ((closure D.W₂ \ D.W₁) ×ˢ Set.Icc (0 : ℝ) 1) :=
    hKcompact.prod isCompact_Icc
  have hf : Continuous fun p : E × ℝ => ‖segMap X Y p.2 p.1‖ := by
    have hraw : Continuous fun p : E × ℝ =>
        (1 - p.2) • X.g p.1 + p.2 • Y.g p.1 :=
      ((continuous_const.sub continuous_snd).smul
        (X.smooth.continuous.comp continuous_fst)).add
        (continuous_snd.smul (Y.smooth.continuous.comp continuous_fst))
    exact hraw.norm
  by_cases hne : ((closure D.W₂ \ D.W₁) ×ˢ Set.Icc (0 : ℝ) 1).Nonempty
  · obtain ⟨p, hpQ, hmin⟩ := hQcompact.exists_isMinOn hne hf.continuousOn
    rw [Set.mem_prod] at hpQ
    refine ⟨‖segMap X Y p.2 p.1‖, ?_, ?_⟩
    · exact norm_pos_iff.mpr (D.shell p.1 hpQ.1 p.2 hpQ.2.1 hpQ.2.2)
    · intro x hx r hr0 hr1
      exact isMinOn_iff.mp hmin (x, r) (Set.mem_prod.mpr ⟨hx, hr0, hr1⟩)
  · refine ⟨1, one_pos, fun x hx r hr0 hr1 => ?_⟩
    have hmem : (x, r) ∈ (closure D.W₂ \ D.W₁) ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mem_prod.mpr ⟨hx, hr0, hr1⟩
    exact absurd (Set.nonempty_of_mem hmem) hne


-- @@ L632-734 verbatim
/-- The interior danger bound: zeros of small segment values away from `W₁`
occur only at times uniformly separated from the collars. -/
lemma exists_danger_bound :
    ∃ rho : ℝ, 0 < rho ∧ ∃ eta : ℝ, 0 < eta ∧
      ∀ x : E, ‖x‖ ≤ D.R → x ∉ D.W₁ → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        ‖segMap X Y r x‖ ≤ eta → rho ≤ r * (1 - r) := by
  classical
  have hKclosed : IsClosed (Metric.closedBall (0 : E) D.R \ D.W₁) := by
    rw [Set.diff_eq]
    exact Metric.isClosed_closedBall.inter D.isOpen_W₁.isClosed_compl
  have hKcompact : IsCompact (Metric.closedBall (0 : E) D.R \ D.W₁) :=
    Metric.isCompact_of_isClosed_isBounded hKclosed
      (Metric.isBounded_closedBall.subset Set.diff_subset)
  by_cases hne : (Metric.closedBall (0 : E) D.R \ D.W₁).Nonempty
  · have hballne : (Metric.closedBall (0 : E) D.R).Nonempty :=
      hne.mono Set.diff_subset
    obtain ⟨x₁, hx₁, hminX⟩ := hKcompact.exists_isMinOn hne
      (X.smooth.continuous.norm.continuousOn)
    obtain ⟨x₂, hx₂, hminY⟩ := hKcompact.exists_isMinOn hne
      (Y.smooth.continuous.norm.continuousOn)
    obtain ⟨x₃, _, hmaxX⟩ := (isCompact_closedBall (0 : E) D.R).exists_isMaxOn
      hballne (X.smooth.continuous.norm.continuousOn)
    obtain ⟨x₄, _, hmaxY⟩ := (isCompact_closedBall (0 : E) D.R).exists_isMaxOn
      hballne (Y.smooth.continuous.norm.continuousOn)
    set dX : ℝ := ‖X.g x₁‖ with hdX
    set dY : ℝ := ‖Y.g x₂‖ with hdY
    set MX : ℝ := ‖X.g x₃‖ with hMX
    set MY : ℝ := ‖Y.g x₄‖ with hMY
    have hdXpos : 0 < dX := by
      apply norm_pos_iff.mpr
      intro hzero
      exact hx₁.2 (D.fiber_subset hzero)
    have hdYpos : 0 < dY := by
      apply norm_pos_iff.mpr
      intro hzero
      have hxf : x₂ ∈ Y.fiber := hzero
      rw [D.fiber_eq] at hxf
      exact hx₂.2 (D.fiber_subset hxf)
    have hMXnn : 0 ≤ MX := norm_nonneg _
    have hMYnn : 0 ≤ MY := norm_nonneg _
    refine ⟨(dX / (2 * (dX + MY + 1))) * (dY / (2 * (dY + MX + 1))),
      by positivity, min dX dY / 2, by positivity, ?_⟩
    intro x hxR hxW r hr0 hr1 hseg
    have hxB : x ∈ Metric.closedBall (0 : E) D.R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hxR
    have hxK : x ∈ Metric.closedBall (0 : E) D.R \ D.W₁ := ⟨hxB, hxW⟩
    have hXlow : dX ≤ ‖X.g x‖ := isMinOn_iff.mp hminX x hxK
    have hYlow : dY ≤ ‖Y.g x‖ := isMinOn_iff.mp hminY x hxK
    have hXhigh : ‖X.g x‖ ≤ MX := isMaxOn_iff.mp hmaxX x hxB
    have hYhigh : ‖Y.g x‖ ≤ MY := isMaxOn_iff.mp hmaxY x hxB
    -- decompose the segment on both sides
    have hsegX : (1 - r) * ‖X.g x‖ ≤ ‖segMap X Y r x‖ + r * ‖Y.g x‖ := by
      have hEq : (1 - r) • X.g x = segMap X Y r x - r • Y.g x := by
        rw [segMap]
        abel
      calc
        (1 - r) * ‖X.g x‖ = ‖(1 - r) • X.g x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        _ = ‖segMap X Y r x - r • Y.g x‖ := by rw [hEq]
        _ ≤ ‖segMap X Y r x‖ + ‖r • Y.g x‖ := norm_sub_le _ _
        _ = ‖segMap X Y r x‖ + r * ‖Y.g x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    have hsegY : r * ‖Y.g x‖ ≤ ‖segMap X Y r x‖ + (1 - r) * ‖X.g x‖ := by
      have hEq : r • Y.g x = segMap X Y r x - (1 - r) • X.g x := by
        rw [segMap]
        abel
      calc
        r * ‖Y.g x‖ = ‖r • Y.g x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
        _ = ‖segMap X Y r x - (1 - r) • X.g x‖ := by rw [hEq]
        _ ≤ ‖segMap X Y r x‖ + ‖(1 - r) • X.g x‖ := norm_sub_le _ _
        _ = ‖segMap X Y r x‖ + (1 - r) * ‖X.g x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hetaX : min dX dY / 2 ≤ dX / 2 := by
      have := min_le_left dX dY
      linarith
    have hetaY : min dX dY / 2 ≤ dY / 2 := by
      have := min_le_right dX dY
      linarith
    -- lower bound on r
    have hr_low : dX / (2 * (dX + MY + 1)) ≤ r := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 - r) * dX ≤ (1 - r) * ‖X.g x‖ :=
        mul_le_mul_of_nonneg_left hXlow (by linarith)
      have h2 : r * ‖Y.g x‖ ≤ r * MY :=
        mul_le_mul_of_nonneg_left hYhigh hr0
      nlinarith
    -- lower bound on 1 - r
    have hr_high : dY / (2 * (dY + MX + 1)) ≤ 1 - r := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : r * dY ≤ r * ‖Y.g x‖ :=
        mul_le_mul_of_nonneg_left hYlow hr0
      have h2 : (1 - r) * ‖X.g x‖ ≤ (1 - r) * MX :=
        mul_le_mul_of_nonneg_left hXhigh (by linarith)
      nlinarith
    exact mul_le_mul hr_low hr_high (by positivity) hr0
  · refine ⟨1, one_pos, 1, one_pos, fun x hxR hxW r _ _ _ => ?_⟩
    have hxB : x ∈ Metric.closedBall (0 : E) D.R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hxR
    have hmem : x ∈ Metric.closedBall (0 : E) D.R \ D.W₁ := ⟨hxB, hxW⟩
    exact absurd (Set.nonempty_of_mem hmem) hne


-- @@ L736-753 verbatim
/-- The continuous patch selector between the two shell regions. -/
lemma exists_chi :
    ∃ chi : E → ℝ, Continuous chi ∧ (∀ x : E, chi x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∈ closure D.W₁, chi x = 0) ∧ ∀ x ∉ D.W₂, chi x = 1 := by
  have hs : IsClosed (closure D.W₁) := isClosed_closure
  have ht : IsClosed D.W₂ᶜ := D.isOpen_W₂.isClosed_compl
  have hd : Disjoint (closure D.W₁) D.W₂ᶜ := by
    rw [Set.disjoint_left]
    intro x hx hxc
    exact hxc (D.closure_subset hx)
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hs ht hd
  refine ⟨⇑f, ?_, hf01, fun x hx => hf0 hx, fun x hx => hf1 hx⟩
  have hχ : ContDiff ℝ ∞ (⇑f) := by
    rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  exact hχ.continuous


-- @@ L755-791 verbatim
/-- **Witness existence**: the residual data alone produces all separation
constants, the patch selector, and a Sard-regular interior target. -/
theorem Witness.nonempty : Nonempty (Witness D) := by
  classical
  obtain ⟨eps₂, heps₂, hshell⟩ := exists_shell_bound D
  obtain ⟨rho, hrho, eta, heta, hdanger⟩ := exists_danger_bound D
  obtain ⟨chi, hchi_cont, hchi_mem, hchi0, hchi1⟩ := exists_chi D
  set delta : ℝ := min (min D.eps eta) eps₂ with hdelta
  have hdeltapos : 0 < delta := by
    apply lt_min (lt_min D.eps_pos heta) heps₂
  have hdense := sard_dense_regular_values_on (isOpen_U D)
    (contDiffOn_quotMap D)
  obtain ⟨y, hyreg, hyball⟩ := hdense.exists_mem_open
    (show IsOpen (Metric.ball (0 : F) delta) from Metric.isOpen_ball)
    (Metric.nonempty_ball.mpr hdeltapos)
  have hynorm : ‖y‖ < delta := by
    rwa [Metric.mem_ball, dist_zero_right] at hyball
  have hy_eps : ‖y‖ < D.eps :=
    lt_of_lt_of_le hynorm ((min_le_left _ _).trans (min_le_left _ _))
  have hy_eta : ‖y‖ < eta :=
    lt_of_lt_of_le hynorm ((min_le_left _ _).trans (min_le_right _ _))
  have hy_eps₂ : ‖y‖ < eps₂ := lt_of_lt_of_le hynorm (min_le_right _ _)
  exact ⟨{
    y := y
    rho := rho
    rho_pos := hrho
    hreg := hyreg
    small_outer := hy_eps
    shell_lt := fun x hx r hr0 hr1 =>
      lt_of_lt_of_le hy_eps₂ (hshell x hx r hr0 hr1)
    danger := fun x hxR hxW r hr0 hr1 hseg =>
      hdanger x hxR hxW r hr0 hr1 (hseg.trans hy_eta.le)
    chi := chi
    chi_continuous := hchi_cont
    chi_mem := hchi_mem
    chi_zero := hchi0
    chi_one := hchi1 }⟩


-- @@ L793-793 verbatim
/-! ## The connector -/


-- @@ L795-800 verbatim
/-- **The main theorem**: the Sard-interpolation residual produces an actual
signed framed level cobordism between the two same-fiber presentations. -/
theorem Data.nonempty_signedCobordism (D : Data X Y S T) :
    Nonempty (SignedFramedLevelCobordism S T) := by
  obtain ⟨W⟩ := Witness.nonempty D
  exact ⟨W.signedCobordism⟩


-- @@ L802-802 verbatim
/-! ## Comparison: the residual follows from off-fiber no-antiparallelism -/


-- @@ L804-879 verbatim
/-- The straight-line no-antiparallelism field alone (with the trivial outer
bound) discharges the entire residual: the shell exists because no convex
combination vanishes off the fiber at all.  In particular the
convex-regularity field of `SameFiberSegmentComparison.Data` has been
eliminated. -/
def Data.ofNoAntiparallel
    (X Y : FramedLevelSet n) (S : FiberSign X) (T : FiberSign Y)
    (fiber_eq : Y.fiber = X.fiber)
    (R eps : ℝ) (eps_pos : 0 < eps)
    (outer : ∀ x : E, R ≤ ‖x‖ → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      eps ≤ ‖segMap X Y r x‖)
    (hagree : ∀ x ∈ X.fiber, 0 < S x * T x)
    (hno : ∀ x ∉ X.fiber, ∀ c : ℝ, c < 0 → Y.g x ≠ c • X.g x) :
    Data X Y S T := by
  classical
  have hopen : IsOpen {x : E | 0 < S x * T x} :=
    isOpen_lt continuous_const (S.continuous.mul T.continuous)
  have hex : ∃ delta : ℝ, 0 < delta ∧
      Metric.cthickening delta X.fiber ⊆ {x : E | 0 < S x * T x} :=
    X.isCompact_fiber.exists_cthickening_subset_open hopen
      fun x hx => hagree x hx
  set delta : ℝ := hex.choose with hdelta_def
  have hdeltapos : 0 < delta := hex.choose_spec.1
  have hsub : Metric.cthickening delta X.fiber ⊆
      {x : E | 0 < S x * T x} := hex.choose_spec.2
  have hseg_ne : ∀ x : E, x ∉ X.fiber → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      segMap X Y r x ≠ 0 := by
    intro x hx r hr0 hr1 hzero
    rcases eq_or_lt_of_le hr0 with hr0e | hr0p
    · have hX : X.g x = 0 := by
        rw [← hr0e] at hzero
        simpa [segMap] using hzero
      exact hx hX
    · rcases eq_or_lt_of_le hr1 with hr1e | hr1p
      · have hY : Y.g x = 0 := by
          rw [hr1e] at hzero
          simpa [segMap] using hzero
        have hmem : x ∈ Y.fiber := hY
        rw [fiber_eq] at hmem
        exact hx hmem
      · have hsne : r ≠ 0 := ne_of_gt hr0p
        have hzero' : (1 - r) • X.g x + r • Y.g x = 0 := hzero
        have h1 : r • Y.g x = (-(1 - r)) • X.g x := by
          rw [neg_smul]
          exact eq_neg_of_add_eq_zero_right hzero'
        have h2 : Y.g x = (r⁻¹ * -(1 - r)) • X.g x := by
          rw [← inv_smul_smul₀ hsne (Y.g x), h1, smul_smul]
        exact hno x hx (r⁻¹ * -(1 - r))
          (mul_neg_of_pos_of_neg (inv_pos.mpr hr0p) (by linarith)) h2
  refine
    { fiber_eq := fiber_eq
      R := R
      eps := eps
      eps_pos := eps_pos
      outer := outer
      W₁ := Metric.thickening delta X.fiber
      W₂ := Metric.thickening (2 * delta) X.fiber
      isOpen_W₁ := Metric.isOpen_thickening
      isOpen_W₂ := Metric.isOpen_thickening
      fiber_subset := Metric.self_subset_thickening hdeltapos _
      agree := ?_
      closure_subset := ?_
      isBounded_W₂ := ?_
      shell := ?_ }
  · intro x hx
    apply hsub
    exact (Metric.closure_thickening_subset_cthickening _ _) hx
  · exact (Metric.closure_thickening_subset_cthickening _ _).trans
      (Metric.cthickening_subset_thickening' (by linarith)
        (by linarith) _)
  · exact (X.isCompact_fiber.cthickening.isBounded).subset
      (Metric.thickening_subset_cthickening _ _)
  · intro x hx r hr0 hr1
    apply hseg_ne x ?_ r hr0 hr1
    intro hxf
    exact hx.2 (Metric.self_subset_thickening hdeltapos _ hxf)


-- @@ L881-881 verbatim
end SameFiberSardInterpolation

-- @@ L882-882 verbatim
end Submission
