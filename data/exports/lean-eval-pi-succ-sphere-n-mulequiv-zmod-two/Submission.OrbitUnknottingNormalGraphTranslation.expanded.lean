import Mathlib
import Submission.OrbitUnknottingTubeCoordinateConjugation


-- @@ L4-21 verbatim
/-!
# Compactly supported normal-graph translations

This file turns a sufficiently small, period-one normal graph into the
tube-coordinate isotopy consumed by
`PeriodicTubeCoordinateIsotopy.toSmoothAmbientIsotopy`.

The fibre map is the compactly supported perturbation

`z ↦ z + β(z) • (normRamp s • h u)`.

Its inverse is not obtained by incorrectly evaluating the same radial cutoff
at the target.  Instead, the small Lipschitz bound makes
`z ↦ y - β(z) • (normRamp s • h u)` a contraction.  Banach's fixed-point
theorem gives the unique global inverse.  A parameterized inverse-function
argument then proves that this inverse is jointly smooth in time, phase and
normal position.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false

-- @@ L24-24 verbatim
set_option maxHeartbeats 300000


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open Set Function Metric Filter

-- @@ L29-29 verbatim
open scoped Topology ContDiff NNReal


-- @@ L31-31 verbatim
namespace Submission

-- @@ L32-32 verbatim
namespace TamedField


-- @@ L34-34 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L36-36 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L37-37 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)

-- @@ L38-38 verbatim
local notation "C" => AddCircle (1 : ℝ)

-- @@ L39-39 verbatim
local notation "P" => ℝ × ℝ


-- @@ L41-57 verbatim
/-- Input contract for one small period-one normal graph.  `bump` is one on
its inner ball and supported in its outer ball.  The two strict inequalities
are exactly the quantitative hypotheses used below: the first gives a global
inverse, and the second keeps the whole move inside the chosen orbit tube. -/
structure SmallPeriodicNormalGraph (O : V.OrbitIndex) where
  h : ℝ → N
  h_smooth : ContDiff ℝ ∞ h
  h_periodic : Function.Periodic h 1
  normBound : ℝ
  normBound_nonneg : 0 ≤ normBound
  norm_h_le : ∀ u, ‖h u‖ ≤ normBound
  bump : ContDiffBump (0 : N)
  bumpLipschitz : ℝ≥0
  bump_lipschitz : LipschitzWith bumpLipschitz bump
  contraction_lt_one : normBound * (bumpLipschitz : ℝ) < 1
  support_lt_tube : bump.rOut + normBound <
    (V.globalSmoothOrbitTube O).radius


-- @@ L59-59 verbatim
variable {V} {O : V.OrbitIndex}


-- @@ L61-61 verbatim
namespace SmallPeriodicNormalGraph


-- @@ L63-63 verbatim
variable (G : V.SmallPeriodicNormalGraph O)


-- @@ L65-66 verbatim
/-- The time-scaled graph displacement. -/
def displacement (s u : ℝ) : N := normRamp s • G.h u


-- @@ L68-71 verbatim
theorem contDiff_displacement :
    ContDiff ℝ ∞ (fun p : P => G.displacement p.1 p.2) := by
  exact (contDiff_normRamp.comp contDiff_fst).smul
    (G.h_smooth.comp contDiff_snd)


-- @@ L73-81 verbatim
theorem norm_displacement_le (s u : ℝ) :
    ‖G.displacement s u‖ ≤ G.normBound := by
  rw [displacement, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (normRamp_nonneg s)]
  calc
    normRamp s * ‖G.h u‖ ≤ 1 * G.normBound :=
      mul_le_mul (normRamp_le_one s) (G.norm_h_le u)
        (norm_nonneg _) zero_le_one
    _ = G.normBound := one_mul _


-- @@ L83-85 verbatim
/-- The compactly supported fibre perturbation. -/
def perturbation (s u : ℝ) (z : N) : N :=
  (G.bump z) • G.displacement s u


-- @@ L87-89 verbatim
/-- Forward fibre map. -/
def forwardNormal (s u : ℝ) (z : N) : N :=
  z + G.perturbation s u z


-- @@ L91-95 verbatim
theorem contDiff_perturbation :
    ContDiff ℝ ∞
      (fun q : P × N => G.perturbation q.1.1 q.1.2 q.2) := by
  exact (G.bump.contDiff.comp contDiff_snd).smul
    (G.contDiff_displacement.comp contDiff_fst)


-- @@ L97-100 verbatim
theorem contDiff_forwardNormal :
    ContDiff ℝ ∞
      (fun q : P × N => G.forwardNormal q.1.1 q.1.2 q.2) := by
  exact contDiff_snd.add G.contDiff_perturbation


-- @@ L102-105 verbatim
/-- A uniform contraction constant valid for every time and phase. -/
def contractionConstant : ℝ≥0 :=
  ⟨G.normBound * (G.bumpLipschitz : ℝ),
    mul_nonneg G.normBound_nonneg G.bumpLipschitz.coe_nonneg⟩


-- @@ L107-108 verbatim
theorem contractionConstant_lt_one : G.contractionConstant < 1 := by
  exact_mod_cast G.contraction_lt_one


-- @@ L110-126 verbatim
theorem perturbation_lipschitz (s u : ℝ) :
    LipschitzWith G.contractionConstant (G.perturbation s u) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [perturbation, perturbation, dist_eq_norm, ← sub_smul,
    norm_smul, Real.norm_eq_abs]
  have hb := G.bump_lipschitz.dist_le_mul x y
  rw [Real.dist_eq] at hb
  calc
    |G.bump x - G.bump y| * ‖G.displacement s u‖ ≤
        ((G.bumpLipschitz : ℝ) * dist x y) * G.normBound :=
      mul_le_mul hb (G.norm_displacement_le s u)
        (norm_nonneg _) (mul_nonneg G.bumpLipschitz.coe_nonneg (dist_nonneg))
    _ = (G.contractionConstant : ℝ) * dist x y := by
      change (G.bumpLipschitz : ℝ) * dist x y * G.normBound =
        (G.normBound * (G.bumpLipschitz : ℝ)) * dist x y
      ring


-- @@ L128-131 verbatim
/-- Fixed-point operator whose unique fixed point is the inverse image of
`y`. -/
def inverseOperator (s u : ℝ) (y z : N) : N :=
  y - G.perturbation s u z


-- @@ L133-140 verbatim
theorem inverseOperator_contracting (s u : ℝ) (y : N) :
    ContractingWith G.contractionConstant (G.inverseOperator s u y) := by
  refine ⟨G.contractionConstant_lt_one, ?_⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro x z
  simpa [inverseOperator, dist_eq_norm, sub_sub_sub_cancel_left,
    norm_neg, norm_sub_rev] using
    G.perturbation_lipschitz s u |>.dist_le_mul z x


-- @@ L142-145 verbatim
/-- Explicit global inverse, as the canonical Banach fixed point. -/
def inverseNormal (s u : ℝ) (y : N) : N :=
  (G.inverseOperator_contracting s u y).fixedPoint
    (G.inverseOperator s u y)


-- @@ L147-150 verbatim
theorem inverseNormal_fixed (s u : ℝ) (y : N) :
    G.inverseOperator s u y (G.inverseNormal s u y) =
      G.inverseNormal s u y :=
  (G.inverseOperator_contracting s u y).fixedPoint_isFixedPt


-- @@ L152-157 verbatim
theorem forwardNormal_inverseNormal (s u : ℝ) (y : N) :
    G.forwardNormal s u (G.inverseNormal s u y) = y := by
  have h := G.inverseNormal_fixed s u y
  simp only [inverseOperator] at h
  rw [forwardNormal]
  exact (sub_eq_iff_eq_add.mp h).symm


-- @@ L159-165 verbatim
theorem inverseNormal_forwardNormal (s u : ℝ) (z : N) :
    G.inverseNormal s u (G.forwardNormal s u z) = z := by
  symm
  exact (G.inverseOperator_contracting s u
    (G.forwardNormal s u z)).fixedPoint_unique (by
      change z + G.perturbation s u z - G.perturbation s u z = z
      abel)


-- @@ L167-173 verbatim
theorem forwardNormal_bijective (s u : ℝ) :
    Bijective (G.forwardNormal s u) :=
  ⟨fun x y hxy => by
      rw [← G.inverseNormal_forwardNormal s u x,
        ← G.inverseNormal_forwardNormal s u y, hxy],
    fun y => ⟨G.inverseNormal s u y,
      G.forwardNormal_inverseNormal s u y⟩⟩


-- @@ L175-177 verbatim
/-- Total forward map, retaining time and phase as parameters. -/
def totalForward (q : P × N) : P × N :=
  (q.1, G.forwardNormal q.1.1 q.1.2 q.2)


-- @@ L179-181 verbatim
/-- Total inverse with the same retained parameters. -/
def totalInverse (q : P × N) : P × N :=
  (q.1, G.inverseNormal q.1.1 q.1.2 q.2)


-- @@ L183-185 verbatim
theorem total_left_inv : LeftInverse G.totalInverse G.totalForward := by
  rintro ⟨⟨s, u⟩, z⟩
  simp [totalInverse, totalForward, G.inverseNormal_forwardNormal]


-- @@ L187-189 verbatim
theorem total_right_inv : RightInverse G.totalInverse G.totalForward := by
  rintro ⟨⟨s, u⟩, z⟩
  simp [totalInverse, totalForward, G.forwardNormal_inverseNormal]


-- @@ L191-192 verbatim
theorem contDiff_totalForward : ContDiff ℝ ∞ G.totalForward := by
  exact contDiff_fst.prodMk G.contDiff_forwardNormal


-- @@ L194-198 verbatim
theorem contDiff_perturbation_slice (s u : ℝ) :
    ContDiff ℝ ∞ (G.perturbation s u) := by
  have hc : ContDiff ℝ ∞ (fun _ : N => ((s, u) : P)) := contDiff_const
  simpa [Function.comp_def] using G.contDiff_perturbation.comp
    (hc.prodMk contDiff_id)


-- @@ L200-204 verbatim
theorem contDiff_forwardNormal_slice (s u : ℝ) :
    ContDiff ℝ ∞ (G.forwardNormal s u) := by
  have hc : ContDiff ℝ ∞ (fun _ : N => ((s, u) : P)) := contDiff_const
  simpa [Function.comp_def] using G.contDiff_forwardNormal.comp
    (hc.prodMk contDiff_id)


-- @@ L206-212 verbatim
theorem norm_fderiv_perturbation_lt_one (s u : ℝ) (z : N) :
    ‖fderiv ℝ (G.perturbation s u) z‖ < 1 := by
  calc
    ‖fderiv ℝ (G.perturbation s u) z‖ ≤
        (G.contractionConstant : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ (G.perturbation_lipschitz s u)
    _ < 1 := by exact_mod_cast G.contractionConstant_lt_one


-- @@ L214-221 verbatim
theorem fderiv_forwardNormal_eq (s u : ℝ) (z : N) :
    fderiv ℝ (G.forwardNormal s u) z =
      ContinuousLinearMap.id ℝ N +
        fderiv ℝ (G.perturbation s u) z := by
  have hp : DifferentiableAt ℝ (G.perturbation s u) z :=
    (G.contDiff_perturbation_slice s u).differentiable (by simp) z
  change fderiv ℝ (fun w : N => w + G.perturbation s u w) z = _
  exact ((hasFDerivAt_id z).add hp.hasFDerivAt).fderiv


-- @@ L223-231 verbatim
theorem fderiv_forwardNormal_bijective (s u : ℝ) (z : N) :
    Bijective (fderiv ℝ (G.forwardNormal s u) z) := by
  let L : N →L[ℝ] N := fderiv ℝ (G.perturbation s u) z
  have hL : ‖L‖ < 1 := G.norm_fderiv_perturbation_lt_one s u z
  have hu : IsUnit (1 - (-L)) := (Units.oneSub (-L) (by simpa)).isUnit
  rw [G.fderiv_forwardNormal_eq]
  change Bijective ((1 : N →L[ℝ] N) + L)
  simpa [sub_neg_eq_add] using
    (ContinuousLinearMap.isUnit_iff_bijective.mp hu)


-- @@ L233-241 verbatim
theorem fderiv_forwardNormal_isInvertible (s u : ℝ) (z : N) :
    (fderiv ℝ (G.forwardNormal s u) z).IsInvertible := by
  have hb := G.fderiv_forwardNormal_bijective s u z
  let e : N ≃L[ℝ] N := ContinuousLinearEquiv.ofBijective
    (fderiv ℝ (G.forwardNormal s u) z)
    (LinearMap.ker_eq_bot.mpr hb.1)
    (LinearMap.range_eq_top.mpr hb.2)
  refine ⟨e, ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _


-- @@ L243-247 verbatim
/-- The implicit equation for the parameterized inverse.  Its first variable
contains `(time, phase, target)` and its second variable is the unknown source
normal vector. -/
def inverseEquation (q : (P × N) × N) : N :=
  G.forwardNormal q.1.1.1 q.1.1.2 q.2 - q.1.2


-- @@ L249-252 verbatim
theorem contDiff_inverseEquation : ContDiff ℝ ∞ G.inverseEquation := by
  exact (G.contDiff_forwardNormal.comp
    ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).sub
      (contDiff_snd.comp contDiff_fst)


-- @@ L254-256 verbatim
/-- The normal component of the total inverse. -/
def inverseSection (q : P × N) : N :=
  G.inverseNormal q.1.1 q.1.2 q.2


-- @@ L258-274 verbatim
theorem fderiv_inverseEquation_comp_inr (q : P × N) (z : N) :
    (fderiv ℝ G.inverseEquation (q, z)).comp
        (ContinuousLinearMap.inr ℝ (P × N) N) =
      fderiv ℝ (G.forwardNormal q.1.1 q.1.2) z := by
  have htotal :=
    (G.contDiff_inverseEquation.differentiable (by simp) (q, z)).hasFDerivAt
  have hinc : HasFDerivAt (fun w : N => (q, w))
      (ContinuousLinearMap.inr ℝ (P × N) N) z :=
    (hasFDerivAt_const (x := z) q).prodMk (hasFDerivAt_id z)
  have hcomp := htotal.comp z hinc
  have hslice : fderiv ℝ (fun w : N => G.inverseEquation (q, w)) z =
      fderiv ℝ (G.forwardNormal q.1.1 q.1.2) z := by
    simpa [inverseEquation] using
      (fderiv_sub_const (𝕜 := ℝ)
        (f := G.forwardNormal q.1.1 q.1.2) (x := z) q.2)
  rw [← hslice]
  exact hcomp.fderiv.symm


-- @@ L276-280 verbatim
theorem inverseEquation_partial_isInvertible (q : P × N) (z : N) :
    ((fderiv ℝ G.inverseEquation (q, z)).comp
      (ContinuousLinearMap.inr ℝ (P × N) N)).IsInvertible := by
  rw [G.fderiv_inverseEquation_comp_inr q z]
  exact G.fderiv_forwardNormal_isInvertible q.1.1 q.1.2 z


-- @@ L282-310 verbatim
/-- The Banach fixed-point inverse is jointly smooth in time, phase and
target.  The implicit-function theorem supplies a local smooth solution;
global injectivity of every fibre map identifies it with the fixed point. -/
theorem contDiff_inverseSection : ContDiff ℝ ∞ G.inverseSection := by
  rw [contDiff_iff_contDiffAt]
  intro q
  let z : N := G.inverseSection q
  let b : (P × N) × N := (q, z)
  let cdf : ContDiffAt ℝ ∞ G.inverseEquation b :=
    G.contDiff_inverseEquation.contDiffAt
  have hi : ((fderiv ℝ G.inverseEquation b).comp
      (ContinuousLinearMap.inr ℝ (P × N) N)).IsInvertible := by
    simpa [b] using G.inverseEquation_partial_isInvertible q z
  let ψ : P × N → N := cdf.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ q := by
    simpa [ψ, b] using cdf.contDiffAt_implicitFunction (by simp) hi
  have hbzero : G.inverseEquation b = 0 := by
    simp [b, z, inverseSection, inverseEquation,
      G.forwardNormal_inverseNormal]
  have heq : G.inverseSection =ᶠ[𝓝 q] ψ := by
    have himp := cdf.eventually_apply_implicitFunction (by simp) hi
    filter_upwards [himp] with q' hq'
    have hz' : G.inverseEquation (q', ψ q') = 0 := by
      rw [hq', hbzero]
    have hfwd : G.forwardNormal q'.1.1 q'.1.2 (ψ q') = q'.2 := by
      exact sub_eq_zero.mp hz'
    show G.inverseNormal q'.1.1 q'.1.2 q'.2 = ψ q'
    rw [← hfwd, G.inverseNormal_forwardNormal]
  exact hψ.congr_of_eventuallyEq heq


-- @@ L312-314 verbatim
theorem contDiff_totalInverse : ContDiff ℝ ∞ G.totalInverse := by
  change ContDiff ℝ ∞ (fun q : P × N => (q.1, G.inverseSection q))
  exact contDiff_fst.prodMk G.contDiff_inverseSection


-- @@ L316-319 verbatim
/-- A single radius containing the support of both the forward map and its
inverse.  The extra `normBound` accounts for how far an inverse image may
move before reaching the support of the bump. -/
def supportRadius : ℝ := G.bump.rOut + G.normBound


-- @@ L321-323 verbatim
theorem supportRadius_lt_tube : G.supportRadius <
    (V.globalSmoothOrbitTube O).radius :=
  G.support_lt_tube


-- @@ L325-333 verbatim
theorem norm_perturbation_le (s u : ℝ) (z : N) :
    ‖G.perturbation s u z‖ ≤ G.normBound := by
  rw [perturbation, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg G.bump.nonneg]
  calc
    G.bump z * ‖G.displacement s u‖ ≤ 1 * G.normBound :=
      mul_le_mul G.bump.le_one (G.norm_displacement_le s u)
        (norm_nonneg _) zero_le_one
    _ = G.normBound := one_mul _


-- @@ L335-339 verbatim
theorem forwardNormal_eq_self_of_rOut_le_norm (s u : ℝ) (z : N)
    (hz : G.bump.rOut ≤ ‖z‖) : G.forwardNormal s u z = z := by
  have hb : G.bump z = 0 := G.bump.zero_of_le_dist (by
    simpa [dist_zero_right] using hz)
  simp [forwardNormal, perturbation, hb]


-- @@ L341-357 verbatim
theorem forwardNormal_mem_tube (s u : ℝ) (z : N)
    (hz : z ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    G.forwardNormal s u z ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius := by
  rw [mem_ball, dist_zero_right] at hz ⊢
  by_cases hout : G.bump.rOut ≤ ‖z‖
  · rwa [G.forwardNormal_eq_self_of_rOut_le_norm s u z hout]
  · rw [forwardNormal]
    calc
      ‖z + G.perturbation s u z‖ ≤
          ‖z‖ + ‖G.perturbation s u z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + G.normBound :=
        add_le_add_right (G.norm_perturbation_le s u z) _
      _ < G.bump.rOut + G.normBound := by
        linarith [lt_of_not_ge hout]
      _ < (V.globalSmoothOrbitTube O).radius := G.support_lt_tube


-- @@ L359-379 verbatim
theorem inverseNormal_eq_self_of_supportRadius_le_norm (s u : ℝ) (y : N)
    (hy : G.supportRadius ≤ ‖y‖) : G.inverseNormal s u y = y := by
  let x : N := G.inverseNormal s u y
  have hxout : G.bump.rOut ≤ ‖x‖ := by
    by_contra hnot
    have hxlt : ‖x‖ < G.bump.rOut := lt_of_not_ge hnot
    have hylt : ‖y‖ < G.supportRadius := by
      rw [← G.forwardNormal_inverseNormal s u y]
      rw [forwardNormal]
      calc
        ‖x + G.perturbation s u x‖ ≤
            ‖x‖ + ‖G.perturbation s u x‖ := norm_add_le _ _
        _ ≤ ‖x‖ + G.normBound :=
          add_le_add_right (G.norm_perturbation_le s u x) _
        _ < G.bump.rOut + G.normBound := by linarith
        _ = G.supportRadius := rfl
    exact (not_lt_of_ge hy) hylt
  calc
    G.inverseNormal s u y = G.forwardNormal s u x := by
      rw [G.forwardNormal_eq_self_of_rOut_le_norm s u x hxout]
    _ = y := G.forwardNormal_inverseNormal s u y


-- @@ L381-402 verbatim
theorem inverseNormal_mem_tube (s u : ℝ) (y : N)
    (hy : y ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    G.inverseNormal s u y ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius := by
  rw [mem_ball, dist_zero_right] at hy ⊢
  by_contra hnot
  have hxR : (V.globalSmoothOrbitTube O).radius ≤
      ‖G.inverseNormal s u y‖ := le_of_not_gt hnot
  have hrOutR : G.bump.rOut <
      (V.globalSmoothOrbitTube O).radius := by
    calc
      G.bump.rOut ≤ G.bump.rOut + G.normBound :=
        le_add_of_nonneg_right G.normBound_nonneg
      _ < (V.globalSmoothOrbitTube O).radius := G.support_lt_tube
  have hxout : G.bump.rOut ≤ ‖G.inverseNormal s u y‖ :=
    (le_of_lt hrOutR).trans hxR
  have hyx : y = G.inverseNormal s u y := by
    exact (G.forwardNormal_inverseNormal s u y).symm.trans
      (G.forwardNormal_eq_self_of_rOut_le_norm s u _ hxout)
  rw [← hyx] at hxR
  exact (not_lt_of_ge hxR) hy


-- @@ L404-407 verbatim
/-- Reassociate `(time, (phase, normal))` into the parameter layout used by
the analytic construction above. -/
def reassocInput (p : ℝ × (ℝ × N)) : P × N :=
  ((p.1, p.2.1), p.2.2)


-- @@ L409-411 verbatim
theorem contDiff_reassocInput : ContDiff ℝ ∞ (reassocInput (n := n)) := by
  exact (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk
    (contDiff_snd.comp contDiff_snd)


-- @@ L413-415 verbatim
/-- Real-phase lift of the forward tube-coordinate isotopy. -/
def forwardLift (s : ℝ) (q : ℝ × N) : ℝ × N :=
  (q.1, G.forwardNormal s q.1 q.2)


-- @@ L417-419 verbatim
/-- Real-phase lift of the inverse tube-coordinate isotopy. -/
def inverseLift (s : ℝ) (q : ℝ × N) : ℝ × N :=
  (q.1, G.inverseNormal s q.1 q.2)


-- @@ L421-424 verbatim
theorem contDiff_joint_forwardLift :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × N) => G.forwardLift p.1 p.2) := by
  exact (contDiff_fst.comp contDiff_snd).prodMk
    (G.contDiff_forwardNormal.comp contDiff_reassocInput)


-- @@ L426-429 verbatim
theorem contDiff_joint_inverseLift :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × N) => G.inverseLift p.1 p.2) := by
  exact (contDiff_fst.comp contDiff_snd).prodMk
    (G.contDiff_inverseSection.comp contDiff_reassocInput)


-- @@ L431-433 verbatim
theorem forwardNormal_add_one (s u : ℝ) (z : N) :
    G.forwardNormal s (u + 1) z = G.forwardNormal s u z := by
  simp [forwardNormal, perturbation, displacement, G.h_periodic u]


-- @@ L435-439 verbatim
theorem inverseNormal_add_one (s u : ℝ) (z : N) :
    G.inverseNormal s (u + 1) z = G.inverseNormal s u z := by
  apply (G.forwardNormal_bijective s (u + 1)).1
  rw [G.forwardNormal_inverseNormal,
    G.forwardNormal_add_one, G.forwardNormal_inverseNormal]


-- @@ L441-443 verbatim
theorem periodic_forwardNormal (s : ℝ) (z : N) :
    Function.Periodic (fun u => G.forwardNormal s u z) 1 :=
  fun u => G.forwardNormal_add_one s u z


-- @@ L445-447 verbatim
theorem periodic_inverseNormal (s : ℝ) (z : N) :
    Function.Periodic (fun u => G.inverseNormal s u z) 1 :=
  fun u => G.inverseNormal_add_one s u z


-- @@ L449-451 verbatim
/-- Descent of the forward lift to the phase circle. -/
def forwardQuot (s : ℝ) (q : C × N) : C × N :=
  (q.1, (G.periodic_forwardNormal s q.2).lift q.1)


-- @@ L453-455 verbatim
/-- Descent of the inverse lift to the phase circle. -/
def inverseQuot (s : ℝ) (q : C × N) : C × N :=
  (q.1, (G.periodic_inverseNormal s q.2).lift q.1)


-- @@ L457-461 verbatim
@[simp] theorem forwardQuot_coe (s u : ℝ) (z : N) :
    G.forwardQuot s ((u : C), z) =
      (((G.forwardLift s (u, z)).1 : C),
        (G.forwardLift s (u, z)).2) := by
  rfl


-- @@ L463-467 verbatim
@[simp] theorem inverseQuot_coe (s u : ℝ) (z : N) :
    G.inverseQuot s ((u : C), z) =
      (((G.inverseLift s (u, z)).1 : C),
        (G.inverseLift s (u, z)).2) := by
  rfl


-- @@ L469-472 verbatim
theorem forwardNormal_zero (u : ℝ) (z : N) :
    G.forwardNormal 0 u z = z := by
  simp [forwardNormal, perturbation, displacement,
    normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num)]


-- @@ L474-477 verbatim
theorem forwardLift_zero : G.forwardLift 0 = id := by
  funext q
  rcases q with ⟨u, z⟩
  simp [forwardLift, G.forwardNormal_zero]


-- @@ L479-482 verbatim
theorem forwardLift_leftInverse (s : ℝ) :
    LeftInverse (G.inverseLift s) (G.forwardLift s) := by
  rintro ⟨u, z⟩
  simp [forwardLift, inverseLift, G.inverseNormal_forwardNormal]


-- @@ L484-487 verbatim
theorem forwardLift_rightInverse (s : ℝ) :
    RightInverse (G.inverseLift s) (G.forwardLift s) := by
  rintro ⟨u, z⟩
  simp [forwardLift, inverseLift, G.forwardNormal_inverseNormal]


-- @@ L489-494 verbatim
theorem forwardLift_mem_tube (s u : ℝ) (z : N)
    (hz : z ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    (G.forwardLift s (u, z)).2 ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius :=
  G.forwardNormal_mem_tube s u z hz


-- @@ L496-501 verbatim
theorem inverseLift_mem_tube (s u : ℝ) (z : N)
    (hz : z ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius) :
    (G.inverseLift s (u, z)).2 ∈ Metric.ball (0 : N)
      (V.globalSmoothOrbitTube O).radius :=
  G.inverseNormal_mem_tube s u z hz


-- @@ L503-508 verbatim
theorem forwardLift_collar (s u : ℝ) (z : N)
    (hz : G.supportRadius ≤ ‖z‖) :
    G.forwardLift s (u, z) = (u, z) := by
  have hout : G.bump.rOut ≤ ‖z‖ :=
    (le_add_of_nonneg_right G.normBound_nonneg).trans hz
  simp [forwardLift, G.forwardNormal_eq_self_of_rOut_le_norm s u z hout]


-- @@ L510-513 verbatim
theorem inverseLift_collar (s u : ℝ) (z : N)
    (hz : G.supportRadius ≤ ‖z‖) :
    G.inverseLift s (u, z) = (u, z) := by
  simp [inverseLift, G.inverseNormal_eq_self_of_supportRadius_le_norm s u z hz]


-- @@ L515-535 verbatim
/-- The complete coordinate-level isotopy contract consumed by the ambient
conjugation theorem. -/
def toPeriodicTubeCoordinateIsotopy :
    V.PeriodicTubeCoordinateIsotopy O where
  supportRadius := G.supportRadius
  supportRadius_lt := G.supportRadius_lt_tube
  forwardLift := G.forwardLift
  inverseLift := G.inverseLift
  forwardQuot := G.forwardQuot
  inverseQuot := G.inverseQuot
  forwardLift_smooth := G.contDiff_joint_forwardLift
  inverseLift_smooth := G.contDiff_joint_inverseLift
  forwardQuot_coe := G.forwardQuot_coe
  inverseQuot_coe := G.inverseQuot_coe
  forward_zero := G.forwardLift_zero
  left_inv := G.forwardLift_leftInverse
  right_inv := G.forwardLift_rightInverse
  forward_mem_tube := G.forwardLift_mem_tube
  inverse_mem_tube := G.inverseLift_mem_tube
  forward_collar := G.forwardLift_collar
  inverse_collar := G.inverseLift_collar


-- @@ L537-539 verbatim
theorem bump_zero : G.bump (0 : N) = 1 := by
  apply G.bump.one_of_mem_closedBall
  simpa [mem_closedBall] using G.bump.rIn_pos.le


-- @@ L541-547 verbatim
/-- At the endpoint, the zero section is sent exactly to the prescribed
normal graph. -/
theorem forwardLift_one_zero (u : ℝ) :
    G.forwardLift 1 (u, (0 : N)) = (u, G.h u) := by
  simp [forwardLift, forwardNormal, perturbation, displacement, G.bump_zero,
    normRamp_of_three_quarter_le
      (show (3 / 4 : ℝ) ≤ 1 by norm_num)]


-- @@ L549-553 verbatim
/-- The requested genuine ambient isotopy, obtained by conjugating the
coordinate construction through the already-built global orbit tube and
extending by the identity across its outer collar. -/
def toSmoothAmbientIsotopy : SmoothAmbientIsotopy n :=
  G.toPeriodicTubeCoordinateIsotopy.toSmoothAmbientIsotopy


-- @@ L555-569 verbatim
/-- Concrete endpoint statement in real-phase tube coordinates. -/
theorem toSmoothAmbientIsotopy_forward_orbit_zero (u : ℝ) :
    G.toSmoothAmbientIsotopy.forward 1
        (V.orbitTubeLift O (u, (0 : N))) =
      V.orbitTubeLift O (u, G.h u) := by
  let A : V.PeriodicTubeCoordinateIsotopy O :=
    G.toPeriodicTubeCoordinateIsotopy
  have hq : ((u : C), (0 : N)) ∈ A.tubeDomain := by
    exact ⟨mem_univ _, mem_ball_self
      (V.globalSmoothOrbitTube O).radius_pos⟩
  change A.ambientForward 1 (V.orbitTubeLift O (u, (0 : N))) = _
  rw [← V.orbitTube_coe O u (0 : N),
    A.ambientForward_orbitTube 1 ((u : C), (0 : N)) hq]
  change V.orbitTube O (G.forwardQuot 1 ((u : C), (0 : N))) = _
  rw [G.forwardQuot_coe, G.forwardLift_one_zero, V.orbitTube_coe]


-- @@ L571-571 verbatim
end SmallPeriodicNormalGraph

-- @@ L572-572 verbatim
end TamedField

-- @@ L573-573 verbatim
end Submission
