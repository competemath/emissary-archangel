import Mathlib
import Submission.PTEndpointValueChange
import Submission.BridgeSign
import Submission.MorseLedgerNormalization
import Submission.EndpointDelta


-- @@ L7-38 verbatim
/-!
# Two-sheet PT splice infrastructure

A single signed endpoint collapse remembers only its northern sheet.  The
correct relative Pontryagin--Thom input therefore consists of two lanes: one
for `S`, and one for `S.neg`.  This file implements the reusable geometry and
categorical splice for those two lanes.

First, the existing relative smooth approximation of a cubical homotopy is
turned into an actual `CollaredSphereHomotopy`; this includes an exact
south-pole exterior, not merely vanishing horizontal coordinates.  Second, a
patched endpoint cobordism is spliced to the transverse middle and to the
reverse patch at the other end.  The public splice contract asks for actual
signed endpoint connectors.  Such a connector can in particular be built
from a homotopy of defining maps followed by sign interpolation on its common
fiber; it does not ask that two globally different defining maps be literally
equal.

For comparison, the file retains an auxiliary exact-presentation lane and
proves that its equality field forces the original defining map to be
eventually constant.  Thus exact equality cannot be obtained for an arbitrary
presentation merely by choosing Sard values or compactly supported cutoffs.
Exact equality of the two sign functions is neither needed nor natural:
normalization changes a vertical coordinate by a positive factor.  We compare
only sign patterns on the relevant fibers.  For the negative lane the
resulting cobordism is negated back, so both outputs have the original endpoint
signs.

This does not assert the false one-loop classification statement.  A public
two-sheet datum requires both lanes and produces two independently checked
signed cobordisms between the same endpoints.
-/


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
namespace Submission


-- @@ L44-44 verbatim
open Set Function Metric Topology.Homotopy MeasureTheory

-- @@ L45-45 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L47-47 verbatim
variable {n : ℕ}


-- @@ L49-49 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L50-50 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L51-51 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L53-53 verbatim
/-! ## A smooth cubical cobordism approximation is a collared sphere homotopy -/


-- @@ L55-58 verbatim
variable
  {p₀ p₁ : Ω^ (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}
  {a₀ : Approximation p₀} {a₁ : Approximation p₁}


-- @@ L60-60 verbatim
namespace CobApproximationPT


-- @@ L62-66 verbatim
/-- The normalized plateaued map as an honest unit-sphere-valued map on
Euclidean space-time. -/
def sphereMap (c : Submission.CobApproximation a₀ a₁) (v : A) : UnitSphere E :=
  ⟨nprepCob c (WithLp.ofLp v),
    mem_sphere_zero_iff_norm.mpr (norm_nprepCob c (WithLp.ofLp v))⟩


-- @@ L68-70 verbatim
@[simp] lemma sphere_coe (c : Submission.CobApproximation a₀ a₁) (v : A) :
    (sphereMap c v : E) = nprepCob c (WithLp.ofLp v) :=
  rfl


-- @@ L72-75 verbatim
lemma contDiff_sphere_coe (c : Submission.CobApproximation a₀ a₁) :
    ContDiff ℝ ∞ fun v => (sphereMap c v : E) :=
  (contDiff_nprepCob c).comp
    (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℝ).contDiff


-- @@ L77-109 verbatim
/-- Outside the clamped spatial cube the plateaued map is exactly the south
pole, not only horizontally zero. -/
lemma sphere_eq_south_of_outside_cube
    (c : Submission.CobApproximation a₀ a₁) {v : A}
    (hv : ∃ j, piInit (WithLp.ofLp v) j ≤ 0 ∨
      1 ≤ piInit (WithLp.ofLp v) j) :
    sphereMap c v = southPole n := by
  have hdist : dist (c.rawC (WithLp.ofLp v)) (-eLast n) < 1 / 8 :=
    c.rawC_south (WithLp.ofLp v) hv
  have hnorm : ‖(-eLast n : E)‖ = 1 := by
    rw [norm_neg, norm_eLast]
  have h2 : ‖nrawCob c (WithLp.ofLp v) - -eLast n‖ ≤
      2 * ‖c.rawC (WithLp.ofLp v) - -eLast n‖ :=
    norm_normalize_sub_le (c.rawC_ne_zero _) hnorm
  have h3 : ‖nrawCob c (WithLp.ofLp v) - -eLast n‖ ≤ 1 / 4 := by
    rw [dist_eq_norm] at hdist
    linarith
  have h4 : |vertC (nrawCob c (WithLp.ofLp v)) + 1| ≤ 1 / 4 := by
    have hcoord := abs_coord_le_norm
      (nrawCob c (WithLp.ofLp v) - -eLast n) (Fin.last n)
    have hval : (nrawCob c (WithLp.ofLp v) - -eLast n) (Fin.last n) =
        vertC (nrawCob c (WithLp.ofLp v)) + 1 := by
      simp [vertC, eLast]
    rw [hval] at hcoord
    exact hcoord.trans h3
  have hvert : vertC (nrawCob c (WithLp.ofLp v)) ≤ -(1 / 2) := by
    rcases abs_le.mp h4 with ⟨-, hhi⟩
    linarith
  have hpraw : prawCob c (WithLp.ofLp v) = -eLast n :=
    plateauAux_of_le hvert
  apply Subtype.ext
  rw [sphere_coe, nprepCob, hpraw, southPole_coe, norm_neg, norm_eLast]
  simp


-- @@ L111-144 verbatim
/-- A point whose spatial norm is larger than `n+1` lies outside the clamped
unit cube in at least one coordinate. -/
lemma outside_cube_of_spatial_norm_gt
    {v : A} (hv : (n : ℝ) + 1 < ‖initCLM (n + 1) v‖) :
    ∃ j, piInit (WithLp.ofLp v) j ≤ 0 ∨
      1 ≤ piInit (WithLp.ofLp v) j := by
  by_contra hnot
  rw [not_exists] at hnot
  have hcoord : ∀ j : Fin (n + 1),
      |initCLM (n + 1) v j| ≤ 1 := by
    intro j
    have hj := hnot j
    rw [not_or, not_le, not_le] at hj
    have hpi : piInit (WithLp.ofLp v) j = initCLM (n + 1) v j := rfl
    rw [hpi] at hj
    exact abs_le.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩
  have hsq : ‖initCLM (n + 1) v‖ ^ 2 =
      ∑ j, initCLM (n + 1) v j ^ 2 := norm_sq_eq_sum _
  have hsum : (∑ j, initCLM (n + 1) v j ^ 2) ≤
      ∑ _j : Fin (n + 1), (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    have hj := hcoord j
    nlinarith [abs_nonneg (initCLM (n + 1) v j),
      sq_abs (initCLM (n + 1) v j)]
  have hone : (∑ _j : Fin (n + 1), (1 : ℝ)) = n + 1 := by simp
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnormsq : ‖initCLM (n + 1) v‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    calc
      ‖initCLM (n + 1) v‖ ^ 2 =
          ∑ j, initCLM (n + 1) v j ^ 2 := hsq
      _ ≤ n + 1 := hsum.trans_eq hone
      _ ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (initCLM (n + 1) v)]


-- @@ L146-153 verbatim
lemma sphere_exterior_south (c : Submission.CobApproximation a₀ a₁) :
    ∃ R : ℝ, ∀ v : A,
    R < ‖initCLM (n + 1) v‖ →
      sphereMap c v = southPole n := by
  refine ⟨n + 1, ?_⟩
  intro v hv
  exact sphere_eq_south_of_outside_cube c
    (outside_cube_of_spatial_norm_gt (by simpa using hv))


-- @@ L155-162 verbatim
lemma sphere_collar_zero (c : Submission.CobApproximation a₀ a₁)
    (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    sphereMap c (spaceTime x t) = sphereMap c (spaceTime x 0) := by
  apply Subtype.ext
  simp only [sphere_coe]
  rw [nprepCob_left c (by rw [piTime_ofLp_spaceTime]; exact ht),
    nprepCob_left c (by rw [piTime_ofLp_spaceTime]; norm_num),
    piInit_ofLp_spaceTime, piInit_ofLp_spaceTime]


-- @@ L164-171 verbatim
lemma sphere_collar_one (c : Submission.CobApproximation a₀ a₁)
    (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    sphereMap c (spaceTime x t) = sphereMap c (spaceTime x 1) := by
  apply Subtype.ext
  simp only [sphere_coe]
  rw [nprepCob_right c (by rw [piTime_ofLp_spaceTime]; exact ht),
    nprepCob_right c (by rw [piTime_ofLp_spaceTime]; norm_num),
    piInit_ofLp_spaceTime, piInit_ofLp_spaceTime]


-- @@ L173-185 verbatim
/-- The exact `CollaredSphereHomotopy` extracted from the smooth relative
approximation. -/
def toCollaredSphereHomotopy (c : Submission.CobApproximation a₀ a₁) :
    CollaredSphereHomotopy n where
  sphere := sphereMap c
  smooth := contDiff_sphere_coe c
  exterior_south := sphere_exterior_south c
  collar_zero := by
    intro x t ht
    exact sphere_collar_zero c x ht
  collar_one := by
    intro x t ht
    exact sphere_collar_one c x ht


-- @@ L187-196 verbatim
/-- The incoming endpoint of the extracted sphere homotopy is exactly the
usual plateaued bridge horizontal map of the incoming approximation. -/
lemma sourceHorizontal_eq_bridgeHMapE
    (c : Submission.CobApproximation a₀ a₁) (x : E) :
    (toCollaredSphereHomotopy c).sourceHorizontal x = bridgeHMapE a₀ x := by
  change initCLM n (nprepCob c (WithLp.ofLp (spaceTime x 0))) =
    bridgeHMap a₀ (WithLp.ofLp x)
  rw [nprepCob_left c (by rw [piTime_ofLp_spaceTime]; norm_num),
    piInit_ofLp_spaceTime]
  rfl


-- @@ L198-206 verbatim
/-- Outgoing counterpart of `sourceHorizontal_eq_bridgeHMapE`. -/
lemma targetHorizontal_eq_bridgeHMapE
    (c : Submission.CobApproximation a₀ a₁) (x : E) :
    (toCollaredSphereHomotopy c).targetHorizontal x = bridgeHMapE a₁ x := by
  change initCLM n (nprepCob c (WithLp.ofLp (spaceTime x 1))) =
    bridgeHMap a₁ (WithLp.ofLp x)
  rw [nprepCob_right c (by rw [piTime_ofLp_spaceTime]; norm_num),
    piInit_ofLp_spaceTime]
  rfl


-- @@ L208-215 verbatim
lemma isRegularValue_source_bridgeHMapE
    (c : Submission.CobApproximation a₀ a₁) {y : F}
    (hreg : IsRegularValue (toCollaredSphereHomotopy c).horizontal y) :
    IsRegularValue (bridgeHMapE a₀) y := by
  have hsource := (toCollaredSphereHomotopy c).isRegularValue_source hreg
  have hfun : (toCollaredSphereHomotopy c).sourceHorizontal = bridgeHMapE a₀ :=
    funext (sourceHorizontal_eq_bridgeHMapE c)
  rwa [hfun] at hsource


-- @@ L217-224 verbatim
lemma isRegularValue_target_bridgeHMapE
    (c : Submission.CobApproximation a₀ a₁) {y : F}
    (hreg : IsRegularValue (toCollaredSphereHomotopy c).horizontal y) :
    IsRegularValue (bridgeHMapE a₁) y := by
  have htarget := (toCollaredSphereHomotopy c).isRegularValue_target hreg
  have hfun : (toCollaredSphereHomotopy c).targetHorizontal = bridgeHMapE a₁ :=
    funext (targetHorizontal_eq_bridgeHMapE c)
  rwa [hfun] at htarget


-- @@ L226-238 verbatim
/-- The induced incoming level-set presentation is literally the canonical
bridge presentation, modulo proof irrelevance of its regularity fields. -/
lemma sourceLevelSet_eq_bridgeFLS
    (c : Submission.CobApproximation a₀ a₁) (y : F) (hy0 : y ≠ 0)
    (hreg : IsRegularValue (toCollaredSphereHomotopy c).horizontal y) :
    (toCollaredSphereHomotopy c).sourceLevelSet y hy0 hreg =
      bridgeFLS a₀ y hy0
        (isRegularValue_source_bridgeHMapE c hreg) := by
  apply FramedLevelSet.eq_of_g_eq
  funext x
  change (toCollaredSphereHomotopy c).sourceHorizontal x - y =
    bridgeHMapE a₀ x - y
  rw [sourceHorizontal_eq_bridgeHMapE]


-- @@ L240-251 verbatim
/-- Outgoing induced presentation equals the outgoing bridge presentation. -/
lemma targetLevelSet_eq_bridgeFLS
    (c : Submission.CobApproximation a₀ a₁) (y : F) (hy0 : y ≠ 0)
    (hreg : IsRegularValue (toCollaredSphereHomotopy c).horizontal y) :
    (toCollaredSphereHomotopy c).targetLevelSet y hy0 hreg =
      bridgeFLS a₁ y hy0
        (isRegularValue_target_bridgeHMapE c hreg) := by
  apply FramedLevelSet.eq_of_g_eq
  funext x
  change (toCollaredSphereHomotopy c).targetHorizontal x - y =
    bridgeHMapE a₁ x - y
  rw [targetHorizontal_eq_bridgeHMapE]


-- @@ L253-268 verbatim
/-- The induced incoming sign is exactly the canonical bridge sign. -/
lemma sourceSign_heq_bridgeFiberSignOf
    (c : Submission.CobApproximation a₀ a₁) (y : F) (hy0 : y ≠ 0)
    (hreg : IsRegularValue (toCollaredSphereHomotopy c).horizontal y)
    (hylt : ‖y‖ < 1) :
    HEq ((toCollaredSphereHomotopy c).sourceSign y hy0 hreg hylt)
      (bridgeFiberSignOf a₀ y hy0
        (isRegularValue_source_bridgeHMapE c hreg) hylt) := by
  apply FiberSign.heq_of_eq_toFun
    (sourceLevelSet_eq_bridgeFLS c y hy0 hreg)
  apply heq_of_eq
  funext x
  change vertC (nprepCob c (WithLp.ofLp (spaceTime x 0))) =
    vertC (nprep a₀ (WithLp.ofLp x))
  rw [nprepCob_left c (by rw [piTime_ofLp_spaceTime]; norm_num),
    piInit_ofLp_spaceTime]


-- @@ L270-285 verbatim
/-- Outgoing induced sign equals the outgoing canonical bridge sign. -/
lemma targetSign_heq_bridgeFiberSignOf
    (c : Submission.CobApproximation a₀ a₁) (y : F) (hy0 : y ≠ 0)
    (hreg : IsRegularValue (toCollaredSphereHomotopy c).horizontal y)
    (hylt : ‖y‖ < 1) :
    HEq ((toCollaredSphereHomotopy c).targetSign y hy0 hreg hylt)
      (bridgeFiberSignOf a₁ y hy0
        (isRegularValue_target_bridgeHMapE c hreg) hylt) := by
  apply FiberSign.heq_of_eq_toFun
    (targetLevelSet_eq_bridgeFLS c y hy0 hreg)
  apply heq_of_eq
  funext x
  change vertC (nprepCob c (WithLp.ofLp (spaceTime x 1))) =
    vertC (nprep a₁ (WithLp.ofLp x))
  rw [nprepCob_right c (by rw [piTime_ofLp_spaceTime]; norm_num),
    piInit_ofLp_spaceTime]


-- @@ L287-287 verbatim
end CobApproximationPT


-- @@ L289-295 verbatim
/-- A cubical homotopy between smooth approximation representatives therefore
produces a smooth, exact-collared, exterior-south sphere homotopy. -/
theorem exists_collaredSphereHomotopy_of_homotopic
    (hpq : GenLoop.Homotopic a₀.representative a₁.representative) :
    Nonempty (CollaredSphereHomotopy n) := by
  obtain ⟨c⟩ := exists_cobApproximation hpq
  exact ⟨CobApproximationPT.toCollaredSphereHomotopy c⟩


-- @@ L297-297 verbatim
/-! ## Retyping signed endpoints along exact presentation identifications -/


-- @@ L299-299 verbatim
namespace SignedFramedLevelCobordism


-- @@ L301-303 verbatim
variable {X₀ X₁ Y₀ Y₁ : FramedLevelSet n}
  {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  {T₀ : FiberSign Y₀} {T₁ : FiberSign Y₁}


-- @@ L305-317 verbatim
/-- Change only the endpoint types of a signed cobordism, using exact equality
of the presentations and heterogeneous equality of the labels. -/
def retypeEndpoints (C : SignedFramedLevelCobordism S₀ S₁)
    (h₀ : X₀ = Y₀) (h₁ : X₁ = Y₁)
    (hs₀ : HEq S₀ T₀) (hs₁ : HEq S₁ T₁) :
    SignedFramedLevelCobordism T₀ T₁ := by
  subst Y₀
  subst Y₁
  have hs₀' : S₀ = T₀ := eq_of_heq hs₀
  have hs₁' : S₁ = T₁ := eq_of_heq hs₁
  subst T₀
  subst T₁
  exact C


-- @@ L319-319 verbatim
end SignedFramedLevelCobordism


-- @@ L321-321 verbatim
/-! ## Transporting endpoint signs along a presentation equality -/


-- @@ L323-323 verbatim
namespace FiberSign


-- @@ L325-325 verbatim
variable {X Y : FramedLevelSet n}


-- @@ L327-329 verbatim
/-- Transport a sign label along an equality of its framed presentation. -/
def transport (hXY : X = Y) (S : FiberSign X) : FiberSign Y :=
  hXY ▸ S


-- @@ L331-333 verbatim
@[simp] theorem transport_rfl (S : FiberSign X) :
    S.transport rfl = S :=
  rfl


-- @@ L335-339 verbatim
@[simp] theorem transport_apply (hXY : X = Y) (S : FiberSign X)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    S.transport hXY x = S x := by
  subst Y
  rfl


-- @@ L341-341 verbatim
end FiberSign


-- @@ L343-354 verbatim
/-- Presentation equality plus equality of sign *patterns* on the common
fiber gives an actual signed cylinder.  This is the correct replacement for
global `HEq` of sign functions: multiplying a label by a positive smooth
function does not change the signed cobordism endpoint. -/
def signedEndpointConnector
    {X Y : FramedLevelSet n} (S : FiberSign X) (T : FiberSign Y)
    (hXY : X = Y)
    (hpos : ∀ x ∈ Y.fiber,
      (0 < S.transport hXY x ↔ 0 < T x)) :
    SignedFramedLevelCobordism S T := by
  subst Y
  exact signInterpolationCobordism S T hpos


-- @@ L356-366 verbatim
/-- A homotopy of defining maps with common regular fiber, followed by sign
interpolation on that fiber, is an endpoint connector without any exact
presentation equality. -/
def signedEndpointConnectorOfDefiningMapHomotopy
    {X Y : FramedLevelSet n} (D : DefiningMapHomotopy X Y)
    (S : FiberSign X) (T : FiberSign Y)
    (hpos : ∀ x ∈ Y.fiber,
      (0 < S.restrict D.fiber_subset x ↔ 0 < T x)) :
    SignedFramedLevelCobordism S T :=
  SignedFramedLevelCobordism.trans (D.signedCobordism S)
    (signInterpolationCobordism (S.restrict D.fiber_subset) T hpos)


-- @@ L368-379 verbatim
/-- A positive pointwise rescaling of a transported label has the same sign
pattern, and hence supplies the hypothesis of `signedEndpointConnector`. -/
lemma transported_signPattern_of_pos_smul
    {X Y : FramedLevelSet n} (S : FiberSign X) (T : FiberSign Y)
    (hXY : X = Y) (q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hq : ∀ x, 0 < q x)
    (hfun : ∀ x, T x = q x * S.transport hXY x) :
    ∀ x ∈ Y.fiber, (0 < S.transport hXY x ↔ 0 < T x) := by
  intro x _
  rw [hfun x]
  exact ⟨fun hx => mul_pos (hq x) hx,
    fun hx => by nlinarith [hq x]⟩


-- @@ L381-392 verbatim
/-- A compactly supported real function vanishes outside some norm ball. -/
lemma exists_eq_zero_of_norm_gt_of_hasCompactSupport
    {f : E → ℝ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, ∀ x : E, R < ‖x‖ → f x = 0 := by
  obtain ⟨r, hr⟩ := hf.isBounded.subset_closedBall (0 : E)
  refine ⟨r, ?_⟩
  intro x hx
  by_contra hne
  have hxt : x ∈ tsupport f := subset_tsupport f hne
  have hball := hr hxt
  rw [mem_closedBall, dist_zero_right] at hball
  exact (not_lt_of_ge hball) hx


-- @@ L394-394 verbatim
namespace CollaredSphereHomotopy


-- @@ L396-407 verbatim
/-- The incoming horizontal slice is exactly zero at spatial infinity. -/
lemma eventually_sourceHorizontal_eq_zero (H : CollaredSphereHomotopy n) :
    ∃ R : ℝ, ∀ x : E, R < ‖x‖ → H.sourceHorizontal x = 0 := by
  obtain ⟨R, hR⟩ := H.exterior_south
  refine ⟨R, ?_⟩
  intro x hx
  have hfar : R < ‖initCLM (n + 1) (spaceTime x 0)‖ := by
    rw [initCLM_spaceTime]
    exact hx
  have hsouth := hR (spaceTime x 0) hfar
  rw [sourceHorizontal, horizontal, hsouth, southPole_coe, map_neg,
    initCLM_eLast, neg_zero]


-- @@ L409-420 verbatim
/-- The outgoing horizontal slice is exactly zero at spatial infinity. -/
lemma eventually_targetHorizontal_eq_zero (H : CollaredSphereHomotopy n) :
    ∃ R : ℝ, ∀ x : E, R < ‖x‖ → H.targetHorizontal x = 0 := by
  obtain ⟨R, hR⟩ := H.exterior_south
  refine ⟨R, ?_⟩
  intro x hx
  have hfar : R < ‖initCLM (n + 1) (spaceTime x 1)‖ := by
    rw [initCLM_spaceTime]
    exact hx
  have hsouth := hR (spaceTime x 1) hfar
  rw [targetHorizontal, horizontal, hsouth, southPole_coe, map_neg,
    initCLM_eLast, neg_zero]


-- @@ L422-422 verbatim
end CollaredSphereHomotopy


-- @@ L424-424 verbatim
/-! ## One patched transverse lane -/


-- @@ L426-426 verbatim
namespace FiberSign.PTCutoff


-- @@ L428-428 verbatim
section CommonTwoSheetLocalizer


-- @@ L430-431 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)
  (κpos : PTCutoff S) (κneg : PTCutoff S.neg)


-- @@ L433-437 verbatim
/-- Horizontal coordinates of the unsmoothed endpoint collapse. -/
lemma sphereMap_initCLM (x : E) :
    initCLM n (sphereMap S κpos x : E) =
      ‖raw S κpos x‖⁻¹ • (κpos x • X.g x) := by
  rw [sphereMap_coe, map_smul, initCLM_raw]


-- @@ L439-447 verbatim
/-- Its vertical coordinate is a positive rescaling of `2κ-1`; this is the
basic reason sign-pattern interpolation, rather than literal sign-function
equality, is the natural endpoint contract. -/
lemma sphereMap_vertical_eq_pos_smul (x : E) :
    vertC (sphereMap S κpos x : E) =
      ‖raw S κpos x‖⁻¹ * endpointVertical S κpos x := by
  change ‖raw S κpos x‖⁻¹ * (raw S κpos x) (Fin.last n) = _
  rw [raw_last]
  rfl


-- @@ L449-451 verbatim
lemma sphereMap_normalizationFactor_pos (x : E) :
    0 < ‖raw S κpos x‖⁻¹ :=
  inv_pos.mpr (norm_pos_iff.mpr (raw_ne_zero S κpos x))


-- @@ L453-517 verbatim
/-- The positive and negative PT lanes may use one and the same smooth
localizer `λ`.  We apply smooth Urysohn separation once inside the intersection
of their two sign-agreement neighborhoods. -/
theorem exists_common_endpointPatchLocalizer :
    ∃ (Ppos : EndpointPatchLocalizer S κpos)
      (Pneg : EndpointPatchLocalizer S.neg κneg),
      Ppos.toFun = Pneg.toFun := by
  let V : Set E := signAgreement S κpos ∩ signAgreement S.neg κneg
  have hopen : IsOpen V :=
    (isOpen_signAgreement S κpos).inter (isOpen_signAgreement S.neg κneg)
  have hsub : X.fiber ⊆ V := by
    intro x hx
    exact ⟨fiber_subset_signAgreement S κpos hx,
      fiber_subset_signAgreement S.neg κneg hx⟩
  obtain ⟨δ, hδpos, hδsub⟩ :=
    X.isCompact_fiber.exists_cthickening_subset_open hopen hsub
  let U : Set E := Metric.thickening δ X.fiber
  have hKU : X.fiber ⊆ U := Metric.self_subset_thickening hδpos _
  have hUc : IsCompact (closure U) := by
    apply IsCompact.of_isClosed_subset X.isCompact_fiber.cthickening
      isClosed_closure
    exact closure_minimal
      (Metric.thickening_subset_cthickening _ _) Metric.isClosed_cthickening
  have hs : IsClosed Uᶜ := Metric.isOpen_thickening.isClosed_compl
  have hd : Disjoint Uᶜ X.fiber := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    exact hxU (hKU hxK)
  obtain ⟨lam, hlam0, hlam1, hlam01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hs X.isClosed_fiber hd
  have hlamsmooth : ContDiff ℝ ∞ (⇑lam) := by
    rw [← contMDiff_iff_contDiff]
    exact lam.contMDiff
  have hlamsupport : HasCompactSupport (⇑lam) := by
    have hsupport : support (⇑lam) ⊆ U := by
      intro x hx
      by_contra hxU
      exact hx (hlam0 hxU)
    have htsupport : tsupport (⇑lam) ⊆ closure U :=
      closure_minimal (hsupport.trans subset_closure) isClosed_closure
    exact IsCompact.of_isClosed_subset hUc isClosed_closure htsupport
  have hlamV : ∀ x, lam x ≠ 0 → x ∈ V := by
    intro x hx
    have hxU : x ∈ U := by
      by_contra hnot
      exact hx (hlam0 hnot)
    exact hδsub (Metric.thickening_subset_cthickening _ _ hxU)
  let Ppos : EndpointPatchLocalizer S κpos := {
    toFun := ⇑lam
    smooth := hlamsmooth
    range := hlam01
    fiber_one := hlam1
    nonzero_agrees := fun x hx => (hlamV x hx).1
    compact_support := hlamsupport
  }
  let Pneg : EndpointPatchLocalizer S.neg κneg := {
    toFun := ⇑lam
    smooth := hlamsmooth
    range := hlam01
    fiber_one := hlam1
    nonzero_agrees := fun x hx => (hlamV x hx).2
    compact_support := hlamsupport
  }
  exact ⟨Ppos, Pneg, rfl⟩


-- @@ L519-534 verbatim
/-- In contrast, the two PT cutoffs themselves cannot be the same function
when the positive sheet is nonempty: one must be `1` there and the other `0`.
-/
theorem cutoff_toFun_ne_of_mem_positivePart
    {x : E} (hx : x ∈ S.positivePart) :
    κpos.toFun ≠ κneg.toFun := by
  intro hfun
  have hpos : κpos x = 1 := κpos.positive_one x hx
  have hxneg : x ∈ S.neg.negativePart := by
    exact ⟨hx.1, by
      rw [FiberSign.neg_apply]
      exact neg_lt_zero.mpr hx.2⟩
  have hneg : κneg x = 0 := κneg.negative_zero x hxneg
  have happ := congrFun hfun x
  rw [hpos, hneg] at happ
  norm_num at happ


-- @@ L536-536 verbatim
end CommonTwoSheetLocalizer


-- @@ L538-540 verbatim
variable {X₀ X₁ : FramedLevelSet n}
  (S₀ : FiberSign X₀) (S₁ : FiberSign X₁)
  (κ₀ : PTCutoff S₀) (κ₁ : PTCutoff S₁)


-- @@ L542-559 verbatim
/-- Exact source level-set compatibility is equivalent to equality of the two
defining maps. -/
theorem patchTargetLevelSet_eq_source_iff
    (P₀ : EndpointPatchLocalizer S₀ κ₀) (y₀ : F)
    (hregular₀ : IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
      (patchTransition S₀ κ₀ P₀) y₀)
    (H : CollaredSphereHomotopy n) (y : F) (hy0 : y ≠ 0)
    (hregular : IsRegularValue H.horizontal y) :
    patchTargetLevelSet S₀ κ₀ P₀ y₀ hregular₀ =
        H.sourceLevelSet y hy0 hregular ↔
      patchTargetMap S₀ κ₀ P₀ y₀ = fun x => H.sourceHorizontal x - y := by
  constructor
  · intro h
    simpa [patchTargetLevelSet, CollaredSphereHomotopy.sourceLevelSet] using
      congrArg FramedLevelSet.g h
  · intro h
    apply FramedLevelSet.eq_of_g_eq
    simpa [patchTargetLevelSet, CollaredSphereHomotopy.sourceLevelSet] using h


-- @@ L561-577 verbatim
/-- Exact target counterpart of `patchTargetLevelSet_eq_source_iff`. -/
theorem patchTargetLevelSet_eq_target_iff
    (P₁ : EndpointPatchLocalizer S₁ κ₁) (y₁ : F)
    (hregular₁ : IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
      (patchTransition S₁ κ₁ P₁) y₁)
    (H : CollaredSphereHomotopy n) (y : F) (hy0 : y ≠ 0)
    (hregular : IsRegularValue H.horizontal y) :
    patchTargetLevelSet S₁ κ₁ P₁ y₁ hregular₁ =
        H.targetLevelSet y hy0 hregular ↔
      patchTargetMap S₁ κ₁ P₁ y₁ = fun x => H.targetHorizontal x - y := by
  constructor
  · intro h
    simpa [patchTargetLevelSet, CollaredSphereHomotopy.targetLevelSet] using
      congrArg FramedLevelSet.g h
  · intro h
    apply FramedLevelSet.eq_of_g_eq
    simpa [patchTargetLevelSet, CollaredSphereHomotopy.targetLevelSet] using h


-- @@ L579-660 verbatim
/-- One small nonzero Sard value can be chosen simultaneously for both
endpoint patch quotients and the middle horizontal map.  Density alone would
not justify a finite intersection; the proof instead removes the finite union
of the three Sard-null critical-value sets from a fixed positive-measure ball.
-/
theorem exists_common_small_regular_value
    (P₀ : EndpointPatchLocalizer S₀ κ₀)
    (P₁ : EndpointPatchLocalizer S₁ κ₁)
    (H : CollaredSphereHomotopy n) (hn : 0 < n) :
    ∃ y : F, 0 < ‖y‖ ∧ ‖y‖ < 1 / 8 ∧
      IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
        (patchTransition S₀ κ₀ P₀) y ∧
      IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
        (patchTransition S₁ κ₁ P₁) y ∧
      IsRegularValue H.horizontal y := by
  let C₀ : Set F := patchQuotient S₀ κ₀ P₀ ''
    {v | v ∈ patchTransition S₀ κ₀ P₀ ∧
      ¬Function.Surjective
        (fderivWithin ℝ (patchQuotient S₀ κ₀ P₀)
          (patchTransition S₀ κ₀ P₀) v)}
  let C₁ : Set F := patchQuotient S₁ κ₁ P₁ ''
    {v | v ∈ patchTransition S₁ κ₁ P₁ ∧
      ¬Function.Surjective
        (fderivWithin ℝ (patchQuotient S₁ κ₁ P₁)
          (patchTransition S₁ κ₁ P₁) v)}
  let CH : Set F := H.horizontal ''
    {v | v ∈ (Set.univ : Set A) ∧
      ¬Function.Surjective
        (fderivWithin ℝ H.horizontal (Set.univ : Set A) v)}
  have hC₀ : volume C₀ = 0 := by
    dsimp [C₀]
    exact sard (isOpen_patchTransition S₀ κ₀ P₀)
      (contDiffOn_patchQuotient S₀ κ₀ P₀)
  have hC₁ : volume C₁ = 0 := by
    dsimp [C₁]
    exact sard (isOpen_patchTransition S₁ κ₁ P₁)
      (contDiffOn_patchQuotient S₁ κ₁ P₁)
  have hCH : volume CH = 0 := by
    dsimp [CH]
    exact sard isOpen_univ H.contDiff_horizontal.contDiffOn
  have hbad : volume ((C₀ ∪ C₁) ∪ CH) = 0 :=
    measure_union_null (measure_union_null hC₀ hC₁) hCH
  let z₀ : F := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 / 16 : ℝ)
  let O : Set F := Metric.ball z₀ (1 / 32)
  have hOpos : 0 < volume O := by
    exact Metric.isOpen_ball.measure_pos volume
      (Metric.nonempty_ball.mpr (by norm_num : (0 : ℝ) < 1 / 32))
  have hnotSub : ¬O ⊆ (C₀ ∪ C₁) ∪ CH := by
    intro hsub
    exact hOpos.ne' (measure_mono_null hsub hbad)
  obtain ⟨y, hyO, hybad⟩ := Set.not_subset.mp hnotSub
  have hreg₀ : IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
      (patchTransition S₀ κ₀ P₀) y := by
    intro v hvU hvy
    by_contra hns
    apply hybad
    exact Or.inl (Or.inl ⟨v, ⟨hvU, hns⟩, hvy⟩)
  have hreg₁ : IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
      (patchTransition S₁ κ₁ P₁) y := by
    intro v hvU hvy
    by_contra hns
    apply hybad
    exact Or.inl (Or.inr ⟨v, ⟨hvU, hns⟩, hvy⟩)
  have hregOn : IsRegularValueOn H.horizontal Set.univ y := by
    intro v _ hvy
    by_contra hns
    apply hybad
    exact Or.inr ⟨v, ⟨Set.mem_univ v, hns⟩, hvy⟩
  have hreg : IsRegularValue H.horizontal y := by
    intro v hvy
    have hs := hregOn v (Set.mem_univ v) hvy
    rwa [fderivWithin_univ] at hs
  have hz₀norm : ‖z₀‖ = 1 / 16 := by
    rw [show z₀ = EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 / 16 : ℝ) from rfl,
      PiLp.norm_single, Real.norm_eq_abs]
    norm_num
  have hdist : ‖y - z₀‖ < 1 / 32 := by
    change dist y z₀ < 1 / 32 at hyO
    rwa [dist_eq_norm] at hyO
  have habs : |‖y‖ - ‖z₀‖| ≤ ‖y - z₀‖ := abs_norm_sub_norm_le y z₀
  rw [hz₀norm, abs_le] at habs
  exact ⟨y, by linarith [habs.1], by linarith [habs.2], hreg₀, hreg₁, hreg⟩


-- @@ L662-742 verbatim
/-- Arbitrarily small version of `exists_common_small_regular_value`.  This
is needed when the endpoint spatial-regularity theorem supplies an abstract
positive radius rather than the fixed numerical `1/8` bound. -/
theorem exists_common_regular_value_lt
    (P₀ : EndpointPatchLocalizer S₀ κ₀)
    (P₁ : EndpointPatchLocalizer S₁ κ₁)
    (H : CollaredSphereHomotopy n) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) :
    ∃ y : F, 0 < ‖y‖ ∧ ‖y‖ < r ∧
      IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
        (patchTransition S₀ κ₀ P₀) y ∧
      IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
        (patchTransition S₁ κ₁ P₁) y ∧
      IsRegularValue H.horizontal y := by
  let C₀ : Set F := patchQuotient S₀ κ₀ P₀ ''
    {v | v ∈ patchTransition S₀ κ₀ P₀ ∧
      ¬Function.Surjective
        (fderivWithin ℝ (patchQuotient S₀ κ₀ P₀)
          (patchTransition S₀ κ₀ P₀) v)}
  let C₁ : Set F := patchQuotient S₁ κ₁ P₁ ''
    {v | v ∈ patchTransition S₁ κ₁ P₁ ∧
      ¬Function.Surjective
        (fderivWithin ℝ (patchQuotient S₁ κ₁ P₁)
          (patchTransition S₁ κ₁ P₁) v)}
  let CH : Set F := H.horizontal ''
    {v | v ∈ (Set.univ : Set A) ∧
      ¬Function.Surjective
        (fderivWithin ℝ H.horizontal (Set.univ : Set A) v)}
  have hC₀ : volume C₀ = 0 := by
    dsimp [C₀]
    exact sard (isOpen_patchTransition S₀ κ₀ P₀)
      (contDiffOn_patchQuotient S₀ κ₀ P₀)
  have hC₁ : volume C₁ = 0 := by
    dsimp [C₁]
    exact sard (isOpen_patchTransition S₁ κ₁ P₁)
      (contDiffOn_patchQuotient S₁ κ₁ P₁)
  have hCH : volume CH = 0 := by
    dsimp [CH]
    exact sard isOpen_univ H.contDiff_horizontal.contDiffOn
  have hbad : volume ((C₀ ∪ C₁) ∪ CH) = 0 :=
    measure_union_null (measure_union_null hC₀ hC₁) hCH
  let z₀ : F := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (r / 2)
  let O : Set F := Metric.ball z₀ (r / 4)
  have hquarter : 0 < r / 4 := div_pos hr (by norm_num)
  have hOpos : 0 < volume O := by
    exact Metric.isOpen_ball.measure_pos volume
      (Metric.nonempty_ball.mpr hquarter)
  have hnotSub : ¬O ⊆ (C₀ ∪ C₁) ∪ CH := by
    intro hsub
    exact hOpos.ne' (measure_mono_null hsub hbad)
  obtain ⟨y, hyO, hybad⟩ := Set.not_subset.mp hnotSub
  have hreg₀ : IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
      (patchTransition S₀ κ₀ P₀) y := by
    intro v hvU hvy
    by_contra hns
    apply hybad
    exact Or.inl (Or.inl ⟨v, ⟨hvU, hns⟩, hvy⟩)
  have hreg₁ : IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
      (patchTransition S₁ κ₁ P₁) y := by
    intro v hvU hvy
    by_contra hns
    apply hybad
    exact Or.inl (Or.inr ⟨v, ⟨hvU, hns⟩, hvy⟩)
  have hregOn : IsRegularValueOn H.horizontal Set.univ y := by
    intro v _ hvy
    by_contra hns
    apply hybad
    exact Or.inr ⟨v, ⟨Set.mem_univ v, hns⟩, hvy⟩
  have hreg : IsRegularValue H.horizontal y := by
    intro v hvy
    have hs := hregOn v (Set.mem_univ v) hvy
    rwa [fderivWithin_univ] at hs
  have hz₀norm : ‖z₀‖ = r / 2 := by
    rw [show z₀ = EuclideanSpace.single (⟨0, hn⟩ : Fin n) (r / 2) from rfl,
      PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (div_pos hr (by norm_num))]
  have hdist : ‖y - z₀‖ < r / 4 := by
    change dist y z₀ < r / 4 at hyO
    rwa [dist_eq_norm] at hyO
  have habs : |‖y‖ - ‖z₀‖| ≤ ‖y - z₀‖ := abs_norm_sub_norm_le y z₀
  rw [hz₀norm, abs_le] at habs
  exact ⟨y, by linarith [habs.1], by linarith [habs.2], hreg₀, hreg₁, hreg⟩


-- @@ L744-774 verbatim
/-- Exact source-presentation compatibility has a strong necessary condition:
the original defining map must be the constant `-y` at spatial infinity.
Indeed the patch preserves `X₀.g` outside the compact supports of `κ₀` and
`P₀`, whereas a sphere-induced nonzero level is exactly `-y` outside the
south-pole radius. -/
theorem source_level_eq_forces_eventually_g_eq_neg
    (P₀ : EndpointPatchLocalizer S₀ κ₀) (y₀ : F)
    (hregular₀ : IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
      (patchTransition S₀ κ₀ P₀) y₀)
    (H : CollaredSphereHomotopy n) (y : F) (hy0 : y ≠ 0)
    (hregular : IsRegularValue H.horizontal y)
    (hlevel : patchTargetLevelSet S₀ κ₀ P₀ y₀ hregular₀ =
      H.sourceLevelSet y hy0 hregular) :
    ∃ R : ℝ, ∀ x : E, R < ‖x‖ → X₀.g x = -y := by
  obtain ⟨Rκ, hRκ⟩ :=
    exists_eq_zero_of_norm_gt_of_hasCompactSupport κ₀.compact_support
  obtain ⟨RP, hRP⟩ :=
    exists_eq_zero_of_norm_gt_of_hasCompactSupport P₀.compact_support
  obtain ⟨RH, hRH⟩ := H.eventually_sourceHorizontal_eq_zero
  refine ⟨max (max Rκ RP) RH, ?_⟩
  intro x hx
  have hκx : κ₀ x = 0 := hRκ x
    ((le_max_left Rκ RP |>.trans (le_max_left (max Rκ RP) RH)).trans_lt hx)
  have hPx : P₀ x = 0 := hRP x
    ((le_max_right Rκ RP |>.trans (le_max_left (max Rκ RP) RH)).trans_lt hx)
  have hHx : H.sourceHorizontal x = 0 := hRH x
    ((le_max_right (max Rκ RP) RH).trans_lt hx)
  have hmaps := congrArg FramedLevelSet.g hlevel
  have hmapsx := congrFun hmaps x
  change patchTargetMap S₀ κ₀ P₀ y₀ x = H.sourceHorizontal x - y at hmapsx
  simpa [patchTargetMap, hκx, hPx, hHx] using hmapsx


-- @@ L776-802 verbatim
/-- Outgoing analogue of `source_level_eq_forces_eventually_g_eq_neg`. -/
theorem target_level_eq_forces_eventually_g_eq_neg
    (P₁ : EndpointPatchLocalizer S₁ κ₁) (y₁ : F)
    (hregular₁ : IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
      (patchTransition S₁ κ₁ P₁) y₁)
    (H : CollaredSphereHomotopy n) (y : F) (hy0 : y ≠ 0)
    (hregular : IsRegularValue H.horizontal y)
    (hlevel : patchTargetLevelSet S₁ κ₁ P₁ y₁ hregular₁ =
      H.targetLevelSet y hy0 hregular) :
    ∃ R : ℝ, ∀ x : E, R < ‖x‖ → X₁.g x = -y := by
  obtain ⟨Rκ, hRκ⟩ :=
    exists_eq_zero_of_norm_gt_of_hasCompactSupport κ₁.compact_support
  obtain ⟨RP, hRP⟩ :=
    exists_eq_zero_of_norm_gt_of_hasCompactSupport P₁.compact_support
  obtain ⟨RH, hRH⟩ := H.eventually_targetHorizontal_eq_zero
  refine ⟨max (max Rκ RP) RH, ?_⟩
  intro x hx
  have hκx : κ₁ x = 0 := hRκ x
    ((le_max_left Rκ RP |>.trans (le_max_left (max Rκ RP) RH)).trans_lt hx)
  have hPx : P₁ x = 0 := hRP x
    ((le_max_right Rκ RP |>.trans (le_max_left (max Rκ RP) RH)).trans_lt hx)
  have hHx : H.targetHorizontal x = 0 := hRH x
    ((le_max_right (max Rκ RP) RH).trans_lt hx)
  have hmaps := congrArg FramedLevelSet.g hlevel
  have hmapsx := congrFun hmaps x
  change patchTargetMap S₁ κ₁ P₁ y₁ x = H.targetHorizontal x - y at hmapsx
  simpa [patchTargetMap, hκx, hPx, hHx] using hmapsx


-- @@ L804-836 verbatim
/-- Fully explicit data needed to splice two already-constructed endpoint
patches through one transverse sphere middle.  The two presentation equalities
are the genuine remaining endpoint-identification problem.  The sign fields
ask only for equality of sign patterns on the common fibers; actual signed
cylinders are constructed from them below. -/
structure PatchedTransverseLane where
  P₀ : EndpointPatchLocalizer S₀ κ₀
  P₁ : EndpointPatchLocalizer S₁ κ₁
  y₀ : F
  y₁ : F
  regular₀ : IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
    (patchTransition S₀ κ₀ P₀) y₀
  regular₁ : IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
    (patchTransition S₁ κ₁ P₁) y₁
  middle : CollaredSphereHomotopy n
  y : F
  y_ne_zero : y ≠ 0
  y_norm_lt_one : ‖y‖ < 1
  y_regular : IsRegularValue middle.horizontal y
  source_level_eq :
    patchTargetLevelSet S₀ κ₀ P₀ y₀ regular₀ =
      middle.sourceLevelSet y y_ne_zero y_regular
  target_level_eq :
    patchTargetLevelSet S₁ κ₁ P₁ y₁ regular₁ =
      middle.targetLevelSet y y_ne_zero y_regular
  source_sign_pattern : ∀ x ∈
      (middle.sourceLevelSet y y_ne_zero y_regular).fiber,
    (0 < (patchTargetSign S₀ κ₀ P₀ y₀ regular₀).transport source_level_eq x ↔
      0 < middle.sourceSign y y_ne_zero y_regular y_norm_lt_one x)
  target_sign_pattern : ∀ x ∈
      (middle.targetLevelSet y y_ne_zero y_regular).fiber,
    (0 < (patchTargetSign S₁ κ₁ P₁ y₁ regular₁).transport target_level_eq x ↔
      0 < middle.targetSign y y_ne_zero y_regular y_norm_lt_one x)


-- @@ L838-838 verbatim
namespace PatchedTransverseLane


-- @@ L840-909 verbatim
/-- Build every endpoint compatibility field from pointwise formulas at one
common Sard value.  Equality of the horizontal defining maps gives the framed
presentation equalities by proof irrelevance.  A positive rescaling formula
for the vertical coordinates gives the sign patterns, after which the actual
sign cylinders are automatic.

This is the strongest useful extensional constructor: normalized sphere maps
naturally satisfy a positive-rescaling formula, not literal equality of their
vertical functions. -/
def ofCommonValueFormulas
    (P₀ : EndpointPatchLocalizer S₀ κ₀)
    (P₁ : EndpointPatchLocalizer S₁ κ₁)
    (H : CollaredSphereHomotopy n) (y : F)
    (hy0 : y ≠ 0) (hylt : ‖y‖ < 1)
    (hregular₀ : IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
      (patchTransition S₀ κ₀ P₀) y)
    (hregular₁ : IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
      (patchTransition S₁ κ₁ P₁) y)
    (hregular : IsRegularValue H.horizontal y)
    (hsourceMap : patchTargetMap S₀ κ₀ P₀ y =
      fun x => H.sourceHorizontal x - y)
    (htargetMap : patchTargetMap S₁ κ₁ P₁ y =
      fun x => H.targetHorizontal x - y)
    (q₀ q₁ : E → ℝ) (hq₀ : ∀ x, 0 < q₀ x) (hq₁ : ∀ x, 0 < q₁ x)
    (hsourceVertical : ∀ x,
      vertC (H.sphere (spaceTime x 0) : E) =
        q₀ x * endpointVertical S₀ κ₀ x)
    (htargetVertical : ∀ x,
      vertC (H.sphere (spaceTime x 1) : E) =
        q₁ x * endpointVertical S₁ κ₁ x) :
    PatchedTransverseLane S₀ S₁ κ₀ κ₁ := by
  have hslevel : patchTargetLevelSet S₀ κ₀ P₀ y hregular₀ =
      H.sourceLevelSet y hy0 hregular := by
    apply FramedLevelSet.eq_of_g_eq
    simpa [patchTargetLevelSet, CollaredSphereHomotopy.sourceLevelSet] using
      hsourceMap
  have htlevel : patchTargetLevelSet S₁ κ₁ P₁ y hregular₁ =
      H.targetLevelSet y hy0 hregular := by
    apply FramedLevelSet.eq_of_g_eq
    simpa [patchTargetLevelSet, CollaredSphereHomotopy.targetLevelSet] using
      htargetMap
  refine {
    P₀ := P₀
    P₁ := P₁
    y₀ := y
    y₁ := y
    regular₀ := hregular₀
    regular₁ := hregular₁
    middle := H
    y := y
    y_ne_zero := hy0
    y_norm_lt_one := hylt
    y_regular := hregular
    source_level_eq := hslevel
    target_level_eq := htlevel
    source_sign_pattern := ?_
    target_sign_pattern := ?_
  }
  · apply transported_signPattern_of_pos_smul
      (patchTargetSign S₀ κ₀ P₀ y hregular₀)
      (H.sourceSign y hy0 hregular hylt) hslevel q₀ hq₀
    intro x
    simpa [patchTargetSign, CollaredSphereHomotopy.sourceSign] using
      hsourceVertical x
  · apply transported_signPattern_of_pos_smul
      (patchTargetSign S₁ κ₁ P₁ y hregular₁)
      (H.targetSign y hy0 hregular hylt) htlevel q₁ hq₁
    intro x
    simpa [patchTargetSign, CollaredSphereHomotopy.targetSign] using
      htargetVertical x


-- @@ L911-911 verbatim
variable (D : PatchedTransverseLane S₀ S₁ κ₀ κ₁)

-- @@ L912-912 verbatim
include D


-- @@ L914-920 verbatim
/-- Every source compatibility package records an eventually constant source
presentation; this exposes the exact residual obstruction at the public lane
interface. -/
theorem source_eventually_g_eq_neg :
    ∃ R : ℝ, ∀ x : E, R < ‖x‖ → X₀.g x = -D.y :=
  source_level_eq_forces_eventually_g_eq_neg S₀ κ₀ D.P₀ D.y₀ D.regular₀
    D.middle D.y D.y_ne_zero D.y_regular D.source_level_eq


-- @@ L922-926 verbatim
/-- Target counterpart of `source_eventually_g_eq_neg`. -/
theorem target_eventually_g_eq_neg :
    ∃ R : ℝ, ∀ x : E, R < ‖x‖ → X₁.g x = -D.y :=
  target_level_eq_forces_eventually_g_eq_neg S₁ κ₁ D.P₁ D.y₁ D.regular₁
    D.middle D.y D.y_ne_zero D.y_regular D.target_level_eq


-- @@ L928-933 verbatim
/-- The source presentation equality and sign pattern give an actual connector
from the patched endpoint to the sphere-induced endpoint. -/
def sourceConnector : SignedFramedLevelCobordism
    (patchTargetSign S₀ κ₀ D.P₀ D.y₀ D.regular₀)
    (D.middle.sourceSign D.y D.y_ne_zero D.y_regular D.y_norm_lt_one) :=
  signedEndpointConnector _ _ D.source_level_eq D.source_sign_pattern


-- @@ L935-940 verbatim
/-- Target counterpart of `sourceConnector`, oriented from the patched
endpoint to the sphere-induced endpoint. -/
def targetConnector : SignedFramedLevelCobordism
    (patchTargetSign S₁ κ₁ D.P₁ D.y₁ D.regular₁)
    (D.middle.targetSign D.y D.y_ne_zero D.y_regular D.y_norm_lt_one) :=
  signedEndpointConnector _ _ D.target_level_eq D.target_sign_pattern


-- @@ L942-947 verbatim
/-- The transverse middle between its own induced signed endpoints. -/
def middleCobordism : SignedFramedLevelCobordism
    (D.middle.sourceSign D.y D.y_ne_zero D.y_regular D.y_norm_lt_one)
    (D.middle.targetSign D.y D.y_ne_zero D.y_regular D.y_norm_lt_one) :=
  (D.middle.toPTTransverseHomotopyData D.y D.y_ne_zero
    D.y_regular D.y_norm_lt_one).toSignedFramedLevelCobordism


-- @@ L949-956 verbatim
/-- Splice source patch, transverse middle, and reversed target patch. -/
def toSignedCobordism : SignedFramedLevelCobordism S₀ S₁ :=
  SignedFramedLevelCobordism.trans
    (patchSignedCobordism S₀ κ₀ D.P₀ D.y₀ D.regular₀)
    (SignedFramedLevelCobordism.trans D.sourceConnector
      (SignedFramedLevelCobordism.trans D.middleCobordism
        (SignedFramedLevelCobordism.trans D.targetConnector.reverse
          (patchSignedCobordism S₁ κ₁ D.P₁ D.y₁ D.regular₁).reverse)))


-- @@ L958-960 verbatim
theorem nonempty_signedCobordism :
    Nonempty (SignedFramedLevelCobordism S₀ S₁) :=
  ⟨toSignedCobordism S₀ S₁ κ₀ κ₁ D⟩


-- @@ L962-962 verbatim
end PatchedTransverseLane


-- @@ L964-971 verbatim
/-! ## Endpoint-connected lane

The preceding exact lane is useful for exposing the failed global-equality
contract.  The actual splice only needs signed cobordisms between the patched
endpoints and the sphere-induced endpoints.  Packaging those connectors
directly is both weaker and exactly categorical: no presentation equality is
smuggled into the public two-sheet input.
-/


-- @@ L973-995 verbatim
/-- A patched transverse lane whose endpoint compatibility is supplied by
actual signed cobordisms.  These are the two genuine geometric obligations of
the endpoint-matching step. -/
structure ConnectedPatchedTransverseLane where
  P₀ : EndpointPatchLocalizer S₀ κ₀
  P₁ : EndpointPatchLocalizer S₁ κ₁
  y₀ : F
  y₁ : F
  regular₀ : IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
    (patchTransition S₀ κ₀ P₀) y₀
  regular₁ : IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
    (patchTransition S₁ κ₁ P₁) y₁
  middle : CollaredSphereHomotopy n
  y : F
  y_ne_zero : y ≠ 0
  y_norm_lt_one : ‖y‖ < 1
  y_regular : IsRegularValue middle.horizontal y
  source_connector : SignedFramedLevelCobordism
    (patchTargetSign S₀ κ₀ P₀ y₀ regular₀)
    (middle.sourceSign y y_ne_zero y_regular y_norm_lt_one)
  target_connector : SignedFramedLevelCobordism
    (patchTargetSign S₁ κ₁ P₁ y₁ regular₁)
    (middle.targetSign y y_ne_zero y_regular y_norm_lt_one)


-- @@ L997-997 verbatim
namespace ConnectedPatchedTransverseLane


-- @@ L999-1041 verbatim
/-- Build the two actual endpoint connectors from homotopies of defining maps
and equality of sign patterns after transporting along their common fibers.
This is the reusable replacement for exact equality of presentations. -/
def ofDefiningMapHomotopies
    (P₀ : EndpointPatchLocalizer S₀ κ₀)
    (P₁ : EndpointPatchLocalizer S₁ κ₁)
    (H : CollaredSphereHomotopy n) (y₀ y₁ y : F)
    (hy0 : y ≠ 0) (hylt : ‖y‖ < 1)
    (hregular₀ : IsRegularValueOn (patchQuotient S₀ κ₀ P₀)
      (patchTransition S₀ κ₀ P₀) y₀)
    (hregular₁ : IsRegularValueOn (patchQuotient S₁ κ₁ P₁)
      (patchTransition S₁ κ₁ P₁) y₁)
    (hregular : IsRegularValue H.horizontal y)
    (D₀ : DefiningMapHomotopy
      (patchTargetLevelSet S₀ κ₀ P₀ y₀ hregular₀)
      (H.sourceLevelSet y hy0 hregular))
    (D₁ : DefiningMapHomotopy
      (patchTargetLevelSet S₁ κ₁ P₁ y₁ hregular₁)
      (H.targetLevelSet y hy0 hregular))
    (hsource : ∀ x ∈ (H.sourceLevelSet y hy0 hregular).fiber,
      (0 < (patchTargetSign S₀ κ₀ P₀ y₀ hregular₀).restrict
          D₀.fiber_subset x ↔
        0 < H.sourceSign y hy0 hregular hylt x))
    (htarget : ∀ x ∈ (H.targetLevelSet y hy0 hregular).fiber,
      (0 < (patchTargetSign S₁ κ₁ P₁ y₁ hregular₁).restrict
          D₁.fiber_subset x ↔
        0 < H.targetSign y hy0 hregular hylt x)) :
    ConnectedPatchedTransverseLane S₀ S₁ κ₀ κ₁ where
  P₀ := P₀
  P₁ := P₁
  y₀ := y₀
  y₁ := y₁
  regular₀ := hregular₀
  regular₁ := hregular₁
  middle := H
  y := y
  y_ne_zero := hy0
  y_norm_lt_one := hylt
  y_regular := hregular
  source_connector :=
    signedEndpointConnectorOfDefiningMapHomotopy D₀ _ _ hsource
  target_connector :=
    signedEndpointConnectorOfDefiningMapHomotopy D₁ _ _ htarget


-- @@ L1043-1059 verbatim
/-- Every exact-presentation lane gives an endpoint-connected lane, but the
converse deliberately does not hold. -/
def ofExact (D : PatchedTransverseLane S₀ S₁ κ₀ κ₁) :
    ConnectedPatchedTransverseLane S₀ S₁ κ₀ κ₁ where
  P₀ := D.P₀
  P₁ := D.P₁
  y₀ := D.y₀
  y₁ := D.y₁
  regular₀ := D.regular₀
  regular₁ := D.regular₁
  middle := D.middle
  y := D.y
  y_ne_zero := D.y_ne_zero
  y_norm_lt_one := D.y_norm_lt_one
  y_regular := D.y_regular
  source_connector := D.sourceConnector
  target_connector := D.targetConnector


-- @@ L1061-1061 verbatim
variable (D : ConnectedPatchedTransverseLane S₀ S₁ κ₀ κ₁)

-- @@ L1062-1062 verbatim
include D


-- @@ L1064-1069 verbatim
/-- The transverse middle between its own induced signed endpoints. -/
def middleCobordism : SignedFramedLevelCobordism
    (D.middle.sourceSign D.y D.y_ne_zero D.y_regular D.y_norm_lt_one)
    (D.middle.targetSign D.y D.y_ne_zero D.y_regular D.y_norm_lt_one) :=
  (D.middle.toPTTransverseHomotopyData D.y D.y_ne_zero
    D.y_regular D.y_norm_lt_one).toSignedFramedLevelCobordism


-- @@ L1071-1079 verbatim
/-- Splice the source patch, the two actual endpoint connectors, the
transverse middle, and the reversed target patch. -/
def toSignedCobordism : SignedFramedLevelCobordism S₀ S₁ :=
  SignedFramedLevelCobordism.trans
    (patchSignedCobordism S₀ κ₀ D.P₀ D.y₀ D.regular₀)
    (SignedFramedLevelCobordism.trans D.source_connector
      (SignedFramedLevelCobordism.trans D.middleCobordism
        (SignedFramedLevelCobordism.trans D.target_connector.reverse
          (patchSignedCobordism S₁ κ₁ D.P₁ D.y₁ D.regular₁).reverse)))


-- @@ L1081-1083 verbatim
theorem nonempty_signedCobordism :
    Nonempty (SignedFramedLevelCobordism S₀ S₁) :=
  ⟨toSignedCobordism S₀ S₁ κ₀ κ₁ D⟩


-- @@ L1085-1085 verbatim
end ConnectedPatchedTransverseLane


-- @@ L1087-1087 verbatim
/-! ## Correct two-sheet assembly -/


-- @@ L1089-1094 verbatim
/-- Positive and negative PT lanes.  The negative lane is formulated for the
negated endpoint labels, exactly matching the second endpoint collapse. -/
structure TwoSheetPatchedTransverseData
    (κ₀neg : PTCutoff S₀.neg) (κ₁neg : PTCutoff S₁.neg) where
  positive : ConnectedPatchedTransverseLane S₀ S₁ κ₀ κ₁
  negative : ConnectedPatchedTransverseLane S₀.neg S₁.neg κ₀neg κ₁neg


-- @@ L1096-1096 verbatim
namespace TwoSheetPatchedTransverseData


-- @@ L1098-1099 verbatim
variable {κ₀neg : PTCutoff S₀.neg} {κ₁neg : PTCutoff S₁.neg}
  (D : TwoSheetPatchedTransverseData S₀ S₁ κ₀ κ₁ κ₀neg κ₁neg)

-- @@ L1100-1100 verbatim
include D


-- @@ L1102-1111 verbatim
/-- Both PT lanes construct signed cobordisms between the original endpoints.
For the negative lane we negate the completed cobordism back. -/
theorem two_signedCobordisms :
    Nonempty (SignedFramedLevelCobordism S₀ S₁) ∧
      Nonempty (SignedFramedLevelCobordism S₀ S₁) := by
  refine ⟨ConnectedPatchedTransverseLane.nonempty_signedCobordism
    S₀ S₁ κ₀ κ₁ D.positive, ?_⟩
  obtain ⟨C⟩ := ConnectedPatchedTransverseLane.nonempty_signedCobordism
    S₀.neg S₁.neg κ₀neg κ₁neg D.negative
  exact ⟨by simpa only [FiberSign.neg_neg] using C.neg⟩


-- @@ L1113-1116 verbatim
/-- End-to-end two-sheet output. -/
theorem nonempty_signedCobordism :
    Nonempty (SignedFramedLevelCobordism S₀ S₁) :=
  (two_signedCobordisms S₀ S₁ κ₀ κ₁ D).1


-- @@ L1118-1118 verbatim
end TwoSheetPatchedTransverseData


-- @@ L1120-1120 verbatim
end FiberSign.PTCutoff


-- @@ L1122-1122 verbatim
end Submission
