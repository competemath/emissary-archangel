import Mathlib
import Submission.SignedPTCobordism


-- @@ L4-12 verbatim
/-!
# Endpoint cutoffs induced by a signed PT cobordism

A compactly supported signed cutoff on a cobordism restricts on either collar
slice to a compactly supported cutoff selecting the positive part of the endpoint
framed level set.  This file records that endpoint datum independently of the
chosen cobordism.  It is the interface used to compare the global signed collapse
with the canonical bridge collapse.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace Submission


-- @@ L18-18 verbatim
open Set Function Metric

-- @@ L19-19 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L21-21 verbatim
variable {n : ℕ}


-- @@ L23-23 verbatim
namespace FiberSign


-- @@ L25-25 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L27-27 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L29-30 verbatim
/-- The negatively labelled union of fiber components. -/
def negativePart : Set E := {x | x ∈ X.fiber ∧ S x < 0}


-- @@ L32-36 verbatim
theorem disjoint_positivePart_negativePart :
    Disjoint S.positivePart S.negativePart := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hp⟩ ⟨-, hn⟩
  linarith


-- @@ L38-45 verbatim
/-- A smooth compactly supported selector of the positive fiber components. -/
structure PTCutoff where
  toFun : E → ℝ
  smooth : ContDiff ℝ ∞ toFun
  range : ∀ x, toFun x ∈ Icc (0 : ℝ) 1
  positive_one : ∀ x ∈ S.positivePart, toFun x = 1
  negative_zero : ∀ x ∈ S.negativePart, toFun x = 0
  compact_support : HasCompactSupport toFun


-- @@ L47-47 verbatim
namespace PTCutoff


-- @@ L49-49 verbatim
instance : CoeFun (PTCutoff S) fun _ => E → ℝ := ⟨PTCutoff.toFun⟩


-- @@ L51-53 verbatim
/-- The endpoint raw collapse associated to a signed selector. -/
def raw (κ : PTCutoff S) (x : E) : E :=
  κ x • embedCLM n (X.g x) + (2 * κ x - 1) • eLast n


-- @@ L55-58 verbatim
lemma raw_last (κ : PTCutoff S) (x : E) :
    raw S κ x (Fin.last n) = 2 * κ x - 1 := by
  rw [raw]
  simp [eLast]


-- @@ L60-63 verbatim
lemma initCLM_raw (κ : PTCutoff S) (x : E) :
    initCLM n (raw S κ x) = κ x • X.g x := by
  rw [raw, map_add, map_smul, map_smul, initCLM_embedCLM, initCLM_eLast,
    smul_zero, add_zero]


-- @@ L65-67 verbatim
lemma contDiff_raw (κ : PTCutoff S) : ContDiff ℝ ∞ (raw S κ) := by
  exact (κ.smooth.smul ((embedCLM n).contDiff.comp X.smooth)).add
    (((contDiff_const.mul κ.smooth).sub contDiff_const).smul contDiff_const)


-- @@ L69-86 verbatim
lemma raw_ne_zero (κ : PTCutoff S) (x : E) : raw S κ x ≠ 0 := by
  intro hzero
  have hlast := congrArg (fun z : E => z (Fin.last n)) hzero
  rw [raw_last S κ, PiLp.zero_apply] at hlast
  have hκ : κ x = 1 / 2 := by linarith
  have hhoriz := congrArg (initCLM n) hzero
  rw [initCLM_raw S κ, map_zero] at hhoriz
  have hκ0 : κ x ≠ 0 := by rw [hκ]; norm_num
  have hg : X.g x = 0 := (smul_eq_zero.mp hhoriz).resolve_left hκ0
  have hxfib : x ∈ X.fiber := hg
  rcases lt_trichotomy (S x) 0 with hneg | heq | hpos
  · have hz := κ.negative_zero x ⟨hxfib, hneg⟩
    rw [hκ] at hz
    norm_num at hz
  · exact S.nonzero x hxfib heq
  · have ho := κ.positive_one x ⟨hxfib, hpos⟩
    rw [hκ] at ho
    norm_num at ho


-- @@ L88-90 verbatim
/-- Normalized endpoint collapse. -/
def sphereMap (κ : PTCutoff S) : C(E, UnitSphere E) :=
  normalizeMap ⟨raw S κ, (contDiff_raw S κ).continuous⟩ (raw_ne_zero S κ)


-- @@ L92-93 verbatim
lemma sphereMap_coe (κ : PTCutoff S) (x : E) :
    (sphereMap S κ x : E) = ‖raw S κ x‖⁻¹ • raw S κ x := rfl


-- @@ L95-100 verbatim
lemma raw_of_positivePart (κ : PTCutoff S) {x : E}
    (hx : x ∈ S.positivePart) : raw S κ x = eLast n := by
  have hg : X.g x = 0 := hx.1
  rw [raw, κ.positive_one x hx, hg]
  simp
  norm_num


-- @@ L102-105 verbatim
lemma raw_of_negativePart (κ : PTCutoff S) {x : E}
    (hx : x ∈ S.negativePart) : raw S κ x = -eLast n := by
  have hg : X.g x = 0 := hx.1
  simp [raw, κ.negative_zero x hx, hg]


-- @@ L107-109 verbatim
lemma raw_of_zero (κ : PTCutoff S) {x : E} (hx : κ x = 0) :
    raw S κ x = -eLast n := by
  simp [raw, hx]


-- @@ L111-115 verbatim
lemma sphereMap_of_zero (κ : PTCutoff S) {x : E} (hx : κ x = 0) :
    sphereMap S κ x = southPole n := by
  apply Subtype.ext
  change ‖raw S κ x‖⁻¹ • raw S κ x = -eLast n
  rw [raw_of_zero S κ hx, norm_neg, norm_eLast, inv_one, one_smul]


-- @@ L117-122 verbatim
lemma sphereMap_of_positivePart (κ : PTCutoff S) {x : E}
    (hx : x ∈ S.positivePart) :
    sphereMap S κ x = SignedFramedLevelCobordism.SignedSlabCutoff.signedPTNorthPole := by
  apply Subtype.ext
  change ‖raw S κ x‖⁻¹ • raw S κ x = eLast n
  rw [raw_of_positivePart S κ hx, norm_eLast, inv_one, one_smul]


-- @@ L124-128 verbatim
lemma sphereMap_of_negativePart (κ : PTCutoff S) {x : E}
    (hx : x ∈ S.negativePart) : sphereMap S κ x = southPole n := by
  apply Subtype.ext
  change ‖raw S κ x‖⁻¹ • raw S κ x = -eLast n
  rw [raw_of_negativePart S κ hx, norm_neg, norm_eLast, inv_one, one_smul]


-- @@ L130-130 verbatim
/-! ### Independence of the cutoff -/


-- @@ L132-159 verbatim
/-- Convex interpolation of two signed selectors is again a signed selector. -/
def lerp (κ₀ κ₁ : PTCutoff S) (s : I) : PTCutoff S where
  toFun x := (1 - (s : ℝ)) * κ₀ x + (s : ℝ) * κ₁ x
  smooth := ((contDiff_const.sub contDiff_const).mul κ₀.smooth).add
    (contDiff_const.mul κ₁.smooth)
  range := by
    intro x
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    rcases κ₀.range x with ⟨h₀0, h₀1⟩
    rcases κ₁.range x with ⟨h₁0, h₁1⟩
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) h₀0) (mul_nonneg hs0 h₁0)
    · have ha : (1 - (s : ℝ)) * κ₀ x ≤ (1 - (s : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left h₀1 (sub_nonneg.mpr hs1)
      have hb : (s : ℝ) * κ₁ x ≤ (s : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h₁1 hs0
      linarith
  positive_one := by
    intro x hx
    rw [κ₀.positive_one x hx, κ₁.positive_one x hx]
    ring
  negative_zero := by
    intro x hx
    rw [κ₀.negative_zero x hx, κ₁.negative_zero x hx]
    ring
  compact_support := by
    exact κ₀.compact_support.mul_left.add κ₁.compact_support.mul_left


-- @@ L161-163 verbatim
/-- Joint raw vector for the convex interpolation. -/
def lerpRaw (κ₀ κ₁ : PTCutoff S) (p : I × E) : E :=
  raw S (lerp S κ₀ κ₁ p.1) p.2


-- @@ L165-186 verbatim
lemma continuous_lerpRaw (κ₀ κ₁ : PTCutoff S) :
    Continuous (lerpRaw S κ₀ κ₁) := by
  have hs : Continuous fun p : I × E => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hκ₀ : Continuous fun p : I × E => κ₀ p.2 :=
    κ₀.smooth.continuous.comp continuous_snd
  have hκ₁ : Continuous fun p : I × E => κ₁ p.2 :=
    κ₁.smooth.continuous.comp continuous_snd
  have hg : Continuous fun p : I × E => X.g p.2 :=
    X.smooth.continuous.comp continuous_snd
  have hcut : Continuous fun p : I × E =>
      (1 - (p.1 : ℝ)) * κ₀ p.2 + (p.1 : ℝ) * κ₁ p.2 :=
    ((continuous_const.sub hs).mul hκ₀).add (hs.mul hκ₁)
  have heq : lerpRaw S κ₀ κ₁ = fun p : I × E =>
      ((1 - (p.1 : ℝ)) * κ₀ p.2 + (p.1 : ℝ) * κ₁ p.2) •
          embedCLM n (X.g p.2) +
        (2 * ((1 - (p.1 : ℝ)) * κ₀ p.2 + (p.1 : ℝ) * κ₁ p.2) - 1) • eLast n := by
    funext p
    rfl
  rw [heq]
  exact (hcut.smul ((embedCLM n).continuous.comp hg)).add
    (((continuous_const.mul hcut).sub continuous_const).smul continuous_const)


-- @@ L188-190 verbatim
lemma lerpRaw_ne_zero (κ₀ κ₁ : PTCutoff S) (p : I × E) :
    lerpRaw S κ₀ κ₁ p ≠ 0 :=
  raw_ne_zero S (lerp S κ₀ κ₁ p.1) p.2


-- @@ L192-195 verbatim
/-- Normalized interpolation of endpoint collapse maps. -/
def lerpSphereMap (κ₀ κ₁ : PTCutoff S) : C(I × E, UnitSphere E) :=
  normalizeMap ⟨lerpRaw S κ₀ κ₁, continuous_lerpRaw S κ₀ κ₁⟩
    (lerpRaw_ne_zero S κ₀ κ₁)


-- @@ L197-216 verbatim
/-- Any two compactly supported signed endpoint cutoffs give homotopic sphere
maps on the ambient Euclidean space. -/
def sphereMapHomotopy (κ₀ κ₁ : PTCutoff S) :
    ContinuousMap.Homotopy (sphereMap S κ₀) (sphereMap S κ₁) where
  toFun := lerpSphereMap S κ₀ κ₁
  continuous_toFun := map_continuous (lerpSphereMap S κ₀ κ₁)
  map_zero_left x := by
    apply Subtype.ext
    have hraw : lerpRaw S κ₀ κ₁ (0, x) = raw S κ₀ x := by
      simp [lerpRaw, raw, lerp]
    change ‖lerpRaw S κ₀ κ₁ (0, x)‖⁻¹ • lerpRaw S κ₀ κ₁ (0, x) =
      ‖raw S κ₀ x‖⁻¹ • raw S κ₀ x
    rw [hraw]
  map_one_left x := by
    apply Subtype.ext
    have hraw : lerpRaw S κ₀ κ₁ (1, x) = raw S κ₁ x := by
      simp [lerpRaw, raw, lerp]
    change ‖lerpRaw S κ₀ κ₁ (1, x)‖⁻¹ • lerpRaw S κ₀ κ₁ (1, x) =
      ‖raw S κ₁ x‖⁻¹ • raw S κ₁ x
    rw [hraw]


-- @@ L218-225 verbatim
lemma lerpSphereMap_of_zero (κ₀ κ₁ : PTCutoff S) {s : I} {x : E}
    (h₀ : κ₀ x = 0) (h₁ : κ₁ x = 0) :
    lerpSphereMap S κ₀ κ₁ (s, x) = southPole n := by
  apply Subtype.ext
  have hraw : lerpRaw S κ₀ κ₁ (s, x) = -eLast n := by
    simp [lerpRaw, raw, lerp, h₀, h₁]
  change ‖lerpRaw S κ₀ κ₁ (s, x)‖⁻¹ • lerpRaw S κ₀ κ₁ (s, x) = -eLast n
  rw [hraw, norm_neg, norm_eLast, inv_one, one_smul]


-- @@ L227-251 verbatim
/-- Relative version: interpolation is fixed at the south pole wherever both
cutoffs vanish. -/
def sphereMapHomotopyRel (κ₀ κ₁ : PTCutoff S) (T : Set E)
    (h₀ : ∀ x ∈ T, κ₀ x = 0) (h₁ : ∀ x ∈ T, κ₁ x = 0) :
    ContinuousMap.HomotopyRel (sphereMap S κ₀) (sphereMap S κ₁) T where
  toFun := lerpSphereMap S κ₀ κ₁
  continuous_toFun := map_continuous (lerpSphereMap S κ₀ κ₁)
  map_zero_left x := by
    apply Subtype.ext
    have hraw : lerpRaw S κ₀ κ₁ (0, x) = raw S κ₀ x := by
      simp [lerpRaw, raw, lerp]
    change ‖lerpRaw S κ₀ κ₁ (0, x)‖⁻¹ • lerpRaw S κ₀ κ₁ (0, x) =
      ‖raw S κ₀ x‖⁻¹ • raw S κ₀ x
    rw [hraw]
  map_one_left x := by
    apply Subtype.ext
    have hraw : lerpRaw S κ₀ κ₁ (1, x) = raw S κ₁ x := by
      simp [lerpRaw, raw, lerp]
    change ‖lerpRaw S κ₀ κ₁ (1, x)‖⁻¹ • lerpRaw S κ₀ κ₁ (1, x) =
      ‖raw S κ₁ x‖⁻¹ • raw S κ₁ x
    rw [hraw]
  prop' s x hx := by
    change lerpSphereMap S κ₀ κ₁ (s, x) = sphereMap S κ₀ x
    rw [lerpSphereMap_of_zero S κ₀ κ₁ (h₀ x hx) (h₁ x hx)]
    exact (sphereMap_of_zero S κ₀ (h₀ x hx)).symm


-- @@ L253-253 verbatim
end PTCutoff


-- @@ L255-255 verbatim
end FiberSign


-- @@ L257-257 verbatim
namespace SignedFramedLevelCobordism.SignedSlabCutoff


-- @@ L259-260 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
  (C : SignedFramedLevelCobordism S₀ S₁)


-- @@ L262-262 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L263-263 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L265-272 verbatim
lemma contDiff_spaceTime_fixed (t : ℝ) :
    ContDiff ℝ ∞ (fun x : E => spaceTime x t) := by
  have heq : (fun x : E => spaceTime x t) =
      fun x => embedCLM (n + 1) x + t • eLast (n + 1) := by
    funext x
    exact spaceTime_eq_affine x t
  rw [heq]
  exact (embedCLM (n + 1)).contDiff.add contDiff_const


-- @@ L274-291 verbatim
/-- Restricting a compactly supported spacetime function to a fixed time slice
preserves compact support. -/
lemma hasCompactSupport_comp_spaceTime (χ : SignedSlabCutoff C) (t : ℝ) :
    HasCompactSupport (fun x : E => χ (spaceTime x t)) := by
  obtain ⟨R, hR⟩ := χ.compact_support.isBounded.subset_closedBall (0 : A)
  rw [hasCompactSupport_def]
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E) R)
    (isClosed_tsupport _)
  apply closure_minimal
  · intro x hx
    have hst : spaceTime x t ∈ tsupport χ :=
      subset_tsupport χ hx
    have hball := hR hst
    rw [mem_closedBall, dist_zero_right] at hball ⊢
    have hinit : initCLM (n + 1) (spaceTime x t) = x := initCLM_spaceTime x t
    rw [← hinit]
    exact (norm_spacePart_le (spaceTime x t)).trans hball
  · exact Metric.isClosed_closedBall


-- @@ L293-318 verbatim
/-- The cutoff induced on the incoming collar. -/
def sourcePTCutoff (χ : SignedSlabCutoff C) : FiberSign.PTCutoff S₀ where
  toFun x := χ (spaceTime x 0)
  smooth := χ.smooth.comp (contDiff_spaceTime_fixed (n := n) 0)
  range := fun x => χ.range (spaceTime x 0)
  positive_one := by
    rintro x ⟨hxg, hxpos⟩
    apply χ.positive_one
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [C.cobordism.collar_zero x 0 (by norm_num), C.source_eq]
      exact hxg
    · simp [vertC_spaceTime]
    · simp [vertC_spaceTime]
    · rw [C.collar_zero x 0 (by norm_num)]
      exact hxpos.le
  negative_zero := by
    rintro x ⟨hxg, hxneg⟩
    apply χ.negative_zero
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [C.cobordism.collar_zero x 0 (by norm_num), C.source_eq]
      exact hxg
    · simp [vertC_spaceTime]
    · simp [vertC_spaceTime]
    · rw [C.collar_zero x 0 (by norm_num)]
      exact hxneg.le
  compact_support := hasCompactSupport_comp_spaceTime C χ 0


-- @@ L320-345 verbatim
/-- The cutoff induced on the outgoing collar. -/
def targetPTCutoff (χ : SignedSlabCutoff C) : FiberSign.PTCutoff S₁ where
  toFun x := χ (spaceTime x 1)
  smooth := χ.smooth.comp (contDiff_spaceTime_fixed (n := n) 1)
  range := fun x => χ.range (spaceTime x 1)
  positive_one := by
    rintro x ⟨hxg, hxpos⟩
    apply χ.positive_one
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [C.cobordism.collar_one x 1 (by norm_num), C.target_eq]
      exact hxg
    · simp [vertC_spaceTime]
    · simp [vertC_spaceTime]
    · rw [C.collar_one x 1 (by norm_num)]
      exact hxpos.le
  negative_zero := by
    rintro x ⟨hxg, hxneg⟩
    apply χ.negative_zero
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [C.cobordism.collar_one x 1 (by norm_num), C.target_eq]
      exact hxg
    · simp [vertC_spaceTime]
    · simp [vertC_spaceTime]
    · rw [C.collar_one x 1 (by norm_num)]
      exact hxneg.le
  compact_support := hasCompactSupport_comp_spaceTime C χ 1


-- @@ L347-364 verbatim
/-- The incoming endpoint of the slab homotopy is exactly the endpoint collapse
constructed from the restricted cutoff. -/
lemma endpointPTCM_zero_eq (χ : SignedSlabCutoff C) :
    endpointPTCM C χ 0 = FiberSign.PTCutoff.sphereMap S₀ (sourcePTCutoff C χ) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  have hraw : raw C χ (spaceTime x 0) =
      FiberSign.PTCutoff.raw S₀ (sourcePTCutoff C χ) x := by
    rw [raw, FiberSign.PTCutoff.raw]
    change χ (spaceTime x 0) • embedCLM n (C.cobordism.G (spaceTime x 0)) + _ =
      χ (spaceTime x 0) • embedCLM n (X₀.g x) + _
    rw [C.cobordism.collar_zero x 0 (by norm_num), C.source_eq]
    rfl
  change ‖raw C χ (spaceTime x 0)‖⁻¹ • raw C χ (spaceTime x 0) =
    ‖FiberSign.PTCutoff.raw S₀ (sourcePTCutoff C χ) x‖⁻¹ •
      FiberSign.PTCutoff.raw S₀ (sourcePTCutoff C χ) x
  rw [hraw]


-- @@ L366-382 verbatim
/-- The outgoing endpoint has the analogous exact identification. -/
lemma endpointPTCM_one_eq (χ : SignedSlabCutoff C) :
    endpointPTCM C χ 1 = FiberSign.PTCutoff.sphereMap S₁ (targetPTCutoff C χ) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  have hraw : raw C χ (spaceTime x 1) =
      FiberSign.PTCutoff.raw S₁ (targetPTCutoff C χ) x := by
    rw [raw, FiberSign.PTCutoff.raw]
    change χ (spaceTime x 1) • embedCLM n (C.cobordism.G (spaceTime x 1)) + _ =
      χ (spaceTime x 1) • embedCLM n (X₁.g x) + _
    rw [C.cobordism.collar_one x 1 (by norm_num), C.target_eq]
    rfl
  change ‖raw C χ (spaceTime x 1)‖⁻¹ • raw C χ (spaceTime x 1) =
    ‖FiberSign.PTCutoff.raw S₁ (targetPTCutoff C χ) x‖⁻¹ •
      FiberSign.PTCutoff.raw S₁ (targetPTCutoff C χ) x
  rw [hraw]


-- @@ L384-384 verbatim
end SignedFramedLevelCobordism.SignedSlabCutoff


-- @@ L386-386 verbatim
end Submission
