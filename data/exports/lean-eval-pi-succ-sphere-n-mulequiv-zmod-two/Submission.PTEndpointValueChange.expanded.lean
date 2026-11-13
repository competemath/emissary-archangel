import Mathlib
import Submission.PTRelativeTransversality
import Submission.NormalizeMoves


-- @@ L5-22 verbatim
/-!
# Relative value change from an arbitrary signed PT endpoint

The horizontal coordinates of the normalized endpoint collapse vanish at the
south pole, hence using target zero directly creates an unbounded exterior
fiber.  This file installs the concrete patch

`((1 + s * κ) • X.g) - (s * λ) • y`.

Here `s` is the collar-flat time ramp, `κ` is the endpoint PT cutoff, and `λ`
is a compactly supported localizer which equals one on the original fiber and
is supported where the old sign and the endpoint collapse's vertical sign
agree.  Consequently the map is exactly `X.g` at spatial infinity, for every
time and every target.  On the open set where `s * λ > 0`, division by that
positive scalar gives a smooth quotient map; one relative Sard value `y`
makes the whole space-time zero set regular.  Where the weight vanishes, a zero
is forced back onto the original regular fiber.
-/


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-28 verbatim
open Set Function Metric

-- @@ L29-29 verbatim
open scoped Topology RealInnerProductSpace ContDiff


-- @@ L31-31 verbatim
variable {n : ℕ}


-- @@ L33-33 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L34-34 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L35-35 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L37-37 verbatim
namespace FiberSign.PTCutoff


-- @@ L39-39 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X) (κ : PTCutoff S)


-- @@ L41-42 verbatim
/-- The unnormalized endpoint collapse's vertical coordinate. -/
def endpointVertical (x : E) : ℝ := 2 * κ x - 1


-- @@ L44-45 verbatim
lemma contDiff_endpointVertical : ContDiff ℝ ∞ (endpointVertical S κ) :=
  (contDiff_const.mul κ.smooth).sub contDiff_const


-- @@ L47-48 verbatim
lemma continuous_endpointVertical : Continuous (endpointVertical S κ) :=
  (contDiff_endpointVertical S κ).continuous


-- @@ L50-54 verbatim
/-- Open neighborhood on which the original label and endpoint vertical label
are both nonzero and have the same sign. -/
def signAgreement : Set E :=
  {x | (0 < S x ∧ 0 < endpointVertical S κ x) ∨
    (S x < 0 ∧ endpointVertical S κ x < 0)}


-- @@ L56-65 verbatim
lemma isOpen_signAgreement : IsOpen (signAgreement S κ) := by
  have hSpos : IsOpen {x : E | 0 < S x} :=
    isOpen_lt continuous_const S.continuous
  have hSneg : IsOpen {x : E | S x < 0} :=
    isOpen_lt S.continuous continuous_const
  have hVpos : IsOpen {x : E | 0 < endpointVertical S κ x} :=
    isOpen_lt continuous_const (continuous_endpointVertical S κ)
  have hVneg : IsOpen {x : E | endpointVertical S κ x < 0} :=
    isOpen_lt (continuous_endpointVertical S κ) continuous_const
  exact (hSpos.inter hVpos).union (hSneg.inter hVneg)


-- @@ L67-77 verbatim
lemma fiber_subset_signAgreement : X.fiber ⊆ signAgreement S κ := by
  intro x hx
  rcases lt_or_gt_of_ne (S.nonzero x hx) with hneg | hpos
  · right
    refine ⟨hneg, ?_⟩
    rw [endpointVertical, κ.negative_zero x ⟨hx, hneg⟩]
    norm_num
  · left
    refine ⟨hpos, ?_⟩
    rw [endpointVertical, κ.positive_one x ⟨hx, hpos⟩]
    norm_num


-- @@ L79-87 verbatim
/-- A compactly supported smooth relative localizer.  Its nonzero locus is
contained in `signAgreement`, while it is identically one on the old fiber. -/
structure EndpointPatchLocalizer where
  toFun : E → ℝ
  smooth : ContDiff ℝ ∞ toFun
  range : ∀ x, toFun x ∈ Icc (0 : ℝ) 1
  fiber_one : ∀ x ∈ X.fiber, toFun x = 1
  nonzero_agrees : ∀ x, toFun x ≠ 0 → x ∈ signAgreement S κ
  compact_support : HasCompactSupport toFun


-- @@ L89-89 verbatim
namespace EndpointPatchLocalizer


-- @@ L91-92 verbatim
instance : CoeFun (EndpointPatchLocalizer S κ) fun _ => E → ℝ :=
  ⟨EndpointPatchLocalizer.toFun⟩


-- @@ L94-95 verbatim
lemma nonneg (P : EndpointPatchLocalizer S κ) (x : E) : 0 ≤ P x :=
  (P.range x).1


-- @@ L97-98 verbatim
lemma le_one (P : EndpointPatchLocalizer S κ) (x : E) : P x ≤ 1 :=
  (P.range x).2


-- @@ L100-137 verbatim
/-- Smooth Urysohn separation constructs a localizer for every endpoint. -/
theorem nonempty : Nonempty (EndpointPatchLocalizer S κ) := by
  have hopen : IsOpen (signAgreement S κ) := isOpen_signAgreement S κ
  have hsub : X.fiber ⊆ signAgreement S κ := fiber_subset_signAgreement S κ
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
  refine ⟨⟨⇑lam, hlamsmooth, hlam01, hlam1, ?_, hlamsupport⟩⟩
  intro x hx
  have hxU : x ∈ U := by
    by_contra hnot
    exact hx (hlam0 hnot)
  exact hδsub (Metric.thickening_subset_cthickening _ _ hxU)


-- @@ L139-139 verbatim
end EndpointPatchLocalizer


-- @@ L141-141 verbatim
variable (P : EndpointPatchLocalizer S κ)


-- @@ L143-145 verbatim
/-- Collar-flat interpolation scale.  It is at least one everywhere. -/
def patchScale (v : A) : ℝ :=
  1 + normRamp (vertC v) * κ (initCLM (n + 1) v)


-- @@ L147-149 verbatim
/-- Compactly localized target weight. -/
def patchWeight (v : A) : ℝ :=
  normRamp (vertC v) * P (initCLM (n + 1) v)


-- @@ L151-153 verbatim
/-- The unshifted, exterior-safe defining map. -/
def patchBase (v : A) : F :=
  patchScale S κ v • X.g (initCLM (n + 1) v)


-- @@ L155-157 verbatim
/-- The complete relative value-change map. -/
def patchCobMap (y : F) (v : A) : F :=
  patchBase S κ v - patchWeight S κ P v • y


-- @@ L159-162 verbatim
lemma contDiff_patchScale : ContDiff ℝ ∞ (patchScale S κ) := by
  exact contDiff_const.add
    ((contDiff_normRamp.comp contDiff_vertC).mul
      (κ.smooth.comp (initCLM (n + 1)).contDiff))


-- @@ L164-166 verbatim
lemma contDiff_patchWeight : ContDiff ℝ ∞ (patchWeight S κ P) := by
  exact (contDiff_normRamp.comp contDiff_vertC).mul
    (P.smooth.comp (initCLM (n + 1)).contDiff)


-- @@ L168-170 verbatim
lemma contDiff_patchBase : ContDiff ℝ ∞ (patchBase S κ) := by
  exact (contDiff_patchScale S κ).smul
    (X.smooth.comp (initCLM (n + 1)).contDiff)


-- @@ L172-174 verbatim
lemma contDiff_patchCobMap (y : F) : ContDiff ℝ ∞ (patchCobMap S κ P y) := by
  exact (contDiff_patchBase S κ).sub
    ((contDiff_patchWeight S κ P).smul contDiff_const)


-- @@ L176-180 verbatim
lemma patchScale_pos (v : A) : 0 < patchScale S κ v := by
  have hs := normRamp_nonneg (vertC v)
  have hκ := (κ.range (initCLM (n + 1) v)).1
  dsimp [patchScale]
  nlinarith


-- @@ L182-184 verbatim
lemma patchWeight_nonneg (v : A) : 0 ≤ patchWeight S κ P v :=
  mul_nonneg (normRamp_nonneg _)
    (EndpointPatchLocalizer.nonneg S κ P (initCLM (n + 1) v))


-- @@ L186-188 verbatim
/-- Open region on which division by the target weight is legitimate. -/
def patchTransition : Set A :=
  {v | 1 / 4 < vertC v ∧ 0 < P (initCLM (n + 1) v)}


-- @@ L190-193 verbatim
lemma isOpen_patchTransition : IsOpen (patchTransition S κ P) := by
  exact (isOpen_lt continuous_const contDiff_vertC.continuous).inter
    (isOpen_lt continuous_const
      (P.smooth.continuous.comp (initCLM (n + 1)).continuous))


-- @@ L195-199 verbatim
lemma normRamp_pos_of_mem_patchTransition {v : A}
    (hv : v ∈ patchTransition S κ P) : 0 < normRamp (vertC v) := by
  apply Real.smoothTransition.pos_of_pos
  change 0 < 2 * (vertC v - 1 / 4)
  linarith [hv.1]


-- @@ L201-203 verbatim
lemma patchWeight_pos {v : A} (hv : v ∈ patchTransition S κ P) :
    0 < patchWeight S κ P v :=
  mul_pos (normRamp_pos_of_mem_patchTransition S κ P hv) hv.2


-- @@ L205-207 verbatim
/-- Quotient used for the relative Sard argument. -/
def patchQuotient (v : A) : F :=
  (patchWeight S κ P v)⁻¹ • patchBase S κ v


-- @@ L209-215 verbatim
lemma contDiffOn_patchQuotient :
    ContDiffOn ℝ ∞ (patchQuotient S κ P) (patchTransition S κ P) := by
  intro v hv
  have hw : patchWeight S κ P v ≠ 0 :=
    (patchWeight_pos S κ P hv).ne'
  exact (((contDiff_patchWeight S κ P).contDiffAt.inv hw).smul
    (contDiff_patchBase S κ).contDiffAt).contDiffWithinAt


-- @@ L217-224 verbatim
lemma patchCobMap_eq_weight_smul (y : F) {v : A}
    (hv : v ∈ patchTransition S κ P) :
    patchCobMap S κ P y v =
      patchWeight S κ P v • (patchQuotient S κ P v - y) := by
  have hw : patchWeight S κ P v ≠ 0 :=
    (patchWeight_pos S κ P hv).ne'
  rw [patchCobMap, patchQuotient, smul_sub, smul_smul,
    mul_inv_cancel₀ hw, one_smul]


-- @@ L226-230 verbatim
/-- The target endpoint map.  Outside the localizer it is simply a positive
multiple of the original defining map; in particular at spatial infinity it
is exactly the original defining map because `κ` and `P` vanish there. -/
def patchTargetMap (y : F) (x : E) : F :=
  (1 + κ x) • X.g x - P x • y


-- @@ L232-234 verbatim
lemma contDiff_patchTargetMap (y : F) : ContDiff ℝ ∞ (patchTargetMap S κ P y) := by
  exact (contDiff_const.add κ.smooth).smul X.smooth |>.sub
    (P.smooth.smul contDiff_const)


-- @@ L236-240 verbatim
lemma patchCobMap_collar_zero (y : F) (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    patchCobMap S κ P y (spaceTime x t) = X.g x := by
  rw [patchCobMap, patchBase, patchScale, patchWeight, vertC_spaceTime,
    initCLM_spaceTime, normRamp_of_le_quarter ht]
  simp


-- @@ L242-246 verbatim
lemma patchCobMap_collar_one (y : F) (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    patchCobMap S κ P y (spaceTime x t) = patchTargetMap S κ P y x := by
  rw [patchCobMap, patchBase, patchScale, patchWeight, patchTargetMap,
    vertC_spaceTime, initCLM_spaceTime, normRamp_of_three_quarter_le ht]
  simp


-- @@ L248-261 verbatim
/-- Every spatial zero lies either on the old bounded fiber or in the compact
support of the localizer. -/
lemma spatial_mem_fiber_or_tsupport {y : F} {v : A}
    (hv : patchCobMap S κ P y v = 0) :
    initCLM (n + 1) v ∈ X.fiber ∨
      initCLM (n + 1) v ∈ tsupport P := by
  by_cases hP : P (initCLM (n + 1) v) = 0
  · left
    have hw : patchWeight S κ P v = 0 := by simp [patchWeight, hP]
    have hb : patchBase S κ v = 0 := by
      simpa [patchCobMap, hw] using hv
    exact (smul_eq_zero.mp hb).resolve_left (patchScale_pos S κ v).ne'
  · right
    exact subset_tsupport P hP


-- @@ L263-276 verbatim
lemma patchCobMap_spatial_bounded (y : F) :
    ∃ R : ℝ, ∀ v : A, patchCobMap S κ P y v = 0 →
      ‖initCLM (n + 1) v‖ ≤ R := by
  obtain ⟨R₀, hR₀⟩ := X.fiber_bounded.subset_closedBall 0
  obtain ⟨R₁, hR₁⟩ := P.compact_support.isBounded.subset_closedBall 0
  refine ⟨max R₀ R₁, ?_⟩
  intro v hv
  rcases spatial_mem_fiber_or_tsupport S κ P hv with h | h
  · have := hR₀ h
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  · have := hR₁ h
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_right _ _)


-- @@ L278-356 verbatim
/-- Relative regularity of the whole patched space-time map. -/
theorem patchCobMap_regular {y : F}
    (hreg : IsRegularValueOn (patchQuotient S κ P)
      (patchTransition S κ P) y) :
    ∀ v : A, patchCobMap S κ P y v = 0 →
      Function.Surjective (fderiv ℝ (patchCobMap S κ P y) v) := by
  intro v hv
  by_cases hw0 : patchWeight S κ P v = 0
  · have hb : patchBase S κ v = 0 := by
      simpa [patchCobMap, hw0] using hv
    have hg : X.g (initCLM (n + 1) v) = 0 :=
      (smul_eq_zero.mp hb).resolve_left (patchScale_pos S κ v).ne'
    have hPone : P (initCLM (n + 1) v) = 1 := P.fiber_one _ hg
    have hs0 : normRamp (vertC v) = 0 := by
      rw [patchWeight, hPone, mul_one] at hw0
      exact hw0
    apply surjective_fderiv_of_slice (contDiff_patchCobMap S κ P y)
    have hslice : (fun x' : E =>
        patchCobMap S κ P y (spaceTime x' (vertC v))) = X.g := by
      funext x'
      rw [patchCobMap, patchBase, patchScale, patchWeight,
        vertC_spaceTime, initCLM_spaceTime, hs0]
      simp
    rw [hslice]
    exact X.regular _ hg
  · have hwpos : 0 < patchWeight S κ P v :=
      lt_of_le_of_ne (patchWeight_nonneg S κ P v) (Ne.symm hw0)
    have hsne : normRamp (vertC v) ≠ 0 := by
      intro hs
      exact hw0 (by simp [patchWeight, hs])
    have hPne : P (initCLM (n + 1) v) ≠ 0 := by
      intro hP
      exact hw0 (by simp [patchWeight, hP])
    have ht : 1 / 4 < vertC v := by
      by_contra hnot
      have hs := normRamp_of_le_quarter (le_of_not_gt hnot)
      exact hsne hs
    have hPpos : 0 < P (initCLM (n + 1) v) :=
      lt_of_le_of_ne
        (EndpointPatchLocalizer.nonneg S κ P (initCLM (n + 1) v))
        (Ne.symm hPne)
    have hvU : v ∈ patchTransition S κ P := ⟨ht, hPpos⟩
    have hweighted : patchWeight S κ P v •
        (patchQuotient S κ P v - y) = 0 := by
      rw [← patchCobMap_eq_weight_smul S κ P y hvU]
      exact hv
    have hsub : patchQuotient S κ P v - y = 0 :=
      (smul_eq_zero.mp hweighted).resolve_left hwpos.ne'
    have hPhi : patchQuotient S κ P v = y := sub_eq_zero.mp hsub
    have hsurjWithin := hreg v hvU hPhi
    have hsurj : Function.Surjective
        (fderiv ℝ (patchQuotient S κ P) v) := by
      rwa [fderivWithin_of_isOpen (isOpen_patchTransition S κ P) hvU]
        at hsurjWithin
    have hEv : patchCobMap S κ P y =ᶠ[𝓝 v]
        fun z => patchWeight S κ P z • (patchQuotient S κ P z - y) :=
      Filter.eventuallyEq_of_mem
        ((isOpen_patchTransition S κ P).mem_nhds hvU)
        fun _ hz => patchCobMap_eq_weight_smul S κ P y hz
    have hwdiff : DifferentiableAt ℝ (patchWeight S κ P) v :=
      (contDiff_patchWeight S κ P).differentiable infty_ne_zero |>.differentiableAt
    have hQdiff : DifferentiableAt ℝ (patchQuotient S κ P) v :=
      ((contDiffOn_patchQuotient S κ P).contDiffAt
        ((isOpen_patchTransition S κ P).mem_nhds hvU)).differentiableAt
        infty_ne_zero
    have hsubdiff : DifferentiableAt ℝ
        (fun z => patchQuotient S κ P z - y) v :=
      hQdiff.sub (differentiableAt_const (c := y))
    have hfd : fderiv ℝ (patchCobMap S κ P y) v =
        patchWeight S κ P v • fderiv ℝ (patchQuotient S κ P) v := by
      rw [hEv.fderiv_eq, fderiv_fun_smul hwdiff hsubdiff,
        fderiv_sub_const y, hPhi, sub_self]
      simp
    rw [hfd]
    intro z
    obtain ⟨u, hu⟩ := hsurj ((patchWeight S κ P v)⁻¹ • z)
    refine ⟨u, ?_⟩
    rw [smul_apply, hu, smul_smul,
      mul_inv_cancel₀ hwpos.ne', one_smul]


-- @@ L358-411 verbatim
/-- The patched target is a genuine framed level set. -/
def patchTargetLevelSet (y : F)
    (hreg : IsRegularValueOn (patchQuotient S κ P)
      (patchTransition S κ P) y) : FramedLevelSet n where
  g := patchTargetMap S κ P y
  smooth := contDiff_patchTargetMap S κ P y
  fiber_bounded := by
    obtain ⟨R, hR⟩ := patchCobMap_spatial_bounded S κ P y
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨R, ?_⟩
    intro x hx
    have hzero : patchCobMap S κ P y (spaceTime x 1) = 0 := by
      rw [patchCobMap_collar_one S κ P y x (by norm_num)]
      exact hx
    have := hR (spaceTime x 1) hzero
    rw [mem_closedBall, dist_zero_right]
    rw [initCLM_spaceTime x 1] at this
    exact this
  regular := by
    intro x hx
    let v : A := spaceTime x 1
    have hv : patchCobMap S κ P y v = 0 := by
      dsimp [v]
      rw [patchCobMap_collar_one S κ P y x (by norm_num)]
      exact hx
    have hsurj := patchCobMap_regular S κ P hreg v hv
    have hlocal : ∀ w : A, 3 / 4 < vertC w →
        patchCobMap S κ P y w =
          patchTargetMap S κ P y (initCLM (n + 1) w) := by
      intro w hw
      calc
        patchCobMap S κ P y w = patchCobMap S κ P y
            (spaceTime (initCLM (n + 1) w) (vertC w)) :=
          congrArg (patchCobMap S κ P y) (spaceTime_init_vert w).symm
        _ = patchTargetMap S κ P y (initCLM (n + 1) w) :=
          patchCobMap_collar_one S κ P y _ (le_of_lt hw)
    have hEv : patchCobMap S κ P y =ᶠ[𝓝 v]
        fun w => patchTargetMap S κ P y (initCLM (n + 1) w) :=
      Filter.eventuallyEq_of_mem
        ((isOpen_lt_vert (3 / 4)).mem_nhds
          (by dsimp [v]; rw [vertC_spaceTime]; norm_num))
        fun w hw => hlocal w hw
    have hgd : HasFDerivAt (patchTargetMap S κ P y)
        (fderiv ℝ (patchTargetMap S κ P y) (initCLM (n + 1) v))
        (initCLM (n + 1) v) :=
      ((contDiff_patchTargetMap S κ P y).differentiable infty_ne_zero _).hasFDerivAt
    have hfd : fderiv ℝ (patchCobMap S κ P y) v =
        (fderiv ℝ (patchTargetMap S κ P y) (initCLM (n + 1) v)).comp
          (initCLM (n + 1)) := by
      rw [hEv.fderiv_eq]
      exact (hgd.comp v (initCLM (n + 1)).hasFDerivAt).fderiv
    rw [hfd, ContinuousLinearMap.coe_comp] at hsurj
    have hs := hsurj.of_comp
    simpa [v, initCLM_spaceTime] using hs


-- @@ L413-438 verbatim
/-- The endpoint collapse's vertical coordinate labels the patched target
fiber. -/
def patchTargetSign (y : F)
    (hreg : IsRegularValueOn (patchQuotient S κ P)
      (patchTransition S κ P) y) :
    FiberSign (patchTargetLevelSet S κ P y hreg) where
  toFun := endpointVertical S κ
  continuous := continuous_endpointVertical S κ
  nonzero := by
    intro x hx hzero
    change patchTargetMap S κ P y x = 0 at hx
    by_cases hP : P x = 0
    · have hb : (1 + κ x) • X.g x = 0 := by
        simpa [patchTargetMap, hP] using hx
      have hscale : (1 + κ x : ℝ) ≠ 0 := by
        have hκ := (κ.range x).1
        positivity
      have hg : x ∈ X.fiber := (smul_eq_zero.mp hb).resolve_left hscale
      have hagree := fiber_subset_signAgreement S κ hg
      rcases hagree with h | h
      · exact (ne_of_gt h.2) hzero
      · exact (ne_of_lt h.2) hzero
    · have hagree := P.nonzero_agrees x hP
      rcases hagree with h | h
      · exact (ne_of_gt h.2) hzero
      · exact (ne_of_lt h.2) hzero


-- @@ L440-443 verbatim
/-- Label used on the relative value-change cobordism. -/
def patchLabel (v : A) : ℝ :=
  (1 - normRamp (vertC v)) * S (initCLM (n + 1) v) +
    normRamp (vertC v) * endpointVertical S κ (initCLM (n + 1) v)


-- @@ L445-451 verbatim
lemma continuous_patchLabel : Continuous (patchLabel S κ) := by
  have hs : Continuous fun v : A => normRamp (vertC v) :=
    contDiff_normRamp.continuous.comp contDiff_vertC.continuous
  exact ((continuous_const.sub hs).mul
      (S.continuous.comp (initCLM (n + 1)).continuous)).add
    (hs.mul ((continuous_endpointVertical S κ).comp
      (initCLM (n + 1)).continuous))


-- @@ L453-463 verbatim
lemma spatial_signAgreement_of_patchCobMap_eq_zero {y : F} {v : A}
    (hv : patchCobMap S κ P y v = 0) :
    initCLM (n + 1) v ∈ signAgreement S κ := by
  by_cases hP : P (initCLM (n + 1) v) = 0
  · have hw : patchWeight S κ P v = 0 := by simp [patchWeight, hP]
    have hb : patchBase S κ v = 0 := by
      simpa [patchCobMap, hw] using hv
    have hg : initCLM (n + 1) v ∈ X.fiber :=
      (smul_eq_zero.mp hb).resolve_left (patchScale_pos S κ v).ne'
    exact fiber_subset_signAgreement S κ hg
  · exact P.nonzero_agrees _ hP


-- @@ L465-497 verbatim
lemma patchLabel_ne_zero_of_patchCobMap_eq_zero {y : F} {v : A}
    (hv : patchCobMap S κ P y v = 0) : patchLabel S κ v ≠ 0 := by
  have hagree := spatial_signAgreement_of_patchCobMap_eq_zero S κ P hv
  have hs0 := normRamp_nonneg (vertC v)
  have hs1 := normRamp_le_one (vertC v)
  rcases hagree with hpos | hneg
  · have h1 : 0 ≤ (1 - normRamp (vertC v)) *
        S (initCLM (n + 1) v) := mul_nonneg (by linarith) hpos.1.le
    have h2 : 0 ≤ normRamp (vertC v) *
        endpointVertical S κ (initCLM (n + 1) v) :=
      mul_nonneg hs0 hpos.2.le
    rcases le_total (normRamp (vertC v)) (1 / 2) with hs | hs
    · have hstrict : 0 < (1 - normRamp (vertC v)) *
          S (initCLM (n + 1) v) := mul_pos (by linarith) hpos.1
      exact ne_of_gt (by dsimp [patchLabel]; linarith)
    · have hstrict : 0 < normRamp (vertC v) *
          endpointVertical S κ (initCLM (n + 1) v) :=
        mul_pos (by linarith) hpos.2
      exact ne_of_gt (by dsimp [patchLabel]; linarith)
  · have h1 : (1 - normRamp (vertC v)) *
        S (initCLM (n + 1) v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg.1.le
    have h2 : normRamp (vertC v) *
        endpointVertical S κ (initCLM (n + 1) v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs0 hneg.2.le
    rcases le_total (normRamp (vertC v)) (1 / 2) with hs | hs
    · have hstrict : (1 - normRamp (vertC v)) *
          S (initCLM (n + 1) v) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg.1
      exact ne_of_lt (by dsimp [patchLabel]; linarith)
    · have hstrict : normRamp (vertC v) *
          endpointVertical S κ (initCLM (n + 1) v) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) hneg.2
      exact ne_of_lt (by dsimp [patchLabel]; linarith)


-- @@ L499-531 verbatim
/-- The actual signed relative value-change cobordism. -/
def patchSignedCobordism (y : F)
    (hreg : IsRegularValueOn (patchQuotient S κ P)
      (patchTransition S κ P) y) :
    SignedFramedLevelCobordism S (patchTargetSign S κ P y hreg) where
  cobordism := {
    X₀ := X
    X₁ := patchTargetLevelSet S κ P y hreg
    G := patchCobMap S κ P y
    smooth := contDiff_patchCobMap S κ P y
    spatial_bounded := patchCobMap_spatial_bounded S κ P y
    regular := patchCobMap_regular S κ P hreg
    collar_zero := patchCobMap_collar_zero S κ P y
    collar_one := patchCobMap_collar_one S κ P y
  }
  source_eq := rfl
  target_eq := rfl
  toFun := patchLabel S κ
  continuous := continuous_patchLabel S κ
  nonzero := by
    intro v hv
    exact patchLabel_ne_zero_of_patchCobMap_eq_zero S κ P hv
  collar_zero := by
    intro x t ht
    rw [patchLabel, vertC_spaceTime, initCLM_spaceTime,
      normRamp_of_le_quarter ht]
    ring
  collar_one := by
    intro x t ht
    change patchLabel S κ (spaceTime x t) = endpointVertical S κ x
    rw [patchLabel, vertC_spaceTime, initCLM_spaceTime,
      normRamp_of_three_quarter_le ht]
    ring


-- @@ L533-551 verbatim
/-- Relative Sard values exist in a fixed small punctured ball. -/
theorem exists_small_patch_regular_value (hn : 0 < n) :
    ∃ y : F, 0 < ‖y‖ ∧ ‖y‖ < 1 / 8 ∧
      IsRegularValueOn (patchQuotient S κ P) (patchTransition S κ P) y := by
  let z₀ : F := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 / 16 : ℝ)
  have hz₀norm : ‖z₀‖ = 1 / 16 := by
    rw [show z₀ = EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 / 16 : ℝ) from rfl,
      PiLp.norm_single, Real.norm_eq_abs]
    norm_num
  obtain ⟨y, hyreg, hyball⟩ :=
    (sard_dense_regular_values_on (isOpen_patchTransition S κ P)
      (contDiffOn_patchQuotient S κ P)).exists_mem_open Metric.isOpen_ball
      (Metric.nonempty_ball.mpr (by norm_num : (0 : ℝ) < 1 / 32))
  have hdist : ‖y - z₀‖ < 1 / 32 := by
    rw [← dist_eq_norm]
    exact hyball
  have habs : |‖y‖ - ‖z₀‖| ≤ ‖y - z₀‖ := abs_norm_sub_norm_le y z₀
  rw [hz₀norm, abs_le] at habs
  exact ⟨y, by linarith [habs.1], by linarith [habs.2], hyreg⟩


-- @@ L553-566 verbatim
/-- Public endpoint value-change theorem.  It starts from an arbitrary signed
framed level set and any endpoint PT cutoff, and ends at the compactly patched
nonzero Sard level induced by that cutoff. -/
theorem exists_signedCobordism_to_patchTarget (hn : 0 < n) :
    ∃ (P : EndpointPatchLocalizer S κ) (y : F)
      (hreg : IsRegularValueOn (patchQuotient S κ P)
        (patchTransition S κ P) y),
      0 < ‖y‖ ∧ ‖y‖ < 1 / 8 ∧
      Nonempty (SignedFramedLevelCobordism S
        (patchTargetSign S κ P y hreg)) := by
  obtain ⟨P⟩ := EndpointPatchLocalizer.nonempty S κ
  obtain ⟨y, hypos, hy8, hreg⟩ :=
    exists_small_patch_regular_value S κ P hn
  exact ⟨P, y, hreg, hypos, hy8, ⟨patchSignedCobordism S κ P y hreg⟩⟩


-- @@ L568-568 verbatim
end FiberSign.PTCutoff


-- @@ L570-570 verbatim
end Submission
