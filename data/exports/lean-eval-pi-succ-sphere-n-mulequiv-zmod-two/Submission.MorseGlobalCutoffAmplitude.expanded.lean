import Mathlib
import Submission.MorseFiniteSharedCovector
import Submission.MorseGlobalCriticalAudit
import Submission.PerturbedIFTSurfaceCover
import Submission.SmallVerticalAmplitudeInverse


-- @@ L7-16 verbatim
/-!
# A small global cutoff amplitude from one shared Morse covector

Multiplication by a fixed compactly supported smooth cutoff is uniformly
Lipschitz-small when the ambient covector is sufficiently small.  Combining
that quantitative neighborhood of zero with the finite sequential Sard theorem
produces one shared covector which is simultaneously Morse-good on every IFT
core and whose globally localized forward vertical shift is small enough to
invert.
-/


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Set Function Filter Metric

-- @@ L21-21 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L23-23 verbatim
namespace Submission


-- @@ L25-25 verbatim
variable {n : ℕ}


-- @@ L27-27 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L28-28 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))

-- @@ L29-29 verbatim
local notation "Cov" => E' →L[ℝ] ℝ


-- @@ L31-31 verbatim
namespace SmoothCutoff


-- @@ L33-33 verbatim
variable {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}

-- @@ L34-34 verbatim
include n


-- @@ L36-38 verbatim
/-- Localize one ambient linear covector by the fixed global cutoff. -/
def localizeCovector (χ : SmoothCutoff K U) (A : Cov) : E' → ℝ :=
  χ.localize (n := n) A


-- @@ L40-42 verbatim
theorem contDiff_localizeCovector (χ : SmoothCutoff K U) (A : Cov) :
    ContDiff ℝ ∞ (χ.localizeCovector (n := n) A) :=
  χ.contDiff_localize (n := n) A.contDiff


-- @@ L44-47 verbatim
theorem hasCompactSupport_localizeCovector
    (χ : SmoothCutoff K U) (A : Cov) :
    HasCompactSupport (χ.localizeCovector (n := n) A) :=
  χ.hasCompactSupport_localize (n := n) A


-- @@ L49-124 verbatim
/-- Quantitative continuity at the zero covector: every sufficiently small
ambient covector becomes globally `1/4`-Lipschitz after multiplication by the
fixed compactly supported cutoff. -/
theorem exists_lipschitz_radius_localizeCovector
    (χ : SmoothCutoff K U) :
    ∃ δ > 0, ∀ A : Cov, ‖A‖ < δ →
      LipschitzWith (⟨1 / 4, by norm_num⟩ : NNReal)
        (χ.localizeCovector (n := n) A) := by
  let weight : E' → ℝ := fun v => ‖v‖ * ‖fderiv ℝ χ v‖
  have hweightContinuous : Continuous weight := by
    exact continuous_norm.mul
      (χ.smooth.continuous_fderiv (by simp)).norm
  have hweightSupport : HasCompactSupport weight := by
    dsimp [weight]
    exact HasCompactSupport.mul_left (f := fun v : E' => ‖v‖)
      (χ.compact_support.fderiv (𝕜 := ℝ)).norm
  obtain ⟨M, hM⟩ :=
    hweightContinuous.bounded_above_of_compact_support hweightSupport
  let R : ℝ := max M 0
  have hR : 0 ≤ R := le_max_right _ _
  have hweight (v : E') : weight v ≤ R := by
    calc
      weight v = ‖weight v‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      _ ≤ M := hM v
      _ ≤ R := le_max_left _ _
  let δ : ℝ := 1 / (4 * (R + 1))
  have hden : 0 < 4 * (R + 1) := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  refine ⟨δ, hδ, ?_⟩
  intro A hA
  have hsmooth := χ.contDiff_localizeCovector (n := n) A
  apply lipschitzWith_of_nnnorm_fderiv_le
    (hsmooth.differentiable (by simp))
  intro v
  have hfd :
      fderiv ℝ (χ.localizeCovector (n := n) A) v =
        χ v • A + A v • fderiv ℝ χ v := by
    simpa [localizeCovector] using χ.fderiv_localize (n := n) A.contDiff v
  have hχ : |χ v| ≤ 1 := by
    rw [abs_of_nonneg (χ.range v).1]
    exact (χ.range v).2
  have hAv : |A v| ≤ ‖A‖ * ‖v‖ := by
    simpa [Real.norm_eq_abs] using A.le_opNorm v
  have hbound :
      ‖fderiv ℝ (χ.localizeCovector (n := n) A) v‖ < 1 / 4 := by
    rw [hfd]
    calc
      ‖χ v • A + A v • fderiv ℝ χ v‖ ≤
          ‖χ v • A‖ + ‖A v • fderiv ℝ χ v‖ := norm_add_le _ _
      _ = |χ v| * ‖A‖ + |A v| * ‖fderiv ℝ χ v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * ‖A‖ + (‖A‖ * ‖v‖) * ‖fderiv ℝ χ v‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hχ (norm_nonneg A))
          (mul_le_mul_of_nonneg_right hAv (norm_nonneg _))
      _ = ‖A‖ * (1 + weight v) := by
        dsimp [weight]
        ring
      _ ≤ ‖A‖ * (1 + R) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
        linarith [hweight v]
      _ < 1 / 4 := by
        have hR1 : 0 < R + 1 := by positivity
        have hm := mul_lt_mul_of_pos_right hA hR1
        have heq : δ * (R + 1) = 1 / 4 := by
          dsimp [δ]
          field_simp [hR1.ne']
        calc
          ‖A‖ * (1 + R) = ‖A‖ * (R + 1) := by ring
          _ < δ * (R + 1) := hm
          _ = 1 / 4 := heq
  apply NNReal.coe_le_coe.mp
  change ‖fderiv ℝ (χ.localizeCovector (n := n) A) v‖ ≤ (1 / 4 : ℝ)
  exact hbound.le


-- @@ L126-155 verbatim
/-- Package an unscaled localized covector as a small forward vertical
amplitude.  The fixed constant `1/4` also makes its inverse small. -/
def smallForwardOfCovector
    (χ : SmoothCutoff K U)
    (hcollar : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ))
    (A : Cov)
    (hlip : LipschitzWith (⟨1 / 4, by norm_num⟩ : NNReal)
      (χ.localizeCovector (n := n) A)) :
    SmallVerticalAmplitude (n := n) := by
  let κ : NNReal := ⟨1 / 4, by norm_num⟩
  have hκNN : κ < 1 := by
    exact_mod_cast (show (1 / 4 : ℝ) < 1 by norm_num)
  have hsmooth := χ.contDiff_localizeCovector (n := n) A
  have hsmall :
      ∀ v, ‖fderiv ℝ (χ.localizeCovector (n := n) A) v‖ < 1 := by
    intro v
    have hderiv :
        ‖fderiv ℝ (χ.localizeCovector (n := n) A) v‖ ≤ (κ : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ hlip
    have hκ : (κ : ℝ) < 1 := by exact_mod_cast hκNN
    exact hderiv.trans_lt hκ
  let base : VerticalAmplitude (n := n) :=
    VerticalAmplitude.ofNormFDerivLtOne
      (χ.localizeCovector (n := n) A) hsmooth
      (χ.localize_collar_zero (n := n) hcollar A) hsmall
  exact {
    toVerticalAmplitude := base
    K := κ
    K_lt_one := hκNN
    lipschitz := hlip }


-- @@ L157-165 verbatim
@[simp] theorem smallForwardOfCovector_apply
    (χ : SmoothCutoff K U)
    (hcollar : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ))
    (A : Cov)
    (hlip : LipschitzWith (⟨1 / 4, by norm_num⟩ : NNReal)
      (χ.localizeCovector (n := n) A)) (v : E') :
    χ.smallForwardOfCovector (n := n) hcollar A hlip v =
      χ.localizeCovector (n := n) A v :=
  rfl


-- @@ L167-175 verbatim
theorem smallForwardOfCovector_twice_K_lt_one
    (χ : SmoothCutoff K U)
    (hcollar : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ))
    (A : Cov)
    (hlip : LipschitzWith (⟨1 / 4, by norm_num⟩ : NNReal)
      (χ.localizeCovector (n := n) A)) :
    2 * (χ.smallForwardOfCovector (n := n) hcollar A hlip).K < 1 := by
  change 2 * (⟨1 / 4, by norm_num⟩ : NNReal) < 1
  exact_mod_cast (show 2 * (1 / 4 : ℝ) < 1 by norm_num)


-- @@ L177-177 verbatim
end SmoothCutoff


-- @@ L179-179 verbatim
/-! ## The actual cutoff height on one IFT chart -/


-- @@ L181-181 verbatim
namespace IFTSurfaceChart


-- @@ L183-183 verbatim
variable {C : FramedLevelCobordism n}

-- @@ L184-184 verbatim
variable {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}


-- @@ L186-190 verbatim
/-- The time of the globally cutoff forward deformation, jointly in the one
ambient covector and the chart parameter. -/
def cutoffAffineHeightUncurried (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) : Cov × E₂ → ℝ :=
  fun z => P.time z.2 + χ (P.param z.2) * z.1 (P.param z.2)


-- @@ L192-197 verbatim
theorem contDiff_cutoffAffineHeightUncurried
    (P : IFTSurfaceChart C) (χ : SmoothCutoff K U) :
    ContDiff ℝ ∞ (P.cutoffAffineHeightUncurried χ) := by
  exact (P.contDiff_time.comp contDiff_snd).add
    ((χ.smooth.comp (P.param_smooth.comp contDiff_snd)).mul
      (contDiff_fst.clm_apply (P.param_smooth.comp contDiff_snd)))


-- @@ L199-202 verbatim
/-- Curried chart height of the global cutoff deformation. -/
def cutoffAffineHeight (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) (A : Cov) (u : E₂) : ℝ :=
  P.cutoffAffineHeightUncurried χ (A, u)


-- @@ L204-208 verbatim
theorem contDiff_cutoffAffineHeight (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) (A : Cov) :
    ContDiff ℝ ∞ (P.cutoffAffineHeight χ A) :=
  P.contDiff_cutoffAffineHeightUncurried χ |>.comp
    (contDiff_const.prodMk contDiff_id)


-- @@ L210-213 verbatim
/-- Joint chart gradient of the genuinely cutoff global height. -/
def cutoffAffineGradient (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) (z : Cov × E₂) : E₂ :=
  scalarAdjointCLM (rightFDeriv (P.cutoffAffineHeightUncurried χ) z) 1


-- @@ L215-220 verbatim
theorem contDiff_cutoffAffineGradient (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) :
    ContDiff ℝ ∞ (P.cutoffAffineGradient χ) := by
  exact (scalarAdjointCLM.contDiff.comp
    (contDiff_rightFDeriv
      (P.contDiff_cutoffAffineHeightUncurried χ))).clm_apply contDiff_const


-- @@ L222-232 verbatim
theorem cutoffAffineGradient_eq_chartGradient
    (P : IFTSurfaceChart C) (χ : SmoothCutoff K U)
    (A : Cov) (u : E₂) :
    P.cutoffAffineGradient χ (A, u) =
      chartGradient (P.cutoffAffineHeight χ A) u := by
  unfold cutoffAffineGradient chartGradient
  have h := fderiv_section_eq_rightFDeriv
    (P.contDiff_cutoffAffineHeightUncurried χ) A u
  change fderiv ℝ (P.cutoffAffineHeight χ A) u =
    rightFDeriv (P.cutoffAffineHeightUncurried χ) (A, u) at h
  rw [h]


-- @@ L234-238 verbatim
theorem cutoffAffineHeight_zero (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) :
    P.cutoffAffineHeight χ 0 = P.time := by
  funext u
  simp [cutoffAffineHeight, cutoffAffineHeightUncurried]


-- @@ L240-244 verbatim
theorem cutoffAffineGradient_zero (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) (u : E₂) :
    P.cutoffAffineGradient χ (0, u) = chartGradient P.time u := by
  rw [P.cutoffAffineGradient_eq_chartGradient,
    P.cutoffAffineHeight_zero]


-- @@ L246-249 verbatim
/-- Joint Hessian of the genuinely cutoff chart height. -/
def cutoffAffineHessian (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) (z : Cov × E₂) : E₂ →L[ℝ] E₂ :=
  rightFDeriv (P.cutoffAffineGradient χ) z


-- @@ L251-254 verbatim
theorem contDiff_cutoffAffineHessian (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) :
    ContDiff ℝ ∞ (P.cutoffAffineHessian χ) :=
  contDiff_rightFDeriv (P.contDiff_cutoffAffineGradient χ)


-- @@ L256-269 verbatim
theorem cutoffAffineHessian_eq_fderiv_chartGradient
    (P : IFTSurfaceChart C) (χ : SmoothCutoff K U)
    (A : Cov) (u : E₂) :
    P.cutoffAffineHessian χ (A, u) =
      fderiv ℝ (chartGradient (P.cutoffAffineHeight χ A)) u := by
  have h := fderiv_section_eq_rightFDeriv
    (P.contDiff_cutoffAffineGradient χ) A u
  change fderiv ℝ (fun y => P.cutoffAffineGradient χ (A, y)) u =
    P.cutoffAffineHessian χ (A, u) at h
  have heq : (fun y => P.cutoffAffineGradient χ (A, y)) =
      chartGradient (P.cutoffAffineHeight χ A) := by
    funext y
    exact P.cutoffAffineGradient_eq_chartGradient χ A y
  rw [← heq, h]


-- @@ L271-275 verbatim
/-- First/second derivative jet of the actual cutoff chart height. -/
def cutoffAffineMorseJet (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) (z : Cov × E₂) :
    E₂ × (E₂ →L[ℝ] E₂) :=
  (P.cutoffAffineGradient χ z, P.cutoffAffineHessian χ z)


-- @@ L277-279 verbatim
def CutoffAffineMorseOn (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) (A : Cov) (S : Set E₂) : Prop :=
  ∀ u ∈ S, P.cutoffAffineMorseJet χ (A, u) ∈ MorseJetGood


-- @@ L281-284 verbatim
/-- Critical parameters of the actual cutoff chart height. -/
def CutoffChartCritical (P : IFTSurfaceChart C)
    (χ : SmoothCutoff K U) (A : Cov) : Set E₂ :=
  {u | P.cutoffAffineGradient χ (A, u) = 0}


-- @@ L286-290 verbatim
theorem contDiff_cutoffAffineGradient_section
    (P : IFTSurfaceChart C) (χ : SmoothCutoff K U) (A : Cov) :
    ContDiff ℝ ∞ (fun u => P.cutoffAffineGradient χ (A, u)) :=
  P.contDiff_cutoffAffineGradient χ |>.comp
    (contDiff_const.prodMk contDiff_id)


-- @@ L292-322 verbatim
/-- For the inverse pullback determined by a forward cutoff deformation, the
ambient time-criticality equation in an original IFT chart is exactly the
zero equation for the actual cutoff chart gradient. -/
theorem forwardParam_mem_inversePullback_timeCritical_iff_cutoffGradient_eq_zero
    (P : IFTSurfaceChart C) (χ : SmoothCutoff K U) (A : Cov)
    (forward : SmallVerticalAmplitude (n := n))
    (hforward : forward.toFun = χ.localizeCovector (n := n) A)
    (hsmall : 2 * forward.K < 1) {u : E₂}
    (hdom : P.domain ∈ nhds u) :
    forward.diffeomorph (P.param u) ∈
        timeCritical
          ((forward.inverse hsmall).toVerticalAmplitude.pullback C).G ↔
      P.cutoffAffineGradient χ (A, u) = 0 := by
  have hinverse :
      (forward.inverse hsmall).diffeomorph.symm = forward.diffeomorph := by
    rw [forward.inverse_diffeomorph hsmall]
    rfl
  have hheight :
      (fun z => tcoord (forward.diffeomorph (P.param z))) =
        P.cutoffAffineHeight χ A := by
    funext z
    rw [SmallVerticalAmplitude.diffeomorph_apply, tcoord_verticalShift]
    change P.time z + forward.toFun (P.param z) =
      P.cutoffAffineHeight χ A z
    rw [hforward]
    rfl
  rw [← hinverse,
    P.pullbackParam_mem_timeCritical_iff_chartGradient_eq_zero
      (forward.inverse hsmall) hdom,
    hinverse, hheight,
    ← P.cutoffAffineGradient_eq_chartGradient]


-- @@ L324-383 verbatim
/-- Morse-goodness on a compact set makes its actual cutoff critical subset
finite.  The proof uses the inverse function theorem pointwise at every zero,
then compactness. -/
theorem finite_cutoffChartCritical_inter_of_morseOn
    (P : IFTSurfaceChart C) (χ : SmoothCutoff K U) (A : Cov)
    {S : Set E₂} (hS : IsCompact S)
    (hMorse : P.CutoffAffineMorseOn χ A S) :
    (P.CutoffChartCritical χ A ∩ S).Finite := by
  let grad : E₂ → E₂ := fun u => P.cutoffAffineGradient χ (A, u)
  have hgrad : ContDiff ℝ ∞ grad :=
    P.contDiff_cutoffAffineGradient_section χ A
  have hclosed : IsClosed (P.CutoffChartCritical χ A) := by
    change IsClosed (grad ⁻¹' ({0} : Set E₂))
    exact isClosed_singleton.preimage hgrad.continuous
  have hdiscrete : IsDiscrete (P.CutoffChartCritical χ A ∩ S) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    have hxzero : grad x = 0 := hx.1
    have hbij : Bijective (P.cutoffAffineHessian χ (A, x)) := by
      have hgood := hMorse x hx.2
      rcases hgood with hne | hbij
      · exact (hne hxzero).elim
      · exact hbij
    have hsection :
        fderiv ℝ grad x = P.cutoffAffineHessian χ (A, x) := by
      exact fderiv_section_eq_rightFDeriv
        (P.contDiff_cutoffAffineGradient χ) A x
    have hbij' : Bijective (fderiv ℝ grad x) := by
      rw [hsection]
      exact hbij
    let e : E₂ ≃L[ℝ] E₂ :=
      ContinuousLinearEquiv.ofBijective (fderiv ℝ grad x)
        (LinearMap.ker_eq_bot.mpr hbij'.1)
        (LinearMap.range_eq_top.mpr hbij'.2)
    have hderiv : HasFDerivAt grad (e : E₂ →L[ℝ] E₂) x := by
      have h := (hgrad.differentiable (by simp) x).hasFDerivAt
      simpa [e, ContinuousLinearEquiv.coe_ofBijective] using h
    let φ := hgrad.contDiffAt.toOpenPartialHomeomorph grad hderiv (by simp)
    refine ⟨φ.source, φ.open_source, ?_⟩
    ext y
    constructor
    · rintro ⟨hySource, hyCritical, _hyS⟩
      have hxSource : x ∈ φ.source :=
        hgrad.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by simp)
      have hφ : (φ : E₂ → E₂) = grad := by rfl
      have hφyx : φ y = φ x := by
        rw [hφ]
        change grad y = 0 at hyCritical
        rw [hyCritical, hxzero]
      have hyx : y = x := φ.injOn hySource hxSource hφyx
      simpa [hyx]
    · intro hy
      rw [mem_singleton_iff] at hy
      subst y
      refine ⟨?_, hx⟩
      exact hgrad.contDiffAt.mem_toOpenPartialHomeomorph_source
        hderiv (by simp)
  rw [inter_comm]
  apply (hS.inter_right hclosed).finite
  simpa [inter_comm] using hdiscrete


-- @@ L385-397 verbatim
/-- On the strict cutoff plateau, the actual cutoff height and the shared
affine height have the same germ. -/
theorem eventuallyEq_cutoffAffineHeight_sharedAffineHeight
    (P : IFTSurfaceChart C) {a b : ℝ}
    (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {V : Set E'} (χ : SmoothCutoff (compactInteriorFiber C a b) V)
    (A : Cov) {u : E₂} (hdom : P.domain ∈ 𝓝 u)
    (ht : P.time u ∈ Ioo a b) :
    P.cutoffAffineHeight χ A =ᶠ[𝓝 u] P.sharedAffineHeight A := by
  filter_upwards [P.eventually_mem_compactInteriorFiber ha hb hdom ht]
    with z hz
  simp [cutoffAffineHeight, cutoffAffineHeightUncurried,
    sharedAffineHeight, χ.eq_one (P.param z) hz]


-- @@ L399-410 verbatim
theorem cutoffAffineGradient_eq_sharedAffineGradient_of_plateau
    (P : IFTSurfaceChart C) {a b : ℝ}
    (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {V : Set E'} (χ : SmoothCutoff (compactInteriorFiber C a b) V)
    (A : Cov) {u : E₂} (hdom : P.domain ∈ 𝓝 u)
    (ht : P.time u ∈ Ioo a b) :
    P.cutoffAffineGradient χ (A, u) = P.sharedAffineGradient (A, u) := by
  rw [P.cutoffAffineGradient_eq_chartGradient,
    P.sharedAffineGradient_eq_chartGradient]
  unfold chartGradient
  rw [(P.eventuallyEq_cutoffAffineHeight_sharedAffineHeight
    ha hb χ A hdom ht).fderiv_eq]


-- @@ L412-426 verbatim
/-- Gradient equality holds on a whole parameter neighborhood of every
strict-plateau point. -/
theorem eventuallyEq_cutoffAffineGradient_sharedAffineGradient
    (P : IFTSurfaceChart C) (hopen : IsOpen P.domain)
    {a b : ℝ} (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {V : Set E'} (χ : SmoothCutoff (compactInteriorFiber C a b) V)
    (A : Cov) {u : E₂} (hu : u ∈ P.domain)
    (ht : P.time u ∈ Ioo a b) :
    (fun z => P.cutoffAffineGradient χ (A, z)) =ᶠ[𝓝 u]
      (fun z => P.sharedAffineGradient (A, z)) := by
  have htime : P.time ⁻¹' Ioo a b ∈ 𝓝 u :=
    (isOpen_Ioo.preimage P.contDiff_time.continuous).mem_nhds ht
  filter_upwards [hopen.mem_nhds hu, htime] with z hzDom hzTime
  exact P.cutoffAffineGradient_eq_sharedAffineGradient_of_plateau
    ha hb χ A (hopen.mem_nhds hzDom) hzTime


-- @@ L428-447 verbatim
theorem cutoffAffineHessian_eq_sharedAffineHessian_of_plateau
    (P : IFTSurfaceChart C) (hopen : IsOpen P.domain)
    {a b : ℝ} (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {V : Set E'} (χ : SmoothCutoff (compactInteriorFiber C a b) V)
    (A : Cov) {u : E₂} (hu : u ∈ P.domain)
    (ht : P.time u ∈ Ioo a b) :
    P.cutoffAffineHessian χ (A, u) = P.sharedAffineHessian (A, u) := by
  rw [P.cutoffAffineHessian_eq_fderiv_chartGradient,
    P.sharedAffineHessian_eq_fderiv_chartGradient]
  have hcut : chartGradient (P.cutoffAffineHeight χ A) =
      fun z => P.cutoffAffineGradient χ (A, z) := by
    funext z
    exact (P.cutoffAffineGradient_eq_chartGradient χ A z).symm
  have hshared : chartGradient (P.sharedAffineHeight A) =
      fun z => P.sharedAffineGradient (A, z) := by
    funext z
    exact (P.sharedAffineGradient_eq_chartGradient A z).symm
  rw [hcut, hshared]
  exact (P.eventuallyEq_cutoffAffineGradient_sharedAffineGradient
    hopen ha hb χ A hu ht).fderiv_eq


-- @@ L449-460 verbatim
theorem cutoffAffineMorseJet_eq_sharedAffineMorseJet_of_plateau
    (P : IFTSurfaceChart C) (hopen : IsOpen P.domain)
    {a b : ℝ} (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {V : Set E'} (χ : SmoothCutoff (compactInteriorFiber C a b) V)
    (A : Cov) {u : E₂} (hu : u ∈ P.domain)
    (ht : P.time u ∈ Ioo a b) :
    P.cutoffAffineMorseJet χ (A, u) = P.sharedAffineMorseJet (A, u) := by
  apply Prod.ext
  · exact P.cutoffAffineGradient_eq_sharedAffineGradient_of_plateau
      ha hb χ A (hopen.mem_nhds hu) ht
  · exact P.cutoffAffineHessian_eq_sharedAffineHessian_of_plateau
      hopen ha hb χ A hu ht


-- @@ L462-462 verbatim
end IFTSurfaceChart


-- @@ L464-464 verbatim
namespace FiniteIFTSurfaceCover


-- @@ L466-466 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]


-- @@ L468-472 verbatim
/-- The part of one compact chart core lying outside the strict plateau
`a < time < b`. -/
def cutoffTransitionCore (B : FiniteIFTSurfaceCover C ι)
    (i : ι) (a b : ℝ) : Set E₂ :=
  B.core i ∩ (B.chart i).time ⁻¹' (Iic a ∪ Ici b)


-- @@ L474-479 verbatim
theorem isCompact_cutoffTransitionCore
    (B : FiniteIFTSurfaceCover C ι) (i : ι) (a b : ℝ) :
    IsCompact (B.cutoffTransitionCore i a b) := by
  exact (B.compact_core i).inter_right
    ((isClosed_Iic.union isClosed_Ici).preimage
      (B.chart i).contDiff_time.continuous)


-- @@ L481-500 verbatim
/-- At the zero covector, the cutoff chart gradient is nonzero throughout a
transition core containing no old time-critical points. -/
theorem cutoffAffineGradient_zero_ne_on_transitionCore
    (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) {a b : ℝ}
    (hcrit : timeCritical C.G ⊆ tcoord ⁻¹' Ioo a b)
    (i : ι) (u : E₂) (hu : u ∈ B.cutoffTransitionCore i a b) :
    (B.chart i).cutoffAffineGradient χ (0, u) ≠ 0 := by
  rw [(B.chart i).cutoffAffineGradient_zero]
  intro hzero
  have huDom : u ∈ (B.chart i).domain := B.core_subset_domain i hu.1
  have hamb : (B.chart i).param u ∈ timeCritical C.G :=
    ((B.chart i).mem_timeCritical_iff_chartGradient_eq_zero
      ((B.domain_open i).mem_nhds huDom)).2 hzero
  have hin := hcrit hamb
  change (B.chart i).time u ∈ Ioo a b at hin
  rcases hu.2 with hle | hge
  · exact (not_lt_of_ge hle) hin.1
  · exact (not_lt_of_ge hge) hin.2


-- @@ L502-517 verbatim
/-- Compact stability gives one covector neighborhood on which the global
cutoff creates no critical points on a fixed transition core. -/
theorem eventually_cutoffAffineGradient_ne_on_transitionCore
    (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) {a b : ℝ}
    (hcrit : timeCritical C.G ⊆ tcoord ⁻¹' Ioo a b)
    (i : ι) :
    ∀ᶠ A : Cov in 𝓝 0, ∀ u ∈ B.cutoffTransitionCore i a b,
      (B.chart i).cutoffAffineGradient χ (A, u) ≠ 0 := by
  apply (B.isCompact_cutoffTransitionCore i a b).eventually_forall_of_forall_eventually
  intro u hu
  have hzero := B.cutoffAffineGradient_zero_ne_on_transitionCore
    χ hcrit i u hu
  exact (B.chart i).contDiff_cutoffAffineGradient χ |>.continuous.continuousAt
    (isClosed_singleton.isOpen_compl.mem_nhds hzero)


-- @@ L519-530 verbatim
/-- Finiteness upgrades the preceding chartwise neighborhoods to one common
ambient-covector neighborhood for every transition core. -/
theorem eventually_all_cutoffAffineGradient_ne_on_transitionCore
    (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) {a b : ℝ}
    (hcrit : timeCritical C.G ⊆ tcoord ⁻¹' Ioo a b) :
    ∀ᶠ A : Cov in 𝓝 0, ∀ i, ∀ u ∈ B.cutoffTransitionCore i a b,
      (B.chart i).cutoffAffineGradient χ (A, u) ≠ 0 := by
  rw [eventually_all]
  intro i
  exact B.eventually_cutoffAffineGradient_ne_on_transitionCore χ hcrit i


-- @@ L532-563 verbatim
/-- Shared Morse-goodness on the plateau and noncriticality on the two
transition strips combine to Morse-goodness of the actual cutoff height on
every compact chart core. -/
theorem cutoffAffineMorseOn_core_of_shared_of_noTransition
    (B : FiniteIFTSurfaceCover C ι)
    {a b : ℝ} (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff (compactInteriorFiber C a b) U)
    (A : Cov)
    (hshared : ∀ i,
      (B.chart i).SharedAffineMorseOn A (B.core i))
    (htransition : ∀ i, ∀ u ∈ B.cutoffTransitionCore i a b,
      (B.chart i).cutoffAffineGradient χ (A, u) ≠ 0) :
    ∀ i, (B.chart i).CutoffAffineMorseOn χ A (B.core i) := by
  intro i u hu
  by_cases ht : (B.chart i).time u ∈ Ioo a b
  · have hjet :=
      (B.chart i).cutoffAffineMorseJet_eq_sharedAffineMorseJet_of_plateau
        (B.domain_open i) ha hb χ A (B.core_subset_domain i hu) ht
    change (B.chart i).cutoffAffineMorseJet χ (A, u) ∈ MorseJetGood
    rw [hjet]
    exact hshared i u hu
  · change (B.chart i).cutoffAffineGradient χ (A, u) ≠ 0 ∨
      Bijective ((B.chart i).cutoffAffineHessian χ (A, u))
    apply Or.inl
    apply htransition i u
    refine ⟨hu, ?_⟩
    change (B.chart i).time u ∈ Iic a ∪ Ici b
    by_cases hleft : (B.chart i).time u ≤ a
    · exact Or.inl hleft
    · apply Or.inr
      exact le_of_not_gt fun hright => ht ⟨lt_of_not_ge hleft, hright⟩


-- @@ L565-569 verbatim
/-- Chart-indexed critical parameters of the actual cutoff height. -/
def cutoffCriticalPoints (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) (A : Cov) : Set (Σ _ : ι, E₂) :=
  {p | p.2 ∈ (B.chart p.1).CutoffChartCritical χ A ∩ B.core p.1}


-- @@ L571-591 verbatim
/-- The actual shared-cutoff critical parameter set is finite. -/
theorem finite_cutoffCriticalPoints
    (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) (A : Cov)
    (hMorse : ∀ i,
      (B.chart i).CutoffAffineMorseOn χ A (B.core i)) :
    (B.cutoffCriticalPoints χ A).Finite := by
  classical
  have hfinite (i : ι) :
      ((B.chart i).CutoffChartCritical χ A ∩ B.core i).Finite :=
    (B.chart i).finite_cutoffChartCritical_inter_of_morseOn
      χ A (B.compact_core i) (hMorse i)
  let s : Finset (Σ _ : ι, E₂) :=
    Finset.univ.sigma fun i => (hfinite i).toFinset
  apply s.finite_toSet.subset
  intro p hp
  change p ∈ s
  simp only [s, Finset.mem_sigma, Finset.mem_univ, true_and,
    Set.Finite.mem_toFinset]
  exact hp


-- @@ L593-599 verbatim
/-- Send a chart-indexed parameter through the one shared forward ambient
diffeomorphism.  This is the ambient center represented by that parameter in
the inverse-pulled-back cobordism. -/
def cutoffCriticalCenter (B : FiniteIFTSurfaceCover C ι)
    (forward : SmallVerticalAmplitude (n := n))
    (p : Σ _ : ι, E₂) : EuclideanSpace ℝ (Fin (n + 2)) :=
  forward.diffeomorph ((B.chart p.1).param p.2)


-- @@ L601-609 verbatim
/-- The chart-indexed cutoff critical parameters whose represented ambient
centers lie in the compact middle time slab. -/
def cutoffCoreCriticalParameters (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) (A : Cov)
    (forward : SmallVerticalAmplitude (n := n)) : Set (Σ _ : ι, E₂) :=
  {p | p ∈ B.cutoffCriticalPoints χ A ∧
    B.cutoffCriticalCenter forward p ∈
      tcoord ⁻¹' Icc (1 / 4 : ℝ) (3 / 4 : ℝ)}


-- @@ L611-621 verbatim
theorem finite_cutoffCoreCriticalParameters
    (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) (A : Cov)
    (forward : SmallVerticalAmplitude (n := n))
    (hMorse : ∀ i,
      (B.chart i).CutoffAffineMorseOn χ A (B.core i)) :
    (B.cutoffCoreCriticalParameters χ A forward).Finite := by
  apply (B.finite_cutoffCriticalPoints χ A hMorse).subset
  intro p hp
  exact hp.1


-- @@ L623-668 verbatim
/-- Exact shared-atlas ownership: the ambient image of the finite
chart-indexed cutoff critical parameters is precisely the full compact
critical locus of the inverse pullback.  In particular, there are neither
uncovered global critical points nor spurious listed centers. -/
theorem image_cutoffCoreCriticalParameters_eq_coreCriticalPoints
    (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U) (A : Cov)
    (forward : SmallVerticalAmplitude (n := n))
    (hforward : forward.toFun = χ.localizeCovector (n := n) A)
    (hsmall : 2 * forward.K < 1) :
    B.cutoffCriticalCenter forward ''
        B.cutoffCoreCriticalParameters χ A forward =
      coreCriticalPoints
        ((forward.inverse hsmall).toVerticalAmplitude.pullback C) := by
  apply Set.Subset.antisymm
  · rintro v ⟨p, hp, rfl⟩
    refine ⟨?_, hp.2⟩
    have hpCore : p.2 ∈ B.core p.1 := hp.1.2
    exact ((B.chart p.1).forwardParam_mem_inversePullback_timeCritical_iff_cutoffGradient_eq_zero
        χ A forward hforward hsmall
        ((B.domain_open p.1).mem_nhds
          (B.core_subset_domain p.1 hpCore))).2 hp.1.1
  · intro v hv
    obtain ⟨i, u, huCore, huv⟩ :=
      B.exists_pullback_chart_parameter_of_coreCritical
        (forward.inverse hsmall) hv
    have hinverse :
        (forward.inverse hsmall).diffeomorph.symm =
          forward.diffeomorph := by
      rw [forward.inverse_diffeomorph hsmall]
      rfl
    have huv' : B.cutoffCriticalCenter forward ⟨i, u⟩ = v := by
      change forward.diffeomorph ((B.chart i).param u) = v
      rw [← hinverse]
      exact huv
    change forward.diffeomorph ((B.chart i).param u) = v at huv'
    refine ⟨⟨i, u⟩, ?_, huv'⟩
    refine ⟨⟨?_, huCore⟩, ?_⟩
    · exact ((B.chart i).forwardParam_mem_inversePullback_timeCritical_iff_cutoffGradient_eq_zero
          χ A forward hforward hsmall
          ((B.domain_open i).mem_nhds
            (B.core_subset_domain i huCore))).1 (huv'.symm ▸ hv.1)
    · change tcoord (forward.diffeomorph ((B.chart i).param u)) ∈
        Icc (1 / 4 : ℝ) (3 / 4 : ℝ)
      exact huv'.symm ▸ hv.2


-- @@ L670-692 verbatim
/-- A single shared covector can be chosen so that it is Morse-good on every
compact IFT core and its one global cutoff deformation is already small enough
to have a small vertical inverse. -/
theorem exists_sharedMorse_globalCutoffAmplitude
    (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U)
    (hU : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ)) :
    ∃ A : Cov,
      (∀ i, (B.chart i).SharedAffineMorseOn A (B.core i)) ∧
      ∃ forward : SmallVerticalAmplitude (n := n),
        forward.toFun = χ.localizeCovector (n := n) A ∧
          2 * forward.K < 1 := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    χ.exists_lipschitz_radius_localizeCovector (n := n)
  obtain ⟨A, hAball, hMorse⟩ :=
    B.exists_sharedAffineMorseCovector_in_ball hδ
  have hAnorm : ‖A‖ < δ := by
    simpa [mem_ball, dist_zero_right] using hAball
  have hlip := hsmall A hAnorm
  let forward := χ.smallForwardOfCovector (n := n) hU A hlip
  refine ⟨A, hMorse, forward, rfl, ?_⟩
  exact χ.smallForwardOfCovector_twice_K_lt_one (n := n) hU A hlip


-- @@ L694-728 verbatim
/-- Strengthened global choice: besides Morse-goodness on every core and
small invertibility, the actual cutoff height has no chart critical point on
any transition core. -/
theorem exists_sharedMorse_globalCutoffAmplitude_noTransition
    (B : FiniteIFTSurfaceCover C ι)
    {K U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff K U)
    (hU : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ))
    {a b : ℝ} (hcrit : timeCritical C.G ⊆ tcoord ⁻¹' Ioo a b) :
    ∃ A : Cov,
      (∀ i, (B.chart i).SharedAffineMorseOn A (B.core i)) ∧
      (∀ i, ∀ u ∈ B.cutoffTransitionCore i a b,
        (B.chart i).cutoffAffineGradient χ (A, u) ≠ 0) ∧
      ∃ forward : SmallVerticalAmplitude (n := n),
        forward.toFun = χ.localizeCovector (n := n) A ∧
          2 * forward.K < 1 := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    χ.exists_lipschitz_radius_localizeCovector (n := n)
  have hball : ball (0 : Cov) δ ∈ 𝓝 0 := ball_mem_nhds 0 hδ
  have htransition :=
    B.eventually_all_cutoffAffineGradient_ne_on_transitionCore χ hcrit
  have hchoice :
      {A : Cov | A ∈ ball 0 δ ∧
        ∀ i, ∀ u ∈ B.cutoffTransitionCore i a b,
          (B.chart i).cutoffAffineGradient χ (A, u) ≠ 0} ∈ 𝓝 0 := by
    filter_upwards [hball, htransition] with A hA hAtransition
    exact ⟨hA, hAtransition⟩
  obtain ⟨A, hAchoice, hMorse⟩ :=
    B.exists_sharedAffineMorseCovector_mem_nhds hchoice
  have hAnorm : ‖A‖ < δ := by
    simpa [mem_ball, dist_zero_right] using hAchoice.1
  have hlip := hsmall A hAnorm
  let forward := χ.smallForwardOfCovector (n := n) hU A hlip
  refine ⟨A, hMorse, hAchoice.2, forward, rfl, ?_⟩
  exact χ.smallForwardOfCovector_twice_K_lt_one (n := n) hU A hlip


-- @@ L730-759 verbatim
/-- One-shot finite shared-atlas package supplied by the global construction:
one ambient covector and one fiber-wide cutoff produce an invertible pullback,
Morse-good actual chart heights on every compact core, a finite chart-indexed
critical set, and exact coverage of the entire compact global critical locus. -/
theorem exists_sharedMorse_globalCutoffCriticalCover
    (B : FiniteIFTSurfaceCover C ι)
    {a b : ℝ} (ha : 1 / 4 < a) (hb : b < 3 / 4)
    {U : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (χ : SmoothCutoff (compactInteriorFiber C a b) U)
    (hU : U ⊆ tcoord ⁻¹' Ioo (1 / 4 : ℝ) (3 / 4 : ℝ))
    (hcrit : timeCritical C.G ⊆ tcoord ⁻¹' Ioo a b) :
    ∃ A : Cov, ∃ forward : SmallVerticalAmplitude (n := n),
      ∃ hsmall : 2 * forward.K < 1,
        forward.toFun = χ.localizeCovector (n := n) A ∧
        (∀ i, (B.chart i).CutoffAffineMorseOn χ A (B.core i)) ∧
        (B.cutoffCoreCriticalParameters χ A forward).Finite ∧
        B.cutoffCriticalCenter forward ''
            B.cutoffCoreCriticalParameters χ A forward =
          coreCriticalPoints
            ((forward.inverse hsmall).toVerticalAmplitude.pullback C) := by
  obtain ⟨A, hshared, htransition, forward, hforward, hsmall⟩ :=
    B.exists_sharedMorse_globalCutoffAmplitude_noTransition χ hU hcrit
  have hMorse : ∀ i,
      (B.chart i).CutoffAffineMorseOn χ A (B.core i) :=
    B.cutoffAffineMorseOn_core_of_shared_of_noTransition
      ha hb χ A hshared htransition
  refine ⟨A, forward, hsmall, hforward, hMorse, ?_, ?_⟩
  · exact B.finite_cutoffCoreCriticalParameters χ A forward hMorse
  · exact B.image_cutoffCoreCriticalParameters_eq_coreCriticalPoints
      χ A forward hforward hsmall


-- @@ L761-761 verbatim
end FiniteIFTSurfaceCover


-- @@ L763-763 verbatim
end Submission
