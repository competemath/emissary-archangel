/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyPressure
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionStabilityBudget
import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionUniqueness
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionOperators
public import LeanPool.NavierStokesAndEuler.Euler.CylinderReflection
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDerivatives
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul


-- @@ L21-22 verbatim
/-! Odd parity of the actual common correction and pressure assembled from finite genuine solutions.
-/


-- @@ L24-24 verbatim
section


-- @@ L26-26 verbatim
/-! Reflection invariance of the concrete lifted-gradient space and pressure solve. -/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace EulerGradientReflection


-- @@ L34-35 verbatim
open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerLiftedPressure EulerCylinderReflection EulerSpatialSobolevInverse

-- @@ L36-36 verbatim
open scoped ContDiff Topology


-- @@ L38-38 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L40-59 verbatim
/-- Reflecting a genuine smooth test gradient gives the negative gradient
of the reflected scalar test. -/
theorem reflection_testGradient (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    reflection period (testGradientLp period κ m φ hφ) =
      -testGradientLp period κ m (reflectedTest period φ) (smoothCompactTest_reflected period φ hφ)
          := by
  apply Lp.ext
  filter_upwards [reflection_ae period (testGradientLp period κ m φ hφ),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (testGradientLp_ae period κ m φ
        hφ),
    Lp.coeFn_neg (testGradientLp period κ m (reflectedTest period φ) (smoothCompactTest_reflected
        period φ hφ)),
    testGradientLp_ae period κ m (reflectedTest period φ) (smoothCompactTest_reflected period φ hφ)]
    with x h1 h2 h3 h4
  rw [h1, h2, h3]
  change liftedGradient period κ m φ (-x) =
    -(testGradientLp period κ m (reflectedTest period φ) (smoothCompactTest_reflected period φ hφ)
        x)
  rw [h4, liftedGradient_reflected period κ m φ hφ.2 x, neg_neg]


-- @@ L61-81 verbatim
/-- Reflection preserves the closure of the span of actual test gradients. -/
theorem gradientSpace_reflection_mem (κ : ℝ) (m : Vector3) {g : LiftL2 period}
    (hg : g ∈ gradientSpace period κ m) : reflection period g ∈ gradientSpace period κ m := by
  let R := (reflection period).toContinuousLinearMap
  have hspan : Submodule.span ℝ
      {f : LiftL2 period | ∃ φ : LiftDomain period → ℝ,
        (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) ∧
        f =ᵐ[liftMeasure period] liftedGradient period κ m φ} ≤
      (gradientSpace period κ m).comap R.toLinearMap := by
    apply Submodule.span_le.2
    rintro f ⟨φ, hφ, hf⟩
    have heq : f = testGradientLp period κ m φ hφ := Lp.ext (hf.trans (testGradientLp_ae period κ m
        φ hφ).symm)
    change reflection period f ∈ gradientSpace period κ m
    rw [heq, reflection_testGradient]
    exact (gradientSpace period κ m).neg_mem (testGradient_mem period κ m
      (testGradientLp_mem_generators period κ m (reflectedTest period φ)
          (smoothCompactTest_reflected period φ hφ)))
  have hclosed : IsClosed ((gradientSpace period κ m).comap R.toLinearMap : Set (LiftL2 period)) :=
    (gradientSpace_closed period κ m).preimage R.continuous
  exact (Submodule.topologicalClosure_minimal _ hspan hclosed) hg


-- @@ L83-91 verbatim
/-- Reflection maps the concrete lifted-gradient subspace onto itself. -/
theorem gradientSpace_map_reflection (κ : ℝ) (m : Vector3) :
    (gradientSpace period κ m).map (reflection period).toLinearMap = gradientSpace period κ m := by
  apply le_antisymm
  · rintro g ⟨f, hf, rfl⟩
    exact gradientSpace_reflection_mem period κ m hf
  · intro g hg
    exact ⟨reflection period g, gradientSpace_reflection_mem period κ m hg, reflection_involutive
        period g⟩


-- @@ L93-103 verbatim
/-- The genuine orthogonal gradient projection commutes with joint reflection. -/
theorem gradientProjection_reflection (κ : ℝ) (m : Vector3) (f : LiftL2 period) :
    reflection period (gradientProjection period κ m f) = gradientProjection period κ m (reflection
        period f) := by
  have hmap := gradientSpace_map_reflection period κ m
  let : ((gradientSpace period κ m).map (reflection period).toLinearMap).HasOrthogonalProjection :=
      by
    rw [hmap]
    infer_instance
  simpa only [gradientProjection, hmap] using
    (reflection period).map_starProjection (gradientSpace period κ m) f


-- @@ L105-113 verbatim
/-- The actual weak divergence-free constraint is preserved by reflection. -/
theorem divergenceFreeSpace_reflection_mem (κ : ℝ) (m : Vector3) {f : LiftL2 period}
    (hf : f ∈ divergenceFreeSpace period κ m) : reflection period f ∈ divergenceFreeSpace period κ
        m := by
  have hz : gradientProjection period κ m f = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (gradientSpace period κ m)).mpr hf
  apply (Submodule.starProjection_apply_eq_zero_iff (gradientSpace period κ m)).mp
  change gradientProjection period κ m (reflection period f) = 0
  rw [← gradientProjection_reflection, hz, map_zero]


-- @@ L115-123 verbatim
/-- An even coefficient field commutes with the actual reflection isometry. -/
theorem coefficientOperator_reflection (A : SmoothCoefficient period)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x) (f : LiftL2 period) :
    reflection period (A.operator f) = A.operator (reflection period f) := by
  apply Lp.ext
  filter_upwards [reflection_ae period (A.operator f),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (A.operator_ae f),
    A.operator_ae (reflection period f), reflection_ae period f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, hA]


-- @@ L125-143 verbatim
/-- Uniqueness of the concrete coercive pressure inverse proves its
reflection covariance for the actual even metric. -/
theorem pressure_reflection (A : SmoothCoefficient period)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (f : LiftL2 period) :
    reflection period (A.pressure κ m c hc hpos f) =
      A.pressure κ m c hc hpos (reflection period f) := by
  apply liftedPressure_unique period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos
  · exact gradientSpace_reflection_mem period κ m
      (liftedPressure_mem period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f)
  · change gradientProjection period κ m (A.operator (reflection period (A.pressure κ m c hc hpos
      f))) = _
    rw [← coefficientOperator_reflection period A hA, ← gradientProjection_reflection]
    have he := liftedPressure_equation period κ m A.coefficient A.measurable A.bound A.norm_bound c
        hc hpos f
    change gradientProjection period κ m (A.operator (A.pressure κ m c hc hpos f)) =
      gradientProjection period κ m f at he
    rw [he, gradientProjection_reflection]


-- @@ L145-145 verbatim
end EulerGradientReflection


-- @@ L147-147 verbatim
end

-- @@ L148-148 verbatim
end


-- @@ L150-150 verbatim
end


-- @@ L152-152 verbatim
section


-- @@ L154-154 verbatim
/-! Joint reflection on the actual complete cylinder Sobolev spaces. -/


-- @@ L156-156 verbatim
@[expose] public section


-- @@ L158-158 verbatim
noncomputable section


-- @@ L160-160 verbatim
namespace EulerSobolevReflection


-- @@ L162-163 verbatim
open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolevSpace
  EulerCylinderReflection EulerGradientReflection EulerCylinderSobolev

-- @@ L164-164 verbatim
open scoped Topology


-- @@ L166-166 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L168-172 verbatim
/-- Reflection of a derivative array includes the sign of each derivative word. -/
def reflectionArrayOperator (q : ℕ) :
    SobolevSpace period q →L[ℝ] (SobolevWord q → LiftL2 period) :=
  ContinuousLinearMap.pi fun w => ((-1 : ℝ) ^ w.1.val) •
    ((reflection period).toContinuousLinearMap.comp (wordOperator period w))


-- @@ L174-191 verbatim
/-- The signed derivative array satisfies the actual strong-derivative compatibility. -/
theorem reflectionArray_mem (q : ℕ) (u : SobolevSpace period q) :
    reflectionArrayOperator period q u ∈ (sobolevSubspace period q).toSubmodule := by
  apply ClosedSubmodule.mem_iInf.mpr
  intro e
  have hd := word_hasDerivAt period u e.1.isLt e.2.1 e.2.2
  have hr := (reflection_hasDerivAt period (standardDirection e.2.2) hd).const_smul ((-1 : ℝ) ^
      e.1.val)
  change HasDerivAt (fun t => translation period (translationPath period (standardDirection e.2.2)
      t)
    (((-1 : ℝ) ^ e.1.val) • reflection period (u.val (edgeParent e))))
    (((-1 : ℝ) ^ (e.1.val + 1)) • reflection period (u.val (edgeChild e))) 0
  convert! hr using 1
  · funext t
    rw [map_smul]
    rfl
  · simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]
    rfl


-- @@ L193-196 verbatim
/-- Joint pullback reflection as a genuine bounded map of the complete Sobolev space. -/
def sobolevReflection (q : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  (reflectionArrayOperator period q).codRestrict (sobolevSubspace period q).toSubmodule
    (reflectionArray_mem period q)


-- @@ L198-200 verbatim
/-- The derivative coordinates of reflection have exactly the alternating signs. -/
@[simp] theorem sobolevReflection_apply {q : ℕ} (u : SobolevSpace period q) (w : SobolevWord q) :
    (sobolevReflection period q u).val w = (-1 : ℝ) ^ w.1.val • reflection period (u.val w) := rfl


-- @@ L202-206 verbatim
/-- The underlying field is the actual L² pullback by joint negation. -/
@[simp] theorem value_sobolevReflection {q : ℕ} (u : SobolevSpace period q) :
    value period (sobolevReflection period q u) = reflection period (value period u) := by
  change (-1 : ℝ) ^ 0 • reflection period (value period u) = _
  simp


-- @@ L208-212 verbatim
/-- Joint reflection is involutive on the complete Sobolev space. -/
@[simp] theorem sobolevReflection_involutive {q : ℕ} (u : SobolevSpace period q) :
    sobolevReflection period q (sobolevReflection period q u) = u := by
  apply value_injective period
  rw [value_sobolevReflection, value_sobolevReflection, reflection_involutive]


-- @@ L214-218 verbatim
/-- Every genuine derivative coordinate keeps its L² norm under reflection. -/
theorem sobolevReflection_word_norm {q : ℕ} (u : SobolevSpace period q) (w : SobolevWord q) :
    ‖(sobolevReflection period q u).val w‖ = ‖u.val w‖ := by
  rw [sobolevReflection_apply, norm_smul, reflection_norm, norm_pow]
  norm_num


-- @@ L220-233 verbatim
/-- Reflection preserves the actual finite Sobolev norm. -/
theorem sobolevReflection_norm {q : ℕ} (u : SobolevSpace period q) :
    ‖sobolevReflection period q u‖ = ‖u‖ := by
  apply le_antisymm
  · change ‖(sobolevReflection period q u).val‖ ≤ ‖u.val‖
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u.val)).mpr
    intro w
    rw [sobolevReflection_word_norm]
    exact norm_le_pi_norm u.val w
  · change ‖u.val‖ ≤ ‖(sobolevReflection period q u).val‖
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro w
    have hh := norm_le_pi_norm (sobolevReflection period q u).val w
    rwa [sobolevReflection_word_norm] at hh


-- @@ L235-239 verbatim
/-- Reflection also preserves the source's sum-over-derivatives Sobolev norm. -/
theorem sobolevReflection_sumNorm {q : ℕ} (u : SobolevSpace period q) :
    sumNorm period (sobolevReflection period q u) = sumNorm period u := by
  unfold sumNorm
  exact Finset.sum_congr rfl fun w _ => sobolevReflection_word_norm period u w


-- @@ L241-246 verbatim
/-- Truncating the Sobolev order commutes with actual reflection. -/
theorem truncate_reflection {q : ℕ} (u : SobolevSpace period (q + 1)) :
    truncateOperator period q (sobolevReflection period (q + 1) u) =
      sobolevReflection period q (truncateOperator period q u) := by
  apply value_injective period
  simp only [value_truncateOperator, value_sobolevReflection]


-- @@ L248-256 verbatim
/-- Every actual coordinate derivative reverses sign under joint reflection. -/
theorem derivative_reflection {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q + 1)) :
    derivativeOperator period q i (sobolevReflection period (q + 1) u) =
      -sobolevReflection period q (derivativeOperator period q i u) := by
  apply Subtype.ext
  funext w
  change (-1 : ℝ) ^ (w.1.val + 1) • reflection period (u.val (derivativeIndex i w)) =
    -((-1 : ℝ) ^ w.1.val • reflection period (u.val (derivativeIndex i w)))
  simp only [pow_succ, mul_smul, neg_one_smul, smul_neg]


-- @@ L258-260 verbatim
/-- The symmetry whose fixed points are odd velocity fields. -/
def oddReflection (q : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  -sobolevReflection period q


-- @@ L262-264 verbatim
/-- Odd reflection is represented by minus the field at the reflected point. -/
@[simp] theorem oddReflection_apply {q : ℕ} (u : SobolevSpace period q) :
    oddReflection period q u = -sobolevReflection period q u := rfl


-- @@ L266-269 verbatim
/-- The signed reflection is involutive. -/
theorem oddReflection_involutive {q : ℕ} (u : SobolevSpace period q) :
    oddReflection period q (oddReflection period q u) = u := by
  simp only [oddReflection_apply, map_neg, neg_neg, sobolevReflection_involutive]


-- @@ L271-274 verbatim
/-- The signed reflection preserves the Sobolev norm. -/
theorem oddReflection_norm {q : ℕ} (u : SobolevSpace period q) :
    ‖oddReflection period q u‖ = ‖u‖ := by
        rw [oddReflection_apply, norm_neg, sobolevReflection_norm]


-- @@ L276-282 verbatim
/-- Signed reflection preserves the genuine weak divergence constraint. -/
theorem oddReflection_divergenceFree {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q)
    (hu : value period u ∈ divergenceFreeSpace period κ m) :
    value period (oddReflection period q u) ∈ divergenceFreeSpace period κ m := by
  change -value period (sobolevReflection period q u) ∈ divergenceFreeSpace period κ m
  rw [value_sobolevReflection]
  exact (divergenceFreeSpace period κ m).neg_mem (divergenceFreeSpace_reflection_mem period κ m hu)


-- @@ L284-284 verbatim
end EulerSobolevReflection


-- @@ L286-286 verbatim
end

-- @@ L287-287 verbatim
end


-- @@ L289-289 verbatim
end


-- @@ L291-291 verbatim
section


-- @@ L293-293 verbatim
/-! Joint odd symmetry of the actual correction source and its coercive pressure. -/


-- @@ L295-295 verbatim
section


-- @@ L297-297 verbatim
/-! Reflection covariance of the literal Sobolev product, transport and pressure operators. -/


-- @@ L299-299 verbatim
@[expose] public section


-- @@ L301-301 verbatim
noncomputable section


-- @@ L303-303 verbatim
namespace EulerSobolevParityOperators


-- @@ L305-309 verbatim
open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerSobolevL2Product EulerSobolevTransport
      EulerCorrectionOperators
  EulerCylinderReflection EulerGradientReflection EulerSobolevReflection


-- @@ L311-311 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L313-315 verbatim
/-- The inherited Sobolev additive normed-group instance. -/
local instance paritySobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

-- @@ L316-317 verbatim
/-- The inherited real Sobolev module instance. -/
local instance paritySobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

-- @@ L318-321 verbatim
/-- The inherited normed-group instance on the actual bilinear operator space. -/
local instance parityBilinearGroup (q : ℕ) : SeminormedAddCommGroup
    (SobolevSpace period (q+1) →L[ℝ] SobolevSpace period (q+1) →L[ℝ] SobolevSpace period q) :=
        inferInstance


-- @@ L323-339 verbatim
/-- Reflection of the actual Sobolev product is the product of reflected fields. -/
theorem product_reflection {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    sobolevReflection period q (productHq period hq L hL u v) =
      productHq period hq L hL (sobolevReflection period q u) (sobolevReflection period q v) := by
  apply value_injective period
  rw [value_sobolevReflection]
  apply Lp.ext
  have hp := productHq_ae period hq L hL (sobolevReflection period q u) (sobolevReflection period q
      v)
  simp only [value_sobolevReflection] at hp
  filter_upwards [reflection_ae period (value period (productHq period hq L hL u v)),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (productHq_ae period hq L hL u
        v),
    hp, reflection_ae period (value period u), reflection_ae period (value period v)]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]


-- @@ L341-345 verbatim
/-- The actual bilinear Sobolev product changes sign in its second input. -/
theorem product_neg_right {q : ℕ} (hq : 6 ≤ q) (L : Vector3 →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (u v : SobolevSpace period q) :
    productHq period hq L hL u (-v) = -productHq period hq L hL u v :=
  map_neg (productHqBilinear period hq L hL u) v


-- @@ L347-365 verbatim
/-- The literal transport operator reverses under joint pullback reflection. -/
theorem transport_reflection {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (q + 1)) :
    transportBilinear period hq L hL (sobolevReflection period (q+1) u) (sobolevReflection period
        (q+1) v) =
      -sobolevReflection period q (transportBilinear period hq L hL u v) := by
  have hi (i : Fin 4) :
      productHq period hq (L i) (hL i) (truncateOperator period q (sobolevReflection period (q+1)
          u))
        (derivativeOperator period q i (sobolevReflection period (q+1) v)) =
      -sobolevReflection period q (productHq period hq (L i) (hL i)
        (truncateOperator period q u) (derivativeOperator period q i v)) := by
    simp only [truncate_reflection period u, derivative_reflection period i v,
      product_neg_right period hq (L i) (hL i)]
    exact congrArg Neg.neg (product_reflection period hq (L i) (hL i)
      (truncateOperator period q u) (derivativeOperator period q i v)).symm
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 4))) rfl (fun i _ => hi i)
  simpa only [transportBilinear_apply, map_sum, Finset.sum_neg_distrib] using hh


-- @@ L367-375 verbatim
/-- Actual even coefficient multiplication commutes with Sobolev reflection. -/
theorem coefficient_reflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x) (u : SobolevSpace period q) :
    sobolevReflection period q (coefficientSobolevOperator period K u) =
      coefficientSobolevOperator period K (sobolevReflection period q u) := by
  apply value_injective period
  rw [value_sobolevReflection, coefficientSobolevOperator_value, coefficientSobolevOperator_value,
    value_sobolevReflection, coefficientOperator_reflection period A hA]


-- @@ L377-388 verbatim
/-- Actual odd coefficient multiplication anticommutes with the L² reflection. -/
theorem odd_coefficient_L2_reflection (A : SmoothCoefficient period)
    (hA : ∀ x, A.coefficient (-x) = -A.coefficient x) (f : LiftL2 period) :
    reflection period (A.operator f) = -A.operator (reflection period f) := by
  apply Lp.ext
  filter_upwards [reflection_ae period (A.operator f),
    (measurePreserving_reflection period).quasiMeasurePreserving.ae (A.operator_ae f),
    Lp.coeFn_neg (A.operator (reflection period f)), A.operator_ae (reflection period f),
    reflection_ae period f] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3]
  change A.coefficient (-x) (f (-x)) = -(A.operator (reflection period f) x)
  rw [h4, h5, hA, neg_apply]


-- @@ L390-400 verbatim
/-- Actual odd coefficient multiplication anticommutes with Sobolev reflection. -/
theorem odd_coefficient_reflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = -A.coefficient x) (u : SobolevSpace period q) :
    sobolevReflection period q (coefficientSobolevOperator period K u) =
      -coefficientSobolevOperator period K (sobolevReflection period q u) := by
  apply value_injective period
  change value period (sobolevReflection period q (coefficientSobolevOperator period K u)) =
    -value period (coefficientSobolevOperator period K (sobolevReflection period q u))
  rw [value_sobolevReflection, coefficientSobolevOperator_value, coefficientSobolevOperator_value,
    value_sobolevReflection, odd_coefficient_L2_reflection period A hA]


-- @@ L402-412 verbatim
/-- The concrete coercive pressure acts covariantly at every Sobolev order. -/
theorem pressureSobolev_reflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    sobolevReflection period q (pressureSobolevOperator period K κ m c hc hpos u) =
      pressureSobolevOperator period K κ m c hc hpos (sobolevReflection period q u) := by
  apply value_injective period
  rw [value_sobolevReflection, pressureSobolevOperator_value, pressureSobolevOperator_value,
    value_sobolevReflection, pressure_reflection period A hA]


-- @@ L414-426 verbatim
/-- The actual pressure-corrected forcing commutes with reflection for an even metric. -/
theorem projectedSource_reflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    sobolevReflection period q (projectedSourceOperator period K κ m c hc hpos u) =
      projectedSourceOperator period K κ m c hc hpos (sobolevReflection period q u) := by
  change sobolevReflection period q (u - coefficientSobolevOperator period K
    (pressureSobolevOperator period K κ m c hc hpos u)) =
    sobolevReflection period q u - coefficientSobolevOperator period K
      (pressureSobolevOperator period K κ m c hc hpos (sobolevReflection period q u))
  simp only [map_sub, coefficient_reflection period K hA, pressureSobolev_reflection period K hA]


-- @@ L428-446 verbatim
/-- The coordinate product reflects without a derivative sign. -/
theorem coordinateProduct_reflection {q : ℕ} (hq : 6 ≤ q) (i : Fin 3)
    (u v : SobolevSpace period (q + 1)) :
    coordinateProduct period hq i (sobolevReflection period (q+1) u) (sobolevReflection period
        (q+1) v) =
      sobolevReflection period q (coordinateProduct period hq i u v) := by
  change productHq period hq (EulerVectorCylinder.coordinate 3 i)
      (EulerVectorCylinder.coordinate_norm_le 3 i)
    (truncateOperator period q (sobolevReflection period (q+1) u))
    (truncateOperator period q (sobolevReflection period (q+1) v)) =
    sobolevReflection period q (productHq period hq (EulerVectorCylinder.coordinate 3 i)
      (EulerVectorCylinder.coordinate_norm_le 3 i) (truncateOperator period q u) (truncateOperator
          period q v))
  exact (congrArg₂ (productHq period hq (EulerVectorCylinder.coordinate 3 i)
      (EulerVectorCylinder.coordinate_norm_le 3 i))
    (truncate_reflection period u) (truncate_reflection period v)).trans
    (product_reflection period hq (EulerVectorCylinder.coordinate 3 i)
      (EulerVectorCylinder.coordinate_norm_le 3 i) (truncateOperator period q u) (truncateOperator
          period q v)).symm


-- @@ L448-471 verbatim
/-- The actual algebraic Euler term reverses reflection because its
coefficient fields, `κ F⁻¹ ∂ᵢF`, are odd. -/
theorem algebraic_reflection {q : ℕ} (hq : 6 ≤ q)
    (A : Fin 3 → SmoothCoefficient period) (K : ∀ i, CoefficientJet period standardDirection q (A
        i))
    (hA : ∀ i x, (A i).coefficient (-x) = -(A i).coefficient x)
    (u v : SobolevSpace period (q + 1)) :
    algebraicBilinear period hq (fun i => coefficientSobolevOperator period (K i))
      (sobolevReflection period (q+1) u) (sobolevReflection period (q+1) v) =
      -sobolevReflection period q (algebraicBilinear period hq (fun i => coefficientSobolevOperator
          period (K i)) u v) := by
  have hi (i : Fin 3) : coefficientSobolevOperator period (K i)
      (coordinateProduct period hq i (sobolevReflection period (q+1) u) (sobolevReflection period
          (q+1) v)) =
      -sobolevReflection period q (coefficientSobolevOperator period (K i) (coordinateProduct
          period hq i u v)) := by
    have hp := congrArg (coefficientSobolevOperator period (K i)) (coordinateProduct_reflection
        period hq i u v)
    have hc := congrArg Neg.neg (odd_coefficient_reflection period (K i) (hA i) (coordinateProduct
        period hq i u v))
    simp only [neg_neg] at hc
    exact hp.trans hc.symm
  have hh := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl (fun i _ => hi i)
  simpa only [algebraicBilinear_apply, map_sum, Finset.sum_neg_distrib] using hh


-- @@ L473-492 verbatim
/-- The literal Euler bilinear term reverses pullback reflection. -/
theorem eulerBilinear_reflection {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (A : Fin 3 → SmoothCoefficient period) (K : ∀ i, CoefficientJet period standardDirection q (A
        i))
    (hA : ∀ i x, (A i).coefficient (-x) = -(A i).coefficient x)
    (u v : SobolevSpace period (q + 1)) :
    eulerBilinear period hq L hL (fun i => coefficientSobolevOperator period (K i))
      (sobolevReflection period (q+1) u) (sobolevReflection period (q+1) v) =
      -sobolevReflection period q (eulerBilinear period hq L hL (fun i =>
          coefficientSobolevOperator period (K i)) u v) := by
  change transportBilinear period hq L hL _ _ + algebraicBilinear period hq _ _ _ =
    -sobolevReflection period q (transportBilinear period hq L hL u v + algebraicBilinear period hq
        _ u v)
  have hh := congrArg₂ HAdd.hAdd (transport_reflection period hq L hL u v) (algebraic_reflection
      period hq A K hA u v)
  exact hh.trans ((neg_add _ _).symm.trans
    (congrArg Neg.neg (map_add (sobolevReflection period q)
      (transportBilinear period hq L hL u v)
      (algebraicBilinear period hq (fun i => coefficientSobolevOperator period (K i)) u v))).symm)


-- @@ L494-506 verbatim
/-- Signed reflection is an exact symmetry of the actual bilinear Euler term. -/
theorem eulerBilinear_oddReflection {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (A : Fin 3 → SmoothCoefficient period) (K : ∀ i, CoefficientJet period standardDirection q (A
        i))
    (hA : ∀ i x, (A i).coefficient (-x) = -(A i).coefficient x)
    (u v : SobolevSpace period (q + 1)) :
    oddReflection period q (eulerBilinear period hq L hL (fun i => coefficientSobolevOperator
        period (K i)) u v) =
      eulerBilinear period hq L hL (fun i => coefficientSobolevOperator period (K i))
        (oddReflection period (q+1) u) (oddReflection period (q+1) v) := by
  simp only [oddReflection_apply, map_neg, neg_apply, neg_neg]
  exact (eulerBilinear_reflection period hq L hL A K hA u v).symm


-- @@ L508-508 verbatim
end EulerSobolevParityOperators


-- @@ L510-510 verbatim
end

-- @@ L511-511 verbatim
end


-- @@ L513-513 verbatim
end


-- @@ L515-515 verbatim
@[expose] public section


-- @@ L517-517 verbatim
noncomputable section


-- @@ L519-519 verbatim
namespace EulerCorrectionParity


-- @@ L521-524 verbatim
open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerSobolevTransport EulerCorrectionOperators
  EulerCylinderReflection  EulerSobolevReflection EulerSobolevParityOperators


-- @@ L526-527 verbatim
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]


-- @@ L529-535 verbatim
/-- Exact equivariance of the residual plus the linearized quadratic increment. -/
theorem linearized_source_equivariant (R : X →L[ℝ] X) (S : Y →L[ℝ] Y)
    (B : X →L[ℝ] X →L[ℝ] Y) (C : X →L[ℝ] Y) (z : X) (r : Y)
    (hB : ∀ u v, S (B u v) = B (R u) (R v)) (hC : ∀ u, S (C u) = C (R u))
    (hz : R z = z) (hr : S r = r) (e : X) :
    S (r + linearize B C z e + B e e) = r + linearize B C z (R e) + B (R e) (R e) := by
  simp only [linearize_apply, map_add, hB, hC, hz, hr]


-- @@ L537-537 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L539-541 verbatim
/-- The inherited Sobolev additive normed-group instance. -/
local instance correctionParityGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

-- @@ L542-544 verbatim
/-- The inherited real Sobolev module instance. -/
local instance correctionParitySpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance


-- @@ L546-550 verbatim
/-- Signed reflection on Sobolev fields has the literal signed L² value. -/
theorem value_oddReflection {q : ℕ} (u : SobolevSpace period q) :
    value period (oddReflection period q u) = -reflection period (value period u) := by
  change -value period (sobolevReflection period q u) = _
  rw [value_sobolevReflection]


-- @@ L552-564 verbatim
/-- Actual almost-everywhere odd parity is precisely a fixed point of signed reflection. -/
theorem oddReflection_fixed_of_ae {q : ℕ} (u : SobolevSpace period q)
    (hu : ∀ᵐ x ∂liftMeasure period, value period u (-x) = -value period u x) :
    oddReflection period q u = u := by
  apply value_injective period
  rw [value_oddReflection]
  have hh : reflection period (value period u) = -value period u := by
    apply Lp.ext
    filter_upwards [reflection_ae period (value period u), Lp.coeFn_neg (value period u), hu]
      with x h1 h2 h3
    rw [h1, h2]
    exact h3
  rw [hh, neg_neg]


-- @@ L566-571 verbatim
/-- Signed reflection commutes with restriction to the next Sobolev order. -/
theorem truncate_oddReflection {q : ℕ} (u : SobolevSpace period (q + 1)) :
    truncateOperator period q (oddReflection period (q+1) u) =
      oddReflection period q (truncateOperator period q u) := by
  simp only [oddReflection_apply, map_neg]
  exact congrArg Neg.neg (truncate_reflection period u)


-- @@ L573-580 verbatim
/-- An actual even coefficient commutes with signed reflection. -/
theorem coefficient_oddReflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x) (u : SobolevSpace period q) :
    oddReflection period q (coefficientSobolevOperator period K u) =
      coefficientSobolevOperator period K (oddReflection period q u) := by
  simp only [oddReflection_apply, map_neg]
  exact congrArg Neg.neg (coefficient_reflection period K hA u)


-- @@ L582-591 verbatim
/-- The actual pressure inverse commutes with signed reflection for an even metric. -/
theorem pressure_oddReflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    oddReflection period q (pressureSobolevOperator period K κ m c hc hpos u) =
      pressureSobolevOperator period K κ m c hc hpos (oddReflection period q u) := by
  simp only [oddReflection_apply, map_neg]
  exact congrArg Neg.neg (pressureSobolev_reflection period K hA κ m c hc hpos u)


-- @@ L593-602 verbatim
/-- The actual pressure-corrected source commutes with signed reflection. -/
theorem projectedSource_oddReflection {q : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection q A)
    (hA : ∀ x, A.coefficient (-x) = A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (u : SobolevSpace period q) :
    oddReflection period q (projectedSourceOperator period K κ m c hc hpos u) =
      projectedSourceOperator period K κ m c hc hpos (oddReflection period q u) := by
  simp only [oddReflection_apply, map_neg]
  exact congrArg Neg.neg (projectedSource_reflection period K hA κ m c hc hpos u)


-- @@ L604-631 verbatim
/-- The literal non-pressure correction source has odd-reflection symmetry
under the source's actual even linear and odd quadratic coefficients. -/
theorem rawSource_oddReflection {q : ℕ} (hq : 6 ≤ q) {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (t : T)
    (hL : ∀ x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
        t).coefficient x)
    (hz : oddReflection period (q + 1) (D.approximation t) = D.approximation t)
    (hr : oddReflection period q (D.residual t) = D.residual t)
    (e : SobolevSpace period (q + 1)) :
    oddReflection period q (D.rawSource period hq t e) =
      D.rawSource period hq t (oddReflection period (q+1) e) := by
  let L := velocityComponents D.κ D.direction
  let hLnorm := velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound
  let F := eulerBilinear period hq L hLnorm (fun i => coefficientSobolevOperator period
      ((D.quadratic i).jet t))
  let C := (coefficientSobolevOperator period (D.linear.jet t)).comp (truncateOperator period q)
  have hF (u v : SobolevSpace period (q+1)) : oddReflection period q (F u v) =
      F (oddReflection period (q+1) u) (oddReflection period (q+1) v) :=
    eulerBilinear_oddReflection period hq L hLnorm (fun i => (D.quadratic i).coefficient t)
      (fun i => (D.quadratic i).jet t) hQ u v
  have hC (u : SobolevSpace period (q+1)) : oddReflection period q (C u) = C (oddReflection period
      (q+1) u) :=
    (coefficient_oddReflection period (D.linear.jet t) hL (truncateOperator period q u)).trans
      (congrArg (coefficientSobolevOperator period (D.linear.jet t)) (truncate_oddReflection period
          u).symm)
  exact linearized_source_equivariant (oddReflection period (q+1)) (oddReflection period q) F C
    (D.approximation t) (D.residual t) hF hC hz hr e


-- @@ L633-653 verbatim
/-- The genuine correction pressure transforms by signed reflection,
with its sign fixed by the actual pressure definition. -/
theorem correction_pressure_oddReflection {q : ℕ} (hq : 6 ≤ q) {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (t : T)
    (hG : ∀ x, (D.metric.coefficient t).coefficient (-x) = (D.metric.coefficient t).coefficient x)
    (hL : ∀ x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
        t).coefficient x)
    (hz : oddReflection period (q + 1) (D.approximation t) = D.approximation t)
    (hr : oddReflection period q (D.residual t) = D.residual t)
    (e : SobolevSpace period (q + 1)) :
    oddReflection period q (D.pressure period hq t e) =
      D.pressure period hq t (oddReflection period (q+1) e) := by
  change oddReflection period q (-(pressureSobolevOperator period (D.metric.jet t) D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e))) = _
  rw [map_neg]
  exact congrArg Neg.neg ((pressure_oddReflection period (D.metric.jet t) hG D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e)).trans
    (congrArg (pressureSobolevOperator period (D.metric.jet t) D.κ D.direction D.coercivity
        D.coercivity_pos
      (D.metric_pos t)) (rawSource_oddReflection period hq D t hL hQ hz hr e)))


-- @@ L655-675 verbatim
/-- The literal projected nonlinear correction equation has the required
odd symmetry, derived from the concrete parity of its prescribed fields. -/
theorem correction_source_oddReflection {q : ℕ} (hq : 6 ≤ q) {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (t : T)
    (hG : ∀ x, (D.metric.coefficient t).coefficient (-x) = (D.metric.coefficient t).coefficient x)
    (hL : ∀ x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
        t).coefficient x)
    (hz : oddReflection period (q + 1) (D.approximation t) = D.approximation t)
    (hr : oddReflection period q (D.residual t) = D.residual t)
    (e : SobolevSpace period (q + 1)) :
    oddReflection period q ((D.coefficients period hq).apply t e) =
      (D.coefficients period hq).apply t (oddReflection period (q+1) e) := by
  change oddReflection period q (-(projectedSourceOperator period (D.metric.jet t) D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e))) = _
  rw [map_neg]
  exact congrArg Neg.neg ((projectedSource_oddReflection period (D.metric.jet t) hG D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t e)).trans
    (congrArg (projectedSourceOperator period (D.metric.jet t) D.κ D.direction D.coercivity
        D.coercivity_pos
      (D.metric_pos t)) (rawSource_oddReflection period hq D t hL hQ hz hr e)))


-- @@ L677-677 verbatim
end EulerCorrectionParity


-- @@ L679-679 verbatim
end

-- @@ L680-680 verbatim
end


-- @@ L682-682 verbatim
end


-- @@ L684-684 verbatim
section


-- @@ L686-686 verbatim
/-! Odd parity of actual inviscid correction solutions, proved by genuine PDE uniqueness. -/


-- @@ L688-688 verbatim
@[expose] public section


-- @@ L690-690 verbatim
noncomputable section


-- @@ L692-692 verbatim
namespace EulerInviscidCorrectionParity


-- @@ L694-696 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionStabilityBudget EulerInviscidCorrectionUniqueness
  EulerVolterraConvolution EulerCylinderReflection EulerSobolevReflection EulerCorrectionParity

-- @@ L697-697 verbatim
open scoped Topology


-- @@ L699-699 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L701-703 verbatim
/-- The inherited finite Sobolev normed-group instance. -/
local instance inviscidParityGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

-- @@ L704-705 verbatim
/-- The inherited real finite Sobolev module instance. -/
local instance inviscidParitySpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance


-- @@ L707-754 verbatim
/-- Every actual zero-initial inviscid correction is odd under the
source's genuine parity hypotheses on the prescribed fields and coefficients.
The reflected path solves the literal same equation; uniqueness is proved
by the existing metric-energy theorem, not assumed. -/
theorem inviscid_correction_odd {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T)) (B : StabilityBudget period hT D)
    (hG : ∀ t x, (D.metric.coefficient t).coefficient (-x) = (D.metric.coefficient t).coefficient x)
    (hL : ∀ t x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ t i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
        t).coefficient x)
    (hzOdd : ∀ t, oddReflection period (q + 1) (D.approximation t) = D.approximation t)
    (hrOdd : ∀ t, oddReflection period q (D.residual t) = D.residual t)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hi : u ⟨0, le_rfl, hT⟩ = 0)
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT u r))
        (value period ((D.coefficients period hq).apply ⟨t, ht.1.le, ht.2.le⟩ (u
            ⟨t, ht.1.le, ht.2.le⟩))) t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ t, value period (u t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∀ t, oddReflection period (q+1) (u t) = u t := by
  let v := (oddReflection period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  have hv0 : v ⟨0,le_rfl,hT⟩ = 0 := by
    change oddReflection period (q+1) (u ⟨0,le_rfl,hT⟩) = 0
    rw [hi, map_zero]
  have hv : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT v r))
        (value period ((D.coefficients period hq).apply ⟨t,ht.1.le,ht.2.le⟩ (v
            ⟨t,ht.1.le,ht.2.le⟩))) t := by
    intro t ht
    let τ : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
    have hd := ((reflection period).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hu t
        ht)).neg
    have he := congrArg (value period (q := q))
      (correction_source_oddReflection period hq D τ (hG τ) (hL τ) (hQ τ) (hzOdd τ) (hrOdd τ) (u τ))
    rw [value_oddReflection] at he
    convert! hd using 1
    · funext r
      change value period (oddReflection period (q+1) (u (projIcc 0 T hT r))) =
        -reflection period (value period (u (projIcc 0 T hT r)))
      exact value_oddReflection period _
    · exact he.symm
  have hvd : ∀ t, value period (v t) ∈ divergenceFreeSpace period D.κ D.direction := by
    intro t
    exact oddReflection_divergenceFree period D.κ D.direction (u t) (hud t)
  have he := inviscid_correction_unique period hq T hT D B u v (hi.trans hv0.symm) hu hv hz hud hvd
  intro t
  exact (congrArg (fun f => f t) he).symm


-- @@ L756-769 verbatim
/-- The actual signed coercive correction pressure has odd gradient parity
at every time once the correction parity has been established. -/
theorem inviscid_correction_pressure_odd {q : ℕ} (hq : 6 ≤ q) {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (t : T)
    (hG : ∀ x, (D.metric.coefficient t).coefficient (-x) = (D.metric.coefficient t).coefficient x)
    (hL : ∀ x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
        t).coefficient x)
    (hz : oddReflection period (q + 1) (D.approximation t) = D.approximation t)
    (hr : oddReflection period q (D.residual t) = D.residual t)
    (u : SobolevSpace period (q + 1)) (hu : oddReflection period (q + 1) u = u) :
    oddReflection period q (D.pressure period hq t u) = D.pressure period hq t u := by
  have hh := correction_pressure_oddReflection period hq D t hG hL hQ hz hr u
  rwa [hu] at hh


-- @@ L771-771 verbatim
end EulerInviscidCorrectionParity


-- @@ L773-773 verbatim
end

-- @@ L774-774 verbatim
end


-- @@ L776-776 verbatim
end


-- @@ L778-778 verbatim
section


-- @@ L780-781 verbatim
/-! Genuine continuous Sobolev realizations of the assembled correction and its actual pressure at
every order. -/


-- @@ L783-783 verbatim
@[expose] public section


-- @@ L785-785 verbatim
noncomputable section


-- @@ L787-787 verbatim
namespace EulerCorrectionAssembly


-- @@ L789-789 verbatim
open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerAllOrderCorrectionData


-- @@ L791-791 verbatim
variable (period : ℝ) [Fact (0 < period)]

-- @@ L792-792 verbatim
variable {T : ℝ} {hT : 0 < T} {A : Data period T}


-- @@ L794-801 verbatim
/-- The assembled correction as one actual L² field with continuous Sobolev realizations at every
order. -/
def FiniteFamily.fieldTower (F : FiniteFamily period hT A) (C : ComparisonData period hT A) :
    FieldTower period T where
  field := F.commonPath period
  realization q := (restrictOperator period (by omega : q ≤ (q+6)+1)).compLeftContinuous ℝ
    (Icc (0 : ℝ) T) (F.solution (q+6) (by omega))
  value_eq q t := F.value_common period C (q+6) (by omega) t


-- @@ L803-810 verbatim
/-- The actual signed pressure as one L² field with continuous Sobolev realizations at every order.
-/
def FiniteFamily.pressureTower (F : FiniteFamily period hT A) (C : ComparisonData period hT A) :
    FieldTower period T where
  field := F.commonPressure period
  realization q := (restrictOperator period (by omega : q ≤ q+6)).compLeftContinuous ℝ
    (Icc (0 : ℝ) T) (F.signedPressurePath period (q+6) (by omega))
  value_eq q t := F.signedPressurePath_value_common period C (q+6) (by omega) t


-- @@ L812-821 verbatim
/-- Each finite solution is exactly the common tower's realization at that same Sobolev order. -/
theorem FiniteFamily.solution_eq_realization (F : FiniteFamily period hT A) (C : ComparisonData
    period hT A)
    (q : ℕ) (hq : 6 ≤ q) :
    F.solution q hq = (F.fieldTower period C).realization (q+1) := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  exact (F.value_common period C q hq t).trans
    ((F.fieldTower period C).value_eq (q+1) t).symm


-- @@ L823-832 verbatim
/-- Every finite signed pressure is exactly the common pressure tower's realization at that order.
-/
theorem FiniteFamily.signedPressurePath_eq_realization (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (q : ℕ) (hq : 6 ≤ q) :
    F.signedPressurePath period q hq = (F.pressureTower period C).realization q := by
  apply ContinuousMap.ext
  intro t
  apply value_injective period
  exact (F.signedPressurePath_value_common period C q hq t).trans
    ((F.pressureTower period C).value_eq q t).symm


-- @@ L834-834 verbatim
end EulerCorrectionAssembly


-- @@ L836-836 verbatim
end

-- @@ L837-837 verbatim
end


-- @@ L839-839 verbatim
end


-- @@ L841-841 verbatim
@[expose] public section


-- @@ L843-843 verbatim
noncomputable section


-- @@ L845-845 verbatim
namespace EulerCorrectionAssembly


-- @@ L847-849 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerAllOrderCorrectionData EulerCylinderReflection
  EulerSobolevReflection EulerCorrectionParity EulerInviscidCorrectionParity


-- @@ L851-851 verbatim
variable (period : ℝ) [Fact (0 < period)]

-- @@ L852-852 verbatim
variable {T : ℝ} {hT : 0 < T} {A : Data period T}


-- @@ L854-870 verbatim
/-- The prescribed source's actual joint spatial-angular parities.
The metric and linear coefficients are even, the quadratic coefficient is odd,
and the approximate velocity and residual are odd as actual L² fields. -/
structure ParityData (A : Data period T) where
  /-- The actual pressure metric is even. -/
  metric : ∀ t x, (A.metric.coefficient t).coefficient (-x) =
    (A.metric.coefficient t).coefficient x
  /-- The actual linear coefficient is even. -/
  linear : ∀ t x, (A.linear.coefficient t).coefficient (-x) =
    (A.linear.coefficient t).coefficient x
  /-- Each actual quadratic coefficient is odd. -/
  quadratic : ∀ t i x, ((A.quadratic i).coefficient t).coefficient (-x) =
    -((A.quadratic i).coefficient t).coefficient x
  /-- The prescribed approximate velocity is an odd actual field. -/
  approximation : ∀ t, -reflection period (A.approximation.field t) = A.approximation.field t
  /-- The prescribed residual is an odd actual field. -/
  residual : ∀ t, -reflection period (A.residual.field t) = A.residual.field t


-- @@ L872-878 verbatim
/-- Oddness of the actual common L² field forces oddness of every Sobolev realization. -/
theorem fieldTower_realization_odd (f : FieldTower period T)
    (hf : ∀ t, -reflection period (f.field t) = f.field t) (q : ℕ) (t : Icc (0 : ℝ) T) :
    oddReflection period q (f.realization q t) = f.realization q t := by
  apply value_injective period
  rw [value_oddReflection, f.value_eq]
  exact hf t


-- @@ L880-894 verbatim
/-- Genuine PDE uniqueness makes every finite correction odd from the prescribed input parity. -/
theorem FiniteFamily.solution_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    oddReflection period (q+1) (F.solution q hq t) = F.solution q hq t := by
  apply inviscid_correction_odd period hq T hT.le (A.atOrder period q)
    (C.stabilityBudget period q) P.metric P.linear P.quadratic
    (fieldTower_realization_odd period A.approximation P.approximation (q+1))
    (fieldTower_realization_odd period A.residual P.residual q) (F.solution q hq)
    (F.initial q hq) (F.equation q hq) _ (F.divergence q hq) t
  intro s
  change value period (A.approximation.realization (q+1) s) ∈
    divergenceFreeSpace period A.κ A.direction
  rw [A.approximation.value_eq]
  exact C.divergence s


-- @@ L896-902 verbatim
/-- The actual assembled continuous L² correction is odd. -/
theorem FiniteFamily.commonPath_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A) (t : Icc (0 : ℝ) T) :
    -reflection period (F.commonPath period t) = F.commonPath period t := by
  have h := congrArg (value period (q := 7)) (F.solution_odd period C P 6 le_rfl t)
  rw [value_oddReflection] at h
  exact h


-- @@ L904-918 verbatim
/-- A continuous representative of an actual odd L² field is pointwise odd. -/
theorem continuous_representative_odd (u : LiftL2 period) (g : LiftDomain period → Vector3)
    (hu : -reflection period u = u) (hg : Continuous g)
    (hrep : (u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g) :
    ∀ x, g (-x) = -g x := by
  have hr : reflection period u = -u := by
    simpa only [neg_neg] using congrArg Neg.neg hu
  have ha : (fun x => g (-x)) =ᵐ[liftMeasure period] fun x => -g x := by
    filter_upwards [reflection_ae period u,
      (measurePreserving_reflection period).quasiMeasurePreserving.ae hrep,
      hrep, Lp.coeFn_neg u] with x h1 h2 h3 h4
    rw [hr] at h1
    rw [← h2, ← h3, ← h1, h4]
    rfl
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq ha (hg.comp continuous_neg) hg.neg)


-- @@ L920-929 verbatim
/-- The canonical smooth correction is odd at every spatial and angular point. -/
theorem FiniteFamily.pointField_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    F.pointField period t (-x) = -F.pointField period t x := by
  have hc : Continuous (F.pointField period t) :=
    EulerMetricTransport.smoothField_continuous period (F.pointField period t)
      (F.pointField_smooth period C t)
  exact continuous_representative_odd period (F.commonPath period t) (F.pointField period t)
    (F.commonPath_odd period C P t) hc (F.pointField_ae period t) x


-- @@ L931-941 verbatim
/-- The actual signed coercive pressure is odd at every finite Sobolev order. -/
theorem FiniteFamily.signedPressurePath_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    oddReflection period q (F.signedPressurePath period q hq t) =
      F.signedPressurePath period q hq t := by
  exact inviscid_correction_pressure_odd period hq (A.atOrder period q) t
    (P.metric t) (P.linear t) (P.quadratic t)
    (fieldTower_realization_odd period A.approximation P.approximation (q+1) t)
    (fieldTower_realization_odd period A.residual P.residual q t)
    (F.solution q hq t) (F.solution_odd period C P q hq t)


-- @@ L943-949 verbatim
/-- The actual assembled signed pressure gradient is odd in L². -/
theorem FiniteFamily.commonPressure_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A) (t : Icc (0 : ℝ) T) :
    -reflection period (F.commonPressure period t) = F.commonPressure period t := by
  have h := congrArg (value period (q := 6)) (F.signedPressurePath_odd period C P 6 le_rfl t)
  rw [value_oddReflection] at h
  exact h


-- @@ L951-957 verbatim
/-- Every realization of the assembled correction tower is odd. -/
theorem FiniteFamily.fieldTower_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    oddReflection period q ((F.fieldTower period C).realization q t) =
      (F.fieldTower period C).realization q t :=
  fieldTower_realization_odd period (F.fieldTower period C) (F.commonPath_odd period C P) q t


-- @@ L959-965 verbatim
/-- Every realization of the actual assembled signed pressure tower is odd. -/
theorem FiniteFamily.pressureTower_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (q : ℕ) (t : Icc (0 : ℝ) T) :
    oddReflection period q ((F.pressureTower period C).realization q t) =
      (F.pressureTower period C).realization q t :=
  fieldTower_realization_odd period (F.pressureTower period C) (F.commonPressure_odd period C P) q t


-- @@ L967-967 verbatim
end EulerCorrectionAssembly
