/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module


public import LeanPool.OSforGFF.Measure.Construct
public import LeanPool.OSforGFF.Spacetime.TimeTranslation
import LeanPool.OSforGFF.Measure.IsGaussian
import LeanPool.OSforGFF.OS.OS2Invariance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Nat.Choose.Multinomial


-- @@ L16-25 verbatim
/-!
# OS4 — Shared Infrastructure

Shared lemmas for os4Clustering and OS4Ergodicity:

- Time translation duality: ⟨T_s ω, g⟩ = ⟨ω, T_{−s} g⟩
- GFF MGF formula: 𝔼[e^{⟨ω,f⟩}] = exp(½ S₂(f,f)) and its time-translation invariance
- Joint MGF factorization: 𝔼[e^{⟨ω,f+T_{−s}g⟩}] = E_f · E_g · exp(S₂(f, T_{−s}g))
- Exponential bound: |e^z − 1| ≤ |z| · e^{|z|}
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open MeasureTheory Real

-- @@ L30-30 verbatim
open TopologicalSpace

-- @@ L31-31 verbatim
open scoped BigOperators


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace OS4infra


-- @@ L37-41 verbatim
/-! ## Time Translation Infrastructure

We re-export the core TimeTranslation API so that importers of OS4infra
get these names in scope without a separate TimeTranslation import.
-/


-- @@ L43-57 verbatim
export TimeTranslation (
  timeIndex getTime timeShift timeShiftConst
  timeShift_time timeShift_spatial timeShift_add timeShift_zero timeShift_comm
  timeShift_contDiff timeShift_dist timeShift_isometry timeShift_antilipschitz
  timeShift_eq_add_const timeShift_hasTemperateGrowth
  timeTranslationSchwartzCLM timeTranslationSchwartz
  timeTranslationSchwartzℂCLM timeTranslationSchwartzℂ
  timeTranslationSchwartz_apply timeTranslationSchwartzℂ_apply
  timeTranslationSchwartz_add timeTranslationSchwartzℂ_add
  timeTranslationSchwartz_zero timeTranslationSchwartzℂ_zero
  timeTranslationSchwartz_add_fun timeTranslationSchwartz_smul
  continuous_timeTranslationSchwartz
  timeTranslationDistribution
  timeTranslationDistribution_apply timeTranslationDistribution_add timeTranslationDistribution_zero
)


-- @@ L59-59 verbatim
/-! ## Time Translation Decomposition Lemmas -/


-- @@ L61-67 verbatim
/-- Time translation commutes with real part extraction for complex Schwartz functions. -/
lemma timeTranslationSchwartzℂ_decompose_fst (s : ℝ) (g : TestFunctionℂ) :
    (complexTestFunctionDecompose (timeTranslationSchwartzℂ s g)).1 =
    timeTranslationSchwartz s (complexTestFunctionDecompose g).1 := by
  ext x
  simp only [complex_testfunction_decompose_fst_apply, timeTranslationSchwartz_apply,
    timeTranslationSchwartzℂ_apply]


-- @@ L69-75 verbatim
/-- Time translation commutes with imaginary part extraction for complex Schwartz functions. -/
lemma timeTranslationSchwartzℂ_decompose_snd (s : ℝ) (g : TestFunctionℂ) :
    (complexTestFunctionDecompose (timeTranslationSchwartzℂ s g)).2 =
    timeTranslationSchwartz s (complexTestFunctionDecompose g).2 := by
  ext x
  simp only [complex_testfunction_decompose_snd_apply, timeTranslationSchwartz_apply,
    timeTranslationSchwartzℂ_apply]


-- @@ L77-85 verbatim
/-- Time translation on distributions is compatible with complex pairing.
    ⟨T_s ω, g⟩_ℂ = ⟨ω, T_{-s} g⟩_ℂ
-/
lemma timeTranslationDistribution_pairingℂ (s : ℝ) (ω : FieldConfiguration)
    (g : TestFunctionℂ) :
    distributionPairingℂReal (timeTranslationDistribution s ω) g =
    distributionPairingℂReal ω (timeTranslationSchwartzℂ (-s) g) := by
  simp only [distributionPairingℂReal, timeTranslationDistribution_apply]
  rw [timeTranslationSchwartzℂ_decompose_fst (-s) g, timeTranslationSchwartzℂ_decompose_snd (-s) g]


-- @@ L87-87 verbatim
/-! ## Continuity of Complex Pairing under Time Translation -/


-- @@ L89-110 verbatim
/-- s ↦ ⟨T_s ω, g⟩_ℂ is continuous. Uses the proved `continuous_timeTranslationSchwartz`. -/
lemma continuous_distributionPairingℂ_timeTranslation (ω : FieldConfiguration)
    (g : TestFunctionℂ) :
    Continuous (fun s => distributionPairingℂReal (timeTranslationDistribution s ω) g) := by
  have h_eq : (fun s => distributionPairingℂReal (timeTranslationDistribution s ω) g)
      = (fun s => distributionPairingℂReal ω (timeTranslationSchwartzℂ (-s) g)) := by
    ext s
    exact timeTranslationDistribution_pairingℂ s ω g
  rw [h_eq]
  simp only [distributionPairingℂReal]
  set g_re := (complexTestFunctionDecompose g).1
  set g_im := (complexTestFunctionDecompose g).2
  have h_decomp_re : ∀ s, (complexTestFunctionDecompose (timeTranslationSchwartzℂ (-s) g)).1
      = timeTranslationSchwartz (-s) g_re := fun s => timeTranslationSchwartzℂ_decompose_fst (-s) g
  have h_decomp_im : ∀ s, (complexTestFunctionDecompose (timeTranslationSchwartzℂ (-s) g)).2
      = timeTranslationSchwartz (-s) g_im := fun s => timeTranslationSchwartzℂ_decompose_snd (-s) g
  simp only [h_decomp_re, h_decomp_im]
  apply Continuous.add
  · exact Complex.continuous_ofReal.comp (ω.continuous.comp
      ((TimeTranslation.continuous_timeTranslationSchwartz g_re).comp continuous_neg))
  · exact (Continuous.mul continuous_const) (Complex.continuous_ofReal.comp (ω.continuous.comp
      ((TimeTranslation.continuous_timeTranslationSchwartz g_im).comp continuous_neg)))


-- @@ L112-112 verbatim
/-! ## Euclidean Group Infrastructure for Time Translation -/


-- @@ L114-117 verbatim
/-- Time translation as a Euclidean group element.
    timeTranslationE t = (1, -timeShiftConst t) where 1 is the identity rotation.
-/
def timeTranslationE (t : ℝ) : QFT.E := ⟨1, -timeShiftConst t⟩


-- @@ L119-132 verbatim
/-- The Euclidean action of timeTranslationE equals timeTranslationSchwartzℂ. -/
lemma euclidean_action_timeTranslationE (t : ℝ) (f : TestFunctionℂ) :
    QFT.euclideanAction (timeTranslationE t) f = timeTranslationSchwartzℂ t f := by
  ext x
  simp only [QFT.euclidean_action_apply, QFT.euclidean_pullback_eq_inv_act]
  simp only [timeTranslationE, QFT.act]
  simp only [timeTranslationSchwartzℂ_apply, timeShift_eq_add_const]
  congr 1
  simp only [QFT.inv_R, QFT.inv_t, QFT.LinearIsometry.inv]
  have h1 : ∀ v, (LinearIsometry.toLinearIsometryEquiv (1 : QFT.O4) rfl).symm v = v := fun v => by
    have hv : (LinearIsometry.toLinearIsometryEquiv (1 : QFT.O4) rfl) v = v := by
      simp only [LinearIsometry.toLinearIsometryEquiv_apply, LinearIsometry.coe_one, id_eq]
    rw [← hv]; exact LinearIsometryEquiv.symm_apply_apply _ v
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, h1, neg_neg]


-- @@ L134-134 verbatim
/-! ## GFF Covariance Invariance -/


-- @@ L136-142 verbatim
/-- The GFF covariance is invariant under simultaneous time translation. -/
lemma freeCovarianceℂ_bilinear_timeTranslation_invariant (m : ℝ) (t : ℝ)
    (f g : TestFunctionℂ) :
    freeCovarianceℂBilinear m (timeTranslationSchwartzℂ t f) (timeTranslationSchwartzℂ t g) =
    freeCovarianceℂBilinear m f g := by
  rw [← euclidean_action_timeTranslationE t f, ← euclidean_action_timeTranslationE t g]
  exact QFT.freeCovarianceℂ_bilinear_euclidean_invariant m (timeTranslationE t) f g


-- @@ L144-144 verbatim
/-! ## GFF Moment Generating Function -/


-- @@ L146-174 verbatim
/-- MGF formula for GFF: ∫ exp(⟨ω,J⟩) dμ = exp(+(1/2) * C(J,J)).
    This follows from the characteristic function formula via substitution J → (-I)•J.
-/
lemma gff_mgf_formula (m : ℝ) [Fact (0 < m)] (J : TestFunctionℂ) :
    (∫ ω, Complex.exp (distributionPairingℂReal ω J) ∂(gaussianFreeFieldFree m).toMeasure) =
    Complex.exp ((1/2 : ℂ) * freeCovarianceℂBilinear m J J) := by
  let negI : ℂ := -Complex.I
  have h_to_cf : (∫ ω, Complex.exp (distributionPairingℂReal ω J)
      ∂(gaussianFreeFieldFree m).toMeasure) =
      GJGeneratingFunctionalℂ (gaussianFreeFieldFree m) (negI • J) := by
    unfold GJGeneratingFunctionalℂ
    congr 1
    ext ω
    congr 1
    have h_lin : distributionPairingℂReal ω (negI • J) =
        negI * distributionPairingℂReal ω J := by
      simpa using pairing_linear_combo ω J 0 negI 0
    rw [h_lin]
    simp only [negI]
    ring_nf
    simp [Complex.I_sq]
  rw [h_to_cf, GFFIsGaussian.gff_complex_characteristic_OS0 m]
  have h_cov : freeCovarianceℂBilinear m (negI • J) (negI • J) =
      -freeCovarianceℂBilinear m J J := by
    rw [freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
    simp only [negI]
    ring_nf
    simp [Complex.I_sq]
  simp_all


-- @@ L176-183 verbatim
/-- The GFF generating function is invariant under time translation. -/
lemma gff_generating_time_invariant (m : ℝ) [Fact (0 < m)] (s : ℝ) (f : TestFunctionℂ) :
    ∫ ω, Complex.exp (distributionPairingℂReal ω (timeTranslationSchwartzℂ s f))
      ∂(gaussianFreeFieldFree m).toMeasure =
    ∫ ω, Complex.exp (distributionPairingℂReal ω f)
      ∂(gaussianFreeFieldFree m).toMeasure := by
  rw [gff_mgf_formula, gff_mgf_formula]
  rw [freeCovarianceℂ_bilinear_timeTranslation_invariant m s f f]


-- @@ L185-185 verbatim
/-! ## Joint MGF Factorization -/


-- @@ L187-211 verbatim
/-- Joint MGF factorization for GFF.
    E[e^{⟨ω,f⟩+⟨ω,g⟩}] = E[e^{⟨ω,f⟩}] E[e^{⟨ω,g⟩}] e^{C(f,g)}
    This follows from the GFF being Gaussian.
-/
lemma gff_joint_mgf_factorization (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    (∫ ω, Complex.exp (distributionPairingℂReal ω f + distributionPairingℂReal ω g)
      ∂(gaussianFreeFieldFree m).toMeasure) =
    (∫ ω, Complex.exp (distributionPairingℂReal ω f) ∂(gaussianFreeFieldFree m).toMeasure) *
    (∫ ω, Complex.exp (distributionPairingℂReal ω g) ∂(gaussianFreeFieldFree m).toMeasure) *
    Complex.exp (SchwingerFunctionℂ₂ (gaussianFreeFieldFree m) f g) := by
  have h_pairing_add : ∀ ω, distributionPairingℂReal ω f + distributionPairingℂReal ω g =
      distributionPairingℂReal ω (f + g) := fun ω => by
    simpa using (pairing_linear_combo ω f g 1 1).symm
  have h_lhs : (∫ ω, Complex.exp (distributionPairingℂReal ω f + distributionPairingℂReal ω g)
      ∂(gaussianFreeFieldFree m).toMeasure) =
      (∫ ω, Complex.exp (distributionPairingℂReal ω (f + g))
      ∂(gaussianFreeFieldFree m).toMeasure) := by
    congr 1; ext ω; rw [h_pairing_add]
  rw [h_lhs, gff_mgf_formula, gff_mgf_formula, gff_mgf_formula,
    gff_two_point_equals_covarianceℂ_free, freeCovarianceℂ_bilinear_add_left,
    freeCovarianceℂ_bilinear_add_right, freeCovarianceℂ_bilinear_add_right,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [freeCovarianceℂ_bilinear_symm m g f]
  ring


-- @@ L213-213 verbatim
/-! ## Exponential Bound -/


-- @@ L215-230 verbatim
/-- ‖e^x - 1‖ ≤ ‖x‖ · e^{‖x‖} for complex x. -/
lemma exp_sub_one_bound_general (x : ℂ) : ‖Complex.exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have h1 : ‖Complex.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
    have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum x 1
    simpa using h
  have hexp_pos := Real.exp_pos ‖x‖
  have h2 : Real.exp ‖x‖ - 1 ≤ ‖x‖ * Real.exp ‖x‖ := by
    by_cases hr1 : ‖x‖ ≤ 1
    · have hle : 1 - Real.exp (-‖x‖) ≤ ‖x‖ := by
        have := Real.add_one_le_exp (-‖x‖); linarith
      have hkey : Real.exp ‖x‖ - 1 = Real.exp ‖x‖ * (1 - Real.exp (-‖x‖)) := by
        rw [Real.exp_neg]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left hle (le_of_lt hexp_pos)]
    · push Not at hr1
      nlinarith [(le_mul_iff_one_le_left hexp_pos).mpr (le_of_lt hr1)]
  linarith


-- @@ L232-232 verbatim
end OS4infra
