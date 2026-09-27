/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import LeanPool.ConnesRigidity.Paper.Section4.AChartDetectorMeasure
public import LeanPool.ConnesRigidity.Paper.Section4.SpectralPropertyT
import LeanPool.ConnesRigidity.Paper.Section4.SpectralDetectorBridge


-- @@ L12-14 verbatim
/-!
Finite detector sets for the raw Zhou split extensions. Paper: §4.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace Connes

-- @@ L19-19 verbatim
namespace PaperSpectralFiniteDetection


-- @@ L21-21 verbatim
open MeasureTheory

-- @@ L22-22 verbatim
open Construction

-- @@ L23-23 verbatim
open Construction.PaperKernel

-- @@ L24-24 verbatim
open PaperDualTopology

-- @@ L25-25 verbatim
open PaperAChartDetectorMeasure

-- @@ L26-26 verbatim
open PaperSpectralDetectorBridge

-- @@ L27-27 verbatim
open PaperPropertyT

-- @@ L28-28 verbatim
open PaperSpectralPropertyT


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-35 verbatim
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k

-- @@ L36-39 verbatim
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A

-- @@ L40-43 verbatim
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

-- @@ L44-47 verbatim
/--
The `VStar` construction used in the Connes rigidity formalization.
-/
abbrev VStar := PaperKernel.VStar

-- @@ L48-54 verbatim
/--
The `SymplecticIndex` construction used in the Connes rigidity formalization.
-/
abbrev SymplecticIndex := OpenAIPort.SymplecticIndex

/- The coefficient functional separates the standard A chart vector. Paper: §4.
-/

-- @@ L55-61 verbatim
/--
The `aZeroCoeff` construction used in the Connes rigidity formalization.
-/
def aZeroCoeff : A →ₗ[k] k where
  toFun a := (a 0).constantCoeff
  map_add' a b := by simp
  map_smul' r a := by simp [smul_eq_mul]


-- @@ L63-68 verbatim
/-- The coefficient functional takes the base chart vector to one. Paper: §4. -/
lemma aZeroCoeff_basisVector_zero :
    aZeroCoeff (PaperFiniteCharts.basisVector 0) = 1 := by
  simp [aZeroCoeff, PaperFiniteCharts.basisVector]

/- The four A-coordinate detector elements are pairwise distinct. Paper: §4. -/

-- @@ L69-122 verbatim
theorem aCoordinateEmbedding_injective :
    Function.Injective
      (fun v : SymplecticIndex =>
        PaperAChartDetectorMeasure.aCoordinateEmbedding v
          (PaperFiniteCharts.basisVector 0)) := by
  intro v w h
  have hfirst := congrArg Prod.fst h
  change (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
      (LinearMap.proj v : VStar)) =
    (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
      (LinearMap.proj w : VStar)) at hfirst
  by_contra hvw
  have hzero :
      PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
        ((LinearMap.proj v : VStar) + (LinearMap.proj w : VStar)) = 0 := by
    calc
      PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
          ((LinearMap.proj v : VStar) + (LinearMap.proj w : VStar)) =
        (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
            (LinearMap.proj v : VStar)) +
          (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
            (LinearMap.proj w : VStar)) := by
              rw [TensorProduct.tmul_add]
      _ = (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
            (LinearMap.proj w : VStar)) +
          (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
            (LinearMap.proj w : VStar)) := by rw [hfirst]
      _ = 0 := by
        calc
          (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
              (LinearMap.proj w : VStar)) +
              (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
                (LinearMap.proj w : VStar)) =
            (1 : k) • (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
              (LinearMap.proj w : VStar)) +
              (1 : k) • (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
                (LinearMap.proj w : VStar)) := by simp
          _ = ((1 : k) + 1) •
              (PaperFiniteCharts.basisVector 0 ⊗ₜ[k]
                (LinearMap.proj w : VStar)) := by
            rw [add_smul]
          _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]
  have hcontract := congrArg
    (fun z : PaperKernel.AVStar =>
      aZeroCoeff (PaperKernel.contractStar
        (LinearMap.applyₗ (R := k) (Pi.single v 1)) z)) hzero
  rw [PaperKernel.contractStar_tmul, map_zero, map_smul,
    aZeroCoeff_basisVector_zero] at hcontract
  have hone : (1 : k) = 0 := by
    simp [smul_eq_mul, hvw] at hcontract
  exact one_ne_zero hone

/- The finite A-detector embedding used by the §4 criterion. Paper: §4.
-/

-- @@ L123-129 verbatim
/--
The `aDetectorEmbedding` construction used in the Connes rigidity formalization.
-/
def aDetectorEmbedding : SymplecticIndex ↪ D where
  toFun v := PaperAChartDetectorMeasure.aCoordinateEmbedding v
    (PaperFiniteCharts.basisVector 0)
  inj' := aCoordinateEmbedding_injective


-- @@ L131-134 verbatim
/-- The C-coordinate detector singled out by the paper's five-detector bound. Paper: §4.
-/
def cDetector : D :=
  (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0))


-- @@ L136-140 verbatim
/-- The finite A-detector image used by the five-detector set. Paper: §4.
-/
def aDetectorImage : Finset D := by
  classical
  exact Finset.univ.image aDetectorEmbedding


-- @@ L142-146 verbatim
/-- The explicit finite detector set for both raw split extensions. Paper: §4.
-/
def detectorFinset : Finset D := by
  classical
  exact insert cDetector aDetectorImage


-- @@ L148-155 verbatim
/-- The standard A chart vector is nonzero. Paper: §4. -/
lemma basisVector_zero_ne_zero :
    (PaperFiniteCharts.basisVector 0 : A) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  simp [PaperFiniteCharts.basisVector] at h0

/- The C detector is nonzero. Paper: §4. -/

-- @@ L156-164 verbatim
lemma diagonal_basisVector_zero_ne_zero :
    (PaperKernel.diagonal (PaperFiniteCharts.basisVector 0) : PaperKernel.C) ≠ 0 := by
  intro h
  apply basisVector_zero_ne_zero
  have hdelta := congrArg PaperKernel.delta h
  rw [PaperKernel.delta_diagonal] at hdelta
  exact hdelta

/- The C detector does not duplicate an A-coordinate detector. Paper: §4. -/

-- @@ L165-176 verbatim
lemma cDetector_not_mem_image :
    cDetector ∉ aDetectorImage := by
  classical
  intro hc
  rw [aDetectorImage] at hc
  rcases Finset.mem_image.mp hc with ⟨v, -, hv⟩
  have hsecond := congrArg Prod.snd hv
  apply diagonal_basisVector_zero_ne_zero
  simpa [cDetector, aDetectorEmbedding,
    PaperAChartDetectorMeasure.aCoordinateEmbedding] using hsecond.symm

/- Summation over the explicit detector set is the paper's five-detector sum. Paper: §4. -/

-- @@ L177-189 verbatim
lemma detectorFinset_sum_eq (f : D → ℝ) :
    (∑ d ∈ detectorFinset, f d) =
      (∑ v : SymplecticIndex,
        f (PaperAChartDetectorMeasure.aCoordinateEmbedding v
          (PaperFiniteCharts.basisVector 0))) + f cDetector := by
  classical
  rw [detectorFinset, Finset.sum_insert cDetector_not_mem_image,
    aDetectorImage, Finset.sum_image]
  · simp only [aDetectorEmbedding]
    abel
  · exact aDetectorEmbedding.injective.injOn

/- Spectral displacement energies are nonnegative. Paper: §4. -/

-- @@ L190-197 verbatim
lemma spectralDetectionEnergy_nonneg
    (μ : ProbabilityMeasure (DiscreteCharacterSpace PaperKernel.D))
    (d : D) :
    0 ≤ spectralDetectionEnergy μ d := by
  unfold spectralDetectionEnergy
  exact integral_nonneg (fun _ => sq_nonneg _)

/- The first concrete split extension has finite spectral detection. Paper: §4. -/

-- @@ L198-206 verbatim
theorem lambda_one_hasFiniteSpectralDetection :
    HasFiniteSpectralDetection PaperSpectralPropertyT.lambdaOneExtension
      detectorFinset (1 / 3 : ℝ) := by
  intro μ hinv
  have h := PaperSpectralDetectorBridge.lambda_one_full_spectral_detection μ hinv
  rw [detectorFinset_sum_eq]
  simpa [cDetector] using h

/- The second concrete split extension has finite spectral detection. Paper: §4. -/

-- @@ L207-216 verbatim
theorem lambda_two_hasFiniteSpectralDetection :
    HasFiniteSpectralDetection PaperSpectralPropertyT.lambdaTwoExtension
      detectorFinset (1 / 3 : ℝ) := by
  intro μ hinv
  have h := PaperSpectralDetectorBridge.lambda_two_full_spectral_detection μ hinv
  rw [detectorFinset_sum_eq]
  simpa [cDetector] using h

/- Package the proved detector set for the first split extension. Paper: §4.
-/

-- @@ L217-225 verbatim
/--
The `lambdaOneSpectralData` construction used in the Connes rigidity formalization.
-/
def lambdaOneSpectralData :
    PaperSpectralPropertyT.SpectralData paperThetaOneHom where
  J := detectorFinset
  c := 1 / 3
  c_pos := by norm_num
  detection := lambda_one_hasFiniteSpectralDetection


-- @@ L227-234 verbatim
/-- Package the proved detector set for the second split extension. Paper: §4.
-/
def lambdaTwoSpectralData :
    PaperSpectralPropertyT.SpectralData paperThetaTwoHom where
  J := detectorFinset
  c := 1 / 3
  c_pos := by norm_num
  detection := lambda_two_hasFiniteSpectralDetection


-- @@ L236-236 verbatim
end

-- @@ L237-237 verbatim
end PaperSpectralFiniteDetection

-- @@ L238-238 verbatim
end Connes
