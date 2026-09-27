/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import LeanPool.ConnesRigidity.Paper.Section4.SpectralDetector
public import LeanPool.ConnesRigidity.Paper.Section4.SpectralPropertyT


-- @@ L11-14 verbatim
/-!
Transport of Zhou's compact-dual detector estimate to the raw Pontryagin-dual
carrier used by the generic split-extension criterion. Paper: §4.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace Connes

-- @@ L19-19 verbatim
namespace PaperSpectralDetectorBridge


-- @@ L21-21 verbatim
open MeasureTheory

-- @@ L22-22 verbatim
open Construction

-- @@ L23-23 verbatim
open Construction.PaperKernel

-- @@ L24-24 verbatim
open PaperSpectralPropertyT

-- @@ L25-25 verbatim
open PaperSpectralDetector

-- @@ L26-26 verbatim
open PaperChartMeasure

-- @@ L27-27 verbatim
open PaperChartDetectorMeasure

-- @@ L28-28 verbatim
open PaperAChartDetectorMeasure


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-35 verbatim
/--
The `Raw` construction used in the Connes rigidity formalization.
-/
abbrev Raw := DiscreteCharacterSpace PaperKernel.D

-- @@ L36-39 verbatim
/--
The `Paper` construction used in the Connes rigidity formalization.
-/
abbrev Paper := PaperSpectralDetector.CharacterSpace


-- @@ L41-52 verbatim
private theorem paperDualCharacterAction_eq_of_apply_eq
    {H₁ H₂ : CountableDiscreteGroup}
    (action₁ : H₁ →* Multiplicative (AddAut PaperKernel.D)) (h₁ : H₁)
    (action₂ : H₂ →* Multiplicative (AddAut PaperKernel.D)) (h₂ : H₂)
    (h : action₁ h₁ = action₂ h₂) :
    paperDualCharacterAction action₁ h₁ =
      paperDualCharacterAction action₂ h₂ := by
  unfold paperDualCharacterAction dualCharacterEquivOfAction
  rw [h]

/- The raw and additive character carriers differ only by a type tag. Paper: §3.
-/

-- @@ L53-56 verbatim
/--
The `rawToPaper` construction used in the Connes rigidity formalization.
-/
def rawToPaper : Raw ≃ Paper := Additive.ofMul


-- @@ L58-64 verbatim
/-- The type-tag equivalence is measurable for the transported Borel models. Paper: §3. -/
theorem rawToPaper_measurable :
    Measurable (rawToPaper : Raw → Paper) := by
  change Measurable (fun x : Raw => x)
  exact measurable_id

/- The inverse type-tag equivalence is measurable. Paper: §3. -/

-- @@ L65-71 verbatim
theorem paperToRaw_measurable :
    Measurable (rawToPaper.symm : Paper → Raw) := by
  change Measurable (fun x : Paper => x)
  exact measurable_id

/- Push a raw probability measure into the paper-facing additive model. Paper: §3--4.
-/

-- @@ L72-79 verbatim
/--
The `paperMeasureOfRaw` construction used in the Connes rigidity formalization.
-/
def paperMeasureOfRaw (μ : ProbabilityMeasure Raw) :
    ProbabilityMeasure Paper :=
  μ.map rawToPaper

/- The two definitions of the dual action agree under the type-tag equivalence. Paper: §4. -/

-- @@ L80-106 verbatim
theorem raw_action_to_paper
    {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut PaperKernel.D))
    (h : H) (χ : Raw) :
    rawToPaper (dualCharacterAction action h χ) =
      paperDualCharacterAction action h (rawToPaper χ) := by
  apply Additive.ext
  apply PontryaginDual.ext
  intro x
  change χ (Multiplicative.ofAdd
      ((Multiplicative.toAdd (action h⁻¹)) (Multiplicative.toAdd x))) =
    (Additive.toMul (PaperDualAutomorphism.dualCharacterEquiv
      (Multiplicative.toAdd (action h)) (rawToPaper χ))) x
  have hdual :
      (Additive.toMul (PaperDualAutomorphism.dualCharacterEquiv
        (Multiplicative.toAdd (action h)) (rawToPaper χ))) x =
        χ (Multiplicative.ofAdd
          ((Multiplicative.toAdd (action h)).symm
            (Multiplicative.toAdd x))) := by
    simpa [rawToPaper] using PaperDualAutomorphism.dualCharacterEquiv_apply
      (Multiplicative.toAdd (action h)) (rawToPaper χ)
        (Multiplicative.toAdd x)
  rw [hdual]
  congr 2
  simp

/- Raw invariance transports to paper invariance. Paper: §4. -/

-- @@ L107-151 verbatim
theorem paper_measure_invariant_of_raw
    {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut PaperKernel.D))
    (μ : ProbabilityMeasure Raw)
    (hinv : IsInvariantSpectralMeasure action μ) :
    IsInvariantPaperSpectralMeasure action (paperMeasureOfRaw μ) := by
  intro h
  change Measure.map (paperDualCharacterAction action h)
      ((μ : Measure Raw).map rawToPaper) =
    (μ : Measure Raw).map rawToPaper
  change Measure.map
      (PaperDualAutomorphism.dualCharacterEquiv
        (Multiplicative.toAdd (action h)))
      ((μ : Measure Raw).map rawToPaper) =
    (μ : Measure Raw).map rawToPaper
  have hmap := congrArg
      (fun ν : Measure Raw => ν.map rawToPaper) (hinv h)
  rw [Measure.map_map rawToPaper_measurable
    (measurable_dualCharacterAction action h)] at hmap
  have hcomp :
      (fun χ : Raw => rawToPaper (dualCharacterAction action h χ)) =
        (fun χ : Raw => PaperDualAutomorphism.dualCharacterEquiv
          (Multiplicative.toAdd (action h)) (rawToPaper χ)) := by
    funext χ
    exact raw_action_to_paper action h χ
  calc
    Measure.map
        (PaperDualAutomorphism.dualCharacterEquiv
          (Multiplicative.toAdd (action h)))
        ((μ : Measure Raw).map rawToPaper) =
      Measure.map (fun χ : Raw => PaperDualAutomorphism.dualCharacterEquiv
        (Multiplicative.toAdd (action h)) (rawToPaper χ))
        (μ : Measure Raw) := by
          simpa [Function.comp_def] using
            (Measure.map_map
              (PaperDualAutomorphism.dualCharacterEquiv_continuous
                (Multiplicative.toAdd (action h))).measurable
              rawToPaper_measurable (μ := (μ : Measure Raw)))
    _ = Measure.map (fun χ : Raw => rawToPaper
        (dualCharacterAction action h χ)) (μ : Measure Raw) := by
          rw [← hcomp]
    _ = (μ : Measure Raw).map rawToPaper := by
          simpa [Function.comp_def] using hmap

/- The paper energy and the generic raw energy are the same integral. Paper: §4. -/

-- @@ L152-190 verbatim
theorem energy_transport
    (μ : ProbabilityMeasure Raw) (d : PaperKernel.D) :
    spectralEnergy (paperMeasureOfRaw μ) d =
      spectralDetectionEnergy μ d := by
  unfold spectralEnergy spectralDetectionEnergy paperMeasureOfRaw
  change (∫ χ : Paper,
      ‖((ZMod.toCircle (detectorValue χ d) : Circle) : ℂ) - 1‖ ^ 2
        ∂((μ : Measure Raw).map rawToPaper)) = _
  have hfm : AEStronglyMeasurable
      (fun χ : Paper =>
        ‖((ZMod.toCircle (detectorValue χ d) : Circle) : ℂ) - 1‖ ^ 2)
      ((μ : Measure Raw).map rawToPaper) := by
    have hpoint :
        (fun χ : Paper =>
          ‖((ZMod.toCircle (detectorValue χ d) : Circle) : ℂ) - 1‖ ^ 2) =
          (fun χ : Paper =>
            (4 : ℝ) * Set.indicator (linearDetector d)
              (fun _ => (1 : ℝ)) χ) := by
      funext χ
      exact detectorEnergy_eq_four_indicator χ d
    rw [hpoint]
    have hm : Measurable
        (fun χ : Paper =>
          (4 : ℝ) * Set.indicator (linearDetector d)
            (fun _ => (1 : ℝ)) χ) := by
      exact measurable_const.mul
        (measurable_const.indicator (measurableSet_linearDetector d))
    exact hm.aestronglyMeasurable
  rw [integral_map (μ := (μ : Measure Raw))
    (φ := (rawToPaper : Raw → Paper)) rawToPaper_measurable.aemeasurable hfm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun χ => by
    change ‖((ZMod.toCircle (detectorValue (rawToPaper χ) d) : Circle) : ℂ) - 1‖ ^ 2 =
      ‖((χ (Multiplicative.ofAdd d) : Circle) : ℂ) - 1‖ ^ 2
    congr 2
    simp [detectorValue, rawToPaper,
      BinaryPontryaginDual.characterLinear_circle])

/- The trivial atom is preserved under the raw/additive identification. Paper: §4. -/

-- @@ L191-212 verbatim
theorem trivial_atom_transport (μ : ProbabilityMeasure Raw) :
    trivialAtom (paperMeasureOfRaw μ) =
      spectralTrivialAtom μ := by
  unfold trivialAtom spectralTrivialAtom paperMeasureOfRaw
  have hpre : rawToPaper ⁻¹' ({0} : Set Paper) = ({1} : Set Raw) := by
    ext χ
    change rawToPaper χ = 0 ↔ χ = 1
    constructor
    · intro hχ
      apply rawToPaper.injective
      simpa [rawToPaper] using hχ
    · intro hχ
      subst χ
      rfl
  rw [measureReal_def, measureReal_def]
  change ENNReal.toReal (((μ : Measure Raw).map rawToPaper)
      ({0} : Set Paper)) =
    ENNReal.toReal ((μ : Measure Raw) ({1} : Set Raw))
  rw [Measure.map_apply rawToPaper_measurable measurableSet_zero, hpre]

/- Zhou's finite detector inequality on the raw carrier from the paper's
SL₃-invariant measure hypothesis. Paper: §4. -/

-- @@ L213-232 verbatim
theorem raw_full_spectral_detection_of_paper_sl3_invariance
    (μ : ProbabilityMeasure Raw)
    (hinv : IsInvariantPaperSL3SpectralMeasure (paperMeasureOfRaw μ)) :
    (1 / 3 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (∑ v : OpenAIPort.SymplecticIndex,
        spectralDetectionEnergy μ
          (aCoordinateEmbedding v (PaperFiniteCharts.basisVector 0))) +
      spectralDetectionEnergy μ
        (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0)) := by
  have hpaper := full_spectral_detection
    (paperMeasureOfRaw μ) hinv
  rw [trivial_atom_transport] at hpaper
  rw [Finset.sum_congr rfl (fun v _ =>
    energy_transport μ
      (aCoordinateEmbedding v (PaperFiniteCharts.basisVector 0)))] at hpaper
  rw [energy_transport μ
    (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0))] at hpaper
  exact hpaper

/- The full acting-group hypothesis implies the paper's detector hypothesis. Paper: §4. -/

-- @@ L233-249 verbatim
theorem raw_full_spectral_detection
    (μ : ProbabilityMeasure Raw)
    (hinv : IsInvariantSpectralMeasure
      PaperChartDetectorMeasure.paperThetaOneAddAction μ) :
    (1 / 3 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (∑ v : OpenAIPort.SymplecticIndex,
        spectralDetectionEnergy μ
          (aCoordinateEmbedding v (PaperFiniteCharts.basisVector 0))) +
      spectralDetectionEnergy μ
        (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0)) := by
  exact raw_full_spectral_detection_of_paper_sl3_invariance μ
    (IsInvariantPaperSL3SpectralMeasure.of_full
      (paperMeasureOfRaw μ)
      (paper_measure_invariant_of_raw
        PaperChartDetectorMeasure.paperThetaOneAddAction μ hinv))

/- The lambda₁ raw action supplies exactly the SL₃ invariance used by §4. Paper: §4. -/

-- @@ L250-278 verbatim
theorem lambda_one_paper_sl3_invariance
    (μ : ProbabilityMeasure Raw)
    (hinv : IsInvariantSpectralMeasure
      PaperSpectralPropertyT.lambdaOneExtension.action μ) :
    IsInvariantPaperSL3SpectralMeasure (paperMeasureOfRaw μ) := by
  intro g
  have hfull := paper_measure_invariant_of_raw
    (action := PaperSpectralPropertyT.lambdaOneExtension.action)
    μ hinv
  have hact :
      PaperSpectralPropertyT.lambdaOneExtension.action g =
        paperThetaOneAddAction
          (⟨g, (1 : PaperKernel.Q)⟩ : Construction.H) := by
    apply Multiplicative.ext
    apply AddEquiv.ext
    intro d
    rw [PaperSpectralPropertyT.lambdaOneExtension,
      PaperSplitExtensions.lambdaExtension_action,
      PaperPropertyT.sl3ToActingGroup_apply]
    exact (paperThetaOneAddAction_apply _ d).symm
  have hdual :
      paperDualCharacterAction
          PaperSpectralPropertyT.lambdaOneExtension.action g =
        paperDualCharacterAction paperThetaOneAddAction
          (⟨g, (1 : PaperKernel.Q)⟩ : Construction.H) := by
    exact paperDualCharacterAction_eq_of_apply_eq _ _ _ _ hact
  simpa only [hdual] using hfull g

/- The two paper actions agree on the SL₃ restriction used by the detector. Paper: §4. -/

-- @@ L279-294 verbatim
theorem paper_theta_two_sl3_addAction_eq (g : SpecialLinear.SL3) :
    paperThetaTwoAddAction (⟨g, (1 : PaperKernel.Q)⟩ : Construction.H) =
      paperThetaOneAddAction (⟨g, (1 : PaperKernel.Q)⟩ : Construction.H) := by
  apply Multiplicative.ext
  apply AddEquiv.ext
  intro d
  change PaperKernel.paperThetaTwoLinearHom (g, (1 : PaperKernel.Q)) d =
    PaperKernel.paperThetaOneLinearHom (g, (1 : PaperKernel.Q)) d
  simpa [PaperKernel.paperThetaOneLinearHom,
    PaperKernel.paperThetaOneLinear,
    PaperKernel.sl3CActionEquiv,
    PaperKernel.paperThetaTwoLinearHom,
    PaperKernel.paperThetaTwoLinearEquiv] using
    PaperKernel.thetaTwoLinearMap_sl3 g d

/- The lambda₂ raw action supplies the same SL₃ detector invariance. Paper: §4. -/

-- @@ L295-333 verbatim
theorem lambda_two_paper_sl3_invariance
    (μ : ProbabilityMeasure Raw)
    (hinv : IsInvariantSpectralMeasure
      PaperSpectralPropertyT.lambdaTwoExtension.action μ) :
    IsInvariantPaperSL3SpectralMeasure (paperMeasureOfRaw μ) := by
  intro g
  have hfull := paper_measure_invariant_of_raw
    (action := PaperSpectralPropertyT.lambdaTwoExtension.action)
    μ hinv
  have hact :
      PaperSpectralPropertyT.lambdaTwoExtension.action g =
        paperThetaTwoAddAction
          (⟨g, (1 : PaperKernel.Q)⟩ : Construction.H) := by
    apply Multiplicative.ext
    apply AddEquiv.ext
    intro d
    rw [PaperSpectralPropertyT.lambdaTwoExtension,
      PaperSplitExtensions.lambdaExtension_action,
      PaperPropertyT.sl3ToActingGroup_apply]
    exact (paperThetaTwoAddAction_apply _ d).symm
  have htwo := hfull g
  have hdualTwo :
      paperDualCharacterAction
          PaperSpectralPropertyT.lambdaTwoExtension.action g =
        paperDualCharacterAction paperThetaTwoAddAction
          (⟨g, (1 : PaperKernel.Q)⟩ : Construction.H) := by
    exact paperDualCharacterAction_eq_of_apply_eq _ _ _ _ hact
  rw [hdualTwo] at htwo
  have hdualOne :
      paperDualCharacterAction paperThetaTwoAddAction
          (⟨g, (1 : PaperKernel.Q)⟩ : Construction.H) =
        paperDualCharacterAction paperThetaOneAddAction
          (⟨g, (1 : PaperKernel.Q)⟩ : Construction.H) := by
    exact paperDualCharacterAction_eq_of_apply_eq _ _ _ _
      (paper_theta_two_sl3_addAction_eq g)
  rw [hdualOne] at htwo
  exact htwo

/- The lambda₁ raw spectral measure obeys Zhou's five-detector estimate. Paper: §4. -/

-- @@ L334-347 verbatim
theorem lambda_one_full_spectral_detection
    (μ : ProbabilityMeasure Raw)
    (hinv : IsInvariantSpectralMeasure
      PaperSpectralPropertyT.lambdaOneExtension.action μ) :
    (1 / 3 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (∑ v : OpenAIPort.SymplecticIndex,
        spectralDetectionEnergy μ
          (aCoordinateEmbedding v (PaperFiniteCharts.basisVector 0))) +
      spectralDetectionEnergy μ
        (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0)) := by
  exact raw_full_spectral_detection_of_paper_sl3_invariance μ
    (lambda_one_paper_sl3_invariance μ hinv)

/- The lambda₂ raw spectral measure obeys the same SL₃ detector estimate. Paper: §4. -/

-- @@ L348-359 verbatim
theorem lambda_two_full_spectral_detection
    (μ : ProbabilityMeasure Raw)
    (hinv : IsInvariantSpectralMeasure
      PaperSpectralPropertyT.lambdaTwoExtension.action μ) :
    (1 / 3 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (∑ v : OpenAIPort.SymplecticIndex,
        spectralDetectionEnergy μ
          (aCoordinateEmbedding v (PaperFiniteCharts.basisVector 0))) +
      spectralDetectionEnergy μ
        (0, PaperKernel.diagonal (PaperFiniteCharts.basisVector 0)) := by
  exact raw_full_spectral_detection_of_paper_sl3_invariance μ
    (lambda_two_paper_sl3_invariance μ hinv)


-- @@ L361-361 verbatim
end

-- @@ L362-362 verbatim
end PaperSpectralDetectorBridge

-- @@ L363-363 verbatim
end Connes
