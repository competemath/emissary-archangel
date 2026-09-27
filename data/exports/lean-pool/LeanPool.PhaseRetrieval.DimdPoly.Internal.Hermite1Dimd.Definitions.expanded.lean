/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.Definitions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Combinatorics.Matroid.Init


-- @@ L12-12 verbatim
/-! # Definitions -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
open Complex MeasureTheory Real Finset

-- @@ L18-18 verbatim
open scoped BigOperators ComplexConjugate Topology


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace Hermite1DimdLEAN


-- @@ L24-25 verbatim
/-- `CSpace`: C Space. -/
abbrev CSpace (d : ℕ) := Fin d → ℂ

-- @@ L26-27 verbatim
/-- `MultiIndex`: Multi Index. -/
abbrev MultiIndex (d : ℕ) := Fin d → ℕ

-- @@ L28-29 verbatim
/-- `T`: T. -/
abbrev T : ℝ := HermiteLEAN.T


-- @@ L31-31 verbatim
lemma T_pos : 0 < T := HermiteLEAN.T_pos


-- @@ L33-33 verbatim
instance : Fact (0 < T) := ⟨T_pos⟩


-- @@ L35-36 verbatim
/-- `Circle`: Circle. -/
abbrev Circle := AddCircle T


-- @@ L38-40 verbatim
/-- `gaussianDensity`: gaussian Density. -/
def gaussianDensity (d : ℕ) (z : CSpace d) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-(∑ q : Fin d, ‖z q‖ ^ 2))


-- @@ L42-44 verbatim
/-- `gaussianMeasure`: gaussian Measure. -/
def gaussianMeasure (d : ℕ) : Measure (CSpace d) :=
  volume.withDensity fun z => ENNReal.ofReal (gaussianDensity d z)


-- @@ L46-52 verbatim
/-- `oneDimPhi`: one Dim Phi. -/
noncomputable def oneDimPhi (k n : ℕ) : ℂ → ℂ := fun z =>
  ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
    Finset.sum (Finset.range (min k n + 1)) (fun j =>
      ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
        z ^ (n - j) * (star z) ^ (k - j))


-- @@ L54-56 verbatim
/-- `PhiKappaAlpha`: Phi Kappa Alpha. -/
def PhiKappaAlpha {d : ℕ} (κ α : MultiIndex d) : CSpace d → ℂ :=
  fun z => ∏ q : Fin d, oneDimPhi (κ q) (α q) (z q)


-- @@ L58-60 verbatim
/-- `nuKappa`: nu Kappa. -/
def nuKappa {d : ℕ} (κ : MultiIndex d) : CSpace d → ℂ :=
  PhiKappaAlpha κ 0


-- @@ L62-63 verbatim
/-- `rho`: rho. -/
def rho (a u : ℂ) : ℝ := |‖a + u‖ - ‖a‖|


-- @@ L65-67 verbatim
/-- `gaussianL2NormSq`: gaussian L2 Norm Sq. -/
def gaussianL2NormSq {d : ℕ} {α : Type*} [Norm α] (F : CSpace d → α) : ℝ :=
  ∫ z, ‖F z‖ ^ 2 ∂ gaussianMeasure d


-- @@ L69-71 verbatim
/-- `gaussianL2Norm`: gaussian L2 Norm. -/
def gaussianL2Norm {d : ℕ} {α : Type*} [Norm α] (F : CSpace d → α) : ℝ :=
  Real.sqrt (gaussianL2NormSq F)


-- @@ L73-75 verbatim
/-- `gaussianInner`: gaussian Inner. -/
def gaussianInner {d : ℕ} (F G : CSpace d → ℂ) : ℂ :=
  ∫ z, F z * conj (G z) ∂ gaussianMeasure d


-- @@ L77-79 verbatim
/-- `circleL2NormSq`: circle L2 Norm Sq. -/
def circleL2NormSq {α : Type*} [Norm α] (F : Circle → α) : ℝ :=
  ∫ t, ‖F t‖ ^ 2 ∂ AddCircle.haarAddCircle


-- @@ L81-83 verbatim
/-- `circleL2Norm`: circle L2 Norm. -/
def circleL2Norm {α : Type*} [Norm α] (F : Circle → α) : ℝ :=
  Real.sqrt (circleL2NormSq F)


-- @@ L85-88 verbatim
/-- `FiniteHermiteSum`: Finite Hermite Sum. -/
structure FiniteHermiteSum (d : ℕ) where
  /-- `coeff`: coeff. -/
  coeff : MultiIndex d →₀ ℂ


-- @@ L90-90 verbatim
namespace FiniteHermiteSum


-- @@ L92-94 verbatim
/-- `support`: support. -/
def support {d : ℕ} (G : FiniteHermiteSum d) : Finset (MultiIndex d) :=
  G.coeff.support


-- @@ L96-96 verbatim
end FiniteHermiteSum


-- @@ L98-100 verbatim
/-- `evalHermiteSum`: eval Hermite Sum. -/
def evalHermiteSum {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : CSpace d → ℂ :=
  fun z => Finset.sum G.support fun α => G.coeff α * PhiKappaAlpha κ α z


-- @@ L102-104 verbatim
/-- `hermiteInner`: hermite Inner. -/
def hermiteInner {d : ℕ} (κ : MultiIndex d) (G H : FiniteHermiteSum d) : ℂ :=
  gaussianInner (evalHermiteSum κ G) (evalHermiteSum κ H)


-- @@ L106-108 verbatim
/-- `hermiteInnerNu`: hermite Inner Nu. -/
def hermiteInnerNu {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℂ :=
  gaussianInner (evalHermiteSum κ G) (nuKappa κ)


-- @@ L110-112 verbatim
/-- `hermiteNormSq`: hermite Norm Sq. -/
def hermiteNormSq {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (evalHermiteSum κ G)


-- @@ L114-116 verbatim
/-- `hermiteNorm`: hermite Norm. -/
def hermiteNorm {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (evalHermiteSum κ G)


-- @@ L118-120 verbatim
/-- `defectFunction`: defect Function. -/
def defectFunction {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : CSpace d → ℝ :=
  fun z => rho (nuKappa κ z) (evalHermiteSum κ G z)


-- @@ L122-124 verbatim
/-- `defectNormSq`: defect Norm Sq. -/
def defectNormSq {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (defectFunction κ G)


-- @@ L126-128 verbatim
/-- `defectNorm`: defect Norm. -/
def defectNorm {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (defectFunction κ G)


-- @@ L130-132 verbatim
/-- `totalDegree`: total Degree. -/
def totalDegree {d : ℕ} (α : MultiIndex d) : ℕ :=
  ∑ q : Fin d, α q


-- @@ L134-136 verbatim
/-- `blockIndexMulti`: block Index Multi. -/
def blockIndexMulti {d : ℕ} (α : MultiIndex d) : MultiIndex d :=
  fun q => HermiteLEAN.blockIndex (α q)


-- @@ L138-147 verbatim
/-- `totalDegreePiece`: total Degree Piece. -/
def totalDegreePiece {d : ℕ} (n : ℕ) (G : FiniteHermiteSum d) : FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (G.support.filter fun α => totalDegree α = n)
    (fun α => if totalDegree α = n then G.coeff α else 0) ?_⟩
  intro α hα
  have hdeg : totalDegree α = n := by
    simp_all
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hdeg] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hdeg⟩


-- @@ L149-151 verbatim
/-- `productAnnulus`: product Annulus. -/
def productAnnulus {d : ℕ} (j : MultiIndex d) : Set (CSpace d) :=
  { z | ∀ q, (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1 }


-- @@ L153-157 verbatim
/-- `indicatorMul`: the indicator of `s` times `f`, valued in `ℂ`. -/
def indicatorMul {α : Type*} (s : Set α) (f : α → ℂ) : α → ℂ :=
  by
    classical
    exact fun x => if x ∈ s then f x else 0


-- @@ L159-163 verbatim
/-- `annulusInner`: annulus Inner. -/
def annulusInner {d : ℕ} (j : MultiIndex d) (F G : CSpace d → ℂ) : ℂ :=
  by
    classical
    exact ∫ z, if z ∈ productAnnulus j then F z * conj (G z) else 0 ∂ gaussianMeasure d


-- @@ L165-169 verbatim
/-- `annulusMass`: annulus Mass. -/
def annulusMass {d : ℕ} (j : MultiIndex d) (F : CSpace d → ℂ) : ℝ :=
  by
    classical
    exact ∫ z, if z ∈ productAnnulus j then ‖F z‖ ^ 2 else 0 ∂ gaussianMeasure d


-- @@ L171-178 verbatim
/-- `defectAnnulusMass`: defect Annulus Mass. -/
def defectAnnulusMass {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d)
    (F : CSpace d → ℂ) : ℝ :=
  by
    classical
    exact
      ∫ z, if z ∈ productAnnulus j then rho (nuKappa κ z) (F z) ^ 2 else 0
        ∂ gaussianMeasure d


-- @@ L180-182 verbatim
/-- `squareBlock`: square Block. -/
def squareBlock {d : ℕ} (ℓ : MultiIndex d) : Set (MultiIndex d) :=
  { α | ∀ q, α q ∈ HermiteLEAN.squareBlock (ℓ q) }


-- @@ L184-186 verbatim
/-- `blockDistance`: block Distance. -/
def blockDistance {d : ℕ} (j ℓ : MultiIndex d) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup fun q => Nat.dist (j q) (ℓ q)


-- @@ L188-197 verbatim
/-- `blockPart`: block Part. -/
def blockPart {d : ℕ} (ℓ : MultiIndex d) (G : FiniteHermiteSum d) : FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (G.support.filter fun α => α ∈ squareBlock ℓ)
    (fun α => if α ∈ squareBlock ℓ then G.coeff α else 0) ?_⟩
  intro α hα
  have hblock : α ∈ squareBlock ℓ := by
    simp_all
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hblock] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hblock⟩


-- @@ L199-202 verbatim
/-- `localCoeffSet`: local Coeff Set. -/
def localCoeffSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Finset (MultiIndex d) :=
  G.support.filter fun α => blockDistance j (blockIndexMulti α) ≤ M


-- @@ L204-207 verbatim
/-- `farCoeffSet`: far Coeff Set. -/
def farCoeffSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Finset (MultiIndex d) :=
  G.support.filter fun α => M < blockDistance j (blockIndexMulti α)


-- @@ L209-219 verbatim
/-- `localPart`: local Part. -/
def localPart {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (localCoeffSet j M G)
    (fun α => if blockDistance j (blockIndexMulti α) ≤ M then G.coeff α else 0) ?_⟩
  intro α hα
  have hlocal : blockDistance j (blockIndexMulti α) ≤ M := by
    simp_all
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hlocal] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hlocal⟩


-- @@ L221-231 verbatim
/-- `remainderPart`: remainder Part. -/
def remainderPart {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (farCoeffSet j M G)
    (fun α => if M < blockDistance j (blockIndexMulti α) then G.coeff α else 0) ?_⟩
  intro α hα
  have hfar : M < blockDistance j (blockIndexMulti α) := by
    simp_all
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hfar] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hfar⟩


-- @@ L233-235 verbatim
/-- `localDegreeSet`: local Degree Set. -/
def localDegreeSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) : Finset ℕ :=
  (localCoeffSet j M G).image totalDegree


-- @@ L237-240 verbatim
/-- `localDegreePiece`: local Degree Piece. -/
def localDegreePiece {d : ℕ} (j : MultiIndex d) (M n : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d :=
  totalDegreePiece n (localPart j M G)


-- @@ L242-244 verbatim
/-- `degreeIntervalLower`: degree Interval Lower. -/
def degreeIntervalLower {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  ∑ q, (max (j q) M - M) ^ 2


-- @@ L246-248 verbatim
/-- `degreeIntervalUpper`: degree Interval Upper. -/
def degreeIntervalUpper {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  ∑ q, ((j q + M + 1) ^ 2 - 1)


-- @@ L250-252 verbatim
/-- `degreeWidth`: degree Width. -/
def degreeWidth {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  degreeIntervalUpper j M - degreeIntervalLower j M + 1


-- @@ L254-256 verbatim
/-- `annulusRadius`: annulus Radius. -/
def annulusRadius {d : ℕ} (j : MultiIndex d) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup fun q => j q


-- @@ L258-259 verbatim
/-- `degreeThreshold`: degree Threshold. -/
def degreeThreshold (d M : ℕ) : ℕ := M + 120 * d * (2 * M + 1)


-- @@ L261-263 verbatim
/-- `productAnnulusConstant`: product Annulus Constant. -/
def productAnnulusConstant (d M : ℕ) : ℝ :=
  12 * Real.sqrt d * ((degreeThreshold d M + M : ℕ) : ℝ)


-- @@ L265-267 verbatim
/-- `productAnnulusConstantSq`: product Annulus Constant Sq. -/
def productAnnulusConstantSq (d M : ℕ) : ℝ :=
  144 * d * ((degreeThreshold d M + M : ℕ) : ℝ) ^ 2


-- @@ L269-271 verbatim
/-- `prodLocalizationConstant`: prod Localization Constant. -/
def prodLocalizationConstant {d : ℕ} (κ : MultiIndex d) : ℝ :=
  ∏ q : Fin d, ((κ q + 1 : ℕ) : ℝ)


-- @@ L273-275 verbatim
/-- `prodLocalizationDecay`: prod Localization Decay. -/
def prodLocalizationDecay {d : ℕ} (κ : MultiIndex d) : ℝ :=
  (∏ q : Fin d, ((κ q + 1 : ℕ) : ℝ))⁻¹


-- @@ L277-279 verbatim
/-- `prodLocalizationShift`: prod Localization Shift. -/
def prodLocalizationShift {d : ℕ} (κ : MultiIndex d) : ℝ :=
  ∑ q : Fin d, ((κ q + 4 : ℕ) : ℝ)


-- @@ L281-283 verbatim
/-- `shellCardinality`: shell Cardinality. -/
def shellCardinality (d r : ℕ) : ℕ :=
  (2 * r + 1) ^ d - (2 * r - 1) ^ d


-- @@ L285-294 verbatim
/-- `localizationLeakageCoefficient`: localization Leakage Coefficient. -/
def localizationLeakageCoefficient (C c B : ℝ) (d M : ℕ) : ℝ :=
  C *
    ∑' r : ℕ,
      if M + 1 ≤ r then
        (shellCardinality d r : ℝ) *
          Real.exp
            (-(c) *
              max ((r : ℝ) - B) 0 ^ 2)
      else 0


-- @@ L296-305 verbatim
/-- `leakageCoefficient`: leakage Coefficient. -/
def leakageCoefficient {d : ℕ} (κ : MultiIndex d) (M : ℕ) : ℝ :=
  prodLocalizationConstant κ *
    ∑' r : ℕ,
      if M + 1 ≤ r then
        (shellCardinality d r : ℝ) *
          Real.exp
            (-(prodLocalizationDecay κ) *
              max ((r : ℝ) - prodLocalizationShift κ) 0 ^ 2)
      else 0


-- @@ L307-309 verbatim
/-- `absorptionPredicate`: absorption Predicate. -/
def absorptionPredicate {d : ℕ} (κ : MultiIndex d) (M : ℕ) : Prop :=
  (4 * productAnnulusConstantSq d M + 2) * leakageCoefficient κ M < 1 / 2


-- @@ L311-314 verbatim
/-- `coercivityConstant`: coercivity Constant. -/
def coercivityConstant {d : ℕ} (κ : MultiIndex d) (M : ℕ) : ℝ :=
  2 * productAnnulusConstant d M /
    Real.sqrt (1 - (4 * productAnnulusConstantSq d M + 2) * leakageCoefficient κ M)


-- @@ L316-317 verbatim
/-- `reductionDelta`: reduction Delta. -/
def reductionDelta (M : ℝ) : ℝ := 1 / (M + 1)

-- @@ L318-319 verbatim
/-- `reductionMtilde`: reduction Mtilde. -/
def reductionMtilde (M : ℝ) : ℝ := 5 * M + 3


-- @@ L321-324 verbatim
/-- `phaseAdjustedDifference`: phase Adjusted Difference. -/
def phaseAdjustedDifference {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) :
    CSpace d → ℂ :=
  fun z => w * (nuKappa κ z + evalHermiteSum κ G z) - nuKappa κ z


-- @@ L326-328 verbatim
/-- `phaseAdjustedNormSq`: phase Adjusted Norm Sq. -/
def phaseAdjustedNormSq {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (phaseAdjustedDifference κ w G)


-- @@ L330-332 verbatim
/-- `phaseAdjustedNorm`: phase Adjusted Norm. -/
def phaseAdjustedNorm {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (phaseAdjustedDifference κ w G)


-- @@ L334-336 verbatim
/-- `positiveFrequencyPolynomial`: positive Frequency Polynomial. -/
def positiveFrequencyPolynomial (E : Finset ℕ) (b : ℕ → ℂ) : Circle → ℂ :=
  fun t => Finset.sum E fun n => b n * fourier (n : ℤ) t


-- @@ L338-340 verbatim
/-- `bandLimitedPolynomial`: band Limited Polynomial. -/
def bandLimitedPolynomial (N L : ℕ) (c : Fin L → ℂ) : Circle → ℂ :=
  fun t => ∑ m : Fin L, c m * fourier ((N + m.1 : ℕ) : ℤ) t


-- @@ L342-344 verbatim
/-- `HasPositiveFrequencySupport`: Has Positive Frequency Support. -/
def HasPositiveFrequencySupport (P : Circle → ℂ) (E : Finset ℕ) : Prop :=
  ∃ b : ℕ → ℂ, P = positiveFrequencyPolynomial E b


-- @@ L346-348 verbatim
/-- `HasBandlimitedSupport`: Has Bandlimited Support. -/
def HasBandlimitedSupport (P : Circle → ℂ) (N L : ℕ) : Prop :=
  ∃ c : Fin L → ℂ, P = bandLimitedPolynomial N L c


-- @@ L350-350 verbatim
end Hermite1DimdLEAN
