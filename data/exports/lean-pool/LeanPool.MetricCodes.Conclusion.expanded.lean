/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import LeanPool.MetricCodes.SpectralDecomposition


-- @@ L10-14 verbatim
/-!
# Binary and spherical code bounds

The unconditional characteristic-minor argument and the final headline theorems.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
noncomputable section MetricCodesNoncomputable


-- @@ L20-20 verbatim
namespace MetricCodes


-- @@ L22-22 verbatim
namespace Spherical


-- @@ L24-24 verbatim
section



-- @@ L27-27 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L29-29 verbatim
namespace HigherYoungAllRankActualProjectedAxisCompletion


-- @@ L31-31 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L32-32 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L33-33 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward

-- @@ L34-34 verbatim
open HigherHarmonicYoung.AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor

-- @@ L35-35 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxProjectedAxisWitness

-- @@ L36-36 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector

-- @@ L37-37 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L38-38 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L39-39 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan

-- @@ L40-40 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L41-41 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector

-- @@ L42-42 verbatim
open MetricCodes.Spherical.HigherHierarchy

-- @@ L43-43 verbatim
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency

-- @@ L44-44 verbatim
open MetricCodes.Spherical.HigherProjectionInstantiation

-- @@ L45-45 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L46-46 verbatim
open MetricCodes.Spherical.HigherYoungActualGraphAssembly

-- @@ L47-47 verbatim
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation

-- @@ L48-48 verbatim
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly

-- @@ L49-49 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange

-- @@ L50-50 verbatim
open MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency


-- @@ L52-91 verbatim
theorem fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
    (hrecurrence : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ (low high : BoxIndex (r + 1) m)
        (row : Fin (r + 2))
        (_ : boxSignature (m := m) a (n + 1) high =
          raiseWeight (boxSignature (m := m) a (n + 1) low) row),
        CanonicalBoxAdjacentFischerRecurrence a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i)
          low high row) :
    FixedLevelHierarchyCodeBound := by
  classical
  apply fixedLevelHierarchyCodeBound_of_extraStrongStableProjectedAxis
  intro r m n a b hinterlacing hlast hnextra hstable
  cases n with
  | zero => omega
  | succ n =>
      have hnstrong : 2 * (r + 1) + 5 ≤ n + 1 := by omega
      let hgram := fun i => canonicalBoxPositiveFischerGram a b hstable i
      let fibre := canonicalBoxGelfandTsetlinFibre a b hstable hgram
      let o := boxAxis (n + 1) (by omega)
      refine ⟨o, fibre, ?_⟩
      intro target source h
      refine ⟨canonicalBoxProjectedAxisWitness a b hstable hgram o ?_
        target source h⟩
      intro low high row hrow
      exact canonicalBoxEdgeAxisDataOfPolynomialData a b hstable hgram
        low high row hrow
        (canonicalBoxForwardPolynomialData_of_recurrence
          a b hstable hgram low high row hrow
          (hrecurrence a b hinterlacing hlast hnextra hstable
            low high row hrow))
        (canonicalBoxReverseAxisRange_of_strongStable a b hstable hgram
          hnstrong low high row hrow)


-- @@ L93-118 verbatim
/-- The characteristic-minor identity for a box fibre: the compressed minor equals the inner-
product constant times the channel numerator polynomial. -/
def ActualBoxAxisCharacteristicMinor
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low : BoxIndex (r + 1) m) : Prop :=
  ∀ p q : HarmonicYoungSpace (n := n)
      (Weyl.flooredWeight b (n + 1)),
    gtAxisCompressedCharacteristicMinor
        (boxSignature (m := m) a (n + 1) low)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable low)
        (hgram low) p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1)
            (Weyl.flooredWeight b (n + 1)))


-- @@ L120-148 verbatim
/-- Agreement of the Cartan characteristic projector and the selected Clebsch range projector on
the canonical box-axis tensor image. -/
def ActualBoxSelectedAxisProjectorAgreement
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low : BoxIndex (r + 1) m) (row : Fin (r + 2)) : Prop :=
  ∀ p : HarmonicYoungSpace (n := n)
      (Weyl.flooredWeight b (n + 1)),
    allRankCartanCharacteristicProjector
        (boxSignature (m := m) a (n + 1) low) (row, true)
        (canonicalGelfandTsetlinAxisTensor
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1))
          (boxSignature_interlaces a b hstable low) (hgram low) p) =
      gtSelectedRowClebschRangeProjector
        (boxSignature (m := m) a (n + 1) low) row
        (canonicalGelfandTsetlinAxisTensor
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1))
          (boxSignature_interlaces a b hstable low) (hgram low) p)


-- @@ L150-176 verbatim
theorem fixedLevelHierarchyCodeBound_of_actualCharacteristicMinorAndProjector
    (hedges : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ (low high : BoxIndex (r + 1) m)
        (row : Fin (r + 2))
        (_ : boxSignature (m := m) a (n + 1) high =
          raiseWeight (boxSignature (m := m) a (n + 1) low) row),
        ActualBoxAxisCharacteristicMinor a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i) low ∧
        ActualBoxSelectedAxisProjectorAgreement a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i)
          low row) :
    FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
  intro r m n a b hinterlacing hlast hnextra hstable low high row hrow
  let hgram := fun i => canonicalBoxPositiveFischerGram a b hstable i
  obtain ⟨hminor, hselected⟩ :=
    hedges a b hinterlacing hlast hnextra hstable low high row hrow
  have hnstrong : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  exact canonicalBoxAdjacentFischerRecurrence_of_minor_of_strongStable
    a b hstable hgram low high row hrow hnstrong hminor hselected


-- @@ L178-209 verbatim
theorem fixedLevelHierarchyCodeBound_of_actualCharacteristicMinor
    (hminor : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ low : BoxIndex (r + 1) m,
        ActualBoxAxisCharacteristicMinor a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i) low) :
    FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_actualCharacteristicMinorAndProjector
  intro r m n a b hinterlacing hlast hn hstable low high row hrow
  refine ⟨hminor a b hinterlacing hlast hn hstable low, ?_⟩
  let lam := boxSignature (m := m) a (n + 1) low
  let mu := Weyl.flooredWeight b (n + 1)
  let h := boxSignature_interlaces a b hstable low
  let hgram := canonicalBoxPositiveFischerGram a b hstable low
  have hfinite : FiniteInterlacing (n + 1) lam mu := by
    constructor
    · exact (hstable
        ((Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)).symm low)).1
    · exact h
  have hdom : Antitone lam := h.antitone_ambient
  have hhigh : Antitone (raiseWeight lam row) := by
    rw [← hrow]
    exact (boxSignature_interlaces a b hstable high).antitone_ambient
  intro p
  exact allRankCartanCharacteristicProjector_canonicalAxis_eq_physicalClebsch
    lam mu h hgram hfinite hdom row hhigh hn p


-- @@ L211-211 verbatim
end HigherYoungAllRankActualProjectedAxisCompletion


-- @@ L213-213 verbatim
end


-- @@ L215-215 verbatim
namespace HigherHarmonicYoung


-- @@ L217-217 verbatim
section



-- @@ L220-220 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L222-222 verbatim
namespace AllRankGTTerminalNegativeProjectorVanishing


-- @@ L224-224 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L225-225 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L226-226 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector

-- @@ L227-227 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L228-228 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L229-229 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L230-230 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L231-231 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L232-232 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L233-233 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L234-234 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels

-- @@ L235-235 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity


-- @@ L237-298 verbatim
theorem allRankCartanCharacteristicProjector_last_false_eq_zero
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hzero : lam (Fin.last r) = 0)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n lam mu) :
    allRankCartanCharacteristicProjector (n := n)
        lam (Fin.last r, false) = 0 := by
  let P := allRankCartanCharacteristicProjector (n := n)
    lam (Fin.last r, false)
  let A := paddedOrthogonalTensorPieriChannel hn lam hdom
  have hle : (⨆ i : PaddedPieriChannel lam,
      LinearMap.range (A i).toLinearMap) ≤ LinearMap.ker P := by
    apply iSup_le
    intro i
    rintro _ ⟨q, rfl⟩
    change P (A i q) = 0
    cases i with
    | inl row =>
        change allRankCartanCharacteristicProjector lam
          (Fin.last r, false)
            ((paddedOrthogonalTensorPieriChannel hn lam hdom
              (Sum.inl row)).toLinearMap q) = 0
        have hraise := allRankCartanCharacteristicProjector_raise_channel
          lam mu hfinite (Fin.last r, false) row.val
          (paddedOrthogonalTensorPieriChannel hn lam hdom
            (Sum.inl row)).toLinearMap
          (paddedOrthogonalTensorPieriChannel_rotation_intertwine
            hn lam hdom (Sum.inl row)) q
        rw [ite_eq_right (by simp only [Prod.mk.injEq, Bool.false_eq_true, and_false,
          not_false_eq_true])] at hraise
        exact hraise
    | inr row =>
        have hsource : lam =
            raiseWeight (paddedPieriSource lam (Sum.inr row)) row.val :=
          (raiseWeight_loweredInternalYoungWeight
            lam row.val row.property.1).symm
        change allRankCartanCharacteristicProjector lam
          (Fin.last r, false)
            ((paddedOrthogonalTensorPieriChannel hn lam hdom
              (Sum.inr row)).toLinearMap q) = 0
        rw [allRankCartanCharacteristicProjector_lower_channel
          lam mu hfinite (Fin.last r, false) row.val
          (paddedPieriSource lam (Sum.inr row)) hsource
          (paddedOrthogonalTensorPieriChannel hn lam hdom
            (Sum.inr row)).toLinearMap
          (paddedOrthogonalTensorPieriChannel_rotation_intertwine
            hn lam hdom (Sum.inr row))]
        have hne : (Fin.last r, false) ≠ (row.val, false) := by
          intro heq
          have hrow := congrArg Prod.fst heq
          change Fin.last r = row.val at hrow
          have hpos := row.property.1
          rw [← hrow, hzero] at hpos
          omega
        simp only [hne, ↓reduceIte]
  rw [paddedOrthogonalTensorPieri_iSup_range_eq_top hn lam hdom hzero] at hle
  apply LinearMap.ext
  intro x
  have hx := hle (show x ∈ (⊤ : Submodule ℝ
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)) from trivial)
  exact hx


-- @@ L300-309 verbatim
theorem signedCharacteristicProjector_last_false_eq_zero
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hzero : lam (Fin.last r) = 0)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n lam mu) :
    signedCharacteristicProjector
      (HigherChannel.ambientShift n lam)
      (gtRelativeCasimir (n := n) lam) (Fin.last r, false) = 0 :=
  allRankCartanCharacteristicProjector_last_false_eq_zero
    hn lam hdom hzero mu hfinite


-- @@ L311-326 verbatim
theorem gtAxisCompressedSignedProjectorCoefficient_last_false_eq_zero
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdom : Antitone lam) (hzero : lam (Fin.last (r + 1)) = 0)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedSignedProjectorCoefficient
      lam mu h hgram p q (Fin.last (r + 1), false) = 0 := by
  unfold gtAxisCompressedSignedProjectorCoefficient
  rw [signedCharacteristicProjector_last_false_eq_zero
    hn lam hdom hzero mu hfinite]
  simp only [canonicalGelfandTsetlinAxisTensor_apply, EuclideanSpace.basisFun_apply,
    canonicalGelfandTsetlinFibre_apply, TensorProduct.tmul_smul, map_smul, LinearMap.zero_apply,
    smul_zero, inner_zero_right]


-- @@ L328-328 verbatim
end AllRankGTTerminalNegativeProjectorVanishing


-- @@ L330-330 verbatim
end


-- @@ L332-332 verbatim
section



-- @@ L335-335 verbatim
open scoped InnerProductSpace


-- @@ L337-337 verbatim
namespace AllRankGTAbsentWallCharacteristicFactor


-- @@ L339-339 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L340-340 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L341-341 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L342-342 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L343-343 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTerminalNegativeProjectorVanishing

-- @@ L344-344 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L345-345 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue


-- @@ L347-353 verbatim
theorem ambientShift_last_eq_wallShift_of_last_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hlast : lam (Fin.last (r + 1)) = 0) :
    ambientShift (n + 1) lam (Fin.last (r + 1)) =
      wallShift (n + 1) (r + 1) := by
  rw [ambientShift_last, hlast]
  norm_num


-- @@ L355-362 verbatim
theorem signedNode_last_false_eq_neg_wallShift
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hlast : lam (Fin.last (r + 1)) = 0) :
    signedNode (ambientShift (n + 1) lam)
        (Fin.last (r + 1), false) =
      -(wallShift (n + 1) (r + 1)) := by
  simp only [signedNode, Bool.false_eq_true, ↓reduceIte]
  rw [ambientShift_last_eq_wallShift_of_last_eq_zero lam hlast]


-- @@ L364-379 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_neg_wallShift
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (-(wallShift (n + 1) (r + 1))) =
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (-(wallShift (n + 1) (r + 1))) *
        gtAxisCompressedSignedProjectorCoefficient
          lam mu h hgram p q (Fin.last (r + 1), false) := by
  simpa only [signedNode_last_false_eq_neg_wallShift lam hlast] using
    gtAxisCompressedCharacteristicMinor_eval_signedNode lam mu h hgram hfinite p q (Fin.last (r
      + 1), false)


-- @@ L381-400 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_iff
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (-(wallShift (n + 1) (r + 1))) = 0 ↔
      gtAxisCompressedSignedProjectorCoefficient
        lam mu h hgram p q (Fin.last (r + 1), false) = 0 := by
  rw [gtAxisCompressedCharacteristicMinor_eval_neg_wallShift
    lam mu h hgram hfinite hlast p q, mul_eq_zero]
  have hderivative :
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
          (-(wallShift (n + 1) (r + 1))) ≠ 0 := by
    simpa only [ne_eq, signedNode_last_false_eq_neg_wallShift lam hlast] using
      (FiniteInterlacing.gtChannelCharacteristic_derivative_eval_ne_zero hfinite (Fin.last (r +
        1)) false)
  simp only [hderivative, false_or]


-- @@ L402-414 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hforbidden : gtAxisCompressedSignedProjectorCoefficient
      lam mu h hgram p q (Fin.last (r + 1), false) = 0) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0 :=
  (gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_iff
    lam mu h hgram hfinite hlast p q).2 hforbidden


-- @@ L416-428 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_of_last_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : lam (Fin.last (r + 1)) = 0)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0 := by
  apply gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero
    lam mu h hgram hfinite hlast p q
  exact gtAxisCompressedSignedProjectorCoefficient_last_false_eq_zero
    hfinite.1 lam mu h hgram h.antitone_ambient hlast hfinite p q


-- @@ L430-430 verbatim
end AllRankGTAbsentWallCharacteristicFactor


-- @@ L432-432 verbatim
end


-- @@ L434-434 verbatim
section



-- @@ L437-437 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L439-439 verbatim
namespace AllRankGTPhysicalInvalidRowProjectorVanishing


-- @@ L441-441 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L442-442 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L443-443 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation

-- @@ L444-444 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L445-445 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan

-- @@ L446-446 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedPieriPhysicalAxisOrthogonality

-- @@ L447-447 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L448-448 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L449-449 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTIllegalStabilizerIntertwiner

-- @@ L450-450 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing

-- @@ L451-451 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidRowCharacteristicMinorVanishing

-- @@ L452-452 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNoninterlacingTensorChannelAxisOrthogonality

-- @@ L453-453 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L454-454 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport

-- @@ L455-455 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality

-- @@ L456-456 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining

-- @@ L457-457 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy

-- @@ L458-458 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L459-459 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L460-460 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram

-- @@ L461-461 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L462-462 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L463-463 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality

-- @@ L464-464 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

-- @@ L465-465 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining

-- @@ L466-466 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels

-- @@ L467-467 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L468-468 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness

-- @@ L469-469 verbatim
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

-- @@ L470-470 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L472-484 verbatim
theorem interlaces_of_appendZeroWeight
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces (appendZeroWeight lam) (appendZeroWeight mu)) :
    Interlaces lam mu := by
  intro row
  constructor
  · simpa only [appendZeroWeight_castSucc] using (h row.castSucc).1
  · have hcast : row.castSucc.succ = row.succ.castSucc := by
      apply Fin.ext
      rfl
    have hrow := (h row.castSucc).2
    rw [hcast] at hrow
    simpa only [appendZeroWeight_castSucc] using hrow


-- @@ L486-515 verbatim
theorem pieri_crossGram_intertwines_of_skew
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (A : HarmonicYoungSpace (n := n + 1)
        (paddedPieriSource (appendZeroWeight lam) i) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)))
    (B : HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)))
    (R : HarmonicYoungSpace (n := n + 1)
        (paddedPieriSource (appendZeroWeight lam) i) →ₗ[ℝ]
      HarmonicYoungSpace (n := n + 1)
        (paddedPieriSource (appendZeroWeight lam) i))
    (T : HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)) →ₗ[ℝ]
      HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)))
    (S : (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)))
    (hR : R.adjoint = -R)
    (hS : S.adjoint = -S)
    (hA : A.comp R = S.comp A)
    (hB : B.comp T = S.comp B) :
    (A.adjoint.comp B).comp T = R.comp (A.adjoint.comp B) :=
  crossGram_intertwines_of_skew A B R T S hR hS hA hB


-- @@ L517-594 verbatim
theorem physicalPaddedPieriChannel_adjoint_canonicalAxis_eq_zero_of_not_interlaces
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdom : Antitone lam)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (hbad : ¬ Interlaces (paddedPieriSource (appendZeroWeight lam) i)
      (appendZeroWeight mu))
    (p : HarmonicYoungSpace (n := n) mu) :
    (physicalPaddedPieriChannel (n := n + 1) (by omega) lam
      (appendZeroWeight_antitone lam hdom) i).toLinearMap.adjoint
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  let hpadded := appendZeroWeight_antitone lam hdom
  let C := (paddedOrthogonalTensorPieriChannel
    (by omega : 2 * (r + 2) + 4 ≤ n + 1)
    (appendZeroWeight lam) hpadded i).toLinearMap
  let A := originalPaddedSelectedAxisTensor lam mu h hgram
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let W := appendZeroRowIsometryEquiv (n := n) (appendZeroWeight mu)
  let T := zeroRowTensorIsometryEquiv (n := n + 1) lam
  have hcross : C.adjoint.comp A = 0 := by
    apply illegalYoungStabilizerIntertwiner_eq_zero
      (paddedPieriSource (appendZeroWeight lam) i)
      (appendZeroWeight mu) (by omega)
      (paddedPieriSource_antitone (appendZeroWeight lam) i)
      (appendZeroWeight_antitone mu
        (interlaces_antitone_stabilizer h)) hbad
    intro a b
    apply pieri_crossGram_intertwines_of_skew lam mu i C A
      (youngAmbientRotation
        (paddedPieriSource (appendZeroWeight lam) i)
          a.castSucc b.castSucc)
      (youngAmbientRotation (appendZeroWeight (appendZeroWeight mu)) a b)
      (tensorAmbientRotation (appendZeroWeight lam)
        a.castSucc b.castSucc)
      (youngAmbientRotation_adjoint
        (paddedPieriSource (appendZeroWeight lam) i)
          a.castSucc b.castSucc)
      (tensorAmbientRotation_adjoint (appendZeroWeight lam)
        a.castSucc b.castSucc)
    · exact paddedOrthogonalTensorPieriChannel_rotation_intertwine
        (by omega) (appendZeroWeight lam) hpadded i
          a.castSucc b.castSucc
    · exact originalPaddedSelectedAxisTensor_rotation_intertwine
        lam mu h hgram a b
  have hz := LinearMap.congr_fun hcross (W (Z p))
  have hC : C.adjoint (T
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)) = 0 := by
    change C.adjoint
      (T (canonicalGelfandTsetlinAxisTensor lam mu h hgram
        (Z.symm (W.symm (W (Z p)))))) = 0 at hz
    simpa only [canonicalGelfandTsetlinAxisTensor_apply, EuclideanSpace.basisFun_apply,
      canonicalGelfandTsetlinFibre_apply, TensorProduct.tmul_smul, map_smul, smul_eq_zero,
      inv_eq_zero, LinearIsometryEquiv.symm_apply_apply] using hz
  apply ext_inner_left ℝ
  intro q
  rw [inner_zero_right, LinearMap.adjoint_inner_right]
  change ⟪T.symm (C q),
    canonicalGelfandTsetlinAxisTensor lam mu h hgram p⟫_ℝ = 0
  calc
    ⟪T.symm (C q),
      canonicalGelfandTsetlinAxisTensor lam mu h hgram p⟫_ℝ =
        ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
          T.symm (C q)⟫_ℝ :=
            real_inner_comm
              (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
              (T.symm (C q))
    _ = ⟪T (canonicalGelfandTsetlinAxisTensor lam mu h hgram p), C q⟫_ℝ := by
          rw [← T.inner_map_map,
            LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪C.adjoint
        (T (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)), q⟫_ℝ :=
          (LinearMap.adjoint_inner_left C q _).symm
    _ = 0 := by
      rw [hC, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _


-- @@ L596-629 verbatim
theorem canonicalAxis_mem_retainedPhysicalPieriSpan
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hdom : Antitone lam)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinAxisTensor lam mu h hgram p ∈
      ⨆ i : {j : PaddedPieriChannel (appendZeroWeight lam) //
        retainedPaddedPieriChannel lam j},
        LinearMap.range
          (physicalPaddedPieriChannel (n := n + 1) (by omega) lam
            (appendZeroWeight_antitone lam hdom) i.val).toLinearMap := by
  classical
  let hfamily : 2 * (r + 2) + 4 ≤ n + 1 := by omega
  let hpadded := appendZeroWeight_antitone lam hdom
  let A := physicalPaddedPieriChannel hfamily lam hpadded
  apply orthogonalCompleteBranch_mem_selected_iSup A
    (physicalPaddedPieriChannel_inner_eq_zero hfamily lam hpadded)
    (physicalPaddedPieriChannel_finrank hfamily lam hpadded)
    (retainedPaddedPieriChannel lam)
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
  intro i hnot q
  cases i with
  | inl row =>
      change ¬ row.val ≠ Fin.last (r + 2) at hnot
      have hlast : row.val = Fin.last (r + 2) := Classical.byContradiction hnot
      rcases row with ⟨row, hsource⟩
      dsimp at hlast
      subst row
      exact paddedOrthogonalTensorPieriChannel_appended_originalCanonicalAxis_orthogonal
        lam mu h hgram hpadded hsource hn p q
  | inr row =>
      exact (hnot trivial).elim


-- @@ L631-672 verbatim
theorem signedCharacteristicProjector_canonicalAxis_eq_zero_of_matching_noninterlacing
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (selected : Fin (r + 2) × Bool)
    (hbad : ∀ i : {j : PaddedPieriChannel (appendZeroWeight lam) //
        retainedPaddedPieriChannel lam j},
      retainedPaddedPieriSignedNode lam i = selected →
        ¬ Interlaces (retainedPaddedPieriPhysicalSource lam i) mu)
    (p : HarmonicYoungSpace (n := n) mu) :
    signedCharacteristicProjector (HigherChannel.ambientShift (n + 1) lam)
      (gtRelativeCasimir lam) selected
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  classical
  let hfamily : 2 * (r + 2) + 4 ≤ n + 1 := by omega
  let hpadded := appendZeroWeight_antitone lam hfinite.antitone_ambient
  let A := physicalPaddedPieriChannel hfamily lam hpadded
  change gtCharacteristicProjector lam selected
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0
  apply gtCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
    lam mu hfinite (retainedPaddedPieriSignedNode lam)
    (retainedPaddedPieriSignedNode_injective lam)
    (fun i => A i.val)
  · intro i j hij u v
    exact physicalPaddedPieriChannel_inner_eq_zero hfamily lam hpadded
      i.val j.val (fun heq => hij (Subtype.ext heq)) u v
  · intro i q
    exact transportedPaddedPieriChannel_eigen_of_retained
      hfamily lam hpadded i q
  · exact canonicalAxis_mem_retainedPhysicalPieriSpan
      lam mu h hgram hfinite.antitone_ambient hn p
  · intro i hi
    apply physicalPaddedPieriChannel_adjoint_canonicalAxis_eq_zero_of_not_interlaces
      lam mu h hgram hfinite.antitone_ambient hn i.val
    intro hsource
    apply hbad i hi
    apply interlaces_of_appendZeroWeight
      (retainedPaddedPieriPhysicalSource lam i) mu
    rw [← paddedPieriSource_retained_eq_appendZero lam i]
    exact hsource


-- @@ L674-703 verbatim
theorem retainedPhysicalSource_not_interlaces_of_invalid_negative
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j})
    (hi : retainedPaddedPieriSignedNode lam i = (row.castSucc, false)) :
    ¬ Interlaces (retainedPaddedPieriPhysicalSource lam i) mu := by
  have hwall : lam row.castSucc = mu row :=
    (not_interlaces_raiseWeight_iff_upperWall lam mu h row).mp hbad
  rcases i with ⟨(actual | actual), hretained⟩
  · have hsign := congrArg Prod.snd hi
    simp only [retainedPaddedPieriSignedNode, Bool.true_eq_false] at hsign
  · have hrow :
        actual.val.castPred (paddedPieriLowerRow_ne_last lam actual) =
          row.castSucc := congrArg Prod.fst hi
    change ¬ Interlaces
      (loweredInternalYoungWeight lam
        (actual.val.castPred (paddedPieriLowerRow_ne_last lam actual))) mu
    rw [hrow]
    apply not_interlaces_lowerAmbient_of_upperWall lam mu row hwall
    have hcast : actual.val = row.castSucc.castSucc := by
      calc
        actual.val =
            (actual.val.castPred
              (paddedPieriLowerRow_ne_last lam actual)).castSucc :=
                (Fin.castSucc_castPred _ _).symm
        _ = row.castSucc.castSucc := congrArg Fin.castSucc hrow
    simpa only [gt_iff_lt, hcast, appendZeroWeight_castSucc] using actual.property.1


-- @@ L705-725 verbatim
theorem retainedPhysicalSource_not_interlaces_of_invalid_positive
    {r : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (i : {j : PaddedPieriChannel (appendZeroWeight lam) //
      retainedPaddedPieriChannel lam j})
    (hi : retainedPaddedPieriSignedNode lam i = (row.succ, true)) :
    ¬ Interlaces (retainedPaddedPieriPhysicalSource lam i) mu := by
  have hwall : lam row.succ = mu row :=
    lowerWall_of_invalid_lower_stabilizer lam mu h row hbad
  rcases i with ⟨(actual | actual), hretained⟩
  · have hrow : actual.val.castPred hretained = row.succ :=
      congrArg Prod.fst hi
    change ¬ Interlaces
      (raiseWeight lam (actual.val.castPred hretained)) mu
    rw [hrow]
    exact not_interlaces_raiseAmbient_of_lowerWall lam mu row hwall
  · have hsign := congrArg Prod.snd hi
    simp only [retainedPaddedPieriSignedNode, Bool.false_eq_true] at hsign


-- @@ L727-743 verbatim
theorem signedCharacteristicProjector_canonicalAxis_invalid_negative_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p : HarmonicYoungSpace (n := n) mu) :
    signedCharacteristicProjector (HigherChannel.ambientShift (n + 1) lam)
      (gtRelativeCasimir lam) (row.castSucc, false)
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  apply signedCharacteristicProjector_canonicalAxis_eq_zero_of_matching_noninterlacing
    lam mu h hgram hfinite hn (row.castSucc, false) _ p
  intro i hi
  exact retainedPhysicalSource_not_interlaces_of_invalid_negative
    lam mu h row hbad i hi


-- @@ L745-762 verbatim
theorem signedCharacteristicProjector_canonicalAxis_invalid_positive_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p : HarmonicYoungSpace (n := n) mu) :
    signedCharacteristicProjector (HigherChannel.ambientShift (n + 1) lam)
      (gtRelativeCasimir lam) (row.succ, true)
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  apply signedCharacteristicProjector_canonicalAxis_eq_zero_of_matching_noninterlacing
    lam mu h hgram hfinite hn (row.succ, true) _ p
  intro i hi
  exact retainedPhysicalSource_not_interlaces_of_invalid_positive
    lam mu h row hbad i hi


-- @@ L764-777 verbatim
theorem gtAxisCompressedSignedProjectorCoefficient_invalid_negative_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
      (row.castSucc, false) = 0 := by
  unfold gtAxisCompressedSignedProjectorCoefficient
  rw [signedCharacteristicProjector_canonicalAxis_invalid_negative_eq_zero
    lam mu h hgram hfinite hn row hbad q, inner_zero_right]


-- @@ L779-793 verbatim
theorem gtAxisCompressedSignedProjectorCoefficient_invalid_positive_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
      (row.succ, true) = 0 := by
  unfold gtAxisCompressedSignedProjectorCoefficient
  rw [signedCharacteristicProjector_canonicalAxis_invalid_positive_eq_zero
    lam mu h hgram hfinite hn row hbad q, inner_zero_right]


-- @@ L795-811 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero_of_invalid
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : ¬ Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1) mu) (.inr (row, false))) = 0 :=
  gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero
    lam mu h hgram hfinite row hbad p q
    (gtAxisCompressedSignedProjectorCoefficient_invalid_negative_eq_zero
      lam mu h hgram hfinite hn row hbad p q)


-- @@ L813-830 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hbad : mu row = 0 ∨
      ¬ Interlaces lam (loweredInternalYoungWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1) mu) (.inr (row, true))) = 0 :=
  gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero
    lam mu h hgram hfinite row hbad p q
    (gtAxisCompressedSignedProjectorCoefficient_invalid_positive_eq_zero
      lam mu h hgram hfinite hn row hbad p q)


-- @@ L832-832 verbatim
end AllRankGTPhysicalInvalidRowProjectorVanishing


-- @@ L834-834 verbatim
end


-- @@ L836-836 verbatim
section



-- @@ L839-839 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L841-841 verbatim
namespace AllRankGTTransverseCharacteristicDeterminant


-- @@ L843-843 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L844-844 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L845-845 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L846-846 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L847-847 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L848-848 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement


-- @@ L850-858 verbatim
theorem nodal_erase_coeff_card_pred
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (i : ι) :
    (Lagrange.nodal (Finset.univ.erase i) nodes).coeff
      (Fintype.card ι - 1) = 1 := by
  have h := (Lagrange.nodal_monic
    (s := Finset.univ.erase i) (v := nodes)).leadingCoeff
  rw [Polynomial.leadingCoeff, Lagrange.natDegree_nodal] at h
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] using h


-- @@ L860-875 verbatim
theorem gtAxisCompressedCharacteristicMinor_coeff_card_pred
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).coeff
      (Fintype.card (Fin (r + 2) × Bool) - 1) =
      ⟪p, q⟫_ℝ := by
  rw [gtAxisCompressedCharacteristicMinor_eq_sum_nodal_erase
    lam mu h hgram hfinite p q, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul,
    nodal_erase_coeff_card_pred
      (signedNode (ambientShift (n + 1) lam)), mul_one]
  exact sum_gtAxisCompressedSignedProjectorCoefficient
    lam mu h hgram hfinite p q


-- @@ L877-918 verbatim
theorem polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
    {ι : Type*} [Fintype ι]
    (nodes : ι → ℝ) (hinj : Function.Injective nodes)
    (P : Polynomial ℝ) (c : ℝ)
    (hdeg : P.degree < Fintype.card ι + 1)
    (hcoeff : P.coeff (Fintype.card ι) = c)
    (hroot : ∀ i : ι, P.eval (nodes i) = 0) :
    P = Polynomial.C c * Lagrange.nodal Finset.univ nodes := by
  classical
  let Q : Polynomial ℝ :=
    P - Polynomial.C c * Lagrange.nodal Finset.univ nodes
  have hqdeg : Q.degree < Fintype.card ι := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    unfold Q
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    by_cases heq : k = Fintype.card ι
    · subst k
      rw [hcoeff]
      have hmonic := (Lagrange.nodal_monic
        (s := Finset.univ) (v := nodes)).leadingCoeff
      rw [Polynomial.leadingCoeff, Lagrange.natDegree_nodal] at hmonic
      simp only [Finset.card_univ] at hmonic
      rw [hmonic]
      ring
    · have hstrict : Fintype.card ι < k := lt_of_le_of_ne hk (Ne.symm heq)
      have hpzero : P.coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact hdeg.trans_le (by exact_mod_cast hstrict)
      have hnzero :
          (Lagrange.nodal (Finset.univ : Finset ι) nodes).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        rw [Lagrange.degree_nodal]
        exact_mod_cast hstrict
      rw [hpzero, hnzero, mul_zero, sub_zero]
  have hqzero : Q = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (Finset.univ : Finset ι) hinj.injOn hqdeg (by
        intro i _
        simp only [Polynomial.eval_sub, hroot i, Polynomial.eval_mul, Polynomial.eval_C,
          Lagrange.eval_nodal_at_node (Finset.mem_univ i), mul_zero, sub_self, Q])
  exact sub_eq_zero.mp hqzero


-- @@ L920-961 verbatim
theorem gtStabilizerArrowheadNode_injective_of_gap
    {r : ℕ} (rho : ℝ) (M : Fin r → ℝ)
    (hrho : 0 < rho)
    (hgap : ∀ i : Fin r, rho + 1 / 2 ≤ M i)
    (hinj : Function.Injective M) :
    Function.Injective (gtStabilizerArrowheadNode rho M) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => cases x; cases y; rfl
      | inr y =>
          rcases y with ⟨j, b⟩
          cases b <;>
            simp only [gtStabilizerArrowheadNode] at hxy <;>
            linarith [hgap j]
  | inr x =>
      rcases x with ⟨i, a⟩
      cases y with
      | inl y =>
          cases a <;>
            simp only [gtStabilizerArrowheadNode] at hxy <;>
            linarith [hgap i]
      | inr y =>
          rcases y with ⟨j, b⟩
          cases a <;> cases b
          · have heq : M i = M j := by
              simp only [gtStabilizerArrowheadNode] at hxy
              linarith
            have hij := hinj heq
            subst j
            rfl
          · simp only [gtStabilizerArrowheadNode] at hxy
            linarith [hgap i, hgap j]
          · simp only [gtStabilizerArrowheadNode] at hxy
            linarith [hgap i, hgap j]
          · have heq : M i = M j := by
              simp only [gtStabilizerArrowheadNode] at hxy
              linarith
            have hij := hinj heq
            subst j
            rfl


-- @@ L963-996 verbatim
theorem gtStabilizerArrowheadNode_injective_of_interlacing
    {r n : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ}
    (h : FiniteInterlacing (n + 1) lam mu) :
    Function.Injective
      (gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu)) := by
  apply gtStabilizerArrowheadNode_injective_of_gap
    (wallShift (n + 1) (r + 1))
    (stabilizerShift (n + 1) mu) h.wallShift_pos
  · intro i
    unfold stabilizerShift wallShift
    have hi : i.val ≤ r := by have := i.isLt; omega
    have hireal : (i.val : ℝ) ≤ r := by exact_mod_cast hi
    have hmu : (0 : ℝ) ≤ mu i := Nat.cast_nonneg _
    push_cast
    linarith
  · have hanti : Antitone mu := by
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      exact (h.2 i.succ).1.trans (by
        simpa only [Fin.castSucc_succ] using (h.2 i.castSucc).2)
    have hstrict : StrictAnti (stabilizerShift (n + 1) mu) := by
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      have hm := hanti (Fin.castSucc_le_succ i)
      unfold stabilizerShift
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hmreal : (mu i.succ : ℝ) ≤ (mu i.castSucc : ℝ) := by
        exact_mod_cast hm
      push_cast
      linarith
    exact hstrict.injective


-- @@ L998-1029 verbatim
theorem gtAxisCompressedCharacteristicMinor_eq_stabilizerArrowheadMinor_of_roots
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ∀ j : Unit ⊕ (Fin (r + 1) × Bool),
      (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) j) = 0) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        gtStabilizerArrowheadMinor
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) := by
  unfold gtStabilizerArrowheadMinor
  apply polynomial_eq_C_mul_nodal_of_roots_and_topCoeff
    (gtStabilizerArrowheadNode
      (wallShift (n + 1) (r + 1))
      (stabilizerShift (n + 1) mu))
    (gtStabilizerArrowheadNode_injective_of_interlacing hfinite)
  · have hdegree := gtAxisCompressedCharacteristicMinor_degree_lt
      lam mu h hgram hfinite p q
    convert hdegree using 1;
      simp [Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool]; ring
  · convert gtAxisCompressedCharacteristicMinor_coeff_card_pred
      lam mu h hgram hfinite p q using 2;
      simp [Fintype.card_sum, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool]; omega
  · exact hroot


-- @@ L1031-1049 verbatim
theorem gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_roots
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hroot : ∀ j : Unit ⊕ (Fin (r + 1) × Bool),
      (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
        (gtStabilizerArrowheadNode
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) j) = 0) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial
          (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) := by
  rw [← gtStabilizerArrowheadMinor_eq_channelNumerator]
  exact gtAxisCompressedCharacteristicMinor_eq_stabilizerArrowheadMinor_of_roots
    lam mu h hgram hfinite p q hroot


-- @@ L1051-1051 verbatim
end AllRankGTTransverseCharacteristicDeterminant


-- @@ L1053-1053 verbatim
end


-- @@ L1055-1055 verbatim
section



-- @@ L1058-1058 verbatim
open scoped InnerProductSpace


-- @@ L1060-1060 verbatim
namespace AllRankGTCharacteristicMinorOfValidRoots


-- @@ L1062-1062 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L1063-1063 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L1064-1064 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L1065-1065 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L1066-1066 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalInvalidRowProjectorVanishing

-- @@ L1067-1067 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant

-- @@ L1068-1068 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L1069-1069 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

-- @@ L1070-1070 verbatim
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower


-- @@ L1072-1123 verbatim
theorem gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_validRoots
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hwall : (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0)
    (hnegative : ∀ row : Fin (r + 1),
      Interlaces lam (raiseWeight mu row) →
        (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
          (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1) mu)
              (.inr (row, false))) = 0)
    (hpositive : ∀ row : Fin (r + 1), 0 < mu row →
      Interlaces lam (loweredInternalYoungWeight mu row) →
        (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
          (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1) mu)
              (.inr (row, true))) = 0) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (HigherChannel.stabilizerShift (n + 1) mu) := by
  apply gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_roots
    lam mu h hgram hfinite p q
  intro node
  cases node with
  | inl wall =>
      cases wall
      exact hwall
  | inr signed =>
      rcases signed with ⟨row, sign⟩
      cases sign with
      | false =>
          by_cases hvalid : Interlaces lam (raiseWeight mu row)
          · exact hnegative row hvalid
          · exact
              gtAxisCompressedCharacteristicMinor_eval_negativeStabilizerNode_eq_zero_of_invalid
                lam mu h hgram hfinite hn row hvalid p q
      | true =>
          by_cases hzero : mu row = 0
          · exact
              gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
                lam mu h hgram hfinite hn row (.inl hzero) p q
          · by_cases hvalid :
              Interlaces lam (loweredInternalYoungWeight mu row)
            · exact hpositive row (Nat.pos_of_ne_zero hzero) hvalid
            · exact
                gtAxisCompressedCharacteristicMinor_eval_positiveStabilizerNode_eq_zero_of_invalid
                  lam mu h hgram hfinite hn row (.inr hvalid) p q


-- @@ L1125-1125 verbatim
end AllRankGTCharacteristicMinorOfValidRoots


-- @@ L1127-1127 verbatim
end


-- @@ L1129-1129 verbatim
section



-- @@ L1132-1132 verbatim
open scoped BigOperators TensorProduct


-- @@ L1134-1134 verbatim
namespace AllRankGTStabilizerCasimirShift


-- @@ L1136-1136 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L1137-1137 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L1138-1138 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L1139-1139 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L1140-1140 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement


-- @@ L1142-1146 verbatim
theorem stabilizerShift_succ_eq_ambientShift {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    stabilizerShift (n + 1) mu row = ambientShift n mu row := by
  simp only [stabilizerShift, ambientShift, Nat.cast_add, Nat.cast_one]
  ring


-- @@ L1148-1155 verbatim
theorem gtStabilizerCasimir_raiseBranch_eigenvalue {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n (raiseWeight mu row)) / 2 =
      -stabilizerShift (n + 1) mu row - 1 / 2 := by
  have h := gtRelativeCasimir_raise_eigenvalue (n := n) mu row
  rw [← stabilizerShift_succ_eq_ambientShift] at h
  linarith


-- @@ L1157-1166 verbatim
theorem gtStabilizerCasimir_lowerBranch_eigenvalue {r n : ℕ}
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : mu = raiseWeight nu row) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n nu) / 2 =
      stabilizerShift (n + 1) mu row - 1 / 2 := by
  have h := gtRelativeCasimir_lower_eigenvalue
    (n := n) mu nu row hnu
  rw [← stabilizerShift_succ_eq_ambientShift] at h
  linarith


-- @@ L1168-1174 verbatim
theorem gtStabilizerRelativeCasimir_raiseTarget_eigenvalue {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n (raiseWeight mu row) - 1) / 2 =
      -stabilizerShift (n + 1) mu row - 1 := by
  have h := gtStabilizerCasimir_raiseBranch_eigenvalue (n := n) mu row
  linarith


-- @@ L1176-1184 verbatim
theorem gtStabilizerRelativeCasimir_lowerTarget_eigenvalue {r n : ℕ}
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : mu = raiseWeight nu row) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n nu - 1) / 2 =
      stabilizerShift (n + 1) mu row - 1 := by
  have h := gtStabilizerCasimir_lowerBranch_eigenvalue
    (n := n) mu nu row hnu
  linarith


-- @@ L1186-1191 verbatim
/-- The stabilizer relative Casimir shifted by one half of the identity. -/
def gtStabilizerShiftedRelativeCasimir {r n : ℕ}
    (nu : Fin (r + 1) → ℕ) :
    Module.End ℝ (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu) :=
  gtRelativeCasimir nu + (1 / 2 : ℝ) • LinearMap.id


-- @@ L1193-1213 verbatim
theorem gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
    {r n : ℕ} (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (raiseWeight mu row)))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (ClebschRotation.tensorAmbientRotation
          (raiseWeight mu row) a b).comp A)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtStabilizerShiftedRelativeCasimir (raiseWeight mu row) (A p) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false)) • A p := by
  simp only [gtStabilizerShiftedRelativeCasimir, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply,
    gtStabilizerArrowheadNode_neg]
  rw [gtRelativeCasimir_channel mu (raiseWeight mu row) A hA,
    gtStabilizerRelativeCasimir_raiseTarget_eigenvalue]
  rw [← add_smul]
  congr 1
  ring


-- @@ L1215-1236 verbatim
theorem gtStabilizerShiftedRelativeCasimir_lowerTarget_channel
    {r n : ℕ} (mu nu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hnu : mu = raiseWeight nu row)
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) nu))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (ClebschRotation.tensorAmbientRotation nu a b).comp A)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtStabilizerShiftedRelativeCasimir nu (A p) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, true)) • A p := by
  simp only [gtStabilizerShiftedRelativeCasimir, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply,
    gtStabilizerArrowheadNode_pos]
  rw [gtRelativeCasimir_channel mu nu A hA,
    gtStabilizerRelativeCasimir_lowerTarget_eigenvalue
      mu nu row hnu]
  rw [← add_smul]
  congr 1
  ring


-- @@ L1238-1238 verbatim
end AllRankGTStabilizerCasimirShift


-- @@ L1240-1240 verbatim
end


-- @@ L1242-1242 verbatim
section



-- @@ L1245-1245 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L1247-1247 verbatim
namespace AllRankGTTransverseCasimirEmbedding


-- @@ L1249-1249 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L1250-1250 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L1251-1251 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L1252-1252 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L1253-1253 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L1254-1254 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift

-- @@ L1255-1255 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L1256-1256 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L1257-1257 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L1258-1258 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L1259-1259 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement


-- @@ L1261-1276 verbatim
/-- The linear embedding of Euclidean space obtained by appending a zero coordinate. -/
def gtTransverseEuclidean (n : ℕ) :
    SpherePacking.Euclidean n →ₗ[ℝ] SpherePacking.Euclidean (n + 1) where
  toFun x := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) 0)
  map_add' x y := by
    ext i
    induction i using Fin.lastCases with
    | last => simp only [WithLp.ofLp_add, Fin.snoc_last, PiLp.add_apply, add_zero]
    | cast j => simp only [WithLp.ofLp_add, Fin.snoc_castSucc, Pi.add_apply, PiLp.add_apply]
  map_smul' c x := by
    ext i
    induction i using Fin.lastCases with
    | last => simp only [WithLp.ofLp_smul, Fin.snoc_last, Real.ringHom_apply, PiLp.smul_apply,
                smul_eq_mul, mul_zero]
    | cast j => simp only [WithLp.ofLp_smul, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul,
                  Real.ringHom_apply, PiLp.smul_apply]


-- @@ L1278-1281 verbatim
@[simp] theorem gtTransverseEuclidean_castSucc
    (n : ℕ) (x : SpherePacking.Euclidean n) (i : Fin n) :
    gtTransverseEuclidean n x i.castSucc = x i := by
  simp only [gtTransverseEuclidean, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc]


-- @@ L1283-1286 verbatim
@[simp] theorem gtTransverseEuclidean_last
    (n : ℕ) (x : SpherePacking.Euclidean n) :
    gtTransverseEuclidean n x (Fin.last n) = 0 := by
  simp only [gtTransverseEuclidean, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last]


-- @@ L1288-1293 verbatim
theorem gtTransverseEuclidean_inner
    (n : ℕ) (x y : SpherePacking.Euclidean n) :
    ⟪gtTransverseEuclidean n x, gtTransverseEuclidean n y⟫_ℝ =
      ⟪x, y⟫_ℝ := by
  rw [PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp [PiLp.inner_apply]


-- @@ L1295-1298 verbatim
/-- The isometric embedding of Euclidean space obtained by appending a zero coordinate. -/
def gtTransverseEuclideanIsometry (n : ℕ) :
    SpherePacking.Euclidean n →ₗᵢ[ℝ] SpherePacking.Euclidean (n + 1) :=
  (gtTransverseEuclidean n).isometryOfInner (gtTransverseEuclidean_inner n)


-- @@ L1300-1304 verbatim
@[simp] theorem gtTransverseEuclideanIsometry_castSucc
    (n : ℕ) (x : SpherePacking.Euclidean n) (i : Fin n) :
    gtTransverseEuclideanIsometry n x i.castSucc = x i := by
  simp only [gtTransverseEuclideanIsometry, gtTransverseEuclidean, LinearMap.coe_isometryOfInner,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc]


-- @@ L1306-1310 verbatim
@[simp] theorem gtTransverseEuclideanIsometry_last
    (n : ℕ) (x : SpherePacking.Euclidean n) :
    gtTransverseEuclideanIsometry n x (Fin.last n) = 0 := by
  simp only [gtTransverseEuclideanIsometry, gtTransverseEuclidean, LinearMap.coe_isometryOfInner,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last]


-- @@ L1312-1317 verbatim
theorem gtTransverseEuclideanIsometry_orthogonal_last
    (n : ℕ) (x : SpherePacking.Euclidean n) :
    ⟪gtTransverseEuclideanIsometry n x,
      EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)⟫_ℝ = 0 := by
  rw [EuclideanSpace.inner_basisFun_real,
    gtTransverseEuclideanIsometry_last]


-- @@ L1319-1330 verbatim
/-- The tensor isometry combining the transverse Euclidean inclusion with a canonical
Gelfand–Tsetlin fibre. -/
def gtTransverseTensorEmbedding
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ)
    (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h) :
    (SpherePacking.Euclidean n ⊗[ℝ] HarmonicYoungSpace (n := n) nu) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n)
    (canonicalGelfandTsetlinFibre lam nu h hgram)


-- @@ L1332-1341 verbatim
@[simp] theorem gtTransverseTensorEmbedding_tmul
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ)
    (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) nu) :
    gtTransverseTensorEmbedding lam nu h hgram (v ⊗ₜ[ℝ] p) =
      gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
        canonicalGelfandTsetlinFibre lam nu h hgram p := rfl


-- @@ L1343-1363 verbatim
theorem gtTransverseTensorEmbedding_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu mu : Fin (r + 1) → ℕ)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu)
    (q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseTensorEmbedding lam nu hnu hnuGram x,
      canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram q⟫_ℝ = 0 := by
  induction x with
  | tmul v p =>
      rw [gtTransverseTensorEmbedding_tmul,
        canonicalGelfandTsetlinAxisTensor_apply,
        TensorProduct.inner_tmul,
        gtTransverseEuclideanIsometry_orthogonal_last]
      simp only [canonicalGelfandTsetlinFibre_apply, zero_mul]
  | add x y hx hy =>
      rw [map_add, inner_add_left, hx, hy, zero_add]


-- @@ L1365-1379 verbatim
/-- The transverse negative-sector map obtained by composing Clebsch raising with the transverse
tensor embedding. -/
def gtTransverseNegativeSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (gtTransverseTensorEmbedding lam (raiseWeight mu row)
    hnu hgram).toLinearMap.comp
      (youngClebschRaise (raiseWeight mu row) mu
        (sum_raiseWeight mu row) row)


-- @@ L1381-1395 verbatim
/-- The transverse positive-sector map obtained by composing Clebsch lowering with the
transverse tensor embedding. -/
def gtTransversePositiveSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam nu hnu) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.comp
    (youngClebschLower nu mu
      (by rw [hmu]; exact sum_raiseWeight nu row) row)


-- @@ L1397-1411 verbatim
theorem gtTransverseNegativeSector_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseNegativeSector lam mu row hnu hnuGram p,
      canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram q⟫_ℝ = 0 := by
  exact gtTransverseTensorEmbedding_axis_inner_eq_zero
    lam (raiseWeight mu row) mu hnu hnuGram hmu hmuGram
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row p) q


-- @@ L1413-1427 verbatim
theorem gtTransversePositiveSector_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p,
      canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram q⟫_ℝ = 0 := by
  exact gtTransverseTensorEmbedding_axis_inner_eq_zero
    lam nu mu hnu hnuGram hmu hmuGram
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row p) q


-- @@ L1429-1429 verbatim
end AllRankGTTransverseCasimirEmbedding


-- @@ L1431-1431 verbatim
end


-- @@ L1433-1433 verbatim
section



-- @@ L1436-1436 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L1438-1438 verbatim
namespace AllRankGTTransverseTangentialCompression


-- @@ L1440-1440 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L1441-1441 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L1442-1442 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis

-- @@ L1443-1443 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L1444-1444 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L1445-1445 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L1446-1446 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph


-- @@ L1448-1461 verbatim
theorem canonicalGelfandTsetlinFibre_rotation_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin n) :
    (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap.adjoint.comp
        ((youngAmbientRotation lam a.castSucc b.castSucc).comp
          (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap) =
      youngAmbientRotation nu a b := by
  rw [← canonicalGelfandTsetlinFibre_rotation_intertwine
    lam nu h hgram a b]
  rw [← LinearMap.comp_assoc,
    (canonicalGelfandTsetlinFibre lam nu h hgram).adjoint_comp_self',
    LinearMap.id_comp]


-- @@ L1463-1483 verbatim
theorem gtTransverseEuclideanIsometry_rotation_intertwine
    (n : ℕ) (a b : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.comp
        (euclideanAmbientRotation a b) =
      (euclideanAmbientRotation a.castSucc b.castSucc).comp
        (gtTransverseEuclideanIsometry n).toLinearMap := by
  apply LinearMap.ext
  intro v
  ext i
  induction i using Fin.lastCases with
  | last =>
      simp only [LinearMap.coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply,
        euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, map_sub, map_smul,
        PiLp.sub_apply, PiLp.smul_apply, gtTransverseEuclideanIsometry_last, smul_eq_mul, mul_zero,
        sub_self, gtTransverseEuclideanIsometry_castSucc, ne_eq, Fin.castSucc_ne_last,
        not_false_eq_true, PiLp.single_eq_of_ne']
  | cast i =>
      simp only [LinearMap.coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply,
        euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, map_sub, map_smul,
        PiLp.sub_apply, PiLp.smul_apply, gtTransverseEuclideanIsometry_castSucc, PiLp.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.castSucc_inj]


-- @@ L1485-1494 verbatim
theorem gtTransverseEuclideanIsometry_rotation_adjoint_compression
    (n : ℕ) (a b : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
        ((euclideanAmbientRotation a.castSucc b.castSucc).comp
          (gtTransverseEuclideanIsometry n).toLinearMap) =
      euclideanAmbientRotation a b := by
  rw [← gtTransverseEuclideanIsometry_rotation_intertwine n a b]
  rw [← LinearMap.comp_assoc,
    (gtTransverseEuclideanIsometry n).adjoint_comp_self',
    LinearMap.id_comp]


-- @@ L1496-1504 verbatim
theorem gtTransverseEuclideanIsometry_adjoint_basisFun_last
    (n : ℕ) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [LinearMap.adjoint_inner_left, inner_zero_left]
  rw [real_inner_comm]
  exact gtTransverseEuclideanIsometry_orthogonal_last n v


-- @@ L1506-1521 verbatim
theorem gtTransverseEuclideanIsometry_cross_rotation_compression
    (n : ℕ) (a : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
        ((euclideanAmbientRotation a.castSucc (Fin.last n)).comp
          (gtTransverseEuclideanIsometry n).toLinearMap) = 0 := by
  apply LinearMap.ext
  intro v
  change
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
      (euclideanAmbientRotation a.castSucc (Fin.last n)
        (gtTransverseEuclideanIsometry n v)) = 0
  rw [euclideanAmbientRotation_apply,
    gtTransverseEuclideanIsometry_last, zero_smul, zero_sub,
    map_neg, map_smul,
    gtTransverseEuclideanIsometry_adjoint_basisFun_last,
    smul_zero, neg_zero]


-- @@ L1523-1538 verbatim
theorem gtTransverseEuclideanIsometry_cross_rotation_compression_swap
    (n : ℕ) (a : Fin n) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
        ((euclideanAmbientRotation (Fin.last n) a.castSucc).comp
          (gtTransverseEuclideanIsometry n).toLinearMap) = 0 := by
  apply LinearMap.ext
  intro v
  change
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
      (euclideanAmbientRotation (Fin.last n) a.castSucc
        (gtTransverseEuclideanIsometry n v)) = 0
  rw [euclideanAmbientRotation_apply,
    gtTransverseEuclideanIsometry_last, zero_smul, sub_zero,
    map_smul,
    gtTransverseEuclideanIsometry_adjoint_basisFun_last,
    smul_zero]


-- @@ L1540-1568 verbatim
theorem gtTransverseTensorEmbedding_rotationTerm_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin (n + 1)) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      TensorProduct.map
        ((gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
          ((euclideanAmbientRotation a b).comp
            (gtTransverseEuclideanIsometry n).toLinearMap))
        ((canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap.adjoint.comp
          ((youngAmbientRotation lam a b).comp
            (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap)) := by
  change
    (TensorProduct.map
      (gtTransverseEuclideanIsometry n).toLinearMap
      (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap).adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (TensorProduct.map
            (gtTransverseEuclideanIsometry n).toLinearMap
            (canonicalGelfandTsetlinFibre lam nu h hgram).toLinearMap)) = _
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  rfl


-- @@ L1570-1584 verbatim
theorem gtTransverseTensorEmbedding_tangentialTerm_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      TensorProduct.map (euclideanAmbientRotation a b)
        (youngAmbientRotation nu a b) := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression,
    gtTransverseEuclideanIsometry_rotation_adjoint_compression,
    canonicalGelfandTsetlinFibre_rotation_adjoint_compression]


-- @@ L1586-1601 verbatim
theorem gtTransverseTensorEmbedding_crossTerm_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc (Fin.last n))
          (youngAmbientRotation lam a.castSucc (Fin.last n))).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) = 0 := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression,
    gtTransverseEuclideanIsometry_cross_rotation_compression]
  apply TensorProduct.ext
  ext v p
  simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.zero_apply]


-- @@ L1603-1618 verbatim
theorem gtTransverseTensorEmbedding_crossTerm_adjoint_compression_swap
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) a.castSucc)
          (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) = 0 := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression,
    gtTransverseEuclideanIsometry_cross_rotation_compression_swap]
  apply TensorProduct.ext
  ext v p
  simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.zero_apply]


-- @@ L1620-1636 verbatim
theorem gtTransverseTensorEmbedding_lastTerm_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) (Fin.last n))
          (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) = 0 := by
  rw [gtTransverseTensorEmbedding_rotationTerm_adjoint_compression]
  have hzero : euclideanAmbientRotation (Fin.last n) (Fin.last n) = 0 := by
    apply LinearMap.ext
    intro v
    simp only [euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, sub_self,
      LinearMap.zero_apply]
  rw [hzero]
  simp only [LinearMap.zero_comp, LinearMap.comp_zero, TensorProduct.map_zero_left]


-- @@ L1638-1666 verbatim
theorem gtTransverseTensorEmbedding_mixedRotation_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      gtMixedRotationOperator (n := n) nu := by
  unfold gtMixedRotationOperator
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential (a b : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_tangentialTerm_adjoint_compression
      lam nu h hgram a b) (v ⊗ₜ[ℝ] p)
  have hcross (a : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_crossTerm_adjoint_compression
      lam nu h hgram a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap (a : Fin n) := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_crossTerm_adjoint_compression_swap
      lam nu h hgram a) (v ⊗ₜ[ℝ] p)
  have hlast := LinearMap.congr_fun
    (gtTransverseTensorEmbedding_lastTerm_adjoint_compression
      lam nu h hgram) (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at htangential hcross hcrossSwap hlast
  simp only [htangential, hcross, hcrossSwap, hlast,
    Finset.sum_const_zero, add_zero]


-- @@ L1668-1668 verbatim
end AllRankGTTransverseTangentialCompression


-- @@ L1670-1670 verbatim
end


-- @@ L1672-1672 verbatim
section



-- @@ L1675-1675 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L1677-1677 verbatim
namespace AllRankGTTransverseTensorRelativeCompression


-- @@ L1679-1679 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L1680-1680 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L1681-1681 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L1682-1682 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L1683-1683 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis

-- @@ L1684-1684 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift

-- @@ L1685-1685 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L1686-1686 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression

-- @@ L1687-1687 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L1688-1688 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L1689-1689 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L1690-1690 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L1691-1691 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement


-- @@ L1693-1700 verbatim
theorem gtRelativeCasimir_eq_scalar_sub_mixed
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    gtRelativeCasimir (n := n) lam =
      (((n : ℝ) - 2) / 2) • LinearMap.id -
        (2 : ℝ)⁻¹ • gtMixedRotationOperator lam := by
  apply TensorProduct.ext
  ext x y
  exact gtRelativeCasimir_tmul_eq_scalar_sub_mixed lam x y


-- @@ L1702-1722 verbatim
theorem gtRelativeCasimir_transverse_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ)
    (I : (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hisom : I.adjoint.comp I = LinearMap.id)
    (hmixed : I.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp I) =
      gtMixedRotationOperator (n := n) nu) :
    I.adjoint.comp ((gtRelativeCasimir (n := n + 1) lam).comp I) =
      gtStabilizerShiftedRelativeCasimir nu := by
  rw [gtRelativeCasimir_eq_scalar_sub_mixed (n := n + 1) lam,
    gtStabilizerShiftedRelativeCasimir,
    gtRelativeCasimir_eq_scalar_sub_mixed (n := n) nu]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp,
    LinearMap.id_comp, LinearMap.comp_sub, LinearMap.comp_smul]
  rw [hisom, hmixed]
  norm_num
  module


-- @@ L1724-1740 verbatim
theorem gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (hmixed :
      (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) nu) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap) =
      gtStabilizerShiftedRelativeCasimir nu := by
  exact gtRelativeCasimir_transverse_compression_of_mixed lam nu
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap
    (gtTransverseTensorEmbedding lam nu h hgram).adjoint_comp_self'
    hmixed


-- @@ L1742-1773 verbatim
theorem gtTransverseNegativeSector_relativeCasimir_adjoint_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (hmixed :
      (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint.comp
          ((gtMixedRotationOperator (n := n + 1) lam).comp
            (gtTransverseTensorEmbedding lam (raiseWeight mu row)
              hnu hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) (raiseWeight mu row))
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransverseNegativeSector lam mu row hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, false)) •
          youngClebschRaise (raiseWeight mu row) mu
            (sum_raiseWeight mu row) row p := by
  exact (LinearMap.congr_fun
    (gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
      lam (raiseWeight mu row) hnu hgram hmixed)
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row p)).trans
    (gtStabilizerShiftedRelativeCasimir_raiseTarget_channel mu row
      (youngClebschRaise (raiseWeight mu row) mu
        (sum_raiseWeight mu row) row)
      (fun a b => youngClebschRaise_rotation_intertwine
        (raiseWeight mu row) mu (sum_raiseWeight mu row) row a b)
      p)


-- @@ L1775-1805 verbatim
theorem gtTransversePositiveSector_relativeCasimir_adjoint_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (hmixed :
      (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap) =
        gtMixedRotationOperator (n := n) nu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransversePositiveSector lam mu nu row hmu hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, true)) •
          youngClebschLower nu mu
            (by rw [hmu]; exact sum_raiseWeight nu row) row p := by
  exact (LinearMap.congr_fun
    (gtRelativeCasimir_gtTransverseTensorEmbedding_adjoint_compression_of_mixed
      lam nu hnu hgram hmixed)
    (youngClebschLower nu mu
      (by rw [hmu]; exact sum_raiseWeight nu row) row p)).trans
    (gtStabilizerShiftedRelativeCasimir_lowerTarget_channel mu nu row hmu
      (youngClebschLower nu mu
        (by rw [hmu]; exact sum_raiseWeight nu row) row)
      (fun a b => youngClebschLower_rotation_intertwine
        nu mu (by rw [hmu]; exact sum_raiseWeight nu row) row a b)
      p)


-- @@ L1807-1825 verbatim
theorem gtTransverseNegativeSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransverseNegativeSector lam mu row hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, false)) •
          youngClebschRaise (raiseWeight mu row) mu
            (sum_raiseWeight mu row) row p :=
  gtTransverseNegativeSector_relativeCasimir_adjoint_compression_of_mixed
    lam mu row hnu hgram
    (gtTransverseTensorEmbedding_mixedRotation_adjoint_compression
      lam (raiseWeight mu row) hnu hgram) p


-- @@ L1827-1845 verbatim
theorem gtTransversePositiveSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam nu hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransversePositiveSector lam mu nu row hmu hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, true)) •
          youngClebschLower nu mu
            (by rw [hmu]; exact sum_raiseWeight nu row) row p :=
  gtTransversePositiveSector_relativeCasimir_adjoint_compression_of_mixed
    lam mu nu row hmu hnu hgram
    (gtTransverseTensorEmbedding_mixedRotation_adjoint_compression
      lam nu hnu hgram) p


-- @@ L1847-1847 verbatim
end AllRankGTTransverseTensorRelativeCompression


-- @@ L1849-1849 verbatim
namespace AllRankGTTransverseWignerEckartPhase


-- @@ L1851-1851 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L1852-1852 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L1853-1853 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalEdgeRaisingGram

-- @@ L1854-1854 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L1855-1855 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L1856-1856 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L1857-1857 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

-- @@ L1858-1858 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels

-- @@ L1859-1859 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L1860-1860 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L1861-1861 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L1862-1862 verbatim
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower


-- @@ L1864-1888 verbatim
theorem gtTransverseNegativeSector_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseNegativeSector lam mu row hnu hnuGram p,
      gtTransverseNegativeSector lam mu row hnu hnuGram q⟫_ℝ =
      (internalRowLowerGramScalar (raiseWeight mu row) row *
        weylEdgeRatio n mu row) * ⟪p, q⟫_ℝ := by
  obtain ⟨c, _hc, hinner, hc⟩ :=
    canonicalEdgeRaisingGram mu kappa row hfinite hraise
  change
    ⟪gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram
        (youngClebschRaise (raiseWeight mu row) mu
          (sum_raiseWeight mu row) row p),
      gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram
        (youngClebschRaise (raiseWeight mu row) mu
          (sum_raiseWeight mu row) row q)⟫_ℝ = _
  rw [(gtTransverseTensorEmbedding lam (raiseWeight mu row)
    hnu hnuGram).inner_map_map, hinner p q, hc]


-- @@ L1890-1899 verbatim
theorem gtTransverseNegativeSector_gram_pos
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (kappa : Fin r → ℕ) (row : Fin (r + 1))
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    0 < internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row := by
  obtain ⟨c, hc, _hinner, heq⟩ :=
    canonicalEdgeRaisingGram mu kappa row hfinite hraise
  simpa only [heq] using hc


-- @@ L1901-1921 verbatim
/-- The transverse negative-sector map normalized by its positive Gram scalar to a linear
isometry. -/
def normalizedGTTransverseNegativeSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (gtTransverseNegativeSector lam mu row hnu hnuGram)
    (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row)
    (gtTransverseNegativeSector_gram_pos mu kappa row hfinite hraise)
    (gtTransverseNegativeSector_inner lam mu kappa row
      hnu hnuGram hfinite hraise)


-- @@ L1923-1936 verbatim
@[simp] theorem normalizedGTTransverseNegativeSector_toLinearMap
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap =
      (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
        weylEdgeRatio n mu row))⁻¹ •
        gtTransverseNegativeSector lam mu row hnu hnuGram := rfl


-- @@ L1938-1950 verbatim
private theorem youngClebschLower_inner_of_loweredSignature_metriccodes2_32e91722
    {r n : ℕ} (high low : Fin (r + 1) → ℕ)
    (row : Fin (r + 1))
    (hlowered : low = loweredInternalYoungWeight high row)
    (hpositive : 0 < high row)
    (hdominant : Antitone high)
    (hdegree : (∑ j, high j) = (∑ j, low j) + 1)
    (p q : HarmonicYoungSpace (n := n) high) :
    ⟪youngClebschLower low high hdegree row p,
      youngClebschLower low high hdegree row q⟫_ℝ =
      internalRowLowerGramScalar high row * ⟪p, q⟫_ℝ := by
  subst low
  exact youngClebschLower_arbitrary_inner high row hpositive hdominant p q


-- @@ L1952-1981 verbatim
theorem gtTransversePositiveSector_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p,
      gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram q⟫_ℝ =
      internalRowLowerGramScalar mu row * ⟪p, q⟫_ℝ := by
  subst mu
  have hpositive : 0 < raiseWeight nu row row := by
    simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le]
  have hdominant : Antitone (raiseWeight nu row) :=
    interlaces_antitone_stabilizer hmu
  change
    ⟪gtTransverseTensorEmbedding lam nu hnu hnuGram
        (youngClebschLower nu (raiseWeight nu row)
          (sum_raiseWeight nu row) row p),
      gtTransverseTensorEmbedding lam nu hnu hnuGram
        (youngClebschLower nu (raiseWeight nu row)
          (sum_raiseWeight nu row) row q)⟫_ℝ = _
  rw [(gtTransverseTensorEmbedding lam nu hnu hnuGram).inner_map_map]
  exact youngClebschLower_inner_of_loweredSignature_metriccodes2_32e91722
    (raiseWeight nu row) nu row
    (canonicalEdge_loweredInternalYoungWeight_raiseWeight nu row).symm
    hpositive hdominant (sum_raiseWeight nu row) p q


-- @@ L1983-1992 verbatim
theorem gtTransversePositiveSector_gram_pos
    {r : ℕ} (nu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hdominant : Antitone nu) :
    0 < internalRowLowerGramScalar (raiseWeight nu row) row := by
  apply internalRowLowerGramScalar_pos
  · simp only [raiseWeight, Function.update_self, lt_add_iff_pos_left, Order.lt_add_one_iff,
      zero_le]
  · intro j hj
    exact canonicalEdge_raiseWeight_strictly_removable
      nu hdominant row j hj


-- @@ L1994-2015 verbatim
/-- The transverse positive-sector map normalized by its positive Gram scalar to a linear
isometry. -/
def normalizedGTTransversePositiveSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram)
    (internalRowLowerGramScalar mu row)
    (by
      subst mu
      exact gtTransversePositiveSector_gram_pos nu row
        (interlaces_antitone_stabilizer hnu))
    (gtTransversePositiveSector_inner lam mu nu row
      hmunu hmu hnu hnuGram)


-- @@ L2017-2028 verbatim
@[simp] theorem normalizedGTTransversePositiveSector_toLinearMap
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu) :
    (normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram).toLinearMap =
      (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹ •
        gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram := rfl


-- @@ L2030-2030 verbatim
end AllRankGTTransverseWignerEckartPhase


-- @@ L2032-2032 verbatim
namespace AllRankGTNormalizedTransverseSector


-- @@ L2034-2034 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L2035-2035 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L2036-2036 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L2037-2037 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L2038-2038 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L2039-2039 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression

-- @@ L2040-2040 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L2041-2041 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L2042-2042 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

-- @@ L2043-2043 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L2044-2044 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L2045-2045 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L2046-2046 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement


-- @@ L2048-2091 verbatim
theorem isometric_scaled_sector_adjoint_compression
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [FiniteDimensional ℝ Z]
    (I : X →ₗᵢ[ℝ] Y) (C : Z →ₗ[ℝ] X)
    (B : Z →ₗᵢ[ℝ] Y) (T : Module.End ℝ Y)
    (phase node : ℝ)
    (hphase : B.toLinearMap = phase • I.toLinearMap.comp C)
    (hnode : ∀ p : Z,
      I.toLinearMap.adjoint (T (I (C p))) = node • C p) :
    B.toLinearMap.adjoint.comp (T.comp B.toLinearMap) =
      node • LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  rw [LinearMap.adjoint_inner_right, real_inner_smul_right]
  have hinner := B.inner_map_map q p
  change ⟪B.toLinearMap q, B.toLinearMap p⟫_ℝ = ⟪q, p⟫_ℝ at hinner
  rw [hphase] at hinner ⊢
  change
    ⟪phase • I (C q), T (phase • I (C p))⟫_ℝ =
      node * ⟪q, p⟫_ℝ
  change
    ⟪phase • I (C q), phase • I (C p)⟫_ℝ =
      ⟪q, p⟫_ℝ at hinner
  rw [real_inner_smul_left, real_inner_smul_right,
    I.inner_map_map] at hinner
  have hpair :
      ⟪I (C q), T (I (C p))⟫_ℝ =
        node * ⟪C q, C p⟫_ℝ := by
    change
      ⟪I.toLinearMap (C q), T (I (C p))⟫_ℝ =
        node * ⟪C q, C p⟫_ℝ
    rw [← LinearMap.adjoint_inner_right I.toLinearMap (C q)
      (T (I (C p))), hnode p, real_inner_smul_right]
  rw [map_smul, real_inner_smul_left, real_inner_smul_right,
    hpair, ← hinner]
  ring


-- @@ L2093-2127 verbatim
theorem normalizedGTTransverseNegativeSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa) :
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (normalizedGTTransverseNegativeSector lam mu kappa row
            hnu hnuGram hfinite hraise).toLinearMap) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift
          (n + 1) mu) (.inr (row, false)) •
          LinearMap.id := by
  apply isometric_scaled_sector_adjoint_compression
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram)
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row)
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise)
    (gtRelativeCasimir lam)
    (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row))⁻¹
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift
        (n + 1) mu) (.inr (row, false)))
  · exact normalizedGTTransverseNegativeSector_toLinearMap
      lam mu kappa row hnu hnuGram hfinite hraise
  · intro p
    exact gtTransverseNegativeSector_relativeCasimir_adjoint_compression
      lam mu row hnu hnuGram p


-- @@ L2129-2161 verbatim
theorem normalizedGTTransversePositiveSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu) :
    (normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (normalizedGTTransversePositiveSector lam mu nu row
            hmunu hmu hnu hnuGram).toLinearMap) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift
          (n + 1) mu) (.inr (row, true)) •
          LinearMap.id := by
  apply isometric_scaled_sector_adjoint_compression
    (gtTransverseTensorEmbedding lam nu hnu hnuGram)
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row)
    (normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram)
    (gtRelativeCasimir lam)
    (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift
        (n + 1) mu) (.inr (row, true)))
  · exact normalizedGTTransversePositiveSector_toLinearMap
      lam mu nu row hmunu hmu hnu hnuGram
  · intro p
    exact gtTransversePositiveSector_relativeCasimir_adjoint_compression
      lam mu nu row hmunu hnu hnuGram p


-- @@ L2163-2163 verbatim
end AllRankGTNormalizedTransverseSector


-- @@ L2165-2165 verbatim
namespace AllRankGTNormalizedTransverseRotationIntertwining


-- @@ L2167-2167 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L2168-2168 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L2169-2169 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L2170-2170 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L2171-2171 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression

-- @@ L2172-2172 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L2173-2173 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L2174-2174 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L2175-2175 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph


-- @@ L2177-2219 verbatim
theorem gtTransverseTensorEmbedding_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ) (h : Interlaces lam nu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam nu h)
    (a b : Fin n) :
    (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap.comp
        (tensorAmbientRotation nu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseTensorEmbedding lam nu h hgram).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul v p =>
      have hE := LinearMap.congr_fun
        (gtTransverseEuclideanIsometry_rotation_intertwine n a b) v
      have hF := LinearMap.congr_fun
        (canonicalGelfandTsetlinFibre_rotation_intertwine
          lam nu h hgram a b) p
      change
        gtTransverseEuclideanIsometry n (euclideanAmbientRotation a b v) =
          euclideanAmbientRotation a.castSucc b.castSucc
            (gtTransverseEuclideanIsometry n v) at hE
      change
        canonicalGelfandTsetlinFibre lam nu h hgram
            (youngAmbientRotation nu a b p) =
          youngAmbientRotation lam a.castSucc b.castSucc
            (canonicalGelfandTsetlinFibre lam nu h hgram p) at hF
      change
        gtTransverseEuclideanIsometry n
            (euclideanAmbientRotation a b v) ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram
            (youngAmbientRotation nu a b p) =
        euclideanAmbientRotation a.castSucc b.castSucc
            (gtTransverseEuclideanIsometry n v) ⊗ₜ[ℝ]
          canonicalGelfandTsetlinFibre lam nu h hgram p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          youngAmbientRotation lam a.castSucc b.castSucc
            (canonicalGelfandTsetlinFibre lam nu h hgram p)
      rw [hE, hF]


-- @@ L2221-2237 verbatim
theorem gtTransverseNegativeSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (a b : Fin n) :
    (gtTransverseNegativeSector lam mu row hnu hnuGram).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseNegativeSector lam mu row hnu hnuGram) := by
  unfold gtTransverseNegativeSector
  rw [LinearMap.comp_assoc,
    youngClebschRaise_rotation_intertwine,
    ← LinearMap.comp_assoc,
    gtTransverseTensorEmbedding_rotation_intertwine,
    LinearMap.comp_assoc]


-- @@ L2239-2256 verbatim
theorem gtTransversePositiveSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (a b : Fin n) :
    (gtTransversePositiveSector lam mu nu row hmu hnu hnuGram).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransversePositiveSector lam mu nu row hmu hnu hnuGram) := by
  unfold gtTransversePositiveSector
  rw [LinearMap.comp_assoc,
    youngClebschLower_rotation_intertwine,
    ← LinearMap.comp_assoc,
    gtTransverseTensorEmbedding_rotation_intertwine,
    LinearMap.comp_assoc]


-- @@ L2258-2276 verbatim
theorem normalizedGTTransverseNegativeSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (a b : Fin n) :
    (normalizedGTTransverseNegativeSector
      lam mu kappa row hnu hnuGram hfinite hraise).toLinearMap.comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (normalizedGTTransverseNegativeSector
          lam mu kappa row hnu hnuGram hfinite hraise).toLinearMap := by
  rw [normalizedGTTransverseNegativeSector_toLinearMap,
    LinearMap.smul_comp, LinearMap.comp_smul,
    gtTransverseNegativeSector_rotation_intertwine]


-- @@ L2278-2295 verbatim
theorem normalizedGTTransversePositiveSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (a b : Fin n) :
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap.comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram).toLinearMap := by
  rw [normalizedGTTransversePositiveSector_toLinearMap,
    LinearMap.smul_comp, LinearMap.comp_smul,
    gtTransversePositiveSector_rotation_intertwine]


-- @@ L2297-2297 verbatim
end AllRankGTNormalizedTransverseRotationIntertwining


-- @@ L2299-2299 verbatim
end


-- @@ L2301-2301 verbatim
section



-- @@ L2304-2304 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L2306-2306 verbatim
namespace AllRankGTTransverseAppendedChannelOrthogonality


-- @@ L2308-2308 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L2309-2309 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L2310-2310 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L2311-2311 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedClebschOrthogonality

-- @@ L2312-2312 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion

-- @@ L2313-2313 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L2314-2314 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport

-- @@ L2315-2315 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining

-- @@ L2316-2316 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L2317-2317 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining

-- @@ L2318-2318 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy

-- @@ L2319-2319 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L2320-2320 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L2321-2321 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L2322-2322 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram

-- @@ L2323-2323 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L2324-2324 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L2325-2325 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L2326-2326 verbatim
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner

-- @@ L2327-2327 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels

-- @@ L2328-2328 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L2329-2329 verbatim
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance

-- @@ L2330-2330 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L2332-2351 verbatim
private theorem appendZeroWeight_antitone_metriccodes2_021c7d5c {r : ℕ}
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu) :
    Antitone (appendZeroWeight mu) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
      have hj : j = Fin.last (r + 1) := by
        apply Fin.ext
        have hbound := j.isLt
        change r + 1 ≤ j.val at hij
        change j.val = r + 1
        omega
      subst j
      exact le_rfl
  | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [appendZeroWeight_last, appendZeroWeight_castSucc, zero_le]
      | cast j =>
          have hle : i ≤ j := by simpa only [Fin.castSucc_le_castSucc_iff] using hij
          simpa only [appendZeroWeight_castSucc, ge_iff_le] using hmu hle


-- @@ L2353-2369 verbatim
/-- A physical stabilizer tensor map transported through two appended zero rows in its source
and one in its target. -/
def paddedPhysicalStabilizerTensor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam)) :
    HarmonicYoungSpace (n := n)
        (appendZeroWeight (appendZeroWeight mu)) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) (appendZeroWeight lam)) :=
  (zeroRowTensorIsometryEquiv (n := n + 1) lam).toLinearMap.comp
    (B.comp
      ((appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap.comp
        (appendZeroRowIsometryEquiv
          (n := n) (appendZeroWeight mu)).symm.toLinearMap))


-- @@ L2371-2409 verbatim
theorem paddedPhysicalStabilizerTensor_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (a b : Fin n) :
    (paddedPhysicalStabilizerTensor lam mu B).comp
        (youngAmbientRotation
          (appendZeroWeight (appendZeroWeight mu)) a b) =
      (tensorAmbientRotation (appendZeroWeight lam)
        a.castSucc b.castSucc).comp
          (paddedPhysicalStabilizerTensor lam mu B) := by
  let T := (zeroRowTensorIsometryEquiv (n := n + 1) lam).toLinearMap
  let Z := (appendZeroRowIsometryEquiv (n := n) mu).symm.toLinearMap
  let W := (appendZeroRowIsometryEquiv
    (n := n) (appendZeroWeight mu)).symm.toLinearMap
  apply LinearMap.ext
  intro p
  change T (B (Z (W (youngAmbientRotation
    (appendZeroWeight (appendZeroWeight mu)) a b p)))) =
    tensorAmbientRotation (appendZeroWeight lam)
      a.castSucc b.castSucc (T (B (Z (W p))))
  have hW := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine
      (appendZeroWeight mu) a b) p
  have hZ := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_symm_rotation_intertwine
      mu a b) (W p)
  have hsector := LinearMap.congr_fun (hB a b) (Z (W p))
  have hT := LinearMap.congr_fun
    (zeroRowTensorIsometryEquiv_rotation_intertwine
      lam a.castSucc b.castSucc) (B (Z (W p)))
  exact (congrArg (fun q => T (B (Z q))) hW).trans
    ((congrArg (fun q => T (B q)) hZ).trans
      ((congrArg T hsector).trans hT))


-- @@ L2411-2449 verbatim
theorem appendedFullBranchPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    (appendedFullBranchPieriLower
      lam hdominant hsource hn nu).adjoint.comp
        (paddedPhysicalStabilizerTensor lam mu B) = 0 := by
  have hpadded : Antitone (appendZeroWeight (appendZeroWeight mu)) :=
    appendZeroWeight_antitone_metriccodes2_021c7d5c (appendZeroWeight mu)
      (appendZeroWeight_antitone_metriccodes2_021c7d5c mu hmu)
  apply youngRotationIntertwiner_eq_zero_of_signature_ne
    (by omega)
    (appendZeroWeight (appendZeroWeight mu)) (fullBranchSignature nu)
    hpadded (Ne.symm (appendedRowFullBranchSignature_ne_appendZero lam mu nu))
  intro a b
  exact crossGram_intertwines_of_skew
    (appendedFullBranchPieriLower lam hdominant hsource hn nu)
    (paddedPhysicalStabilizerTensor lam mu B)
    (youngAmbientRotation (fullBranchSignature nu) a b)
    (youngAmbientRotation (appendZeroWeight (appendZeroWeight mu)) a b)
    (tensorAmbientRotation (appendZeroWeight lam) a.castSucc b.castSucc)
    (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
    (tensorAmbientRotation_adjoint (appendZeroWeight lam)
      a.castSucc b.castSucc)
    (appendedFullBranchPieriLower_rotation_intertwine
      lam hdominant hsource hn nu a b)
    (paddedPhysicalStabilizerTensor_rotation_intertwine
      lam mu B hB a b)


-- @@ L2451-2485 verbatim
theorem appendedFullBranchPieriLower_paddedPhysicalStabilizerTensor_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (p : HarmonicYoungSpace (n := n)
      (appendZeroWeight (appendZeroWeight mu)))
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪paddedPhysicalStabilizerTensor lam mu B p,
      appendedFullBranchPieriLower lam hdominant hsource hn nu q⟫_ℝ = 0 := by
  let A := paddedPhysicalStabilizerTensor lam mu B
  let C := appendedFullBranchPieriLower lam hdominant hsource hn nu
  have hzero := LinearMap.congr_fun
    (appendedFullBranchPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
      lam mu hmu B hB hdominant hsource hn nu) p
  have hz : C.adjoint (A p) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hzero
  change ⟪A p, C q⟫_ℝ = 0
  calc
    ⟪A p, C q⟫_ℝ = ⟪C.adjoint (A p), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left C q (A p)).symm
    _ = 0 := by
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _


-- @@ L2487-2529 verbatim
theorem appendedPaddedPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1) :
    (normalizedPaddedPieriLower (n := n + 1)
      (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).adjoint.comp
        (paddedPhysicalStabilizerTensor lam mu B) = 0 := by
  classical
  let source := raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))
  let C := (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap
  let A := paddedPhysicalStabilizerTensor lam mu B
  apply LinearMap.ext
  intro p
  change C.adjoint (A p) = 0
  apply ext_inner_left ℝ
  intro q
  rw [inner_zero_right]
  have hsum := canonicalFullBranch_sum_projection source hn hsource q
  rw [← hsum, sum_inner]
  apply Finset.sum_eq_zero
  intro nu _
  let F := (canonicalFullBranchFibre source hn nu).toLinearMap
  obtain ⟨z, hz⟩ := Submodule.starProjection_apply_mem
    (LinearMap.range F) q
  change F z = (LinearMap.range F).starProjection q at hz
  rw [← hz]
  calc
    ⟪F z, C.adjoint (A p)⟫_ℝ = ⟪C (F z), A p⟫_ℝ :=
      LinearMap.adjoint_inner_right C (F z) (A p)
    _ = ⟪A p, C (F z)⟫_ℝ := real_inner_comm (A p) (C (F z))
    _ = 0 :=
      appendedFullBranchPieriLower_paddedPhysicalStabilizerTensor_inner_eq_zero
        lam mu hmu B hB hdominant hsource hn nu p z


-- @@ L2531-2578 verbatim
theorem paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪B p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdominant
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0 := by
  let C := (normalizedPaddedPieriLower (n := n + 1)
    (appendZeroWeight lam) hdominant (Fin.last (r + 2)) hsource).toLinearMap
  let A := paddedPhysicalStabilizerTensor lam mu B
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let W := appendZeroRowIsometryEquiv (n := n) (appendZeroWeight mu)
  let T := zeroRowTensorIsometryEquiv (n := n + 1) lam
  have hzero := LinearMap.congr_fun
    (appendedPaddedPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
      lam mu hmu B hB hdominant hsource hn) (W (Z p))
  have hz : C.adjoint (T (B p)) = 0 := by
    change C.adjoint (A (W (Z p))) = 0 at hzero
    change C.adjoint (T (B (Z.symm (W.symm (W (Z p)))))) = 0 at hzero
    rw [W.symm_apply_apply, Z.symm_apply_apply] at hzero
    exact hzero
  change ⟪B p, T.symm (C q)⟫_ℝ = 0
  calc
    ⟪B p, T.symm (C q)⟫_ℝ =
      ⟪T (B p), T (T.symm (C q))⟫_ℝ :=
        (T.inner_map_map (B p) (T.symm (C q))).symm
    _ = ⟪T (B p), C q⟫_ℝ := by
      rw [LinearIsometryEquiv.apply_symm_apply]
    _ = ⟪C.adjoint (T (B p)), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left C q (T (B p))).symm
    _ = 0 := by
      rw [hz, young_inner_eq_polynomialInner,
        SpherePacking.Fischer.polynomialInner_comm]
      exact SpherePacking.fischer_polynomialInner_zero_right _ _


-- @@ L2580-2608 verbatim
theorem paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransverseNegativeSector_orthogonal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪normalizedGTTransverseNegativeSector
        lam mu kappa row hnu hnuGram hfinite hraise p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdominant
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0 := by
  apply paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
    lam mu hfinite.antitone_ambient
    (normalizedGTTransverseNegativeSector
      lam mu kappa row hnu hnuGram hfinite hraise).toLinearMap
    (normalizedGTTransverseNegativeSector_rotation_intertwine
      lam mu kappa row hnu hnuGram hfinite hraise)
    hdominant hsource hn p q


-- @@ L2610-2637 verbatim
theorem paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransversePositiveSector_orthogonal
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n + 1)
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    ⟪normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdominant
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0 := by
  apply paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
    lam mu (interlaces_antitone_stabilizer hmu)
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap
    (normalizedGTTransversePositiveSector_rotation_intertwine
      lam mu nu row hmunu hmu hnu hnuGram)
    hdominant hsource hn p q


-- @@ L2639-2639 verbatim
end AllRankGTTransverseAppendedChannelOrthogonality


-- @@ L2641-2641 verbatim
end


-- @@ L2643-2643 verbatim
section



-- @@ L2646-2646 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L2648-2648 verbatim
namespace AllRankGTTransverseSectorSignedSpan


-- @@ L2650-2650 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L2651-2651 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L2652-2652 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L2653-2653 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L2654-2654 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral

-- @@ L2655-2655 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan

-- @@ L2656-2656 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining

-- @@ L2657-2657 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L2658-2658 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport

-- @@ L2659-2659 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality

-- @@ L2660-2660 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality

-- @@ L2661-2661 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L2662-2662 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L2663-2663 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L2664-2664 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L2665-2665 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L2666-2666 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels

-- @@ L2667-2667 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

-- @@ L2668-2668 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L2669-2669 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L2671-2696 verbatim
theorem gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (happended :
      ∀ (hsource : Antitone
          (raiseWeight (appendZeroWeight lam) (Fin.last (r + 1))))
        (q : HarmonicYoungSpace (n := n)
          (raiseWeight (appendZeroWeight lam) (Fin.last (r + 1)))),
        ⟪v, physicalPaddedPieriChannel hn lam hdom
          (Sum.inl ⟨Fin.last (r + 1), hsource⟩) q⟫_ℝ = 0) :
    v ∈ gtSignedEigenvectorSpan (n := n) lam := by
  apply gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
    hn lam hdom v
  intro i hnot q
  cases i with
  | inl row =>
      rcases row with ⟨row, hsource⟩
      change ¬ row ≠ Fin.last (r + 1) at hnot
      have hrow : row = Fin.last (r + 1) := Classical.byContradiction hnot
      subst row
      exact happended hsource q
  | inr row =>
      exact False.elim (hnot trivial)


-- @@ L2698-2722 verbatim
theorem gtPhysicalStabilizerIntertwiner_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdom : Antitone (appendZeroWeight lam))
    (p : HarmonicYoungSpace (n := n) mu) :
    B p ∈ gtSignedEigenvectorSpan (n := n + 1) lam := by
  apply gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    (by omega) lam hdom (B p)
  intro hsource q
  change
    ⟪B p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdom
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0
  exact
    paddedOrthogonalTensorPieriChannel_appended_stabilizerIntertwiner_orthogonal
      lam mu hmu B hB hdom hsource hn p q


-- @@ L2724-2724 verbatim
end AllRankGTTransverseSectorSignedSpan


-- @@ L2726-2726 verbatim
end


-- @@ L2728-2728 verbatim
section



-- @@ L2731-2731 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L2733-2733 verbatim
namespace AllRankGTNormalizedTransverseCharacteristicAnnihilation


-- @@ L2735-2735 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L2736-2736 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L2737-2737 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L2738-2738 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L2739-2739 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral

-- @@ L2740-2740 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L2741-2741 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport

-- @@ L2742-2742 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality

-- @@ L2743-2743 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L2744-2744 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSectorSignedSpan

-- @@ L2745-2745 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L2746-2746 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L2747-2747 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L2748-2748 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L2749-2749 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality

-- @@ L2750-2750 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

-- @@ L2751-2751 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels

-- @@ L2752-2752 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L2754-2784 verbatim
theorem normalizedGTTransverseNegativeSector_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise p ∈
        gtSignedEigenvectorSpan (n := n + 1) lam := by
  let hdom : Antitone (appendZeroWeight lam) :=
    appendZeroWeight_antitone lam hnu.antitone_ambient
  apply gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    (by omega) lam hdom
    (normalizedGTTransverseNegativeSector
      lam mu kappa row hnu hnuGram hfinite hraise p)
  intro hsource q
  change
    ⟪normalizedGTTransverseNegativeSector
        lam mu kappa row hnu hnuGram hfinite hraise p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdom
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0
  exact
    paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransverseNegativeSector_orthogonal
      lam mu kappa row hnu hnuGram hfinite hraise hdom hsource hn p q


-- @@ L2786-2815 verbatim
theorem normalizedGTTransversePositiveSector_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransversePositiveSector lam mu nu row
      hmunu hmu hnu hnuGram p ∈
        gtSignedEigenvectorSpan (n := n + 1) lam := by
  let hdom : Antitone (appendZeroWeight lam) :=
    appendZeroWeight_antitone lam hmu.antitone_ambient
  apply gtSignedEigenvectorSpan_mem_of_appendedPhysicalPaddedPieriChannel_orthogonal
    (by omega) lam hdom
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram p)
  intro hsource q
  change
    ⟪normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram p,
      zeroRowTransportPaddedPieriChannel lam
        (paddedOrthogonalTensorPieriChannel (by omega)
          (appendZeroWeight lam) hdom
          (Sum.inl ⟨Fin.last (r + 2), hsource⟩)) q⟫_ℝ = 0
  exact
    paddedOrthogonalTensorPieriChannel_appended_normalizedGTTransversePositiveSector_orthogonal
      lam mu nu row hmunu hmu hnu hnuGram hdom hsource hn p q


-- @@ L2817-2834 verbatim
theorem normalizedGTTransverseNegativeSector_characteristic_aeval_eq_zero
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise p) = 0 :=
  gtSignedEigenvectorSpan_le_characteristic_ker lam
    (normalizedGTTransverseNegativeSector_mem_gtSignedEigenvectorSpan
      hn lam mu kappa row hnu hnuGram hfinite hraise p)


-- @@ L2836-2852 verbatim
theorem normalizedGTTransversePositiveSector_characteristic_aeval_eq_zero
    {r n : ℕ} (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (normalizedGTTransversePositiveSector lam mu nu row
          hmunu hmu hnu hnuGram p) = 0 :=
  gtSignedEigenvectorSpan_le_characteristic_ker lam
    (normalizedGTTransversePositiveSector_mem_gtSignedEigenvectorSpan
      hn lam mu nu row hmunu hmu hnu hnuGram p)


-- @@ L2854-2854 verbatim
end AllRankGTNormalizedTransverseCharacteristicAnnihilation


-- @@ L2856-2856 verbatim
end


-- @@ L2858-2858 verbatim
section



-- @@ L2861-2861 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L2863-2863 verbatim
namespace AllRankGTWallTransverseCompression


-- @@ L2865-2865 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L2866-2866 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L2867-2867 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L2868-2868 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L2869-2869 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L2870-2870 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L2871-2871 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L2872-2872 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L2873-2873 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L2874-2874 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L2875-2875 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L2876-2876 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L2878-2884 verbatim
private def gtWallFullBranchOfSignature {r : ℕ}
    (lam signature : Fin (r + 1) → ℕ)
    (hupper : ∀ i, signature i ≤ lam i)
    (hlower : ∀ i : Fin r, lam i.succ ≤ signature i.castSucc) :
    FullBranchWeight lam :=
  ⟨fun i => ⟨signature i, Nat.lt_succ_of_le (hupper i)⟩,
    fun i => hlower i⟩


-- @@ L2886-2905 verbatim
theorem exists_fullBranchSignature_wall_of_last_pos {r : ℕ}
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    ∃ nu : FullBranchWeight lam,
      fullBranchSignature nu =
        raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)) := by
  let signature : Fin (r + 2) → ℕ :=
    raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))
  have hupper : ∀ i, signature i ≤ lam i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [signature, raiseWeight] using
        (show 1 ≤ lam (Fin.last (r + 1)) by omega)
    · simpa [signature, raiseWeight, Fin.castSucc_ne_last] using (h j).1
  have hlower : ∀ i : Fin (r + 1),
      lam i.succ ≤ signature i.castSucc := by
    intro i
    simpa [signature, raiseWeight, Fin.castSucc_ne_last] using (h i).2
  exact ⟨gtWallFullBranchOfSignature lam signature hupper hlower, rfl⟩


-- @@ L2907-2914 verbatim
/-- A chosen full branch whose signature is the appended stabilizer weight raised in its last
coordinate. -/
def gtWallFullBranch
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hlast : 0 < lam (Fin.last (r + 1))) : FullBranchWeight lam :=
  Classical.choose (exists_fullBranchSignature_wall_of_last_pos
    lam mu h hlast)


-- @@ L2916-2923 verbatim
@[simp] theorem gtWallFullBranch_signature
    {r : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    fullBranchSignature (gtWallFullBranch lam mu h hlast) =
      raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)) :=
  Classical.choose_spec
    (exists_fullBranchSignature_wall_of_last_pos lam mu h hlast)


-- @@ L2925-2935 verbatim
/-- The canonical full-branch fibre corresponding to the wall signature. -/
def gtWallCanonicalFullBranchFibre
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    HarmonicYoungSpace (n := n)
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam :=
  (gtWallFullBranch_signature lam mu h hlast) ▸
    canonicalFullBranchFibre lam hn (gtWallFullBranch lam mu h hlast)


-- @@ L2937-2950 verbatim
/-- The tensor isometry combining the transverse Euclidean inclusion with the canonical wall
fibre. -/
def gtTransverseWallTensorEmbedding
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n)
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n)
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast)


-- @@ L2952-2969 verbatim
/-- The transverse wall-sector map obtained by composing Clebsch raising with the wall tensor
embedding. -/
def gtTransverseWallSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (gtTransverseWallTensorEmbedding
    lam mu h hn hlast).toLinearMap.comp
      ((youngClebschRaise
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (appendZeroWeight mu)
        (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1))).comp
          (appendZeroRowIsometryEquiv mu).toLinearMap)


-- @@ L2971-2971 verbatim
end AllRankGTWallTransverseCompression


-- @@ L2973-2973 verbatim
end


-- @@ L2975-2975 verbatim
section



-- @@ L2978-2978 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L2980-2980 verbatim
namespace AllRankGTWallSectorGram


-- @@ L2982-2982 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L2983-2983 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L2984-2984 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalEdgeRaisingGram

-- @@ L2985-2985 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

-- @@ L2986-2986 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L2987-2987 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

-- @@ L2988-2988 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L2989-2989 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L2990-2990 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L2992-2997 verbatim
/-- The gt wall sector gram used in the spherical-code argument. -/
def gtWallSectorGram {r : ℕ} (n : ℕ) (mu : Fin (r + 1) → ℕ) : ℝ :=
  internalRowLowerGramScalar
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) *
    weylEdgeRatio n (appendZeroWeight mu) (Fin.last (r + 1))


-- @@ L2999-3012 verbatim
theorem gtWallZeroRow_finiteInterlacing
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1) :
    FiniteInterlacing n (appendZeroWeight mu) mu := by
  refine ⟨by omega, ?_⟩
  intro row
  constructor
  · simp only [appendZeroWeight_castSucc, Std.le_refl]
  · refine Fin.lastCases ?_ (fun row => ?_) row
    · simp only [Fin.succ_last, Nat.succ_eq_add_one, appendZeroWeight_last, zero_le]
    · simpa only [← Fin.castSucc_succ, appendZeroWeight_castSucc] using
        (interlaces_antitone_stabilizer h)
          (Fin.castSucc_le_succ row)


-- @@ L3014-3037 verbatim
theorem gtWallRaisedZeroRow_finiteInterlacing
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    FiniteInterlacing n
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) mu := by
  have hmuLast : 0 < mu (Fin.last r) := by
    have hbound := (h (Fin.last r)).2
    have hbound' : lam (Fin.last (r + 1)) ≤ mu (Fin.last r) := by
      simpa only [Fin.succ_last, Nat.succ_eq_add_one] using hbound
    omega
  refine ⟨by omega, ?_⟩
  intro row
  constructor
  · simp only [raiseWeight, appendZeroWeight_last, zero_add, ne_eq, Fin.castSucc_ne_last,
      not_false_eq_true, Function.update_of_ne, appendZeroWeight_castSucc, Std.le_refl]
  · refine Fin.lastCases ?_ (fun row => ?_) row
    · simpa only [raiseWeight, appendZeroWeight_last, zero_add, Fin.succ_last, Nat.succ_eq_add_one,
        Function.update_self] using (show 1 ≤ mu (Fin.last r) by omega)
    · simpa only [raiseWeight, appendZeroWeight_last, zero_add, ← Fin.castSucc_succ, ne_eq,
      Fin.castSucc_ne_last,
        not_false_eq_true, Function.update_of_ne, appendZeroWeight_castSucc] using
        (interlaces_antitone_stabilizer h) (Fin.castSucc_le_succ row)


-- @@ L3039-3056 verbatim
theorem gtWallSectorGram_pos
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    0 < gtWallSectorGram n mu := by
  obtain ⟨raisingGram, hpositive, _, heq⟩ :=
    canonicalEdgeRaisingGram (appendZeroWeight mu) mu
      (Fin.last (r + 1))
      (gtWallZeroRow_finiteInterlacing lam mu h hn)
      (gtWallRaisedZeroRow_finiteInterlacing lam mu h hn hlast)
  change 0 <
    internalRowLowerGramScalar
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1)) *
      weylEdgeRatio n (appendZeroWeight mu) (Fin.last (r + 1))
  rw [← heq]
  exact hpositive


-- @@ L3058-3105 verbatim
theorem gtTransverseWallSector_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseWallSector lam mu h hn hlast p,
      gtTransverseWallSector lam mu h hn hlast q⟫_ℝ =
      gtWallSectorGram n mu * ⟪p, q⟫_ℝ := by
  obtain ⟨raisingGram, _, hinner, heq⟩ :=
    canonicalEdgeRaisingGram (appendZeroWeight mu) mu
      (Fin.last (r + 1))
      (gtWallZeroRow_finiteInterlacing lam mu h hn)
      (gtWallRaisedZeroRow_finiteInterlacing lam mu h hn hlast)
  change
    ⟪gtTransverseWallTensorEmbedding lam mu h hn hlast
        (youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu p)),
      gtTransverseWallTensorEmbedding lam mu h hn hlast
        (youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu q))⟫_ℝ = _
  calc
    _ = ⟪youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu p),
        youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu q)⟫_ℝ :=
      (gtTransverseWallTensorEmbedding lam mu h hn hlast).inner_map_map _ _
    _ = raisingGram *
          ⟪appendZeroRowIsometryEquiv mu p,
            appendZeroRowIsometryEquiv mu q⟫_ℝ := hinner _ _
    _ = raisingGram * ⟪p, q⟫_ℝ :=
      congrArg (fun x : ℝ => raisingGram * x)
        ((appendZeroRowIsometryEquiv mu).inner_map_map p q)
    _ = gtWallSectorGram n mu * ⟪p, q⟫_ℝ := by
      rw [heq]
      rfl


-- @@ L3107-3107 verbatim
end AllRankGTWallSectorGram


-- @@ L3109-3109 verbatim
end


-- @@ L3111-3111 verbatim
section



-- @@ L3114-3114 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L3116-3116 verbatim
namespace AllRankGTWallTransverseCompression


-- @@ L3118-3118 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L3119-3119 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L3120-3120 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L3121-3121 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L3122-3122 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L3123-3123 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis

-- @@ L3124-3124 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift

-- @@ L3125-3125 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L3126-3126 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression

-- @@ L3127-3127 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression

-- @@ L3128-3128 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L3129-3129 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L3130-3130 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L3131-3131 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L3132-3132 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L3133-3133 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L3134-3134 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L3136-3149 verbatim
theorem stabilizerIsometry_rotation_adjoint_compression
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (hF : ∀ a b : Fin n,
      F.toLinearMap.comp (youngAmbientRotation nu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap)
    (a b : Fin n) :
    F.toLinearMap.adjoint.comp
      ((youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap) =
      youngAmbientRotation nu a b := by
  rw [← hF a b, ← LinearMap.comp_assoc,
    F.adjoint_comp_self', LinearMap.id_comp]


-- @@ L3151-3162 verbatim
/-- The tensor isometry combining the transverse Euclidean inclusion with a supplied stabilizer
isometry. -/
def transverseTensorEmbeddingOfStabilizerIsometry
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n) F


-- @@ L3164-3190 verbatim
theorem transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (a b : Fin (n + 1)) :
    (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      TensorProduct.map
        ((gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
          ((euclideanAmbientRotation a b).comp
            (gtTransverseEuclideanIsometry n).toLinearMap))
        (F.toLinearMap.adjoint.comp
          ((youngAmbientRotation lam a b).comp F.toLinearMap)) := by
  change
    (TensorProduct.map
      (gtTransverseEuclideanIsometry n).toLinearMap F.toLinearMap).adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (TensorProduct.map
            (gtTransverseEuclideanIsometry n).toLinearMap F.toLinearMap)) = _
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  rfl


-- @@ L3192-3292 verbatim
theorem transverseTensorEmbeddingOfStabilizerIsometry_mixedRotation
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (hF : ∀ a b : Fin n,
      F.toLinearMap.comp (youngAmbientRotation nu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      gtMixedRotationOperator (n := n) nu := by
  let I := (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap
  have htangential (a b : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc b.castSucc)
            (youngAmbientRotation lam a.castSucc b.castSucc)).comp I) =
        TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation nu a b) := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc b.castSucc)
            (youngAmbientRotation lam a.castSucc b.castSucc)).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = _
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_rotation_adjoint_compression,
      stabilizerIsometry_rotation_adjoint_compression lam nu F hF]
  have hcross (a : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc (Fin.last n))
            (youngAmbientRotation lam a.castSucc (Fin.last n))).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation a.castSucc (Fin.last n))
            (youngAmbientRotation lam a.castSucc (Fin.last n))).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_cross_rotation_compression]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hcrossSwap (a : Fin n) :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) a.castSucc)
            (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) a.castSucc)
            (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm,
      gtTransverseEuclideanIsometry_cross_rotation_compression_swap]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hlast :
      I.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) (Fin.last n))
            (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp I) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
          ((TensorProduct.map
            (euclideanAmbientRotation (Fin.last n) (Fin.last n))
            (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp
            (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) = 0
    rw [transverseTensorEmbeddingOfStabilizerIsometry_rotationTerm]
    have hzero : euclideanAmbientRotation (Fin.last n) (Fin.last n) = 0 := by
      apply LinearMap.ext
      intro v
      simp only [euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, sub_self,
        LinearMap.zero_apply]
    rw [hzero]
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, TensorProduct.map_zero_left]
  unfold gtMixedRotationOperator
  change I.adjoint.comp ((∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
    TensorProduct.map (euclideanAmbientRotation a b)
      (youngAmbientRotation lam a b)).comp I) = _
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential' (a b : Fin n) :=
    LinearMap.congr_fun (htangential a b) (v ⊗ₜ[ℝ] p)
  have hcross' (a : Fin n) :=
    LinearMap.congr_fun (hcross a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap' (a : Fin n) :=
    LinearMap.congr_fun (hcrossSwap a) (v ⊗ₜ[ℝ] p)
  have hlast' := LinearMap.congr_fun hlast (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at htangential' hcross' hcrossSwap' hlast'
  simp only [htangential', hcross', hcrossSwap', hlast',
    Finset.sum_const_zero, add_zero]


-- @@ L3294-3316 verbatim
theorem transverseTensorEmbeddingOfStabilizerIsometry_relativeCasimir
    {s r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (nu : Fin (s + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) nu →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (hF : ∀ a b : Fin n,
      F.toLinearMap.comp (youngAmbientRotation nu a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry lam nu F).toLinearMap) =
      gtStabilizerShiftedRelativeCasimir nu := by
  rw [gtRelativeCasimir_eq_scalar_sub_mixed (n := n + 1) lam,
    gtStabilizerShiftedRelativeCasimir,
    gtRelativeCasimir_eq_scalar_sub_mixed (n := n) nu]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp,
    LinearMap.id_comp, LinearMap.comp_sub, LinearMap.comp_smul]
  rw [(transverseTensorEmbeddingOfStabilizerIsometry
    lam nu F).adjoint_comp_self',
    transverseTensorEmbeddingOfStabilizerIsometry_mixedRotation
      lam nu F hF]
  norm_num
  module


-- @@ L3318-3324 verbatim
theorem stabilizerShift_appendZeroWeight_last_add_half_eq_wall
    {r n : ℕ} (mu : Fin (r + 1) → ℕ) :
    stabilizerShift (n + 1) (appendZeroWeight mu) (Fin.last (r + 1)) +
        (1 / 2 : ℝ) = wallShift (n + 1) (r + 1) := by
  simp only [stabilizerShift, wallShift, appendZeroWeight_last,
    Nat.cast_zero, Nat.cast_add, Nat.cast_one, Fin.val_last]
  ring


-- @@ L3326-3358 verbatim
theorem gtStabilizerShiftedRelativeCasimir_terminal_youngClebschRaise
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (p : HarmonicYoungSpace (n := n) (appendZeroWeight mu)) :
    gtStabilizerShiftedRelativeCasimir
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (youngClebschRaise
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (appendZeroWeight mu)
        (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1)) p) =
      (-wallShift (n + 1) (r + 1)) •
        youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1)) p := by
  rw [gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
    (appendZeroWeight mu) (Fin.last (r + 1))
    (youngClebschRaise
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)))
    (fun a b => youngClebschRaise_rotation_intertwine
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) a b) p]
  simp only
    [HigherYoungAllRankGTArrowheadSchurComplement.gtStabilizerArrowheadNode_neg]
  congr 1
  linarith [stabilizerShift_appendZeroWeight_last_add_half_eq_wall
    (n := n) mu]


-- @@ L3360-3378 verbatim
@[simp] theorem gtTransverseWallTensorEmbedding_tmul
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n)
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))) :
    gtTransverseWallTensorEmbedding lam mu h hn hlast (v ⊗ₜ[ℝ] p) =
      gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
        gtWallCanonicalFullBranchFibre lam mu h hn hlast p := by
  change
    TensorProduct.map
      (gtTransverseEuclideanIsometry n).toLinearMap
      (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap
      (v ⊗ₜ[ℝ] p) = _
  exact TensorProduct.map_tmul
    (gtTransverseEuclideanIsometry n).toLinearMap
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap v p


-- @@ L3380-3400 verbatim
theorem gtTransverseWallTensorEmbedding_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n)
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))))
    (q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseWallTensorEmbedding lam mu h hn hlast x,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0 := by
  induction x with
  | tmul v p =>
      rw [gtTransverseWallTensorEmbedding_tmul,
        canonicalGelfandTsetlinAxisTensor_apply,
        TensorProduct.inner_tmul,
        gtTransverseEuclideanIsometry_orthogonal_last]
      simp only [canonicalGelfandTsetlinFibre_apply, zero_mul]
  | add x y hx hy =>
      rw [map_add, inner_add_left, hx, hy, zero_add]


-- @@ L3402-3417 verbatim
theorem gtTransverseWallSector_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪gtTransverseWallSector lam mu h hn hlast p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0 := by
  exact gtTransverseWallTensorEmbedding_axis_inner_eq_zero
    lam mu h hn hlast hgram
    (youngClebschRaise
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu p)) q


-- @@ L3419-3432 verbatim
private theorem transportedFullBranchFibre_rotation_intertwine_metriccodes2_5c2d5a44
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (nu : FullBranchWeight lam)
    (sigma : Fin (r + 2) → ℕ)
    (hsigma : fullBranchSignature nu = sigma)
    (a b : Fin n) :
    let F : HarmonicYoungSpace (n := n) sigma →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam :=
        hsigma ▸ canonicalFullBranchFibre lam hn nu
    F.toLinearMap.comp (youngAmbientRotation sigma a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp F.toLinearMap := by
  subst sigma
  exact canonicalFullBranchFibre_rotation_intertwine lam hn nu a b


-- @@ L3434-3448 verbatim
theorem gtWallCanonicalFullBranchFibre_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap.comp
      (youngAmbientRotation
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap :=
  transportedFullBranchFibre_rotation_intertwine_metriccodes2_5c2d5a44 lam hn
    (gtWallFullBranch lam mu h hlast)
    (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (gtWallFullBranch_signature lam mu h hlast) a b


-- @@ L3450-3464 verbatim
theorem gtTransverseWallTensorEmbedding_relativeCasimir_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap) =
      gtStabilizerShiftedRelativeCasimir
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) := by
  exact transverseTensorEmbeddingOfStabilizerIsometry_relativeCasimir
    lam (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast)
    (gtWallCanonicalFullBranchFibre_rotation_intertwine
      lam mu h hn hlast)


-- @@ L3466-3495 verbatim
theorem gtTransverseWallSector_relativeCasimir_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransverseWallSector lam mu h hn hlast p)) =
      (-wallShift (n + 1) (r + 1)) •
        youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1))
          (appendZeroRowIsometryEquiv mu p) := by
  unfold gtTransverseWallSector
  change
    ((gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap))
        (youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1))
          (appendZeroRowIsometryEquiv mu p)) = _
  rw [gtTransverseWallTensorEmbedding_relativeCasimir_compression]
  exact gtStabilizerShiftedRelativeCasimir_terminal_youngClebschRaise
    mu (appendZeroRowIsometryEquiv mu p)


-- @@ L3497-3497 verbatim
end AllRankGTWallTransverseCompression


-- @@ L3499-3499 verbatim
end


-- @@ L3501-3501 verbatim
section



-- @@ L3504-3504 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L3506-3506 verbatim
namespace AllRankGTWallSectorIsometry


-- @@ L3508-3508 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L3509-3509 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L3510-3510 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L3511-3511 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram

-- @@ L3512-3512 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

-- @@ L3513-3513 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L3514-3514 verbatim
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability


-- @@ L3516-3529 verbatim
/-- The transverse wall-sector map normalized by its positive Gram scalar to a linear isometry. -/
def normalizedGTTransverseWallSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (gtTransverseWallSector lam mu h hn hlast)
    (gtWallSectorGram n mu)
    (gtWallSectorGram_pos lam mu h hn hlast)
    (gtTransverseWallSector_inner lam mu h hn hlast)


-- @@ L3531-3538 verbatim
@[simp] theorem normalizedGTTransverseWallSector_toLinearMap
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap =
      (Real.sqrt (gtWallSectorGram n mu))⁻¹ •
        gtTransverseWallSector lam mu h hn hlast := rfl


-- @@ L3540-3548 verbatim
@[simp] theorem normalizedGTTransverseWallSector_apply
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransverseWallSector lam mu h hn hlast p =
      (Real.sqrt (gtWallSectorGram n mu))⁻¹ •
        gtTransverseWallSector lam mu h hn hlast p := rfl


-- @@ L3550-3565 verbatim
theorem normalizedGTTransverseWallSector_axis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪normalizedGTTransverseWallSector lam mu h hn hlast p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0 := by
  change
    ⟪(Real.sqrt (gtWallSectorGram n mu))⁻¹ •
        gtTransverseWallSector lam mu h hn hlast p,
      canonicalGelfandTsetlinAxisTensor lam mu h hgram q⟫_ℝ = 0
  rw [real_inner_smul_left,
    gtTransverseWallSector_axis_inner_eq_zero
      lam mu h hn hlast hgram p q, mul_zero]


-- @@ L3567-3580 verbatim
theorem canonicalAxis_inner_normalizedGTTransverseWallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
      normalizedGTTransverseWallSector lam mu h hn hlast q⟫_ℝ = 0 := by
  exact (real_inner_comm
    (canonicalGelfandTsetlinAxisTensor lam mu h hgram p)
    (normalizedGTTransverseWallSector lam mu h hn hlast q)).symm.trans
      (normalizedGTTransverseWallSector_axis_inner_eq_zero
        lam mu h hn hlast hgram q p)


-- @@ L3582-3582 verbatim
end AllRankGTWallSectorIsometry


-- @@ L3584-3584 verbatim
end


-- @@ L3586-3586 verbatim
section



-- @@ L3589-3589 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L3591-3591 verbatim
namespace AllRankGTNormalizedWallCharacteristicAnnihilation


-- @@ L3593-3593 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L3594-3594 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L3595-3595 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral

-- @@ L3596-3596 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L3597-3597 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L3598-3598 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSectorSignedSpan

-- @@ L3599-3599 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression

-- @@ L3600-3600 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry

-- @@ L3601-3601 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

-- @@ L3602-3602 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L3603-3603 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L3604-3604 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L3605-3605 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L3606-3606 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L3607-3607 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L3608-3608 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L3609-3609 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

-- @@ L3610-3610 verbatim
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance

-- @@ L3611-3611 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L3613-3625 verbatim
private theorem wallFullBranchFibre_rotation_intertwine_metriccodes2_3a89272e
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap.comp
      (youngAmbientRotation
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) a b) =
      (youngAmbientRotation lam a.castSucc b.castSucc).comp
        (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap :=
  gtWallCanonicalFullBranchFibre_rotation_intertwine
    lam mu h hn hlast a b


-- @@ L3627-3667 verbatim
private theorem wallTensorEmbedding_rotation_intertwine_metriccodes2_3a89272e
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.comp
        (tensorAmbientRotation
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x with
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul v p =>
      have hE := LinearMap.congr_fun
        (gtTransverseEuclideanIsometry_rotation_intertwine n a b) v
      have hF := LinearMap.congr_fun
        (wallFullBranchFibre_rotation_intertwine_metriccodes2_3a89272e
          lam mu h hn hlast a b) p
      simp only [LinearMap.comp_apply] at hE hF
      change
        gtTransverseEuclideanIsometry n
            (euclideanAmbientRotation a b v) ⊗ₜ[ℝ]
          gtWallCanonicalFullBranchFibre lam mu h hn hlast p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          gtWallCanonicalFullBranchFibre lam mu h hn hlast
            (youngAmbientRotation
              (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1))) a b p) =
        euclideanAmbientRotation a.castSucc b.castSucc
            (gtTransverseEuclideanIsometry n v) ⊗ₜ[ℝ]
          gtWallCanonicalFullBranchFibre lam mu h hn hlast p +
        gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
          youngAmbientRotation lam a.castSucc b.castSucc
            (gtWallCanonicalFullBranchFibre lam mu h hn hlast p)
      exact congrArg₂ (· + ·)
        (congrArg (fun w => w ⊗ₜ[ℝ]
          gtWallCanonicalFullBranchFibre lam mu h hn hlast p) hE)
        (congrArg (fun w => gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ] w) hF)


-- @@ L3669-3716 verbatim
private theorem wallSector_rotation_intertwine_metriccodes2_3a89272e
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (gtTransverseWallSector lam mu h hn hlast).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseWallSector lam mu h hn hlast) := by
  apply LinearMap.ext
  intro p
  have hzero := LinearMap.congr_fun
    (appendZeroRowIsometryEquiv_rotation_intertwine mu a b) p
  have hraise := LinearMap.congr_fun
    (youngClebschRaise_rotation_intertwine
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) a b)
    (appendZeroRowIsometryEquiv mu p)
  have htensor := LinearMap.congr_fun
    (wallTensorEmbedding_rotation_intertwine_metriccodes2_3a89272e
      lam mu h hn hlast a b)
    (youngClebschRaise
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1)) (appendZeroRowIsometryEquiv mu p))
  simp only [LinearMap.comp_apply] at hzero hraise htensor ⊢
  change
    gtTransverseWallTensorEmbedding lam mu h hn hlast
        (youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1))
          (appendZeroRowIsometryEquiv mu (youngAmbientRotation mu a b p))) = _
  exact (congrArg (fun q =>
    gtTransverseWallTensorEmbedding lam mu h hn hlast
      (youngClebschRaise
        (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (appendZeroWeight mu)
        (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
        (Fin.last (r + 1)) q)) hzero).trans
    ((congrArg
      (gtTransverseWallTensorEmbedding lam mu h hn hlast) hraise).trans
      htensor)


-- @@ L3718-3730 verbatim
theorem normalizedGTTransverseWallSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (a b : Fin n) :
    (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap.comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap := by
  rw [normalizedGTTransverseWallSector_toLinearMap,
    LinearMap.smul_comp, LinearMap.comp_smul,
    wallSector_rotation_intertwine_metriccodes2_3a89272e lam mu h hn hlast a b]


-- @@ L3732-3749 verbatim
theorem normalizedGTTransverseWallSector_mem_gtSignedEigenvectorSpan
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    normalizedGTTransverseWallSector lam mu h hn hlast p ∈
      gtSignedEigenvectorSpan (n := n + 1) lam := by
  have hdominant : Antitone (appendZeroWeight lam) :=
    (fullBranchSignature_interlaces_appendZeroWeight lam
      (fullBranchOfInterlaces mu h)).antitone_ambient
  exact gtPhysicalStabilizerIntertwiner_mem_gtSignedEigenvectorSpan
    hstable lam mu (interlaces_antitone_stabilizer h)
    (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap
    (normalizedGTTransverseWallSector_rotation_intertwine
      lam mu h hn hlast)
    hdominant p


-- @@ L3751-3763 verbatim
theorem normalizedGTTransverseWallSector_characteristic_aeval_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
      (gtChannelCharacteristicPolynomial (n + 1) lam)
      (normalizedGTTransverseWallSector lam mu h hn hlast p) = 0 :=
  gtSignedEigenvectorSpan_le_characteristic_ker lam
    (normalizedGTTransverseWallSector_mem_gtSignedEigenvectorSpan
      lam mu h hn hstable hlast p)


-- @@ L3765-3765 verbatim
end AllRankGTNormalizedWallCharacteristicAnnihilation


-- @@ L3767-3767 verbatim
end


-- @@ L3769-3769 verbatim
section



-- @@ L3772-3772 verbatim
namespace AllRankGTPresentWallSignedNodeSeparation


-- @@ L3774-3774 verbatim
open MetricCodes.Spherical.HigherChannel


-- @@ L3776-3787 verbatim
theorem wallShift_lt_ambientShift_of_last_pos
    {r n : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ}
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (row : Fin (r + 2)) :
    wallShift (n + 1) (r + 1) < ambientShift (n + 1) lam row := by
  have hpositive : (0 : ℝ) < (lam (Fin.last (r + 1)) : ℝ) := by
    exact_mod_cast hlast
  have horder := hfinite.ambientShift_strictAnti.antitone row.le_last
  rw [ambientShift_last] at horder
  linarith


-- @@ L3789-3806 verbatim
theorem presentWall_ne_signedAmbientNode
    {r n : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ}
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (z : Fin (r + 2) × Bool) :
    -(wallShift (n + 1) (r + 1)) ≠
      signedNode (ambientShift (n + 1) lam) z := by
  rcases z with ⟨row, sign⟩
  cases sign with
  | false =>
      simp only [signedNode, Bool.false_eq_true, ↓reduceIte]
      intro heq
      linarith [wallShift_lt_ambientShift_of_last_pos hfinite hlast row]
  | true =>
      simp only [signedNode, ↓reduceIte]
      intro heq
      linarith [hfinite.wallShift_pos, hfinite.ambientShift_pos row]


-- @@ L3808-3808 verbatim
end AllRankGTPresentWallSignedNodeSeparation


-- @@ L3810-3810 verbatim
end


-- @@ L3812-3812 verbatim
section



-- @@ L3815-3815 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L3817-3817 verbatim
namespace AllRankGTTransverseFullBranchDecomposition


-- @@ L3819-3819 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L3820-3820 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L3821-3821 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness

-- @@ L3822-3822 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L3823-3823 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness


-- @@ L3825-3837 verbatim
/-- The tensor isometry induced by a canonical full-branch fibre while retaining the Euclidean
tensor factor. -/
def gtFullTransverseInternalEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu)) →ₗᵢ[ℝ]
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry
    (LinearIsometry.id :
      SpherePacking.Euclidean n →ₗᵢ[ℝ] SpherePacking.Euclidean n)
    (canonicalFullBranchFibre lam hn mu)


-- @@ L3839-3845 verbatim
@[simp] theorem gtFullTransverseInternalEmbedding_tmul {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam)
    (v : SpherePacking.Euclidean n)
    (p : HarmonicYoungSpace (n := n) (fullBranchSignature mu)) :
    gtFullTransverseInternalEmbedding lam hn mu (v ⊗ₜ[ℝ] p) =
      v ⊗ₜ[ℝ] canonicalFullBranchFibre lam hn mu p := rfl


-- @@ L3847-3875 verbatim
theorem gtFullTransverseInternalEmbedding_orthogonal {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (y : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullTransverseInternalEmbedding lam hn mu x,
      gtFullTransverseInternalEmbedding lam hn nu y⟫_ℝ = 0 := by
  induction x with
  | tmul v p =>
      induction y with
      | tmul w q =>
          rw [gtFullTransverseInternalEmbedding_tmul,
            gtFullTransverseInternalEmbedding_tmul,
            TensorProduct.inner_tmul]
          calc
            ⟪v, w⟫_ℝ *
                ⟪canonicalFullBranchFibre lam hn mu p,
                  canonicalFullBranchFibre lam hn nu q⟫_ℝ =
              ⟪v, w⟫_ℝ * 0 :=
                congrArg (fun z : ℝ => ⟪v, w⟫_ℝ * z)
                  (canonicalFullBranchFibre_orthogonal
                    lam hn mu nu hne p q)
            _ = 0 := mul_zero _
      | add y z hy hz =>
          rw [map_add, inner_add_right, hy, hz, add_zero]
  | add x z hx hz =>
      rw [map_add, inner_add_left, hx, hz, add_zero]


-- @@ L3877-3910 verbatim
theorem gtFullTransverseInternalEmbedding_finrank_sum {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (hdom : Antitone lam) :
    Module.finrank ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) =
      ∑ mu : FullBranchWeight lam,
        Module.finrank ℝ
          (SpherePacking.Euclidean n ⊗[ℝ]
            HarmonicYoungSpace (n := n) (fullBranchSignature mu)) := by
  rw [Module.finrank_tensorProduct]
  calc
    Module.finrank ℝ (SpherePacking.Euclidean n) *
        Module.finrank ℝ (HarmonicYoungSpace (n := n + 1) lam) =
      Module.finrank ℝ (SpherePacking.Euclidean n) *
        ∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (HarmonicYoungSpace (n := n)
              (fullBranchSignature mu)) := by
          congr 1
          convert canonicalFullBranch_finrank_sum_allRank lam hn hdom using 1
          · apply Finset.sum_congr rfl
            intro mu _
            congr 1
    _ = ∑ mu : FullBranchWeight lam,
          Module.finrank ℝ
            (SpherePacking.Euclidean n ⊗[ℝ]
              HarmonicYoungSpace (n := n)
                (fullBranchSignature mu)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mu _
          symm
          exact Module.finrank_tensorProduct


-- @@ L3912-3924 verbatim
theorem gtFullTransverseInternalEmbedding_iSup_range_eq_top
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range
        (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam)) :=
  orthogonalBranch_iSup_range_eq_top
    (gtFullTransverseInternalEmbedding lam hn)
    (gtFullTransverseInternalEmbedding_orthogonal lam hn)
    (gtFullTransverseInternalEmbedding_finrank_sum lam hn hdom)


-- @@ L3926-3937 verbatim
/-- The tensor isometry induced by the transverse Euclidean inclusion while retaining the
harmonic Young factor. -/
def gtFullTransverseAmbientInclusion {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n + 1) lam) →ₗᵢ[ℝ]
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n)
    (LinearIsometry.id :
      HarmonicYoungSpace (n := n + 1) lam →ₗᵢ[ℝ]
        HarmonicYoungSpace (n := n + 1) lam)


-- @@ L3939-3949 verbatim
/-- The tensor isometry combining the transverse Euclidean inclusion with a canonical full-
branch fibre. -/
def gtFullTransverseEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) :
    (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu)) →ₗᵢ[ℝ]
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam) :=
  TensorProduct.mapIsometry (gtTransverseEuclideanIsometry n)
    (canonicalFullBranchFibre lam hn mu)


-- @@ L3951-3959 verbatim
theorem gtFullTransverseEmbedding_eq_comp {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) :
    (gtFullTransverseEmbedding lam hn mu).toLinearMap =
      (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap.comp
        (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap := by
  apply TensorProduct.ext
  ext v p
  rfl


-- @@ L3961-3983 verbatim
theorem gtFullTransverseEmbedding_orthogonal {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (y : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullTransverseEmbedding lam hn mu x,
      gtFullTransverseEmbedding lam hn nu y⟫_ℝ = 0 := by
  have hmu := LinearMap.congr_fun
    (gtFullTransverseEmbedding_eq_comp lam hn mu) x
  have hnu := LinearMap.congr_fun
    (gtFullTransverseEmbedding_eq_comp lam hn nu) y
  change
    ⟪(gtFullTransverseEmbedding lam hn mu).toLinearMap x,
      (gtFullTransverseEmbedding lam hn nu).toLinearMap y⟫_ℝ = 0
  rw [hmu, hnu]
  calc
    _ = ⟪gtFullTransverseInternalEmbedding lam hn mu x,
          gtFullTransverseInternalEmbedding lam hn nu y⟫_ℝ :=
      (gtFullTransverseAmbientInclusion (n := n) lam).inner_map_map _ _
    _ = 0 :=
      gtFullTransverseInternalEmbedding_orthogonal lam hn mu nu hne x y


-- @@ L3985-4015 verbatim
theorem gtFullTransverseEmbedding_iSup_range {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap) =
      LinearMap.range
        (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
  calc
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap) =
        ⨆ mu : FullBranchWeight lam,
          (LinearMap.range
            (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
          congr 1
          funext mu
          rw [gtFullTransverseEmbedding_eq_comp, LinearMap.range_comp]
    _ = (⨆ mu : FullBranchWeight lam,
          LinearMap.range
            (gtFullTransverseInternalEmbedding lam hn mu).toLinearMap).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap :=
          (Submodule.map_iSup _ _).symm
    _ = (⊤ : Submodule ℝ
          (SpherePacking.Euclidean n ⊗[ℝ]
            HarmonicYoungSpace (n := n + 1) lam)).map
              (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap := by
          rw [gtFullTransverseInternalEmbedding_iSup_range_eq_top
            lam hn hdom]
    _ = LinearMap.range
          (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap :=
          Submodule.map_top _


-- @@ L4017-4017 verbatim
end AllRankGTTransverseFullBranchDecomposition


-- @@ L4019-4019 verbatim
namespace AllRankGTActualAxisTransverseDecomposition


-- @@ L4021-4021 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L4022-4022 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L4023-4023 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L4024-4024 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L4025-4025 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness


-- @@ L4027-4041 verbatim
theorem euclidean_eq_gtTransverse_add_last_axis {n : ℕ}
    (v : SpherePacking.Euclidean (n + 1)) :
    v = gtTransverseEuclideanIsometry n
        (WithLp.toLp 2 (fun i : Fin n => v i.castSucc)) +
      v (Fin.last n) •
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp only [EuclideanSpace.basisFun_apply, PiLp.add_apply,
              gtTransverseEuclideanIsometry_last, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul,
              mul_one, zero_add]
  | cast j => simp only [EuclideanSpace.basisFun_apply, PiLp.add_apply,
                gtTransverseEuclideanIsometry_castSucc, PiLp.smul_apply, ne_eq,
                Fin.castSucc_ne_last, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul,
                mul_zero, add_zero]


-- @@ L4043-4061 verbatim
/-- The isometry sending a harmonic Young vector to its tensor with the last coordinate axis. -/
def gtFullAxisAmbientInclusion {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n + 1) lam →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (TensorProduct.mk ℝ (SpherePacking.Euclidean (n + 1))
    (HarmonicYoungSpace (n := n + 1) lam)
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).isometryOfInner
      (by
        intro p q
        change
          ⟪(EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ] p,
            (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ] q⟫_ℝ =
            ⟪p, q⟫_ℝ
        rw [TensorProduct.inner_tmul,
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).inner_eq_one,
          one_mul]
        rfl)


-- @@ L4063-4091 verbatim
theorem gtFullAxisAmbientInclusion_sup_transverse_range_eq_top
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    LinearMap.range (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap ⊔
        LinearMap.range
          (gtFullTransverseAmbientInclusion (n := n) lam).toLinearMap =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam)) := by
  apply top_unique
  intro x _
  induction x with
  | tmul v p =>
      let w : SpherePacking.Euclidean n :=
        WithLp.toLp 2 (fun i : Fin n => v i.castSucc)
      have hv := euclidean_eq_gtTransverse_add_last_axis v
      change v ⊗ₜ[ℝ] p ∈ _
      rw [hv, TensorProduct.add_tmul]
      apply Submodule.add_mem
      · apply Submodule.mem_sup_right
        exact ⟨w ⊗ₜ[ℝ] p, rfl⟩
      · apply Submodule.mem_sup_left
        refine ⟨v (Fin.last n) • p, ?_⟩
        change
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
              (v (Fin.last n) • p) =
            (v (Fin.last n) •
              (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))) ⊗ₜ[ℝ] p
        simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)


-- @@ L4093-4102 verbatim
/-- The isometry obtained by embedding a full-branch fibre and tensoring with the last
coordinate axis. -/
def gtFullAxisEmbedding {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam) :
    HarmonicYoungSpace (n := n) (fullBranchSignature mu) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (gtFullAxisAmbientInclusion (n := n) lam).comp
    (canonicalFullBranchFibre lam hn mu)


-- @@ L4104-4110 verbatim
@[simp] theorem gtFullAxisEmbedding_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu : FullBranchWeight lam)
    (p : HarmonicYoungSpace (n := n) (fullBranchSignature mu)) :
    gtFullAxisEmbedding lam hn mu p =
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
        canonicalFullBranchFibre lam hn mu p := rfl


-- @@ L4112-4125 verbatim
theorem gtFullAxisEmbedding_orthogonal {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam) (hne : mu ≠ nu)
    (p : HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullAxisEmbedding lam hn mu p,
      gtFullAxisEmbedding lam hn nu q⟫_ℝ = 0 := by
  calc
    ⟪gtFullAxisEmbedding lam hn mu p,
        gtFullAxisEmbedding lam hn nu q⟫_ℝ =
      ⟪canonicalFullBranchFibre lam hn mu p,
        canonicalFullBranchFibre lam hn nu q⟫_ℝ :=
          (gtFullAxisAmbientInclusion (n := n) lam).inner_map_map _ _
    _ = 0 := canonicalFullBranchFibre_orthogonal lam hn mu nu hne p q


-- @@ L4127-4150 verbatim
theorem gtFullAxisEmbedding_inner_transverse_eq_zero {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n + 1)
    (mu nu : FullBranchWeight lam)
    (p : HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪gtFullAxisEmbedding lam hn mu p,
      gtFullTransverseEmbedding lam hn nu x⟫_ℝ = 0 := by
  induction x with
  | tmul v q =>
      rw [gtFullAxisEmbedding_apply]
      change
        ⟪(EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
            canonicalFullBranchFibre lam hn mu p,
          gtTransverseEuclideanIsometry n v ⊗ₜ[ℝ]
            canonicalFullBranchFibre lam hn nu q⟫_ℝ = 0
      rw [TensorProduct.inner_tmul]
      have hzero :
          ⟪EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n),
            gtTransverseEuclideanIsometry n v⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact gtTransverseEuclideanIsometry_orthogonal_last n v
      rw [hzero, zero_mul]
  | add x y hx hy => rw [map_add, inner_add_right, hx, hy, add_zero]


-- @@ L4152-4184 verbatim
theorem gtFullAxisEmbedding_iSup_range
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap) =
        LinearMap.range
          (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
  calc
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap) =
        ⨆ mu : FullBranchWeight lam,
          (LinearMap.range
            (canonicalFullBranchFibre lam hn mu).toLinearMap).map
              (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
          congr 1
          funext mu
          change
            LinearMap.range
                ((gtFullAxisAmbientInclusion (n := n) lam).toLinearMap.comp
                  (canonicalFullBranchFibre lam hn mu).toLinearMap) = _
          rw [LinearMap.range_comp]
    _ = (⨆ mu : FullBranchWeight lam,
          LinearMap.range (canonicalFullBranchFibre lam hn mu).toLinearMap).map
            (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap :=
          (Submodule.map_iSup _ _).symm
    _ = (⊤ : Submodule ℝ
          (HarmonicYoungSpace (n := n + 1) lam)).map
            (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap := by
          rw [canonicalFullBranch_iSup_range_eq_top_unconditional
            lam hn hdom]
    _ = LinearMap.range
          (gtFullAxisAmbientInclusion (n := n) lam).toLinearMap :=
          Submodule.map_top _


-- @@ L4186-4198 verbatim
theorem gtFullAxisTransverse_iSup_range_eq_top
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam) :
    (⨆ mu : FullBranchWeight lam,
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap) ⊔
        (⨆ mu : FullBranchWeight lam,
          LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
          HarmonicYoungSpace (n := n + 1) lam)) := by
  rw [gtFullAxisEmbedding_iSup_range lam hn hdom,
    gtFullTransverseEmbedding_iSup_range lam hn hdom]
  exact gtFullAxisAmbientInclusion_sup_transverse_range_eq_top lam


-- @@ L4200-4200 verbatim
end AllRankGTActualAxisTransverseDecomposition


-- @@ L4202-4202 verbatim
end


-- @@ L4204-4204 verbatim
section



-- @@ L4207-4207 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L4209-4209 verbatim
namespace AllRankGTPhysicalCompleteBlockReconstruction


-- @@ L4211-4211 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L4212-4212 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition

-- @@ L4213-4213 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L4214-4214 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L4215-4215 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L4216-4216 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness


-- @@ L4218-4237 verbatim
theorem inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero
    {ι : Type*} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (E : ι → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (y : V) (hzero : ∀ i : ι, (A i).adjoint y = 0)
    (x : V) (hx : x ∈ ⨆ i : ι, LinearMap.range (A i)) :
    ⟪x, y⟫_ℝ = 0 := by
  refine Submodule.iSup_induction
    (motive := fun z : V => ⟪z, y⟫_ℝ = 0) _ hx ?_ ?_ ?_
  · intro i z hz
    obtain ⟨p, rfl⟩ := hz
    rw [← LinearMap.adjoint_inner_right, hzero i, inner_zero_right]
  · simp only [inner_zero_left]
  · intro u v hu hv
    rw [inner_add_left, hu, hv, add_zero]


-- @@ L4239-4271 verbatim
theorem eq_zero_of_iSup_range_sup_eq_top_of_adjoint_eq_zero
    {ι κ : Type*} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (E : ι → Type*) (F : κ → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ j, NormedAddCommGroup (F j)]
    [∀ j, InnerProductSpace ℝ (F j)]
    [∀ j, FiniteDimensional ℝ (F j)]
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (B : (j : κ) → F j →ₗ[ℝ] V)
    (hcomplete :
      (⨆ i : ι, LinearMap.range (A i)) ⊔
        (⨆ j : κ, LinearMap.range (B j)) = ⊤)
    (y : V)
    (haxis : ∀ i : ι, (A i).adjoint y = 0)
    (htransverse : ∀ j : κ, (B j).adjoint y = 0) :
    y = 0 := by
  apply ext_inner_left ℝ
  intro x
  rw [inner_zero_right]
  have hx : x ∈
      (⨆ i : ι, LinearMap.range (A i)) ⊔
        (⨆ j : κ, LinearMap.range (B j)) := by
    rw [hcomplete]
    trivial
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [inner_add_left,
    inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero E A y haxis u hu,
    inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero F B y htransverse v hv,
    add_zero]


-- @@ L4273-4299 verbatim
theorem eq_of_iSup_range_sup_eq_top_of_adjoint_eq
    {ι κ : Type*} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (E : ι → Type*) (F : κ → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ j, NormedAddCommGroup (F j)]
    [∀ j, InnerProductSpace ℝ (F j)]
    [∀ j, FiniteDimensional ℝ (F j)]
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (B : (j : κ) → F j →ₗ[ℝ] V)
    (hcomplete :
      (⨆ i : ι, LinearMap.range (A i)) ⊔
        (⨆ j : κ, LinearMap.range (B j)) = ⊤)
    (x y : V)
    (haxis : ∀ i : ι, (A i).adjoint x = (A i).adjoint y)
    (htransverse : ∀ j : κ, (B j).adjoint x = (B j).adjoint y) :
    x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_iSup_range_sup_eq_top_of_adjoint_eq_zero
    E F A B hcomplete (x - y)
  · intro i
    rw [map_sub, haxis i, sub_self]
  · intro j
    rw [map_sub, htransverse j, sub_self]


-- @@ L4301-4301 verbatim
end AllRankGTPhysicalCompleteBlockReconstruction


-- @@ L4303-4303 verbatim
end


-- @@ L4305-4305 verbatim
section



-- @@ L4308-4308 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L4310-4310 verbatim
namespace AllRankGTValidTransverseArrowheadRow


-- @@ L4312-4312 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L4313-4313 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L4314-4314 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L4315-4315 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent

-- @@ L4316-4316 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L4317-4317 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)


-- @@ L4319-4328 verbatim
/-- The canonical Gelfand–Tsetlin axis tensor map bundled as a linear isometry. -/
def canonicalGelfandTsetlinAxisIsometry
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  (canonicalGelfandTsetlinAxisTensor lam mu h hgram).isometryOfInner
    (canonicalGelfandTsetlinAxisTensor_inner lam mu h hgram)


-- @@ L4330-4330 verbatim
end AllRankGTValidTransverseArrowheadRow


-- @@ L4332-4332 verbatim
end


-- @@ L4334-4334 verbatim
section



-- @@ L4337-4337 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L4339-4339 verbatim
namespace AllRankGTPhysicalRetainedAdditiveColumn


-- @@ L4341-4341 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L4342-4342 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition

-- @@ L4343-4343 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L4344-4344 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction

-- @@ L4345-4345 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L4346-4346 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow

-- @@ L4347-4347 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L4348-4348 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness


-- @@ L4350-4391 verbatim
theorem linearMap_comp_eq_smul_add_of_complete_adjoint_block_rows
    {ι κ E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (X : ι → Type*) (Y : κ → Type*)
    [∀ i, NormedAddCommGroup (X i)]
    [∀ i, InnerProductSpace ℝ (X i)]
    [∀ i, FiniteDimensional ℝ (X i)]
    [∀ j, NormedAddCommGroup (Y j)]
    [∀ j, InnerProductSpace ℝ (Y j)]
    [∀ j, FiniteDimensional ℝ (Y j)]
    (C : (i : ι) → X i →ₗ[ℝ] V)
    (D : (j : κ) → Y j →ₗ[ℝ] V)
    (hcomplete :
      (⨆ i : ι, LinearMap.range (C i)) ⊔
        (⨆ j : κ, LinearMap.range (D j)) = ⊤)
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (A : F →ₗ[ℝ] V)
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (haxis : ∀ i : ι,
      (C i).adjoint.comp (T.comp B) =
        d • ((C i).adjoint.comp B) +
          ((C i).adjoint.comp A).comp K)
    (htransverse : ∀ j : κ,
      (D j).adjoint.comp (T.comp B) =
        d • ((D j).adjoint.comp B) +
          ((D j).adjoint.comp A).comp K) :
    T.comp B = d • B + A.comp K := by
  apply LinearMap.ext
  intro p
  apply eq_of_iSup_range_sup_eq_top_of_adjoint_eq
    X Y C D hcomplete (T (B p)) (d • B p + A (K p))
  · intro i
    have hi := LinearMap.congr_fun (haxis i) p
    simpa only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul] using hi
  · intro j
    have hj := LinearMap.congr_fun (htransverse j) p
    simpa only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, map_add, map_smul] using hj


-- @@ L4393-4427 verbatim
theorem gtRelativeCasimir_comp_eq_smul_add_of_full_axis_transverse_rows
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (B : E →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (A : F →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (haxis : ∀ mu : FullBranchWeight lam,
      (gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        d • ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp B) +
          ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp A).comp K)
    (htransverse : ∀ mu : FullBranchWeight lam,
      (gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        d • ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp B) +
          ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp A).comp K) :
    (gtRelativeCasimir (n := n + 1) lam).comp B =
      d • B + A.comp K := by
  exact linearMap_comp_eq_smul_add_of_complete_adjoint_block_rows
    (fun mu : FullBranchWeight lam =>
      HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (fun mu : FullBranchWeight lam =>
      SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (fullBranchSignature mu))
    (fun mu => (gtFullAxisEmbedding lam hn mu).toLinearMap)
    (fun mu => (gtFullTransverseEmbedding lam hn mu).toLinearMap)
    (gtFullAxisTransverse_iSup_range_eq_top lam hn hdom)
    (gtRelativeCasimir (n := n + 1) lam) B A K d haxis htransverse


-- @@ L4429-4462 verbatim
theorem gtRelativeCasimir_comp_eq_smul_add_of_orthogonal_full_block_rows
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    {E F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (B : E →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (A : F →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (haxisOrth : ∀ mu : FullBranchWeight lam,
      (gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp B = 0)
    (htransverseOrth : ∀ mu : FullBranchWeight lam,
      (gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp A = 0)
    (haxis : ∀ mu : FullBranchWeight lam,
      (gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint.comp A).comp K)
    (htransverse : ∀ mu : FullBranchWeight lam,
      (gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp
          ((gtRelativeCasimir (n := n + 1) lam).comp B) =
        d • ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint.comp B)) :
    (gtRelativeCasimir (n := n + 1) lam).comp B =
      d • B + A.comp K := by
  apply gtRelativeCasimir_comp_eq_smul_add_of_full_axis_transverse_rows
    lam hn hdom B A K d
  · intro mu
    rw [haxisOrth mu, smul_zero, zero_add, haxis mu]
  · intro mu
    rw [htransverseOrth mu, LinearMap.zero_comp, add_zero,
      htransverse mu]


-- @@ L4464-4464 verbatim
end AllRankGTPhysicalRetainedAdditiveColumn


-- @@ L4466-4466 verbatim
end


-- @@ L4468-4468 verbatim
section



-- @@ L4471-4471 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L4473-4473 verbatim
namespace AllRankGTRelativeCasimirCrossBlock


-- @@ L4475-4475 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L4476-4476 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L4477-4477 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L4478-4478 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L4479-4479 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent

-- @@ L4480-4480 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)


-- @@ L4482-4493 verbatim
/-- The cross block of the relative Casimir from a supplied tensor map to the canonical
Gelfand–Tsetlin axis image. -/
def gtTransverseAxisCrossBlock
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam)) :
    Module.End ℝ (HarmonicYoungSpace (n := n) mu) :=
  (canonicalGelfandTsetlinAxisTensor lam mu h hgram).adjoint.comp
    ((gtRelativeCasimir lam).comp B)


-- @@ L4495-4495 verbatim
end AllRankGTRelativeCasimirCrossBlock


-- @@ L4497-4497 verbatim
end


-- @@ L4499-4499 verbatim
section



-- @@ L4502-4502 verbatim
open scoped TensorProduct


-- @@ L4504-4504 verbatim
namespace AllRankGTPhysicalPaddedPieriFullEigen


-- @@ L4506-4506 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L4507-4507 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L4508-4508 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing

-- @@ L4509-4509 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L4510-4510 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport

-- @@ L4511-4511 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality

-- @@ L4512-4512 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy

-- @@ L4513-4513 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels

-- @@ L4514-4514 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L4515-4515 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L4517-4540 verbatim
theorem physicalPaddedPieriChannel_relativeCasimir
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (p : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) i)) :
    gtRelativeCasimir (n := n) lam
        (physicalPaddedPieriChannel hn lam hdom i p) =
      HigherChannel.signedNode
        (HigherChannel.ambientShift n (appendZeroWeight lam))
        (paddedPieriSignedChannel (appendZeroWeight lam) i) •
        physicalPaddedPieriChannel hn lam hdom i p := by
  exact zeroRowTransportPaddedPieriChannel_eigen_of_intertwine
    lam
    (paddedOrthogonalTensorPieriChannel hn
      (appendZeroWeight lam) hdom i)
    (zeroRowTensorIsometryEquiv_symm_relativeCasimir_intertwine lam).symm
    (HigherChannel.signedNode
      (HigherChannel.ambientShift n (appendZeroWeight lam))
      (paddedPieriSignedChannel (appendZeroWeight lam) i))
    p
    (paddedOrthogonalTensorPieriChannel_relativeCasimir hn
      (appendZeroWeight lam) hdom i p)


-- @@ L4542-4542 verbatim
end AllRankGTPhysicalPaddedPieriFullEigen


-- @@ L4544-4544 verbatim
end


-- @@ L4546-4546 verbatim
section



-- @@ L4549-4549 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L4551-4551 verbatim
namespace AllRankGTSelectedMuAxisProjectionVanishing


-- @@ L4553-4553 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L4554-4554 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L4555-4555 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange

-- @@ L4556-4556 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L4557-4557 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition

-- @@ L4558-4558 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTInvalidNonterminalProjectorVanishing

-- @@ L4559-4559 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriFullEigen

-- @@ L4560-4560 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L4561-4561 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent

-- @@ L4562-4562 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L4563-4563 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality

-- @@ L4564-4564 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow

-- @@ L4565-4565 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness

-- @@ L4566-4566 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy

-- @@ L4567-4567 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L4568-4568 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L4569-4569 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L4570-4570 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram

-- @@ L4571-4571 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L4572-4572 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L4573-4573 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L4574-4574 verbatim
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner

-- @@ L4575-4575 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTAxisTensorRotationIntertwining

-- @@ L4576-4576 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels

-- @@ L4577-4577 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L4578-4578 verbatim
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance

-- @@ L4579-4579 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L4581-4605 verbatim
theorem physicalPaddedPieriChannel_rotation_intertwine
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i : PaddedPieriChannel (appendZeroWeight lam))
    (a b : Fin n) :
    (physicalPaddedPieriChannel hn lam hdom i).toLinearMap.comp
        (youngAmbientRotation
          (paddedPieriSource (appendZeroWeight lam) i) a b) =
      (tensorAmbientRotation lam a b).comp
        (physicalPaddedPieriChannel hn lam hdom i).toLinearMap := by
  apply LinearMap.ext
  intro p
  let Z := (zeroRowTensorIsometryEquiv (n := n) lam).symm.toLinearMap
  let A := (paddedOrthogonalTensorPieriChannel
    hn (appendZeroWeight lam) hdom i).toLinearMap
  change Z (A (youngAmbientRotation
    (paddedPieriSource (appendZeroWeight lam) i) a b p)) =
      tensorAmbientRotation lam a b (Z (A p))
  have hA := LinearMap.congr_fun
    (paddedOrthogonalTensorPieriChannel_rotation_intertwine
      hn (appendZeroWeight lam) hdom i a b) p
  have hZ := LinearMap.congr_fun
    (zeroRowTensorIsometryEquiv_symm_rotation_intertwine lam a b) (A p)
  exact (congrArg Z hA).trans hZ


-- @@ L4607-4676 verbatim
theorem gtRelativeCasimir_tensorAmbientRotation_commute
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (a b : Fin n) :
    (gtRelativeCasimir (n := n) lam).comp
        (tensorAmbientRotation lam a b) =
      (tensorAmbientRotation lam a b).comp
        (gtRelativeCasimir (n := n) lam) := by
  classical
  let A := physicalPaddedPieriChannel hn lam hdom
  have hcomplete :
      (⨆ i : PaddedPieriChannel (appendZeroWeight lam),
        LinearMap.range (A i).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) lam)) :=
    orthogonalBranch_iSup_range_eq_top A
      (physicalPaddedPieriChannel_inner_eq_zero hn lam hdom)
      (physicalPaddedPieriChannel_finrank hn lam hdom)
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ i : PaddedPieriChannel (appendZeroWeight lam),
      LinearMap.range (A i).toLinearMap := by
    rw [hcomplete]
    trivial
  change
    gtRelativeCasimir lam (tensorAmbientRotation lam a b x) =
      tensorAmbientRotation lam a b (gtRelativeCasimir lam x)
  refine Submodule.iSup_induction
    (motive := fun x =>
      gtRelativeCasimir lam (tensorAmbientRotation lam a b x) =
        tensorAmbientRotation lam a b (gtRelativeCasimir lam x))
    _ hx ?_ ?_ ?_
  · intro i x hxi
    obtain ⟨p, rfl⟩ := hxi
    let d := signedNode
      (HigherChannel.ambientShift n (appendZeroWeight lam))
      (paddedPieriSignedChannel (appendZeroWeight lam) i)
    have hrot := LinearMap.congr_fun
      (physicalPaddedPieriChannel_rotation_intertwine hn lam hdom i a b) p
    change
      A i (youngAmbientRotation
        (paddedPieriSource (appendZeroWeight lam) i) a b p) =
        tensorAmbientRotation lam a b (A i p) at hrot
    have heigen (q : HarmonicYoungSpace (n := n)
        (paddedPieriSource (appendZeroWeight lam) i)) :
        gtRelativeCasimir lam (A i q) = d • A i q := by
      simpa only [A, d] using
        physicalPaddedPieriChannel_relativeCasimir hn lam hdom i q
    calc
      gtRelativeCasimir lam
          (tensorAmbientRotation lam a b (A i p)) =
        gtRelativeCasimir lam
          (A i (youngAmbientRotation
            (paddedPieriSource (appendZeroWeight lam) i) a b p)) :=
          congrArg (gtRelativeCasimir lam) hrot.symm
      _ = d • A i (youngAmbientRotation
          (paddedPieriSource (appendZeroWeight lam) i) a b p) :=
          heigen _
      _ = d • tensorAmbientRotation lam a b (A i p) :=
          congrArg (d • ·) hrot
      _ = tensorAmbientRotation lam a b (d • A i p) :=
          (map_smul (tensorAmbientRotation lam a b) d (A i p)).symm
      _ = tensorAmbientRotation lam a b
            (gtRelativeCasimir lam (A i p)) :=
          congrArg (tensorAmbientRotation lam a b) (heigen p).symm
  · simp only [map_zero]
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy


-- @@ L4678-4702 verbatim
theorem gtFullAxisEmbedding_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1)
    (nu : FullBranchWeight lam) (a b : Fin n) :
    (gtFullAxisEmbedding lam hn nu).toLinearMap.comp
        (youngAmbientRotation (fullBranchSignature nu) a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtFullAxisEmbedding lam hn nu).toLinearMap := by
  apply LinearMap.ext
  intro p
  change
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
        canonicalFullBranchFibre lam hn nu
          (youngAmbientRotation (fullBranchSignature nu) a b p) =
      tensorAmbientRotation lam a.castSucc b.castSucc
        ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) ⊗ₜ[ℝ]
          canonicalFullBranchFibre lam hn nu p)
  rw [tensorAmbientRotation_tmul,
    euclideanAmbientRotation_castSucc_last,
    TensorProduct.zero_tmul, zero_add]
  exact congrArg
    (fun q => (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
      ⊗ₜ[ℝ] q)
    (LinearMap.congr_fun
      (canonicalFullBranchFibre_rotation_intertwine lam hn nu a b) p)


-- @@ L4704-4726 verbatim
theorem gtFullAxisEmbedding_selected_range_eq_canonicalAxis
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu) :
    LinearMap.range
        (gtFullAxisEmbedding (n := n) lam hn
          (fullBranchOfInterlaces mu hmu)).toLinearMap =
      LinearMap.range
        (canonicalGelfandTsetlinAxisIsometry
          lam mu hmu hgram).toLinearMap := by
  change
    LinearMap.range
        ((gtFullAxisAmbientInclusion (n := n) lam).toLinearMap.comp
          (canonicalFullBranchFibre lam hn
            (fullBranchOfInterlaces mu hmu)).toLinearMap) =
      LinearMap.range
        ((gtFullAxisAmbientInclusion (n := n) lam).toLinearMap.comp
          (canonicalGelfandTsetlinFibre lam mu hmu hgram).toLinearMap)
  rw [LinearMap.range_comp, LinearMap.range_comp,
    canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam mu hmu hn hmu.antitone_ambient hgram]


-- @@ L4728-4807 verbatim
theorem gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight lam)
    (hne : fullBranchSignature nu ≠ appendZeroWeight mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullAxisEmbedding (n := n) lam (by omega) nu).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) = 0 := by
  let Z := appendZeroRowIsometryEquiv (n := n) mu
  let F := (gtFullAxisEmbedding (n := n) lam (by omega) nu).toLinearMap
  let Bpad := B.comp Z.symm.toLinearMap
  let C := (gtRelativeCasimir (n := n + 1) lam).comp Bpad
  have hdom : Antitone (appendZeroWeight lam) :=
    (fullBranchSignature_interlaces_appendZeroWeight lam
      (fullBranchOfInterlaces mu hmu)).antitone_ambient
  have hdommu : Antitone (appendZeroWeight mu) := by
    rw [← fullBranchOfInterlaces_signature_eq_appendZeroWeight mu hmu]
    exact fullBranchSignature_antitone (fullBranchOfInterlaces mu hmu)
  have hBpad (a b : Fin n) :
      Bpad.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp Bpad := by
    apply LinearMap.ext
    intro q
    have hZ := LinearMap.congr_fun
      (appendZeroRowIsometryEquiv_symm_rotation_intertwine mu a b) q
    have hactual := LinearMap.congr_fun (hB a b) (Z.symm q)
    change B (Z.symm (youngAmbientRotation
      (appendZeroWeight mu) a b q)) =
        tensorAmbientRotation lam a.castSucc b.castSucc
          (B (Z.symm q))
    exact (congrArg B hZ).trans hactual
  have hC (a b : Fin n) :
      C.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp C := by
    calc
      C.comp (youngAmbientRotation (appendZeroWeight mu) a b) =
        (gtRelativeCasimir (n := n + 1) lam).comp
          (Bpad.comp (youngAmbientRotation (appendZeroWeight mu) a b)) := by
            ext q
            rfl
      _ = (gtRelativeCasimir (n := n + 1) lam).comp
          ((tensorAmbientRotation lam a.castSucc b.castSucc).comp Bpad) := by
            rw [hBpad a b]
      _ = ((gtRelativeCasimir (n := n + 1) lam).comp
          (tensorAmbientRotation lam a.castSucc b.castSucc)).comp Bpad := by
            ext q
            rfl
      _ = ((tensorAmbientRotation lam a.castSucc b.castSucc).comp
          (gtRelativeCasimir (n := n + 1) lam)).comp Bpad := by
            rw [gtRelativeCasimir_tensorAmbientRotation_commute
              (by omega) lam hdom a.castSucc b.castSucc]
      _ = (tensorAmbientRotation lam a.castSucc b.castSucc).comp C := by
            ext q
            rfl
  have hzero : F.adjoint.comp C = 0 := by
    apply youngRotationIntertwiner_eq_zero_of_signature_ne
      (by omega : 2 * ((r + 1) + 1) + 2 ≤ n)
      (appendZeroWeight mu) (fullBranchSignature nu)
      hdommu (Ne.symm hne)
    intro a b
    exact crossGram_intertwines_of_skew F C
      (youngAmbientRotation (fullBranchSignature nu) a b)
      (youngAmbientRotation (appendZeroWeight mu) a b)
      (tensorAmbientRotation lam a.castSucc b.castSucc)
      (youngAmbientRotation_adjoint (fullBranchSignature nu) a b)
      (tensorAmbientRotation_adjoint lam a.castSucc b.castSucc)
      (gtFullAxisEmbedding_rotation_intertwine lam (by omega) nu a b)
      (hC a b)
  have hp := LinearMap.congr_fun hzero (Z p)
  change F.adjoint
    (gtRelativeCasimir lam (B (Z.symm (Z p)))) = 0 at hp
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hp


-- @@ L4809-4809 verbatim
end AllRankGTSelectedMuAxisProjectionVanishing


-- @@ L4811-4811 verbatim
end


-- @@ L4813-4813 verbatim
end HigherHarmonicYoung


-- @@ L4815-4815 verbatim
end Spherical


-- @@ L4817-4817 verbatim
end MetricCodes



-- @@ L4820-4820 verbatim
namespace MetricCodes


-- @@ L4822-4822 verbatim
namespace Spherical


-- @@ L4824-4824 verbatim
namespace HigherHarmonicYoung


-- @@ L4826-4826 verbatim
section


-- @@ L4828-4828 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L4830-4830 verbatim
namespace AllRankGTFullTransverseSameSignatureRow


-- @@ L4832-4832 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L4833-4833 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L4834-4834 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange

-- @@ L4835-4835 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L4836-4836 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector

-- @@ L4837-4837 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L4838-4838 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L4839-4839 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L4840-4840 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression

-- @@ L4841-4841 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L4842-4842 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L4843-4843 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

-- @@ L4844-4844 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L4845-4845 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L4846-4846 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L4847-4847 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L4848-4848 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L4849-4849 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

-- @@ L4850-4850 verbatim
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature

-- @@ L4851-4851 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L4853-4888 verbatim
theorem tensor_mapIsometry_range_eq_of_second_range_eq
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (e : E →ₗᵢ[ℝ] F) (g : X →ₗᵢ[ℝ] Z) (h : Y →ₗᵢ[ℝ] Z)
    (heq : LinearMap.range g.toLinearMap = LinearMap.range h.toLinearMap) :
    LinearMap.range (TensorProduct.mapIsometry e g).toLinearMap =
      LinearMap.range (TensorProduct.mapIsometry e h).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x with
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul v p =>
        have hmem : g p ∈ LinearMap.range h.toLinearMap := by
          rw [← heq]
          exact ⟨p, rfl⟩
        obtain ⟨q, hq⟩ := hmem
        change h q = g p at hq
        refine ⟨v ⊗ₜ[ℝ] q, ?_⟩
        change e v ⊗ₜ[ℝ] h q = e v ⊗ₜ[ℝ] g p
        rw [hq]
  · rintro _ ⟨x, rfl⟩
    induction x with
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul v p =>
        have hmem : h p ∈ LinearMap.range g.toLinearMap := by
          rw [heq]
          exact ⟨p, rfl⟩
        obtain ⟨q, hq⟩ := hmem
        change g q = h p at hq
        refine ⟨v ⊗ₜ[ℝ] q, ?_⟩
        change e v ⊗ₜ[ℝ] g q = e v ⊗ₜ[ℝ] h p
        rw [hq]


-- @@ L4890-4914 verbatim
theorem adjoint_eigen_of_range_le
    {X Y H : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (I : X →ₗ[ℝ] H) (J : Y →ₗ[ℝ] H)
    (hrange : LinearMap.range J ≤ LinearMap.range I)
    (T : Module.End ℝ H) (x : H) (d : ℝ)
    (hI : I.adjoint (T x) = d • I.adjoint x) :
    J.adjoint (T x) = d • J.adjoint x := by
  apply ext_inner_left ℝ
  intro q
  obtain ⟨z, hz⟩ := hrange (show J q ∈ LinearMap.range J from ⟨q, rfl⟩)
  calc
    ⟪q, J.adjoint (T x)⟫_ℝ = ⟪J q, T x⟫_ℝ :=
      LinearMap.adjoint_inner_right J q (T x)
    _ = ⟪I z, T x⟫_ℝ := by rw [hz]
    _ = ⟪z, I.adjoint (T x)⟫_ℝ :=
      (LinearMap.adjoint_inner_right I z (T x)).symm
    _ = ⟪z, d • I.adjoint x⟫_ℝ := by rw [hI]
    _ = d * ⟪z, I.adjoint x⟫_ℝ := real_inner_smul_right z (I.adjoint x) d
    _ = d * ⟪I z, x⟫_ℝ := by rw [LinearMap.adjoint_inner_right]
    _ = d * ⟪J q, x⟫_ℝ := by rw [hz]
    _ = ⟪q, d • J.adjoint x⟫_ℝ := by
      rw [real_inner_smul_right, LinearMap.adjoint_inner_right]


-- @@ L4916-4930 verbatim
theorem gtTransverseTensorEmbedding_range_eq_selectedFull
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hdom : Antitone lam)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h) :
    LinearMap.range (gtTransverseTensorEmbedding lam mu h hgram).toLinearMap =
      LinearMap.range
        (gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces mu h)).toLinearMap := by
  exact tensor_mapIsometry_range_eq_of_second_range_eq
    (gtTransverseEuclideanIsometry n)
    (canonicalGelfandTsetlinFibre lam mu h hgram)
    (canonicalFullBranchFibre lam hn (fullBranchOfInterlaces mu h))
    (canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam mu h hn hdom hgram)


-- @@ L4932-4975 verbatim
theorem negativeSector_shortTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p : HarmonicYoungSpace (n := n) mu) :
    let I := gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram
    let B := normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise
    let d := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, false))
    I.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • I.toLinearMap.adjoint (B p) := by
  dsimp
  let c : ℝ := (Real.sqrt
    (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row))⁻¹
  let C := youngClebschRaise (n := n) (raiseWeight mu row) mu
    (sum_raiseWeight mu row) row
  have hphase :
      normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise p =
        c • gtTransverseNegativeSector lam mu row hnu hnuGram p := by
    change (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap p = _
    rw [normalizedGTTransverseNegativeSector_toLinearMap]
    rfl
  have hself :
      (gtTransverseTensorEmbedding lam (raiseWeight mu row)
          hnu hnuGram).toLinearMap.adjoint
        (gtTransverseNegativeSector lam mu row hnu hnuGram p) = C p := by
    exact LinearMap.congr_fun
      (gtTransverseTensorEmbedding lam (raiseWeight mu row)
        hnu hnuGram).adjoint_comp_self' (C p)
  rw [hphase, map_smul, map_smul, map_smul,
    gtTransverseNegativeSector_relativeCasimir_adjoint_compression,
    hself]
  exact smul_comm _ _ _


-- @@ L4977-5013 verbatim
theorem negativeSector_selectedFullTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    let J := gtFullTransverseEmbedding lam hn
      (fullBranchOfInterlaces (raiseWeight mu row) hnu)
    let B := normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise
    let d := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, false))
    J.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • J.toLinearMap.adjoint (B p) := by
  dsimp
  apply adjoint_eigen_of_range_le
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram).toLinearMap
    (gtFullTransverseEmbedding lam hn
      (fullBranchOfInterlaces (raiseWeight mu row) hnu)).toLinearMap
    (le_of_eq
      (gtTransverseTensorEmbedding_range_eq_selectedFull
        lam (raiseWeight mu row) hnu hn hnu.antitone_ambient hnuGram).symm)
    (gtRelativeCasimir (n := n + 1) lam)
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise p)
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, false)))
  exact negativeSector_shortTensor_adjoint_eigen
    lam mu kappa row hnu hnuGram hfinite hraise p


-- @@ L5015-5055 verbatim
theorem positiveSector_shortTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    let I := gtTransverseTensorEmbedding lam nu hnu hnuGram
    let B := normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram
    let d := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, true))
    I.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • I.toLinearMap.adjoint (B p) := by
  dsimp
  let c : ℝ := (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹
  let C := youngClebschLower (n := n) nu mu
    (by rw [hmunu]; exact sum_raiseWeight nu row) row
  have hphase :
      normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram p =
        c • gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p := by
    change (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap p = _
    rw [normalizedGTTransversePositiveSector_toLinearMap]
    rfl
  have hself :
      (gtTransverseTensorEmbedding lam nu hnu hnuGram).toLinearMap.adjoint
        (gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p) =
          C p := by
    exact LinearMap.congr_fun
      (gtTransverseTensorEmbedding lam nu hnu hnuGram).adjoint_comp_self'
      (C p)
  rw [hphase, map_smul, map_smul, map_smul,
    gtTransversePositiveSector_relativeCasimir_adjoint_compression,
    hself]
  exact smul_comm _ _ _


-- @@ L5057-5091 verbatim
theorem positiveSector_selectedFullTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    let J := gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces nu hnu)
    let B := normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram
    let d := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, true))
    J.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • J.toLinearMap.adjoint (B p) := by
  dsimp
  apply adjoint_eigen_of_range_le
    (gtTransverseTensorEmbedding lam nu hnu hnuGram).toLinearMap
    (gtFullTransverseEmbedding lam hn
      (fullBranchOfInterlaces nu hnu)).toLinearMap
    (le_of_eq
      (gtTransverseTensorEmbedding_range_eq_selectedFull
        lam nu hnu hn hnu.antitone_ambient hnuGram).symm)
    (gtRelativeCasimir (n := n + 1) lam)
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram p)
    (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
      (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
        (.inr (row, true)))
  exact positiveSector_shortTensor_adjoint_eigen
    lam mu nu row hmunu hmu hnu hnuGram p


-- @@ L5093-5093 verbatim
end AllRankGTFullTransverseSameSignatureRow


-- @@ L5095-5095 verbatim
end


-- @@ L5097-5097 verbatim
section



-- @@ L5100-5100 verbatim
open scoped InnerProductSpace TensorProduct


-- @@ L5102-5102 verbatim
namespace AllRankGTWallFullTransverseFactorization


-- @@ L5104-5104 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L5105-5105 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L5106-5106 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L5107-5107 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L5108-5108 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry

-- @@ L5109-5109 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

-- @@ L5110-5110 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L5111-5111 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L5112-5112 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L5113-5113 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L5114-5114 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L5116-5137 verbatim
theorem gtWallCanonicalFullBranchFibre_range_eq_fullBranch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    LinearMap.range (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap =
      LinearMap.range (canonicalFullBranchFibre lam hn
        (gtWallFullBranch lam mu h hlast)).toLinearMap := by
  unfold gtWallCanonicalFullBranchFibre
  have transport_range_eq {signature : Fin (r + 2) → ℕ}
      (hsignature :
        fullBranchSignature (gtWallFullBranch lam mu h hlast) = signature) :
      LinearMap.range
          (hsignature ▸
            (canonicalFullBranchFibre lam hn
              (gtWallFullBranch lam mu h hlast))).toLinearMap =
        LinearMap.range
          (canonicalFullBranchFibre lam hn
            (gtWallFullBranch lam mu h hlast)).toLinearMap := by
    subst signature
    rfl
  exact transport_range_eq (gtWallFullBranch_signature lam mu h hlast)


-- @@ L5139-5159 verbatim
theorem gtTransverseWallTensorEmbedding_range_eq_fullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    LinearMap.range
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap =
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (gtWallFullBranch lam mu h hlast)).toLinearMap := by
  change
    LinearMap.range
      (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
        (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap) =
      LinearMap.range
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          (canonicalFullBranchFibre lam hn
            (gtWallFullBranch lam mu h hlast)).toLinearMap)
  rw [TensorProduct.range_map, TensorProduct.range_map,
    gtWallCanonicalFullBranchFibre_range_eq_fullBranch
      lam mu h hn hlast]


-- @@ L5161-5191 verbatim
theorem normalizedGTTransverseWallSector_range_le_fullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    LinearMap.range
        (normalizedGTTransverseWallSector
          lam mu h hn hlast).toLinearMap ≤
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (gtWallFullBranch lam mu h hlast)).toLinearMap := by
  rw [← gtTransverseWallTensorEmbedding_range_eq_fullTransverse
    lam mu h hn hlast]
  rintro _ ⟨p, rfl⟩
  change normalizedGTTransverseWallSector lam mu h hn hlast p ∈ _
  rw [normalizedGTTransverseWallSector_apply]
  change
    (Real.sqrt
      (MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram.gtWallSectorGram n mu))⁻¹ •
      (gtTransverseWallTensorEmbedding lam mu h hn hlast)
        ((youngClebschRaise
          (raiseWeight
            (appendZeroWeight mu)
            (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight
            (appendZeroWeight mu)
            (Fin.last (r + 1)))
          (Fin.last (r + 1)))
            ((appendZeroRowIsometryEquiv mu) p)) ∈ _
  exact Submodule.smul_mem _ _ ⟨_, rfl⟩


-- @@ L5193-5193 verbatim
end AllRankGTWallFullTransverseFactorization


-- @@ L5195-5195 verbatim
end


-- @@ L5197-5197 verbatim
section



-- @@ L5200-5200 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L5202-5202 verbatim
namespace AllRankGTTransversePhysicalDiagonalColumn


-- @@ L5204-5204 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L5205-5205 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L5206-5206 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow

-- @@ L5207-5207 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L5208-5208 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L5209-5209 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization

-- @@ L5210-5210 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram

-- @@ L5211-5211 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry

-- @@ L5212-5212 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

-- @@ L5213-5213 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L5214-5214 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L5215-5215 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L5216-5216 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L5217-5217 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L5219-5255 verbatim
theorem normalizedWallSector_shortTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    let I := gtTransverseWallTensorEmbedding lam mu h hn hlast
    let B := normalizedGTTransverseWallSector lam mu h hn hlast
    let d := -(wallShift (n + 1) (r + 1))
    I.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • I.toLinearMap.adjoint (B p) := by
  dsimp
  let c : ℝ := (Real.sqrt (gtWallSectorGram n mu))⁻¹
  let C :=
    (youngClebschRaise (n := n)
      (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (appendZeroWeight mu)
      (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
      (Fin.last (r + 1))).comp
        (appendZeroRowIsometryEquiv (n := n) mu).toLinearMap
  have hphase :
      normalizedGTTransverseWallSector lam mu h hn hlast p =
        c • gtTransverseWallSector lam mu h hn hlast p := by
    change (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap p = _
    rw [normalizedGTTransverseWallSector_toLinearMap]
    rfl
  have hself :
      (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap.adjoint
        (gtTransverseWallSector lam mu h hn hlast p) = C p := by
    exact LinearMap.congr_fun
      (gtTransverseWallTensorEmbedding lam mu h hn hlast).adjoint_comp_self'
      (C p)
  rw [map_smul, map_smul, map_smul,
    gtTransverseWallSector_relativeCasimir_compression,
    hself]
  exact smul_comm _ _ _


-- @@ L5257-5282 verbatim
theorem normalizedWallSector_selectedFullTensor_adjoint_eigen
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (p : HarmonicYoungSpace (n := n) mu) :
    let J := gtFullTransverseEmbedding lam hn
      (gtWallFullBranch lam mu h hlast)
    let B := normalizedGTTransverseWallSector lam mu h hn hlast
    let d := -(wallShift (n + 1) (r + 1))
    J.toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam (B p)) =
        d • J.toLinearMap.adjoint (B p) := by
  dsimp
  apply adjoint_eigen_of_range_le
    (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap
    (gtFullTransverseEmbedding lam hn
      (gtWallFullBranch lam mu h hlast)).toLinearMap
    (le_of_eq
      (gtTransverseWallTensorEmbedding_range_eq_fullTransverse
        lam mu h hn hlast).symm)
    (gtRelativeCasimir (n := n + 1) lam)
    (normalizedGTTransverseWallSector lam mu h hn hlast p)
    (-(wallShift (n + 1) (r + 1)))
  exact normalizedWallSector_shortTensor_adjoint_eigen
    lam mu h hn hlast p


-- @@ L5284-5284 verbatim
end AllRankGTTransversePhysicalDiagonalColumn


-- @@ L5286-5286 verbatim
end


-- @@ L5288-5288 verbatim
section



-- @@ L5291-5291 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L5293-5293 verbatim
namespace AllRankGTTransverseWrongBranchCompression


-- @@ L5295-5295 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L5296-5296 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L5297-5297 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L5298-5298 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L5299-5299 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L5300-5300 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis

-- @@ L5301-5301 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L5302-5302 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L5303-5303 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression

-- @@ L5304-5304 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression

-- @@ L5305-5305 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L5306-5306 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

-- @@ L5307-5307 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

-- @@ L5308-5308 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L5309-5309 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L5310-5310 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L5311-5311 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L5312-5312 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L5313-5313 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L5314-5314 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality

-- @@ L5315-5315 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L5317-5343 verbatim
theorem transverseStabilizerIsometry_adjoint_comp_of_orthogonal
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (horth : F.toLinearMap.adjoint.comp G.toLinearMap = 0) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        (transverseTensorEmbeddingOfStabilizerIsometry
          lam target G).toLinearMap = 0 := by
  change
    (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
      F.toLinearMap).adjoint.comp
      (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
        G.toLinearMap) = 0
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  have hz := LinearMap.congr_fun horth p
  change F.toLinearMap.adjoint (G p) = 0 at hz
  change
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
        (gtTransverseEuclideanIsometry n v) ⊗ₜ[ℝ]
      F.toLinearMap.adjoint (G p) = 0
  rw [hz, TensorProduct.tmul_zero]


-- @@ L5345-5375 verbatim
theorem transverseStabilizerIsometry_rotationTerm_cross
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (a b : Fin (n + 1)) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map (euclideanAmbientRotation a b)
          (youngAmbientRotation lam a b)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) =
      TensorProduct.map
        ((gtTransverseEuclideanIsometry n).toLinearMap.adjoint.comp
          ((euclideanAmbientRotation a b).comp
            (gtTransverseEuclideanIsometry n).toLinearMap))
        (F.toLinearMap.adjoint.comp
          ((youngAmbientRotation lam a b).comp G.toLinearMap)) := by
  change
    (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
      F.toLinearMap).adjoint.comp
      ((TensorProduct.map (euclideanAmbientRotation a b)
        (youngAmbientRotation lam a b)).comp
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          G.toLinearMap)) = _
  rw [TensorProduct.adjoint_map]
  apply TensorProduct.ext
  ext v p
  rfl


-- @@ L5377-5497 verbatim
theorem transverseStabilizerIsometry_mixedRotation_cross_eq_zero
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (horth : F.toLinearMap.adjoint.comp G.toLinearMap = 0)
    (hG : ∀ a b : Fin n,
      G.toLinearMap.comp (youngAmbientRotation target a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp G.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0 := by
  let I := (transverseTensorEmbeddingOfStabilizerIsometry
    lam source F).toLinearMap
  let J := (transverseTensorEmbeddingOfStabilizerIsometry
    lam target G).toLinearMap
  have htangential (a b : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc b.castSucc)
          (youngAmbientRotation lam a.castSucc b.castSucc)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross]
    have hz : F.toLinearMap.adjoint.comp
        ((youngAmbientRotation lam a.castSucc b.castSucc).comp G.toLinearMap) = 0 := by
      rw [← hG a b, ← LinearMap.comp_assoc, horth, LinearMap.zero_comp]
    rw [hz]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_right, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hcross (a : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc (Fin.last n))
          (youngAmbientRotation lam a.castSucc (Fin.last n))).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation a.castSucc (Fin.last n))
          (youngAmbientRotation lam a.castSucc (Fin.last n))).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross,
      gtTransverseEuclideanIsometry_cross_rotation_compression]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hcrossSwap (a : Fin n) :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) a.castSucc)
          (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp J) = 0 := by
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) a.castSucc)
          (youngAmbientRotation lam (Fin.last n) a.castSucc)).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross,
      gtTransverseEuclideanIsometry_cross_rotation_compression_swap]
    apply TensorProduct.ext
    ext v p
    simp only [TensorProduct.map_zero_left, LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
      LinearMap.zero_apply]
  have hlast :
      I.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) (Fin.last n))
          (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp J) = 0 := by
    have hzero : euclideanAmbientRotation (Fin.last n) (Fin.last n) = 0 := by
      apply LinearMap.ext
      intro v
      simp only [euclideanAmbientRotation_apply, EuclideanSpace.basisFun_apply, sub_self,
        LinearMap.zero_apply]
    change
      (transverseTensorEmbeddingOfStabilizerIsometry
        lam source F).toLinearMap.adjoint.comp
        ((TensorProduct.map
          (euclideanAmbientRotation (Fin.last n) (Fin.last n))
          (youngAmbientRotation lam (Fin.last n) (Fin.last n))).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0
    rw [transverseStabilizerIsometry_rotationTerm_cross, hzero]
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, TensorProduct.map_zero_left]
  unfold gtMixedRotationOperator
  change I.adjoint.comp ((∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
    TensorProduct.map (euclideanAmbientRotation a b)
      (youngAmbientRotation lam a b)).comp J) = 0
  apply TensorProduct.ext'
  intro v p
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    LinearMap.zero_apply]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  have htangential' (a b : Fin n) :=
    LinearMap.congr_fun (htangential a b) (v ⊗ₜ[ℝ] p)
  have hcross' (a : Fin n) :=
    LinearMap.congr_fun (hcross a) (v ⊗ₜ[ℝ] p)
  have hcrossSwap' (a : Fin n) :=
    LinearMap.congr_fun (hcrossSwap a) (v ⊗ₜ[ℝ] p)
  have hlast' := LinearMap.congr_fun hlast (v ⊗ₜ[ℝ] p)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    at htangential' hcross' hcrossSwap' hlast'
  simp only [htangential', hcross', hcrossSwap', hlast',
    Finset.sum_const_zero, add_zero]


-- @@ L5499-5522 verbatim
theorem transverseStabilizerIsometry_relativeCasimir_cross_eq_zero
    {s t r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (source : Fin (s + 1) → ℕ) (target : Fin (t + 1) → ℕ)
    (F : HarmonicYoungSpace (n := n) source →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (G : HarmonicYoungSpace (n := n) target →ₗᵢ[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (horth : F.toLinearMap.adjoint.comp G.toLinearMap = 0)
    (hG : ∀ a b : Fin n,
      G.toLinearMap.comp (youngAmbientRotation target a b) =
        (youngAmbientRotation lam a.castSucc b.castSucc).comp G.toLinearMap) :
    (transverseTensorEmbeddingOfStabilizerIsometry
      lam source F).toLinearMap.adjoint.comp
        ((gtRelativeCasimir (n := n + 1) lam).comp
          (transverseTensorEmbeddingOfStabilizerIsometry
            lam target G).toLinearMap) = 0 := by
  rw [gtRelativeCasimir_eq_scalar_sub_mixed]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp,
    LinearMap.id_comp, LinearMap.comp_sub, LinearMap.comp_smul]
  rw [transverseStabilizerIsometry_adjoint_comp_of_orthogonal
    lam source target F G horth,
    transverseStabilizerIsometry_mixedRotation_cross_eq_zero
      lam source target F G horth hG]
  simp only [Nat.cast_add, Nat.cast_one, smul_zero, sub_self]


-- @@ L5524-5537 verbatim
theorem canonicalFullBranchFibre_adjoint_comp_of_ne
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1)
    (branch selected : FullBranchWeight lam)
    (hne : branch ≠ selected) :
    (canonicalFullBranchFibre lam hn branch).toLinearMap.adjoint.comp
      (canonicalFullBranchFibre lam hn selected).toLinearMap = 0 := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
  rw [LinearMap.adjoint_inner_right]
  exact canonicalFullBranchFibre_orthogonal lam hn branch selected hne q p


-- @@ L5539-5558 verbatim
theorem canonicalFullBranchFibre_adjoint_canonicalGelfandTsetlinFibre_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces mu h) :
    (canonicalFullBranchFibre lam hn branch).toLinearMap.adjoint.comp
      (canonicalGelfandTsetlinFibre lam mu h hgram).toLinearMap = 0 := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
  rw [LinearMap.adjoint_inner_right]
  exact (real_inner_comm
    (canonicalGelfandTsetlinFibre lam mu h hgram p)
    (canonicalFullBranchFibre lam hn branch q)).trans
      (canonicalGelfandTsetlinFibre_fullBranch_orthogonal_of_ne_selected
        lam mu h hn hgram branch hwrong p q)


-- @@ L5560-5577 verbatim
theorem gtFullTransverseEmbedding_relativeCasimir_cross_physical_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces mu h) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseTensorEmbedding lam mu h hgram).toLinearMap) = 0 := by
  exact transverseStabilizerIsometry_relativeCasimir_cross_eq_zero
    (s := r + 1) (t := r) (r := r + 1) (n := n)
    lam (fullBranchSignature branch) mu
    (canonicalFullBranchFibre lam hn branch)
    (canonicalGelfandTsetlinFibre lam mu h hgram)
    (canonicalFullBranchFibre_adjoint_canonicalGelfandTsetlinFibre_eq_zero
      lam mu h hn hgram branch hwrong)
    (canonicalGelfandTsetlinFibre_rotation_intertwine lam mu h hgram)


-- @@ L5579-5597 verbatim
theorem gtFullTransverseEmbedding_negativeRelativeCasimir_eq_zero_of_wrong_branch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces (raiseWeight mu row) hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        (gtTransverseNegativeSector lam mu row hnu hnuGram p)) = 0 := by
  have hz := LinearMap.congr_fun
    (gtFullTransverseEmbedding_relativeCasimir_cross_physical_eq_zero
      lam (raiseWeight mu row) hnu hn hnuGram branch hwrong)
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row p)
  exact hz


-- @@ L5599-5618 verbatim
theorem gtFullTransverseEmbedding_positiveRelativeCasimir_eq_zero_of_wrong_branch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        (gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram p)) = 0 := by
  have hz := LinearMap.congr_fun
    (gtFullTransverseEmbedding_relativeCasimir_cross_physical_eq_zero
      lam nu hnu hn hnuGram branch hwrong)
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row p)
  exact hz


-- @@ L5620-5645 verbatim
theorem gtFullTransverseEmbedding_normalizedNegativeRelativeCasimir_eq_zero_of_wrong_branch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces (raiseWeight mu row) hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        (normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise p)) = 0 := by
  change
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        ((normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise).toLinearMap p)) = 0
  rw [normalizedGTTransverseNegativeSector_toLinearMap,
    LinearMap.smul_apply, map_smul, map_smul,
    gtFullTransverseEmbedding_negativeRelativeCasimir_eq_zero_of_wrong_branch
      lam mu row hnu hnuGram hn branch hwrong p, smul_zero]


-- @@ L5647-5671 verbatim
theorem gtFullTransverseEmbedding_normalizedPositiveRelativeCasimir_eq_zero_of_wrong_branch
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ fullBranchOfInterlaces nu hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        (normalizedGTTransversePositiveSector lam mu nu row
          hmunu hmu hnu hnuGram p)) = 0 := by
  change
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
      (gtRelativeCasimir (n := n + 1) lam
        ((normalizedGTTransversePositiveSector lam mu nu row
          hmunu hmu hnu hnuGram).toLinearMap p)) = 0
  rw [normalizedGTTransversePositiveSector_toLinearMap,
    LinearMap.smul_apply, map_smul, map_smul,
    gtFullTransverseEmbedding_positiveRelativeCasimir_eq_zero_of_wrong_branch
      lam mu nu row hmunu hnu hnuGram hn branch hwrong p, smul_zero]


-- @@ L5673-5673 verbatim
end AllRankGTTransverseWrongBranchCompression


-- @@ L5675-5675 verbatim
end


-- @@ L5677-5677 verbatim
section



-- @@ L5680-5680 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L5682-5682 verbatim
namespace AllRankGTWallTransverseCrossOrthogonality


-- @@ L5684-5684 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L5685-5685 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L5686-5686 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L5687-5687 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L5688-5688 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L5689-5689 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression

-- @@ L5690-5690 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry

-- @@ L5691-5691 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

-- @@ L5692-5692 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L5693-5693 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L5694-5694 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L5695-5695 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L5696-5696 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L5697-5697 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L5699-5710 verbatim
private theorem canonicalFullBranchFibre_adjoint_transport_of_ne_metriccodes2_f07c51ce
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (branch selected : FullBranchWeight lam)
    (signature : Fin (r + 2) → ℕ)
    (hsignature : fullBranchSignature selected = signature)
    (hwrong : branch ≠ selected) :
    (canonicalFullBranchFibre lam hn branch).toLinearMap.adjoint.comp
      (hsignature ▸ (canonicalFullBranchFibre lam hn selected)).toLinearMap = 0 := by
  subst signature
  exact canonicalFullBranchFibre_adjoint_comp_of_ne
    lam hn branch selected hwrong


-- @@ L5712-5724 verbatim
theorem canonicalFullBranchFibre_adjoint_wallCanonicalFullBranchFibre_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (canonicalFullBranchFibre lam hn branch).toLinearMap.adjoint.comp
      (gtWallCanonicalFullBranchFibre lam mu h hn hlast).toLinearMap = 0 := by
  exact canonicalFullBranchFibre_adjoint_transport_of_ne_metriccodes2_f07c51ce
    lam hn branch (gtWallFullBranch lam mu h hlast)
    (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (gtWallFullBranch_signature lam mu h hlast) hwrong


-- @@ L5726-5742 verbatim
theorem gtFullTransverseEmbedding_adjoint_wallTensorEmbedding_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap = 0 := by
  exact transverseStabilizerIsometry_adjoint_comp_of_orthogonal
    (s := r + 1) (t := r + 1) (r := r + 1) (n := n)
    lam (fullBranchSignature branch)
    (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (canonicalFullBranchFibre lam hn branch)
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast)
    (canonicalFullBranchFibre_adjoint_wallCanonicalFullBranchFibre_eq_zero
      lam mu h hn hlast branch hwrong)


-- @@ L5744-5763 verbatim
theorem gtFullTransverseEmbedding_relativeCasimir_cross_wallTensorEmbedding_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap) = 0 := by
  exact transverseStabilizerIsometry_relativeCasimir_cross_eq_zero
    (s := r + 1) (t := r + 1) (r := r + 1) (n := n)
    lam (fullBranchSignature branch)
    (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
    (canonicalFullBranchFibre lam hn branch)
    (gtWallCanonicalFullBranchFibre lam mu h hn hlast)
    (canonicalFullBranchFibre_adjoint_wallCanonicalFullBranchFibre_eq_zero
      lam mu h hn hlast branch hwrong)
    (gtWallCanonicalFullBranchFibre_rotation_intertwine
      lam mu h hn hlast)


-- @@ L5765-5777 verbatim
theorem gtFullTransverseEmbedding_adjoint_wallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      (gtTransverseWallSector lam mu h hn hlast) = 0 := by
  unfold gtTransverseWallSector
  rw [← LinearMap.comp_assoc,
    gtFullTransverseEmbedding_adjoint_wallTensorEmbedding_eq_zero
      lam mu h hn hlast branch hwrong, LinearMap.zero_comp]


-- @@ L5779-5804 verbatim
theorem gtFullTransverseEmbedding_relativeCasimir_cross_wallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseWallSector lam mu h hn hlast)) = 0 := by
  unfold gtTransverseWallSector
  calc
    _ = ((gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap)).comp
        ((youngClebschRaise
          (raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (appendZeroWeight mu)
          (sum_raiseWeight (appendZeroWeight mu) (Fin.last (r + 1)))
          (Fin.last (r + 1))).comp
            (appendZeroRowIsometryEquiv mu).toLinearMap) := by
              ext p
              rfl
    _ = 0 := by
      rw [gtFullTransverseEmbedding_relativeCasimir_cross_wallTensorEmbedding_eq_zero
        lam mu h hn hlast branch hwrong, LinearMap.zero_comp]


-- @@ L5806-5817 verbatim
theorem gtFullTransverseEmbedding_adjoint_normalizedWallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap = 0 := by
  rw [normalizedGTTransverseWallSector_toLinearMap, LinearMap.comp_smul,
    gtFullTransverseEmbedding_adjoint_wallSector_eq_zero
      lam mu h hn hlast branch hwrong, smul_zero]


-- @@ L5819-5832 verbatim
theorem gtFullTransverseEmbedding_relativeCasimir_cross_normalizedWallSector_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (branch : FullBranchWeight lam)
    (hwrong : branch ≠ gtWallFullBranch lam mu h hlast) :
    (gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint.comp
      ((gtRelativeCasimir (n := n + 1) lam).comp
        (normalizedGTTransverseWallSector lam mu h hn hlast).toLinearMap) = 0 := by
  rw [normalizedGTTransverseWallSector_toLinearMap, LinearMap.comp_smul,
    LinearMap.comp_smul,
    gtFullTransverseEmbedding_relativeCasimir_cross_wallSector_eq_zero
      lam mu h hn hlast branch hwrong, smul_zero]


-- @@ L5834-5834 verbatim
end AllRankGTWallTransverseCrossOrthogonality


-- @@ L5836-5836 verbatim
end


-- @@ L5838-5838 verbatim
section



-- @@ L5841-5841 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L5843-5843 verbatim
namespace AllRankGTPhysicalWallAdditiveColumn


-- @@ L5845-5845 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L5846-5846 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L5847-5847 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L5848-5848 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition

-- @@ L5849-5849 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L5850-5850 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedWallCharacteristicAnnihilation

-- @@ L5851-5851 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn

-- @@ L5852-5852 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCrossBlock

-- @@ L5853-5853 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L5854-5854 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing

-- @@ L5855-5855 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L5856-5856 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransversePhysicalDiagonalColumn

-- @@ L5857-5857 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow

-- @@ L5858-5858 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization

-- @@ L5859-5859 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry

-- @@ L5860-5860 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

-- @@ L5861-5861 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCrossOrthogonality

-- @@ L5862-5862 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L5863-5863 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L5864-5864 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L5865-5865 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L5866-5866 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L5868-5891 verbatim
private theorem adjoint_eq_adjoint_isometric_range_projection_metriccodes2_c0c59de2
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : E →ₗᵢ[ℝ] F) (C : G →ₗ[ℝ] F)
    (hCA : LinearMap.range C ≤ LinearMap.range A.toLinearMap)
    (x : F) :
    C.adjoint x = C.adjoint (A (A.toLinearMap.adjoint x)) := by
  apply ext_inner_left ℝ
  intro p
  obtain ⟨q, hq⟩ := hCA ⟨p, rfl⟩
  change A q = C p at hq
  calc
    ⟪p, C.adjoint x⟫_ℝ = ⟪C p, x⟫_ℝ :=
      LinearMap.adjoint_inner_right C p x
    _ = ⟪A q, x⟫_ℝ := by rw [hq]
    _ = ⟪q, A.toLinearMap.adjoint x⟫_ℝ :=
      (LinearMap.adjoint_inner_right A.toLinearMap q x).symm
    _ = ⟪A q, A (A.toLinearMap.adjoint x)⟫_ℝ :=
      (A.inner_map_map q (A.toLinearMap.adjoint x)).symm
    _ = ⟪C p, A (A.toLinearMap.adjoint x)⟫_ℝ := by rw [hq]
    _ = ⟪p, C.adjoint (A (A.toLinearMap.adjoint x))⟫_ℝ :=
      (LinearMap.adjoint_inner_right C p _).symm


-- @@ L5893-6023 verbatim
theorem gtRelativeCasimir_normalizedWallSector_additiveColumn
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    let hw : 2 * (r + 1) + 5 ≤ n + 1 := by omega
    let B := normalizedGTTransverseWallSector lam mu h hw hlast
    (gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap =
      (-(wallShift (n + 1) (r + 1))) • B.toLinearMap +
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp
          (gtTransverseAxisCrossBlock lam mu h hgram B.toLinearMap) := by
  dsimp
  let hw : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  let B := normalizedGTTransverseWallSector lam mu h hw hlast
  let A := canonicalGelfandTsetlinAxisTensor lam mu h hgram
  let K := gtTransverseAxisCrossBlock lam mu h hgram B.toLinearMap
  let selected := fullBranchOfInterlaces mu h
  let wall := gtWallFullBranch lam mu h hlast
  change
    (gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap =
      (-(wallShift (n + 1) (r + 1))) • B.toLinearMap + A.comp K
  apply gtRelativeCasimir_comp_eq_smul_add_of_orthogonal_full_block_rows
    lam hw h.antitone_ambient B.toLinearMap A K
      (-(wallShift (n + 1) (r + 1)))
  · intro branch
    apply LinearMap.ext
    intro p
    apply ext_inner_left ℝ
    intro q
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    obtain ⟨z, hz⟩ :=
      normalizedGTTransverseWallSector_range_le_fullTransverse
        lam mu h hw hlast (show B p ∈ LinearMap.range B.toLinearMap from ⟨p, rfl⟩)
    change gtFullTransverseEmbedding lam hw wall z = B p at hz
    change ⟪gtFullAxisEmbedding lam hw branch q, B p⟫_ℝ = 0
    rw [← hz]
    exact gtFullAxisEmbedding_inner_transverse_eq_zero
      lam hw branch wall q z
  · intro branch
    apply LinearMap.ext
    intro p
    apply ext_inner_left ℝ
    intro q
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    have hp : A p ∈ LinearMap.range
        (gtFullAxisEmbedding lam hw selected).toLinearMap := by
      rw [gtFullAxisEmbedding_selected_range_eq_canonicalAxis
        lam mu h hw hgram]
      exact ⟨p, rfl⟩
    obtain ⟨z, hz⟩ := hp
    change gtFullAxisEmbedding lam hw selected z = A p at hz
    rw [← hz, real_inner_comm]
    exact gtFullAxisEmbedding_inner_transverse_eq_zero
      lam hw selected branch z q
  · intro branch
    by_cases hbranch : branch = selected
    · subst branch
      apply LinearMap.ext
      intro p
      change
        (gtFullAxisEmbedding lam hw selected).toLinearMap.adjoint
            (gtRelativeCasimir (n := n + 1) lam (B p)) =
          (gtFullAxisEmbedding lam hw selected).toLinearMap.adjoint
            (A (K p))
      have hrange :
          LinearMap.range
            (gtFullAxisEmbedding lam hw selected).toLinearMap ≤
              LinearMap.range
                (canonicalGelfandTsetlinAxisIsometry lam mu h hgram).toLinearMap := by
        rw [gtFullAxisEmbedding_selected_range_eq_canonicalAxis
          lam mu h hw hgram]
      have hproj := adjoint_eq_adjoint_isometric_range_projection_metriccodes2_c0c59de2
        (canonicalGelfandTsetlinAxisIsometry lam mu h hgram)
        (gtFullAxisEmbedding lam hw selected).toLinearMap hrange
        (gtRelativeCasimir (n := n + 1) lam (B p))
      change
        (gtFullAxisEmbedding lam hw selected).toLinearMap.adjoint
            (gtRelativeCasimir (n := n + 1) lam (B p)) =
          (gtFullAxisEmbedding lam hw selected).toLinearMap.adjoint
            (A (A.adjoint
              (gtRelativeCasimir (n := n + 1) lam (B p)))) at hproj
      exact hproj
    · have hsignature : fullBranchSignature branch ≠ appendZeroWeight mu := by
        intro heq
        apply hbranch
        apply fullBranchSignature_injective lam
        simpa [selected,
          fullBranchOfInterlaces_signature_eq_appendZeroWeight] using heq
      have hleft :
          (gtFullAxisEmbedding lam hw branch).toLinearMap.adjoint.comp
            ((gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap) = 0 := by
        apply LinearMap.ext
        intro p
        exact gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
          lam mu h hn branch hsignature B.toLinearMap
          (normalizedGTTransverseWallSector_rotation_intertwine
            lam mu h hw hlast) p
      rw [hleft]
      apply Eq.symm
      apply LinearMap.ext
      intro p
      apply ext_inner_left ℝ
      intro q
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
      rw [LinearMap.adjoint_inner_right]
      have hp : A (K p) ∈ LinearMap.range
          (gtFullAxisEmbedding lam hw selected).toLinearMap := by
        rw [gtFullAxisEmbedding_selected_range_eq_canonicalAxis
          lam mu h hw hgram]
        exact ⟨K p, rfl⟩
      obtain ⟨z, hz⟩ := hp
      change gtFullAxisEmbedding lam hw selected z = A (K p) at hz
      rw [← hz]
      exact gtFullAxisEmbedding_orthogonal
        lam hw branch selected hbranch q z
  · intro branch
    by_cases hbranch : branch = wall
    · subst branch
      apply LinearMap.ext
      intro p
      exact normalizedWallSector_selectedFullTensor_adjoint_eigen
        lam mu h hw hlast p
    · rw [gtFullTransverseEmbedding_relativeCasimir_cross_normalizedWallSector_eq_zero
        lam mu h hw hlast branch hbranch,
        gtFullTransverseEmbedding_adjoint_normalizedWallSector_eq_zero
          lam mu h hw hlast branch hbranch,
        smul_zero]


-- @@ L6025-6025 verbatim
end AllRankGTPhysicalWallAdditiveColumn


-- @@ L6027-6027 verbatim
end


-- @@ L6029-6029 verbatim
section



-- @@ L6032-6032 verbatim
open scoped BigOperators


-- @@ L6034-6034 verbatim
namespace AllRankGTTransverseEigenNodeSeparation


-- @@ L6036-6036 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L6037-6037 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L6038-6038 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L6039-6039 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement


-- @@ L6041-6087 verbatim
theorem negativeStabilizerNode_ne_signedAmbientNode_of_valid_raise
    {r n : ℕ} (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1))
    (hraise : Interlaces lam (raiseWeight mu row))
    (channel : Fin (r + 2) × Bool) :
    gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false)) ≠
      signedNode (ambientShift (n + 1) lam) channel := by
  have hweight : mu row < lam row.castSucc := by
    have hh := (hraise row).1
    simpa only [gt_iff_lt, raiseWeight, Function.update_self, Order.add_one_le_iff] using hh
  have hweightR : (mu row : ℝ) < (lam row.castSucc : ℝ) := by
    exact_mod_cast hweight
  have hupper :
      stabilizerShift (n + 1) mu row + 1 / 2 <
        ambientShift (n + 1) lam row.castSucc := by
    simp only [stabilizerShift, ambientShift, Fin.val_castSucc,
      Nat.cast_add, Nat.cast_one]
    linarith
  have hlower :
      ambientShift (n + 1) lam row.succ <
        stabilizerShift (n + 1) mu row + 1 / 2 := by
    linarith [hfinite.stabilizerShift_ge_succ row]
  rcases channel with ⟨j, sign⟩
  cases sign
  · simp only [gtStabilizerArrowheadNode_neg, one_div, signedNode, Bool.false_eq_true, ↓reduceIte,
      ne_eq]
    intro heq
    have hcoord :
        stabilizerShift (n + 1) mu row + 1 / 2 =
          ambientShift (n + 1) lam j := by linarith
    by_cases hji : j ≤ row.castSucc
    · have hmono := hfinite.ambientShift_strictAnti.antitone hji
      linarith
    · have hij : row.succ ≤ j := by
        have hlt : row.castSucc < j := lt_of_not_ge hji
        apply Fin.le_iff_val_le_val.mpr
        have hv : row.val < j.val := hlt
        exact Nat.succ_le_of_lt hv
      have hmono := hfinite.ambientShift_strictAnti.antitone hij
      linarith
  · simp only [gtStabilizerArrowheadNode_neg, one_div, signedNode, ↓reduceIte, ne_eq]
    have hM := hfinite.stabilizerShift_pos row
    have hL := hfinite.ambientShift_pos j
    linarith


-- @@ L6089-6137 verbatim
theorem positiveStabilizerNode_ne_signedAmbientNode_of_valid_lower
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1))
    (hlower : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (channel : Fin (r + 2) × Bool) :
    gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, true)) ≠
      signedNode (ambientShift (n + 1) lam) channel := by
  have hweight : lam row.succ < mu row := by
    have hh := (hnu row).2
    rw [hlower]
    simpa only [raiseWeight, Function.update_self, Order.lt_add_one_iff, ge_iff_le,
      Nat.succ_eq_add_one] using
      Nat.lt_succ_of_le hh
  have hweightR : (lam row.succ : ℝ) < (mu row : ℝ) := by
    exact_mod_cast hweight
  have hlower' :
      ambientShift (n + 1) lam row.succ <
        stabilizerShift (n + 1) mu row - 1 / 2 := by
    simp only [stabilizerShift, ambientShift, Fin.val_succ,
      Nat.cast_add, Nat.cast_one]
    linarith
  have hupper :
      stabilizerShift (n + 1) mu row - 1 / 2 <
        ambientShift (n + 1) lam row.castSucc := by
    linarith [hfinite.ambientShift_castSucc_ge row]
  rcases channel with ⟨j, sign⟩
  cases sign
  · simp only [gtStabilizerArrowheadNode_pos, one_div, signedNode, Bool.false_eq_true, ↓reduceIte,
      ne_eq]
    have hL := hfinite.ambientShift_pos j
    have hlowpos := hfinite.ambientShift_pos row.succ
    linarith
  · simp only [gtStabilizerArrowheadNode_pos, one_div, signedNode, ↓reduceIte, ne_eq]
    intro heq
    by_cases hji : j ≤ row.castSucc
    · have hmono := hfinite.ambientShift_strictAnti.antitone hji
      linarith
    · have hij : row.succ ≤ j := by
        have hlt : row.castSucc < j := lt_of_not_ge hji
        apply Fin.le_iff_val_le_val.mpr
        have hv : row.val < j.val := hlt
        exact Nat.succ_le_of_lt hv
      have hmono := hfinite.ambientShift_strictAnti.antitone hij
      linarith


-- @@ L6139-6139 verbatim
end AllRankGTTransverseEigenNodeSeparation


-- @@ L6141-6141 verbatim
end


-- @@ L6143-6143 verbatim
section



-- @@ L6146-6146 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L6148-6148 verbatim
namespace AllRankGTFullySelectedTransverseBranchProjection


-- @@ L6150-6150 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L6151-6151 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange

-- @@ L6152-6152 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L6153-6153 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L6154-6154 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L6155-6155 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L6156-6156 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L6157-6157 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L6158-6158 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L6159-6159 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L6160-6160 verbatim
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature

-- @@ L6161-6161 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L6163-6184 verbatim
theorem gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (tau : Fin (r + 1) → ℕ) (h : Interlaces lam tau)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hdom : Antitone lam)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam tau h) :
    LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces tau h)).toLinearMap =
      LinearMap.range
        (gtTransverseTensorEmbedding lam tau h hgram).toLinearMap := by
  change
    LinearMap.range
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          (canonicalFullBranchFibre lam hn
            (fullBranchOfInterlaces tau h)).toLinearMap) =
      LinearMap.range
        (TensorProduct.map (gtTransverseEuclideanIsometry n).toLinearMap
          (canonicalGelfandTsetlinFibre lam tau h hgram).toLinearMap)
  rw [TensorProduct.range_map, TensorProduct.range_map,
    canonicalGelfandTsetlinFibre_range_eq_selectedFullBranch
      lam tau h hn hdom hgram]


-- @@ L6186-6186 verbatim
end AllRankGTFullySelectedTransverseBranchProjection


-- @@ L6188-6188 verbatim
end


-- @@ L6190-6190 verbatim
section



-- @@ L6193-6193 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L6195-6195 verbatim
namespace AllRankGTPhysicalSelectedTwoBlockClosure


-- @@ L6197-6197 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L6198-6198 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition

-- @@ L6199-6199 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction

-- @@ L6200-6200 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L6201-6201 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L6202-6202 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness


-- @@ L6204-6221 verbatim
theorem linearIsometry_range_starProjection
    {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ H]
    (F : E →ₗᵢ[ℝ] H) (x : H) :
    (LinearMap.range F.toLinearMap).starProjection x =
      F (F.toLinearMap.adjoint x) := by
  apply (LinearMap.range F.toLinearMap).eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨F.toLinearMap.adjoint x, rfl⟩
  · rintro _ ⟨p, rfl⟩
    change ⟪x - F (F.toLinearMap.adjoint x), F p⟫_ℝ = 0
    rw [inner_sub_left]
    change
      ⟪x, F.toLinearMap p⟫_ℝ -
        ⟪F (F.toLinearMap.adjoint x), F p⟫_ℝ = 0
    rw [← LinearMap.adjoint_inner_left F.toLinearMap p x,
      F.inner_map_map, sub_self]


-- @@ L6223-6266 verbatim
theorem mem_submodule_of_complete_orthogonal_two_family_projections
    {ι κ H : Type*} [Finite ι] [Finite κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (U : ι → Submodule ℝ H) (V : κ → Submodule ℝ H)
    (hU : ∀ i j : ι, i ≠ j → U i ⟂ U j)
    (hV : ∀ i j : κ, i ≠ j → V i ⟂ V j)
    (hUV : ∀ i : ι, ∀ j : κ, U i ⟂ V j)
    (hcomplete : (⨆ i, U i) ⊔ (⨆ j, V j) = ⊤)
    (S : Submodule ℝ H) (x : H)
    (haxis : ∀ i : ι, (U i).starProjection x ∈ S)
    (htransverse : ∀ j : κ, (V j).starProjection x ∈ S) :
    x ∈ S := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype κ := Fintype.ofFinite κ
  let W : ι ⊕ κ → Submodule ℝ H := Sum.elim U V
  have hpair : ∀ a b : ι ⊕ κ, a ≠ b → W a ⟂ W b := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact hU i j (fun hij => hab (congrArg Sum.inl hij))
      | inr j => exact hUV i j
    | inr i =>
      cases b with
      | inl j => exact (hUV j i).symm
      | inr j => exact hV i j (fun hij => hab (congrArg Sum.inr hij))
  have horth : OrthogonalFamily ℝ
      (fun i : ι ⊕ κ => ↥(W i)) (fun i => (W i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise hpair
  have hspan : (⨆ i : ι ⊕ κ, W i) = ⊤ := by
    rw [iSup_sum]
    change (⨆ i, U i) ⊔ (⨆ j, V j) = ⊤
    exact hcomplete
  have hx : x ∈ ⨆ i : ι ⊕ κ, W i := by
    rw [hspan]
    trivial
  rw [← horth.sum_projection_of_mem_iSup x hx]
  apply S.sum_mem
  intro i _
  cases i with
  | inl j => exact haxis j
  | inr j => exact htransverse j


-- @@ L6268-6307 verbatim
theorem gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hn : 2 * r + 5 ≤ n + 1) (hdom : Antitone lam)
    (S : Submodule ℝ
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (x : SpherePacking.Euclidean (n + 1) ⊗[ℝ]
      HarmonicYoungSpace (n := n + 1) lam)
    (haxis : ∀ mu : FullBranchWeight lam,
      gtFullAxisEmbedding lam hn mu
        ((gtFullAxisEmbedding lam hn mu).toLinearMap.adjoint x) ∈ S)
    (htransverse : ∀ mu : FullBranchWeight lam,
      gtFullTransverseEmbedding lam hn mu
        ((gtFullTransverseEmbedding lam hn mu).toLinearMap.adjoint x) ∈ S) :
    x ∈ S := by
  apply mem_submodule_of_complete_orthogonal_two_family_projections
    (fun mu : FullBranchWeight lam =>
      LinearMap.range (gtFullAxisEmbedding lam hn mu).toLinearMap)
    (fun mu : FullBranchWeight lam =>
      LinearMap.range (gtFullTransverseEmbedding lam hn mu).toLinearMap)
    (S := S) (x := x)
  · intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullAxisEmbedding_orthogonal lam hn i j hij p q
  · intro i j hij
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullTransverseEmbedding_orthogonal lam hn i j hij p q
  · intro i j
    apply Submodule.isOrtho_iff_inner_eq.mpr
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact gtFullAxisEmbedding_inner_transverse_eq_zero lam hn i j p q
  · exact gtFullAxisTransverse_iSup_range_eq_top lam hn hdom
  · intro i
    rw [linearIsometry_range_starProjection]
    exact haxis i
  · intro i
    rw [linearIsometry_range_starProjection]
    exact htransverse i


-- @@ L6309-6309 verbatim
end AllRankGTPhysicalSelectedTwoBlockClosure


-- @@ L6311-6311 verbatim
end


-- @@ L6313-6313 verbatim
section



-- @@ L6316-6316 verbatim
open scoped InnerProductSpace TensorProduct


-- @@ L6318-6318 verbatim
namespace AllRankGTTransverseSelectedClebschRange


-- @@ L6320-6320 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L6321-6321 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartHighest

-- @@ L6322-6322 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy

-- @@ L6323-6323 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation

-- @@ L6324-6324 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L6325-6325 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality

-- @@ L6326-6326 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels

-- @@ L6327-6327 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L6328-6328 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L6330-6360 verbatim
theorem linearIsometry_projection_mem_range_of_adjoint_coordinate_mem
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (F : X →ₗᵢ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (hBF : LinearMap.range B ≤ LinearMap.range F.toLinearMap)
    (v : Y)
    (hcoordinate : F.toLinearMap.adjoint v ∈
      LinearMap.range (F.toLinearMap.adjoint.comp B)) :
    F (F.toLinearMap.adjoint v) ∈ LinearMap.range B := by
  obtain ⟨p, hp⟩ := hcoordinate
  obtain ⟨x, hx⟩ := hBF ⟨p, rfl⟩
  have hself := LinearMap.congr_fun F.adjoint_comp_self' x
  have hself' : F.toLinearMap.adjoint (F.toLinearMap x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hself
  have hcoord : F.toLinearMap.adjoint (B p) =
      F.toLinearMap.adjoint v := by
    simpa only [LinearMap.comp_apply] using hp
  change F.toLinearMap (F.toLinearMap.adjoint v) ∈ LinearMap.range B
  refine ⟨p, ?_⟩
  calc
    B p = F.toLinearMap x := hx.symm
    _ = F.toLinearMap
      (F.toLinearMap.adjoint (F.toLinearMap x)) :=
        congrArg F.toLinearMap hself'.symm
    _ = F.toLinearMap (F.toLinearMap.adjoint (B p)) :=
      congrArg (fun y : Y => F.toLinearMap (F.toLinearMap.adjoint y)) hx
    _ = F.toLinearMap (F.toLinearMap.adjoint v) :=
      congrArg F.toLinearMap hcoord


-- @@ L6362-6377 verbatim
theorem linearIsometry_projection_mem_range_of_adjoint_scalar
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (F : X →ₗᵢ[ℝ] Y) (B : Z →ₗ[ℝ] Y)
    (hBF : LinearMap.range B ≤ LinearMap.range F.toLinearMap)
    (v : Y) (p : Z) (d : ℝ)
    (hcoordinate : F.toLinearMap.adjoint v =
      d • F.toLinearMap.adjoint (B p)) :
    F (F.toLinearMap.adjoint v) ∈ LinearMap.range B := by
  apply linearIsometry_projection_mem_range_of_adjoint_coordinate_mem
    F B hBF v
  refine ⟨d • p, ?_⟩
  simpa only [LinearMap.comp_apply, map_smul] using hcoordinate.symm


-- @@ L6379-6396 verbatim
theorem linearMap_range_le_isometry_of_scaled_factor_of_range_eq
    {W X Y Z : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (F : X →ₗᵢ[ℝ] Y) (E : W →ₗᵢ[ℝ] Y)
    (B : Z →ₗ[ℝ] Y) (C : Z →ₗ[ℝ] W) (phase : ℝ)
    (hrange : LinearMap.range F.toLinearMap =
      LinearMap.range E.toLinearMap)
    (hfactor : B = phase • E.toLinearMap.comp C) :
    LinearMap.range B ≤ LinearMap.range F.toLinearMap := by
  intro y hy
  obtain ⟨p, rfl⟩ := hy
  rw [hrange]
  refine ⟨phase • C p, ?_⟩
  rw [map_smul, hfactor]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]


-- @@ L6398-6398 verbatim
end AllRankGTTransverseSelectedClebschRange


-- @@ L6400-6400 verbatim
end


-- @@ L6402-6402 verbatim
section



-- @@ L6405-6405 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L6407-6407 verbatim
namespace AllRankGTTransverseRetainedTwoBlockClosure


-- @@ L6409-6409 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L6410-6410 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L6411-6411 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L6412-6412 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition

-- @@ L6413-6413 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection

-- @@ L6414-6414 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow

-- @@ L6415-6415 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining

-- @@ L6416-6416 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L6417-6417 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure

-- @@ L6418-6418 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing

-- @@ L6419-6419 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L6420-6420 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition

-- @@ L6421-6421 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange

-- @@ L6422-6422 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L6423-6423 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWrongBranchCompression

-- @@ L6424-6424 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow

-- @@ L6425-6425 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L6426-6426 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

-- @@ L6427-6427 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

-- @@ L6428-6428 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

-- @@ L6429-6429 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L6430-6430 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L6431-6431 verbatim
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

-- @@ L6432-6432 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

-- @@ L6433-6433 verbatim
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature

-- @@ L6434-6434 verbatim
open MetricCodes.Spherical.ThreeRowYoungBranching


-- @@ L6436-6465 verbatim
theorem normalizedGTTransverseNegativeSector_range_le_selectedFullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hn : 2 * (r + 1) + 5 ≤ n + 1) :
    LinearMap.range
        (normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise).toLinearMap ≤
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces (raiseWeight mu row) hnu)).toLinearMap := by
  apply linearMap_range_le_isometry_of_scaled_factor_of_range_eq
    (gtFullTransverseEmbedding lam hn
      (fullBranchOfInterlaces (raiseWeight mu row) hnu))
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hnuGram)
    (normalizedGTTransverseNegativeSector lam mu kappa row
      hnu hnuGram hfinite hraise).toLinearMap
    (youngClebschRaise (raiseWeight mu row) mu
      (sum_raiseWeight mu row) row)
    (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
      weylEdgeRatio n mu row))⁻¹
  · exact gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
      lam (raiseWeight mu row) hnu hn hnu.antitone_ambient hnuGram
  · exact normalizedGTTransverseNegativeSector_toLinearMap
      lam mu kappa row hnu hnuGram hfinite hraise


-- @@ L6467-6493 verbatim
theorem normalizedGTTransversePositiveSector_range_le_selectedFullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1) :
    LinearMap.range
        (normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram).toLinearMap ≤
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces nu hnu)).toLinearMap := by
  apply linearMap_range_le_isometry_of_scaled_factor_of_range_eq
    (gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces nu hnu))
    (gtTransverseTensorEmbedding lam nu hnu hnuGram)
    (normalizedGTTransversePositiveSector
      lam mu nu row hmunu hmu hnu hnuGram).toLinearMap
    (youngClebschLower nu mu
      (by rw [hmunu]; exact sum_raiseWeight nu row) row)
    (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹
  · exact gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
      lam nu hnu hn hnu.antitone_ambient hnuGram
  · exact normalizedGTTransversePositiveSector_toLinearMap
      lam mu nu row hmunu hmu hnu hnuGram


-- @@ L6495-6570 verbatim
theorem gtTransverseNegativeSector_relativeCasimir_mem_axis_sup_sector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (row : Fin (r + 1))
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtRelativeCasimir lam
      (normalizedGTTransverseNegativeSector lam mu kappa row
        hnu hnuGram hfinite hraise p) ∈
      LinearMap.range
        (canonicalGelfandTsetlinAxisIsometry
          lam mu hmu hmuGram).toLinearMap ⊔
      LinearMap.range
        (normalizedGTTransverseNegativeSector lam mu kappa row
          hnu hnuGram hfinite hraise).toLinearMap := by
  let hn : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  let A := canonicalGelfandTsetlinAxisIsometry lam mu hmu hmuGram
  let B := normalizedGTTransverseNegativeSector lam mu kappa row
    hnu hnuGram hfinite hraise
  let S := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap
  change gtRelativeCasimir lam (B p) ∈ S
  apply gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
    lam hn hmu.antitone_ambient S (gtRelativeCasimir lam (B p))
  · intro branch
    by_cases hs : fullBranchSignature branch = appendZeroWeight mu
    · have hb :=
        (fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
          mu hmu branch).mpr hs
      subst branch
      apply Submodule.mem_sup_left
      rw [← gtFullAxisEmbedding_selected_range_eq_canonicalAxis
        lam mu hmu hn hmuGram]
      exact ⟨_, rfl⟩
    · have hz :=
        gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
          lam mu hmu hstable branch hs B.toLinearMap
          (normalizedGTTransverseNegativeSector_rotation_intertwine
            lam mu kappa row hnu hnuGram hfinite hraise) p
      change gtFullAxisEmbedding lam hn branch
        ((gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      change (gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
        (gtRelativeCasimir lam (B p)) = 0 at hz
      rw [hz, map_zero]
      exact S.zero_mem
  · intro branch
    by_cases hb : branch =
        fullBranchOfInterlaces (raiseWeight mu row) hnu
    · subst branch
      apply Submodule.mem_sup_right
      apply linearIsometry_projection_mem_range_of_adjoint_scalar
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces (raiseWeight mu row) hnu))
        B.toLinearMap
        (normalizedGTTransverseNegativeSector_range_le_selectedFullTransverse
          lam mu kappa row hnu hnuGram hfinite hraise hn)
        (gtRelativeCasimir lam (B p)) p
        (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, false)))
      exact negativeSector_selectedFullTensor_adjoint_eigen
        lam mu kappa row hnu hnuGram hfinite hraise hn p
    · have hz :=
        gtFullTransverseEmbedding_normalizedNegativeRelativeCasimir_eq_zero_of_wrong_branch
          lam mu kappa row hnu hnuGram hfinite hraise hn branch hb p
      change gtFullTransverseEmbedding lam hn branch
        ((gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      rw [hz, map_zero]
      exact S.zero_mem


-- @@ L6572-6643 verbatim
theorem gtTransversePositiveSector_relativeCasimir_mem_axis_sup_sector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hstable : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtRelativeCasimir lam
      (normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram p) ∈
      LinearMap.range
        (canonicalGelfandTsetlinAxisIsometry
          lam mu hmu hmuGram).toLinearMap ⊔
      LinearMap.range
        (normalizedGTTransversePositiveSector
          lam mu nu row hmunu hmu hnu hnuGram).toLinearMap := by
  let hn : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  let A := canonicalGelfandTsetlinAxisIsometry lam mu hmu hmuGram
  let B := normalizedGTTransversePositiveSector
    lam mu nu row hmunu hmu hnu hnuGram
  let S := LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap
  change gtRelativeCasimir lam (B p) ∈ S
  apply gtPhysicalTensor_mem_submodule_of_full_axis_transverse_projection
    lam hn hmu.antitone_ambient S (gtRelativeCasimir lam (B p))
  · intro branch
    by_cases hs : fullBranchSignature branch = appendZeroWeight mu
    · have hb :=
        (fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
          mu hmu branch).mpr hs
      subst branch
      apply Submodule.mem_sup_left
      rw [← gtFullAxisEmbedding_selected_range_eq_canonicalAxis
        lam mu hmu hn hmuGram]
      exact ⟨_, rfl⟩
    · have hz :=
        gtFullAxisEmbedding_adjoint_relativeCasimir_stabilizerSector_eq_zero
          lam mu hmu hstable branch hs B.toLinearMap
          (normalizedGTTransversePositiveSector_rotation_intertwine
            lam mu nu row hmunu hmu hnu hnuGram) p
      change gtFullAxisEmbedding lam hn branch
        ((gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      change (gtFullAxisEmbedding lam hn branch).toLinearMap.adjoint
        (gtRelativeCasimir lam (B p)) = 0 at hz
      rw [hz, map_zero]
      exact S.zero_mem
  · intro branch
    by_cases hb : branch = fullBranchOfInterlaces nu hnu
    · subst branch
      apply Submodule.mem_sup_right
      apply linearIsometry_projection_mem_range_of_adjoint_scalar
        (gtFullTransverseEmbedding lam hn (fullBranchOfInterlaces nu hnu))
        B.toLinearMap
        (normalizedGTTransversePositiveSector_range_le_selectedFullTransverse
          lam mu nu row hmunu hmu hnu hnuGram hn)
        (gtRelativeCasimir lam (B p)) p
        (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) (.inr (row, true)))
      exact positiveSector_selectedFullTensor_adjoint_eigen
        lam mu nu row hmunu hmu hnu hnuGram hn p
    · have hz :=
        gtFullTransverseEmbedding_normalizedPositiveRelativeCasimir_eq_zero_of_wrong_branch
          lam mu nu row hmunu hmu hnu hnuGram hn branch hb p
      change gtFullTransverseEmbedding lam hn branch
        ((gtFullTransverseEmbedding lam hn branch).toLinearMap.adjoint
          (gtRelativeCasimir lam (B p))) ∈ S
      rw [hz, map_zero]
      exact S.zero_mem


-- @@ L6645-6645 verbatim
end AllRankGTTransverseRetainedTwoBlockClosure


-- @@ L6647-6647 verbatim
end


-- @@ L6649-6649 verbatim
section



-- @@ L6652-6652 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L6654-6654 verbatim
namespace AllRankGTAxisCompressedValidNodeRoot


-- @@ L6656-6656 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L6657-6657 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L6658-6658 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L6659-6659 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L6660-6660 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L6661-6661 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L6662-6662 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L6663-6663 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue


-- @@ L6665-6675 verbatim
/-- The signed characteristic adjugate expressed as a sum of characteristic projectors weighted
by the nodal polynomials with one node removed. -/
def signedCharacteristicAdjugate {r : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ) (T : Module.End ℝ V)
    (z : ℝ) : Module.End ℝ V :=
  ∑ channel : Fin (r + 1) × Bool,
    (Lagrange.nodal
      ((Finset.univ : Finset (Fin (r + 1) × Bool)).erase channel)
      (signedNode L)).eval z •
        signedCharacteristicProjector L T channel


-- @@ L6677-6724 verbatim
theorem signedCharacteristicAdjugate_resolvent_apply
    {r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ)
    (hL : Function.Injective (signedNode L))
    (T : Module.End ℝ V) (z : ℝ) (v : V)
    (hchar : Polynomial.aeval T (signedAmbientCharacteristic L) v = 0) :
    (z • (LinearMap.id : Module.End ℝ V) - T)
        (signedCharacteristicAdjugate L T z v) =
      (signedAmbientCharacteristic L).eval z • v := by
  classical
  unfold signedCharacteristicAdjugate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.sum_apply]
  rw [Finset.smul_sum, map_sum, ← Finset.sum_sub_distrib]
  have hterm (channel : Fin (r + 1) × Bool) :
      z • ((Lagrange.nodal
          ((Finset.univ : Finset (Fin (r + 1) × Bool)).erase channel)
          (signedNode L)).eval z •
            signedCharacteristicProjector L T channel v) -
        T ((Lagrange.nodal
          ((Finset.univ : Finset (Fin (r + 1) × Bool)).erase channel)
          (signedNode L)).eval z •
            signedCharacteristicProjector L T channel v) =
        (signedAmbientCharacteristic L).eval z •
          signedCharacteristicProjector L T channel v := by
    rw [map_smul,
      signedCharacteristicProjector_eigen_of_aeval_apply
        L T channel v hchar,
      smul_smul, smul_smul, ← sub_smul]
    congr 1
    have hnodal := congrArg (Polynomial.eval z)
      (Lagrange.nodal_eq_mul_nodal_erase
        (s := (Finset.univ : Finset (Fin (r + 1) × Bool)))
        (v := signedNode L) (Finset.mem_univ channel))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hnodal
    change
      z * _ - _ * signedNode L channel =
        (signedAmbientCharacteristic L).eval z
    change
      z * _ - _ * signedNode L channel =
        (Lagrange.nodal Finset.univ (signedNode L)).eval z
    nlinarith
  simp_rw [hterm]
  rw [← Finset.smul_sum]
  congr 1
  simpa only [LinearMap.sum_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (sum_signedCharacteristicProjector L hL T) v


-- @@ L6726-6748 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_eq_adjugate_inner
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) (z : ℝ) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval z =
      ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
        signedCharacteristicAdjugate
          (ambientShift (n + 1) lam)
          (gtRelativeCasimir (n := n + 1) lam) z
            (canonicalGelfandTsetlinAxisTensor lam mu h hgram q)⟫_ℝ := by
  classical
  rw [gtAxisCompressedCharacteristicMinor_eq_sum_nodal_erase
    lam mu h hgram hfinite p q]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, signedCharacteristicAdjugate,
    LinearMap.sum_apply, inner_sum, LinearMap.smul_apply,
    real_inner_smul_right,
    gtAxisCompressedSignedProjectorCoefficient]
  apply Finset.sum_congr rfl
  intro channel _
  ring


-- @@ L6750-6795 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_eq_zero_of_arrowhead_operator_row
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (node : ℝ)
    (coupling : Module.End ℝ (HarmonicYoungSpace (n := n) mu))
    (hcoupling : Function.Injective coupling)
    (horth : B.adjoint
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram q) = 0)
    (hchar :
      Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram q) = 0)
    (hrow : ∀ x : SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam,
      B.adjoint (gtRelativeCasimir (n := n + 1) lam x) =
        node • B.adjoint x +
          coupling ((canonicalGelfandTsetlinAxisTensor
            lam mu h hgram).adjoint x)) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval node = 0 := by
  let A := canonicalGelfandTsetlinAxisTensor lam mu h hgram
  let T := gtRelativeCasimir (n := n + 1) lam
  let v := signedCharacteristicAdjugate
    (ambientShift (n + 1) lam) T node (A q)
  have hresolvent := signedCharacteristicAdjugate_resolvent_apply
    (ambientShift (n + 1) lam)
    (signedNode_injective hfinite.ambientShift_pos
      hfinite.ambientShift_strictAnti.injective)
    T node (A q) hchar
  change node • v - T v =
    (gtChannelCharacteristicPolynomial (n + 1) lam).eval node • A q at hresolvent
  have hprojected := congrArg B.adjoint hresolvent
  rw [map_sub, map_smul, map_smul, horth, smul_zero,
    hrow v] at hprojected
  have haxis : A.adjoint v = 0 := by
    apply hcoupling
    simpa only [map_zero, sub_add_cancel_left, neg_eq_zero] using hprojected
  rw [gtAxisCompressedCharacteristicMinor_eval_eq_adjugate_inner
    lam mu h hgram hfinite p q node]
  change ⟪A p, v⟫_ℝ = 0
  rw [← LinearMap.adjoint_inner_right A p v, haxis, inner_zero_right]


-- @@ L6797-6797 verbatim
end AllRankGTAxisCompressedValidNodeRoot


-- @@ L6799-6799 verbatim
end


-- @@ L6801-6801 verbatim
end HigherHarmonicYoung


-- @@ L6803-6803 verbatim
section



-- @@ L6806-6806 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L6808-6808 verbatim
namespace HigherYoungAllRankGTCanonicalAxisSignedCharacteristic


-- @@ L6810-6810 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L6811-6811 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L6812-6812 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L6813-6813 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral

-- @@ L6814-6814 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L6815-6815 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness

-- @@ L6816-6816 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph

-- @@ L6817-6817 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue


-- @@ L6819-6833 verbatim
theorem gtChannelCharacteristic_aeval_canonicalAxis_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by
  simpa only [canonicalGelfandTsetlinAxisTensor_apply, EuclideanSpace.basisFun_apply,
    canonicalGelfandTsetlinFibre_apply, TensorProduct.tmul_smul, map_smul, smul_eq_zero,
      inv_eq_zero, pow_zero,
    Module.End.one_apply] using
    gtChannelCharacteristic_aeval_apply_canonicalAxis_iterate_eq_zero lam mu h hgram p
      (canonicalGelfandTsetlinAxisTensor_mem_gtSignedEigenvectorSpan lam mu h hn hgram p) 0


-- @@ L6835-6835 verbatim
end HigherYoungAllRankGTCanonicalAxisSignedCharacteristic


-- @@ L6837-6837 verbatim
end


-- @@ L6839-6839 verbatim
namespace HigherHarmonicYoung


-- @@ L6841-6841 verbatim
section



-- @@ L6844-6844 verbatim
open scoped BigOperators


-- @@ L6846-6846 verbatim
namespace AllRankGTAmbientCharacteristicAtTransverseNode


-- @@ L6848-6848 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L6849-6849 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

-- @@ L6850-6850 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue


-- @@ L6852-6859 verbatim
theorem signedAmbientCharacteristic_eval_ne_zero_of_forall_ne
    {r : ℕ} (L : Fin (r + 1) → ℝ) (d : ℝ)
    (hnode : ∀ i : Fin (r + 1) × Bool, d ≠ signedNode L i) :
    (signedAmbientCharacteristic L).eval d ≠ 0 := by
  unfold signedAmbientCharacteristic
  apply Lagrange.eval_nodal_not_at_node
  intro i _
  exact hnode i


-- @@ L6861-6867 verbatim
theorem gtChannelCharacteristicPolynomial_eval_ne_zero_of_forall_ne
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (d : ℝ)
    (hnode : ∀ i : Fin (r + 1) × Bool,
      d ≠ signedNode (ambientShift n lam) i) :
    (gtChannelCharacteristicPolynomial n lam).eval d ≠ 0 :=
  signedAmbientCharacteristic_eval_ne_zero_of_forall_ne
    (ambientShift n lam) d hnode


-- @@ L6869-6869 verbatim
end AllRankGTAmbientCharacteristicAtTransverseNode


-- @@ L6871-6871 verbatim
end


-- @@ L6873-6873 verbatim
section



-- @@ L6876-6876 verbatim
open scoped InnerProductSpace


-- @@ L6878-6878 verbatim
namespace AllRankGTTransverseCouplingNonzero


-- @@ L6880-6888 verbatim
theorem polynomial_eigenvector_eq_zero_of_annihilating_eval_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V) (P : Polynomial ℝ)
    (d : ℝ) (v : V)
    (heigen : T v = d • v)
    (hchar : Polynomial.aeval T P v = 0)
    (heval : P.eval d ≠ 0) : v = 0 := by
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul heigen] at hchar
  exact (smul_eq_zero.mp hchar).resolve_left heval


-- @@ L6890-6890 verbatim
end AllRankGTTransverseCouplingNonzero


-- @@ L6892-6892 verbatim
end


-- @@ L6894-6894 verbatim
section



-- @@ L6897-6897 verbatim
open scoped InnerProductSpace TensorProduct


-- @@ L6899-6899 verbatim
namespace AllRankGTCartanSpectralCouplingNonvanishing


-- @@ L6901-6901 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L6902-6902 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L6903-6903 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode

-- @@ L6904-6904 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L6905-6905 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero

-- @@ L6906-6906 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue


-- @@ L6908-6921 verbatim
theorem arrowhead_eigen_of_coupling_kernel
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (p : E) (hp : K p = 0) :
    T (B p) = d • B p := by
  have h := LinearMap.congr_fun hrow p
  simpa only [LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, hp, map_zero, add_zero] using h


-- @@ L6923-6940 verbatim
theorem arrowhead_coupling_eq_zero_of_apply_eq_zero
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (hB : Function.Injective B)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0)
    (p : E) (hp : K p = 0) : p = 0 := by
  have heigen := arrowhead_eigen_of_coupling_kernel
    T B A K d hrow p hp
  have hzero := polynomial_eigenvector_eq_zero_of_annihilating_eval_ne_zero
    T P d (B p) heigen (hchar p) heval
  exact hB (by simpa only [map_zero] using hzero)


-- @@ L6942-6959 verbatim
theorem arrowhead_coupling_injective_of_characteristic
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (hB : Function.Injective B)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0) :
    Function.Injective K := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply arrowhead_coupling_eq_zero_of_apply_eq_zero
    T B hB A K P d hrow hchar heval (p - q)
  rw [map_sub, hpq, sub_self]


-- @@ L6961-6975 verbatim
theorem arrowhead_isometric_coupling_injective_of_characteristic
    {E F V : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗᵢ[ℝ] V)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B.toLinearMap = d • B.toLinearMap + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0) :
    Function.Injective K :=
  arrowhead_coupling_injective_of_characteristic
    T B.toLinearMap B.injective A K P d hrow hchar heval


-- @@ L6977-7002 verbatim
theorem gtSignedArrowheadCoupling_injective
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (B : E →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam))
    (A : F →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam))
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (hrow :
      (gtRelativeCasimir (n := n) lam).comp B.toLinearMap =
        d • B.toLinearMap + A.comp K)
    (hchar : ∀ p : E,
      Polynomial.aeval (gtRelativeCasimir (n := n) lam)
        (gtChannelCharacteristicPolynomial n lam) (B p) = 0)
    (hnode : ∀ i : Fin (r + 1) × Bool,
      d ≠ signedNode (HigherChannel.ambientShift n lam) i) :
    Function.Injective K := by
  apply arrowhead_isometric_coupling_injective_of_characteristic
    (gtRelativeCasimir (n := n) lam) B A K
    (gtChannelCharacteristicPolynomial n lam) d hrow hchar
  exact gtChannelCharacteristicPolynomial_eval_ne_zero_of_forall_ne
    lam d hnode


-- @@ L7004-7004 verbatim
end AllRankGTCartanSpectralCouplingNonvanishing


-- @@ L7006-7006 verbatim
end


-- @@ L7008-7008 verbatim
section



-- @@ L7011-7011 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L7013-7013 verbatim
namespace AllRankGTValidTransverseMinorRoots


-- @@ L7015-7015 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L7016-7016 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L7017-7017 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L7018-7018 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L7019-7019 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot

-- @@ L7020-7020 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCanonicalAxisSignedCharacteristic

-- @@ L7021-7021 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L7022-7022 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing

-- @@ L7023-7023 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent

-- @@ L7024-7024 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L7025-7025 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L7026-7026 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow

-- @@ L7027-7027 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L7028-7028 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

-- @@ L7029-7029 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue






-- @@ L7035-7045 verbatim
private theorem end_adjoint_injective_of_injective_metriccodes2_f07ed3eb
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (K : Module.End ℝ V)
    (hK : Function.Injective K) : Function.Injective K.adjoint := by
  have hsurjective : Function.Surjective K :=
    LinearMap.injective_iff_surjective.mp hK
  have hrange : K.range = ⊤ := LinearMap.range_eq_top.mpr hsurjective
  have horthogonal := LinearMap.orthogonal_range K
  have hkernel : K.adjoint.ker = ⊥ := by
    simpa only [hrange, Submodule.top_orthogonal_eq_bot] using horthogonal.symm
  exact LinearMap.ker_eq_bot.mp hkernel


-- @@ L7047-7060 verbatim
private theorem gtActualPhysicalColumn_adjoint_row_metriccodes2_f07ed3eb
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (A B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (node : ℝ) (K : Module.End ℝ (HarmonicYoungSpace (n := n) mu))
    (hcolumn : (gtRelativeCasimir (n := n + 1) lam).comp B =
      node • B + A.comp K) :
    B.adjoint.comp (gtRelativeCasimir (n := n + 1) lam) =
      node • B.adjoint + K.adjoint.comp A.adjoint := by
  have hadjoint := congrArg LinearMap.adjoint hcolumn
  simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    gtRelativeCasimir_adjoint, map_add, map_smul] using hadjoint


-- @@ L7062-7108 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram
      (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (B : HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (node : ℝ)
    (K : Module.End ℝ (HarmonicYoungSpace (n := n) mu))
    (horthogonal : ∀ p q : HarmonicYoungSpace (n := n) mu,
      ⟪canonicalGelfandTsetlinAxisTensor lam mu h hgram p,
        B q⟫_ℝ = 0)
    (hcolumn :
      (gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap =
        node • B.toLinearMap +
          (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp K)
    (hsector : ∀ p : HarmonicYoungSpace (n := n) mu,
      Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam) (B p) = 0)
    (hnode : ∀ i : Fin (r + 2) × Bool,
      node ≠ signedNode (ambientShift (n + 1) lam) i)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval node = 0 := by
  have hK : Function.Injective K :=
    gtSignedArrowheadCoupling_injective lam B
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram)
      K node hcolumn hsector hnode
  have hKadjoint : Function.Injective K.adjoint :=
    end_adjoint_injective_of_injective_metriccodes2_f07ed3eb K hK
  apply gtAxisCompressedCharacteristicMinor_eval_eq_zero_of_arrowhead_operator_row
    lam mu h hgram hfinite p q B.toLinearMap node K.adjoint hKadjoint
  · apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [LinearMap.adjoint_inner_right, real_inner_comm]
    exact horthogonal q _
  · exact gtChannelCharacteristic_aeval_canonicalAxis_eq_zero
      lam mu h hn hgram q
  · intro x
    have hrow := LinearMap.congr_fun
      (gtActualPhysicalColumn_adjoint_row_metriccodes2_f07ed3eb lam mu
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram)
        B.toLinearMap node K hcolumn) x
    simpa only [LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply] using hrow


-- @@ L7110-7110 verbatim
end AllRankGTValidTransverseMinorRoots


-- @@ L7112-7112 verbatim
end


-- @@ L7114-7114 verbatim
section



-- @@ L7117-7117 verbatim
namespace AllRankGTAdjacentCommonInterlacing


-- @@ L7119-7119 verbatim
open MetricCodes.Spherical.HigherChannel


-- @@ L7121-7124 verbatim
/-- The prefix of a stabilizer weight obtained by dropping its final coordinate. -/
def gtSelectedPrefixWeight {r : ℕ}
    (mu : Fin (r + 1) → ℕ) : Fin r → ℕ :=
  fun j => mu j.castSucc


-- @@ L7126-7134 verbatim
theorem gtSelectedPrefixWeight_finiteInterlacing
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (hn : 2 * r + 4 ≤ n) (hdom : Antitone mu) :
    FiniteInterlacing n mu (gtSelectedPrefixWeight mu) := by
  refine ⟨hn, ?_⟩
  intro j
  constructor
  · exact le_rfl
  · exact hdom (Fin.castSucc_le_succ j)


-- @@ L7136-7164 verbatim
theorem gtSelectedPrefixWeight_finiteInterlacing_raise
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hn : 2 * r + 4 ≤ n)
    (hdom : Antitone mu)
    (hraiseDom : Antitone (raiseWeight mu row)) :
    FiniteInterlacing n (raiseWeight mu row)
      (gtSelectedPrefixWeight mu) := by
  refine ⟨hn, ?_⟩
  intro j
  constructor
  · change mu j.castSucc ≤ raiseWeight mu row j.castSucc
    by_cases hrow : j.castSucc = row
    · subst row
      simp only [raiseWeight, Function.update_self, le_add_iff_nonneg_right, zero_le]
    · simp only [raiseWeight, ne_eq, hrow, not_false_eq_true, Function.update_of_ne, Std.le_refl]
  · by_cases hrow : j.succ = row
    · have hne : j.castSucc ≠ row := by
        intro heq
        have hlt : j.castSucc < j.succ :=
          Fin.castSucc_lt_succ_iff.mpr le_rfl
        rw [heq, hrow] at hlt
        exact (lt_irrefl _ hlt)
      have hle := hraiseDom (Fin.castSucc_le_succ j)
      simpa only [raiseWeight, hrow, Function.update_self, gtSelectedPrefixWeight,
        Order.add_one_le_iff, gt_iff_lt, ne_eq, hne, not_false_eq_true,
        Function.update_of_ne] using hle
    · change raiseWeight mu row j.succ ≤ mu j.castSucc
      simpa only [raiseWeight, ne_eq, hrow, not_false_eq_true, Function.update_of_ne] using
        hdom (Fin.castSucc_le_succ j)


-- @@ L7166-7166 verbatim
end AllRankGTAdjacentCommonInterlacing


-- @@ L7168-7168 verbatim
end


-- @@ L7170-7170 verbatim
section



-- @@ L7173-7173 verbatim
namespace AllRankGTValidTransverseSignedIndex


-- @@ L7175-7175 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L7176-7176 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L7177-7177 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L7178-7178 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L7179-7179 verbatim
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower


-- @@ L7181-7181 verbatim
end AllRankGTValidTransverseSignedIndex


-- @@ L7183-7183 verbatim
end


-- @@ L7185-7185 verbatim
section



-- @@ L7188-7188 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L7190-7190 verbatim
namespace AllRankGTValidTransverseSectorFamily


-- @@ L7192-7192 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L7193-7193 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L7194-7194 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L7195-7195 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing

-- @@ L7196-7196 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L7197-7197 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent

-- @@ L7198-7198 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L7199-7199 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector

-- @@ L7200-7200 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

-- @@ L7201-7201 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L7202-7202 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow

-- @@ L7203-7203 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseMinorRoots

-- @@ L7204-7204 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSignedIndex

-- @@ L7205-7205 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L7206-7206 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

-- @@ L7207-7207 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L7208-7208 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L7209-7209 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

-- @@ L7210-7210 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L7211-7211 verbatim
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability

-- @@ L7212-7212 verbatim
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower


-- @@ L7214-7236 verbatim
theorem normalizedNegativeSector_canonicalAxis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      normalizedGTTransverseNegativeSector
        lam mu kappa row hnu hnuGram hfinite hraise q⟫_ℝ = 0 := by
  change
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      (Real.sqrt (internalRowLowerGramScalar (raiseWeight mu row) row *
        weylEdgeRatio n mu row))⁻¹ •
        gtTransverseNegativeSector lam mu row hnu hnuGram q⟫_ℝ = 0
  rw [real_inner_smul_right, real_inner_comm,
    gtTransverseNegativeSector_axis_inner_eq_zero
      lam mu row hnu hnuGram hmu hmuGram q p, mul_zero]


-- @@ L7238-7256 verbatim
theorem normalizedPositiveSector_canonicalAxis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      normalizedGTTransversePositiveSector
        lam mu nu row hmunu hmu hnu hnuGram q⟫_ℝ = 0 := by
  change
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      (Real.sqrt (internalRowLowerGramScalar mu row))⁻¹ •
        gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram q⟫_ℝ = 0
  rw [real_inner_smul_right, real_inner_comm,
    gtTransversePositiveSector_axis_inner_eq_zero
      lam mu nu row hmunu hnu hnuGram hmu hmuGram q p, mul_zero]


-- @@ L7258-7258 verbatim
end AllRankGTValidTransverseSectorFamily


-- @@ L7260-7260 verbatim
end


-- @@ L7262-7262 verbatim
section



-- @@ L7265-7265 verbatim
open scoped BigOperators InnerProductSpace TensorProduct


-- @@ L7267-7267 verbatim
namespace AllRankGTUnconditionalCharacteristicMinor


-- @@ L7269-7269 verbatim
open MetricCodes.Spherical.HigherChannel

-- @@ L7270-7270 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung

-- @@ L7271-7271 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

-- @@ L7272-7272 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor

-- @@ L7273-7273 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentWallCharacteristicFactor

-- @@ L7274-7274 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing

-- @@ L7275-7275 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCharacteristicMinorOfValidRoots

-- @@ L7276-7276 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

-- @@ L7277-7278 verbatim
open
  MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseCharacteristicAnnihilation

-- @@ L7279-7279 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector

-- @@ L7280-7280 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedWallCharacteristicAnnihilation

-- @@ L7281-7281 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPresentWallSignedNodeSeparation

-- @@ L7282-7282 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalWallAdditiveColumn

-- @@ L7283-7283 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCrossBlock

-- @@ L7284-7284 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector

-- @@ L7285-7285 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation

-- @@ L7286-7286 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseRetainedTwoBlockClosure

-- @@ L7287-7287 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase

-- @@ L7288-7288 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow

-- @@ L7289-7289 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseMinorRoots

-- @@ L7290-7290 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily

-- @@ L7291-7291 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry

-- @@ L7292-7292 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

-- @@ L7293-7293 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

-- @@ L7294-7294 verbatim
open MetricCodes.Spherical.HigherHierarchy

-- @@ L7295-7295 verbatim
open MetricCodes.Spherical.HigherProjectionInstantiation

-- @@ L7296-7296 verbatim
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

-- @@ L7297-7297 verbatim
open MetricCodes.Spherical.HigherYoungActualGraphAssembly

-- @@ L7298-7298 verbatim
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation

-- @@ L7299-7299 verbatim
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion

-- @@ L7300-7300 verbatim
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

-- @@ L7301-7301 verbatim
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

-- @@ L7302-7302 verbatim
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower


-- @@ L7304-7357 verbatim
theorem isometricSector_operator_column_of_mem_axis_sector
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ H]
    (A B : V →ₗᵢ[ℝ] H) (T : Module.End ℝ H) (d : ℝ)
    (horth : A.toLinearMap.adjoint.comp B.toLinearMap = 0)
    (hdiag : B.toLinearMap.adjoint.comp
      (T.comp B.toLinearMap) = d • LinearMap.id)
    (hclosed : ∀ p : V,
      T (B p) ∈ LinearMap.range A.toLinearMap ⊔
        LinearMap.range B.toLinearMap) :
    T.comp B.toLinearMap = d • B.toLinearMap +
      A.toLinearMap.comp
        (A.toLinearMap.adjoint.comp (T.comp B.toLinearMap)) := by
  have hAB (p : V) : A.toLinearMap.adjoint (B p) = 0 :=
    LinearMap.congr_fun horth p
  have hBA (p : V) : B.toLinearMap.adjoint (A p) = 0 := by
    have hreverse := congrArg LinearMap.adjoint horth
    simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
      map_zero] at hreverse
    exact LinearMap.congr_fun hreverse p
  apply LinearMap.ext
  intro p
  obtain ⟨u, ⟨x, rfl⟩, v, ⟨y, rfl⟩, heq⟩ :=
    Submodule.mem_sup.mp (hclosed p)
  have hx : x = A.toLinearMap.adjoint (T (B p)) := by
    have h := congrArg A.toLinearMap.adjoint heq
    change A.toLinearMap.adjoint (A x + B y) =
      A.toLinearMap.adjoint (T (B p)) at h
    rw [map_add, hAB, add_zero] at h
    have hself := LinearMap.congr_fun A.adjoint_comp_self' x
    change A.toLinearMap.adjoint (A x) = x at hself
    exact hself.symm.trans h
  have hy : y = d • p := by
    have h := congrArg B.toLinearMap.adjoint heq
    change B.toLinearMap.adjoint (A x + B y) =
      B.toLinearMap.adjoint (T (B p)) at h
    rw [map_add, hBA, zero_add] at h
    have hself := LinearMap.congr_fun B.adjoint_comp_self' y
    change B.toLinearMap.adjoint (B y) = y at hself
    rw [hself] at h
    have hdiagonal := LinearMap.congr_fun hdiag p
    change B.toLinearMap.adjoint (T (B p)) = d • p at hdiagonal
    exact h.trans hdiagonal
  change T (B p) = d • B p +
    A (A.toLinearMap.adjoint (T (B p)))
  calc
    T (B p) = A x + B y := heq.symm
    _ = A (A.toLinearMap.adjoint (T (B p))) + B (d • p) := by
      rw [hx, hy]
    _ = d • B p + A (A.toLinearMap.adjoint (T (B p))) := by
      rw [map_smul]
      module


-- @@ L7359-7420 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_negativeValidNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false))) = 0 := by
  let kappa := gtSelectedPrefixWeight mu
  let hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu :=
    positiveGelfandTsetlinFischerGram (by omega) lam (raiseWeight mu row) hnu
  let hkappa : FiniteInterlacing n mu kappa :=
    gtSelectedPrefixWeight_finiteInterlacing mu (by omega)
      (interlaces_antitone_stabilizer h)
  let hraise : FiniteInterlacing n (raiseWeight mu row) kappa :=
    gtSelectedPrefixWeight_finiteInterlacing_raise
      mu row (by omega) (interlaces_antitone_stabilizer h)
        (interlaces_antitone_stabilizer hnu)
  let A := canonicalGelfandTsetlinAxisIsometry lam mu h hgram
  let B := normalizedGTTransverseNegativeSector
    lam mu kappa row hnu hnuGram hkappa hraise
  let T := gtRelativeCasimir (n := n + 1) lam
  let node := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
    (stabilizerShift (n + 1) mu) (.inr (row, false))
  have horth : A.toLinearMap.adjoint.comp B.toLinearMap = 0 := by
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    exact normalizedNegativeSector_canonicalAxis_inner_eq_zero
      lam mu kappa h hgram row hnu hnuGram hkappa hraise y x
  have hdiag : B.toLinearMap.adjoint.comp (T.comp B.toLinearMap) =
      node • LinearMap.id :=
    normalizedGTTransverseNegativeSector_relativeCasimir_adjoint_compression
      lam mu kappa row hnu hnuGram hkappa hraise
  have hclosed (x : HarmonicYoungSpace (n := n) mu) :
      T (B x) ∈ LinearMap.range A.toLinearMap ⊔
        LinearMap.range B.toLinearMap :=
    gtTransverseNegativeSector_relativeCasimir_mem_axis_sup_sector
      lam mu kappa row h hgram hnu hnuGram hkappa hraise hn x
  let K := A.toLinearMap.adjoint.comp (T.comp B.toLinearMap)
  have hcolumn : T.comp B.toLinearMap = node • B.toLinearMap +
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp K :=
    isometricSector_operator_column_of_mem_axis_sector
      A B T node horth hdiag hclosed
  exact gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
    lam mu h hgram hfinite hn B node K
    (fun x y => normalizedNegativeSector_canonicalAxis_inner_eq_zero
      lam mu kappa h hgram row hnu hnuGram hkappa hraise x y)
    hcolumn
    (fun x => normalizedGTTransverseNegativeSector_characteristic_aeval_eq_zero
      hn lam mu kappa row hnu hnuGram hkappa hraise x)
    (negativeStabilizerNode_ne_signedAmbientNode_of_valid_raise
      lam mu hfinite row hnu)
    p q


-- @@ L7422-7475 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_positiveValidNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, true))) = 0 := by
  let hnuGram : PositiveGelfandTsetlinFischerGram (n := n) lam nu hnu :=
    positiveGelfandTsetlinFischerGram (by omega) lam nu hnu
  let A := canonicalGelfandTsetlinAxisIsometry lam mu h hgram
  let B := normalizedGTTransversePositiveSector
    lam mu nu row hmunu h hnu hnuGram
  let T := gtRelativeCasimir (n := n + 1) lam
  let node := gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
    (stabilizerShift (n + 1) mu) (.inr (row, true))
  have horth : A.toLinearMap.adjoint.comp B.toLinearMap = 0 := by
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, inner_zero_right]
    rw [LinearMap.adjoint_inner_right]
    exact normalizedPositiveSector_canonicalAxis_inner_eq_zero
      lam mu nu row hmunu h hgram hnu hnuGram y x
  have hdiag : B.toLinearMap.adjoint.comp (T.comp B.toLinearMap) =
      node • LinearMap.id :=
    normalizedGTTransversePositiveSector_relativeCasimir_adjoint_compression
      lam mu nu row hmunu h hnu hnuGram
  have hclosed (x : HarmonicYoungSpace (n := n) mu) :
      T (B x) ∈ LinearMap.range A.toLinearMap ⊔
        LinearMap.range B.toLinearMap :=
    gtTransversePositiveSector_relativeCasimir_mem_axis_sup_sector
      lam mu nu row hmunu h hgram hnu hnuGram hn x
  let K := A.toLinearMap.adjoint.comp (T.comp B.toLinearMap)
  have hcolumn : T.comp B.toLinearMap = node • B.toLinearMap +
      (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp K :=
    isometricSector_operator_column_of_mem_axis_sector
      A B T node horth hdiag hclosed
  exact gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
    lam mu h hgram hfinite hn B node K
    (fun x y => normalizedPositiveSector_canonicalAxis_inner_eq_zero
      lam mu nu row hmunu h hgram hnu hnuGram x y)
    hcolumn
    (fun x => normalizedGTTransversePositiveSector_characteristic_aeval_eq_zero
      hn lam mu nu row hmunu h hnu hnuGram x)
    (positiveStabilizerNode_ne_signedAmbientNode_of_valid_lower
      lam mu nu hfinite row hmunu hnu)
    p q


-- @@ L7477-7502 verbatim
theorem gtAxisCompressedCharacteristicMinor_eval_wallNode_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p q : HarmonicYoungSpace (n := n) mu) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval
      (-(wallShift (n + 1) (r + 1))) = 0 := by
  by_cases hlast : lam (Fin.last (r + 1)) = 0
  · exact gtAxisCompressedCharacteristicMinor_eval_neg_wallShift_eq_zero_of_last_eq_zero
      lam mu h hgram hfinite hlast p q
  · have hpos : 0 < lam (Fin.last (r + 1)) := Nat.pos_of_ne_zero hlast
    let hw : 2 * (r + 1) + 5 ≤ n + 1 := by omega
    let B := normalizedGTTransverseWallSector lam mu h hw hpos
    let K := gtTransverseAxisCrossBlock lam mu h hgram B.toLinearMap
    exact gtAxisCompressedCharacteristicMinor_eval_actualPhysicalNode_eq_zero
      lam mu h hgram hfinite hn B (-(wallShift (n + 1) (r + 1))) K
      (fun x y => canonicalAxis_inner_normalizedGTTransverseWallSector_eq_zero
        lam mu h hw hpos hgram x y)
      (gtRelativeCasimir_normalizedWallSector_additiveColumn
        lam mu h hgram hn hpos)
      (fun x => normalizedGTTransverseWallSector_characteristic_aeval_eq_zero
        lam mu h hw hn hpos x)
      (presentWall_ne_signedAmbientNode hfinite hpos)
      p q


-- @@ L7504-7525 verbatim
theorem gtAxisCompressedCharacteristicMinor_eq_channelNumerator
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu) := by
  apply gtAxisCompressedCharacteristicMinor_eq_channelNumerator_of_validRoots
    lam mu h hgram hfinite hn p q
  · exact gtAxisCompressedCharacteristicMinor_eval_wallNode_eq_zero
      lam mu h hgram hfinite hn p q
  · intro row hnu
    exact gtAxisCompressedCharacteristicMinor_eval_negativeValidNode_eq_zero
      lam mu h hgram hfinite hn row hnu p q
  · intro row hpos hnu
    exact gtAxisCompressedCharacteristicMinor_eval_positiveValidNode_eq_zero
      lam mu (loweredInternalYoungWeight mu row) h hgram hfinite hn row
      (raiseWeight_loweredInternalYoungWeight mu row hpos).symm hnu p q


-- @@ L7527-7537 verbatim
theorem fixedLevelHierarchyCodeBound : FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_actualCharacteristicMinor
  intro r m n a b _ _ hn hstable low p q
  exact gtAxisCompressedCharacteristicMinor_eq_channelNumerator
    (boxSignature (m := m) a (n + 1) low)
    (Weyl.flooredWeight b (n + 1))
    (boxSignature_interlaces a b hstable low)
    (canonicalBoxPositiveFischerGram a b hstable low)
    (hstable
      ((Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)).symm low))
    hn p q


-- @@ L7539-7539 verbatim
end AllRankGTUnconditionalCharacteristicMinor


-- @@ L7541-7541 verbatim
end


-- @@ L7543-7543 verbatim
end HigherHarmonicYoung


-- @@ L7545-7545 verbatim
section


-- @@ L7547-7547 verbatim
open Filter Topology

-- @@ L7548-7548 verbatim
open scoped Topology


-- @@ L7550-7550 verbatim
namespace HigherHierarchy


-- @@ L7552-7552 verbatim
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor


-- @@ L7554-7561 verbatim
theorem main_general {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ {r : ℕ} {R : ℝ}
      (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → s < 2 * Gamma a b → Phi a b < R →
        ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
          (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))) ∧
      sphericalCodeRate s ≤ closedHierarchyVariationalRate s :=
  main_general_of_actualCodeBound fixedLevelHierarchyCodeBound hs hs'


-- @@ L7563-7572 verbatim
theorem strict_hierarchy {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s :=
  strict_hierarchy_of_actualCodeBound fixedLevelHierarchyCodeBound hs hs'


-- @@ L7574-7574 verbatim
end HigherHierarchy


-- @@ L7576-7576 verbatim
end


-- @@ L7578-7578 verbatim
end Spherical


-- @@ L7580-7580 verbatim
end MetricCodes


-- @@ L7582-7582 verbatim
section


-- @@ L7584-7584 verbatim
open Filter Topology

-- @@ L7585-7585 verbatim
open scoped Topology


-- @@ L7587-7587 verbatim
namespace SpherePacking


-- @@ L7589-7591 verbatim
/-- The kissing number used in the spherical-code argument. -/
def kissingNumber (n : ℕ) : ℕ∞ :=
  sphericalCodeNumber n ((1 : ℝ) / 2)


-- @@ L7593-7593 verbatim
end SpherePacking


-- @@ L7595-7595 verbatim
namespace MetricCodes.Johnson


-- @@ L7597-7602 verbatim
theorem main_binary_theorem {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    MetricCodes.Hamming.binaryRate δ ≤ combinedVariationalRate δ ∧
      combinedVariationalRate δ < mrrwRate δ :=
  ⟨binaryRate_le_combinedVariationalRate hδ hhalf,
    MetricCodes.MRRW.strict_mrrw2 hδ hhalf⟩


-- @@ L7604-7604 verbatim
end MetricCodes.Johnson


-- @@ L7606-7606 verbatim
namespace MetricCodes.Spherical.HigherHierarchy.NumericalMaximum


-- @@ L7608-7630 verbatim
theorem eventually_kissingNumber_lt_published :
    ∀ᶠ n : ℕ in atTop,
      ((SpherePacking.kissingNumber n).toNat : ℝ) ≤
        (2 : ℝ) ^ ((0.39661 : ℝ) * (n : ℝ)) := by
  have hcode :=
    (MetricCodes.Spherical.HigherHierarchy.main_general
      (s := (1 : ℝ) / 2) (by norm_num) (by norm_num)).1
      (R := (0.39661 : ℝ))
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissingAmbient
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissingStabilizer
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_interlacing
      (by linarith [MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_spectral_certificate])
      (by linarith [MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_entropy_certificate])
  filter_upwards [hcode] with n hn
  obtain ⟨C, hC⟩ :=
    SpherePacking.exists_maximal_sphericalCode (n := n) (s := (1 : ℝ) / 2)
      (by norm_num)
  have hcard : (SpherePacking.kissingNumber n).toNat = C.points.card := by
    change (SpherePacking.sphericalCodeNumber n ((1 : ℝ) / 2)).toNat = _
    rw [← hC]
    exact ENat.toNat_natCast _
  rw [hcard]
  exact (hn C).le


-- @@ L7632-7632 verbatim
end MetricCodes.Spherical.HigherHierarchy.NumericalMaximum


-- @@ L7634-7634 verbatim
end


-- @@ L7636-7636 verbatim
end MetricCodesNoncomputable
