import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Detector.Row
import OAI.NumberTheory.DirichletL.Detector.Compensation


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped BigOperators Classical

-- @@ L10-10 verbatim
open MeasureTheory

-- @@ L11-11 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L12-12 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve

-- @@ L13-13 verbatim
open CubicEisenstein ProbeCompleted ProbeRow


-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L17-21 verbatim
structure CalibrationData where
  excluded : Finset (Ideal O)
  generator : O
  generator_ne_zero : generator ≠ 0
  residue : MulChar (O ⧸ Ideal.span {generator}) ℂ


-- @@ L23-23 verbatim
def elementNorm (a : O) : ℝ := Ideal.absNorm (Ideal.span {a})


-- @@ L25-26 verbatim
def CalibrationData.residueMonoid (C : CalibrationData) : O →* ℂ :=
  C.residue.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {C.generator})).toMonoidHom


-- @@ L28-29 verbatim
def CalibrationData.Xi (C : CalibrationData) : O →* ℂ :=
  C.residueMonoid * (idealRowHom C.generator).toMonoidHom.comp principalIdealHom.toMonoidHom


-- @@ L31-34 verbatim
def CalibrationData.tau (C : CalibrationData) : ℂ :=
  (∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    quotientTrace C.generator C.generator_ne_zero d) /
      (Real.sqrt (elementNorm C.generator) : ℂ)


-- @@ L36-39 verbatim
def sexticGauss (s : O) (hs : s ≠ 0) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s},
    idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s}) *
      quotientTrace s hs (Ideal.Quotient.mk _ h * d)


-- @@ L41-47 verbatim
theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _


-- @@ L49-50 verbatim
def verticalIntegral (σ : ℝ) (F : ℂ → ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, F ((σ : ℂ) + y * Complex.I)


-- @@ L52-67 verbatim
def markedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p ∈ C.excluded, ¬p ∣ s.val then
      let a := primaryGenerator s.val
      let ha := supported_primaryGenerator_ne_zero s.val s.property
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s / Y) * idealRowHom C.generator s.val /
        (C.tau * C.residueMonoid a * (Real.sqrt (elementNorm C.generator * q_s * X) : ℂ)) *
      ∑' m : O,
        C.residueMonoid m * (Real.sqrt q_s : ℂ)⁻¹ * sexticGauss a ha (-m) *
          W₀ (elementNorm m / (elementNorm C.generator * q_s * X)) *
          verticalIntegral 4 (fun t => (Z : ℂ) ^ t * Complex.exp (t ^ 2) *
            spectralRow C.excluded D (rowCoefficient η C.Xi a has m) t)
    else 0


-- @@ L69-71 verbatim
def physicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  markedPhysicalProbe η C 1 W₀ W₁ X Y Z


-- @@ L73-73 verbatim
def slotProduct {K : ℕ} (p : Fin K → O) (J : Finset (Fin K)) : O := ∏ i ∈ J, p i


-- @@ L75-78 verbatim
def compensatedTuple {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin K → O) (X Y Z : ℝ) : ℂ :=
  ProbeCompensation.tupleOperation p elementNorm (HeckeFamily.elementCoeff η)
    (fun a => markedPhysicalProbe η C (Ideal.span {a}) W₀ W₁) X Y Z


-- @@ L80-81 verbatim
@[simp] theorem elementNorm_one : elementNorm (1 : O) = 1 := by
  simp [elementNorm]


-- @@ L83-83 verbatim
attribute [local irreducible] markedPhysicalProbe


-- @@ L85-93 verbatim
theorem compensatedTuple_zero (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin 0 → O) (X Y Z : ℝ) :
    compensatedTuple η C W₀ W₁ p X Y Z = physicalProbe η C W₀ W₁ X Y Z := by
  unfold compensatedTuple
  rw [ProbeCompensation.tupleOperation_zero p elementNorm (HeckeFamily.elementCoeff η)
    elementNorm_one (HeckeFamily.elementCoeff_one η)]
  change markedPhysicalProbe η C (Ideal.span {(1 : O)}) W₀ W₁ X Y Z =
    markedPhysicalProbe η C 1 W₀ W₁ X Y Z
  rw [Ideal.span_singleton_one, Ideal.one_eq_top]


-- @@ L95-106 verbatim
theorem compensatedTuple_one (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (p : Fin 1 → O) (X Y Z : ℝ) :
    compensatedTuple η C W₀ W₁ p X Y Z =
      star (HeckeFamily.elementCoeff η (p 0)) *
        markedPhysicalProbe η C (Ideal.span {p 0}) W₀ W₁ X Y (Z * elementNorm (p 0)) -
      (elementNorm (p 0) ^ (-(3 / 2 : ℝ)) : ℝ) *
        physicalProbe η C W₀ W₁ (X / elementNorm (p 0)) (Y / elementNorm (p 0)) Z := by
  unfold compensatedTuple
  rw [ProbeCompensation.tupleOperation_one p elementNorm (HeckeFamily.elementCoeff η)
    elementNorm_one (HeckeFamily.elementCoeff_one η)]
  change _ = _ - _ * markedPhysicalProbe η C 1 W₀ W₁ _ _ Z
  rw [Ideal.span_singleton_one, Ideal.one_eq_top]


-- @@ L108-113 verbatim
def compensatedPhysicalProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (slotPrimes : Fin K → Finset O)
    (slotWindow : Fin K → ℝ → ℂ) (slotScale : Fin K → ℝ) (X Y Z : ℝ) : ℂ :=
  ∑ p : ((i : Fin K) → {a : O // a ∈ slotPrimes i}),
    (∏ i : Fin K, slotWindow i (elementNorm (p i).val / slotScale i)) *
      compensatedTuple η C W₀ W₁ (fun i => (p i).val) X Y Z


-- @@ L115-115 verbatim
end SevenEighths.ProbePhysical

-- @@ L116-116 verbatim
end


-- @@ L118-118 verbatim
end OAI
