import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open MeasureTheory


-- @@ L9-9 verbatim
namespace Problem160


-- @@ L11-11 verbatim
abbrev Plane := EuclideanSpace ℝ (Fin 2)


-- @@ L13-14 verbatim
def circleDir (t : ℝ) : Plane :=
  WithLp.toLp 2 ![Real.cos t, Real.sin t]


-- @@ L16-18 verbatim
def normalizedAngleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ •
    Measure.restrict volume (Set.Ico 0 (2 * Real.pi))


-- @@ L20-21 verbatim
def circleMeasure : Measure Plane :=
  Measure.map circleDir normalizedAngleMeasure


-- @@ L23-24 verbatim
def weakPairMeasure (R : ℝ) : Measure (Plane × Plane) :=
  (Measure.restrict volume (Metric.ball (0 : Plane) R)).prod circleMeasure


-- @@ L26-28 verbatim
def ProperColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    ∀ x y : Plane, dist x y = 1 → c x ≠ c y


-- @@ L30-38 verbatim
def WeakMeasurableColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    AEMeasurable c volume ∧
      ∀ R : ℝ, 0 < R →
        (∑ i : Fin k,
          (weakPairMeasure R)
            {p : Plane × Plane |
              c (Prod.fst p) = i ∧
              c (Prod.fst p + Prod.snd p) = i}) = 0


-- @@ L40-41 verbatim
def planeChromaticNumber : ℕ :=
  sInf {k : ℕ | ProperColoring k}


-- @@ L43-43 verbatim
end Problem160


-- @@ L45-45 verbatim
end


-- @@ L47-47 verbatim
end OAI
