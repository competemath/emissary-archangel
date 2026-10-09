import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory Filter

-- @@ L7-7 verbatim
open scoped BigOperators Topology

-- @@ L8-8 verbatim
universe u


-- @@ L10-10 verbatim
namespace SubpolynomialLp


-- @@ L12-13 verbatim
def coordinateDistance (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ a, |x a - y a| ^ p) ^ (1 / p)


-- @@ L15-22 verbatim
/-- The universal property used in the definition of d_p(n,D). -/
def GoodDimension (p : ℝ) (n : ℕ) (D : ℝ) (d : ℕ) : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
    (x : Fin n → @Lp Ω ℝ mΩ _ (ENNReal.ofReal p) μ),
    Function.Injective x →
    ∃ (y : Fin n → Fin d → ℝ) (s : ℝ), 0 < s ∧
      ∀ i j, s * ‖x i - x j‖ ≤ coordinateDistance p (y i) (y j) ∧
        coordinateDistance p (y i) (y j) ≤ D * s * ‖x i - x j‖


-- @@ L24-27 verbatim
/-- The least universal coordinate dimension. The theorem also asserts that
this least dimension has the defining property, ruling out an empty infimum. -/
def dimension (p : ℝ) (n : ℕ) (D : ℝ) : ℕ :=
  sInf {d : ℕ | GoodDimension.{u} p n D d}


-- @@ L29-29 verbatim
def gamma (p : ℝ) : ℝ := if p < 2 then 2 - p else 1 - 2 / p


-- @@ L31-31 verbatim
end SubpolynomialLp


-- @@ L33-33 verbatim
end


-- @@ L35-35 verbatim
end OAI
