/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyParity
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyReconstruction


-- @@ L12-12 verbatim
/-! Pointwise parity and canonical normalization of the assembled actual pressure. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerGraphPressurePotential


-- @@ L21-21 verbatim
open EulerLiftedGradientSpace


-- @@ L23-26 verbatim
/-- The physical phase graph respects joint spatial and angular reflection. -/
theorem cylinderGraph_neg (period k : ℝ) (m x : Vector3) :
    cylinderGraph period k m (-x) = -cylinderGraph period k m x := by
  simp [cylinderGraph]


-- @@ L28-28 verbatim
end EulerGraphPressurePotential


-- @@ L30-30 verbatim
namespace EulerCanonicalGraphPotential


-- @@ L32-32 verbatim
open EulerLiftedGradientSpace


-- @@ L34-39 verbatim
/-- The canonical radial scalar potential of an odd vector field is even.
This identity does not need a choice of additive gauge or a potential-existence assumption. -/
theorem radialPotential_even (V : Vector3 → Vector3)
    (hV : ∀ x, V (-x) = -V x) (x : Vector3) :
    radialPotential V (-x) = radialPotential V x := by
  simp only [radialPotential, smul_neg, hV, inner_neg_neg]


-- @@ L41-41 verbatim
end EulerCanonicalGraphPotential


-- @@ L43-43 verbatim
namespace EulerCorrectionAssembly


-- @@ L45-46 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerAllOrderCorrectionData
  EulerGraphPressurePotential EulerCanonicalGraphPotential

-- @@ L47-47 verbatim
open scoped ContDiff


-- @@ L49-49 verbatim
variable (period : ℝ) [Fact (0 < period)]

-- @@ L50-50 verbatim
variable {T : ℝ} {hT : 0 < T} {A : Data period T}


-- @@ L52-61 verbatim
/-- The canonical pressure representative is pointwise odd, as a consequence
of genuine PDE uniqueness and parity of the prescribed data. -/
theorem FiniteFamily.pointPressure_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A)
    (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    F.pointPressure period t (-x) = -F.pointPressure period t x :=
  continuous_representative_odd period (F.commonPressure period t)
    (F.pointPressure period t) (F.commonPressure_odd period C P t)
    (Continuous.uncurry_left t (F.pointPressure_joint_continuous period))
    (F.pointPressure_ae period t) x


-- @@ L63-69 verbatim
/-- The actual signed pressure-gradient vector on the physical phase graph is odd. -/
theorem FiniteFamily.graphPressure_odd (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A) (k : ℝ)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    F.graphPressure period k t (-x) = -F.graphPressure period k t x := by
  unfold FiniteFamily.graphPressure
  rw [cylinderGraph_neg, F.pointPressure_odd period C P, smul_neg]


-- @@ L71-78 verbatim
/-- The origin-normalized scalar pressure is even at every time.
In particular parity is an exact identity, not merely equality modulo a constant. -/
theorem FiniteFamily.normalizedGraphPotential_even (F : FiniteFamily period hT A)
    (C : ComparisonData period hT A) (P : ParityData period A) (k : ℝ)
    (t : Icc (0 : ℝ) T) (x : Vector3) :
    F.normalizedGraphPotential period k t (-x) =
      F.normalizedGraphPotential period k t x :=
  radialPotential_even _ (F.graphPressure_odd period C P k t) x


-- @@ L80-88 verbatim
/-- Any smooth potential of the same graph field agrees with the canonical
radial potential after subtracting its value at the origin. -/
theorem FiniteFamily.normalizedGraphPotential_eq_sub (F : FiniteFamily period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (q : Vector3 → ℝ)
    (hq : ContDiff ℝ ∞ q)
    (hgrad : ∀ x, gradient q x = F.graphPressure period k t x) (x : Vector3) :
    F.normalizedGraphPotential period k t x = q x - q 0 :=
  radialPotential_eq_sub _
    (Continuous.uncurry_left t (F.graphPressure_joint_continuous period k)) q hq hgrad x


-- @@ L90-98 verbatim
/-- The constructed scalar pressure is the unique smooth potential of its
graph field with the prescribed zero value at the origin. -/
theorem FiniteFamily.normalizedGraphPotential_unique (F : FiniteFamily period hT A)
    (k : ℝ) (t : Icc (0 : ℝ) T) (q : Vector3 → ℝ)
    (hq : ContDiff ℝ ∞ q)
    (hgrad : ∀ x, gradient q x = F.graphPressure period k t x) (hq0 : q 0 = 0) :
    F.normalizedGraphPotential period k t = q := by
  funext x
  rw [F.normalizedGraphPotential_eq_sub period k t q hq hgrad x, hq0, sub_zero]


-- @@ L100-100 verbatim
end EulerCorrectionAssembly
