/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamelFinish
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyBalls
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP8
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.SingletonNull


-- @@ L17-21 verbatim
/-!
# Pointwise Potential

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
open scoped BigOperators ENNReal NNReal Topology


-- @@ L27-27 verbatim
open MeasureTheory MeasureTheory.Measure Set Metric


-- @@ L29-29 verbatim
open CKN.Foundation.Heat CKN.Foundation.Parabolic

-- @@ L30-30 verbatim
open CKN.Foundation.Parabolic.Morrey

-- @@ L31-31 verbatim
open CKN.Core.HeatPotential

-- @@ L32-32 verbatim
open CKN.Core.Step3



-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
namespace CKN.Core.Step4


-- @@ L39-42 verbatim
lemma heatPotentialKernel_abs_le_riesz₂ (z w : ParabolicPoint) :
    |heatPotentialKernel z w| ≤
      1000 * (parabolicRieszKernel 2 z w).toReal := by
  exact _root_.CKN.Core.HeatPotential.heatPotentialKernel_abs_le_riesz₂ z w


-- @@ L44-48 verbatim
lemma heatPotentialSpatialKernel_abs_le_riesz₁ (i : Fin 3)
    (z w : ParabolicPoint) :
    |heatPotentialSpatialKernel i z w| ≤
      300000 * (parabolicRieszKernel 1 z w).toReal := by
  exact _root_.CKN.Core.HeatPotential.heatPotentialSpatialKernel_abs_le_riesz₁ i z w


-- @@ L50-57 verbatim
/-- Riesz-potential majorant for the localized scalar and divergence heat sources. -/
def pointwisePotentialMajorant (g : ParabolicPoint → Vec3)
    (h : Fin 3 → ParabolicPoint → Vec3) : ParabolicPoint → ℝ :=
  fun z =>
    3000 * (parabolicRieszPotential 2
      (fun w => vec3EuclideanNorm (g w)) z).toReal +
    900000 * ∑ j, (parabolicRieszPotential 1
      (fun w => vec3EuclideanNorm (h j w)) z).toReal


















-- @@ L75-83 verbatim
theorem forceLqDataOnBox
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J) :
    CKN.localVecLp (CKN.spaceTimeSet Ω' J) q f := by
  exact hsol.2.2.2.2.1 Ω' J hbox


-- @@ L85-85 verbatim
end CKN.Core.Step4
