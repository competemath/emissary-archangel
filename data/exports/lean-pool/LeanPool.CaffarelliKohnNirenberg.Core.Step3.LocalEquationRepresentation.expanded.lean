/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedCampanato
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian


-- @@ L13-17 verbatim
/-!
# Local Equation Representation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open scoped BigOperators ENNReal NNReal Topology


-- @@ L23-23 verbatim
open MeasureTheory MeasureTheory.Measure Set Metric



-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace CKN.Core.Step3


-- @@ L30-30 verbatim
open CKN.Foundation.Heat CKN.Foundation.Parabolic

-- @@ L31-31 verbatim
open CKN.Core.HeatPotential


-- @@ L33-40 verbatim
/-!
# Localized equation and heat-potential representation

The cutoff-tested S3 identity is the distribution-free entry point for the
local equation.  The source terms below are the paper's displayed formulas.
The pressure representation is recorded as a structural decomposition, while
the pointwise estimate is proved directly from the explicit heat kernels.
-/


-- @@ L42-45 verbatim
/-- Velocity multiplied by the localization cutoff. -/
def localizedVelocity (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => φ z • u z


-- @@ L47-50 verbatim
/-- Convective derivative of velocity, expressed through its selected weak gradient. -/
def localizedConvection (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) : ParabolicPoint → Vec3 :=
  fun z i => ∑ j, u z j * Du z i j


-- @@ L52-60 verbatim
/-- Scalar-source part of the localized heat equation before putting convection in divergence
form. -/
def localizedEquationG (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => fun i =>
    timePartial φ z * u z i +
      spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i -
      φ z * localizedConvection u Du z i + φ z * f z i


-- @@ L62-65 verbatim
/-- Divergence-source contribution from differentiating the localization cutoff. -/
def localizedEquationH (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) : Fin 3 → ParabolicPoint → Vec3 :=
  fun i z => (-2 * spatialPartial φ i z) • u z










-- @@ L75-75 verbatim
end CKN.Core.Step3
