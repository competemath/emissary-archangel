/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOrbitSmoothL2Field
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider


-- @@ L12-18 verbatim
/-!
# Solved mean fields are actual admissible forcing fields

The genuine continuous L² solution path and its solved spatial translation
orbit produce the literal smooth L² slices required by the forcing interface.
The same construction applies to its actual time derivative and pressure force.
-/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerMeanPacketProvider


-- @@ L27-30 verbatim
open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanTimeContinuousTranslation
   EulerMeanScalarPressure EulerPacketPointJets
      EulerPacketProfileRecursion

-- @@ L31-31 verbatim
open scoped ContDiff


-- @@ L33-33 verbatim
namespace Forcing


-- @@ L35-35 verbatim
variable {D : Data} {raw : VectorField}


-- @@ L37-51 verbatim
/-- Actual path-orbit regularity is converted into literal spatial derivative data. -/
def ofOrbitPath (p : C(Icc (0 : ℝ) D.T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation D.T a p))
    (heq : ∀ (t : Icc (0 : ℝ) D.T) x θ,
      raw (t,(x,θ)) = representative (p t) (pathTranslation_evaluation_contDiff D.T p hp t) x) :
    Forcing D raw where
  slices t := smoothL2Field (p (D.clamp t)) (pathTranslation_evaluation_contDiff D.T p hp (D.clamp
      t))
  jets_continuous n := by
    simpa only [Data.clamp_coe] using smoothL2Field_path_jet_continuous D.T p hp n
  path := p
  path_eq t := by
    rw [Data.clamp_coe, smoothL2Field_toLp]
  raw_eq t x θ := by
    simpa only [Data.clamp_coe, smoothL2Field_field] using heq t x θ


-- @@ L53-56 verbatim
/-- The output velocity of the genuine source mean solve can be used as the next forcing input. -/
def vectorForcing (G : Forcing D raw) : Forcing D G.vector :=
  ofOrbitPath G.velocityPath G.velocityPath_orbit (fun t x θ => by
    simp only [vector, pathRepresentative, Data.clamp_coe])


-- @@ L58-61 verbatim
/-- Its true continuous time derivative has the same literal spatial admissibility. -/
def vectorDerivativeForcing (G : Forcing D raw) : Forcing D G.vectorDerivative :=
  ofOrbitPath G.derivativePath G.derivativePath_orbit (fun t x θ => by
    simp only [vectorDerivative, pathRepresentative, Data.clamp_coe])


-- @@ L63-66 verbatim
/-- Pressure force, defined pointwise by `pathRepresentative D.T G.pressureForcePath
G.pressureForcePath_orbit (D.clamp z.1) z.2.1`. -/
def pressureForce (G : Forcing D raw) : VectorField := fun z =>
  pathRepresentative D.T G.pressureForcePath G.pressureForcePath_orbit (D.clamp z.1) z.2.1


-- @@ L68-72 verbatim
/-- The physical pressure gradient, rather than the unneeded scalar pressure value, is spatially L².
-/
def pressureForceForcing (G : Forcing D raw) : Forcing D G.pressureForce :=
  ofOrbitPath G.pressureForcePath G.pressureForcePath_orbit (fun t x θ => by
    simp only [pressureForce, pathRepresentative, Data.clamp_coe])


-- @@ L74-74 verbatim
end Forcing


-- @@ L76-79 verbatim
theorem meanSolve_admissible (D : Data) (raw : VectorField) (h : Nonempty (Forcing D raw)) :
    Nonempty (Forcing D (meanSolve D raw).1) := by
  rw [meanSolve_of_admissible D raw h]
  exact ⟨(Classical.choice h).vectorForcing⟩


-- @@ L81-81 verbatim
end EulerMeanPacketProvider
