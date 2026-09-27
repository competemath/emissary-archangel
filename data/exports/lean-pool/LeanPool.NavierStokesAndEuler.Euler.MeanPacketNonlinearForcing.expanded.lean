/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2CoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcingAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothCoefficientProduct
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothCoefficientContinuity


-- @@ L14-21 verbatim
/-!
# Nonlinear closure of actual admissible mean forcing

Sobolev evaluation supplies bounded coefficients from one actual smooth L²
factor. Consequently finite-dimensional bilinear products preserve the
literal spatial L² jets and their time continuity without an extra product
regularity assumption.
-/


-- @@ L23-23 verbatim
section


-- @@ L25-25 verbatim
/-! Actual multiplication closure for admissible mean forcing. -/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace EulerMeanPacketProvider.Forcing


-- @@ L33-34 verbatim
open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketProfileRecursion
  EulerLpSmoothCoefficientProduct


-- @@ L36-36 verbatim
variable {D : Data} {raw : VectorField}


-- @@ L38-46 verbatim
/-- Multiplying the raw field by a genuinely bounded smooth coefficient path
preserves all actual L² spatial jets and their time continuity. -/
def multiply (G : Forcing D raw) (A : SmoothCoefficientPath (Icc (0 : ℝ) D.T) (Space →L[ℝ] Space)) :
    Forcing D (fun z => A.field (D.clamp z.1) z.2.1 (raw z)) :=
  ofSlices (fun r => product A (D.clamp r) (G.slices r))
    (fun n => by
      simpa only [Data.clamp_coe] using continuous_product_jet A
        (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous n)
    (fun t x θ => by rw [G.raw_eq t x θ]; rfl)


-- @@ L48-48 verbatim
end EulerMeanPacketProvider.Forcing


-- @@ L50-50 verbatim
end

-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
@[expose] public section


-- @@ L57-57 verbatim
noncomputable section


-- @@ L59-59 verbatim
namespace EulerMeanPacketProvider


-- @@ L61-62 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerMeanSobolevBoundedField EulerPacketPointJets EulerPacketProfileRecursion


-- @@ L64-64 verbatim
namespace Forcing


-- @@ L66-66 verbatim
variable {D : Data} {raw raw' : VectorField}


-- @@ L68-75 verbatim
/-- Admissibility depends only on the raw field on the actual time interval. -/
def congr (G : Forcing D raw)
    (heq : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw' (t, (x, θ)) = raw (t, (x, θ))) : Forcing D raw' where
  slices := G.slices
  jets_continuous := G.jets_continuous
  path := G.path
  path_eq := G.path_eq
  raw_eq t x θ := (heq t x θ).trans (G.raw_eq t x θ)


-- @@ L77-85 verbatim
/-- A literal bilinear product of two admissible fields is admissible. -/
def bilinear (G : Forcing D raw) (H : Forcing D raw')
    (B : Space →L[ℝ] Space →L[ℝ] Space) : Forcing D (fun z => B (raw z) (raw' z)) := by
  let A := SmoothCoefficientPath.map B
    (coefficientPath (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous)
  apply (H.multiply A).congr
  intro t x θ
  simp only [A, Data.clamp_coe, SmoothCoefficientPath.map_apply, coefficientPath_apply,
    G.raw_eq t x θ]


-- @@ L87-87 verbatim
end Forcing


-- @@ L89-93 verbatim
theorem admissible_bilinear (D : Data) (raw raw' : VectorField)
    (h : Nonempty (Forcing D raw)) (h' : Nonempty (Forcing D raw'))
    (B : Space →L[ℝ] Space →L[ℝ] Space) :
    Nonempty (Forcing D (fun z => B (raw z) (raw' z))) :=
  ⟨(Classical.choice h).bilinear (Classical.choice h') B⟩


-- @@ L95-95 verbatim
end EulerMeanPacketProvider
