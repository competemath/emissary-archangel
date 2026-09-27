/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldProducts
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarPrimitive
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath


-- @@ L13-13 verbatim
/-! Actual raw slow and normal-weighted angular advection on cylinder-path witnesses. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCylinderField


-- @@ L22-26 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
    EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerCylinderPathProduct
  EulerCylinderScalarPrimitive EulerMeanCoefficients EulerMetricTransport
  EulerLiftedWeakDerivative EulerCylinderSobolev EulerPacketProfileRecursion

-- @@ L27-27 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L29-32 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCylinderFieldAdvection1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L33-36 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCylinderFieldAdvection2 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L37-40 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCylinderFieldAdvection3 : NormedAddCommGroup (Space →ᵇ Space) :=
    inferInstance

-- @@ L41-42 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space)` instance to shorten typeclass synthesis. -/
local instance instPacketCylinderFieldAdvection4 : NormedSpace ℝ (Space →ᵇ Space) := inferInstance

-- @@ L43-46 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCylinderFieldAdvection5 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)
    := inferInstance

-- @@ L47-50 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCylinderFieldAdvection6 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance


-- @@ L52-55 verbatim
/-- Embed the actual normal component into a fixed unit vector. -/
def normalComponentMap : Space →L[ℝ] Space →L[ℝ] Space :=
  ((ContinuousLinearMap.compL ℝ Space ℝ Space) scalarEmbed).comp
    (toDual ℝ Space).toContinuousLinearMap


-- @@ L57-58 verbatim
@[simp] theorem normalComponentMap_apply (m v : Space) :
    normalComponentMap m v = scalarEmbed (inner ℝ m v) := rfl


-- @@ L60-62 verbatim
theorem normalComponentMap_project (m v : Space) :
    scalarProject (normalComponentMap m v) = inner ℝ m v := by
  rw [normalComponentMap_apply,project_embed]


-- @@ L64-64 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L66-68 verbatim
/-- Normal component path, given by `mapCoefficientPath normalComponentMap N`. -/
def normalComponentPath (N : C(K, Space →ᵇ Space)) : C(K,Space →ᵇ Space →L[ℝ] Space) :=
  mapCoefficientPath normalComponentMap N


-- @@ L70-82 verbatim
theorem normalComponentPath_orbit (N : C(K, Space →ᵇ Space))
    (hN : ContDiff ℝ ∞ (translateCoefficientPath N)) :
    ContDiff ℝ ∞ (translateCoefficientPath (normalComponentPath N)) := by
  have he : translateCoefficientPath (normalComponentPath N) =
      (mapCoefficientPath normalComponentMap) ∘ translateCoefficientPath N := by
    funext a
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  rw [he]
  exact (mapCoefficientPath (K := K) normalComponentMap).contDiff.comp hN


-- @@ L84-84 verbatim
namespace Field


-- @@ L86-86 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}


-- @@ L88-95 verbatim
/-- Spatial transport expressed directly in the full raw covering derivative. -/
def spatialTransport (G : Field P T raw) (H : Field P T raw') :
    Field P T (fun z => fderiv ℝ (fun y => raw' (z.1,y)) z.2 (raw z,0)) where
  path := advectionPath P G.path H.path G.orbit H.orbit
  orbit := advectionPath_orbit P G.path H.path G.orbit H.orbit
  raw_eq t x θ := by
    rw [H.raw_fderiv,G.raw_eq]
    exact (pointField_advectionPath P G.path H.path G.orbit H.orbit t (x,(θ : AddCircle P))).symm


-- @@ L97-109 verbatim
/-- The normal factor is a real coefficient operation; no L² integrability of the normal itself is
needed. -/
def angularTransport (G : Field P T raw) (H : Field P T raw')
    (N : C(Icc (0 : ℝ) T, Space →ᵇ Space))
    (hN : ContDiff ℝ ∞ (translateCoefficientPath N)) (m : VectorField)
    (hm : ∀ (t : Icc (0 : ℝ) T) x θ, m (t, (x, θ)) = N t x) :
    Field P T (fun z => inner ℝ (m z) (raw z) •
      fderiv ℝ (fun y => raw' (z.1,y)) z.2 (0,1)) := by
  let NG := G.multiply (normalComponentPath N) (normalComponentPath_orbit N hN)
    (fun z => normalComponentMap (m z)) (fun t x θ => by rw [hm]; rfl)
  let Q := NG.scalarProduct (H.derivative 0) scalarProject (le_of_eq scalarProject_norm)
  exact Q.congr (fun t x θ => by
    simp only [normalComponentMap_project, standardDirection_zero])


-- @@ L111-111 verbatim
end Field

-- @@ L112-112 verbatim
end EulerPacketCylinderField
