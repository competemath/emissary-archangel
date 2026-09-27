/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighMean
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathAdvection
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderPaths


-- @@ L14-14 verbatim
/-! Supported, zero-mean raw cylinder witnesses feed the actual high-mode solver. -/


-- @@ L16-16 verbatim
section


-- @@ L18-18 verbatim
/-! Genuine nonlinear cylinder products preserve support of their multiplying factor. -/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace EulerCylinderPathProduct


-- @@ L26-28 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpSupportedSubspace EulerMetricTransport EulerLiftedWeakDerivative

-- @@ L29-29 verbatim
open scoped ContDiff


-- @@ L31-32 verbatim
variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (S : Set Space) (hS : MeasurableSet S)


-- @@ L34-37 verbatim
/-- Retain the actual values of a continuous path that already has the stated support. -/
def supportedPath (p : C(K, LiftL2 P)) (h : ∀ t, p t ∈ Supported P Space S hS) :
    C(K,Supported P Space S hS) :=
  ⟨fun t => ⟨p t,h t⟩, p.continuous.subtype_mk h⟩


-- @@ L39-45 verbatim
omit [CompactSpace K] in
@[simp] theorem include_supportedPath (p : C(K, LiftL2 P))
    (h : ∀ t, p t ∈ Supported P Space S hS) :
    includePath P S hS (supportedPath P S hS p h) = p := by
  apply ContinuousMap.ext
  intro t
  rfl


-- @@ L47-49 verbatim
variable (p q : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))


-- @@ L51-60 verbatim
theorem scalarProductPath_supported_left (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) :
    scalarProductPath P L hL p q hp hq t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  have hzero := (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (p t)).mp (hs t)
  filter_upwards [hzero,scalarProductPath_ae P L hL p q hp hq t,pointField_ae P p hp t]
    with x hz hr hrep hx
  rw [hr, ← hrep, hz hx, map_zero, zero_smul]


-- @@ L62-71 verbatim
theorem scalarProductPath_supported_right (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (hs : ∀ t, q t ∈ Supported P Space S hS) (t : K) :
    scalarProductPath P L hL p q hp hq t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  have hzero := (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (q t)).mp (hs t)
  filter_upwards [hzero,scalarProductPath_ae P L hL p q hp hq t,pointField_ae P q hq t]
    with x hz hr hrep hx
  rw [hr, ← hrep, hz hx, smul_zero]


-- @@ L73-82 verbatim
theorem bilinearProductPath_supported_left (B : Space →L[ℝ] Space →L[ℝ] Space)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) :
    bilinearProductPath P B p q hp hq t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  have hzero := (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (p t)).mp (hs t)
  filter_upwards [hzero,bilinearProductPath_ae P B p q hp hq t,pointField_ae P p hp t]
    with x hz hr hrep hx
  rw [hr, ← hrep, hz hx, map_zero, zero_apply]


-- @@ L84-88 verbatim
theorem scalarDerivativeProductPath_supported (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (i : Fin 4) (t : K) :
    scalarDerivativeProductPath P L hL p q hp hq i t ∈ Supported P Space S hS :=
  scalarProductPath_supported_left P S hS p (derivativePath P q i) hp
    (derivativePath_orbit P q hq i) L hL hs t


-- @@ L90-99 verbatim
theorem advectionPath_supported (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) :
    advectionPath P p q hp hq t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  have hzero := (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (p t)).mp (hs t)
  filter_upwards [hzero,advectionPath_ae P p q hp hq t,pointField_ae P p hp t]
    with x hz hr hrep hx
  rw [hr, ← hrep, hz hx]
  exact map_zero _


-- @@ L101-101 verbatim
end EulerCylinderPathProduct


-- @@ L103-103 verbatim
end

-- @@ L104-104 verbatim
end


-- @@ L106-106 verbatim
end


-- @@ L108-108 verbatim
@[expose] public section


-- @@ L110-110 verbatim
noncomputable section


-- @@ L112-112 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L114-116 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderPaths
  EulerCylinderPathProduct EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerPacketProfileRecursion EulerCylinderAngleAverage


-- @@ L118-119 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]


-- @@ L121-131 verbatim
/-- Only actual support and literal mean zero are added to the existing field witness. -/
def transverseForcing (D : EulerTransversePacketProvider.Data U) {raw : VectorField}
    (G : Field P D.T raw)
    (hs : ∀ t, G.path t ∈ Supported P Space D.support D.support_measurable)
    (hm : ∀ (t : Icc (0 : ℝ) D.T) x,
      (∫ θ in (0 : ℝ)..P, raw (t, (x, θ))) = 0) :
    EulerTransversePacketProvider.Forcing P D raw where
  path := supportedPath P D.support D.support_measurable G.path hs
  path_orbit := by simpa only [include_supportedPath] using G.orbit
  raw_eq t x θ := by simpa only [include_supportedPath] using G.raw_eq t x θ
  mean_zero t := G.average_zero_of_raw_integral hm t


-- @@ L133-140 verbatim
/-- A literal compact-support proof may be used directly, without selecting a new representative. -/
def transverseForcingOfRaw (D : EulerTransversePacketProvider.Data U) {raw : VectorField}
    (G : Field P D.T raw)
    (hs : ∀ (t : Icc (0 : ℝ) D.T) x, x ∉ D.support → ∀ θ : ℝ, raw (t,(x,θ)) = 0)
    (hm : ∀ (t : Icc (0 : ℝ) D.T) x,
      (∫ θ in (0 : ℝ)..P, raw (t,(x,θ))) = 0) :
    EulerTransversePacketProvider.Forcing P D raw :=
  G.transverseForcing D (G.supported_of_raw_zero D.support D.support_measurable hs) hm


-- @@ L142-142 verbatim
end EulerPacketCylinderField.Field
