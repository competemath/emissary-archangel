/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalData
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarTime
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear


-- @@ L14-14 verbatim
/-! Actual admissible forcing restriction and the history trace used as forward initial data. -/


-- @@ L16-16 verbatim
section


-- @@ L18-19 verbatim
/-! Time restriction and changes of time variable commute with actual smooth cylinder
representatives. -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerLpCylinderTranslation


-- @@ L27-29 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderScalarPrimitive EulerMetricTransport
      EulerParameterWordGevrey

-- @@ L30-30 verbatim
open scoped ContDiff


-- @@ L32-34 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {K L : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace L] [CompactSpace L]


-- @@ L36-36 verbatim
section Paths


-- @@ L38-38 verbatim
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L40-43 verbatim
theorem timeComp_orbit_contDiff (p : C(K, CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) (φ : C(L, K)) :
    ContDiff ℝ ∞ (fun a => pathTranslate P a (p.comp φ)) :=
  (ContinuousMap.compCLM ℝ (CylinderL2 P V) φ).contDiff.comp hp


-- @@ L45-52 verbatim
theorem timeComp_norm (φ : C(L, K)) :
    ‖ContinuousMap.compCLM ℝ (CylinderL2 P V) φ‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg p)).2
  intro t
  exact p.norm_coe_le_norm (φ t)


-- @@ L54-61 verbatim
theorem timeComp_block_le {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (p : C(K, CylinderL2 P V)) (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p))
    (φ : C(L, K)) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => pathTranslate P b (p.comp φ)) n a ≤
      block directions q (fun b => pathTranslate P b p) n a :=
  (block_comp_clm_le directions q (ContinuousMap.compCLM ℝ (CylinderL2 P V) φ) _ hp n a).trans
    ((mul_le_mul_of_nonneg_right (timeComp_norm P φ) (block_nonneg directions q _ n a)).trans_eq
      (one_mul _))


-- @@ L63-63 verbatim
end Paths


-- @@ L65-73 verbatim
theorem pointField_timeComp (p : C(K, CylinderL2 P Space))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) (φ : C(L, K)) (t : L) :
    pointField P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t = pointField P p hp (φ t) := by
  apply Measure.eq_of_ae_eq
    ((pointField_ae P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t).symm.trans
      (pointField_ae P p hp (φ t)))
  · exact smoothField_continuous P _ (pointField_smooth P (p.comp φ) (timeComp_orbit_contDiff P p
      hp φ) t)
  · exact smoothField_continuous P _ (pointField_smooth P p hp (φ t))


-- @@ L75-83 verbatim
theorem scalarPointField_timeComp (p : C(K, CylinderL2 P ℝ))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) (φ : C(L, K)) (t : L) :
    scalarPointField P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t =
      scalarPointField P p hp (φ t) :=
  Measure.eq_of_ae_eq
    ((scalarPointField_ae P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t).symm.trans
      (scalarPointField_ae P p hp (φ t)))
    (scalarPointField_continuous P (p.comp φ) (timeComp_orbit_contDiff P p hp φ) t)
    (scalarPointField_continuous P p hp (φ t))


-- @@ L85-85 verbatim
end EulerLpCylinderTranslation


-- @@ L87-87 verbatim
end

-- @@ L88-88 verbatim
end


-- @@ L90-90 verbatim
end


-- @@ L92-92 verbatim
@[expose] public section


-- @@ L94-94 verbatim
noncomputable section


-- @@ L96-96 verbatim
namespace EulerTransversePacketProvider


-- @@ L98-100 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTimeIntervalRestriction
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
  EulerPacketProfileRecursion EulerCylinderAngleAverage

-- @@ L101-101 verbatim
open scoped ContDiff


-- @@ L103-105 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField}


-- @@ L107-108 verbatim
/-- Shifted raw, defined pointwise by `raw (τ+z.1,z.2)`. -/
def shiftedRaw (τ : ℝ) (raw : VectorField) : VectorField := fun z => raw (τ+z.1,z.2)


-- @@ L110-110 verbatim
namespace Forcing


-- @@ L112-112 verbatim
variable (G : Forcing P D raw)


-- @@ L114-125 verbatim
/-- Restriction keeps the literal original forcing on the history interval. -/
def initial (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ D.T) : Forcing P (D.initial τ hτ hτT) raw where
  path := G.path.comp (initialInclusion D.T τ hτT)
  path_orbit := timeComp_orbit_contDiff P
    (includePath P D.support D.support_measurable G.path) G.path_orbit (initialInclusion D.T τ hτT)
  raw_eq t x θ := by
    have h := G.raw_eq (initialInclusion D.T τ hτT t) x θ
    have he := congrFun (pointField_timeComp P
      (includePath P D.support D.support_measurable G.path) G.path_orbit
      (initialInclusion D.T τ hτT) t) (x,(θ : AddCircle P))
    exact h.trans he.symm
  mean_zero t := G.mean_zero (initialInclusion D.T τ hτT t)


-- @@ L127-139 verbatim
/-- The forward forcing uses elapsed time s and the literal source time τ+s. -/
def tail (τ : ℝ) (hτ : 0 ≤ τ) (hτT : τ < D.T) :
    Forcing P (D.tail τ hτ hτT) (shiftedRaw τ raw) where
  path := G.path.comp (tailInclusion D.T τ hτ)
  path_orbit := timeComp_orbit_contDiff P
    (includePath P D.support D.support_measurable G.path) G.path_orbit (tailInclusion D.T τ hτ)
  raw_eq t x θ := by
    have h := G.raw_eq (tailInclusion D.T τ hτ t) x θ
    have he := congrFun (pointField_timeComp P
      (includePath P D.support D.support_measurable G.path) G.path_orbit
      (tailInclusion D.T τ hτ) t) (x,(θ : AddCircle P))
    exact h.trans he.symm
  mean_zero t := G.mean_zero (tailInclusion D.T τ hτ t)


-- @@ L141-141 verbatim
end Forcing


-- @@ L143-143 verbatim
namespace HistoryData


-- @@ L145-145 verbatim
variable (B : HistoryData D) (G : Forcing P D raw)


-- @@ L147-154 verbatim
/-- The genuine terminal coordinate velocity of the history problem,
with its actual support, mixed smoothness, and zero angular mean. -/
def terminalInitial : InitialData P D where
  value := ⟨B.coordinatePath G ⟨D.T,D.T_pos.le,le_rfl⟩,
    B.coordinatePath_supported G ⟨D.T,D.T_pos.le,le_rfl⟩⟩
  orbit := (ContinuousMap.evalCLM ℝ ⟨D.T,D.T_pos.le,le_rfl⟩ :
    C(Icc (0 : ℝ) D.T,CylinderL2 P U) →L[ℝ] CylinderL2 P U).contDiff.comp (B.coordinatePath_orbit G)
  mean_zero := B.coordinatePath_mean_zero G ⟨D.T,D.T_pos.le,le_rfl⟩


-- @@ L156-162 verbatim
/-- The history trace in the same fixed reference-plane coordinates is the
actual initial datum passed to the forward interval. -/
def forwardInitial (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T) :
    InitialData P (D.tail τ hτ.le hτT) where
  value := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).value
  orbit := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).orbit
  mean_zero := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).mean_zero


-- @@ L164-166 verbatim
theorem forwardInitial_eq (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T) :
    ((B.forwardInitial G τ hτ hτT).value : CylinderL2 P U) =
      (B.initial τ hτ hτT.le).coordinatePath (G.initial τ hτ hτT.le) ⟨τ,hτ.le,le_rfl⟩ := rfl


-- @@ L168-168 verbatim
end HistoryData

-- @@ L169-169 verbatim
end EulerTransversePacketProvider
