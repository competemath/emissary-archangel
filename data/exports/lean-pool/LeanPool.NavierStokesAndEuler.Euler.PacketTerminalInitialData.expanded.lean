/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalDatumBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.PacketTerminalDatum
public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
public import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMap
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageRepresentative
import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarPrimitive
import LeanPool.NavierStokesAndEuler.Euler.CylinderSmoothOrbit


-- @@ L18-18 verbatim
/-! The manuscript's literal compact wave is an admissible terminal coordinate field. -/


-- @@ L20-20 verbatim
section


-- @@ L22-22 verbatim
/-! The literal terminal datum belongs to the actual supported, mean-zero cylinder space. -/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace EulerPacketTerminalDatum


-- @@ L30-34 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerSpatialCutoffs EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpSupportedSubspace
  EulerCylinderAngleAverage EulerCylinderConstantMap EulerCylinderSmoothOrbit
      EulerCylinderSobolevSpace
  EulerCylinderScalarPrimitive EulerCylinderFieldReflection

-- @@ L35-35 verbatim
open scoped ContDiff


-- @@ L37-45 verbatim
theorem terminal_map {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (δ : ℝ) (hδ : 0 < δ) (ξ : U) (L : U →L[ℝ] V) :
    terminal δ hδ (L ξ) = EulerCylinderConstantMap.map period L (terminal δ hδ ξ) := by
  apply Lp.ext
  filter_upwards [terminal_ae δ hδ (L ξ),map_ae period L (terminal δ hδ ξ),
    terminal_ae δ hδ ξ] with x hl hr hu
  rw [hl,hr,hu]
  exact (L.map_smul (scalarField δ x) ξ).symm


-- @@ L47-60 verbatim
private theorem terminal_vector_average (δ : ℝ) (hδ : 0 < δ) :
    average period (terminal δ hδ unitVector) = 0 := by
  let J := EulerCylinderSmoothOrbit.sobolev period 3 (terminal δ hδ unitVector)
    (terminal_orbit_contDiff δ hδ unitVector)
  have hval : value period J = terminal δ hδ unitVector :=
    EulerCylinderSmoothOrbit.sobolev_value period 3 (terminal δ hδ unitVector)
      (terminal_orbit_contDiff δ hδ unitVector)
  have hrep : (value period J : LiftDomain period → Space) =ᵐ[liftMeasure period]
      field δ unitVector := by
    rw [hval]
    exact terminal_ae δ hδ unitVector
  have havg := (average_eq_zero_iff period J (field δ unitVector)
    (compactField δ hδ unitVector).continuous hrep).2 (field_integral_zero δ unitVector)
  rwa [hval] at havg


-- @@ L62-73 verbatim
theorem terminal_average_zero {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [CompleteSpace U] (δ : ℝ) (hδ : 0 < δ) (ξ : U) :
    average period (terminal δ hδ ξ) = 0 := by
  let L : Space →L[ℝ] U := (toSpanSingleton ℝ ξ).comp scalarProject
  have hunit : scalarProject unitVector = 1 := by
    simpa only [scalarEmbed,toSpanSingleton_apply,one_smul] using project_embed 1
  have hL : L unitVector = ξ := by
    change scalarProject unitVector • ξ = ξ
    rw [hunit,one_smul]
  rw [← hL,terminal_map δ hδ unitVector L,
    average_intertwines period (EulerCylinderConstantMap.map period L)
      (fun s u => map_translation period L (0,s) u),terminal_vector_average δ hδ,map_zero]


-- @@ L75-83 verbatim
theorem terminal_supported {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (ξ : U) (S : Set Space) (hS : MeasurableSet S)
    (hs : tsupport innerCutoff ⊆ S) : terminal δ hδ ξ ∈ Supported period U S hS := by
  apply (mem_supportedSpace_ae (liftMeasure period) (spatialSet period S)
    (spatialSet_measurable period S hS) _).2
  filter_upwards [terminal_ae δ hδ ξ] with x hx hn
  rw [hx]
  apply field_zero_outside δ ξ x
  exact fun hh => hn (hs hh)


-- @@ L85-90 verbatim
theorem terminal_reflection {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (δ : ℝ) (hδ : 0 < δ) (ξ : U) :
    reflection period (terminal δ hδ ξ) = -terminal δ hδ ξ := by
  simpa only [neg_one_smul] using reflection_of_representative period
    (terminal δ hδ ξ) (field δ ξ) (terminal_ae δ hδ ξ) (-1)
    (fun x => by simpa only [neg_one_smul] using field_odd δ ξ x)


-- @@ L92-92 verbatim
end EulerPacketTerminalDatum


-- @@ L94-94 verbatim
end

-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
end


-- @@ L99-99 verbatim
@[expose] public section


-- @@ L101-101 verbatim
noncomputable section


-- @@ L103-103 verbatim
namespace EulerPacketTerminalDatum


-- @@ L105-107 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerParameterWordGevrey EulerGevrey

-- @@ L108-108 verbatim
open scoped ContDiff


-- @@ L110-112 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support)


-- @@ L114-118 verbatim
/-- Initial data, bundling `value`, `orbit`, `mean_zero`. -/
def initialData : InitialData period D where
  value := ⟨terminal δ hδ ξ,terminal_supported δ hδ ξ D.support D.support_measurable hs⟩
  orbit := terminal_orbit_contDiff δ hδ ξ
  mean_zero := terminal_average_zero δ hδ ξ


-- @@ L120-121 verbatim
theorem initialData_value : ((initialData D δ hδ ξ hs).value : CylinderL2 period U) =
    terminal δ hδ ξ := rfl


-- @@ L123-130 verbatim
theorem initialData_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hδ1 : δ ≤ 1) (n : ℕ) :
    block directions q (fun b => translate period b
      ((initialData D δ hδ ξ hs).value : CylinderL2 period U)) n 0 ≤
      sobolevCoefficientAmplitude ι q (jetRadius δ) (scalarJetCost δ * ‖ξ‖ * terminalMass) *
        majorant (wordRadius ι δ) 0 n :=
  terminal_block_bound directions hd q δ hδ hδ1 ξ n 0


-- @@ L132-132 verbatim
end EulerPacketTerminalDatum
