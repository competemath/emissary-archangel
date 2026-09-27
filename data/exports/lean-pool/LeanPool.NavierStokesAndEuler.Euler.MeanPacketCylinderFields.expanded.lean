/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketOrbitForcing
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialEmbedding
import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMean


-- @@ L14-20 verbatim
/-!
# Actual mean outputs as constant-angle cylinder paths

The ordinary spatial L² field is embedded in the product measure. Its genuine
translation orbit, literal raw representative and true time derivative are
preserved by the same bounded linear embedding.
-/


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace EulerMeanPacketProvider


-- @@ L29-32 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderSpatialEmbedding
  EulerMeanTimeContinuousTranslation EulerPacketProfileRecursion EulerPacketCylinderField
  EulerCylinderSmoothOrbit EulerVolterraConvolution

-- @@ L33-33 verbatim
open scoped ContDiff


-- @@ L35-35 verbatim
variable (P T : ℝ) [Fact (0 < P)]


-- @@ L37-40 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanPacketCylinderFields1 : NormedAddCommGroup C(Icc (0 : ℝ) T,L2) :=
    inferInstance

-- @@ L41-43 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanPacketCylinderFields2 : NormedSpace ℝ C(Icc (0 : ℝ) T,L2) := inferInstance

-- @@ L44-47 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten
typeclass synthesis. -/
local instance instMeanPacketCylinderFields3 : NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance

-- @@ L48-51 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instMeanPacketCylinderFields4 : NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance


-- @@ L53-56 verbatim
/-- Spatial embedding path, given by `(embedding (V := Space) P).compLeftContinuous ℝ (Icc (0 :
ℝ) T)`. -/
def spatialEmbeddingPath : C(Icc (0 : ℝ) T,L2) →L[ℝ] C(Icc (0 : ℝ) T,LiftL2 P) :=
  (embedding (V := Space) P).compLeftContinuous ℝ (Icc (0 : ℝ) T)


-- @@ L58-59 verbatim
@[simp] theorem spatialEmbeddingPath_apply (p : C(Icc (0 : ℝ) T, L2))
    (t : Icc (0 : ℝ) T) : spatialEmbeddingPath P T p t = embedding P (p t) := rfl


-- @@ L61-66 verbatim
theorem spatialEmbeddingPath_translation (p : C(Icc (0 : ℝ) T, L2)) (a : LiftTangent) :
    pathTranslate P a (spatialEmbeddingPath P T p) =
      spatialEmbeddingPath P T (pathTranslation T a.1 p) := by
  apply ContinuousMap.ext
  intro t
  exact EulerCylinderSpatialMean.embedding_translate P a (p t)


-- @@ L68-73 verbatim
theorem spatialEmbeddingPath_orbit (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (spatialEmbeddingPath P T p)) := by
  have h := (spatialEmbeddingPath P T).contDiff.comp
    (hp.comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : LiftTangent → Space)))
  simpa only [Function.comp_def,spatialEmbeddingPath_translation] using h


-- @@ L75-81 verbatim
theorem spatialEmbeddingPath_time (hT : 0 ≤ T) (p q : C(Icc (0 : ℝ) T, L2))
    (h : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (spatialEmbeddingPath P T p))
      (spatialEmbeddingPath P T q t) (Icc (0 : ℝ) T) t :=
  (embedding (V := Space) P).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (h t)


-- @@ L83-83 verbatim
namespace Forcing


-- @@ L85-85 verbatim
variable {T} {D : Data} {raw : VectorField} (G : Forcing D raw)


-- @@ L87-101 verbatim
/-- Literal smooth mean forcing becomes an actual cylinder witness with no angular dependence. -/
def toCylinderField : Field P D.T raw :=
  Field.ofLifted (spatialEmbeddingPath P D.T G.path)
    (spatialEmbeddingPath_orbit P D.T G.path G.path_orbit)
    (fun t z => (G.slices t).field z.1)
    (fun t => (G.slices t).smooth.continuous.comp continuous_fst)
    (fun t => by
      have hg : (G.path t : Space → Space) =ᵐ[volume] (G.slices t).field := by
        rw [G.path_eq]
        exact (G.slices t).toLp_ae
      filter_upwards [lift_ae P (G.path t),
        (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
          (ν := (volume : Measure (AddCircle P)))).ae hg] with z hl hz
      exact hl.trans hz)
    G.raw_eq


-- @@ L103-104 verbatim
@[simp] theorem toCylinderField_path :
    (G.toCylinderField P).path = spatialEmbeddingPath P D.T G.path := rfl


-- @@ L106-107 verbatim
/-- Vector cylinder field, given by `G.vectorForcing.toCylinderField P`. -/
def vectorCylinderField : Field P D.T G.vector := G.vectorForcing.toCylinderField P


-- @@ L109-111 verbatim
/-- Vector derivative cylinder field, given by `G.vectorDerivativeForcing.toCylinderField P`. -/
def vectorDerivativeCylinderField : Field P D.T G.vectorDerivative :=
  G.vectorDerivativeForcing.toCylinderField P


-- @@ L113-115 verbatim
theorem vectorCylinderField_time :
    TimeDerivative D.T_pos.le (G.vectorCylinderField P) (G.vectorDerivativeCylinderField P) :=
  spatialEmbeddingPath_time P D.T D.T_pos.le G.velocityPath G.derivativePath G.velocityPath_time


-- @@ L117-117 verbatim
end Forcing


-- @@ L119-124 verbatim
/-- Mean solve cylinder field, given by `((Classical.choice h).vectorCylinderField P).congr (fun
_ _ _ => by rw [meanSolve_of_admissible D raw h])`. -/
def meanSolveCylinderField (D : Data) (raw : VectorField) (h : Nonempty (Forcing D raw)) :
    Field P D.T (meanSolve D raw).1 :=
  ((Classical.choice h).vectorCylinderField P).congr (fun _ _ _ => by
    rw [meanSolve_of_admissible D raw h])


-- @@ L126-126 verbatim
end EulerMeanPacketProvider
