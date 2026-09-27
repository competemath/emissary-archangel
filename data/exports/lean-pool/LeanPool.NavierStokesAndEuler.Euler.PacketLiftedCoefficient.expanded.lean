/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftEquation
public import LeanPool.NavierStokesAndEuler.Euler.LiftedSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
import LeanPool.NavierStokesAndEuler.Euler.CylinderMeasureDescent
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftRadiusBounds
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblySourceTower
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTensorBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderBoundedCover
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Compact
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Comp


-- @@ L29-31 verbatim
/-! Actual smooth four-dimensional coefficients of the corrected packet.
The lifted field equals the constructed exact velocity, has the genuine
time derivative, is periodic, and has zero divergence. -/


-- @@ L33-33 verbatim
section


-- @@ L35-38 verbatim
/-! Transposing a tensor with continuous bounded path values gives an
actual continuous path of bounded tensor fields. Finite coordinates prove
continuity; the norm estimate uses the original multilinear map directly
and therefore has constant one. -/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L46-46 verbatim
namespace EulerContinuousBoundedTensor


-- @@ L48-51 verbatim
variable {K X E V : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]


-- @@ L53-56 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instContinuousBoundedTensor1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance

-- @@ L57-58 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instContinuousBoundedTensor2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance

-- @@ L59-62 verbatim
/-- Cache the standard `NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousBoundedTensor3 (n : ℕ) : NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

-- @@ L63-66 verbatim
/-- Cache the standard `NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousBoundedTensor4 (n : ℕ) : NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance


-- @@ L68-74 verbatim
/-- Coordinates, given by `ContinuousLinearMap.pi (fun w => (ContinuousLinearMap.id ℝ (E
[×n]→L[ℝ] V)).flipMultilinear (fun i => Module.finBasis ℝ E (w i)))`. -/
def coordinates (n : ℕ) :
    (E [×n]→L[ℝ] V) →L[ℝ] ((Fin n → Fin (Module.finrank ℝ E)) → V) :=
  ContinuousLinearMap.pi (fun w =>
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] V)).flipMultilinear
      (fun i => Module.finBasis ℝ E (w i)))


-- @@ L76-83 verbatim
omit [FiniteDimensional ℝ V] in
private theorem coordinates_injective (n : ℕ) :
    Function.Injective (coordinates (E := E) (V := V) n) := by
  intro A B h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin n => Module.finBasis ℝ E)
  intro w
  exact congrFun h w


-- @@ L85-89 verbatim
/-- Reassembly, given by `((coordinates (E := E) (V := V)
n).toLinearMap.leftInverse).toContinuousLinearMap`. -/
def reassembly (n : ℕ) :
    ((Fin n → Fin (Module.finrank ℝ E)) → V) →L[ℝ] (E [×n]→L[ℝ] V) :=
  ((coordinates (E := E) (V := V) n).toLinearMap.leftInverse).toContinuousLinearMap


-- @@ L91-94 verbatim
private theorem reassembly_coordinates (n : ℕ) (A : E [×n]→L[ℝ] V) :
    reassembly n (coordinates n A) = A :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (coordinates_injective n)) A


-- @@ L96-102 verbatim
/-- Tuple bounded as an element of `(ι → (X →ᵇ V)) →L[ℝ] (X →ᵇ (ι → V))`. -/
def tupleBounded {ι : Type*} [Fintype ι] :
    (ι → (X →ᵇ V)) →L[ℝ] (X →ᵇ (ι → V)) := by
  classical
  exact ∑ i : ι,
    ((ContinuousLinearMap.single ℝ (fun _ : ι => V) i).compLeftContinuousBounded X).comp
      (ContinuousLinearMap.proj i)


-- @@ L104-109 verbatim
omit [FiniteDimensional ℝ V] in
private theorem tupleBounded_apply {ι : Type*} [Fintype ι]
    (u : ι → (X →ᵇ V)) (x : X) (i : ι) :
    tupleBounded u x i = u i x := by
  classical
  simp [tupleBounded]


-- @@ L111-119 verbatim
/-- Tensor path, bundling `toFun`, `continuous_toFun`. -/
def tensorPath (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) :
    C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toFun t := (reassembly (E := E) (V := V) n).compLeftContinuousBounded X
    (tupleBounded (fun w => A (fun i => Module.finBasis ℝ E (w i)) t))
  continuous_toFun :=
    ((reassembly (E := E) (V := V) n).compLeftContinuousBounded X).continuous.comp
      ((tupleBounded (X := X) (V := V)).continuous.comp
        (continuous_pi (fun w => (A (fun i => Module.finBasis ℝ E (w i))).continuous)))


-- @@ L121-132 verbatim
omit [CompactSpace K] in
theorem tensorPath_eq (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) (t : K) (x : X) :
    tensorPath n A t x = (BoundedContinuousFunction.evalCLM ℝ x).compContinuousMultilinearMap
      ((ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap A) := by
  change reassembly n (tupleBounded _ x) = _
  have he : tupleBounded (fun w => A (fun i => Module.finBasis ℝ E (w i)) t) x =
      coordinates n ((BoundedContinuousFunction.evalCLM ℝ x).compContinuousMultilinearMap
        ((ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap A)) := by
    funext w
    rw [tupleBounded_apply]
    rfl
  rw [he, reassembly_coordinates]


-- @@ L134-138 verbatim
omit [CompactSpace K] in
@[simp] theorem tensorPath_apply (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V))
    (t : K) (x : X) (v : Fin n → E) : tensorPath n A t x v = A v t x := by
  rw [tensorPath_eq]
  rfl


-- @@ L140-143 verbatim
/-- Cache the standard `NormedAddCommGroup (C(K, X →ᵇ (E [×n]→L[ℝ] V)))` instance to shorten
typeclass synthesis. -/
local instance instContinuousBoundedTensor5 (n : ℕ) : NormedAddCommGroup (C(K, X →ᵇ (E [×n]→L[ℝ]
    V))) := inferInstance

-- @@ L144-147 verbatim
/-- Cache the standard `NormedSpace ℝ (C(K, X →ᵇ (E [×n]→L[ℝ] V)))` instance to shorten
typeclass synthesis. -/
local instance instContinuousBoundedTensor6 (n : ℕ) : NormedSpace ℝ (C(K, X →ᵇ (E [×n]→L[ℝ] V))) :=
    inferInstance

-- @@ L148-151 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] C(K, X →ᵇ V))` instance to shorten
typeclass synthesis. -/
local instance instContinuousBoundedTensor7 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] C(K, X →ᵇ V))
    := inferInstance

-- @@ L152-155 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] C(K, X →ᵇ V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousBoundedTensor8 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] C(K, X →ᵇ V)) :=
    inferInstance


-- @@ L157-166 verbatim
theorem tensorPath_norm_le (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) :
    ‖tensorPath n A‖ ≤ ‖A‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg A)
  intro v
  rw [tensorPath_apply]
  exact (((A v t).norm_coe_le_norm x).trans ((A v).norm_coe_le_norm t)).trans (A.le_opNorm v)


-- @@ L168-189 verbatim
/-- Tensor path linear, bundling `toFun`, `map_add`, `map_smul`. -/
def tensorPathLinear (n : ℕ) :
    (E [×n]→L[ℝ] C(K, X →ᵇ V)) →ₗ[ℝ] C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toFun := tensorPath n
  map_add' A B := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [tensorPath_apply, add_apply, ContinuousMap.add_apply,
      BoundedContinuousFunction.add_apply]
  map_smul' c A := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [tensorPath_apply, smul_apply, ContinuousMap.smul_apply,
      BoundedContinuousFunction.smul_apply, RingHom.id_apply]


-- @@ L191-199 verbatim
/-- Tensor path map, bundling `toLinearMap`, `cont`. -/
def tensorPathMap (n : ℕ) :
    (E [×n]→L[ℝ] C(K, X →ᵇ V)) →L[ℝ] C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toLinearMap := tensorPathLinear n
  cont := AddMonoidHomClass.continuous_of_bound
    (tensorPathLinear (K := K) (X := X) (E := E) (V := V) n) 1
    (fun A => by
      change ‖tensorPath n A‖ ≤ 1 * ‖A‖
      simpa only [one_mul] using tensorPath_norm_le n A)


-- @@ L201-203 verbatim
@[simp] theorem tensorPathMap_apply (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V))
    (t : K) (x : X) (v : Fin n → E) : tensorPathMap n A t x v = A v t x :=
  tensorPath_apply n A t x v


-- @@ L205-210 verbatim
theorem tensorPathMap_norm_le (n : ℕ) :
    ‖tensorPathMap (K := K) (X := X) (E := E) (V := V) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖tensorPath n A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using tensorPath_norm_le n A


-- @@ L212-223 verbatim
theorem tensorPath_iteratedFDeriv (f : E → C(K, X →ᵇ V)) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (a : E) (t : K) (x : X) :
    tensorPathMap n (iteratedFDeriv ℝ n f a) t x =
      iteratedFDeriv ℝ n (fun b => f b t x) a := by
  change tensorPath n (iteratedFDeriv ℝ n f a) t x = _
  rw [tensorPath_eq]
  have ht := (ContinuousMap.evalCLM ℝ t).iteratedFDeriv_comp_left (x := a) hf.contDiffAt
    (show (n : ℕ∞) ≤ ∞ by simp)
  rw [← ht]
  exact ((BoundedContinuousFunction.evalCLM ℝ x).iteratedFDeriv_comp_left
    ((ContinuousMap.evalCLM ℝ t).contDiff.comp hf).contDiffAt
    (show (n : ℕ∞) ≤ ∞ by simp)).symm


-- @@ L225-225 verbatim
end EulerContinuousBoundedTensor


-- @@ L227-227 verbatim
end

-- @@ L228-228 verbatim
end


-- @@ L230-230 verbatim
end


-- @@ L232-232 verbatim
section


-- @@ L234-236 verbatim
/-! The actual finite packet fields supply bounded smooth cover
coefficients. Their fixed-Hq word bounds give uniform tensor-jet bounds,
with a single fixed coordinate radius conversion. -/


-- @@ L238-238 verbatim
section


-- @@ L240-243 verbatim
/-! Actual smooth bounded real-cover coefficients obtained from a smooth
mixed translation orbit in cylinder L². Every spatial tensor jet is a
continuous path in the uniform norm. No integrability on the real cover is
asserted or used. -/


-- @@ L245-245 verbatim
@[expose] public section


-- @@ L247-247 verbatim
noncomputable section


-- @@ L249-249 verbatim
namespace EulerCylinderSmoothTimeField


-- @@ L251-252 verbatim
open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerCylinderBoundedCover EulerContinuousBoundedTensor

-- @@ L253-253 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L255-257 verbatim
variable (P : ℝ) [Fact (0 < P)] {K : Type} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))


-- @@ L259-262 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance

-- @@ L263-266 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)
    := inferInstance

-- @@ L267-270 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instCylinderSmoothTimeField3 (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance

-- @@ L271-274 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instCylinderSmoothTimeField4 (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance


-- @@ L276-278 verbatim
/-- Cover jet, given by `tensorPathMap n (iteratedFDeriv ℝ n (coverOrbit P p hp) 0)`. -/
def coverJet (n : ℕ) : C(K, LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) :=
  tensorPathMap n (iteratedFDeriv ℝ n (coverOrbit P p hp) 0)


-- @@ L280-286 verbatim
theorem coverJet_eq (n : ℕ) (t : K) (x : LiftTangent) :
    coverJet P p hp n t x = iteratedFDeriv ℝ n (coverPath P p hp t : LiftTangent → Space) x := by
  rw [coverJet, tensorPath_iteratedFDeriv _ (coverOrbit_contDiff P p hp)]
  have he : (fun a => coverOrbit P p hp a t x) =
      fun a => coverPath P p hp t (x+a) := funext (fun a => coverOrbit_apply P p hp a t x)
  rw [he, iteratedFDeriv_comp_add_left]
  simp only [add_zero]


-- @@ L288-296 verbatim
theorem coverPath_smooth (t : K) :
    ContDiff ℝ ∞ (coverPath P p hp t : LiftTangent → Space) := by
  have hc := (BoundedContinuousFunction.evalCLM ℝ (0 : LiftTangent)).contDiff.comp
    ((ContinuousMap.evalCLM ℝ t).contDiff.comp (coverOrbit_contDiff P p hp))
  have he : (fun a => coverOrbit P p hp a t 0) =
      (coverPath P p hp t : LiftTangent → Space) := by
    funext a
    simpa only [zero_add] using coverOrbit_apply P p hp a t 0
  exact he ▸ hc


-- @@ L298-303 verbatim
/-- Of path, bundling `field`, `smooth`, `jet`, `jet_eq`. -/
def ofPath : SmoothTimeField K LiftTangent Space where
  field := coverPath P p hp
  smooth := coverPath_smooth P p hp
  jet := coverJet P p hp
  jet_eq := coverJet_eq P p hp


-- @@ L305-306 verbatim
@[simp] theorem ofPath_apply (t : K) (x : LiftTangent) :
    (ofPath P p hp).field t x = pointField P p hp t (coveringMap P x) := rfl


-- @@ L308-317 verbatim
theorem ofPath_jet_norm_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (t : K) (x : LiftTangent),
      ‖iteratedFDeriv ℝ n (fun y => pointField P p hp t (coveringMap P y)) x‖ ≤ C) :
    ‖(ofPath P p hp).jet n‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hC).2
  intro t
  apply (BoundedContinuousFunction.norm_le hC).2
  intro x
  rw [(ofPath P p hp).jet_eq]
  exact hb t x


-- @@ L319-319 verbatim
end EulerCylinderSmoothTimeField


-- @@ L321-321 verbatim
end

-- @@ L322-322 verbatim
end


-- @@ L324-324 verbatim
end


-- @@ L326-326 verbatim
@[expose] public section


-- @@ L328-328 verbatim
noncomputable section


-- @@ L330-330 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L332-334 verbatim
open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerCylinderSmoothTimeField EulerCylinderCoordinates EulerCylinderSobolevSpace
  EulerPacketProfileRecursion EulerGevrey

-- @@ L335-335 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L337-337 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw raw_t : VectorField}


-- @@ L339-342 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketFieldSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance

-- @@ L343-346 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketFieldSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance

-- @@ L347-350 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instPacketFieldSmoothTimeField3 (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance

-- @@ L351-354 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instPacketFieldSmoothTimeField4 (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance


-- @@ L356-358 verbatim
/-- To smooth time field, given by `ofPath P G.path G.orbit`. -/
def toSmoothTimeField (G : Field P T raw) : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  ofPath P G.path G.orbit


-- @@ L360-361 verbatim
theorem toSmoothTimeField_apply (G : Field P T raw) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.toSmoothTimeField.field t x = raw (t,x) := (G.raw_eq t x.1 x.2).symm


-- @@ L363-367 verbatim
theorem toSmoothTimeField_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (hT : 0 ≤ T) (hd : TimeDerivative hT G H) :
    SmoothTimeField.TimeDerivative T hT G.toSmoothTimeField H.toSmoothTimeField := by
  intro t x
  exact pointField_hasDerivWithinAt P T hT G.path H.path G.orbit H.orbit hd t (coveringMap P x)


-- @@ L369-373 verbatim
theorem toSmoothTimeField_map_jet (G : Field P T raw) (L : Space →L[ℝ] Space) (n : ℕ) :
    (G.map L).toSmoothTimeField.jet n = (G.toSmoothTimeField.map L).jet n := by
  apply SmoothTimeField.jet_eq_of_field_eq
  intro t x
  rw [(G.map L).toSmoothTimeField_apply, SmoothTimeField.map_apply, G.toSmoothTimeField_apply]


-- @@ L375-387 verbatim
theorem WordBound.toSmoothTimeField_jet_bound {G : Field P T raw} {q : ℕ} {R A : ℝ}
    (hG : G.WordBound q R A 0) (hq : 3 ≤ q) (hR : 0 ≤ R) (hA : 0 ≤ A) (n : ℕ) :
    ‖G.toSmoothTimeField.jet n‖ ≤ (sobolevEmbeddingConstant P 3*A) *
      (‖coordinateEquiv.symm.toContinuousLinearMap‖*R)^n * (n.factorial : ℝ)^2 := by
  have hS := sobolevEmbeddingConstant_nonneg P 3
  apply ofPath_jet_norm_le P G.path G.orbit n _ (by positivity)
  intro t x
  have he : (fun y => pointField P G.path G.orbit t (coveringMap P y)) =
      fun y => raw (t,y) := funext (fun y => (G.raw_eq t y.1 y.2).symm)
  rw [he]
  apply (hG.raw_tensor_le hq t n x).trans_eq
  simp only [majorant, Nat.add_zero, mul_pow]
  ring


-- @@ L389-389 verbatim
end EulerPacketCylinderField.Field


-- @@ L391-391 verbatim
end

-- @@ L392-392 verbatim
end


-- @@ L394-394 verbatim
end


-- @@ L396-396 verbatim
section


-- @@ L398-400 verbatim
/-! The constructed all-order correction and its true time derivative
are actual smooth bounded cover coefficients. Their quantitative bounds
come from the checked weighted Sobolev estimates. -/


-- @@ L402-402 verbatim
@[expose] public section


-- @@ L404-404 verbatim
noncomputable section


-- @@ L406-406 verbatim
namespace EulerAllOrderDriftCorrection


-- @@ L408-409 verbatim
open Set EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerCylinderSobolevSpace
  EulerCylinderCoordinates

-- @@ L410-410 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L412-412 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}


-- @@ L414-417 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Vector3)` instance to shorten
typeclass synthesis. -/
local instance instCorrectionSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Vector3) := inferInstance

-- @@ L418-421 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Vector3)` instance to shorten
typeclass synthesis. -/
local instance instCorrectionSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ]
    Vector3) := inferInstance

-- @@ L422-425 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3))`
instance to shorten typeclass synthesis. -/
local instance instCorrectionSmoothTimeField3 (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3)) := inferInstance

-- @@ L426-429 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3))` instance
to shorten typeclass synthesis. -/
local instance instCorrectionSmoothTimeField4 (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3)) := inferInstance


-- @@ L431-434 verbatim
/-- Correction coefficient, given by `(B.fieldTower P).toSmoothTimeField`. -/
def Budget.correctionCoefficient (B : Budget P hT A) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Vector3 :=
  (B.fieldTower P).toSmoothTimeField


-- @@ L436-439 verbatim
/-- Correction derivative coefficient, given by `(B.timeDerivativeTower P).toSmoothTimeField`. -/
def Budget.correctionDerivativeCoefficient (B : Budget P hT A) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Vector3 :=
  (B.timeDerivativeTower P).toSmoothTimeField


-- @@ L441-445 verbatim
theorem Budget.correctionCoefficient_timeDerivative (B : Budget P hT A) :
    SmoothTimeField.TimeDerivative T hT.le (B.correctionCoefficient P)
      (B.correctionDerivativeCoefficient P) :=
  (B.fieldTower P).toSmoothTimeField_timeDerivative_of_interior (B.timeDerivativeTower P)
    hT.le 6 (by norm_num) (B.fieldTower_hasDerivAt_timeDerivativeTower P 6 le_rfl)


-- @@ L447-454 verbatim
theorem Budget.correctionCoefficient_jet_bound (B : Budget P hT A) (n : ℕ) :
    ‖(B.correctionCoefficient P).jet n‖ ≤
      (sobolevEmbeddingConstant P 3 * B.correctionSize P) *
        (‖coordinateEquiv.symm.toContinuousLinearMap‖ * (B.reducedRadius P)⁻¹)^n *
          (n.factorial : ℝ)^2 :=
  (B.fieldTower P).toSmoothTimeField_jet_weighted n (B.reducedRadius P)
    (B.correctionSize P) (B.reducedRadius_pos P) (B.correctionSize_nonneg P)
    (B.fieldTower_reducedNorm P (n+6) n le_rfl)


-- @@ L456-466 verbatim
theorem Budget.correctionDerivativeCoefficient_jet_bound (B : Budget P hT A)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (n : ℕ) (t : Icc (0 : ℝ) T),
      EulerSobolevGevreyOperators.weightedNorm P 6 n (B.reducedRadius P)
        ((B.timeDerivativeTower P).realization (n + 6) t) ≤ C) (n : ℕ) :
    ‖(B.correctionDerivativeCoefficient P).jet n‖ ≤
      (sobolevEmbeddingConstant P 3 * C) *
        (‖coordinateEquiv.symm.toContinuousLinearMap‖ * (B.reducedRadius P)⁻¹)^n *
          (n.factorial : ℝ)^2 :=
  (B.timeDerivativeTower P).toSmoothTimeField_jet_weighted n (B.reducedRadius P)
    C (B.reducedRadius_pos P) hC (hb n)


-- @@ L468-468 verbatim
end EulerAllOrderDriftCorrection


-- @@ L470-470 verbatim
end

-- @@ L471-471 verbatim
end


-- @@ L473-473 verbatim
end


-- @@ L475-475 verbatim
@[expose] public section


-- @@ L477-477 verbatim
noncomputable section


-- @@ L479-479 verbatim
namespace EulerAllOrderDriftCorrection


-- @@ L481-483 verbatim
open Set MeasureTheory EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerSmoothLimit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderSmoothOrbit
  EulerLiftedSmoothTimeField EulerLiftedTransportTrace EulerMetricTransport

-- @@ L484-484 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L486-487 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A) {raw raw_t : VectorField}


-- @@ L489-492 verbatim
/-- Packet coefficient, given by `G.toSmoothTimeField.add (B.correctionCoefficient P)`. -/
def Budget.packetCoefficient (G : Field P T raw) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  G.toSmoothTimeField.add (B.correctionCoefficient P)


-- @@ L494-498 verbatim
/-- Packet derivative coefficient, given by `H.toSmoothTimeField.add
(B.correctionDerivativeCoefficient P)`. -/
def Budget.packetDerivativeCoefficient (H : Field P T raw_t) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  H.toSmoothTimeField.add (B.correctionDerivativeCoefficient P)


-- @@ L500-503 verbatim
/-- Lifted packet coefficient, given by `lift (B.packetCoefficient P G) A.κ A.direction`. -/
def Budget.liftedPacketCoefficient (G : Field P T raw) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  lift (B.packetCoefficient P G) A.κ A.direction


-- @@ L505-509 verbatim
/-- Lifted packet derivative coefficient, given by `lift (B.packetDerivativeCoefficient P H) A.κ
A.direction`. -/
def Budget.liftedPacketDerivativeCoefficient (H : Field P T raw_t) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  lift (B.packetDerivativeCoefficient P H) A.κ A.direction


-- @@ L511-521 verbatim
theorem Budget.packetCoefficient_eq_corrected (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.packetCoefficient P G).field t x = (B.correctedFieldTower P).pointField t (coveringMap P x)
        := by
  rw [B.correctedFieldTower_eq P, FieldTower.add_pointField, hG]
  change G.toSmoothTimeField.field t x + (B.fieldTower P).pointField t (coveringMap P x) = _
  rw [G.toSmoothTimeField_apply]
  change raw (t,x) + (B.fieldTower P).pointField t (coveringMap P x) =
    G.toFieldTower.pointField t (x.1,(x.2 : AddCircle P)) +
      (B.fieldTower P).pointField t (coveringMap P x)
  rw [G.toFieldTower_pointField_raw]


-- @@ L523-529 verbatim
theorem Budget.liftedPacketCoefficient_eq_corrected (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.liftedPacketCoefficient P G).field t x =
      transportDirection A.κ A.direction ((B.correctedFieldTower P).pointField t (coveringMap P x))
          := by
  change transportDirection A.κ A.direction ((B.packetCoefficient P G).field t x) = _
  rw [B.packetCoefficient_eq_corrected P G hG]


-- @@ L531-535 verbatim
theorem Budget.packetCoefficient_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (h : TimeDerivative hT.le G H) :
    SmoothTimeField.TimeDerivative T hT.le (B.packetCoefficient P G)
      (B.packetDerivativeCoefficient P H) :=
  (G.toSmoothTimeField_timeDerivative H hT.le h).add (B.correctionCoefficient_timeDerivative P)


-- @@ L537-541 verbatim
theorem Budget.liftedPacketCoefficient_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (h : TimeDerivative hT.le G H) :
    SmoothTimeField.TimeDerivative T hT.le (B.liftedPacketCoefficient P G)
      (B.liftedPacketDerivativeCoefficient P H) :=
  (B.packetCoefficient_timeDerivative P G H h).map (transportLinear A.κ A.direction)


-- @@ L543-553 verbatim
theorem Budget.liftedPacketCoefficient_periodic (G : Field P T raw)
    (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.liftedPacketCoefficient P G).field t (x.1,(c : ℝ)+x.2) =
      (B.liftedPacketCoefficient P G).field t x := by
  have hc : coveringMap P (x.1,(c : ℝ)+x.2) = coveringMap P x :=
    EulerCylinderMeasureDescent.coveringMap_deck P c x
  change transportDirection A.κ A.direction
    (EulerCylinderSmoothOrbit.pointField P G.path G.orbit t (coveringMap P (x.1,(c : ℝ)+x.2)) +
      (B.fieldTower P).pointField t (coveringMap P (x.1,(c : ℝ)+x.2))) = _
  rw [hc]
  rfl


-- @@ L555-566 verbatim
theorem Budget.liftedPacketCoefficient_trace (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    LinearMap.trace ℝ LiftTangent
      (fderiv ℝ ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent)
          x).toLinearMap = 0 := by
  have he : ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) =
      coverVelocity P A.κ A.direction ((B.correctedFieldTower P).pointField t) :=
    funext (B.liftedPacketCoefficient_eq_corrected P G hG t)
  rw [he]
  exact coverVelocity_trace_zero P A.κ A.direction ((B.correctedFieldTower P).pointField t)
    ((B.correctedFieldTower P).field t) (B.correctedFieldTower_divergence P t)
    ((B.correctedFieldTower P).pointField_ae t) ((B.correctedFieldTower P).pointField_smooth t) x


-- @@ L568-568 verbatim
end EulerAllOrderDriftCorrection
