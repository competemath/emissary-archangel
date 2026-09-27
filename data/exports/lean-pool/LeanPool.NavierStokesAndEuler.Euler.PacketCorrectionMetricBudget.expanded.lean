/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionSourceData
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime


-- @@ L13-16 verbatim
/-! A genuine inverse-metric budget for the source correction data.
Its time derivative, symmetry, coercivity and inverse identity are proved
from the prescribed deformation; the bounds are finite norms of actual
coefficient paths and their actual first translation derivative. -/


-- @@ L18-18 verbatim
section


-- @@ L20-21 verbatim
/-! The time derivative of the actual inverse pressure metric, first as
a bounded matrix field and then as its cylinder L² multiplier. -/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace EulerPacketCorrectionCoefficients


-- @@ L29-31 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets
  EulerPacketCylinderField EulerLpCylinderRectangular EulerLiftedGradientSpace
  EulerVolterraConvolution EulerTransverseGramPath EulerMeanCoefficients

-- @@ L32-32 verbatim
open scoped BoundedContinuousFunction


-- @@ L34-37 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricTime1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L38-40 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricTime2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

-- @@ L41-44 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricTime3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

-- @@ L45-48 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricTime4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance


-- @@ L50-51 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)


-- @@ L53-57 verbatim
/-- Raw inverse metric time, given by `(rawFrameTime D z).adjoint.comp (rawFrame D z) +
(rawFrame D z).adjoint.comp (rawFrameTime D z)`. -/
def rawInverseMetricTime (z : Domain) : Space →L[ℝ] Space :=
  (rawFrameTime D z).adjoint.comp (rawFrame D z) +
    (rawFrame D z).adjoint.comp (rawFrameTime D z)


-- @@ L59-63 verbatim
/-- Inverse metric time coefficient, given by `((frameTimeCoefficient D).adjoint.comp
(frameCoefficient D)).add ((frameCoefficient D).adjoint.comp (frameTimeCoefficient D))`. -/
def inverseMetricTimeCoefficient : MatrixCoefficient D.T (rawInverseMetricTime D) :=
  ((frameTimeCoefficient D).adjoint.comp (frameCoefficient D)).add
    ((frameCoefficient D).adjoint.comp (frameTimeCoefficient D))


-- @@ L65-68 verbatim
@[simp] theorem inverseMetricTimeCoefficient_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (inverseMetricTimeCoefficient D).path t x =
      (D.F₁.field t x).adjoint.comp (D.F.field t x) +
        (D.F.field t x).adjoint.comp (D.F₁.field t x) := rfl


-- @@ L70-91 verbatim
theorem inverseMetric_field_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T)
    (x : Space) :
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le (inverseMetricCoefficient D).path s x)
      (extendPath D.T D.T_pos.le (inverseMetricTimeCoefficient D).path t x)
      (Icc (0 : ℝ) D.T) t := by
  have h := hasDerivWithinAt_gram
    (fun s => extendPath D.T D.T_pos.le D.F.field s x)
    (extendPath D.T D.T_pos.le D.F₁.field t x)
    (Icc (0 : ℝ) D.T) t (D.frame_time t ht x)
  have hvalue : (fun s => extendPath D.T D.T_pos.le (inverseMetricCoefficient D).path s x) =
      fun s => (extendPath D.T D.T_pos.le D.F.field s x).adjoint.comp
        (extendPath D.T D.T_pos.le D.F.field s x) := by
    funext s
    exact inverseMetricCoefficient_apply D (projIcc 0 D.T D.T_pos.le s) x
  have hderivative : extendPath D.T D.T_pos.le (inverseMetricTimeCoefficient D).path t x =
      (extendPath D.T D.T_pos.le D.F₁.field t x).adjoint.comp
          (extendPath D.T D.T_pos.le D.F.field t x) +
        (extendPath D.T D.T_pos.le D.F.field t x).adjoint.comp
          (extendPath D.T D.T_pos.le D.F₁.field t x) :=
    inverseMetricTimeCoefficient_apply D (projIcc 0 D.T D.T_pos.le t) x
  rw [hvalue,hderivative]
  exact h


-- @@ L93-93 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L95-98 verbatim
/-- Inverse metric derivative path, given by `fullPathMap P (inverseMetricTimeCoefficient
D).path`. -/
def inverseMetricDerivativePath : C(Icc (0 : ℝ) D.T,LiftL2 P →L[ℝ] LiftL2 P) :=
  fullPathMap P (inverseMetricTimeCoefficient D).path


-- @@ L100-105 verbatim
theorem inverseMetric_operator_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) :
    HasDerivWithinAt (extendPath D.T D.T_pos.le
      (fullPathMap P (inverseMetricCoefficient D).path))
      (inverseMetricDerivativePath D P t) (Icc (0 : ℝ) D.T) t :=
  fullPath_hasDerivWithinAt P D.T D.T_pos.le (inverseMetricCoefficient D).path
    (inverseMetricTimeCoefficient D).path (inverseMetric_field_hasDerivWithinAt D) t


-- @@ L107-113 verbatim
theorem inverseMetricDerivativePath_norm (t : Icc (0 : ℝ) D.T) :
    ‖inverseMetricDerivativePath D P t‖ ≤ ‖(inverseMetricTimeCoefficient D).path‖ := by
  exact ((fullOperatorMap (E := Space) (F := Space) P).le_opNorm ((inverseMetricTimeCoefficient
      D).path t)).trans
    ((mul_le_mul_of_nonneg_right (fullOperatorMap_norm (E := Space) (F := Space) P)
      (norm_nonneg ((inverseMetricTimeCoefficient D).path t))).trans
        (by simpa only [one_mul] using (inverseMetricTimeCoefficient D).path.norm_coe_le_norm t))


-- @@ L115-115 verbatim
end EulerPacketCorrectionCoefficients


-- @@ L117-117 verbatim
end

-- @@ L118-118 verbatim
end


-- @@ L120-120 verbatim
end


-- @@ L122-122 verbatim
@[expose] public section


-- @@ L124-124 verbatim
noncomputable section


-- @@ L126-126 verbatim
namespace EulerPacketCorrectionCoefficients


-- @@ L128-131 verbatim
open Set EulerSmoothLimit EulerPacketCylinderField EulerAllOrderCorrectionData
  EulerCorrectionEnergyData EulerRegularizedMetricPaths EulerVolterraConvolution
  EulerLpCylinderRectangular EulerMeanCoefficients EulerLiftedGradientSpace
  EulerPacketProfileRecursion

-- @@ L132-132 verbatim
open scoped BoundedContinuousFunction


-- @@ L134-137 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricBudget1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L138-141 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCorrectionMetricBudget2 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance

-- @@ L142-145 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricBudget3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)
    := inferInstance

-- @@ L146-149 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCorrectionMetricBudget4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance


-- @@ L151-152 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]


-- @@ L154-159 verbatim
theorem inverseMetric_operatorPath_eq :
    metricOperatorPath P D.T (inverseMetricTower D P).coefficient
      (inverseMetricTower_continuous D P) = fullPathMap P (inverseMetricCoefficient D).path := by
  apply ContinuousMap.ext
  intro t
  exact MatrixCoefficient.toCoefficientTower_operator P (inverseMetricCoefficient D) t


-- @@ L161-169 verbatim
theorem inverseMetric_operator_hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 D.T) :
    HasDerivAt (extendPath D.T D.T_pos.le
      (metricOperatorPath P D.T (inverseMetricTower D P).coefficient
        (inverseMetricTower_continuous D P)))
      (extendPath D.T D.T_pos.le (inverseMetricDerivativePath D P) t) t := by
  rw [inverseMetric_operatorPath_eq]
  have h := (inverseMetric_operator_hasDerivWithinAt D P
    ⟨t,⟨ht.1.le,ht.2.le⟩⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  simpa only [extendPath,projIcc_of_mem D.T_pos.le ⟨ht.1.le,ht.2.le⟩] using h


-- @@ L171-172 verbatim
/-- Inverse metric bound, given by `‖(inverseMetricCoefficient D).path‖`. -/
def inverseMetricBound : ℝ := ‖(inverseMetricCoefficient D).path‖


-- @@ L174-177 verbatim
/-- Inverse metric first bound, given by `‖iteratedFDeriv ℝ 1 (translateCoefficientPath
(inverseMetricCoefficient D).path) 0‖`. -/
def inverseMetricFirstBound : ℝ :=
  ‖iteratedFDeriv ℝ 1 (translateCoefficientPath (inverseMetricCoefficient D).path) 0‖


-- @@ L179-180 verbatim
/-- Inverse metric time bound, given by `‖(inverseMetricTimeCoefficient D).path‖`. -/
def inverseMetricTimeBound : ℝ := ‖(inverseMetricTimeCoefficient D).path‖


-- @@ L182-196 verbatim
theorem inverseMetricBound_le : inverseMetricBound D ≤ ‖D.F.field‖^2 := by
  apply (ContinuousMap.norm_le _ (sq_nonneg ‖D.F.field‖)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (sq_nonneg ‖D.F.field‖)).2
  intro x
  rw [inverseMetricCoefficient_apply]
  have hF : ‖D.F.field t x‖ ≤ ‖D.F.field‖ :=
    ((D.F.field t).norm_coe_le_norm x).trans (D.F.field.norm_coe_le_norm t)
  calc
    _ ≤ ‖(D.F.field t x).adjoint‖*‖D.F.field t x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖D.F.field t x‖*‖D.F.field t x‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ ‖D.F.field‖*‖D.F.field‖ := mul_le_mul hF hF (norm_nonneg _) (norm_nonneg _)
    _ = _ := (pow_two _).symm


-- @@ L198-220 verbatim
theorem inverseMetricTimeBound_le :
    inverseMetricTimeBound D ≤ 2*‖D.F.field‖*‖D.F₁.field‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro x
  rw [inverseMetricTimeCoefficient_apply]
  have hF : ‖D.F.field t x‖ ≤ ‖D.F.field‖ :=
    ((D.F.field t).norm_coe_le_norm x).trans (D.F.field.norm_coe_le_norm t)
  have hF₁ : ‖D.F₁.field t x‖ ≤ ‖D.F₁.field‖ :=
    ((D.F₁.field t).norm_coe_le_norm x).trans (D.F₁.field.norm_coe_le_norm t)
  calc
    _ ≤ ‖(D.F₁.field t x).adjoint.comp (D.F.field t x)‖ +
        ‖(D.F.field t x).adjoint.comp (D.F₁.field t x)‖ := norm_add_le _ _
    _ ≤ ‖(D.F₁.field t x).adjoint‖*‖D.F.field t x‖ +
        ‖(D.F.field t x).adjoint‖*‖D.F₁.field t x‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ = ‖D.F₁.field t x‖*‖D.F.field t x‖ + ‖D.F.field t x‖*‖D.F₁.field t x‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map,ContinuousLinearMap.adjoint.norm_map]
    _ ≤ ‖D.F₁.field‖*‖D.F.field‖ + ‖D.F.field‖*‖D.F₁.field‖ :=
      add_le_add (mul_le_mul hF₁ hF (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul hF hF₁ (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring


-- @@ L222-244 verbatim
/-- The actual source inverse metric supplies every field of the metric
budget at every finite Sobolev order. -/
def sourceMetricBudget (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    MetricBudget P D.T D.T_pos.le ((correctionData D P κ hκ Z G).atOrder P (q+1)) where
  metric := (inverseMetricTower D P).coefficient
  continuous := inverseMetricTower_continuous D P
  derivative := inverseMetricDerivativePath D P
  hasDeriv := inverseMetric_operator_hasDerivAt D P
  c := D.inverseBound⁻¹
  c_pos := inv_pos.mpr D.inverseBound_pos
  symmetric t x v w := inverseMetric_symmetric D t x.1 v w
  coercive t x v := inverseMetric_coercive D t x.1 v
  inverse t x v := inverseMetricTower_inverse D P t x v
  bound := inverseMetricBound D
  first := inverseMetricFirstBound D
  time := inverseMetricTimeBound D
  bound_nonneg := norm_nonneg _
  first_nonneg := norm_nonneg _
  time_nonneg := norm_nonneg _
  bound_le t := (inverseMetricCoefficient D).path.norm_coe_le_norm t
  first_le _ := le_rfl
  time_le t := inverseMetricDerivativePath_norm D P t


-- @@ L246-252 verbatim
/-- Source metric budget of fields, given by `sourceMetricBudget D P κ hκ Z.toFieldTower
G.toFieldTower q`. -/
def sourceMetricBudgetOfFields (κ : ℝ) (hκ : |κ| ≤ 1)
    {z r : VectorField} (Z : Field P D.T z) (G : Field P D.T r) (q : ℕ) :
    MetricBudget P D.T D.T_pos.le
      ((correctionDataOfFields D P κ hκ Z G).atOrder P (q+1)) :=
  sourceMetricBudget D P κ hκ Z.toFieldTower G.toFieldTower q


-- @@ L254-256 verbatim
@[simp] theorem sourceMetricBudget_metric (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).metric = (inverseMetricTower D P).coefficient := rfl


-- @@ L258-260 verbatim
@[simp] theorem sourceMetricBudget_derivative (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).derivative = inverseMetricDerivativePath D P := rfl


-- @@ L262-264 verbatim
@[simp] theorem sourceMetricBudget_c (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).c = D.inverseBound⁻¹ := rfl


-- @@ L266-269 verbatim
theorem sourceMetricBudget_bound_le (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).bound ≤ ‖D.F.field‖^2 :=
  inverseMetricBound_le D


-- @@ L271-274 verbatim
theorem sourceMetricBudget_time_le (κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    (sourceMetricBudget D P κ hκ Z G q).time ≤ 2*‖D.F.field‖*‖D.F₁.field‖ :=
  inverseMetricTimeBound_le D


-- @@ L276-276 verbatim
end EulerPacketCorrectionCoefficients
