/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular


-- @@ L11-11 verbatim
/-! Actual angular averaging on the cylinder, including its supported spaces. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerCylinderAngleAverage


-- @@ L20-22 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerLpSupportedSubspace EulerMeanCoefficients

-- @@ L23-23 verbatim
open scoped BoundedContinuousFunction


-- @@ L25-25 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L27-27 verbatim
section Average


-- @@ L29-29 verbatim
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]


-- @@ L31-33 verbatim
/-- Angle curve, given by `translate P (0,s) u`. -/
def angleCurve (u : CylinderL2 P V) (s : ℝ) : CylinderL2 P V :=
  translate P (0,s) u


-- @@ L35-37 verbatim
omit [CompleteSpace V] in
theorem angleCurve_continuous (u : CylinderL2 P V) : Continuous (angleCurve P u) :=
  (translate_continuous P u).comp (continuous_const.prodMk continuous_id)


-- @@ L39-41 verbatim
/-- Average integral, given by `P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P u s)`. -/
def averageIntegral (u : CylinderL2 P V) : CylinderL2 P V :=
  P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P u s)


-- @@ L43-54 verbatim
omit [CompleteSpace V] in
theorem averageIntegral_add (u v : CylinderL2 P V) :
    averageIntegral P (u+v) = averageIntegral P u+averageIntegral P v := by
  have he : angleCurve P (u+v) = angleCurve P u+angleCurve P v := by
    funext s
    exact map_add (translate P (0,s)) u v
  rw [averageIntegral, he]
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add
    ((angleCurve_continuous P u).intervalIntegrable 0 P)
    ((angleCurve_continuous P v).intervalIntegrable 0 P), smul_add]
  rfl


-- @@ L56-65 verbatim
omit [CompleteSpace V] in
theorem averageIntegral_smul (r : ℝ) (u : CylinderL2 P V) :
    averageIntegral P (r • u) = r • averageIntegral P u := by
  have he : angleCurve P (r • u) = r • angleCurve P u := by
    funext s
    exact map_smul (translate P (0,s)) r u
  rw [averageIntegral, he]
  simp only [Pi.smul_apply]
  rw [intervalIntegral.integral_smul, smul_comm P⁻¹ r]
  rfl


-- @@ L67-79 verbatim
omit [CompleteSpace V] in
theorem averageIntegral_norm (u : CylinderL2 P V) : ‖averageIntegral P u‖ ≤ ‖u‖ := by
  have hP : 0 < P := Fact.out
  have hb : ‖∫ s in (0 : ℝ)..P, angleCurve P u s‖ ≤ ‖u‖*P := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := P) (f := angleCurve P u) (C := ‖u‖) (fun s _ => by
        exact le_of_eq ((translate P (0,s)).norm_map u))
    simpa only [sub_zero, abs_of_pos hP] using h
  change ‖P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P u s)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hP)]
  calc
    _ ≤ P⁻¹*(‖u‖*P) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hP.le)
    _ = ‖u‖ := by field_simp


-- @@ L81-85 verbatim
/-- Average linear, bundling `toFun`, `map_add`, `map_smul`. -/
def averageLinear : CylinderL2 P V →ₗ[ℝ] CylinderL2 P V where
  toFun := averageIntegral P
  map_add' := averageIntegral_add P
  map_smul' := averageIntegral_smul P


-- @@ L87-91 verbatim
/-- The Bochner average of genuine angular translations. -/
def average : CylinderL2 P V →L[ℝ] CylinderL2 P V :=
  (averageLinear P).mkContinuous 1 (fun u => by
    change ‖averageIntegral P u‖ ≤ (1 : ℝ)*‖u‖
    simpa only [one_mul] using averageIntegral_norm P u)


-- @@ L93-95 verbatim
omit [CompleteSpace V] in
@[simp] theorem average_apply (u : CylinderL2 P V) :
    average P u = averageIntegral P u := rfl


-- @@ L97-101 verbatim
omit [CompleteSpace V] in
theorem average_norm : ‖average (V := V) P‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one (fun u => by
    change ‖averageIntegral P u‖ ≤ (1 : ℝ)*‖u‖
    simpa only [one_mul] using averageIntegral_norm P u)


-- @@ L103-115 verbatim
theorem average_translation (a : LiftTangent) (u : CylinderL2 P V) :
    average P (translate P a u) = translate P a (average P u) := by
  change P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P (translate P a u) s) =
    translate P a (P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P u s))
  rw [map_smul]
  change P⁻¹ • _ = P⁻¹ • (translate P a).toContinuousLinearMap _
  rw [← (translate P a).toContinuousLinearMap.intervalIntegral_comp_comm
    ((angleCurve_continuous P u).intervalIntegrable 0 P)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change translate P (0,s) (translate P a u) = translate P a (translate P (0,s) u)
  rw [translate_add, translate_add, add_comm (0,s) a]


-- @@ L117-117 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L119-121 verbatim
/-- Path average, given by `(average P).compLeftContinuous ℝ K`. -/
def pathAverage : C(K,CylinderL2 P V) →L[ℝ] C(K,CylinderL2 P V) :=
  (average P).compLeftContinuous ℝ K


-- @@ L123-125 verbatim
omit [CompactSpace K] [CompleteSpace V] in
@[simp] theorem pathAverage_apply (u : C(K, CylinderL2 P V)) (t : K) :
    pathAverage P u t = average P (u t) := rfl


-- @@ L127-134 verbatim
omit [CompleteSpace V] in
theorem pathAverage_norm : ‖pathAverage (K := K) (V := V) P‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  exact (averageIntegral_norm P (u t)).trans (u.norm_coe_le_norm t)


-- @@ L136-141 verbatim
omit [CompactSpace K] in
theorem pathAverage_translation (a : LiftTangent) (u : C(K, CylinderL2 P V)) :
    pathAverage P (pathTranslate P a u) = pathTranslate P a (pathAverage P u) := by
  apply ContinuousMap.ext
  intro t
  exact average_translation P a (u t)


-- @@ L143-143 verbatim
end Average


-- @@ L145-145 verbatim
section Intertwining


-- @@ L147-148 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


-- @@ L150-161 verbatim
/-- Every actual angular intertwiner commutes with the constructed average. -/
theorem average_intertwines (L : CylinderL2 P E →L[ℝ] CylinderL2 P F)
    (hL : ∀ s u, L (translate P (0, s) u) = translate P (0, s) (L u))
    (u : CylinderL2 P E) : average P (L u) = L (average P u) := by
  change P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P (L u) s) =
    L (P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P u s))
  rw [map_smul, ← L.intervalIntegral_comp_comm
    ((angleCurve_continuous P u).intervalIntegrable 0 P)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact (hL s u).symm


-- @@ L163-163 verbatim
end Intertwining


-- @@ L165-165 verbatim
section Coefficients


-- @@ L167-168 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]


-- @@ L170-175 verbatim
/-- Spatial rectangular coefficients preserve angular means exactly. -/
theorem average_fullOperator (A : Space →ᵇ E →L[ℝ] F) (u : CylinderL2 P E) :
    average P (fullOperatorMap P A u) = fullOperatorMap P A (average P u) := by
  apply average_intertwines P
  intro s v
  simpa only [Prod.fst, translated_zero] using fullOperator_translation P (0,s) A v


-- @@ L177-177 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L179-184 verbatim
theorem pathAverage_fullMultiplier (A : C(K, Space →ᵇ E →L[ℝ] F))
    (u : C(K, CylinderL2 P E)) :
    pathAverage P (fullMultiplierMap P A u) = fullMultiplierMap P A (pathAverage P u) := by
  apply ContinuousMap.ext
  intro t
  exact average_fullOperator P (A t) (u t)


-- @@ L186-186 verbatim
end Coefficients


-- @@ L188-188 verbatim
section Supported


-- @@ L190-191 verbatim
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S)


-- @@ L193-211 verbatim
/-- Angular averaging preserves the actual spatial support subspace. -/
theorem average_mem (u : Supported P V S hS) :
    average P (u : CylinderL2 P V) ∈ Supported P V S hS := by
  have hs (s : ℝ) : translate P (0,s) (u : CylinderL2 P V) ∈ Supported P V S hS := by
    apply translate_mem P (0,s) S S hS hS _ u
    intro x hx
    change x+(0 : Space) ∈ S at hx
    simpa only [add_zero] using hx
  let f : ℝ → Supported P V S hS := fun s => ⟨translate P (0,s) (u : CylinderL2 P V), hs s⟩
  have hf : Continuous f := Continuous.subtype_mk
    (angleCurve_continuous P (u : CylinderL2 P V)) _
  let v : Supported P V S hS := P⁻¹ • (∫ s in (0 : ℝ)..P, f s)
  have he : (v : CylinderL2 P V) = average P (u : CylinderL2 P V) := by
    change (Supported P V S hS).subtypeL (P⁻¹ • (∫ s in (0 : ℝ)..P, f s)) = _
    rw [map_smul, ← (Supported P V S hS).subtypeL.intervalIntegral_comp_comm
      (hf.intervalIntegrable 0 P)]
    rfl
  rw [← he]
  exact v.property


-- @@ L213-217 verbatim
/-- Supported average, given by `((average P).comp (Supported P V S hS).subtypeL).codRestrict
(Supported P V S hS) (average_mem P S hS)`. -/
def supportedAverage : Supported P V S hS →L[ℝ] Supported P V S hS :=
  ((average P).comp (Supported P V S hS).subtypeL).codRestrict
    (Supported P V S hS) (average_mem P S hS)


-- @@ L219-220 verbatim
@[simp] theorem supportedAverage_coe (u : Supported P V S hS) :
    (supportedAverage P S hS u : CylinderL2 P V) = average P (u : CylinderL2 P V) := rfl


-- @@ L222-226 verbatim
theorem supportedAverage_norm : ‖supportedAverage (V := V) P S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro u
  change ‖averageIntegral P (u : CylinderL2 P V)‖ ≤ (1 : ℝ)*‖(u : CylinderL2 P V)‖
  simpa only [one_mul] using averageIntegral_norm P (u : CylinderL2 P V)


-- @@ L228-228 verbatim
end Supported


-- @@ L230-230 verbatim
end EulerCylinderAngleAverage
