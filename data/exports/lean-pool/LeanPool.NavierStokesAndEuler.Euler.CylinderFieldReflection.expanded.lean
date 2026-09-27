/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderReflection
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl


-- @@ L13-14 verbatim
/-! Joint reflection for arbitrary Hilbert-valued cylinder fields and their actual supported spaces.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerCylinderFieldReflection


-- @@ L23-25 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
      EulerLpSupportedSubspace

-- @@ L26-26 verbatim
open scoped BoundedContinuousFunction


-- @@ L28-28 verbatim
variable (P : ℝ) [Fact (0 < P)]


-- @@ L30-30 verbatim
section Basic


-- @@ L32-32 verbatim
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L34-38 verbatim
/-- Reflection, given by `Lp.compMeasurePreservingₗᵢ ℝ (fun x : LiftDomain P => -x)
(EulerCylinderReflection.measurePreserving_reflection P)`. -/
def reflection : CylinderL2 P V →ₗᵢ[ℝ] CylinderL2 P V :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : LiftDomain P => -x)
    (EulerCylinderReflection.measurePreserving_reflection P)


-- @@ L40-42 verbatim
theorem reflection_ae (u : CylinderL2 P V) :
    reflection P u =ᵐ[liftMeasure P] fun x => u (-x) :=
  Lp.coeFn_compMeasurePreserving u (EulerCylinderReflection.measurePreserving_reflection P)


-- @@ L44-49 verbatim
theorem reflection_involutive (u : CylinderL2 P V) : reflection P (reflection P u) = u := by
  apply Lp.ext
  filter_upwards [reflection_ae P (reflection P u),
    (EulerCylinderReflection.measurePreserving_reflection P).quasiMeasurePreserving.ae
      (reflection_ae P u)] with x h₁ h₂
  simp only [h₁,h₂,neg_neg]


-- @@ L51-58 verbatim
theorem reflection_of_representative (u : CylinderL2 P V) (f : LiftDomain P → V)
    (hf : u =ᵐ[liftMeasure P] f) (c : ℝ) (hc : ∀ x, f (-x) = c • f x) :
    reflection P u = c • u := by
  apply Lp.ext
  filter_upwards [reflection_ae P u,
    (EulerCylinderReflection.measurePreserving_reflection P).quasiMeasurePreserving.ae hf,
    Lp.coeFn_smul c u, hf] with x hr hn hs he
  rw [hr,hn,hc,hs,Pi.smul_apply,he]


-- @@ L60-71 verbatim
theorem representative_of_reflection (u : CylinderL2 P V) (f : LiftDomain P → V)
    (hf : u =ᵐ[liftMeasure P] f) (hcont : Continuous f) (c : ℝ)
    (hc : reflection P u = c • u) (x : LiftDomain P) : f (-x) = c • f x := by
  have he : (fun y => f (-y)) =ᵐ[liftMeasure P] (fun y => c • f y) := by
    filter_upwards [reflection_ae P u,
      (EulerCylinderReflection.measurePreserving_reflection P).quasiMeasurePreserving.ae hf,
      Lp.coeFn_smul c u, hf] with y hr hn hs hy
    rw [hc] at hr
    rw [hs,Pi.smul_apply,hy,hn] at hr
    exact hr.symm
  exact congrFun (Measure.eq_of_ae_eq he (hcont.comp continuous_neg) (continuous_const.smul hcont))
      x


-- @@ L73-73 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L75-77 verbatim
/-- Path reflection, given by `(reflection P).toContinuousLinearMap.compLeftContinuous ℝ K`. -/
def pathReflection : C(K,CylinderL2 P V) →L[ℝ] C(K,CylinderL2 P V) :=
  (reflection P).toContinuousLinearMap.compLeftContinuous ℝ K


-- @@ L79-81 verbatim
omit [CompactSpace K] in
@[simp] theorem pathReflection_apply (u : C(K, CylinderL2 P V)) (t : K) :
    pathReflection P u t = reflection P (u t) := rfl


-- @@ L83-83 verbatim
end Basic


-- @@ L85-85 verbatim
section Coefficients


-- @@ L87-88 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]


-- @@ L90-101 verbatim
theorem reflection_fullOperator (A : Space →ᵇ E →L[ℝ] F)
    (hA : ∀ x, A (-x) = A x) (u : CylinderL2 P E) :
    reflection P (fullOperatorMap P A u) = fullOperatorMap P A (reflection P u) := by
  apply Lp.ext
  filter_upwards [reflection_ae P (fullOperatorMap P A u),
    (EulerCylinderReflection.measurePreserving_reflection P).quasiMeasurePreserving.ae
      (EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P A) u),
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P A) (reflection P u),
    reflection_ae P u] with x hr hn hf hu
  change fullOperatorMap P A u (-x) = A (-x.1) (u (-x)) at hn
  change fullOperatorMap P A (reflection P u) x = A x.1 (reflection P u x) at hf
  rw [hr,hn,hf,hu,hA]


-- @@ L103-103 verbatim
end Coefficients


-- @@ L105-105 verbatim
section Supported


-- @@ L107-108 verbatim
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set Space) (hS : MeasurableSet S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)


-- @@ L110-122 verbatim
include hSym in
theorem reflection_mem (u : Supported P V S hS) :
    reflection P (u : CylinderL2 P V) ∈ Supported P V S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S) (spatialSet_measurable P S hS)
      _).mpr
  filter_upwards [reflection_ae P (u : CylinderL2 P V),
    (EulerCylinderReflection.measurePreserving_reflection P).quasiMeasurePreserving.ae
      ((mem_supportedSpace_ae (liftMeasure P) (spatialSet P S) (spatialSet_measurable P S hS)
        (u : CylinderL2 P V)).mp u.property)] with x hr hu hx
  rw [hr]
  apply hu
  intro hn
  exact hx ((hSym x.1).mp hn)


-- @@ L124-127 verbatim
/-- Supported reflection as an element of `Supported P V S hS →L[ℝ] Supported P V S hS`. -/
def supportedReflection : Supported P V S hS →L[ℝ] Supported P V S hS :=
  ((reflection P).toContinuousLinearMap.comp (Supported P V S hS).subtypeL).codRestrict
    (Supported P V S hS) (reflection_mem P S hS hSym)


-- @@ L129-130 verbatim
@[simp] theorem supportedReflection_coe (u : Supported P V S hS) :
    (supportedReflection P S hS hSym u : CylinderL2 P V) = reflection P (u : CylinderL2 P V) := rfl


-- @@ L132-132 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L134-137 verbatim
/-- Supported path reflection, given by `(supportedReflection P S hS hSym).compLeftContinuous ℝ
K`. -/
def supportedPathReflection : C(K,Supported P V S hS) →L[ℝ] C(K,Supported P V S hS) :=
  (supportedReflection P S hS hSym).compLeftContinuous ℝ K


-- @@ L139-141 verbatim
omit [CompactSpace K] in
@[simp] theorem supportedPathReflection_apply (u : C(K, Supported P V S hS)) (t : K) :
    supportedPathReflection P S hS hSym u t = supportedReflection P S hS hSym (u t) := rfl


-- @@ L143-143 verbatim
end Supported


-- @@ L145-145 verbatim
section SupportedCoefficients


-- @@ L147-149 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (S : Set Space) (hS : MeasurableSet S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)


-- @@ L151-156 verbatim
theorem supportedReflection_operator (A : Space →ᵇ E →L[ℝ] F)
    (hA : ∀ x, A (-x) = A x) (u : Supported P E S hS) :
    supportedReflection P S hS hSym (supportedOperatorMap P S hS A u) =
      supportedOperatorMap P S hS A (supportedReflection P S hS hSym u) := by
  apply Subtype.ext
  exact reflection_fullOperator P A hA (u : CylinderL2 P E)


-- @@ L158-158 verbatim
end SupportedCoefficients

-- @@ L159-159 verbatim
end EulerCylinderFieldReflection
