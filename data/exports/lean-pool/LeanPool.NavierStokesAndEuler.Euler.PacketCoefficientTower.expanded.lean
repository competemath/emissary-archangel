/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathSmooth
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDerivatives
public import LeanPool.NavierStokesAndEuler.Euler.SobolevCoefficientPressure


-- @@ L14-15 verbatim
/-! Actual packet matrix coefficients provide the complete coefficient
towers required by the all-order nonlinear correction construction. -/


-- @@ L17-17 verbatim
section


-- @@ L19-20 verbatim
/-! The constructed coefficient jets act continuously in operator norm
on every finite cylinder Sobolev space. -/


-- @@ L22-22 verbatim
section


-- @@ L24-25 verbatim
/-! Operator-norm continuity into a finite Sobolev space is equivalent
to continuity of all its actual derivative-coordinate operators. -/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace EulerCylinderSobolevSpace


-- @@ L33-33 verbatim
open EulerLiftedGradientSpace


-- @@ L35-36 verbatim
variable (P : ℝ) [Fact (0 < P)] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L38-40 verbatim
/-- Word composition, defined pointwise by `(wordOperator P w).comp A`. -/
def wordComposition (q : ℕ) (A : E →L[ℝ] SobolevSpace P q) :
    SobolevWord q → E →L[ℝ] LiftL2 P := fun w => (wordOperator P w).comp A


-- @@ L42-56 verbatim
theorem norm_wordComposition (q : ℕ) (A : E →L[ℝ] SobolevSpace P q) :
    ‖wordComposition P q A‖ = ‖A‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr
    intro w
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro u
    exact (word_norm_le P (A u) w).trans (A.le_opNorm u)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    change ‖(A u).val‖ ≤ ‖wordComposition P q A‖*‖u‖
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg u))).mpr
    intro w
    exact ((wordComposition P q A w).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_le_pi_norm (wordComposition P q A) w) (norm_nonneg u))


-- @@ L58-68 verbatim
theorem wordComposition_isometry (q : ℕ) :
    Isometry (wordComposition (E := E) P q) := by
  apply Isometry.of_dist_eq
  intro A B
  rw [dist_eq_norm,dist_eq_norm]
  have he : wordComposition P q A-wordComposition P q B = wordComposition P q (A-B) := by
    funext w
    apply ContinuousLinearMap.ext
    intro u
    rfl
  rw [he,norm_wordComposition]


-- @@ L70-74 verbatim
theorem continuous_of_wordCompositions {K : Type*} [TopologicalSpace K]
    (q : ℕ) (A : K → E →L[ℝ] SobolevSpace P q)
    (hA : ∀ w : SobolevWord q, Continuous (fun t => (wordOperator P w).comp (A t))) :
    Continuous A :=
  (wordComposition_isometry (E := E) P q).comp_continuous_iff.mp (continuous_pi hA)


-- @@ L76-85 verbatim
theorem continuous_of_valueComposition {K : Type*} [TopologicalSpace K]
    (A : K → E →L[ℝ] SobolevSpace P 0)
    (hA : Continuous (fun t => (valueOperator P 0).comp (A t))) : Continuous A := by
  apply continuous_of_wordCompositions P 0 A
  rintro ⟨⟨n,hn⟩,w⟩
  have hn0 : n=0 := by omega
  subst n
  have hw : w=Fin.elim0 := Subsingleton.elim _ _
  subst w
  exact hA


-- @@ L87-110 verbatim
theorem continuous_of_value_and_derivatives {K : Type*} [TopologicalSpace K]
    (q : ℕ) (A : K → E →L[ℝ] SobolevSpace P (q + 1))
    (hA : Continuous (fun t => (valueOperator P (q + 1)).comp (A t)))
    (hD : ∀ i : Fin 4, Continuous (fun t => (derivativeOperator P q i).comp (A t))) :
    Continuous A := by
  apply continuous_of_wordCompositions P (q+1) A
  rintro ⟨⟨n,hn⟩,w⟩
  cases n with
  | zero =>
    have hw : w=Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact hA
  | succ n =>
    let w₀ : SobolevWord q := ⟨⟨n,by omega⟩,Fin.init w⟩
    let i : Fin 4 := w (Fin.last n)
    have he : wordOperator P ⟨⟨n+1,hn⟩,w⟩ =
        (wordOperator P w₀).comp (derivativeOperator P q i) := by
      apply ContinuousLinearMap.ext
      intro u
      change u.val ⟨⟨n+1,hn⟩,w⟩ = u.val (derivativeIndex i w₀)
      simp only [derivativeIndex,w₀,i,Fin.snoc_init_self]
    rw [he]
    simpa only [ContinuousLinearMap.comp_assoc] using
      (hD i).const_clm_comp (wordOperator P w₀)


-- @@ L112-112 verbatim
end EulerCylinderSobolevSpace


-- @@ L114-114 verbatim
end

-- @@ L115-115 verbatim
end


-- @@ L117-117 verbatim
end


-- @@ L119-119 verbatim
@[expose] public section


-- @@ L121-121 verbatim
noncomputable section


-- @@ L123-123 verbatim
namespace EulerCoefficientPath


-- @@ L125-127 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSobolevCoefficientPressure


-- @@ L129-129 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L131-131 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L133-135 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCoefficientPathSobolev1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance

-- @@ L136-138 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCoefficientPathSobolev2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

-- @@ L139-142 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCoefficientPathSobolev3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

-- @@ L143-146 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCoefficientPathSobolev4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance


-- @@ L148-150 verbatim
variable (P : ℝ) [Fact (0 < P)]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))


-- @@ L152-154 verbatim
/-- Sobolev operator, given by `coefficientSobolevOperator P (coefficientJet P A hA q t)`. -/
def sobolevOperator (q : ℕ) (t : K) : SobolevSpace P q →L[ℝ] SobolevSpace P q :=
  coefficientSobolevOperator P (coefficientJet P A hA q t)


-- @@ L156-159 verbatim
@[simp] theorem sobolevOperator_value (q : ℕ) (t : K) (u : SobolevSpace P q) :
    value P (sobolevOperator P A hA q t u) =
      (smoothCoefficient P A hA t).operator (value P u) :=
  coefficientSobolevOperator_value P (coefficientJet P A hA q t) u


-- @@ L161-166 verbatim
theorem sobolevOperator_value_comp (q : ℕ) (t : K) :
    (valueOperator P q).comp (sobolevOperator P A hA q t) =
      (smoothCoefficient P A hA t).operator.comp (valueOperator P q) := by
  apply ContinuousLinearMap.ext
  intro u
  exact sobolevOperator_value P A hA q t u


-- @@ L168-188 verbatim
theorem sobolevOperator_derivative (q : ℕ) (t : K) (i : Fin 4)
    (u : SobolevSpace P (q + 1)) :
    derivativeOperator P q i (sobolevOperator P A hA (q+1) t u) =
      sobolevOperator P A hA q t (derivativeOperator P q i u) +
      sobolevOperator P (orbitDerivativePath A (standardDirection i).1)
        (orbitDerivativePath_orbit A hA (standardDirection i).1) q t (truncateOperator P q u) := by
  apply value_injective P
  have h₁ := derivativeOperator_hasDerivAt P i (sobolevOperator P A hA (q+1) t u)
  rw [sobolevOperator_value] at h₁
  have h₂ := (smoothCoefficient P A hA t).product_hasDerivAt
    (smoothCoefficient P (orbitDerivativePath A (standardDirection i).1)
      (orbitDerivativePath_orbit A hA (standardDirection i).1) t)
    (standardDirection i) (fun x => (cylinder_fieldDerivative P A hA t (standardDirection i)
        x).symm)
    (value P u) (value P (derivativeOperator P q i u)) (derivativeOperator_hasDerivAt P i u)
  change value P (derivativeOperator P q i (sobolevOperator P A hA (q+1) t u)) =
    value P (sobolevOperator P A hA q t (derivativeOperator P q i u)) +
    value P (sobolevOperator P (orbitDerivativePath A (standardDirection i).1)
      (orbitDerivativePath_orbit A hA (standardDirection i).1) q t (truncateOperator P q u))
  simp only [sobolevOperator_value,value_truncateOperator]
  exact h₁.unique h₂


-- @@ L190-198 verbatim
theorem sobolevOperator_derivative_comp (q : ℕ) (t : K) (i : Fin 4) :
    (derivativeOperator P q i).comp (sobolevOperator P A hA (q+1) t) =
      (sobolevOperator P A hA q t).comp (derivativeOperator P q i) +
      (sobolevOperator P (orbitDerivativePath A (standardDirection i).1)
        (orbitDerivativePath_orbit A hA (standardDirection i).1) q t).comp (truncateOperator P q)
            := by
  apply ContinuousLinearMap.ext
  intro u
  exact sobolevOperator_derivative P A hA q t i u


-- @@ L200-220 verbatim
private theorem sobolevOperator_continuous_aux (q : ℕ) :
    ∀ (A : C(K, Space →ᵇ Space →L[ℝ] Space))
      (hA : ContDiff ℝ ∞ (translateCoefficientPath A)),
      Continuous (fun t => sobolevOperator P A hA q t) := by
  induction q with
  | zero =>
    intro A hA
    apply continuous_of_valueComposition P
    simp_rw [sobolevOperator_value_comp]
    exact (smoothCoefficient_operator_continuous P A hA).clm_comp_const (valueOperator P 0)
  | succ q ih =>
    intro A hA
    apply continuous_of_value_and_derivatives P q
    · simp_rw [sobolevOperator_value_comp]
      exact (smoothCoefficient_operator_continuous P A hA).clm_comp_const (valueOperator P (q+1))
    · intro i
      simp_rw [sobolevOperator_derivative_comp]
      exact ((ih A hA).clm_comp_const (derivativeOperator P q i)).add
        ((ih (orbitDerivativePath A (standardDirection i).1)
          (orbitDerivativePath_orbit A hA (standardDirection i).1)).clm_comp_const
              (truncateOperator P q))


-- @@ L222-224 verbatim
theorem sobolevOperator_continuous (q : ℕ) :
    Continuous (fun t => sobolevOperator P A hA q t) :=
  sobolevOperator_continuous_aux P q A hA


-- @@ L226-226 verbatim
end EulerCoefficientPath


-- @@ L228-228 verbatim
end

-- @@ L229-229 verbatim
end


-- @@ L231-231 verbatim
end


-- @@ L233-233 verbatim
@[expose] public section


-- @@ L235-235 verbatim
noncomputable section


-- @@ L237-237 verbatim
namespace EulerPacketCylinderField.MatrixCoefficient


-- @@ L239-241 verbatim
open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevCoefficientPressure EulerCoefficientPath EulerLpCylinderRectangular
  EulerPacketPointJets


-- @@ L243-243 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {raw : Domain → Space →L[ℝ] Space}


-- @@ L245-250 verbatim
/-- To coefficient tower, bundling `coefficient`, `jet`, `continuous`. -/
def toCoefficientTower (A : MatrixCoefficient T raw) :
    EulerAllOrderCorrectionData.CoefficientTower P T where
  coefficient := smoothCoefficient P A.path A.orbit
  jet q t := coefficientJet P A.path A.orbit q t
  continuous q := sobolevOperator_continuous P A.path A.orbit q


-- @@ L252-254 verbatim
@[simp] theorem toCoefficientTower_coefficient (A : MatrixCoefficient T raw)
    (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    ((A.toCoefficientTower P).coefficient t).coefficient x = A.path t x.1 := rfl


-- @@ L256-259 verbatim
theorem toCoefficientTower_raw (A : MatrixCoefficient T raw)
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    ((A.toCoefficientTower P).coefficient t).coefficient (x,(θ : AddCircle P)) =
      raw (t,(x,θ)) := (A.raw_eq t x θ).symm


-- @@ L261-264 verbatim
theorem toCoefficientTower_operator (A : MatrixCoefficient T raw)
    (t : Icc (0 : ℝ) T) :
    ((A.toCoefficientTower P).coefficient t).operator = fullOperatorMap P (A.path t) :=
  smoothCoefficient_operator P A.path A.orbit t


-- @@ L266-268 verbatim
theorem toCoefficientTower_operator_continuous (A : MatrixCoefficient T raw) :
    Continuous (fun t => ((A.toCoefficientTower P).coefficient t).operator) :=
  smoothCoefficient_operator_continuous P A.path A.orbit


-- @@ L270-275 verbatim
theorem toCoefficientTower_sobolev_value (A : MatrixCoefficient T raw)
    (q : ℕ) (t : Icc (0 : ℝ) T) (u : SobolevSpace P q) :
    value P (coefficientSobolevOperator P ((A.toCoefficientTower P).jet q t) u) =
      fullOperatorMap P (A.path t) (value P u) := by
  rw [coefficientSobolevOperator_value]
  exact congrArg (fun L => L (value P u)) (toCoefficientTower_operator P A t)


-- @@ L277-277 verbatim
end EulerPacketCylinderField.MatrixCoefficient
