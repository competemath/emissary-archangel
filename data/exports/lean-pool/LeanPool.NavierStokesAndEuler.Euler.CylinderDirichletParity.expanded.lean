/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletNaturality


-- @@ L13-19 verbatim
/-!
# Joint parity of the constructed cylinder history

Even coefficient fields commute with actual spatial-angular reflection.
The genuine coercive inverse therefore preserves odd forcing, including
its continuous velocity and acceleration representatives.
-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace EulerCylinderFieldReflection


-- @@ L28-28 verbatim
open ContinuousLinearMap InnerProductSpace EulerLpCylinderTranslation


-- @@ L30-31 verbatim
variable (P : ℝ) [Fact (0 < P)] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]


-- @@ L33-42 verbatim
theorem reflection_adjoint : (reflection (V := V) P).toContinuousLinearMap.adjoint =
    (reflection P).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left]
  change ⟪u,reflection P v⟫_ℝ = ⟪reflection P u,v⟫_ℝ
  simpa only [reflection_involutive] using
    (reflection (V := V) P).inner_map_map (reflection P u) v


-- @@ L44-44 verbatim
end EulerCylinderFieldReflection


-- @@ L46-46 verbatim
namespace EulerCylinderDirichlet.Coefficients


-- @@ L48-50 verbatim
open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp EulerTimeLpBoundedMap
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerCylinderFieldReflection
  EulerTransverseGramInverse


-- @@ L52-58 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)
  (hQ : ∀ t x, D.Q t (-x) = D.Q t x)
  (hQ₁ : ∀ t x, D.Q₁ t (-x) = D.Q₁ t x)
  (hH : ∀ t x, D.H t (-x) = D.H t x)


-- @@ L60-60 verbatim
include hQ hQ₁ hH


-- @@ L62-75 verbatim
theorem continuousVelocity_reflection (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.velocityPath P (pathLp T D.time_pos.le (pathReflection P f)) t =
      reflection P (D.velocityPath P (pathLp T D.time_pos.le f) t) := by
  apply D.continuousVelocity_intertwines P D
    (reflection P).toContinuousLinearMap (reflection P).toContinuousLinearMap
    (fun s u => (reflection_fullOperator P (D.Q s) (hQ s) u).symm)
    (fun s u => (reflection_fullOperator P (D.Q₁ s) (hQ₁ s) u).symm)
    _ _ (fun s u => (reflection_fullOperator P (D.H s) (hH s) u).symm) f t
  · intro s u
    rw [reflection_adjoint,reflection_adjoint]
    exact (reflection_fullOperator P (D.Q s) (hQ s) u).symm
  · intro s u
    rw [reflection_adjoint,reflection_adjoint]
    exact (reflection_fullOperator P (D.Q₁ s) (hQ₁ s) u).symm


-- @@ L77-89 verbatim
theorem accelerationPath_reflection (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.accelerationPath P (pathReflection P f) t = reflection P (D.accelerationPath P f t) := by
  apply D.accelerationPath_intertwines P D
    (reflection P).toContinuousLinearMap (reflection P).toContinuousLinearMap
    (fun s u => (reflection_fullOperator P (D.Q s) (hQ s) u).symm)
    (fun s u => (reflection_fullOperator P (D.Q₁ s) (hQ₁ s) u).symm)
    _ _ (fun s u => (reflection_fullOperator P (D.H s) (hH s) u).symm) f t
  · intro s u
    rw [reflection_adjoint,reflection_adjoint]
    exact (reflection_fullOperator P (D.Q s) (hQ s) u).symm
  · intro s u
    rw [reflection_adjoint,reflection_adjoint]
    exact (reflection_fullOperator P (D.Q₁ s) (hQ₁ s) u).symm


-- @@ L91-101 verbatim
omit hQ hQ₁ hH in
theorem accelerationPath_neg (f : C(Icc (0 : ℝ) T, CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    D.accelerationPath P (-f) t = -(D.accelerationPath P f t) := by
  have hn : pathLp T D.time_pos.le (-f) = -(pathLp T D.time_pos.le f) :=
    map_neg (pathLpOperator T D.time_pos.le) f
  change gramInverse (D.frame P t) D.lower D.lower_pos (D.frame_lower P t)
    ((D.frame P t).adjoint (-f t-(2 : ℝ) • D.frameDerivative P t
      (D.velocityPath P (pathLp T D.time_pos.le (-f)) t))) = _
  rw [hn,map_neg,ContinuousMap.neg_apply,map_neg,smul_neg,neg_sub_neg,← neg_sub]
  simp only [map_neg]
  rfl


-- @@ L103-111 verbatim
theorem velocityPath_odd (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ∀ t, reflection P (f t) = -f t) (t : Icc (0 : ℝ) T) :
    reflection P (D.velocityPath P (pathLp T D.time_pos.le f) t) =
      -(D.velocityPath P (pathLp T D.time_pos.le f) t) := by
  have he : pathReflection P f = -f := ContinuousMap.ext hf
  rw [← D.continuousVelocity_reflection P hQ hQ₁ hH f t,he]
  have hn : pathLp T D.time_pos.le (-f) = -(pathLp T D.time_pos.le f) :=
    map_neg (pathLpOperator T D.time_pos.le) f
  rw [hn,map_neg,ContinuousMap.neg_apply]


-- @@ L113-117 verbatim
theorem accelerationPath_odd (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ∀ t, reflection P (f t) = -f t) (t : Icc (0 : ℝ) T) :
    reflection P (D.accelerationPath P f t) = -(D.accelerationPath P f t) := by
  have he : pathReflection P f = -f := ContinuousMap.ext hf
  rw [← D.accelerationPath_reflection P hQ hQ₁ hH f t,he,D.accelerationPath_neg P f t]


-- @@ L119-125 verbatim
theorem physicalVelocity_odd (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ∀ t, reflection P (f t) = -f t) (t : Icc (0 : ℝ) T) :
    reflection P (D.physicalVelocity P f t) = -(D.physicalVelocity P f t) := by
  change reflection P (fullOperatorMap P (D.Q t) (D.velocityPath P (pathLp T D.time_pos.le f) t)) =
      _
  rw [reflection_fullOperator P (D.Q t) (hQ t),D.velocityPath_odd P hQ hQ₁ hH f hf t,map_neg]
  rfl


-- @@ L127-134 verbatim
theorem physicalDerivative_odd (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ∀ t, reflection P (f t) = -f t) (t : Icc (0 : ℝ) T) :
    reflection P (D.physicalDerivative P f t) = -(D.physicalDerivative P f t) := by
  change reflection P (fullOperatorMap P (D.Q₁ t) (D.velocityPath P (pathLp T D.time_pos.le f) t) +
    fullOperatorMap P (D.Q t) (D.accelerationPath P f t)) = _
  rw [map_add,reflection_fullOperator P (D.Q₁ t) (hQ₁ t),reflection_fullOperator P (D.Q t) (hQ t),
    D.velocityPath_odd P hQ hQ₁ hH f hf t,D.accelerationPath_odd P hQ hQ₁ hH f hf t,map_neg,map_neg]
  exact (neg_add _ _).symm


-- @@ L136-136 verbatim
end EulerCylinderDirichlet.Coefficients
