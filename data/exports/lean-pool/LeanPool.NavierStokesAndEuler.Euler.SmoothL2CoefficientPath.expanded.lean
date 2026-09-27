/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSobolevBoundedField
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets


-- @@ L14-20 verbatim
/-!
# Actual bounded smooth coefficient paths from smooth L² jets

Finite-dimensional Sobolev evaluation supplies the uniform norm at every
spatial order. The resulting coefficient path contains the original field
and its actual derivative tensors; no bounded-derivative hypothesis is added.
-/


-- @@ L22-22 verbatim
section


-- @@ L24-24 verbatim
/-! Every actual spatial derivative tensor remains a smooth L² field. -/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace EulerLpTranslation.SmoothL2Field


-- @@ L32-32 verbatim
open MeasureTheory ContinuousLinearMap EulerSmoothLimit

-- @@ L33-33 verbatim
open scoped ContDiff


-- @@ L35-35 verbatim
universe u v


-- @@ L37-50 verbatim
/-- Jet field auxiliary, constructed using `Nat.rec`. -/
def jetFieldAux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V],
      SmoothL2Field V → SmoothL2Field (Space [×n]→L[ℝ] V) :=
  Nat.rec (motive := fun n => ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V],
      SmoothL2Field V → SmoothL2Field (Space [×n]→L[ℝ] V))
    (fun V _ _ A => mapField (V := V) (W := Space [×0]→L[ℝ] V)
      (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
          A)
    (fun n ih V _ _ A => mapField
      (V := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (W := Space [×(n+1)]→L[ℝ] V)
      (continuousMultilinearCurryRightEquiv' ℝ n Space
          V).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (ih (Space →L[ℝ] V) A.derivative)) n


-- @@ L52-54 verbatim
/-- Jet field, given by `jetFieldAux n V A`. -/
def jetField (n : ℕ) {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) : SmoothL2Field (Space [×n]→L[ℝ] V) := jetFieldAux n V A


-- @@ L56-60 verbatim
@[simp] theorem jetField_zero {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) :
    jetField 0 A = mapField (V := V) (W := Space [×0]→L[ℝ] V)
      (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
          A := rfl


-- @@ L62-68 verbatim
@[simp] theorem jetField_succ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) (n : ℕ) :
    jetField (n+1) A = mapField
      (V := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (W := Space [×(n+1)]→L[ℝ] V)
      (continuousMultilinearCurryRightEquiv' ℝ n Space
          V).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (jetField n A.derivative) := rfl


-- @@ L70-84 verbatim
private theorem jetField_field_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothL2Field V) (x : Space),
      (jetField n A).field x = iteratedFDeriv ℝ n A.field x := by
  induction n with
  | zero =>
    intro V _ _ A x
    change (continuousMultilinearCurryFin0 ℝ Space V).symm (A.field x) = _
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  | succ n ih =>
    intro V _ _ A x
    change (continuousMultilinearCurryRightEquiv' ℝ n Space V).symm
      ((jetField n A.derivative).field x) = _
    rw [ih (Space →L[ℝ] V) A.derivative x, iteratedFDeriv_succ_eq_comp_right]
    rfl


-- @@ L86-89 verbatim
@[simp] theorem jetField_field {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) (n : ℕ) (x : Space) :
    (jetField n A).field x = iteratedFDeriv ℝ n A.field x :=
  jetField_field_aux n V A x


-- @@ L91-95 verbatim
theorem jetField_toLp {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) (n : ℕ) : (jetField n A).toLp = A.jetLp n := by
  apply Lp.ext
  filter_upwards [(jetField n A).toLp_ae, A.jetLp_ae n] with x h₁ h₂
  exact h₁.trans ((jetField_field A n x).trans h₂.symm)


-- @@ L97-97 verbatim
variable {K : Type v} [TopologicalSpace K]


-- @@ L99-134 verbatim
private theorem continuous_jetField_jet_aux (n : ℕ) :
    ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : K → SmoothL2Field V),
      (∀ k, Continuous (fun t => (A t).jetLp k)) →
      ∀ k, Continuous (fun t => (jetField n (A t)).jetLp k) := by
  induction n with
  | zero =>
    intro V _ _ A hA k
    have he : (fun t => (jetField 0 (A t)).jetLp k) =
        (fun t => (mapField (V := V) (W := Space [×0]→L[ℝ] V)
          (continuousMultilinearCurryFin0 ℝ Space
              V).symm.toContinuousLinearEquiv.toContinuousLinearMap
          (A t)).jetLp k) :=
      funext fun t => congrArg (fun F => F.jetLp k) (jetField_zero (A t))
    rw [he]
    exact continuous_jetLp_mapField (V := V) (W := Space [×0]→L[ℝ] V)
      (continuousMultilinearCurryFin0 ℝ Space V).symm.toContinuousLinearEquiv.toContinuousLinearMap
          A hA k
  | succ n ih =>
    intro V _ _ A hA k
    have hd : ∀ j, Continuous (fun t => (A t).derivative.jetLp j) :=
      continuous_jetLp_derivative A hA
    have hr : ∀ j, Continuous (fun t => (jetField n (A t).derivative).jetLp j) :=
      ih (Space →L[ℝ] V) (fun t => (A t).derivative) hd
    have he : (fun t => (jetField (n+1) (A t)).jetLp k) =
        (fun t => (mapField
          (V := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (W := Space [×(n+1)]→L[ℝ] V)
          (continuousMultilinearCurryRightEquiv' ℝ n Space
              V).symm.toContinuousLinearEquiv.toContinuousLinearMap
          (jetField n (A t).derivative)).jetLp k) :=
      funext fun t => congrArg (fun F => F.jetLp k) (jetField_succ (A t) n)
    rw [he]
    apply continuous_jetLp_mapField
      (V := Space [×n]→L[ℝ] (Space →L[ℝ] V)) (W := Space [×(n+1)]→L[ℝ] V)
      (continuousMultilinearCurryRightEquiv' ℝ n Space
          V).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (fun t => jetField n (A t).derivative) hr


-- @@ L136-139 verbatim
theorem continuous_jetField_jet {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : K → SmoothL2Field V) (hA : ∀ k, Continuous (fun t => (A t).jetLp k)) (n k : ℕ) :
    Continuous (fun t => (jetField n (A t)).jetLp k) :=
  continuous_jetField_jet_aux n V A hA k


-- @@ L141-141 verbatim
end EulerLpTranslation.SmoothL2Field


-- @@ L143-143 verbatim
end

-- @@ L144-144 verbatim
end


-- @@ L146-146 verbatim
end


-- @@ L148-148 verbatim
@[expose] public section


-- @@ L150-150 verbatim
noncomputable section


-- @@ L152-152 verbatim
namespace EulerMeanSobolevBoundedField


-- @@ L154-155 verbatim
open MeasureTheory EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerLpTranslation.SmoothL2Field

-- @@ L156-156 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L158-158 verbatim
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]


-- @@ L160-163 verbatim
local instance tensorFiniteDimensional (n : ℕ) : FiniteDimensional ℝ (Space [×n]→L[ℝ] V) := by
  let J : (Space [×n]→L[ℝ] V) →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => Space) V :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective


-- @@ L165-165 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L167-179 verbatim
/-- The actual raw L² family as a uniformly smooth bounded coefficient path. -/
def coefficientPath (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) : SmoothCoefficientPath K V where
  field := ⟨fun t => finiteField (A t), continuous_finiteField A hA⟩
  smooth t := by
    change ContDiff ℝ ∞ (fun x => finiteField (A t) x)
    simpa only [finiteField_apply] using (A t).smooth
  jet n := ⟨fun t => finiteField (jetField n (A t)),
    continuous_finiteField (fun t => jetField n (A t)) (continuous_jetField_jet A hA n)⟩
  jet_eq n t x := by
    change finiteField (jetField n (A t)) x =
      iteratedFDeriv ℝ n (fun y => finiteField (A t) y) x
    simp only [finiteField_apply, jetField_field]


-- @@ L181-183 verbatim
@[simp] theorem coefficientPath_apply (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (t : K) (x : Space) :
    (coefficientPath A hA).field t x = (A t).field x := finiteField_apply _ _


-- @@ L185-185 verbatim
end EulerMeanSobolevBoundedField
