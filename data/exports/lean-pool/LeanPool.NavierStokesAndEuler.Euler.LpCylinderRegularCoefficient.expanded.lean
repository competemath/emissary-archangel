/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod


-- @@ L14-15 verbatim
/-! A genuinely smooth translated bounded-field family lifts to actual mixed cylinder coefficients.
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
namespace EulerLpCylinderCoefficients


-- @@ L24-25 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderPaths
  EulerMeanCoefficients

-- @@ L26-26 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L28-32 verbatim
variable (period : ℝ) [Fact (0 < period)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ)
  (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))


-- @@ L34-35 verbatim
/-- Cache the standard `NormedAddCommGroup (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient1 : NormedAddCommGroup (V →L[ℝ] V) := inferInstance

-- @@ L36-37 verbatim
/-- Cache the standard `NormedSpace ℝ (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient2 : NormedSpace ℝ (V →L[ℝ] V) := inferInstance

-- @@ L38-41 verbatim
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ V →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularCoefficient3 : NormedAddCommGroup (Space →ᵇ V →L[ℝ] V) :=
    inferInstance

-- @@ L42-45 verbatim
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ V →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularCoefficient4 : NormedSpace ℝ (Space →ᵇ V →L[ℝ] V) :=
    inferInstance

-- @@ L46-49 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient5 : NormedAddCommGroup C(Icc (0 : ℝ) T,Space →ᵇ V
    →L[ℝ] V) := inferInstance

-- @@ L50-53 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient6 : NormedSpace ℝ C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ]
    V) := inferInstance

-- @@ L54-57 verbatim
/-- Cache the standard `NormedAddCommGroup (Supported period V S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient7 : NormedAddCommGroup (Supported period V S hS) :=
    inferInstance

-- @@ L58-61 verbatim
/-- Cache the standard `NormedSpace ℝ (Supported period V S hS)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularCoefficient8 : NormedSpace ℝ (Supported period V S hS) :=
    inferInstance

-- @@ L62-66 verbatim
/-- Cache the standard `NormedAddCommGroup (Supported period V S hS →L[ℝ] Supported period V S
hS)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient9 : NormedAddCommGroup (Supported period V S hS
    →L[ℝ] Supported period V S hS)
    := inferInstance

-- @@ L67-71 verbatim
/-- Cache the standard `NormedSpace ℝ (Supported period V S hS →L[ℝ] Supported period V S hS)`
instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularCoefficient10 : NormedSpace ℝ (Supported period V S hS →L[ℝ]
    Supported period V S hS) :=
    inferInstance


-- @@ L73-83 verbatim
include hB in
/-- This requires only actual translated coefficient regularity, so applies to the constructed Gram
generator. -/
theorem mixedCoefficient_contDiff :
    ContDiff ℝ ∞ (fun a : LiftTangent => liftedOperatorPath period S hS T (translateCoefficientPath
        B a.1)) :=
  (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
    (F := C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS))
    (liftedOperatorPathMap period S hS T)).comp
      (hB.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff)


-- @@ L85-107 verbatim
include hB in
/-- All actual mixed coefficient derivatives retain the real bounded-field derivative bound. -/
theorem mixedCoefficient_bound (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C) (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => liftedOperatorPath period S hS T
      (translateCoefficientPath B b.1)) a‖ ≤ C := by
  let f := translateCoefficientPath B
  have hright : ‖iteratedFDeriv ℝ n (f ∘ ContinuousLinearMap.fst ℝ Space ℝ) a‖ ≤ C := by
    rw [(ContinuousLinearMap.fst ℝ Space ℝ).iteratedFDeriv_comp_right hB a (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    calc
      _ ≤ ‖iteratedFDeriv ℝ n f a.1‖ * ∏ _i : Fin n, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ =>
            ContinuousLinearMap.norm_fst_le ℝ Space ℝ)
      _ ≤ C := by simpa only [Finset.prod_const_one,mul_one] using hb a.1
  have hleft := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := LiftTangent)
    (F := C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
    (G := C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS))
    (liftedOperatorPathMap period S hS T)
    ((hB.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).contDiffAt (x := a)) (n := n) (by simp)
  exact hleft.trans ((mul_le_mul_of_nonneg_right (liftedOperatorPathMap_norm period S hS T)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hright))


-- @@ L109-109 verbatim
end EulerLpCylinderCoefficients
