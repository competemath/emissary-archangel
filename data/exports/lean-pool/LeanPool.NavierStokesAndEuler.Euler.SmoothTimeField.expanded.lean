/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath


-- @@ L11-13 verbatim
/-! Smooth bounded fields on a general real normed domain, with actual
spatial jets continuous in the uniform time-path norm. This extends the
ordinary-space coefficient interface to the lifted four-dimensional flow. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L22-22 verbatim
universe u


-- @@ L24-33 verbatim
/-- Smooth time field data, collecting `field`, `smooth`, `jet`, `jet_eq`. -/
structure SmoothTimeField (K E V : Type u) [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Underlying field of `SmoothTimeField`, of type `C(K, E →ᵇ V)`. -/
  field : C(K, E →ᵇ V)
  smooth : ∀ t, ContDiff ℝ ∞ (field t : E → V)
  /-- Jet of `SmoothTimeField`, of type `(n : ℕ) → C(K, E →ᵇ (E [×n]→L[ℝ] V))`. -/
  jet : (n : ℕ) → C(K, E →ᵇ (E [×n]→L[ℝ] V))
  jet_eq : ∀ n t x, jet n t x = iteratedFDeriv ℝ n (field t : E → V) x


-- @@ L35-35 verbatim
namespace SmoothTimeField


-- @@ L37-40 verbatim
variable {K E V W : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]


-- @@ L42-43 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeField1 : NormedAddCommGroup (E →ᵇ V) := inferInstance

-- @@ L44-45 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeField2 : NormedSpace ℝ (E →ᵇ V) := inferInstance

-- @@ L46-47 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ W)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeField3 : NormedAddCommGroup (E →ᵇ W) := inferInstance

-- @@ L48-49 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ W)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeField4 : NormedSpace ℝ (E →ᵇ W) := inferInstance

-- @@ L50-52 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E →L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeField5 : NormedAddCommGroup (E →ᵇ (E →L[ℝ] V)) := inferInstance

-- @@ L53-55 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E →L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeField6 : NormedSpace ℝ (E →ᵇ (E →L[ℝ] V)) := inferInstance

-- @@ L56-59 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeField7 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

-- @@ L60-62 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeField8 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance


-- @@ L64-66 verbatim
/-- Map path, given by `(L.compLeftContinuousBounded E).compLeftContinuous ℝ K`. -/
def mapPath (L : V →L[ℝ] W) : C(K,E →ᵇ V) →L[ℝ] C(K,E →ᵇ W) :=
  (L.compLeftContinuousBounded E).compLeftContinuous ℝ K


-- @@ L68-72 verbatim
/-- Derivative field, given by `mapPath (continuousMultilinearCurryFin1 ℝ E
V).toContinuousLinearEquiv.toContinuousLinearMap (A.jet 1)`. -/
def derivativeField (A : SmoothTimeField K E V) : C(K,E →ᵇ (E →L[ℝ] V)) :=
  mapPath (continuousMultilinearCurryFin1 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap
    (A.jet 1)


-- @@ L74-81 verbatim
theorem derivativeField_eq (A : SmoothTimeField K E V) (t : K) (x : E) :
    A.derivativeField t x = fderiv ℝ (A.field t : E → V) x := by
  change continuousMultilinearCurryFin1 ℝ E V (A.jet 1 t x) = _
  rw [A.jet_eq]
  apply ContinuousLinearMap.ext
  intro a
  rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp


-- @@ L83-88 verbatim
/-- Derivative jet, constructed using `mapPath`. -/
def derivativeJet (A : SmoothTimeField K E V) (n : ℕ) :
    C(K,E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] V))) :=
  mapPath (K := K) (V := E [×(n+1)]→L[ℝ] V) (W := E [×n]→L[ℝ] (E →L[ℝ] V))
    (continuousMultilinearCurryRightEquiv' ℝ n E V).toContinuousLinearEquiv.toContinuousLinearMap
    (A.jet (n+1))


-- @@ L90-94 verbatim
theorem derivativeJet_eq (A : SmoothTimeField K E V) (n : ℕ) (t : K) (x : E) :
    A.derivativeJet n t x = iteratedFDeriv ℝ n (fderiv ℝ (A.field t : E → V)) x := by
  change continuousMultilinearCurryRightEquiv' ℝ n E V (A.jet (n+1) t x) = _
  rw [A.jet_eq, iteratedFDeriv_succ_eq_comp_right]
  exact (continuousMultilinearCurryRightEquiv' ℝ n E V).apply_symm_apply _


-- @@ L96-110 verbatim
/-- Derivative, bundling `field`, `smooth`, `have`, `exact` and the required compatibility
proofs. -/
def derivative (A : SmoothTimeField K E V) : SmoothTimeField K E (E →L[ℝ] V) where
  field := A.derivativeField
  smooth t := by
    have he : (A.derivativeField t : E → E →L[ℝ] V) = fderiv ℝ (A.field t : E → V) :=
      funext (A.derivativeField_eq t)
    rw [he]
    exact (A.smooth t).fderiv_right (m := ∞) (by simp)
  jet := A.derivativeJet
  jet_eq n t x := by
    have he : (A.derivativeField t : E → E →L[ℝ] V) = fderiv ℝ (A.field t : E → V) :=
      funext (A.derivativeField_eq t)
    rw [he]
    exact A.derivativeJet_eq n t x


-- @@ L112-112 verbatim
end SmoothTimeField


-- @@ L114-114 verbatim
namespace EulerMeanCoefficients.SmoothCoefficientPath


-- @@ L116-116 verbatim
open EulerSmoothLimit


-- @@ L118-122 verbatim
/-- To smooth time field, given by `⟨A.field, A.smooth, A.jet, A.jet_eq⟩`. -/
def toSmoothTimeField {K V : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothCoefficientPath K V) :
    SmoothTimeField K Space V :=
  ⟨A.field, A.smooth, A.jet, A.jet_eq⟩


-- @@ L124-126 verbatim
@[simp] theorem toSmoothTimeField_field {K V : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothCoefficientPath K V) :
    A.toSmoothTimeField.field = A.field := rfl


-- @@ L128-128 verbatim
end EulerMeanCoefficients.SmoothCoefficientPath
