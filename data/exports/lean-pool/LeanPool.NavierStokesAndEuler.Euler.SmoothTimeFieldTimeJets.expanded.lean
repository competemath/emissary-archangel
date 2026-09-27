/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeSuperposition
public import LeanPool.NavierStokesAndEuler.Euler.SmoothPathTimeJets
import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldTimeDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp


-- @@ L15-16 verbatim
/-! A literal time derivative of smooth bounded fields differentiates
every actual spatial jet, both pointwise and in the uniform field norm. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section



-- @@ L24-24 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L26-26 verbatim
namespace SmoothTimeField


-- @@ L28-28 verbatim
open Set EulerVolterraConvolution EulerSmoothPathTimeJets


-- @@ L30-32 verbatim
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V)


-- @@ L34-37 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldTimeJets1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance

-- @@ L38-39 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeFieldTimeJets2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance

-- @@ L40-43 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldTimeJets3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

-- @@ L44-47 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldTimeJets4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance


-- @@ L49-51 verbatim
/-- Slice family, given by `A.superposition ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) x)`. -/
def sliceFamily (x : E) : C(Icc (0 : ℝ) T,V) :=
  A.superposition ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) x)


-- @@ L53-55 verbatim
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
@[simp] theorem sliceFamily_apply (x : E) (t : Icc (0 : ℝ) T) :
    sliceFamily T A x t = A.field t x := rfl


-- @@ L57-61 verbatim
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
theorem sliceFamily_contDiff : ContDiff ℝ ∞ (sliceFamily T A) :=
  A.superposition_contDiff.comp
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E)
      (F := C(Icc (0 : ℝ) T,E)) (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)))


-- @@ L63-66 verbatim
theorem sliceFamily_jet (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    jetFamily T (sliceFamily T A) n x t = A.jet n t x := by
  rw [jetFamily_apply T _ (sliceFamily_contDiff T A)]
  exact (A.jet_eq n t x).symm


-- @@ L68-82 verbatim
theorem TimeDerivative.jet_pointwise (htime : TimeDerivative T hT A A₁)
    (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => extendPath T hT (A.jet n) s x)
      (A₁.jet n t x) (Icc (0 : ℝ) T) t := by
  have hd : ∀ y (s : Icc (0 : ℝ) T),
      HasDerivWithinAt (extendPath T hT (sliceFamily T A y))
        (sliceFamily T A₁ y s) (Icc (0 : ℝ) T) s := fun y s => htime s y
  have h := jetFamily_hasDerivWithinAt T hT (sliceFamily T A) (sliceFamily T A₁)
    (sliceFamily_contDiff T A) (sliceFamily_contDiff T A₁) hd n x t
  have he : extendPath T hT (jetFamily T (sliceFamily T A) n x) =
      fun s => extendPath T hT (A.jet n) s x := by
    funext s
    exact sliceFamily_jet T A n x (projIcc 0 T hT s)
  rw [he, sliceFamily_jet] at h
  exact h


-- @@ L84-90 verbatim
theorem TimeDerivative.derivative (htime : TimeDerivative T hT A A₁) :
    TimeDerivative T hT A.derivative A₁.derivative := by
  intro t x
  let L := (continuousMultilinearCurryFin1 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (TimeDerivative.jet_pointwise T hT A A₁ htime 1 x t)
  exact h


-- @@ L92-100 verbatim
theorem TimeDerivative.jet_uniform (htime : TimeDerivative T hT A A₁)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (A.jet n))
      (A₁.jet n t) (Icc (0 : ℝ) T) t := by
  have h := EulerBoundedFieldTimeDerivative.hasDerivWithinAt T hT (A.jet n) (A₁.jet n)
    (fun s hs x => by
      simpa only [extendPath, projIcc_of_mem hT hs] using
        TimeDerivative.jet_pointwise T hT A A₁ htime n x ⟨s,hs⟩) t t.property
  simpa only [extendPath, projIcc_of_mem hT t.property] using h


-- @@ L102-102 verbatim
end SmoothTimeField
