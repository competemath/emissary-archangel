/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp


-- @@ L17-23 verbatim
/-!
# Actual composition and adjoint calculus on continuous paths

The pointwise operator operations are built from bounded maps in the uniform
norm. Their regularity and factorial bounds are consequently genuine
derivative statements in that norm.
-/


-- @@ L25-25 verbatim
@[expose] public section



-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace EulerContinuousPathComposition


-- @@ L32-33 verbatim
open ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerTransverseGramInverse EulerOperatorGevreyCalculus EulerGevrey

-- @@ L34-34 verbatim
open scoped ContDiff


-- @@ L36-36 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L38-38 verbatim
section Normed


-- @@ L40-43 verbatim
variable {U E F : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L45-46 verbatim
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition1 : NormedAddCommGroup (E →L[ℝ] F) := inferInstance

-- @@ L47-48 verbatim
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition2 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

-- @@ L49-50 verbatim
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition3 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance

-- @@ L51-52 verbatim
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition4 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance

-- @@ L53-54 verbatim
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition5 : NormedAddCommGroup (U →L[ℝ] F) := inferInstance

-- @@ L55-56 verbatim
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition6 : NormedSpace ℝ (U →L[ℝ] F) := inferInstance

-- @@ L57-60 verbatim
/-- Cache the standard `NormedAddCommGroup ((U →L[ℝ] E) →L[ℝ] U →L[ℝ] F)` instance to shorten
typeclass synthesis. -/
local instance instContinuousPathComposition7 : NormedAddCommGroup ((U →L[ℝ] E) →L[ℝ] U →L[ℝ] F) :=
    inferInstance

-- @@ L61-64 verbatim
/-- Cache the standard `NormedSpace ℝ ((U →L[ℝ] E) →L[ℝ] U →L[ℝ] F)` instance to shorten
typeclass synthesis. -/
local instance instContinuousPathComposition8 : NormedSpace ℝ ((U →L[ℝ] E) →L[ℝ] U →L[ℝ] F) :=
    inferInstance

-- @@ L65-67 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instContinuousPathComposition9 : NormedAddCommGroup C(K,E →L[ℝ] F) := inferInstance

-- @@ L68-69 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition10 : NormedSpace ℝ C(K,E →L[ℝ] F) := inferInstance

-- @@ L70-72 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instContinuousPathComposition11 : NormedAddCommGroup C(K,U →L[ℝ] E) := inferInstance

-- @@ L73-74 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition12 : NormedSpace ℝ C(K,U →L[ℝ] E) := inferInstance

-- @@ L75-77 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,U →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instContinuousPathComposition13 : NormedAddCommGroup C(K,U →L[ℝ] F) := inferInstance

-- @@ L78-79 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition14 : NormedSpace ℝ C(K,U →L[ℝ] F) := inferInstance

-- @@ L80-83 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,(U →L[ℝ] E) →L[ℝ] U →L[ℝ] F)` instance to shorten
typeclass synthesis. -/
local instance instContinuousPathComposition15 : NormedAddCommGroup C(K,(U →L[ℝ] E) →L[ℝ] U →L[ℝ]
    F) := inferInstance

-- @@ L84-87 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,(U →L[ℝ] E) →L[ℝ] U →L[ℝ] F)` instance to shorten
typeclass synthesis. -/
local instance instContinuousPathComposition16 : NormedSpace ℝ C(K,(U →L[ℝ] E) →L[ℝ] U →L[ℝ] F) :=
    inferInstance


-- @@ L89-97 verbatim
/-- A fixed bounded map acts pointwise on continuous paths with the same norm bound. -/
theorem postcomposition_norm (A : E →L[ℝ] F) :
    ‖A.compLeftContinuous ℝ K‖ ≤ ‖A‖ := by
  apply opNorm_le_bound _ (norm_nonneg A)
  intro p
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg p))).2
  intro t
  exact (A.le_opNorm (p t)).trans
    (mul_le_mul_of_nonneg_left (p.norm_coe_le_norm t) (norm_nonneg A))


-- @@ L99-101 verbatim
/-- Lift the actual operator composition bilinear map to the coefficient path. -/
def compositionLift : C(K,E →L[ℝ] F) →L[ℝ] C(K,(U →L[ℝ] E) →L[ℝ] U →L[ℝ] F) :=
  (compL ℝ U E F).compLeftContinuous ℝ K


-- @@ L103-105 verbatim
include U E F in
theorem compositionLift_norm : ‖compositionLift (K := K) (U := U) (E := E) (F := F)‖ ≤ 1 :=
  (postcomposition_norm (K := K) (compL ℝ U E F)).trans (norm_compL_le ℝ U E F)


-- @@ L107-109 verbatim
/-- Literal pointwise composition of two continuous coefficient paths. -/
def compose (A : C(K, E →L[ℝ] F)) (B : C(K, U →L[ℝ] E)) : C(K,U →L[ℝ] F) :=
  multiplier (compositionLift A) B


-- @@ L111-112 verbatim
@[simp] theorem compose_apply (A : C(K, E →L[ℝ] F)) (B : C(K, U →L[ℝ] E)) (t : K) :
    compose A B t = (A t).comp (B t) := rfl


-- @@ L114-114 verbatim
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L116-125 verbatim
/-- Actual uniform-norm smoothness of pointwise composition. -/
theorem contDiff_compose (A : P → C(K, E →L[ℝ] F)) (B : P → C(K, U →L[ℝ] E))
    {n : ℕ∞ω} (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) :
    ContDiff ℝ n (fun x => compose (A x) (B x)) := by
  have hLift : ContDiff ℝ n (fun x => compositionLift (U := U) (A x)) :=
    ContDiff.comp (g := compositionLift (K := K) (U := U) (E := E) (F := F)) (f := A)
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
        (E := C(K,E →L[ℝ] F)) (F := C(K,(U →L[ℝ] E) →L[ℝ] U →L[ℝ] F))
        (compositionLift (K := K) (U := U) (E := E) (F := F))) hA
  exact contDiff_apply (fun x => compositionLift (U := U) (A x)) B hLift hB


-- @@ L127-144 verbatim
/-- Pointwise composition has the same fixed factorial product constant. -/
theorem compose_bound (A : P → C(K, E →L[ℝ] F)) (B : P → C(K, U →L[ℝ] E))
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (c d : ℕ)
    (hbA : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R c n)
    (hbB : ∀ n x, ‖iteratedFDeriv ℝ n B x‖ ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => compose (A y) (B y)) x‖ ≤
      (3*C*D)*majorant R (c+d) n := by
  have hLift : ContDiff ℝ ∞ (fun x => compositionLift (U := U) (A x)) :=
    ContDiff.comp (g := compositionLift (K := K) (U := U) (E := E) (F := F)) (f := A)
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
        (E := C(K,E →L[ℝ] F)) (F := C(K,(U →L[ℝ] E) →L[ℝ] U →L[ℝ] F))
        (compositionLift (K := K) (U := U) (E := E) (F := F))) hA
  have hbLift := contraction_bound (compositionLift (K := K) (U := U) (E := E) (F := F))
    compositionLift_norm A hA R C hR hC c hbA
  exact apply_bound (fun y => compositionLift (U := U) (A y)) B hLift hB
    R C D hR hC hD c d hbLift hbB n x


-- @@ L146-146 verbatim
end Normed


-- @@ L148-148 verbatim
section Hilbert


-- @@ L150-152 verbatim
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L154-155 verbatim
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition17 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance

-- @@ L156-157 verbatim
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition18 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance

-- @@ L158-159 verbatim
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition19 : NormedAddCommGroup (E →L[ℝ] U) := inferInstance

-- @@ L160-161 verbatim
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition20 : NormedSpace ℝ (E →L[ℝ] U) := inferInstance

-- @@ L162-164 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instContinuousPathComposition21 : NormedAddCommGroup C(K,U →L[ℝ] E) := inferInstance

-- @@ L165-166 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition22 : NormedSpace ℝ C(K,U →L[ℝ] E) := inferInstance

-- @@ L167-169 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,E →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instContinuousPathComposition23 : NormedAddCommGroup C(K,E →L[ℝ] U) := inferInstance

-- @@ L170-171 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instContinuousPathComposition24 : NormedSpace ℝ C(K,E →L[ℝ] U) := inferInstance


-- @@ L173-175 verbatim
/-- Actual adjoint at every parameter in the compact path domain. -/
def adjointMap : C(K,U →L[ℝ] E) →L[ℝ] C(K,E →L[ℝ] U) :=
  (realAdjoint (U := U) (E := E)).compLeftContinuous ℝ K


-- @@ L177-179 verbatim
omit [CompactSpace K] in
@[simp] theorem adjointMap_apply (A : C(K, U →L[ℝ] E)) (t : K) :
    adjointMap A t = (A t).adjoint := rfl


-- @@ L181-186 verbatim
theorem adjointMap_norm : ‖adjointMap (K := K) (U := U) (E := E)‖ ≤ 1 := by
  apply (postcomposition_norm (K := K) (realAdjoint (U := U) (E := E))).trans
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖A.adjoint‖ ≤ (1 : ℝ)*‖A‖
  simp only [LinearIsometryEquiv.norm_map, one_mul, le_refl]


-- @@ L188-188 verbatim
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]


-- @@ L190-195 verbatim
theorem contDiff_adjoint (A : P → C(K, U →L[ℝ] E)) {n : ℕ∞ω} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun x => adjointMap (A x)) :=
  ContDiff.comp (g := adjointMap (K := K) (U := U) (E := E)) (f := A)
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := C(K,U →L[ℝ] E)) (F := C(K,E →L[ℝ] U))
      (adjointMap (K := K) (U := U) (E := E))) hA


-- @@ L197-201 verbatim
theorem adjoint_bound (A : P → C(K, U →L[ℝ] E)) (hA : ContDiff ℝ ∞ A)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => adjointMap (A y)) x‖ ≤ C*majorant R d n :=
  contraction_bound (adjointMap (K := K) (U := U) (E := E)) adjointMap_norm A hA R C hR hC d hb n x


-- @@ L203-203 verbatim
end Hilbert


-- @@ L205-205 verbatim
end EulerContinuousPathComposition
