/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalPath
import Mathlib.Analysis.Calculus.Deriv.Comp
public import LeanPool.NavierStokesAndEuler.Euler.LpSupportedMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamel
import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldTimeDerivative


-- @@ L14-22 verbatim
/-!
# Constructed spatial L² evolution from the coefficient field alone

The bounded-field Banach algebra supplies actual fundamental fields by the
proved Picard construction. Their multiplication operators give an actual
evolution on supported spatial L². The localized H3 estimate is imposed only
on this genuine homogeneous propagator and is then inherited with constant
one by the spatial L² evolution.
-/


-- @@ L24-24 verbatim
section


-- @@ L26-34 verbatim
/-!
# Lifting the localized homogeneous propagator to actual spatial L²

The homogeneous fundamental fields are multiplied against genuine spatial L²
functions supported in a fixed measurable set. The resulting continuous
operator paths satisfy the homogeneous differential equation and inverse
identities. Their propagator norm uses only the pointwise bound on that set,
so the source's `C g(t)/g(s)` estimate is preserved exactly.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
namespace EulerLpSupportedEvolution


-- @@ L42-43 verbatim
open Set MeasureTheory ContinuousLinearMap EulerVolterraConvolution
  EulerLpSupportedSubspace EulerLpSupportedMultiplier EulerLinearDuhamel

-- @@ L44-44 verbatim
open scoped BoundedContinuousFunction


-- @@ L46-49 verbatim
variable {α V : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] (μ : Measure α)
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set α) (hS : MeasurableSet S)


-- @@ L51-52 verbatim
/-- Cache the standard `NormedRing (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpSupportedEvolution1 : NormedRing (V →L[ℝ] V) := inferInstance

-- @@ L53-55 verbatim
/-- Cache the standard `NormedRing (Field (α := α) (V := V))` instance to shorten typeclass
synthesis. -/
local instance instLpSupportedEvolution2 : NormedRing (Field (α := α) (V := V)) := inferInstance

-- @@ L56-59 verbatim
/-- Cache the standard `NormedAddCommGroup (Field (α := α) (V := V))` instance to shorten
typeclass synthesis. -/
local instance instLpSupportedEvolution3 : NormedAddCommGroup (Field (α := α) (V := V)) :=
    inferInstance

-- @@ L60-62 verbatim
/-- Cache the standard `NormedSpace ℝ (Field (α := α) (V := V))` instance to shorten typeclass
synthesis. -/
local instance instLpSupportedEvolution4 : NormedSpace ℝ (Field (α := α) (V := V)) := inferInstance

-- @@ L63-64 verbatim
/-- Cache the standard `NormedAddCommGroup (Lp V 2 μ)` instance to shorten typeclass synthesis. -/
local instance instLpSupportedEvolution5 : NormedAddCommGroup (Lp V 2 μ) := inferInstance

-- @@ L65-66 verbatim
/-- Cache the standard `InnerProductSpace ℝ (Lp V 2 μ)` instance to shorten typeclass synthesis. -/
local instance instLpSupportedEvolution6 : InnerProductSpace ℝ (Lp V 2 μ) := inferInstance

-- @@ L67-70 verbatim
/-- Cache the standard `NormedAddCommGroup (supportedSpace (V := V) μ S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpSupportedEvolution7 : NormedAddCommGroup (supportedSpace (V := V) μ S hS) :=
    inferInstance

-- @@ L71-74 verbatim
/-- Cache the standard `InnerProductSpace ℝ (supportedSpace (V := V) μ S hS)` instance to
shorten typeclass synthesis. -/
local instance instLpSupportedEvolution8 : InnerProductSpace ℝ (supportedSpace (V := V) μ S hS) :=
    inferInstance

-- @@ L75-78 verbatim
/-- Cache the standard `NormedSpace ℝ (supportedSpace (V := V) μ S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpSupportedEvolution9 : NormedSpace ℝ (supportedSpace (V := V) μ S hS) :=
    inferInstance

-- @@ L79-83 verbatim
/-- Cache the standard `NormedAddCommGroup (supportedSpace (V := V) μ S hS →L[ℝ] supportedSpace
(V := V) μ S hS)` instance to shorten typeclass synthesis. -/
local instance instLpSupportedEvolution10 : NormedAddCommGroup (supportedSpace (V := V) μ S hS
    →L[ℝ] supportedSpace (V
    := V) μ S hS) := inferInstance

-- @@ L84-88 verbatim
/-- Cache the standard `NormedSpace ℝ (supportedSpace (V := V) μ S hS →L[ℝ] supportedSpace (V :=
V) μ S hS)` instance to shorten typeclass synthesis. -/
local instance instLpSupportedEvolution11 : NormedSpace ℝ (supportedSpace (V := V) μ S hS →L[ℝ]
    supportedSpace (V :=
    V) μ S hS) := inferInstance


-- @@ L90-93 verbatim
/-- The actual supported-space operator associated with a continuous field path. -/
def operatorPath (T : ℝ) (A : C(Icc (0 : ℝ) T, Field (α := α) (V := V))) :
    C(Icc (0 : ℝ) T,supportedSpace (V := V) μ S hS →L[ℝ] supportedSpace (V := V) μ S hS) :=
  ⟨fun t => operator μ S hS (A t), (operatorMap μ S hS).continuous.comp A.continuous⟩


-- @@ L95-97 verbatim
omit [CompleteSpace V] in
@[simp] theorem operatorPath_apply (T : ℝ) (A : C(Icc (0 : ℝ) T, Field (α := α) (V := V)))
    (t : Icc (0 : ℝ) T) : operatorPath μ S hS T A t = operator μ S hS (A t) := rfl


-- @@ L99-122 verbatim
/-- Actual pointwise time derivatives lift to supported-L² operator derivatives. -/
theorem operatorPath_hasDerivWithinAt (T : ℝ) (hT : 0 ≤ T)
    (A A' : C(Icc (0 : ℝ) T, Field (α := α) (V := V)))
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : α,
      HasDerivWithinAt (fun s => extendPath (Y := Field (α := α) (V := V)) T hT A s x)
        (extendPath (Y := Field (α := α) (V := V)) T hT A' t x) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (operatorPath μ S hS T A))
      (operatorPath μ S hS T A' t) (Icc (0 : ℝ) T) t := by
  have hfield := EulerBoundedFieldTimeDerivative.hasDerivWithinAt T hT A A' hpoint t t.property
  have hlinear : HasFDerivAt (fun A : Field (α := α) (V := V) => operatorMap μ S hS A)
      (operatorMap μ S hS) (extendPath (Y := Field (α := α) (V := V)) T hT A t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Field (α := α) (V := V))
      (F := supportedSpace (V := V) μ S hS →L[ℝ] supportedSpace (V := V) μ S hS)
      (operatorMap μ S hS)
  have hd : HasDerivWithinAt
      (fun s => operatorMap μ S hS (extendPath (Y := Field (α := α) (V := V)) T hT A s))
      (operatorMap μ S hS (extendPath (Y := Field (α := α) (V := V)) T hT A' t))
      (Icc (0 : ℝ) T) t := hlinear.comp_hasDerivWithinAt (t : ℝ) hfield
  change HasDerivWithinAt (fun s => operatorMap μ S hS (A (projIcc 0 T hT s)))
    (operatorMap μ S hS (A' t)) (Icc (0 : ℝ) T) t
  change HasDerivWithinAt (fun s => operatorMap μ S hS (A (projIcc 0 T hT s)))
    (operatorMap μ S hS (A' (projIcc 0 T hT t))) (Icc (0 : ℝ) T) t at hd
  rwa [projIcc_of_mem hT t.property] at hd


-- @@ L124-131 verbatim
variable (T : ℝ) (hT : 0 ≤ T)
  (B Φ Ψ : C(Icc (0 : ℝ) T, Field (α := α) (V := V)))
  (hRight : ∀ t x, x ∈ S → (Φ t x).comp (Ψ t x) = ContinuousLinearMap.id ℝ V)
  (hLeft : ∀ t x, x ∈ S → (Ψ t x).comp (Φ t x) = ContinuousLinearMap.id ℝ V)
  (hΦ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : α,
    HasDerivWithinAt (fun s => extendPath (Y := Field (α := α) (V := V)) T hT Φ s x)
      ((extendPath (Y := Field (α := α) (V := V)) T hT B t x).comp (extendPath (Y := Field (α := α)
          (V := V)) T hT Φ t x)) (Icc (0 : ℝ) T) t)


-- @@ L133-162 verbatim
/-- The actual pointwise homogeneous fields give a homogeneous evolution on
the genuine supported spatial L² space. -/
def liftEvolution : Evolution T hT (operatorPath μ S hS T B) where
  forward := operatorPath μ S hS T Φ
  backward := operatorPath μ S hS T Ψ
  forward_backward := by
    intro t
    change (operator μ S hS (Φ t)).comp (operator μ S hS (Ψ t)) = _
    rw [← operator_mul]
    calc
      operator μ S hS (Φ t * Ψ t) = operator μ S hS (1 : Field (α := α) (V := V)) :=
        operator_congr_on μ S hS _ _ (fun x hx => hRight t x hx)
      _ = _ := operator_one μ S hS
  backward_forward := by
    intro t
    change (operator μ S hS (Ψ t)).comp (operator μ S hS (Φ t)) = _
    rw [← operator_mul]
    calc
      operator μ S hS (Ψ t * Φ t) = operator μ S hS (1 : Field (α := α) (V := V)) :=
        operator_congr_on μ S hS _ _ (fun x hx => hLeft t x hx)
      _ = _ := operator_one μ S hS
  derivative := by
    intro t
    let D : C(Icc (0 : ℝ) T,Field (α := α) (V := V)) :=
      ⟨fun s => B s * Φ s, B.continuous.mul Φ.continuous⟩
    have hd := operatorPath_hasDerivWithinAt μ S hS T hT Φ D hΦ t
    change HasDerivWithinAt (extendPath T hT (operatorPath μ S hS T Φ))
      (operator μ S hS (B t * Φ t)) (Icc (0 : ℝ) T) t at hd
    rw [operator_mul] at hd
    exact hd


-- @@ L164-175 verbatim
/-- The pointwise localized (H3) estimate is the actual L² propagator norm,
with the identical relative profile factor. -/
theorem liftEvolution_propagator_norm (g : Icc (0 : ℝ) T → ℝ) (hg : ∀ t, 0 < g t)
    (C : ℝ) (hC : 0 ≤ C)
    (hprop : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x ∈ S,
      ‖(Φ t x).comp (Ψ s x)‖ ≤ C*g t/g s)
    (t s : Icc (0 : ℝ) T) (hst : s ≤ t) :
    ‖(liftEvolution μ S hS T hT B Φ Ψ hRight hLeft hΦ).propagator t s‖ ≤ C*g t/g s := by
  change ‖(operator μ S hS (Φ t)).comp (operator μ S hS (Ψ s))‖ ≤ _
  rw [← operator_mul]
  exact operator_norm_le μ S hS (Φ t*Ψ s) (C*g t/g s)
    (div_nonneg (mul_nonneg hC (hg t).le) (hg s).le) (hprop t s hst)


-- @@ L177-189 verbatim
/-- The actual forced supported-L² path has the source's polynomial profile bound. -/
theorem liftedSolution_profile_bound
    (f : C(Icc (0 : ℝ) T, supportedSpace (V := V) μ S hS))
    (a₀ : supportedSpace (V := V) μ S hS)
    (g : Icc (0 : ℝ) T → ℝ) (hg : ∀ t, 0 < g t) (hg₀ : g ⟨0, le_rfl, hT⟩ = 1)
    (C D : ℝ) (hC : 0 ≤ C)
    (hprop : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x ∈ S,
      ‖(Φ t x).comp (Ψ s x)‖ ≤ C*g t/g s)
    (hf : ∀ s, ‖f s‖ ≤ D*g s) (t : Icc (0 : ℝ) T) :
    ‖(liftEvolution μ S hS T hT B Φ Ψ hRight hLeft hΦ).solution f a₀ t‖ ≤
      C*g t*(‖a₀‖+(t : ℝ)*D) :=
  (liftEvolution μ S hS T hT B Φ Ψ hRight hLeft hΦ).solution_profile_bound f a₀ g hg hg₀ C D hC
    (liftEvolution_propagator_norm μ S hS T hT B Φ Ψ hRight hLeft hΦ g hg C hC hprop) hf t


-- @@ L191-205 verbatim
/-- This profile-bounded path solves the actual supported-L² differential equation. -/
theorem liftedSolution_hasDerivWithinAt
    (f : C(Icc (0 : ℝ) T, supportedSpace (V := V) μ S hS))
    (a₀ : supportedSpace (V := V) μ S hS) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (extendPath T hT ((liftEvolution μ S hS T hT B Φ Ψ hRight hLeft hΦ).solution f a₀))
      (operator μ S hS (B t) ((liftEvolution μ S hS T hT B Φ Ψ hRight hLeft hΦ).solution f a₀ t) +
          f t)
      (Icc (0 : ℝ) T) t := by
  let U := liftEvolution μ S hS T hT B Φ Ψ hRight hLeft hΦ
  have hd := U.solution_derivative f a₀ t
  apply hd.congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs]
  rfl


-- @@ L207-207 verbatim
end EulerLpSupportedEvolution


-- @@ L209-209 verbatim
end

-- @@ L210-210 verbatim
end


-- @@ L212-212 verbatim
end


-- @@ L214-214 verbatim
@[expose] public section


-- @@ L216-216 verbatim
noncomputable section


-- @@ L218-218 verbatim
namespace EulerLpSupportedConstructedEvolution


-- @@ L220-222 verbatim
open Set MeasureTheory ContinuousLinearMap EulerVolterraConvolution
  EulerLpSupportedSubspace EulerLpSupportedMultiplier EulerLpSupportedEvolution
  EulerLinearDuhamel EulerLinearFundamentalExistence

-- @@ L223-223 verbatim
open scoped BoundedContinuousFunction


-- @@ L225-226 verbatim
variable {α V : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]


-- @@ L228-229 verbatim
/-- Cache the standard `NormedRing (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpSupportedConstructedEvolution1 : NormedRing (V →L[ℝ] V) := inferInstance

-- @@ L230-231 verbatim
/-- Cache the standard `NormedAlgebra ℝ (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpSupportedConstructedEvolution2 : NormedAlgebra ℝ (V →L[ℝ] V) := inferInstance

-- @@ L232-235 verbatim
/-- Cache the standard `NormedRing (Field (α := α) (V := V))` instance to shorten typeclass
synthesis. -/
local instance instLpSupportedConstructedEvolution3 : NormedRing (Field (α := α) (V := V)) :=
    inferInstance

-- @@ L236-239 verbatim
/-- Cache the standard `NormedAlgebra ℝ (Field (α := α) (V := V))` instance to shorten typeclass
synthesis. -/
local instance instLpSupportedConstructedEvolution4 : NormedAlgebra ℝ (Field (α := α) (V := V)) :=
    inferInstance


-- @@ L241-241 verbatim
variable (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T, Field (α := α) (V := V)))


-- @@ L243-257 verbatim
omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- The constructed fields satisfy the literal pointwise homogeneous ODE. -/
theorem fundamental_pointwise_derivative (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : α) :
    HasDerivWithinAt
      (fun s => extendPath (Y := Field (α := α) (V := V)) T hT (fundamentalPath T hT B).forward s x)
      ((extendPath (Y := Field (α := α) (V := V)) T hT B t x).comp
        (extendPath (Y := Field (α := α) (V := V)) T hT (fundamentalPath T hT B).forward t x))
      (Icc (0 : ℝ) T) t := by
  let ev : Field (α := α) (V := V) →L[ℝ] (V →L[ℝ] V) := BoundedContinuousFunction.evalCLM ℝ x
  have hd := (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
    (E := Field (α := α) (V := V)) (F := V →L[ℝ] V) ev).comp_hasDerivWithinAt t
      ((fundamentalPath T hT B).derivative ⟨t,ht⟩)
  simp only [extendPath, projIcc_of_mem hT ht]
  convert hd using 1
  all_goals rfl


-- @@ L259-267 verbatim
/-- A genuine supported-L² evolution constructed from the original bounded coefficient. -/
def constructedSupportedEvolution (μ : Measure α) (S : Set α) (hS : MeasurableSet S) :
    Evolution T hT (operatorPath μ S hS T B) :=
  liftEvolution μ S hS T hT B (fundamentalPath T hT B).forward (fundamentalPath T hT B).backward
    (fun t x _ => congrArg (fun A : Field (α := α) (V := V) => A x)
      ((fundamentalPath T hT B).forward_backward t))
    (fun t x _ => congrArg (fun A : Field (α := α) (V := V) => A x)
      ((fundamentalPath T hT B).backward_forward t))
    (fundamental_pointwise_derivative T hT B)


-- @@ L269-282 verbatim
/-- The actual supported-L² propagator retains the exact localized H3 bound. -/
theorem constructedSupportedEvolution_propagator_norm
    (μ : Measure α) (S : Set α) (hS : MeasurableSet S)
    (g : Icc (0 : ℝ) T → ℝ) (hg : ∀ t, 0 < g t) (C : ℝ) (hC : 0 ≤ C)
    (hprop : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x ∈ S,
      ‖((fundamentalPath T hT B).forward t x).comp ((fundamentalPath T hT B).backward s x)‖ ≤
        C*g t/g s)
    (t s : Icc (0 : ℝ) T) (hst : s ≤ t) :
    ‖(constructedSupportedEvolution T hT B μ S hS).propagator t s‖ ≤ C*g t/g s := by
  change ‖(operator μ S hS ((fundamentalPath T hT B).forward t)).comp
    (operator μ S hS ((fundamentalPath T hT B).backward s))‖ ≤ _
  rw [← operator_mul]
  exact operator_norm_le μ S hS _ (C*g t/g s)
    (div_nonneg (mul_nonneg hC (hg t).le) (hg s).le) (hprop t s hst)


-- @@ L284-284 verbatim
end EulerLpSupportedConstructedEvolution
