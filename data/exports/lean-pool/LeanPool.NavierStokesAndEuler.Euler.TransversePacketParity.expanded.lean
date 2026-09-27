/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderParity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorParity
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderEquation
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelNaturality
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficientTime
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamel
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelWeighted


-- @@ L21-21 verbatim
/-! Joint odd parity of the actual transverse velocity, its time derivative, and its corrector. -/


-- @@ L23-23 verbatim
section


-- @@ L25-25 verbatim
/-! Reflection parity of the actual Gram-projected source evolution and its physical velocity. -/


-- @@ L27-27 verbatim
section


-- @@ L29-35 verbatim
/-!
# Independence and symmetries of the actual forward solve

The forced solution is independent of the selected homogeneous fundamental
representation. Consequently coefficient symmetries pass to the solution
without assuming any corresponding symmetry of that representation.
-/


-- @@ L37-37 verbatim
@[expose] public section


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
namespace EulerLinearDuhamel


-- @@ L43-43 verbatim
open Set ContinuousLinearMap EulerContinuousTimeIntegral


-- @@ L45-45 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

-- @@ L46-46 verbatim
variable {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T, E →L[ℝ] E)}


-- @@ L48-48 verbatim
namespace Evolution


-- @@ L50-55 verbatim
/-- The true forced path is independent of the fundamental evolution chosen to represent it. -/
theorem solution_independent (U V : Evolution T hT B) (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    U.solution f a₀ = V.solution f a₀ := by
  ext t
  exact V.solution_unique f a₀ (U.solutionReal f a₀) (U.solution_derivative f a₀)
    (U.solution_initial f a₀) t


-- @@ L57-60 verbatim
/-- Sign reversal of both data reverses the actual solution. -/
theorem solution_neg (U : Evolution T hT B) (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    U.solution (-f) (-a₀) = -U.solution f a₀ := by
  rw [U.solution_eq_operators, U.solution_eq_operators, map_neg, map_neg, neg_add]


-- @@ L62-65 verbatim
/-- Zero data vanish identically. -/
@[simp] theorem solution_zero (U : Evolution T hT B) :
    U.solution (0 : C(Icc (0 : ℝ) T,E)) 0 = 0 := by
  rw [U.solution_eq_operators, map_zero, map_zero, add_zero]


-- @@ L67-67 verbatim
end Evolution


-- @@ L69-70 verbatim
variable {P : Type*} (T : ℝ) (hT : 0 ≤ T)
  (B : P → C(Icc (0 : ℝ) T, E →L[ℝ] E)) (U : ∀ x, Evolution T hT (B x))


-- @@ L72-89 verbatim
/-- Reflection or any other parameter symmetry is inherited from coefficients
and data; no regularity or symmetry of the chosen propagators is required. -/
theorem solution_odd_under (σ : P → P) (hB : ∀ x, B (σ x) = B x)
    (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → E)
    (hf : ∀ x, f (σ x) = -f x) (ha₀ : ∀ x, a₀ (σ x) = -a₀ x) (x : P) :
    (U (σ x)).solution (f (σ x)) (a₀ (σ x)) = -(U x).solution (f x) (a₀ x) := by
  have he := (U x).frozen_solution (U (σ x)) (f (σ x)) (a₀ (σ x))
  have hm : multiplier (0 : C(Icc (0 : ℝ) T,E →L[ℝ] E)) = 0 := by
    ext p t
    rfl
  have hcoeff : B (σ x)-B x = 0 := by rw [hB x, sub_self]
  rw [hcoeff, hm, zero_apply, add_zero] at he
  calc
    (U (σ x)).solution (f (σ x)) (a₀ (σ x)) =
        (U x).initialOperator (a₀ (σ x)) + (U x).forcingOperator (f (σ x)) := he
    _ = -((U x).initialOperator (a₀ x) + (U x).forcingOperator (f x)) := by
      rw [hf x, ha₀ x, map_neg, map_neg, neg_add]
    _ = -(U x).solution (f x) (a₀ x) := by rw [(U x).solution_eq_operators]


-- @@ L91-101 verbatim
/-- The actual forward solution stays in the union of the supports of its data. -/
theorem solution_support_subset (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → E) :
    Function.support (fun x => (U x).solution (f x) (a₀ x)) ⊆
      Function.support f ∪ Function.support a₀ := by
  intro x hx
  by_cases hf : f x = 0
  · by_cases ha : a₀ x = 0
    · have hz : (U x).solution (f x) (a₀ x) = 0 := by rw [hf, ha, Evolution.solution_zero]
      exact (hx hz).elim
    · exact Or.inr ha
  · exact Or.inl hf


-- @@ L103-103 verbatim
end EulerLinearDuhamel


-- @@ L105-105 verbatim
end

-- @@ L106-106 verbatim
end


-- @@ L108-108 verbatim
end


-- @@ L110-110 verbatim
section


-- @@ L112-112 verbatim
/-! Actual supported forward evolution preserves joint odd parity for even coefficients. -/


-- @@ L114-114 verbatim
@[expose] public section


-- @@ L116-116 verbatim
noncomputable section


-- @@ L118-118 verbatim
namespace EulerCylinderForwardParity


-- @@ L120-122 verbatim
open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerLpCylinderCoefficients EulerCylinderFieldReflection
      EulerLinearDuhamel

-- @@ L123-123 verbatim
open scoped BoundedContinuousFunction


-- @@ L125-130 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)
  (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))
  (hB : ∀ t x, B t (-x) = B t x)
  (U : Evolution T hT (liftedOperatorPath P S hS T B))


-- @@ L132-141 verbatim
include hB in
theorem solution_reflection (f : C(Icc (0 : ℝ) T, Supported P V S hS)) (a₀ : Supported P V S hS) :
    supportedPathReflection P S hS hSym (U.solution f a₀) =
      U.solution (supportedPathReflection P S hS hSym f) (supportedReflection P S hS hSym a₀) := by
  apply (U.solution_map U (supportedReflection P S hS hSym) _ f a₀).symm
  intro t u
  change liftedOperator P S hS (B t) (supportedReflection P S hS hSym u) =
    supportedReflection P S hS hSym (liftedOperator P S hS (B t) u)
  rw [← supportedOperator_eq_square]
  exact (supportedReflection_operator P S hS hSym (B t) (hB t) u).symm


-- @@ L143-154 verbatim
include hB in
theorem solution_reflection_neg (f : C(Icc (0 : ℝ) T, Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, supportedReflection P S hS hSym (f t) = -f t)
    (ha₀ : supportedReflection P S hS hSym a₀ = -a₀) (t : Icc (0 : ℝ) T) :
    supportedReflection P S hS hSym (U.solution f a₀ t) = -U.solution f a₀ t := by
  have hfp : supportedPathReflection P S hS hSym f = -f := by
    apply ContinuousMap.ext
    exact hf
  have he := solution_reflection P S hS hSym T hT B hB U f a₀
  rw [hfp,ha₀,U.solution_neg] at he
  exact congrArg (fun p : C(Icc (0 : ℝ) T,Supported P V S hS) => p t) he


-- @@ L156-164 verbatim
include hB hSym in
theorem solution_full_reflection_neg (f : C(Icc (0 : ℝ) T, Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, reflection P (f t : CylinderL2 P V) = -(f t : CylinderL2 P V))
    (ha₀ : reflection P (a₀ : CylinderL2 P V) = -(a₀ : CylinderL2 P V)) (t : Icc (0 : ℝ) T) :
    reflection P (U.solution f a₀ t : CylinderL2 P V) = -(U.solution f a₀ t : CylinderL2 P V) := by
  have h := solution_reflection_neg P S hS hSym T hT B hB U f a₀
    (fun r => Subtype.ext (hf r)) (Subtype.ext ha₀) t
  exact congrArg (fun u : Supported P V S hS => (u : CylinderL2 P V)) h


-- @@ L166-166 verbatim
end EulerCylinderForwardParity


-- @@ L168-168 verbatim
end

-- @@ L169-169 verbatim
end


-- @@ L171-171 verbatim
end


-- @@ L173-173 verbatim
@[expose] public section


-- @@ L175-175 verbatim
noncomputable section


-- @@ L177-177 verbatim
namespace EulerSourceCylinderParity


-- @@ L179-183 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerMeanCoefficients
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderRectangular
  EulerSourceForwardCoefficient EulerBoundedFieldForwardGenerator EulerTransverseGramInverse
  EulerSourceCylinderForcing EulerSourceCylinderForward EulerSourceCylinderEquation
  EulerCylinderFieldReflection EulerCylinderForwardParity

-- @@ L184-184 verbatim
open scoped BoundedContinuousFunction


-- @@ L186-186 verbatim
section Coefficients


-- @@ L188-192 verbatim
variable {K U E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (Q Q₁ : SmoothCoefficientPath K (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)


-- @@ L194-196 verbatim
theorem sourceForcing_even (hE : ∀ t x, Q.field t (-x) = Q.field t x) (t : K) (x : Space) :
    sourceForcing Q c hc hQ t (-x) = sourceForcing Q c hc hQ t x := by
  simp only [sourceForcing, leftInversePath_apply, hE]


-- @@ L198-201 verbatim
theorem sourceGenerator_even (hE : ∀ t x, Q.field t (-x) = Q.field t x)
    (hE₁ : ∀ t x, Q₁.field t (-x) = Q₁.field t x) (t : K) (x : Space) :
    sourceGenerator Q Q₁ c hc hQ t (-x) = sourceGenerator Q Q₁ c hc hQ t x := by
  simp only [sourceGenerator, generatorPath_apply, hE, hE₁]


-- @@ L203-203 verbatim
end Coefficients


-- @@ L205-205 verbatim
section Evolution


-- @@ L207-218 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (S : Set Space) (hS : MeasurableSet S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : SmoothCoefficientPath (Icc (0 : ℝ) T) (U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x v, c * ‖v‖ ^ 2 ≤ ‖Q.field t x v‖ ^ 2)
  (hE : ∀ t x, Q.field t (-x) = Q.field t x)
  (hE₁ : ∀ t x, Q₁.field t (-x) = Q₁.field t x)
  (f : C(Icc (0 : ℝ) T, Supported P E S hS)) (a₀ : Supported P U S hS)
  (hf : ∀ t, reflection P (f t : CylinderL2 P E) = -(f t : CylinderL2 P E))
  (ha₀ : reflection P (a₀ : CylinderL2 P U) = -(a₀ : CylinderL2 P U))


-- @@ L220-226 verbatim
include hE hf in
theorem projectedForcing_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (projectedForcing P S hS Q c hc hQ f t : CylinderL2 P U) =
      -(projectedForcing P S hS Q c hc hQ f t : CylinderL2 P U) := by
  change reflection P (fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)) =
    -fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)
  rw [reflection_fullOperator P _ (sourceForcing_even Q c hc hQ hE t), hf, map_neg]


-- @@ L228-235 verbatim
include hSym hE hE₁ hf ha₀ in
theorem coordinates_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) =
      -(coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) :=
  solution_full_reflection_neg P S hS hSym T hT (sourceGenerator Q Q₁ c hc hQ)
    (sourceGenerator_even Q Q₁ c hc hQ hE hE₁)
    (evolution P T hT Q Q₁ c hc hQ S hS) (projectedForcing P S hS Q c hc hQ f) a₀
    (projectedForcing_reflection_neg P S hS T Q c hc hQ hE f hf) ha₀ t


-- @@ L237-245 verbatim
include hSym hE hE₁ hf ha₀ in
theorem velocity_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (velocity P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) =
      -(velocity P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) := by
  change reflection P (fullOperatorMap P (Q.field t)
      (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U)) = _
  rw [reflection_fullOperator P _ (hE t),
    coordinates_reflection_neg P S hS hSym T hT Q Q₁ c hc hQ hE hE₁ f a₀ hf ha₀, map_neg]
  rfl


-- @@ L247-259 verbatim
include hSym hE hE₁ hf ha₀ in
theorem coordinateDerivative_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) =
      -(coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) := by
  change reflection P
    (fullOperatorMap P (sourceGenerator Q Q₁ c hc hQ t)
        (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) +
      fullOperatorMap P (sourceForcing Q c hc hQ t) (f t : CylinderL2 P E)) = _
  rw [map_add, reflection_fullOperator P _ (sourceGenerator_even Q Q₁ c hc hQ hE hE₁ t),
    reflection_fullOperator P _ (sourceForcing_even Q c hc hQ hE t),
    coordinates_reflection_neg P S hS hSym T hT Q Q₁ c hc hQ hE hE₁ f a₀ hf ha₀,
    hf, map_neg, map_neg, ← neg_add]
  rfl


-- @@ L261-274 verbatim
include hSym hE hE₁ hf ha₀ in
theorem velocityDerivative_reflection_neg (t : Icc (0 : ℝ) T) :
    reflection P (velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) =
      -(velocityDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P E) := by
  change reflection P
    (fullOperatorMap P (Q₁.field t)
        (coordinates P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U) +
      fullOperatorMap P (Q.field t)
        (coordinateDerivative P S hS T hT Q Q₁ c hc hQ f a₀ t : CylinderL2 P U)) = _
  rw [map_add, reflection_fullOperator P _ (hE₁ t), reflection_fullOperator P _ (hE t),
    coordinates_reflection_neg P S hS hSym T hT Q Q₁ c hc hQ hE hE₁ f a₀ hf ha₀,
    coordinateDerivative_reflection_neg P S hS hSym T hT Q Q₁ c hc hQ hE hE₁ f a₀ hf ha₀,
    map_neg, map_neg, ← neg_add]
  rfl


-- @@ L276-276 verbatim
end Evolution

-- @@ L277-277 verbatim
end EulerSourceCylinderParity


-- @@ L279-279 verbatim
end

-- @@ L280-280 verbatim
end


-- @@ L282-282 verbatim
end


-- @@ L284-284 verbatim
@[expose] public section


-- @@ L286-286 verbatim
noncomputable section


-- @@ L288-288 verbatim
namespace EulerTransversePacketProvider


-- @@ L290-292 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerPacketProfileRecursion
  EulerPacketCylinderField EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerCylinderFieldReflection EulerTransverseBoundedFrame


-- @@ L294-294 verbatim
namespace Data


-- @@ L296-296 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)


-- @@ L298-302 verbatim
theorem frame_even (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) : D.frame.field t (-x) = D.frame.field t x := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [frame,coefficient_apply,hF]


-- @@ L304-308 verbatim
theorem frameDerivative_even (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) : D.frameDerivative.field t (-x) = D.frameDerivative.field t
        x := by
  rw [D.frame_strain,D.frame_strain,hM,D.frame_even hF]


-- @@ L310-318 verbatim
theorem inverse_even (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) : D.FInv.field t (-x) = D.FInv.field t x := by
  apply ContinuousLinearMap.ext
  intro v
  calc
    D.FInv.field t (-x) v = D.FInv.field t (-x) (D.F.field t x (D.FInv.field t x v)) := by
      rw [D.inverse_right]
    _ = D.FInv.field t (-x) (D.F.field t (-x) (D.FInv.field t x v)) := by rw [hF]
    _ = D.FInv.field t x v := D.inverse_left t (-x) _


-- @@ L320-323 verbatim
theorem normal_even (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) : D.normal.field t (-x) = D.normal.field t x := by
  change (D.FInv.field t (-x)).adjoint D.m₀ = (D.FInv.field t x).adjoint D.m₀
  rw [D.inverse_even hF]


-- @@ L325-325 verbatim
end Data


-- @@ L327-327 verbatim
namespace Forcing


-- @@ L329-331 verbatim
variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)


-- @@ L333-337 verbatim
/-- Forcing field, bundling `path`, `orbit`, `raw_eq`. -/
def forcingField : Field P D.T raw where
  path := includePath P D.support D.support_measurable G.path
  orbit := G.path_orbit
  raw_eq := G.raw_eq


-- @@ L339-344 verbatim
omit [CompleteSpace U] in
theorem path_reflection_neg
    (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))
    (t : Icc (0 : ℝ) D.T) :
    reflection P (G.path t : CylinderL2 P Space) = -(G.path t : CylinderL2 P Space) :=
  G.forcingField.reflection_neg_of_raw_odd t (hraw t)


-- @@ L346-350 verbatim
variable (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ)))
  (hinit : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U))


-- @@ L352-358 verbatim
include hSym hF hM hraw hinit in
theorem velocityPath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (G.fullVelocityPath I t) = -G.fullVelocityPath I t :=
  EulerSourceCylinderParity.velocity_reflection_neg P D.support D.support_measurable hSym
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    (D.frame_even hF) (D.frameDerivative_even hF hM) G.path I.value (G.path_reflection_neg hraw)
        hinit t


-- @@ L360-366 verbatim
include hSym hF hM hraw hinit in
theorem derivativePath_reflection_neg (t : Icc (0 : ℝ) D.T) :
    reflection P (G.fullDerivativePath I t) = -G.fullDerivativePath I t :=
  EulerSourceCylinderParity.velocityDerivative_reflection_neg P D.support D.support_measurable hSym
    D.T D.T_pos.le D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    (D.frame_even hF) (D.frameDerivative_even hF hM) G.path I.value (G.path_reflection_neg hraw)
        hinit t


-- @@ L368-372 verbatim
include hSym hF hM hraw hinit in
theorem vector_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.vector I (t,(-x,-θ)) = -G.vector I (t,(x,θ)) :=
  (G.vectorField I).raw_odd_of_reflection_neg t
    (G.velocityPath_reflection_neg I hSym hF hM hraw hinit t) x θ


-- @@ L374-378 verbatim
include hSym hF hM hraw hinit in
theorem vectorDerivative_odd (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.vectorDerivative I (t,(-x,-θ)) = -G.vectorDerivative I (t,(x,θ)) :=
  (G.vectorDerivativeField I).raw_odd_of_reflection_neg t
    (G.derivativePath_reflection_neg I hSym hF hM hraw hinit t) x θ


-- @@ L380-383 verbatim
include hSym hF hM hraw hinit in
theorem corrector_odd_of_data (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    G.corrector I (t,(-x,-θ)) = -G.corrector I (t,(x,θ)) :=
  G.corrector_odd I t (D.inverse_even hF t) (G.vector_odd I hSym hF hM hraw hinit t) x θ


-- @@ L385-385 verbatim
end Forcing

-- @@ L386-386 verbatim
end EulerTransversePacketProvider
