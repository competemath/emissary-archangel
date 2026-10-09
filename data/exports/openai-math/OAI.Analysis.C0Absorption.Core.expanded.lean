import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace C0Absorption


-- @@ L8-8 verbatim
open scoped ZeroAtInfty


-- @@ L10-10 verbatim
abbrev C0 := C₀(ℕ, ℝ)


-- @@ L12-14 verbatim
def BiLip {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ x y, c * dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ C * dist x y


-- @@ L16-17 verbatim
def NoLinearC0 (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] : Prop :=
  ∀ T : C0 →L[ℝ] Z, ¬ ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖T x‖


-- @@ L19-21 verbatim
def MetricUniversal (Z : Type*) [MetricSpace Z] : Prop :=
  ∀ (M : Type) [MetricSpace M] [TopologicalSpace.SeparableSpace M],
    ∃ f : M → Z, BiLip f


-- @@ L23-28 verbatim
def MainConclusion : Prop :=
  ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℝ Z),
    CompleteSpace Z ∧ TopologicalSpace.SeparableSpace Z ∧ NoLinearC0 Z ∧
    (∃ F : Z × C0 → Z, Function.Surjective F ∧ BiLip F) ∧
    (∃ f : C0 → Z, BiLip f) ∧ MetricUniversal Z ∧
    ¬ Nonempty ((Z × C0) ≃L[ℝ] Z)


-- @@ L30-30 verbatim
end C0Absorption


-- @@ L32-32 verbatim
end OAI
