/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Tactic.Positivity.Finset


-- @@ L12-17 verbatim
/-!
# Shared definitions for external theorem compatibility

These mirror definitions from the source project so external theorems can be
stated and proved using the same types.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open Filter Topology Metric InnerProductSpace


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace PLAcceleratedNesterovLean


-- @@ L27-27 verbatim
/-! ## Ambient space -/


-- @@ L29-30 verbatim
/-- The ambient Euclidean space ℝ^d (matching PLAcceleratedNesterovLean). -/
abbrev Ed (d : ℕ) := EuclideanSpace ℝ (Fin d)


-- @@ L32-32 verbatim
/-! ## Tubular neighborhoods -/


-- @@ L34-40 verbatim
/-- A tubular neighborhood of S is an open set U ⊇ S such that every
    point in U has a unique nearest point in S. -/
structure IsTubularNeighborhood {E : Type*} [PseudoMetricSpace E]
    (S U : Set E) : Prop where
  isOpen : IsOpen U
  subset : S ⊆ U
  uniqueProj : ∀ x ∈ U, ∃! p, p ∈ S ∧ dist x p = Metric.infDist x S


-- @@ L42-42 verbatim
/-! ## Optimization definitions -/


-- @@ L44-44 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


-- @@ L46-47 verbatim
/-- The set of global minimizers of f. -/
def Ext.argminSet (f : E → ℝ) : Set E := {x | ∀ y, f x ≤ f y}


-- @@ L49-50 verbatim
/-- The infimal value f⋆ = inf_x f(x). -/
def Ext.fStar (f : E → ℝ) : ℝ := ⨅ x, f x


-- @@ L52-54 verbatim
/-- μ-PŁ condition using ‖fderiv‖ (PLMB compatibility layer). -/
def Ext.PolyakLojasiewicz (f : E → ℝ) (μ : ℝ) (U : Set E) : Prop :=
  0 < μ ∧ ∀ x ∈ U, ‖fderiv ℝ f x‖ ^ 2 ≥ 2 * μ * (f x - Ext.fStar f)


-- @@ L56-58 verbatim
/-- The gradient of f at x (Riesz representative of fderiv ℝ f x). -/
def Ext.gradient (f : E → ℝ) (x : E) : E :=
  (toDual ℝ E).symm (fderiv ℝ f x)


-- @@ L60-62 verbatim
/-- The Hessian quadratic form ξᵀ D²f(x) ξ = ⟨D(∇f)(x)·ξ, ξ⟩. -/
def Ext.hessianQuadForm (f : E → ℝ) (x ξ : E) : ℝ :=
  @inner ℝ E _ (fderiv ℝ (Ext.gradient f) x ξ) ξ


-- @@ L64-64 verbatim
end PLAcceleratedNesterovLean
