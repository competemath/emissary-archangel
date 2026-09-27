/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L13-19 verbatim
/-!
# Elementary facts about analytic function germs

The public theorem represents germs by functions modulo `=ᶠ[𝓝 x]`.  These
lemmas record the corresponding ring-theoretic unit fact without introducing a
separate sheaf or stalk API into the public statement.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
open Filter

-- @@ L24-24 verbatim
open scoped Topology



-- @@ L27-27 verbatim
namespace ClassicalComplexWPT


-- @@ L29-38 verbatim
/-- A representative which is eventually nonzero defines a unit in the function-germ ring. -/
theorem germ_isUnit_of_eventually_ne {X : Type*} {l : Filter X} {g : X → ℂ}
    (hg : ∀ᶠ x in l, g x ≠ 0) : IsUnit (g : Filter.Germ l ℂ) := by
  refine ⟨⟨(g : Filter.Germ l ℂ), (g⁻¹ : Filter.Germ l ℂ), ?_, ?_⟩, rfl⟩
  · apply Filter.Germ.coe_eq.mpr
    filter_upwards [hg] with x hx
    exact mul_inv_cancel₀ hx
  · apply Filter.Germ.coe_eq.mpr
    filter_upwards [hg] with x hx
    exact inv_mul_cancel₀ hx


-- @@ L40-45 verbatim
/-- A nonvanishing analytic germ is a ring-theoretic unit. -/
theorem analytic_germ_isUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℂ} {x : E} (hg : AnalyticAt ℂ g x) (hg0 : g x ≠ 0) :
    IsUnit (g : Filter.Germ (𝓝 x) ℂ) := by
  apply germ_isUnit_of_eventually_ne
  exact hg.continuousAt.eventually_ne hg0


-- @@ L47-47 verbatim
end ClassicalComplexWPT
