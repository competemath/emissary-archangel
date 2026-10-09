import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise


-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-17 verbatim
/-!
# Containment covers and expectation thresholds

Both costs use budget one half. Fractional coefficients are indexed by every
subset of the ground set, without a support-size bound. The empty subset is
included, and ordinary natural powers give `p^0 = 1`, including at zero.
The thresholds are real suprema of feasible densities in the closed unit interval.
-/


-- @@ L19-19 verbatim
namespace TalagrandThreshold


-- @@ L21-21 verbatim
open scoped BigOperators


-- @@ L23-23 verbatim
abbrev Family (α : Type*) := Finset (Finset α)


-- @@ L25-25 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
def cost (p : ℝ) (G : Family α) : ℝ := ∑ S ∈ G, p ^ S.card


-- @@ L31-31 verbatim
def Covers (G F : Family α) : Prop := ∀ H ∈ F, ∃ S ∈ G, S ⊆ H


-- @@ L33-34 verbatim
def Small (p : ℝ) (F : Family α) : Prop :=
  ∃ G : Family α, Covers G F ∧ cost p G ≤ 1 / 2


-- @@ L36-37 verbatim
def fracCost (p : ℝ) (g : Finset α → ℝ) : ℝ :=
  ∑ S : Finset α, g S * p ^ S.card


-- @@ L39-41 verbatim
def FractionalCover (F : Family α) (g : Finset α → ℝ) : Prop :=
  (∀ S, 0 ≤ g S ∧ g S ≤ 1) ∧
    ∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, g S


-- @@ L43-44 verbatim
def FractionalSmall (p : ℝ) (F : Family α) : Prop :=
  ∃ g : Finset α → ℝ, FractionalCover F g ∧ fracCost p g ≤ 1 / 2


-- @@ L46-47 verbatim
def Increasing (F : Family α) : Prop :=
  ∀ H ∈ F, ∀ K : Finset α, H ⊆ K → K ∈ F


-- @@ L49-50 verbatim
def integralFeasible (F : Family α) : Set ℝ :=
  {p | 0 ≤ p ∧ p ≤ 1 ∧ Small p F}


-- @@ L52-53 verbatim
def fractionalFeasible (F : Family α) : Set ℝ :=
  {p | 0 ≤ p ∧ p ≤ 1 ∧ FractionalSmall p F}


-- @@ L55-56 verbatim
/-- The integral expectation threshold. -/
def q (F : Family α) : ℝ := sSup (integralFeasible F)


-- @@ L58-59 verbatim
/-- The fractional expectation threshold. -/
def qf (F : Family α) : ℝ := sSup (fractionalFeasible F)


-- @@ L61-63 verbatim
omit [Fintype α] [DecidableEq α] in
@[simp] theorem mem_integralFeasible {F : Family α} {p : ℝ} :
    p ∈ integralFeasible F ↔ 0 ≤ p ∧ p ≤ 1 ∧ Small p F := Iff.rfl


-- @@ L65-67 verbatim
omit [DecidableEq α] in
@[simp] theorem mem_fractionalFeasible {F : Family α} {p : ℝ} :
    p ∈ fractionalFeasible F ↔ 0 ≤ p ∧ p ≤ 1 ∧ FractionalSmall p F := Iff.rfl


-- @@ L69-69 verbatim
end

-- @@ L70-70 verbatim
end TalagrandThreshold


-- @@ L72-72 verbatim
end OAI
