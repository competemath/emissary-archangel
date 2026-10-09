import OAI.Combinatorics.ExpectationThreshold.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-12 verbatim
/-!
# Elementary bounds for the actual expectation thresholds

When the empty set is absent from the family, zero is feasible for both
thresholds. Their feasible sets are bounded by one, and indicator covers
give the integral-to-fractional comparison.
-/


-- @@ L14-14 verbatim
namespace TalagrandThreshold


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L20-23 verbatim
omit [Fintype α] [DecidableEq α] in
theorem integralFeasible_subset_Icc (F : Family α) :
    integralFeasible F ⊆ Set.Icc (0 : ℝ) 1 :=
  fun _ hp => ⟨hp.1, hp.2.1⟩


-- @@ L25-28 verbatim
omit [DecidableEq α] in
theorem fractionalFeasible_subset_Icc (F : Family α) :
    fractionalFeasible F ⊆ Set.Icc (0 : ℝ) 1 :=
  fun _ hp => ⟨hp.1, hp.2.1⟩


-- @@ L30-32 verbatim
omit [Fintype α] [DecidableEq α] in
theorem integralFeasible_bddAbove (F : Family α) : BddAbove (integralFeasible F) :=
  ⟨1, fun _ hp => hp.2.1⟩


-- @@ L34-36 verbatim
omit [DecidableEq α] in
theorem fractionalFeasible_bddAbove (F : Family α) : BddAbove (fractionalFeasible F) :=
  ⟨1, fun _ hp => hp.2.1⟩


-- @@ L38-41 verbatim
omit [Fintype α] [DecidableEq α] in
theorem zero_mem_integralFeasible (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    (0 : ℝ) ∈ integralFeasible F :=
  ⟨le_rfl, zero_le_one, small_zero F hF⟩


-- @@ L43-45 verbatim
theorem zero_mem_fractionalFeasible (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    (0 : ℝ) ∈ fractionalFeasible F :=
  ⟨le_rfl, zero_le_one, fractionalSmall_zero F hF⟩


-- @@ L47-50 verbatim
omit [Fintype α] [DecidableEq α] in
theorem integralFeasible_nonempty (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    (integralFeasible F).Nonempty :=
  ⟨0, zero_mem_integralFeasible F hF⟩


-- @@ L52-54 verbatim
theorem fractionalFeasible_nonempty (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    (fractionalFeasible F).Nonempty :=
  ⟨0, zero_mem_fractionalFeasible F hF⟩


-- @@ L56-61 verbatim
omit [Fintype α] [DecidableEq α] in
/-- Integral feasibility is preserved by lowering the nonnegative density. -/
theorem integralFeasible_mono {F : Family α} {p r : ℝ}
    (hr : r ∈ integralFeasible F) (hp : 0 ≤ p) (hpr : p ≤ r) :
    p ∈ integralFeasible F :=
  ⟨hp, hpr.trans hr.2.1, hr.2.2.mono hp hpr⟩


-- @@ L63-68 verbatim
omit [DecidableEq α] in
/-- Fractional feasibility is preserved by lowering the nonnegative density. -/
theorem fractionalFeasible_mono {F : Family α} {p r : ℝ}
    (hr : r ∈ fractionalFeasible F) (hp : 0 ≤ p) (hpr : p ≤ r) :
    p ∈ fractionalFeasible F :=
  ⟨hp, hpr.trans hr.2.1, hr.2.2.mono hp hpr⟩


-- @@ L70-72 verbatim
theorem integralFeasible_subset_fractionalFeasible (F : Family α) :
    integralFeasible F ⊆ fractionalFeasible F :=
  fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.fractionalSmall⟩


-- @@ L74-77 verbatim
omit [Fintype α] [DecidableEq α] in
theorem le_q_of_mem {F : Family α} {p : ℝ} (hp : p ∈ integralFeasible F) :
    p ≤ q F :=
  le_csSup (integralFeasible_bddAbove F) hp


-- @@ L79-82 verbatim
omit [DecidableEq α] in
theorem le_qf_of_mem {F : Family α} {p : ℝ} (hp : p ∈ fractionalFeasible F) :
    p ≤ qf F :=
  le_csSup (fractionalFeasible_bddAbove F) hp


-- @@ L84-87 verbatim
omit [Fintype α] [DecidableEq α] in
theorem le_q_of_small {F : Family α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : Small p F) : p ≤ q F :=
  le_q_of_mem ⟨hp0, hp1, hp⟩


-- @@ L89-92 verbatim
omit [DecidableEq α] in
theorem le_qf_of_fractionalSmall {F : Family α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : FractionalSmall p F) : p ≤ qf F :=
  le_qf_of_mem ⟨hp0, hp1, hp⟩


-- @@ L94-96 verbatim
omit [Fintype α] [DecidableEq α] in
theorem q_nonneg (F : Family α) (hF : (∅ : Finset α) ∉ F) : 0 ≤ q F :=
  le_q_of_mem (zero_mem_integralFeasible F hF)


-- @@ L98-99 verbatim
theorem qf_nonneg (F : Family α) (hF : (∅ : Finset α) ∉ F) : 0 ≤ qf F :=
  le_qf_of_mem (zero_mem_fractionalFeasible F hF)


-- @@ L101-103 verbatim
omit [Fintype α] [DecidableEq α] in
theorem q_le_one (F : Family α) (hF : (∅ : Finset α) ∉ F) : q F ≤ 1 :=
  csSup_le (integralFeasible_nonempty F hF) (fun _ hp => hp.2.1)


-- @@ L105-106 verbatim
theorem qf_le_one (F : Family α) (hF : (∅ : Finset α) ∉ F) : qf F ≤ 1 :=
  csSup_le (fractionalFeasible_nonempty F hF) (fun _ hp => hp.2.1)


-- @@ L108-110 verbatim
theorem q_le_qf (F : Family α) (hF : (∅ : Finset α) ∉ F) : q F ≤ qf F :=
  csSup_le_csSup (fractionalFeasible_bddAbove F) (integralFeasible_nonempty F hF)
    (integralFeasible_subset_fractionalFeasible F)


-- @@ L112-112 verbatim
end

-- @@ L113-113 verbatim
end TalagrandThreshold


-- @@ L115-115 verbatim
end OAI
