import OAI.Combinatorics.GraphThreshold.Resampling
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
/-! # Success and failure of a local resampling transition -/


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
namespace LeanBlast.SecondKahnKalai


-- @@ L13-13 verbatim
variable {X B : Type*} [DecidableEq X] [Fintype B]


-- @@ L15-20 verbatim
/-- The denominator is large enough and the retained fragment fits in the
halved integral capacity. -/
def LocalSuccess (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) : Prop :=
  Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (W ∪ A c) ∧
    (A b \ W).card ≤ m / 2


-- @@ L22-25 verbatim
/-- A local failure is the complement of the actual local success event. -/
def LocalFailure (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) : Prop :=
  ¬ LocalSuccess ν A ρ m W c b


-- @@ L27-32 verbatim
theorem localFailure_iff (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) :
    LocalFailure ν A ρ m W c b ↔
      resamplingZ ν A ρ (W ∪ A c) < Real.exp (-10 * (m : ℝ)) ∨
        m / 2 < (A b \ W).card := by
  simp only [LocalFailure, LocalSuccess, not_and_or, not_le]


-- @@ L34-41 verbatim
theorem localFailure_iff_twice (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) :
    LocalFailure ν A ρ m W c b ↔
      resamplingZ ν A ρ (W ∪ A c) < Real.exp (-10 * (m : ℝ)) ∨
        m < 2 * (A b \ W).card := by
  rw [localFailure_iff]
  apply or_congr Iff.rfl
  omega


-- @@ L43-43 verbatim
end LeanBlast.SecondKahnKalai


-- @@ L45-45 verbatim
end


-- @@ L47-47 verbatim
end OAI
