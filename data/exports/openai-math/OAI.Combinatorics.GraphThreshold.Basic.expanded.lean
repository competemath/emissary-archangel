import OAI.Combinatorics.GraphThreshold.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace LeanBlast.SecondKahnKalai


-- @@ L9-12 verbatim
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1


-- @@ L14-14 verbatim
namespace FiniteLaw


-- @@ L16-17 verbatim
def expectation {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * f ω


-- @@ L19-21 verbatim
def prob {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.weight ω else 0


-- @@ L23-24 verbatim
def IsPositive {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) : Prop :=
  ∀ ω, 0 < μ.weight ω


-- @@ L26-26 verbatim
end FiniteLaw


-- @@ L28-30 verbatim
def IsSpread {X B : Type*} [DecidableEq X] [Fintype B]
    (μ : FiniteLaw B) (A : B → Finset X) (a : ℝ) : Prop :=
  ∀ J : Finset X, J.Nonempty → μ.prob (fun b => J ⊆ A b) ≤ a ^ J.card


-- @@ L32-32 verbatim
end LeanBlast.SecondKahnKalai


-- @@ L34-34 verbatim
end


-- @@ L36-36 verbatim
end OAI
