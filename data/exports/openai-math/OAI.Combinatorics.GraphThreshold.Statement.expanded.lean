import OAI.Combinatorics.GraphThreshold.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe u


-- @@ L9-9 verbatim
namespace LeanBlast.SecondKahnKalai


-- @@ L11-14 verbatim
def SecondKahnKalaiStatement : Prop :=
  ∀ (n : ℕ) (V : Type u) [Fintype V] (H : SimpleGraph V),
    2 ≤ n → Fintype.card V ≤ n → 1 ≤ edgeCount H →
      SecondKahnKalaiBounds n H


-- @@ L16-16 verbatim
end LeanBlast.SecondKahnKalai


-- @@ L18-18 verbatim
end


-- @@ L20-20 verbatim
end OAI
