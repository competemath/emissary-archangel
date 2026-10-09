import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace CliqueFreeLog


-- @@ L7-9 verbatim
noncomputable def averageDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ := by
  classical
  exact 2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)


-- @@ L11-11 verbatim
end CliqueFreeLog


-- @@ L13-13 verbatim
end OAI
