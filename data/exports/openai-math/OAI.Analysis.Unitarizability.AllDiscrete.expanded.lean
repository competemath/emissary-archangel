import Mathlib
import OAI.Analysis.Unitarizability.DiscreteModel
import OAI.Analysis.Unitarizability.NearOne
import OAI.Analysis.Unitarizability.Amenable


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
namespace Dixmier

-- @@ L10-10 verbatim
universe u v


-- @@ L12-24 verbatim
theorem current_main_theorem : CurrentMainTheorem.{u,v} := by
  intro G _ _ _
  constructor
  · constructor
    · intro hG
      exact amenable_unitarizable hG
    · intro hunit
      by_contra hnot
      obtain ⟨H, hnorm, hinner, hcomplete, π, _, hb, hn⟩ :=
        nonamenable_near_one_large.{u,v} hnot 1 zero_lt_one
      exact hn (@hunit H hnorm hinner hcomplete π ⟨1 + 1, hb⟩)
  · intro ε hε hG
    exact nonamenable_near_one_large.{u,v} hG ε hε


-- @@ L26-26 verbatim
end Dixmier

-- @@ L27-27 verbatim
end


-- @@ L29-29 verbatim
end OAI
