import OAI.Analysis.LipschitzEquivalence.CompactHilbertWSC


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
namespace LipschitzCounterexample


-- @@ L8-9 verbatim
theorem main : MainClaim :=
  SeparatingStages.main_of_free_wsc CompactWSC.hilbert_free_wsc


-- @@ L11-11 verbatim
end LipschitzCounterexample


-- @@ L13-13 verbatim
end


-- @@ L15-15 verbatim
end OAI
