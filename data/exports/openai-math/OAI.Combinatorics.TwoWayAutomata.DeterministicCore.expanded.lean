import OAI.Combinatorics.TwoWayAutomata.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace TwoWayComplementation


-- @@ L7-9 verbatim
/-- At most one next-state/move pair at every state and scanned symbol. -/
def TwoNFA.Deterministic {Sigma Q : Type*} (A : TwoNFA Sigma Q) : Prop :=
  ∀ q symbol, (A.transition q symbol).Subsingleton


-- @@ L11-11 verbatim
end TwoWayComplementation


-- @@ L13-13 verbatim
end OAI
