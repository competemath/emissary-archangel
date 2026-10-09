import OAI.Combinatorics.TwoWayAutomata.DeterministicCore
import OAI.Combinatorics.TwoWayAutomata.Main


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace TwoWayComplementation


-- @@ L8-14 verbatim
theorem TwoNFA.Deterministic.reindex {Sigma Q Q' : Type*} {A : TwoNFA Sigma Q}
    (hA : A.Deterministic) (e : Q ≃ Q') : (A.reindex e).Deterministic := by
  intro q symbol a ha b hb
  have h := hA (e.symm q) symbol ha hb
  apply Prod.ext
  · exact e.symm.injective (congrArg (fun t : Q × Fin 3 => t.1) h)
  · exact congrArg (fun t : Q × Fin 3 => t.2) h


-- @@ L16-19 verbatim
theorem TwoNFA.Deterministic.pullAlphabet {Sigma Gamma Q : Type*} {A : TwoNFA Gamma Q}
    (hA : A.Deterministic) (f : Sigma → Gamma) : (A.pullAlphabet f).Deterministic := by
  intro q symbol
  exact hA q (Sum.map id f symbol)


-- @@ L21-21 verbatim
end TwoWayComplementation


-- @@ L23-23 verbatim
end OAI
