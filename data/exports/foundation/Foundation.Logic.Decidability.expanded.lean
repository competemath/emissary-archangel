module

public import Foundation.Logic.Entailment
public import Foundation.Vorspiel.Computability


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
namespace FFL.Entailment


-- @@ L10-10 verbatim
section


-- @@ L12-12 verbatim
variable {F S : Type*} [Primcodable F] [Entailment S F]


-- @@ L14-14 verbatim
variable (𝓢 : S)


-- @@ L16-17 verbatim
class Decidable where
  dec : ComputablePred (theory 𝓢)


-- @@ L19-19 verbatim
def Undecidable := ¬Decidable 𝓢


-- @@ L21-22 verbatim
class EssentiallyUndecidable [Tilde F] where
  essentially_undec : ∀ 𝓣 : S, 𝓢 ⪯ 𝓣 → Incomplete 𝓣 → Undecidable 𝓣


-- @@ L24-27 verbatim
variable {𝓢}

lemma decidable_of_incomplete : Inconsistent 𝓢 → Decidable 𝓢 :=
  fun h ↦ ⟨by rw [h.theory_eq]; exact ComputablePred.const _⟩


-- @@ L29-29 verbatim
end


-- @@ L31-31 verbatim
end FFL.Entailment


-- @@ L33-33 verbatim
end
