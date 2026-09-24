module

public import Foundation.Propositional.Formula.Basic
public import Foundation.Propositional.Entailment.Cl


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
namespace FFL.Propositional


-- @@ L10-10 verbatim
open FFL.Entailment

-- @@ L11-11 verbatim
open Entailment


-- @@ L13-17 verbatim
@[ext]
structure Logic (α) where
  logic : Set (Formula α)
  subst : ∀ s, ∀ φ ∈ logic, φ⟦s⟧ ∈ logic
  mdp : ∀ {φ ψ}, φ 🡒 ψ ∈ logic → φ ∈ logic → ψ ∈ logic


-- @@ L19-19 verbatim
namespace Logic


-- @@ L21-23 verbatim
instance : SetLike (Logic α) (Formula α) where
  coe := logic
  coe_injective _ _ := Logic.ext


-- @@ L25-26 verbatim
class IsTrivial (L : Logic α) : Prop where
  eq_univ : L.logic = Set.univ


-- @@ L28-29 verbatim
structure ExtensionOf (L : Logic α) extends Logic α where
  subset_L : ∀ {φ}, φ ∈ L → φ ∈ logic


-- @@ L31-31 verbatim
end Logic



-- @@ L34-34 verbatim
protected abbrev Trivial : Logic α := ⟨Set.univ, by tauto, by tauto⟩


-- @@ L36-36 verbatim
instance : (Propositional.Trivial : Logic α).IsTrivial  := ⟨rfl⟩



-- @@ L39-39 verbatim
end FFL.Propositional



-- @@ L42-42 verbatim
end
