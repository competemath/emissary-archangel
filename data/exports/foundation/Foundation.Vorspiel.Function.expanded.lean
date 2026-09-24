module

public import Mathlib.Data.Fintype.Basic


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace Function


-- @@ L9-9 verbatim
variable  {α : Type u} {β : Type v}


-- @@ L11-14 verbatim
def funEqOn (φ : α → Prop) (f g : α → β) : Prop := ∀ a, φ a → f a = g a

lemma funEqOn.of_subset {φ ψ : α → Prop} {f g : α → β} (e : funEqOn φ f g) (h : ∀ a, ψ a → φ a) : funEqOn ψ f g :=
  by intro a ha; exact e a (h a ha)


-- @@ L16-16 verbatim
end Function


-- @@ L18-18 verbatim
end
