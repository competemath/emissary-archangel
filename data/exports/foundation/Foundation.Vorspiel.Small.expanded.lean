module

public import Mathlib.Logic.Small.Basic


-- @@ L5-6 verbatim
@[expose]
public section


-- @@ L8-8 verbatim
section Small


-- @@ L10-10 verbatim
variable {α : Type uα} {β : Type uβ}


-- @@ L12-14 verbatim
theorem small_preimage_of_injective (f : α → β) (h : Function.Injective f) (s : Set β) [Small.{u} s] :
    Small.{u} (f ⁻¹' s) := small_of_injective (β := s) (f := fun x ↦ ⟨f x, x.prop⟩) fun x y ↦ by
  simp [Function.Injective.eq_iff h, SetCoe.ext_iff]


-- @@ L16-16 verbatim
end Small


-- @@ L18-18 verbatim
end
