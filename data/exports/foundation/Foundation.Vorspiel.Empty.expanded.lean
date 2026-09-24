module

public import Mathlib.Data.Fintype.Basic


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-9 verbatim
namespace Empty

lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim := funext (by rintro ⟨⟩)


-- @@ L11-11 verbatim
end Empty


-- @@ L13-13 verbatim
end
