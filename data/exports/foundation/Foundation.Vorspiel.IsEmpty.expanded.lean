module

public import Mathlib.Logic.IsEmpty.Basic


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace IsEmpty

-- @@ L8-12 verbatim
variable {o : Sort u} (h : IsEmpty o)

lemma eq_elim' {α : Sort*} (f : o → α) : f = h.elim' := funext h.elim

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim := funext h.elim


-- @@ L14-14 verbatim
end IsEmpty


-- @@ L16-16 verbatim
end
