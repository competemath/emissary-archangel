module

public import Mathlib.Util.Notation3
public import Mathlib.Tactic.Basic


-- @@ L6-6 verbatim
public section


-- @@ L8-9 verbatim
/-- The pair of two random variables -/
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)


-- @@ L11-11 verbatim
@[inherit_doc prod] notation3:100 "⟨" X ", " Y "⟩" => prod X Y


-- @@ L13-15 expanded
@[simp]
lemma prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    (⟨X, Y⟩ : Ω → S × T) ω = (X ω, Y ω) :=
  rfl

