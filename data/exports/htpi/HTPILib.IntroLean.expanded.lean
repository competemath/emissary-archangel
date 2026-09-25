/- Copyright 2023-2025 Daniel J. Velleman -/

import HTPILib.HTPIDefs

-- @@ L4-4 verbatim
namespace HTPI


-- @@ L6-13 expanded
theorem Example_3_2_4 (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) :=
  by
  assume h2 : ¬R
  assume h3 : P
  have h4 : Q → R := h h3
  contrapos at h4
  { show ¬Q; exact h4 h2
  }
  done


-- @@ L15-15 verbatim
theorem extremely_easy (P : Prop) (h : P) : P := h


-- @@ L17-18 verbatim
theorem very_easy
    (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2


-- @@ L20-21 verbatim
theorem easy (P Q R : Prop) (h1 : P → Q)
    (h2 : Q → R) (h3 : P) : R := h2 (h1 h3)


-- @@ L23-29 expanded
theorem two_imp (P Q R : Prop) (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P :=
  by
  contrapos --Goal is now P → ¬R
    
  assume h3 : P
  have h4 : Q := h1 h3
  { show ¬R; exact h2 h4
  }
  done


-- @@ L31-38 expanded
theorem Example_3_2_5_simple (B C : Set Nat) (a : Nat) (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C :=
  by
  define at h2
  demorgan at h2; conditional at h2
  { show a ∈ C; exact h2 h1
  }
  done


-- @@ L40-46 expanded
theorem Example_3_2_5_simple_general (U : Type) (B C : Set U) (a : U) (h1 : a ∈ B)
    (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2; conditional at h2
  { show a ∈ C; exact h2 h1
  }
  done

