/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta


-- @@ L10-14 verbatim
/-!
# Coefficients

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Ideal


-- @@ L20-20 verbatim
namespace NumberField.Odlyzko


-- @@ L22-22 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L24-26 verbatim
/-- An ideal norm count used in the Odlyzko-bound argument. -/
noncomputable def idealNormCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // absNorm I = n}


-- @@ L28-30 verbatim
lemma dedekindZeta_eq_LSeries_idealNormCount (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (idealNormCount K n : ℂ)) s :=
  rfl


-- @@ L32-32 verbatim
end NumberField.Odlyzko
