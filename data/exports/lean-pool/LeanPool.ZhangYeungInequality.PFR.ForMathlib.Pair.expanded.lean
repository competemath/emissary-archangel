/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Util.Notation3


-- @@ L11-15 verbatim
/-!
# LeanPool.ZhangYeungInequality.PFR.ForMathlib.Pair

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.PFR.ForMathlib.Pair`.
-/


-- @@ L17-17 verbatim
public section


-- @@ L19-20 verbatim
/-- The pair of two random variables -/
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)


-- @@ L22-22 verbatim
@[inherit_doc prod] scoped[ZhangYeungPFR] notation3:100 "⟨" X ", " Y "⟩" => prod X Y


-- @@ L24-24 verbatim
open scoped ZhangYeungPFR


-- @@ L26-28 expanded
@[simp]
lemma prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    (⟨X, Y⟩ : Ω → S × T) ω = (X ω, Y ω) :=
  rfl

