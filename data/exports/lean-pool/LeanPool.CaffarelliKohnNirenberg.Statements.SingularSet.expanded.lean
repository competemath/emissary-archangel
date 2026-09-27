/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint


-- @@ L10-14 verbatim
/-!
# Singular Set

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Set



-- @@ L21-21 verbatim
open CKN.Foundation.Parabolic


-- @@ L23-23 verbatim
namespace CKN


-- @@ L25-28 verbatim
/-- The singular set from paper label `def:regular`. -/
def SingularSet (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3) :
    Set ParabolicPoint :=
  {z | z ∈ spaceTimeSet Ω I ∧ ¬ IsRegularPoint Ω I u z}


-- @@ L30-30 verbatim
end CKN
