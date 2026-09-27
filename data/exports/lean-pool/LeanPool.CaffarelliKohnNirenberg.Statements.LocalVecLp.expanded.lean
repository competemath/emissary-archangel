/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.LocalLp


-- @@ L10-14 verbatim
/-!
# Local Vec Lp

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open CKN.Foundation.Parabolic



-- @@ L21-21 verbatim
namespace CKN


-- @@ L23-26 verbatim
/-- Componentwise local vector `Lp` membership used by paper label `def:sws`. -/
def localVecLp (E : Set ParabolicPoint) (p : ℝ)
    (g : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3, localLp E p (fun z => g z i)


-- @@ L28-28 verbatim
end CKN
