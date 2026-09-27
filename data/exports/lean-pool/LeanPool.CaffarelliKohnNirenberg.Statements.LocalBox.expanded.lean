/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic


-- @@ L10-14 verbatim
/-!
# Local Box

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Set

-- @@ L19-19 verbatim
open CKN.Foundation.Parabolic



-- @@ L22-22 verbatim
namespace CKN


-- @@ L24-27 verbatim
/-- Compactly interior spatial and time subdomains used by paper label `def:sws`. -/
def localBox (Ω : Set Vec3) (I : Set ℝ) (Ω' : Set Vec3) (J : Set ℝ) : Prop :=
  IsOpen Ω' ∧ IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω ∧
    OrdConnected J ∧ IsCompact (closure J) ∧ closure J ⊆ I


-- @@ L29-29 verbatim
end CKN
