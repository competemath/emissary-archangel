/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic


-- @@ L10-14 verbatim
/-!
# Morrey Vec Mem

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open MeasureTheory Set

-- @@ L19-19 verbatim
open scoped ENNReal

-- @@ L20-20 verbatim
open CKN.Foundation.Parabolic

-- @@ L21-21 verbatim
open CKN.Foundation.Parabolic.Morrey



-- @@ L24-24 verbatim
namespace CKN


-- @@ L26-30 verbatim
/-- Componentwise parabolic Morrey membership used by paper label `def:parabolic-morrey`. -/
def morreyVecMem (P τ : ℝ) (S : Set ParabolicPoint)
    (u : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3,
    morreyBallNorm P τ (S.indicator (fun z => u z i)) < ∞


-- @@ L32-32 verbatim
end CKN
