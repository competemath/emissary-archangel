/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import Mathlib.Geometry.Manifold.PartitionOfUnity


-- @@ L11-16 verbatim
/-!
# Uniqueness of weak partial derivatives

Locally integrable weak partial derivatives of the same function on an open
set agree almost everywhere.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open MeasureTheory Set Filter

-- @@ L21-21 verbatim
open scoped Topology BigOperators



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace CKN


-- @@ L28-34 verbatim
/-- Locally integrable weak partial derivatives of the same function agree almost everywhere. -/
theorem hasWeakPartialDerivOn_unique_ae {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {f g h : Vec d → ℝ}
    (hgLoc : LocallyIntegrableOn g U volume) (hhLoc : LocallyIntegrableOn h U volume)
    (hg : HasWeakPartialDerivOn U i f g) (hh : HasWeakPartialDerivOn U i f h) :
    g =ᵐ[volume.restrict U] h :=
  HasWeakPartialDerivOn.ae_eq hU hgLoc hhLoc hg hh


-- @@ L36-36 verbatim
end CKN
