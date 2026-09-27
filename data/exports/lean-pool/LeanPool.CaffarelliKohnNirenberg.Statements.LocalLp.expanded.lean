/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic


-- @@ L11-15 verbatim
/-!
# Local Lp

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open MeasureTheory

-- @@ L20-20 verbatim
open scoped ENNReal

-- @@ L21-21 verbatim
open CKN.Foundation.Parabolic



-- @@ L24-24 verbatim
namespace CKN


-- @@ L26-28 verbatim
/-- Local scalar `Lp` membership used by paper label `def:sws`. -/
def localLp (E : Set ParabolicPoint) (p : ℝ) (g : ParabolicPoint → ℝ) : Prop :=
  MeasureTheory.MemLp g (ENNReal.ofReal p) (volume.restrict E)


-- @@ L30-30 verbatim
end CKN
