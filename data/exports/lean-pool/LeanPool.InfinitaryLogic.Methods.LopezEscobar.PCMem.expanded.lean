/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Methods.Interpolation.GraphLanguage
public import LeanPool.InfinitaryLogic.Methods.LopezEscobar.WitnessLang
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability.Init
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

-- @@ L15-22 verbatim
/-!
# The López–Escobar PC-class interface (issue #10, Unit 4 commit 1)

The base embedding `baseGraphEmb : L →ᴸ graphLanguage (KLang L)` (available because `L` is
relational), and the code compatibility theorem tying the abstract `PCMem` on `ℕ` to
membership in `codeReduct '' ModelsOf Θ`.  This freezes the PC-class interface independently
of López–Escobar's tree machinery.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace FirstOrder.Language


-- @@ L28-28 verbatim
open FirstOrder Structure Set


-- @@ L30-30 verbatim
variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]


-- @@ L32-36 verbatim
/-- The base embedding of `L` into the relationalized `graphLanguage (KLang L)`: functions are
vacuous (`L` is relational), base relations go to their graph-language base image. -/
def baseGraphEmb : L →ᴸ graphLanguage (KLang L) where
  onFunction {_} f := isEmptyElim f
  onRelation {_} R := GraphRelation.base (Sum.inl R)


-- @@ L38-38 verbatim
end FirstOrder.Language
