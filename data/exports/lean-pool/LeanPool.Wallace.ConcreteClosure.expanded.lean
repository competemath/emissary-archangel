/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.ConcreteData
public import LeanPool.Wallace.CountableClosure
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order


-- @@ L18-25 verbatim
/-!
# Concrete countable dependency closures

For a nonzero vector `x`, this module closes its finite support under all prepared sequences
whose fresh code coordinate has entered the closure.  The resulting coordinate set is
countable, contains the support of `x`, and has exactly the closure property required by the
transfinite character extension.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open Set


-- @@ L31-31 verbatim
namespace Wallace

-- @@ L32-32 verbatim
namespace ConcreteClosure


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
open TriangularPreprocess

-- @@ L37-37 verbatim
open ConcreteData


-- @@ L39-39 verbatim
variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)


-- @@ L41-43 verbatim
/-- The least closure obtained in finitely many dependency steps from the support of `x`. -/
def closure (x : ContinuumFreeGroup) : Set ContinuumIndex :=
  preparedClosure codeIndex (prepared N hN M) x


-- @@ L45-47 verbatim
theorem support_subset_closure (x : ContinuumFreeGroup) :
    ↑x.support ⊆ closure N hN M x :=
  support_subset_preparedClosure codeIndex (prepared N hN M) x


-- @@ L49-51 verbatim
theorem closure_countable (x : ContinuumFreeGroup) :
    (closure N hN M x).Countable :=
  preparedClosure_countable codeIndex (prepared N hN M) x


-- @@ L53-58 verbatim
/-- The closure contains every coordinate of each relevant prepared sequence. -/
theorem prepared_support_mem_closure (x : ContinuumFreeGroup)
    (a : ContinuumIndex) (ha : codeIndex a ∈ closure N hN M x)
    (n : ℕ) (i : ContinuumIndex) (hi : i ∈ (prepared N hN M a n).support) :
    i ∈ closure N hN M x :=
  preparedSupport_subset_preparedClosure codeIndex (prepared N hN M) x a ha n hi


-- @@ L60-64 verbatim
theorem closure_closedUnderPreparedSupports (x : ContinuumFreeGroup) :
    TransfiniteExtension.ClosedUnderPreparedSupports
      (transfiniteData N hN M) (closure N hN M x) := by
  intro a ha n i hi
  exact prepared_support_mem_closure N hN M x a ha n i hi


-- @@ L66-66 verbatim
end


-- @@ L68-68 verbatim
end ConcreteClosure

-- @@ L69-69 verbatim
end Wallace
