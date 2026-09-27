/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.BlockFilters
public import LeanPool.Wallace.TransfiniteExtension
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order


-- @@ L18-29 verbatim
/-!
# Concrete triangular data and block-density ultrafilters

This module makes all global choices which are shared by the local character fusions.  For
arbitrary positive block sizes and arbitrary bounded-independence thresholds, it chooses the
prepared subsequence of every triangularly coded injective sequence.  It also transports the
standard continuum-sized almost-disjoint family to the canonical continuum index and chooses a
free block-density ultrafilter for every code.

The choices here are entirely set-theoretic.  No topology on the free group and no character is
assumed.
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
open Filter Set Topology


-- @@ L35-35 verbatim
namespace Wallace

-- @@ L36-36 verbatim
namespace ConcreteData


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
open TriangularPreprocess

-- @@ L41-41 verbatim
open BlockData

-- @@ L42-42 verbatim
open FiniteCombinatorics


-- @@ L44-44 verbatim
/-! ## The globally prepared sequences -/


-- @@ L46-46 verbatim
variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)


-- @@ L48-50 verbatim
/-- The strictly increasing subsequence selector supplied by block preprocessing. -/
def selector (a : ContinuumIndex) : ℕ → ℕ :=
  Classical.choose (triangular_block_preprocess a N hN M)


-- @@ L52-53 verbatim
theorem selector_strictMono (a : ContinuumIndex) : StrictMono (selector N hN M a) :=
  (Classical.choose_spec (triangular_block_preprocess a N hN M)).1


-- @@ L55-57 verbatim
/-- The prepared subsequence coded by `a`. -/
def prepared (a : ContinuumIndex) (n : ℕ) : ContinuumFreeGroup :=
  codedSequence a (selector N hN M a n)


-- @@ L59-61 verbatim
/-- The shifted finite set in block `l`. -/
def differenceBlock (a : ContinuumIndex) (l : ℕ) : Finset ContinuumFreeGroup :=
  (blockPositions N hN l).image fun n ↦ prepared N hN M a n - codeBasisVector a


-- @@ L63-65 verbatim
theorem differenceBlock_boundedIndependent (a : ContinuumIndex) (l : ℕ) :
    BoundedIndependent (M l) (differenceBlock N hN M a l) := by
  exact (Classical.choose_spec (triangular_block_preprocess a N hN M)).2.1 l |>.2


-- @@ L67-69 verbatim
theorem prepared_support_lt (a : ContinuumIndex) (n : ℕ) (i : ContinuumIndex)
    (hi : i ∈ (prepared N hN M a n).support) : i < codeIndex a := by
  exact (Classical.choose_spec (triangular_block_preprocess a N hN M)).2.2 n i hi


-- @@ L71-73 verbatim
theorem prepared_injective (a : ContinuumIndex) :
    Function.Injective (prepared N hN M a) :=
  (codedSequence_injective a).comp (selector_strictMono N hN M a).injective


-- @@ L75-81 verbatim
/-- Translating a prepared sequence by its prescribed basis point preserves injectivity. -/
theorem preparedDifference_injective (a : ContinuumIndex) :
    Function.Injective
      (fun n ↦ prepared N hN M a n - codeBasisVector a) := by
  intro m n hmn
  apply prepared_injective N hN M a
  exact sub_left_injective hmn


-- @@ L83-83 verbatim
/-! ## Packaging for the transfinite extension -/


-- @@ L85-91 verbatim
/-- The concrete triangular data used by the transfinite recursion. -/
def transfiniteData : TransfiniteExtension.ContinuumData where
  Code := ContinuumIndex
  codeIndex := codeIndex
  prepared := prepared N hN M
  support_lt := prepared_support_lt N hN M
  p := ultrafilter N hN


-- @@ L93-93 verbatim
end


-- @@ L95-95 verbatim
end ConcreteData

-- @@ L96-96 verbatim
end Wallace
