/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.BlockFilters
public import LeanPool.Wallace.RationalTransfiniteExtension
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order


-- @@ L19-24 verbatim
/-!
# Concrete triangular data for the rational direct sum

This module chooses, uniformly for every coded injective rational sequence, its prepared
subsequence and its free block-density ultrafilter.
-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
open Filter Set Topology


-- @@ L30-30 verbatim
namespace Wallace

-- @@ L31-31 verbatim
namespace RationalData


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open RationalTriangularPreprocess

-- @@ L36-36 verbatim
open BlockData

-- @@ L37-37 verbatim
open FiniteCombinatorics


-- @@ L39-39 verbatim
variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)


-- @@ L41-43 verbatim
/-- Strictly increasing selector supplied by rational block preprocessing. -/
def selector (a : ContinuumIndex) : ℕ → ℕ :=
  Classical.choose (triangular_block_preprocess a N hN M)


-- @@ L45-46 verbatim
theorem selector_strictMono (a : ContinuumIndex) : StrictMono (selector N hN M a) :=
  (Classical.choose_spec (triangular_block_preprocess a N hN M)).1


-- @@ L48-50 verbatim
/-- Prepared subsequence represented by code `a`. -/
def prepared (a : ContinuumIndex) (n : ℕ) : ContinuumRationalGroup :=
  codedSequence a (selector N hN M a n)


-- @@ L52-55 verbatim
/-- Shifted finite set in block `l`. -/
def differenceBlock (a : ContinuumIndex) (l : ℕ) : Finset ContinuumRationalGroup :=
  (TriangularPreprocess.blockPositions N hN l).image fun n ↦
    prepared N hN M a n - codeBasisVector a


-- @@ L57-59 verbatim
theorem differenceBlock_boundedIndependent (a : ContinuumIndex) (l : ℕ) :
    BoundedIndependent (M l) (differenceBlock N hN M a l) := by
  exact (Classical.choose_spec (triangular_block_preprocess a N hN M)).2.1 l |>.2


-- @@ L61-63 verbatim
theorem prepared_support_lt (a : ContinuumIndex) (n : ℕ) (i : ContinuumIndex)
    (hi : i ∈ (prepared N hN M a n).support) : i < codeIndex a := by
  exact (Classical.choose_spec (triangular_block_preprocess a N hN M)).2.2 n i hi


-- @@ L65-67 verbatim
theorem prepared_injective (a : ContinuumIndex) :
    Function.Injective (prepared N hN M a) :=
  (codedSequence_injective a).comp (selector_strictMono N hN M a).injective


-- @@ L69-73 verbatim
theorem preparedDifference_injective (a : ContinuumIndex) :
    Function.Injective (fun n ↦ prepared N hN M a n - codeBasisVector a) := by
  intro m n hmn
  apply prepared_injective N hN M a
  exact sub_left_injective hmn


-- @@ L75-81 verbatim
/-- Concrete input for the rational transfinite recursion. -/
def transfiniteData : RationalTransfiniteExtension.ContinuumData where
  Code := ContinuumIndex
  codeIndex := codeIndex
  prepared := prepared N hN M
  support_lt := prepared_support_lt N hN M
  p := ultrafilter N hN


-- @@ L83-83 verbatim
end

-- @@ L84-84 verbatim
end RationalData

-- @@ L85-85 verbatim
end Wallace
