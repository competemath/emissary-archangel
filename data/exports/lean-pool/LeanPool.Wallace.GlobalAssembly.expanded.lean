/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.ConcreteClosure
public import LeanPool.Wallace.SeparationInterface
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order


-- @@ L19-28 verbatim
/-!
# From the local fusions to the Wallace counterexample

This module performs the final global assembly.  Its only input is the output of the countable
fusion: for each nonzero vector, a character on its concrete countable dependency closure which
detects that vector and satisfies the prescribed ultrafilter limits for all codes internal to the
closure.  The transfinite recursion extends each such character to the whole free group and
makes it admissible at every code.  The resulting characters form a separating family, so the
minimal construction interface yields the Wallace semigroup.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
open Filter Set Topology


-- @@ L34-34 verbatim
namespace Wallace

-- @@ L35-35 verbatim
namespace GlobalAssembly


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
open TriangularPreprocess

-- @@ L40-40 verbatim
open ConcreteData

-- @@ L41-41 verbatim
open BlockData

-- @@ L42-42 verbatim
open ConcreteClosure

-- @@ L43-43 verbatim
open TransfiniteExtension


-- @@ L45-45 verbatim
variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)


-- @@ L47-52 verbatim
/-- The exact local output required from the countable fusion. -/
def HasLocalSeparatingCharacters : Prop :=
  ∀ x : {x : ContinuumFreeGroup // x ≠ 0},
    ∃ χD : (closure N hN M x.1 →₀ ℤ) →+ UnitAddCircle,
      χD (Finsupp.subtypeDomain (closure N hN M x.1) x.1) ≠ 0 ∧
        LocallyAdmissible (transfiniteData N hN M) (closure N hN M x.1) χD


-- @@ L54-54 verbatim
variable (H : HasLocalSeparatingCharacters N hN M)


-- @@ L56-59 verbatim
/-- The chosen local character for a nonzero vector. -/
def localCharacter (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    (closure N hN M x.1 →₀ ℤ) →+ UnitAddCircle :=
  Classical.choose (H x)


-- @@ L61-64 verbatim
theorem localCharacter_self_ne_zero (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    localCharacter N hN M H x
      (Finsupp.subtypeDomain (closure N hN M x.1) x.1) ≠ 0 :=
  (Classical.choose_spec (H x)).1


-- @@ L66-69 verbatim
theorem localCharacter_admissible (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    LocallyAdmissible (transfiniteData N hN M) (closure N hN M x.1)
      (localCharacter N hN M H x) :=
  (Classical.choose_spec (H x)).2


-- @@ L71-75 verbatim
/-- Extend the chosen local character by the well-founded triangular recursion. -/
def globalCharacter (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    ContinuumFreeGroup →+ UnitAddCircle :=
  TransfiniteExtension.globalCharacter (transfiniteData N hN M)
    (closure N hN M x.1) (localCharacter N hN M H x)


-- @@ L77-82 verbatim
theorem globalCharacter_self_ne_zero (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    globalCharacter N hN M H x x.1 ≠ 0 := by
  rw [globalCharacter,
    TransfiniteExtension.globalCharacter_eq_local_restriction]
  · exact localCharacter_self_ne_zero N hN M H x
  · exact support_subset_closure N hN M x.1


-- @@ L84-94 verbatim
theorem globalCharacter_admissible (x : {x : ContinuumFreeGroup // x ≠ 0})
    (a : ContinuumIndex) :
    Tendsto
      (fun n ↦ globalCharacter N hN M H x (prepared N hN M a n))
      (ultrafilter N hN a)
      (nhds (globalCharacter N hN M H x (codeBasisVector a))) := by
  exact TransfiniteExtension.globalCharacter_admissible
    (transfiniteData N hN M) (closure N hN M x.1)
    (localCharacter N hN M H x)
    (closure_closedUnderPreparedSupports N hN M x.1)
    (localCharacter_admissible N hN M H x) a


-- @@ L96-109 verbatim
/-- The completely concrete separating package obtained from the local fusion theorem. -/
def separationPackage : SeparationPackage ContinuumIndex where
  Code := ContinuumIndex
  codeEquiv := sequenceCodeEquiv
  codeIndex := codeIndex
  subsequence := selector N hN M
  subsequence_strictMono := selector_strictMono N hN M
  ultrafilter := ultrafilter N hN
  ultrafilter_free := ultrafilter_free N hN
  character := globalCharacter N hN M H
  character_self_ne_zero := globalCharacter_self_ne_zero N hN M H
  character_limit := by
    intro a x
    exact globalCharacter_admissible N hN M H x a


-- @@ L111-111 verbatim
end


-- @@ L113-113 verbatim
end GlobalAssembly

-- @@ L114-114 verbatim
end Wallace
