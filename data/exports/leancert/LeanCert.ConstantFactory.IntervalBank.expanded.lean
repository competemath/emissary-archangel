/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

import LeanCert.ConstantFactory
import LeanCert.Engine.Integrate


-- @@ L10-23 verbatim
/-!
# Interval Kernel Banks for ConstantFactory

This module adds the interval analogue of the exact ConstantFactory observer
identity.  A `KernelIntervalBank R` supplies certified intervals for the base
moments `moment R m`; a finite perturbation `Q` is then checked by summing the
signed scaled kernel intervals.

The first implementation follows the existing powerset observer representation:

`F (R ∪ Q) = ∑ A ∈ Q.powerset, subsetSign A * moment R (subsetWeight A)`.

Coefficient-compressed perturbation polynomials can be layered on top later.
-/


-- @@ L25-25 verbatim
namespace LeanCert.ConstantFactory


-- @@ L27-27 verbatim
open LeanCert.Core

-- @@ L28-28 verbatim
open LeanCert.QProduct

-- @@ L29-29 verbatim
open LeanCert.Engine


-- @@ L31-36 verbatim
/-- Certified interval enclosures for all monomial moments of a base profile `R`. -/
structure KernelIntervalBank (R : Finset Nat) where
  /-- Interval enclosure for `moment R m`. -/
  interval : Nat → IntervalRat
  /-- Soundness of each interval enclosure. -/
  correct : ∀ m, moment R m ∈ interval m


-- @@ L38-40 verbatim
/-- Semantic contribution of one perturbation subset. -/
noncomputable def observerTerm (R : Finset Nat) (A : Finset Nat) : ℝ :=
  (subsetSign A : ℝ) * moment R (subsetWeight A)


-- @@ L42-45 verbatim
/-- Interval contribution of one perturbation subset. -/
def observerIntervalTerm {R : Finset Nat} (bank : KernelIntervalBank R)
    (A : Finset Nat) : IntervalRat :=
  IntervalRat.scale (subsetSign A) (bank.interval (subsetWeight A))


-- @@ L47-49 verbatim
/-- Semantic observer sum over an explicit subset list. -/
noncomputable def observerIntegralList (R : Finset Nat) (terms : List (Finset Nat)) : ℝ :=
  (terms.map (observerTerm R)).sum


-- @@ L51-55 verbatim
/-- Interval observer sum over an explicit subset list. -/
def observerIntervalList {R : Finset Nat} (bank : KernelIntervalBank R) :
    List (Finset Nat) → IntervalRat
  | [] => IntervalRat.singleton 0
  | A :: rest => IntervalRat.add (observerIntervalTerm bank A) (observerIntervalList bank rest)


-- @@ L57-60 verbatim
/-- Interval observer certificate for perturbation `Q`, using the existing powerset basis. -/
noncomputable def observerInterval {R : Finset Nat} (Q : Finset Nat) (bank : KernelIntervalBank R) :
    IntervalRat :=
  observerIntervalList bank Q.powerset.toList


-- @@ L62-66 verbatim
theorem observerTerm_mem_interval {R : Finset Nat} (bank : KernelIntervalBank R)
    (A : Finset Nat) :
    observerTerm R A ∈ observerIntervalTerm bank A := by
  unfold observerTerm observerIntervalTerm
  exact IntervalRat.mem_scale (subsetSign A) (bank.correct (subsetWeight A))


-- @@ L68-78 verbatim
/-- List-level interval observer soundness. -/
theorem observerIntegralList_mem_observerIntervalList {R : Finset Nat}
    (bank : KernelIntervalBank R) :
    ∀ terms, observerIntegralList R terms ∈ observerIntervalList bank terms
  | [] => by
      simpa [observerIntegralList, observerIntervalList] using
        (IntervalRat.mem_singleton (0 : ℚ))
  | A :: rest => by
      simp only [observerIntegralList, observerIntervalList, List.map_cons, List.sum_cons]
      exact IntervalRat.mem_add (observerTerm_mem_interval bank A)
        (observerIntegralList_mem_observerIntervalList bank rest)


-- @@ L80-86 verbatim
theorem observerIntegralList_powerset_eq (R Q : Finset Nat) :
    observerIntegralList R Q.powerset.toList = observerIntegral R Q := by
  classical
  simp [observerIntegralList, observerIntegral, observerTerm]
  apply Finset.sum_congr rfl
  intro A _
  rfl


-- @@ L88-99 verbatim
/--
Interval ConstantFactory identity.

If a bank encloses every base moment of `R`, then the product integral for every
disjoint finite perturbation `Q` lies in the signed interval observer sum.
-/
theorem F_union_mem_observerInterval {R Q : Finset Nat} (hdisj : Disjoint R Q)
    (bank : KernelIntervalBank R) :
    F (R ∪ Q) ∈ observerInterval Q bank := by
  rw [F_union_eq_observerIntegral R Q hdisj]
  rw [← observerIntegralList_powerset_eq R Q]
  exact observerIntegralList_mem_observerIntervalList bank Q.powerset.toList


-- @@ L101-106 verbatim
/-- Exact rational moments as a degenerate interval bank. -/
def exactKernelIntervalBank (R : Finset Nat) : KernelIntervalBank R where
  interval m := IntervalRat.singleton (momentRat R m)
  correct m := by
    rw [← momentRat_correct R m]
    exact IntervalRat.mem_singleton (momentRat R m)


-- @@ L108-108 verbatim
end LeanCert.ConstantFactory
