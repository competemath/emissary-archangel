/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.SuperSymmetry.SU5.ChargeSpectrum.PhenoClosed
public import Physlib.StringTheory.FTheory.SU5.Charges.OfRationalSection

-- @@ L10-94 verbatim
/-!

# Charges which are not pheno-constrained and do not regenerate dangerous couplings with Yukawas

## i. Overview

WARNING: This file can take a long time to compute.

In this module, given a configuration of the sections in codimension one
fiber `CodimensionOneConfig`, we find the multiset of all
`ℤ`-valued charges which have values allowed by the configuration,
permit a top Yukawa coupling, are not phenomenologically constrained,
and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

The multiset of charge spectrum is called `viableCharges`.
The main proof that `viableCharges` contains all such charges is
using `completeness_of_isPhenoClosedQ5_isPhenoClosedQ10`.
Note this proof relies on us stating `viableCharges` and then verifying
that it has the required properties.

To make our lives easier, we first construct a multiset of charge spectrum called
`viableCompletions` which contains all completions of charges which minimally allow the top Yukawa,
which are not phenomenologically constrained, and do not regenerate dangerous couplings.
Again the proof that `viableCompletions` has these properties is done by
first stating `viableCompletions` and then verifying that it has the required properties,
primarily using `ContainsPhenoCompletionsOfMinimallyAllows`.

We also define `viableChargesAdditional` which are the multiset of charge spectrum
which are in `viableCharges` but not in `viableCompletions`. This helps split some of the
proofs.

Note that this file is slow to run, any improvements to the speed of this file
will be very welcome. In particular working out a way to restrict by anomaly cancellation.

## ii. Key results

- `viableCharges` contains all charges, for a given `CodimensionOneConfig`, `I`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.
- The lemma `mem_viableCharges_iff` expresses membership of `viableCharges I`, i.e.
  that it contains all charges which permit a top Yukawa coupling,
  are not phenomenologically constrained, and do not regenerate dangerous couplings.
- The lemma `mem_viableCharges_iff` follows directly from
  `completeness_of_isPhenoClosedQ5_isPhenoClosedQ10`
  and a number of conditions on `viableCharges` which can be proved using the `decide`
  tactic.
- `viableCharges` itself is constructed via `viableCompletions` which
  contains all completions of charges which minimally allow the top Yukawa,
  which are not phenomenologically constrained, and do not regenerate dangerous couplings.

## iii. Table of contents

- A. Viable completions of charges permitting a top Yukawa coupling
  - A.1. Stating the multiset `viableCompletions`
  - A.2. Cardinality of `viableCompletions`
  - A.3. No duplicates of `viableCompletions`
  - A.4. Elements of `viableCompletions` are not pheno-constrained
  - A.5. Elements of `viableCompletions` do not regenerate dangerous couplings
  - A.6. `viableCompletions` contain all pheno-viable completions of top-yukawa permitting
- B. The multiset of additional viable charges
  - B.1. Stating the multiset `viableChargesAdditional`
  - B.2. `viableChargesAdditional` has no duplicates
  - B.3. Elements of `viableChargesAdditional` are not pheno-constrained
  - B.4. Elements of `viableChargesAdditional` do not regenerate dangerous couplings
  - B.5. `viableChargesAdditional` is disjoint from `viableCompletions`
- C. The multiset of all viable charges given a configuration of sections
  - C.1. Stating the multiset `viableCharges`
  - C.2. `viableCharges` has no duplicates
  - C.3. Cardinality of `viableCharges`
  - C.4. Elements of `viableCharges` have charges allowed by configuration
  - C.5. Elements of `viableCharges` are complete
  - C.6. Elements of `viableCharges` permit a top Yukawa coupling
  - C.7. Elements of `viableCharges` are not pheno-constrained
  - C.8. Elements of `viableCharges` do not regenerate dangerous couplings
  - C.9. Elements of `viableCharges` have at most two 5-bar reps
  - C.10. Elements of `viableCharges` have at most two 10d reps
  - C.11. `viableCharges` is phenomenologically closed under adding 5-bar charges
  - C.12. `viableCharges` is phenomenologically closed under adding 10d charges
  - C.13. `viableCompletions` is a subset of `viableCharges`
  - C.14. `viableCharges` contains all pheno-viable charges given a section configuration

## iv. References

* None.
-/


-- @@ L96-96 verbatim
@[expose] public section

-- @@ L97-97 verbatim
namespace FTheory


-- @@ L99-99 verbatim
namespace SU5


-- @@ L101-101 verbatim
namespace ChargeSpectrum

-- @@ L102-102 verbatim
open SuperSymmetry.SU5

-- @@ L103-103 verbatim
open SuperSymmetry.SU5.ChargeSpectrum

-- @@ L104-104 verbatim
open PotentialTerm

-- @@ L105-105 verbatim
open CodimensionOneConfig

-- @@ L106-106 verbatim
open Physlib


-- @@ L108-112 verbatim
/-!

## A. Viable completions of charges permitting a top Yukawa coupling

-/


-- @@ L114-118 verbatim
/-!

### A.1. Stating the multiset `viableCompletions`

-/


-- @@ L120-228 verbatim
/--
The multiset of charges which are completions of charges which minimally allow the top Yukawa,
  which are not phenomenologically constrained, and do not regenerate dangerous couplings.

This can be constructed via

`#eval completeMinSubset same.allowedBarFiveCharges same.allowedTenCharges`
-/
def viableCompletions (I : CodimensionOneConfig) : Multiset (ChargeSpectrum ℤ) :=
  match I with
  | same => {
    /- qHu = -3, and Q10 = {-3, 0} -/
    ⟨some (-2), some (-3), {2}, {-3, 0}⟩, ⟨some (-1), some (-3), {1}, {-3, 0}⟩,
    ⟨some 1, some (-3), {-1}, {-3, 0}⟩, ⟨some 1, some (-3), {2}, {-3, 0}⟩,
    ⟨some 2, some (-3), {-2}, {-3, 0}⟩, ⟨some 2, some (-3), {1}, {-3, 0}⟩,
    /- qHu = -2, and Q10 = {-1} -/
    ⟨some (-3), some (-2), {0}, {-1}⟩, ⟨some (-3), some (-2), {1}, {-1}⟩,
    ⟨some (-3), some (-2), {2}, {-1}⟩, ⟨some (-1), some (-2), {0}, {-1}⟩,
    ⟨some (-1), some (-2), {1}, {-1}⟩, ⟨some (-1), some (-2), {2}, {-1}⟩,
    ⟨some 0, some (-2), {-3}, {-1}⟩, ⟨some 0, some (-2), {-1}, {-1}⟩,
    ⟨some 0, some (-2), {1}, {-1}⟩, ⟨some 0, some (-2), {2}, {-1}⟩,
    ⟨some 1, some (-2), {-3}, {-1}⟩, ⟨some 1, some (-2), {-1}, {-1}⟩,
    ⟨some 1, some (-2), {0}, {-1}⟩, ⟨some 1, some (-2), {2}, {-1}⟩,
    ⟨some 2, some (-2), {-3}, {-1}⟩, ⟨some 2, some (-2), {-1}, {-1}⟩,
    ⟨some 2, some (-2), {0}, {-1}⟩, ⟨some 2, some (-2), {1}, {-1}⟩,
    /- qHu = -2, and Q10 = {-2, 0} -/
    ⟨some (-3), some (-2), {3}, {-2, 0}⟩, ⟨some (-1), some (-2), {3}, {-2, 0}⟩,
    ⟨some 3, some (-2), {-3}, {-2, 0}⟩,
    /- qHu = -2, and Q10 = {-3, 1} -/
    ⟨some (-1), some (-2), {0}, {-3, 1}⟩,⟨some 0, some (-2), {-1}, {-3, 1}⟩,
    ⟨some 0, some (-2), {3}, {-3, 1}⟩, ⟨some 3, some (-2), {0}, {-3, 1}⟩,
    /- qHu = 0, and Q10 = {-3, 3} -/
    ⟨some (-2), some 0, {-1}, {-3, 3}⟩, ⟨some (-2), some 0, {1}, {-3, 3}⟩,
    ⟨some (-1), some 0, {-2}, {-3, 3}⟩, ⟨some (-1), some 0, {2}, {-3, 3}⟩,
    ⟨some 1, some 0, {-2}, {-3, 3}⟩, ⟨some 1, some 0, {2}, {-3, 3}⟩,
    ⟨some 2, some 0, {-1}, {-3, 3}⟩, ⟨some 2, some 0, {1}, {-3, 3}⟩,
    /- qHu = 2, and Q10 = {1} -/
    ⟨some (-2), some 2, {-1}, {1}⟩, ⟨some (-2), some 2, {0}, {1}⟩, ⟨some (-2), some 2, {1}, {1}⟩,
    ⟨some (-2), some 2, {3}, {1}⟩, ⟨some (-1), some 2, {-2}, {1}⟩, ⟨some (-1), some 2, {0}, {1}⟩,
    ⟨some (-1), some 2, {1}, {1}⟩, ⟨some (-1), some 2, {3}, {1}⟩, ⟨some 0, some 2, {-2}, {1}⟩,
    ⟨some 0, some 2, {-1}, {1}⟩, ⟨some 0, some 2, {1}, {1}⟩, ⟨some 0, some 2, {3}, {1}⟩,
    ⟨some 1, some 2, {-2}, {1}⟩, ⟨some 1, some 2, {-1}, {1}⟩, ⟨some 1, some 2, {0}, {1}⟩,
    ⟨some 3, some 2, {-2}, {1}⟩, ⟨some 3, some 2, {-1}, {1}⟩, ⟨some 3, some 2, {0}, {1}⟩,
    /- qHu = 2, and Q10 = {0, 2} -/
    ⟨some (-3), some 2, {3}, {0, 2}⟩, ⟨some 1, some 2, {-3}, {0, 2}⟩,
    ⟨some 3, some 2, {-3}, {0, 2}⟩,
    /- qHu = 2, and Q10 = {-1, 3} -/
    ⟨some (-3), some 2, {0}, {-1, 3}⟩, ⟨some 0, some 2, {-3}, {-1, 3}⟩,
    ⟨some 0, some 2, {1}, {-1, 3}⟩, ⟨some 1, some 2, {0}, {-1, 3}⟩,
    /- qHu = 3, and Q10 = {0, 3} -/
    ⟨some (-2), some 3, {-1}, {0, 3}⟩, ⟨some (-2), some 3, {2}, {0, 3}⟩,
    ⟨some (-1), some 3, {-2}, {0, 3}⟩, ⟨some (-1), some 3, {1}, {0, 3}⟩,
    ⟨some 1, some 3, {-1}, {0, 3}⟩, ⟨some 2, some 3, {-2}, {0, 3}⟩}
  | nearestNeighbor => {
    /- qHu = -14, and Q10 = {-7} -/
    ⟨some (-9), some (-14), {-4}, {-7}⟩, ⟨some (-9), some (-14), {1}, {-7}⟩,
    ⟨some (-9), some (-14), {6}, {-7}⟩, ⟨some (-9), some (-14), {11}, {-7}⟩,
    ⟨some (-4), some (-14), {-9}, {-7}⟩, ⟨some (-4), some (-14), {1}, {-7}⟩,
    ⟨some (-4), some (-14), {6}, {-7}⟩, ⟨some (-4), some (-14), {11}, {-7}⟩,
    ⟨some 1, some (-14), {-9}, {-7}⟩, ⟨some 1, some (-14), {-4}, {-7}⟩,
    ⟨some 1, some (-14), {6}, {-7}⟩, ⟨some 1, some (-14), {11}, {-7}⟩,
    ⟨some 6, some (-14), {-9}, {-7}⟩, ⟨some 6, some (-14), {-4}, {-7}⟩,
    ⟨some 6, some (-14), {1}, {-7}⟩, ⟨some 6, some (-14), {11}, {-7}⟩,
    ⟨some 11, some (-14), {-9}, {-7}⟩, ⟨some 11, some (-14), {-4}, {-7}⟩,
    ⟨some 11, some (-14), {1}, {-7}⟩, ⟨some 11, some (-14), {6}, {-7}⟩,
    /- qHu = -14, and Q10 = {-12, -2} -/
    ⟨some 11, some (-14), {-9}, {-12, -2}⟩,
    /- qHu = -9, and Q10 = {-12, 3} -/
    ⟨some 1, some (-9), {11}, {-12, 3}⟩, ⟨some 11, some (-9), {1}, {-12, 3}⟩,
    /- qHu = -4, and Q10 = {-2} -/
    ⟨some (-14), some (-4), {-9}, {-2}⟩, ⟨some (-14), some (-4), {11}, {-2}⟩,
    ⟨some (-9), some (-4), {-14}, {-2}⟩, ⟨some (-9), some (-4), {11}, {-2}⟩,
    ⟨some 1, some (-4), {-14}, {-2}⟩, ⟨some 1, some (-4), {11}, {-2}⟩,
    ⟨some 11, some (-4), {-14}, {-2}⟩, ⟨some 11, some (-4), {-9}, {-2}⟩,
    /- qHu = 1, and Q10 = {-12, 13} -/
    ⟨some (-9), some 1, {-4}, {-12, 13}⟩, ⟨some (-4), some 1, {-9}, {-12, 13}⟩,
    ⟨some 6, some 1, {-9}, {-12, 13}⟩,
    /- qHu = 6, and Q10 = {3} -/
    ⟨some (-14), some 6, {-4}, {3}⟩, ⟨some (-14), some 6, {1}, {3}⟩,
    ⟨some (-14), some 6, {11}, {3}⟩, ⟨some (-4), some 6, {-14}, {3}⟩,
    ⟨some (-4), some 6, {1}, {3}⟩, ⟨some (-4), some 6, {11}, {3}⟩,
    ⟨some 1, some 6, {-14}, {3}⟩, ⟨some 1, some 6, {-4}, {3}⟩,
    ⟨some 11, some 6, {-14}, {3}⟩, ⟨some 11, some 6, {-4}, {3}⟩,
    /- qHu = 6, and Q10 = {-7, 13} -/
    ⟨some (-9), some 6, {-4}, {-7, 13}⟩, ⟨some (-4), some 6, {-9}, {-7, 13}⟩,
    ⟨some (-4), some 6, {11}, {-7, 13}⟩, ⟨some 11, some 6, {-4}, {-7, 13}⟩}
  | nextToNearestNeighbor => {
    /- qHu = -8, and Q10 = {-4} -/
    ⟨some (-13), some (-8), {7}, {-4}⟩, ⟨some (-3), some (-8), {7}, {-4}⟩,
    ⟨some 2, some (-8), {-13}, {-4}⟩, ⟨some 2, some (-8), {-3}, {-4}⟩,
    ⟨some 2, some (-8), {7}, {-4}⟩, ⟨some 7, some (-8), {-13}, {-4}⟩,
    ⟨some 7, some (-8), {-3}, {-4}⟩,
    /- qHu = 2, and Q10 = {1} -/
    ⟨some (-13), some 2, {-8}, {1}⟩, ⟨some (-13), some 2, {7}, {1}⟩,
    ⟨some (-13), some 2, {12}, {1}⟩, ⟨some (-8), some 2, {-13}, {1}⟩,
    ⟨some (-8), some 2, {7}, {1}⟩, ⟨some 7, some 2, {-13}, {1}⟩, ⟨some 7, some 2, {-8}, {1}⟩,
    ⟨some 7, some 2, {12}, {1}⟩, ⟨some 12, some 2, {-13}, {1}⟩, ⟨some 12, some 2, {7}, {1}⟩,
    /- qHu = 2, and Q10 = {-9, 11} -/
    ⟨some (-8), some 2, {-3}, {-9, 11}⟩, ⟨some (-3), some 2, {-8}, {-9, 11}⟩,
    ⟨some (-3), some 2, {12}, {-9, 11}⟩, ⟨some 12, some 2, {-3}, {-9, 11}⟩,
    /- qHu = 12, and Q10 = {6} -/
    ⟨some (-13), some 12, {-8}, {6}⟩, ⟨some (-13), some 12, {2}, {6}⟩,
    ⟨some (-13), some 12, {7}, {6}⟩, ⟨some (-8), some 12, {-13}, {6}⟩,
    ⟨some (-8), some 12, {2}, {6}⟩, ⟨some (-8), some 12, {7}, {6}⟩,
    ⟨some (-3), some 12, {-13}, {6}⟩, ⟨some (-3), some 12, {-8}, {6}⟩,
    ⟨some (-3), some 12, {2}, {6}⟩, ⟨some (-3), some 12, {7}, {6}⟩,
    ⟨some 2, some 12, {-13}, {6}⟩, ⟨some 2, some 12, {-8}, {6}⟩,
    ⟨some 2, some 12, {7}, {6}⟩, ⟨some 7, some 12, {-13}, {6}⟩,
    ⟨some 7, some 12, {-8}, {6}⟩, ⟨some 7, some 12, {2}, {6}⟩}


-- @@ L230-234 verbatim
/-!

### A.2. Cardinality of `viableCompletions`

-/


-- @@ L236-239 verbatim
lemma viableCompletions_card (I : CodimensionOneConfig) :
    (viableCompletions I).card = if I = same then 70 else
      if I = nearestNeighbor then 48 else 37 := by
  cases I <;> rfl


-- @@ L241-245 verbatim
/-!

### A.3. No duplicates of `viableCompletions`

-/


-- @@ L247-249 verbatim
lemma viableCompletions_nodup (I : CodimensionOneConfig) :
    (viableCompletions I).Nodup := by
  cases I <;> decide +kernel


-- @@ L251-255 verbatim
/-!

### A.4. Elements of `viableCompletions` are not pheno-constrained

-/


-- @@ L257-259 verbatim
lemma viableCompletions_isPhenoConstrained (I : CodimensionOneConfig) :
    ∀ x ∈ viableCompletions I, ¬ IsPhenoConstrained x := by
  cases I <;> decide +kernel


-- @@ L261-265 verbatim
/-!

### A.5. Elements of `viableCompletions` do not regenerate dangerous couplings

-/


-- @@ L267-269 verbatim
lemma viableCompletions_yukawaGeneratesDangerousAtLevel_one (I : CodimensionOneConfig) :
    ∀ x ∈ viableCompletions I, ¬ YukawaGeneratesDangerousAtLevel x 1 := by
  cases I <;> decide +kernel


-- @@ L271-275 verbatim
/-!

### A.6. `viableCompletions` contain all pheno-viable completions of top-yukawa permitting

-/


-- @@ L277-281 verbatim
lemma containsPhenoCompletionsOfMinimallyAllows_viableCompletions :
    (I : CodimensionOneConfig) →
    ContainsPhenoCompletionsOfMinimallyAllows I.allowedBarFiveCharges
      I.allowedTenCharges (viableCompletions I) := by
  decide +kernel


-- @@ L283-287 verbatim
/-!

## B. The multiset of additional viable charges

-/


-- @@ L289-293 verbatim
/-!

### B.1. Stating the multiset `viableChargesAdditional`

-/


-- @@ L295-342 verbatim
/-- The charges in addition to `viableCompletions` which which permit a top Yukawa coupling,
  are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

  These can be found with e.g.
  - #eval (viableChargesMultiset same.allowedBarFiveCharges same.allowedTenCharges).toFinset \
    (completeMinSubset same.allowedBarFiveCharges
      same.allowedTenCharges).toFinset
-/
def viableChargesAdditional : CodimensionOneConfig → Multiset (ChargeSpectrum ℤ)
  | .same =>
    {⟨some 1, some (-3), {-1, 2}, {-3, 0}⟩, ⟨some 2, some (-3), {-2, 1}, {-3, 0}⟩,
      ⟨some (-3), some (-2), {0}, {3, -1}⟩, ⟨some (-3), some (-2), {0, 2}, {-1}⟩,
      ⟨some (-3), some (-2), {2}, {-3, -1}⟩, ⟨some (-1), some (-2), {0, 2}, {-1}⟩,
      ⟨some 0, some (-2), {-3}, {3, -1}⟩, ⟨some 0, some (-2), {-3, 1}, {-1}⟩,
      ⟨some 0, some (-2), {1}, {3, -1}⟩, ⟨some 1, some (-2), {0}, {3, -1}⟩,
      ⟨some 2, some (-2), {-3}, {-3, -1}⟩, ⟨some 2, some (-2), {-3, -1}, {-1}⟩,
      ⟨some 2, some (-2), {-3, 0}, {-1}⟩, ⟨some 2, some (-2), {-1, 1}, {-1}⟩,
      ⟨some 0, some (-2), {-1, 3}, {-3, 1}⟩, ⟨some (-2), some 2, {-1, 1}, {1}⟩,
      ⟨some (-2), some 2, {0, 3}, {1}⟩, ⟨some (-2), some 2, {1, 3}, {1}⟩,
      ⟨some (-2), some 2, {3}, {3, 1}⟩, ⟨some (-1), some 2, {0}, {-3, 1}⟩,
      ⟨some 0, some 2, {-1}, {-3, 1}⟩, ⟨some 0, some 2, {-1, 3}, {1}⟩,
      ⟨some 0, some 2, {3}, {-3, 1}⟩, ⟨some 1, some 2, {-2, 0}, {1}⟩,
      ⟨some 3, some 2, {-2}, {3, 1}⟩, ⟨some 3, some 2, {-2, 0}, {1}⟩,
      ⟨some 3, some 2, {0}, {-3, 1}⟩, ⟨some 0, some 2, {-3, 1}, {-1, 3}⟩,
      ⟨some (-2), some 3, {-1, 2}, {0, 3}⟩, ⟨some (-1), some 3, {-2, 1}, {0, 3}⟩,
      ⟨some 0, some (-2), {-3, 1}, {3, -1}⟩, ⟨some 0, some 2, {-1, 3}, {-3, 1}⟩}
  | .nearestNeighbor =>
      {⟨some (-9), some (-14), {-4}, {13, -7}⟩, ⟨some (-9), some (-14), {-4, 6}, {-7}⟩,
      ⟨some (-4), some (-14), {-9}, {13, -7}⟩, ⟨some (-4), some (-14), {-9, 6}, {-7}⟩,
      ⟨some (-4), some (-14), {-9, 11}, {-7}⟩, ⟨some (-4), some (-14), {6, 11}, {-7}⟩,
      ⟨some (-4), some (-14), {11}, {13, -7}⟩, ⟨some 1, some (-14), {-4, 6}, {-7}⟩,
      ⟨some 6, some (-14), {-9, -4}, {-7}⟩, ⟨some 6, some (-14), {-4}, {-12, -7}⟩,
      ⟨some 6, some (-14), {-9, 1}, {-7}⟩, ⟨some 6, some (-14), {1, 11}, {-7}⟩,
      ⟨some 11, some (-14), {-9, -4}, {-7}⟩, ⟨some 11, some (-14), {-4}, {13, -7}⟩,
      ⟨some 11, some (-14), {-4, 1}, {-7}⟩, ⟨some 11, some (-14), {-9, 6}, {-7}⟩,
      ⟨some (-9), some (-4), {-14, 11}, {-2}⟩, ⟨some (-9), some (-4), {11}, {-12, -2}⟩,
      ⟨some 1, some (-4), {-14, 11}, {-2}⟩, ⟨some (-14), some 6, {1, 11}, {3}⟩,
      ⟨some 11, some 6, {-14, -4}, {3}⟩, ⟨some (-4), some 6, {-9, 11}, {-7, 13}⟩,
      ⟨some (-4), some (-14), {-9, 11}, {13, -7}⟩}
  | .nextToNearestNeighbor =>
      {⟨some (-13), some 2, {-8, 12}, {1}⟩, ⟨some (-8), some 2, {-13, 7}, {1}⟩,
      ⟨some 7, some 2, {-8, 12}, {1}⟩, ⟨some 12, some 2, {-13, 7}, {1}⟩,
      ⟨some (-3), some 2, {-8, 12}, {-9, 11}⟩, ⟨some (-13), some 12, {-8}, {-9, 6}⟩,
      ⟨some (-13), some 12, {-8, 7}, {6}⟩, ⟨some (-13), some 12, {7}, {-4, 6}⟩,
      ⟨some (-8), some 12, {-13}, {-9, 6}⟩, ⟨some (-8), some 12, {-13, 2}, {6}⟩,
      ⟨some (-8), some 12, {2, 7}, {6}⟩, ⟨some 2, some 12, {-13, -8}, {6}⟩,
      ⟨some 2, some 12, {-8, 7}, {6}⟩, ⟨some 7, some 12, {-13, 2}, {6}⟩}


-- @@ L344-348 verbatim
/-!

### B.2. `viableChargesAdditional` has no duplicates

-/


-- @@ L350-352 verbatim
lemma viableChargesAdditional_nodup (I : CodimensionOneConfig) :
    (viableChargesAdditional I).Nodup := by
  cases I <;> decide +kernel


-- @@ L354-358 verbatim
/-!

### B.3. Elements of `viableChargesAdditional` are not pheno-constrained

-/


-- @@ L360-362 verbatim
lemma not_isPhenoConstrained_of_mem_viableChargesAdditional (I : CodimensionOneConfig) :
    ∀ x ∈ (viableChargesAdditional I), ¬ IsPhenoConstrained x := by
  cases I <;> decide +kernel


-- @@ L364-368 verbatim
/-!

### B.4. Elements of `viableChargesAdditional` do not regenerate dangerous couplings

-/


-- @@ L370-373 verbatim
lemma yukawaGeneratesDangerousAtLevel_one_of_mem_viableChargesAdditional
    (I : CodimensionOneConfig) :
    ∀ x ∈ (viableChargesAdditional I), ¬ YukawaGeneratesDangerousAtLevel x 1 := by
  cases I <;> decide +kernel


-- @@ L375-379 verbatim
/-!

### B.5. `viableChargesAdditional` is disjoint from `viableCompletions`

-/


-- @@ L381-385 verbatim
lemma viableCompletions_disjiont_viableChargesAdditional (I : CodimensionOneConfig) :
    Disjoint (viableCompletions I) (viableChargesAdditional I) := by
  refine Multiset.inter_eq_zero_iff_disjoint.mp ?_
  cases I
  <;> decide +kernel


-- @@ L387-391 verbatim
/-!

## C. The multiset of all viable charges given a configuration of sections

-/


-- @@ L393-397 verbatim
/-!

### C.1. Stating the multiset `viableCharges`

-/


-- @@ L399-406 verbatim
/-- All charges, for a given `CodimensionOneConfig`, `I`,
  which permit a top Yukawa coupling, are not phenomenologically constrained,
  and do not regenerate dangerous couplings with one insertion of a Yukawa coupling.

  These trees can be found with e.g.
  `#eval viableChargesExt nextToNearestNeighbor`. -/
def viableCharges (I : CodimensionOneConfig) : Multiset (ChargeSpectrum ℤ) :=
  viableCompletions I + viableChargesAdditional I


-- @@ L408-412 verbatim
/-!

### C.2. `viableCharges` has no duplicates

-/


-- @@ L414-416 verbatim
lemma viableCharges_nodup (I : CodimensionOneConfig) :
    (viableCharges I).Nodup := (Multiset.Nodup.add_iff (viableCompletions_nodup I)
    (viableChargesAdditional_nodup I)).mpr (viableCompletions_disjiont_viableChargesAdditional I)


-- @@ L418-422 verbatim
/-!

### C.3. Cardinality of `viableCharges`

-/


-- @@ L424-428 verbatim
lemma viableCharges_card (I : CodimensionOneConfig) :
    (viableCharges I).card =
    if I = .same then 102 else
    if I = .nearestNeighbor then 71 else 51 := by
  decide +revert


-- @@ L430-434 verbatim
/-!

### C.4. Elements of `viableCharges` have charges allowed by configuration

-/


-- @@ L436-440 verbatim
lemma viableCharges_mem_ofFinset (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges := by
  revert I
  simp [mem_ofFinset_iff]
  decide +kernel


-- @@ L442-446 verbatim
/-!

### C.5. Elements of `viableCharges` are complete

-/

-- @@ L447-449 verbatim
lemma isComplete_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), IsComplete x := by
  decide +revert


-- @@ L451-455 verbatim
/-!

### C.6. Elements of `viableCharges` permit a top Yukawa coupling

-/


-- @@ L457-459 verbatim
lemma allowsTerm_topYukawa_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.AllowsTerm topYukawa := by
  decide +revert


-- @@ L461-465 verbatim
/-!

### C.7. Elements of `viableCharges` are not pheno-constrained

-/


-- @@ L467-472 verbatim
lemma not_isPhenoConstrained_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), ¬ IsPhenoConstrained x := by
  intro x hx
  rw [viableCharges, Multiset.mem_add] at hx
  exact hx.elim (viableCompletions_isPhenoConstrained I x)
    (not_isPhenoConstrained_of_mem_viableChargesAdditional I x)


-- @@ L474-478 verbatim
/-!

### C.8. Elements of `viableCharges` do not regenerate dangerous couplings

-/


-- @@ L480-486 verbatim
lemma not_yukawaGeneratesDangerousAtLevel_one_of_mem_viableCharges
    (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), ¬ YukawaGeneratesDangerousAtLevel x 1 := by
  intro x hx
  rw [viableCharges, Multiset.mem_add] at hx
  exact hx.elim (viableCompletions_yukawaGeneratesDangerousAtLevel_one I x)
    (yukawaGeneratesDangerousAtLevel_one_of_mem_viableChargesAdditional I x)


-- @@ L488-492 verbatim
/-!

### C.9. Elements of `viableCharges` have at most two 5-bar reps

-/


-- @@ L494-496 verbatim
lemma card_five_bar_le_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.Q5.card ≤ 2 := by
  decide +revert


-- @@ L498-502 verbatim
/-!

### C.10. Elements of `viableCharges` have at most two 10d reps

-/


-- @@ L504-506 verbatim
lemma card_ten_le_of_mem_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCharges I), x.Q10.card ≤ 2 := by
  decide +revert


-- @@ L508-516 verbatim
/-!

### C.11. `viableCharges` is phenomenologically closed under adding 5-bar charges

We now show that adding a Q5 or a Q10 charge to an element of `viableCharges I` leads to a
charge which is either not phenomenologically constrained, or does not regenerate dangerous
couplings, or is already in `viableCharges I`.

-/


-- @@ L518-526 verbatim
/-- Inserting a `q5` charge into an element of `viableCharges I` either
1. produces another element of `viableCharges I`, or
2. produce a charge which is phenomenologically constrained or regenerates dangerous couplings
  with the Yukawas. -/
lemma isPhenoClosedQ5_viableCharges : (I : CodimensionOneConfig) →
    IsPhenoClosedQ5 I.allowedBarFiveCharges (viableCharges I) := by
  refine fun I => isPhenClosedQ5_of_isPhenoConstrainedQ5 ?_
  revert I
  decide +kernel


-- @@ L528-532 verbatim
/-!

### C.12. `viableCharges` is phenomenologically closed under adding 10d charges

-/


-- @@ L534-542 verbatim
/-- Inserting a `q10` charge into an element of `viableCharges I` either
1. produces another element of `viableCharges I`, or
2. produce a charge which is phenomenologically constrained or regenerates dangerous couplings
  with the Yukawas. -/
lemma isPhenoClosedQ10_viableCharges : (I : CodimensionOneConfig) →
    IsPhenoClosedQ10 I.allowedTenCharges (viableCharges I) := by
  refine fun I => isPhenClosedQ10_of_isPhenoConstrainedQ10 ?_
  revert I
  decide +kernel


-- @@ L544-548 verbatim
/-!

### C.13. `viableCompletions` is a subset of `viableCharges`

-/


-- @@ L550-554 verbatim
lemma viableCompletions_subset_viableCharges (I : CodimensionOneConfig) :
    ∀ x ∈ (viableCompletions I), x ∈ viableCharges I := by
  intro x hx
  rw [viableCharges, Multiset.mem_add]
  exact Or.inl hx


-- @@ L556-560 verbatim
/-!

### C.14. `viableCharges` contains all pheno-viable charges given a section configuration

-/


-- @@ L562-576 verbatim
lemma mem_viableCharges_iff {I} {x : ChargeSpectrum}
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges) :
    x ∈ viableCharges I ↔ AllowsTerm x topYukawa ∧
    ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1 ∧ IsComplete x :=
  completeness_of_isPhenoClosedQ5_isPhenoClosedQ10
    (allowsTerm_topYukawa_of_mem_viableCharges I)
    (not_isPhenoConstrained_of_mem_viableCharges I)
    (not_yukawaGeneratesDangerousAtLevel_one_of_mem_viableCharges I)
    (isComplete_of_mem_viableCharges I)
    (isPhenoClosedQ5_viableCharges I)
    (isPhenoClosedQ10_viableCharges I)
    (containsPhenoCompletionsOfMinimallyAllows_of_subset
      (containsPhenoCompletionsOfMinimallyAllows_viableCompletions I)
      (viableCompletions_subset_viableCharges I))
    hsub


-- @@ L578-588 verbatim
lemma mem_viableCharges_iff' {I} {x : ChargeSpectrum} :
    x ∈ viableCharges I ↔
    x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges ∧
    AllowsTerm x topYukawa ∧
    ¬ IsPhenoConstrained x ∧ ¬ YukawaGeneratesDangerousAtLevel x 1 ∧ IsComplete x := by
  constructor
  · intro h
    have h1 := viableCharges_mem_ofFinset I x h
    exact ⟨h1, (mem_viableCharges_iff h1).mp h⟩
  · rintro ⟨h1, h⟩
    exact (mem_viableCharges_iff h1).mpr h


-- @@ L590-590 verbatim
end ChargeSpectrum


-- @@ L592-592 verbatim
end SU5


-- @@ L594-594 verbatim
end FTheory
