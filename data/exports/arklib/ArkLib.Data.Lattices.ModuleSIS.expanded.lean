/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import VCVio.OracleComp.Constructions.SampleableType
public import ArkLib.Data.Lattices.CyclotomicRing.Rq
public import ArkLib.Data.Lattices.Vectors


-- @@ L12-37 verbatim
/-!
# Module Short Integer Solution (Module-SIS) over the Cyclotomic Ring

A small, ArkLib-native generic `SIS` search game and its Module-SIS specialization
over the computable cyclotomic ring `Rq Φ`. The kernel-form relation: given a uniformly
random matrix `A`, find a nonzero short vector `z` with `A *ᵥ z = 0`.

Note, there is another SIS definition in VCV-io, that is however not defined over computable
polynomials (CompPoly), for details checkout:
`VCV-io/LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean`.

This is the hardness assumption the Ajtai [Ajt96] commitment binding reductions target, in
the module form used by Greyhound [NS24] and Hachi [NOZ26].

## Main definitions

* `SIS.Problem` / `experiment` / `advantage` — the generic search game.
* `ModuleSIS.relation` / `problem` / `Adversary` / `advantage` — Module-SIS over `Rq Φ`.

## References

* [Ajtai, M., *Generating Hard Instances of Lattice Problems*][Ajt96]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
open OracleComp CompPoly ArkLib.Lattices

-- @@ L42-42 verbatim
open scoped ENNReal


-- @@ L44-44 verbatim
namespace ArkLib.Lattices


-- @@ L46-46 verbatim
/-! ## Generic SIS search game -/


-- @@ L48-48 verbatim
namespace SIS


-- @@ L50-50 verbatim
variable {Sample Solution : Type}


-- @@ L52-58 verbatim
/-- A generic SIS-style problem: public challenge data `Sample` (e.g. a matrix), a
`Solution` type, and a validity predicate. -/
structure Problem (Sample Solution : Type) where
  /-- Distribution of the public challenge. -/
  sampleChallenge : ProbComp Sample
  /-- Validity of a candidate solution (short + satisfies the linear constraint). -/
  isValid : Sample → Solution → Bool


-- @@ L60-61 verbatim
/-- A search adversary for a SIS-style problem. -/
abbrev Adversary (_problem : Problem Sample Solution) := Sample → ProbComp Solution


-- @@ L63-67 verbatim
/-- The SIS experiment: sample a challenge, run the adversary, check validity. -/
def experiment (problem : Problem Sample Solution) (adv : Adversary problem) : ProbComp Bool := do
  let challenge ← problem.sampleChallenge
  let solution ← adv challenge
  return problem.isValid challenge solution


-- @@ L69-72 verbatim
/-- Search advantage for a SIS-style problem. -/
noncomputable def advantage (problem : Problem Sample Solution) (adv : Adversary problem) :
    ℝ≥0∞ :=
  Pr[= true | experiment problem adv]


-- @@ L74-74 verbatim
end SIS


-- @@ L76-76 verbatim
/-! ## Module-SIS over `Rq Φ` -/


-- @@ L78-78 verbatim
namespace ModuleSIS


-- @@ L80-80 verbatim
open CyclotomicModulus


-- @@ L82-82 verbatim
variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]


-- @@ L84-85 verbatim
/-- A Module-SIS solution for a matrix with `cols` columns over `Rq Φ`. -/
abbrev Solution (cols : Nat) := PolyVec (Rq Φ) cols


-- @@ L87-93 verbatim
/-- The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short,
and lies in the kernel of `A`. -/
def relation {rows cols : Nat}
    [DecidableEq (PolyVec (Rq Φ) cols)] [DecidableEq (PolyVec (Rq Φ) rows)]
    (isShort : Solution Φ cols → Bool)
    (A : PolyMatrix (Rq Φ) rows cols) (z : Solution Φ cols) : Bool :=
  decide (z ≠ 0) && isShort z && decide (A *ᵥ z = 0)


-- @@ L95-101 verbatim
/-- Module-SIS as an instance of the generic SIS search game. -/
def problem (rows cols : Nat) [SampleableType (PolyMatrix (Rq Φ) rows cols)]
    [DecidableEq (PolyVec (Rq Φ) cols)] [DecidableEq (PolyVec (Rq Φ) rows)]
    (isShort : Solution Φ cols → Bool) :
    SIS.Problem (PolyMatrix (Rq Φ) rows cols) (Solution Φ cols) where
  sampleChallenge := $ᵗ (PolyMatrix (Rq Φ) rows cols)
  isValid := relation Φ isShort


-- @@ L103-107 verbatim
/-- A Module-SIS adversary. -/
abbrev Adversary (rows cols : Nat) [SampleableType (PolyMatrix (Rq Φ) rows cols)]
    [DecidableEq (PolyVec (Rq Φ) cols)] [DecidableEq (PolyVec (Rq Φ) rows)]
    (isShort : Solution Φ cols → Bool) :=
  SIS.Adversary (problem Φ rows cols isShort)


-- @@ L109-113 verbatim
/-- The Module-SIS experiment. -/
def experiment (rows cols : Nat) [SampleableType (PolyMatrix (Rq Φ) rows cols)]
    [DecidableEq (PolyVec (Rq Φ) cols)] [DecidableEq (PolyVec (Rq Φ) rows)]
    (isShort : Solution Φ cols → Bool) (adv : Adversary Φ rows cols isShort) : ProbComp Bool :=
  SIS.experiment (problem Φ rows cols isShort) adv


-- @@ L115-119 verbatim
/-- The Module-SIS advantage. -/
noncomputable def advantage (rows cols : Nat) [SampleableType (PolyMatrix (Rq Φ) rows cols)]
    [DecidableEq (PolyVec (Rq Φ) cols)] [DecidableEq (PolyVec (Rq Φ) rows)]
    (isShort : Solution Φ cols → Bool) (adv : Adversary Φ rows cols isShort) : ℝ≥0∞ :=
  SIS.advantage (problem Φ rows cols isShort) adv


-- @@ L121-121 verbatim
end ModuleSIS


-- @@ L123-123 verbatim
end ArkLib.Lattices
