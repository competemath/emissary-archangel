/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.ProofSystem.BatchedFri.Spec.SingleRound
public import ArkLib.ProofSystem.Fri.Spec.General


-- @@ L12-16 verbatim
/-!
# ArkLib.ProofSystem.BatchedFri.Spec.General

Definitions and results for this component of ArkLib.
-/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
namespace BatchedFri


-- @@ L23-23 verbatim
namespace Spec


-- @@ L25-39 verbatim
open OracleSpec OracleComp ProtocolSpec NNReal BatchingRound Domain

/- Batched FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree" of each round,
         a folding degree of `1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `l`, the number of round consistency checks to be run by the query round.
  - `m`, number of batched polynomials.
-/

-- @@ L40-40 verbatim
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]

-- @@ L41-41 verbatim
variable {n : ℕ}

-- @@ L42-42 verbatim
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)

-- @@ L43-43 verbatim
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)

-- @@ L44-44 verbatim
variable (l m : ℕ)

-- @@ L45-47 verbatim
variable {ω : SmoothCosetFftDomain n F}

-- /- Input/Output relations for the Batched FRI protocol. -/

-- @@ L48-52 verbatim
def inputRelation (δ : ℝ≥0) :
    Set
      (
        Unit × (∀ j, OracleStatement m ω j) × (Witness F s d m)
      ) := sorry



-- @@ L55-64 verbatim
instance instBatchFRIreductionMessageOI : ∀ j,
  OracleInterface
    ((batchSpec F m ++ₚ
      (
        Fri.Spec.pSpecFold k (ω := ω) s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Message j) := fun j ↦ by
      apply instOracleInterfaceMessageAppend


-- @@ L66-77 verbatim
instance instBatchFRIreductionChallengeOI : ∀ j,
  OracleInterface
    ((batchSpec F m ++ₚ
      (
        Fri.Spec.pSpecFold k (ω := ω) s ++ₚ
        Fri.Spec.FinalFoldPhase.pSpec F ++ₚ
        Fri.Spec.QueryRound.pSpec (ω := ω) l
      )
    ).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/- Oracle reduction of the batched FRI protocol. -/

-- @@ L78-82 verbatim
@[reducible]
def batchedFRIreduction :=
  OracleReduction.append
    (BatchingRound.batchOracleReduction s d m)
    (Fri.Spec.reduction (ω := ω) k s d dom_size_cond l)


-- @@ L84-84 verbatim
end Spec


-- @@ L86-86 verbatim
end BatchedFri
