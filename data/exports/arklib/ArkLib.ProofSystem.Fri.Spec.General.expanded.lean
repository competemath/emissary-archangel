/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.ProofSystem.Fri.Spec.SingleRound


-- @@ L11-15 verbatim
/-!
# ArkLib.ProofSystem.Fri.Spec.General

Definitions and results for this component of ArkLib.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace Fri


-- @@ L21-21 verbatim
open OracleSpec OracleComp ProtocolSpec NNReal Domain


-- @@ L23-36 verbatim
namespace Spec

/- FRI parameters:
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
-/

-- @@ L37-37 verbatim
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]

-- @@ L38-38 verbatim
variable {n : ℕ}

-- @@ L39-39 verbatim
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)

-- @@ L40-40 verbatim
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)

-- @@ L41-41 verbatim
variable (l : ℕ)

-- @@ L42-44 verbatim
variable {ω : SmoothCosetFftDomain n F}

/- Input/Output relations for the FRI protocol. -/

-- @@ L45-53 verbatim
def inputRelation (δ : ℝ≥0) :
    Set
      (
        (Statement (k := k) F 0 × (∀ j, OracleStatement (k := k) s ω 0 j)) ×
        Witness F s d (0 : Fin (k + 2))
      ) :=
  match k with
  | 0 => FinalFoldPhase.inputRelation s (ω := ω) d (round_bound dom_size_cond) δ
  | .succ _ => FoldPhase.inputRelation s (ω := ω) d 0 (round_bound dom_size_cond) δ


-- @@ L55-62 verbatim
def outputRelation (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
        Witness F s d (Fin.last (k + 1))
      ) := QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ

/- Protocol spec for the combined non-final folding rounds of the FRI protocol. -/

-- @@ L63-68 verbatim
@[reducible]
def pSpecFold : ProtocolSpec (Fin.vsum fun (_ : Fin k) ↦ 2) :=
  ProtocolSpec.seqCompose (fun (i : Fin k) => FoldPhase.pSpec (ω := ω) s i)

/- `OracleInterface` instance for `pSpecFold` and with the final folding round
   protocol specification appended to it. -/

-- @@ L69-70 verbatim
instance : ∀ j, OracleInterface ((pSpecFold (ω := ω) k s).Message j) :=
  instOracleInterfaceMessageSeqCompose


-- @@ L72-73 verbatim
instance : ∀ j, OracleInterface (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F)).Message j) :=
  instOracleInterfaceMessageAppend


-- @@ L75-77 verbatim
instance : ∀ j,
    OracleInterface (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface


-- @@ L79-84 verbatim
instance :
    ∀ i,
      OracleInterface
        ((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ
          QueryRound.pSpec (ω := ω) l).Message i) :=
  instOracleInterfaceMessageAppend


-- @@ L86-92 verbatim
instance :
    ∀ j,
      OracleInterface (((pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ
        QueryRound.pSpec (ω := ω) l)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/- Oracle reduction for all folding rounds of the FRI protocol -/

-- @@ L93-105 verbatim
@[reducible]
def reductionFold :
    OracleReduction []ₒ
    (Statement F (0 : Fin (k + 1))) (OracleStatement s ω (0 : Fin (k + 1)))
      (Witness F s d (0 : Fin (k + 2)))
    (FinalStatement F k) (FinalOracleStatement s ω)
      (Witness F s d (Fin.last (k + 1)))
    (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F) := OracleReduction.append
      (OracleReduction.seqCompose _ _ (fun (i : Fin (k + 1)) => Witness F s d i.castSucc)
        (FoldPhase.foldOracleReduction s (ω := ω) d))
      (FinalFoldPhase.finalFoldOracleReduction (k := k) s d)

/- Oracle reduction of the FRI protocol. -/

-- @@ L106-114 verbatim
@[reducible]
def reduction :
    OracleReduction []ₒ
    (Statement F (0 : Fin (k + 1))) (OracleStatement s ω (0 : Fin (k + 1)))
      (Witness F s d (0 : Fin (k + 2)))
    (FinalStatement F k) (FinalOracleStatement s ω) (Witness F s d (Fin.last (k + 1)))
    (pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F ++ₚ QueryRound.pSpec l (ω := ω)) :=
  OracleReduction.append (reductionFold k s d)
    (QueryRound.queryOracleReduction (k := k) s d dom_size_cond l)


-- @@ L116-116 verbatim
end Spec


-- @@ L118-118 verbatim
end Fri
