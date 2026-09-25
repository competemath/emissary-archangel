/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SeededFork
public import VCVio.ProgramLogic.Unary.HoareTriple


-- @@ L11-17 verbatim
/-!
# Seed-Based Forking Lemma — Program Logic Bridge

Wraps the probabilistic seeded forking lemma bounds from
`CryptoFoundations/SeededFork.lean` as quantitative Hoare triples (`Triple`) for use in the
program logic framework.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open OracleSpec OracleComp ENNReal


-- @@ L23-23 verbatim
namespace OracleComp.ProgramLogic


-- @@ L25-27 expanded
variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [∀ i, SampleableType (spec.Range i)]
  [spec.DecidableEq] [SubSpec unifSpec spec] {α : Type}


-- @@ L29-31 expanded
variable (main : OracleComp spec α) (qb : ι → ℕ) (js : List ι) (i : ι)
  (cf : α → Option (Fin (qb i + 1))) [IsUniformSpec spec] [LawfulSubSpec unifSpec spec]


-- @@ L33-44 expanded
/-- Seeded forking lemma as a quantitative Hoare triple for the fork-success event. -/
theorem triple_seededFork :
    Triple (spec := spec)
      (let acc : ℝ≥0∞ := ∑ s, probOutput (cf <$> main) (some s)
      let h : ℝ≥0∞ := Fintype.card (spec.Range i)
      let q := qb i + 1
      acc * (acc / q - h⁻¹))
      (seededFork main qb js i cf) (fun r => if r.isSome then 1 else 0) :=
  triple_ofLE <|
    le_trans (OracleComp.le_probEvent_isSome_seededFork main qb js i cf)
      (triple_toLE (triple_probEvent_indicator (seededFork main qb js i cf) fun r => r.isSome))


-- @@ L46-46 verbatim
end OracleComp.ProgramLogic
