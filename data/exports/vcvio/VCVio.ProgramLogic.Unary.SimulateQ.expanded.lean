/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.Coercions.SubSpec


-- @@ L14-26 verbatim
/-!
# Oracle-Aware Unary WP Rules

This file connects the quantitative weakest precondition (`wp`) to `simulateQ`,
providing rules that let program logic proofs pass through oracle simulation boundaries.

## Main results

- `wp_simulateQ_eq`: If an oracle implementation preserves distributions, then `wp` is preserved.
- `wp_liftComp`: Lifting a computation to a larger oracle spec preserves `wp`.
- `wp_simulateQ_run'_eq`: Stateful oracle implementations that preserve distributions
  preserve `wp`.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
open ENNReal OracleSpec OracleComp


-- @@ L32-32 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L34-34 verbatim
namespace OracleComp.ProgramLogic


-- @@ L36-36 verbatim
variable {ι : Type*} {spec : OracleSpec ι}

-- @@ L37-37 verbatim
variable [IsUniformSpec spec]

-- @@ L38-38 verbatim
variable {α : Type}


-- @@ L40-56 expanded
/-- If every oracle query in `impl` has the same evaluation distribution as the original query,
then `wp` of the simulated computation equals `wp` of the original. -/
@[game_rule]
theorem wp_simulateQ_eq (impl : QueryImpl spec (OracleComp spec))
    (hImpl :
      ∀ (t : spec.Domain),
        evalSPMF (impl t) = evalSPMF (liftM (OracleSpec.query t) : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) : wp (simulateQ impl oa) post = wp oa post := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa
    ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query]
    rw [wp_bind, wp_bind]
    simp_rw [ih]
    exact wp_congr_evalSPMF (hImpl t) _


-- @@ L58-68 expanded
/-- Lifting a computation to a larger oracle spec via `liftComp` preserves `wp`. -/
@[game_rule]
theorem wp_liftComp {ι' : Type*} {superSpec : OracleSpec ι'} [IsUniformSpec superSpec]
    [h : SubSpec spec superSpec] [LawfulSubSpec spec superSpec] (mx : OracleComp spec α)
    (post : α → ℝ≥0∞) : wp (liftComp mx superSpec) post = wp mx post :=
  by
  change
    @μ _ superSpec _ (liftComp mx superSpec >>= fun a => pure (post a)) =
      μ (mx >>= fun a => pure (post a))
  exact μ_cross_congr_evalSPMF (by simp only [evalSPMF_bind, evalSPMF_liftComp, evalSPMF_pure])


-- @@ L70-81 expanded
/-- If a stateful oracle implementation preserves distributions (each query produces a uniform
distribution after discarding state), then `wp` of `simulateQ ... run'` equals `wp` of the
original computation. -/
@[game_rule]
theorem wp_simulateQ_run'_eq {σ : Type} (impl : QueryImpl spec (StateT σ (OracleComp spec)))
    (hImpl :
      ∀ (t : spec.Domain) (s : σ),
        evalSPMF ((impl t).run' s) = OptionT.lift (PMF.uniformOfFintype (spec.Range t)))
    (oa : OracleComp spec α) (s : σ) (post : α → ℝ≥0∞) :
    wp ((simulateQ impl oa).run' s) post = wp oa post :=
  wp_congr_evalSPMF (evalSPMF_simulateQ_run'_eq_evalSPMF impl hImpl s oa) post


-- @@ L83-83 verbatim
end OracleComp.ProgramLogic
