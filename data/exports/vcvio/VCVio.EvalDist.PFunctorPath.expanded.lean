/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.PFunctorMeasure.Core
public import PolyFun.PFunctor.Free.Path.Bounded
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map


-- @@ L13-25 verbatim
/-!
# Measure semantics of typed interaction paths

Every `FreeM` program is a fully syntactic tree of typed interactions. PolyFun's `withPath`
instrumentation retains the dependent root-to-leaf path selected by the answers, while
`withPathLength` projects that syntax to a plain natural number before any probability semantics
is chosen.

This module denotes those instrumented programs directly as Mathlib measures. The canonical
complexity observer is `queryCountMeasure : Measure ℕ`, which needs no measurable-space choice
for the dependent path type. A full `pathMeasure` remains available when a caller supplies that
choice explicitly; no global measurable-space instance on paths is installed.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
open MeasureTheory

-- @@ L30-30 verbatim
open scoped ENNReal


-- @@ L32-32 verbatim
universe u v uA


-- @@ L34-34 verbatim
namespace PFunctor.FreeM


-- @@ L36-37 verbatim
variable {P : PFunctor.{uA, u}} [∀ a, MeasurableSpace (P.B a)] [P.IsMeasureSpec]
  [∀ a, DiscreteMeasurableSpace (P.B a)] {α : Type v}


-- @@ L39-39 verbatim
/-! ## Observable measures -/


-- @@ L41-45 verbatim
/-- The measure of fully typed paths through `program` for an explicitly selected measurable
space on its dependent path type. -/
noncomputable def pathMeasure (program : FreeM P α)
    [MeasurableSpace (Path program)] : Measure (Path program) :=
  denote (withPath program)


-- @@ L47-52 verbatim
/-- The distribution of the number of interactions on a completed typed path.

The length projection happens in syntax, before denotation, so this canonical observer does not
need a measurable-space instance on `Path program`. -/
noncomputable def queryCountMeasure (program : FreeM P α) : Measure ℕ :=
  denote (withPathLength program)


-- @@ L54-56 verbatim
/-- The expected number of interactions on a completed typed path. -/
noncomputable def expectedQueryCount (program : FreeM P α) : ℝ≥0∞ :=
  ∫⁻ count, (count : ℝ≥0∞) ∂queryCountMeasure program


-- @@ L58-58 verbatim
/-! ## Marginals and projections -/


-- @@ L60-64 verbatim
/-- Pushing the full path measure through path length gives the canonical query-count measure. -/
theorem map_length_pathMeasure (program : FreeM P α)
    [MeasurableSpace (Path program)] [DiscreteMeasurableSpace (Path program)] :
    (pathMeasure program).map (Path.length program) = queryCountMeasure program := by
  rw [pathMeasure, queryCountMeasure, withPathLength, denote_map_of_discrete]


-- @@ L66-75 verbatim
/-- Forgetting the path while retaining its selected leaf recovers the program denotation. -/
theorem map_output_pathMeasure [MeasurableSpace α] (program : FreeM P α)
    [MeasurableSpace (Path program)] [DiscreteMeasurableSpace (Path program)] :
    (pathMeasure program).map (output program) = denote program := by
  unfold pathMeasure
  calc
    (denote (withPath program)).map (output program) =
        denote (FreeM.map (output program) (withPath program)) :=
      (denote_map_of_discrete (withPath program) (output program)).symm
    _ = denote program := congrArg denote (map_output_withPath program)


-- @@ L77-77 verbatim
/-! ## Exact and worst-case path lengths -/


-- @@ L79-91 verbatim
/-- If every typed path has length `count`, then the query-count measure is the Dirac measure at
`count`. The proof uses the full path measure only under a local discrete measurable space. -/
theorem queryCountMeasure_eq_dirac_of_length_eq (program : FreeM P α) (count : ℕ)
    (hlength : ∀ path : Path program, Path.length program path = count) :
    queryCountMeasure program = Measure.dirac count := by
  let _ : MeasurableSpace (Path program) := ⊤
  let _ : IsProbabilityMeasure (pathMeasure program) := by
    unfold pathMeasure
    exact isProbabilityMeasure_denote _
  rw [← map_length_pathMeasure]
  have hfun : Path.length program = fun _ ↦ count := funext hlength
  rw [hfun, Measure.map_const]
  simp


-- @@ L93-98 verbatim
/-- A pointwise constant typed-path length has that exact expectation. -/
theorem expectedQueryCount_eq_of_length_eq (program : FreeM P α) (count : ℕ)
    (hlength : ∀ path : Path program, Path.length program path = count) :
    expectedQueryCount program = (count : ℝ≥0∞) := by
  rw [expectedQueryCount, queryCountMeasure_eq_dirac_of_length_eq program count hlength]
  simp


-- @@ L100-114 verbatim
/-- A branchwise syntactic roll bound bounds expected query count.

This is derived from PolyFun's pointwise path theorem and total measure mass; it is not an
independent expected-cost assumption. -/
theorem expectedQueryCount_le_of_isTotalRollBound (program : FreeM P α) {bound : ℕ}
    (hbound : program.IsTotalRollBound bound) :
    expectedQueryCount program ≤ (bound : ℝ≥0∞) := by
  let _ : MeasurableSpace (Path program) := ⊤
  let _ : IsProbabilityMeasure (pathMeasure program) := by
    unfold pathMeasure
    exact isProbabilityMeasure_denote _
  rw [expectedQueryCount, ← map_length_pathMeasure,
    MeasureTheory.lintegral_map Measurable.of_discrete Measurable.of_discrete]
  refine (lintegral_mono (g := fun _ => (bound : ℝ≥0∞)) fun path => ?_).trans_eq (by simp)
  exact Nat.cast_le.2 (Path.length_le_of_isTotalRollBound program hbound path)


-- @@ L116-116 verbatim
end PFunctor.FreeM
