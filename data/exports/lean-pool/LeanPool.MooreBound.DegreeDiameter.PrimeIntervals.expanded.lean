/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.AsymptoticsLimits
public import LeanPool.MooreBound.PrimeNumberTheoremAnd.Consequences


-- @@ L12-22 verbatim
/-!
# Main degree--diameter consequences

These wrappers discharge the abstract prime-interval premise of the analytic reduction using the
proved prime-number-theorem consequence `prime_between`.  Thus the only remaining hypothesis of
the exported results is the finite-geometry construction
`AsymptoticHalvedWitnessHypothesis`.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace MooreBound


-- @@ L28-28 verbatim
open Filter


-- @@ L30-30 verbatim
namespace DegreeDiameter


-- @@ L32-34 verbatim
lemma primeIntervalHypothesis_of_primeNumberTheorem : PrimeIntervalHypothesis := by
  intro η hη
  exact prime_between hη


-- @@ L36-40 verbatim
/-- Theorem 1.1 reduced to the halved-flag construction. -/
theorem theorem_1_1_of_asymptoticHalvedWitness
    (hw : AsymptoticHalvedWitnessHypothesis) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun d : ℕ ↦ (nKD k d : ℝ) / (d : ℝ) ^ k) atTop (nhds 1) :=
  theorem_1_1_of_prime_intervals primeIntervalHypothesis_of_primeNumberTheorem hw hk


-- @@ L42-47 verbatim
/-- Corollary 1.2 reduced to the halved-flag construction. -/
theorem corollary_1_2_of_asymptoticHalvedWitness
    (hw : AsymptoticHalvedWitnessHypothesis)
    {ell : ℕ} (hell : 2 ≤ ell) :
    1 ≤ liminf (fun d : ℕ ↦ (h ell d : ℝ) / (d : ℝ) ^ ell) atTop :=
  corollary_1_2_of_prime_intervals primeIntervalHypothesis_of_primeNumberTheorem hw hell


-- @@ L49-49 verbatim
end DegreeDiameter


-- @@ L51-51 verbatim
end MooreBound
