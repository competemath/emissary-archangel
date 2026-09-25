module

public import Carleson.Classical.CarlesonOnTheRealLineBasic
public import Carleson.TwoSidedCarleson.RestrictedWeakType

/-
This file contains the proof of an upgraded version of Lemma 11.1.4 (real Carleson),
from section 11.7.
-/


-- @@ L11-11 verbatim
open MeasureTheory Function Metric Bornology Real NNReal ENNReal


-- @@ L13-15 verbatim
public noncomputable section

/- Version of Lemma 11.1.5 for general exponents -/

-- @@ L16-31 verbatim
lemma general_carlesonOperator_on_the_reals_hasStrongType {q : ℝ≥0} (hq : q ∈ Set.Ioo 1 2) :
    HasStrongType (carlesonOperator K) q q volume volume (C_carleson_hasStrongType 4 q) := by
  have : Countable (Θ ℝ) := instCountableInt
  apply two_sided_metric_carleson_hasStrongType (a := 4) (by norm_num) hq Hilbert_strong_2_2

/-
--TODO: currently unused, maybe remove this?
lemma carlesonOperatorReal_hasStrongType {q : ℝ≥0} (hq : q ∈ Set.Ioo 1 2) :
    HasStrongType T q q volume volume (C_carleson_hasStrongType 4 q) := by
  intro f hf
  constructor
  · sorry
  apply le_trans _ (general_carlesonOperator_on_the_reals_hasStrongType hq f hf).2
  apply eLpNorm_mono_enorm
  apply carlesonOperatorReal_le_carlesonOperator
-/


-- @@ L33-35 verbatim
local notation "T" => carlesonOperatorReal K

/- Replacement for Lemma 11.1.5 -/

-- @@ L36-40 verbatim
lemma rcarleson' {q : ℝ≥0} (hq : q ∈ Set.Ioo 1 2) {f : ℝ → ℂ} (hf : MemLp f q) :
    eLpNorm (T f) q ≤ (C_carleson_hasStrongType 4 q) * eLpNorm f q := by
  apply le_trans _ (general_carlesonOperator_on_the_reals_hasStrongType hq f hf).2
  apply eLpNorm_mono_enorm
  apply carlesonOperatorReal_le_carlesonOperator


-- @@ L42-42 verbatim
end
