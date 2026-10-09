import OAI.Analysis.MetricEntropy.EntropyPair
import OAI.Analysis.MetricEntropy.Asymptotics


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-13 verbatim
/-!
# Limits for an actual family of constructed bodies

The family is indexed by rank `j + 1`, so every individual body has a positive
dimension and positive primal entropy. Its defining properties concern the
literal covering numbers; the limit arguments do not replace them by new
abstract quantities.
-/


-- @@ L15-15 verbatim
namespace MetricEntropyDuality


-- @@ L17-17 verbatim
open Filter Topology


-- @@ L19-27 verbatim
theorem tendsto_entropyBudget_successor_zero (a : ℝ) :
    Tendsto (fun j : ℕ => entropyBudget a (j + 1) ((j + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  change Tendsto
    (entropyRatioBound (compressionRadius a) (pivotSlots (accuracy a)) ∘ fun j : ℕ => j + 1)
    atTop (𝓝 0)
  exact
    (tendsto_entropyRatioBound_zero (compressionRadius a) (pivotSlots (accuracy a))).comp
      (tendsto_add_atTop_nat 1)


-- @@ L29-29 verbatim
namespace EntropyPair


-- @@ L31-36 verbatim
/-- The actual dimensions tend to infinity; no monotonicity is required. -/
theorem family_dimension_atTop {a : ℝ}
    (P : ∀ j : ℕ, EntropyPair a (j + 1) ((j + 1 : ℕ) : ℝ)) :
    Tendsto (fun j => (P j).dimension) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_add_atTop_nat 1)
  exact Filter.Eventually.of_forall (fun j => (P j).rank_le_dimension)


-- @@ L38-45 verbatim
/-- The quotient here is the actual dual entropy divided by the actual,
strictly positive primal entropy at every index. -/
theorem family_ratio_tendsto_zero {a : ℝ}
    (P : ∀ j : ℕ, EntropyPair a (j + 1) ((j + 1 : ℕ) : ℝ)) :
    Tendsto (fun j => entropyRatio a (P j).body) atTop (𝓝 0) :=
  squeeze_zero' (Filter.Eventually.of_forall (fun j => (P j).ratio_nonneg))
    (Filter.Eventually.of_forall (fun j => (P j).ratio_lt.le))
    (tendsto_entropyBudget_successor_zero a)


-- @@ L47-47 verbatim
end EntropyPair


-- @@ L49-49 verbatim
end MetricEntropyDuality


-- @@ L51-51 verbatim
end OAI
