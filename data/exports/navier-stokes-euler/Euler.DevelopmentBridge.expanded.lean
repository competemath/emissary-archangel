import Euler.ClassicalBridge
import Euler.InitialDataBridge
import Euler.LpSmoothField


-- @@ L5-13 verbatim
/-!
# Interface to the current Euler development

The divergence operators agree definitionally. Compact smooth initial data
satisfy the Comparator's initial-data conditions. To package a Comparator
solution as the development's `SmoothL2Field`, however, one must establish
square integrability of every spatial derivative. The exact equivalence below
exposes that obligation without adding it to the reference statement.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set MeasureTheory

-- @@ L18-18 verbatim
open scoped ContDiff


-- @@ L20-20 verbatim
namespace Euler.ComparatorBridge


-- @@ L22-22 verbatim
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


-- @@ L24-25 verbatim
theorem divergence_eq_development (v : ℝ³ → ℝ³) (x : ℝ³) :
    Euler.divergence v x = EulerSmoothLimit.divergence v x := rfl


-- @@ L27-31 verbatim
theorem admissible_initial_data
    (A : EulerLpTranslation.SmoothL2Field ℝ³) (hc : HasCompactSupport A.field)
    (hd : ∀ x, EulerSmoothLimit.divergence A.field x = 0) :
    InitialVelocityConditionDecay A.field :=
  initialVelocityConditionDecay_of_compact A.field A.smooth hc hd


-- @@ L33-43 verbatim
theorem exists_smoothL2Field_iff
    {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) (t : ℝ) (ht : 0 ≤ t) :
    (∃ A : EulerLpTranslation.SmoothL2Field ℝ³, A.field = (v · t)) ↔
      ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m (v · t)) 2 volume := by
  constructor
  · rintro ⟨A, hA⟩ m
    rw [← hA]
    exact A.integrable m
  · intro hjets
    exact ⟨⟨(v · t), h.velocity_contDiff t ht, hjets⟩, rfl⟩


-- @@ L45-54 verbatim
/-- A conversion once the required all-order spatial integrability is proved.
This hypothesis is deliberately explicit; the Comparator does not provide it. -/
def velocityField
    {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (hjets : ∀ t ≥ 0, ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m (v · t)) 2 volume)
    (t : ℝ) (ht : 0 ≤ t) : EulerLpTranslation.SmoothL2Field ℝ³ where
  field := (v · t)
  smooth := h.velocity_contDiff t ht
  integrable := hjets t ht


-- @@ L56-56 verbatim
end Euler.ComparatorBridge
