import Submission.PTTransverseHomotopyCobordism
import Submission.MorseLedgerCobordism


-- @@ L4-18 verbatim
/-!
# Spatial flatness of a transverse Pontryagin--Thom cobordism

`PTTransverseHomotopyData` already requires its sphere-valued homotopy to be
the south pole outside a spatial ball.  Its selected horizontal level map is
therefore literally the constant `-target` there.  The core PT file only uses
this fact to prove boundedness of the zero set; this file records the stronger
spatial-flatness statement needed by the separated-support configuration
calculus.

This is the safe compactification output available for a Cassini saddle after
passing through the transverse PT construction.  It does not assert that the
regular-value endpoint presentations are definitionally the original Cassini
endpoints; that endpoint comparison remains a separate obligation.
-/


-- @@ L20-20 verbatim
set_option autoImplicit false


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace Submission


-- @@ L26-26 verbatim
open Set Function Metric

-- @@ L27-27 verbatim
open scoped Topology RealInnerProductSpace


-- @@ L29-29 verbatim
variable {n : ℕ}

-- @@ L30-30 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L31-31 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L33-33 verbatim
namespace PTTransverseHomotopyData


-- @@ L35-35 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (n + 1 + 1))

-- @@ L36-36 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L38-61 verbatim
/-- A radius one unit larger than the south-pole radius is nonnegative and
converts the strict exterior estimate in `exterior_south` to the weak estimate
used by `SpatialFlatOutside`. -/
theorem exists_nonneg_spatialFlatOutside
    (D : PTTransverseHomotopyData S₀ S₁) :
    ∃ R : ℝ, 0 ≤ R ∧
      D.toFramedLevelCobordism.SpatialFlatOutside (-D.target) 0 R := by
  obtain ⟨R, hR⟩ := D.exterior_south
  refine ⟨max R 0 + 1, by positivity, ?_⟩
  intro v hv
  have hnorm : R < ‖initCLM (n + 1) v‖ := by
    have hlarge : max R 0 + 1 ≤ ‖initCLM (n + 1) v‖ := by
      simpa [dist_zero_right] using hv
    have hstrict : R < max R 0 + 1 := by
      have hle : R ≤ max R 0 := le_max_left _ _
      linarith
    exact hstrict.trans_le hlarge
  have hsouth : D.sphere v = southPole n := hR v hnorm
  change D.levelMap v = -D.target
  rw [PTTransverseHomotopyData.levelMap]
  have hsouth' := congrArg Subtype.val hsouth
  rw [hsouth']
  change initCLM n (-eLast n) - D.target = -D.target
  rw [map_neg, initCLM_eLast, neg_zero, zero_sub]


-- @@ L63-72 verbatim
/-- Signed and unsigned PT cobordisms have the same underlying spatial
flatness certificate. -/
theorem exists_nonneg_signedSpatialFlatOutside
    (D : PTTransverseHomotopyData S₀ S₁) :
    ∃ R : ℝ, 0 ≤ R ∧
      D.toSignedFramedLevelCobordism.SpatialFlatOutside (-D.target) 0 R := by
  obtain ⟨R, hR, hflat⟩ := D.exists_nonneg_spatialFlatOutside
  refine ⟨R, hR, ?_⟩
  change D.toFramedLevelCobordism.SpatialFlatOutside (-D.target) 0 R
  exact hflat


-- @@ L74-78 verbatim
/-- The PT background is genuinely nonzero because the selected horizontal
value is required to be nonzero. -/
theorem neg_target_ne_zero (D : PTTransverseHomotopyData S₀ S₁) :
    -D.target ≠ 0 :=
  neg_ne_zero.mpr D.target_ne_zero


-- @@ L80-80 verbatim
end PTTransverseHomotopyData


-- @@ L82-82 verbatim
end Submission
