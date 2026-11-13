import Mathlib
import Submission.PTEndpointLedgerStability
import Submission.PTEndpointPatchRegularity
import Submission.PTTwoSheetSplice


-- @@ L6-19 verbatim
/-!
# Assembly of the Cassini PT endpoint-stability witness

This constructor fills all six fields of `CassiniPTEndpointStability` from the
two irreducible endpoint inputs:

* spatial regularity of each small-value patch family;
* a fixed-fiber defining-map homotopy from each patched presentation to the
  corresponding transverse sphere presentation, with the evident sign
  pattern comparison.

Everything else--the signed connectors, their regular slabs, collar gluing,
and southern-sheet exclusion--is constructed here.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
open Set Function

-- @@ L28-28 verbatim
open scoped Topology RealInnerProductSpace ContDiff


-- @@ L30-30 verbatim
namespace CassiniPTEndpointStability


-- @@ L32-32 verbatim
variable (m : ℕ) (hm : 0 < m)


-- @@ L34-34 verbatim
local notation "X₀" => ConcreteZeroPairCassiniTwist.sourceFLS m hm

-- @@ L35-35 verbatim
local notation "X₁" => ConcreteZeroPairCassiniTwist.targetFLS m hm

-- @@ L36-36 verbatim
local notation "S₀" => FiberSign.allPositive X₀

-- @@ L37-37 verbatim
local notation "S₁" => FiberSign.allPositive X₁

-- @@ L38-38 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L40-76 verbatim
/-- Choose one nonzero target which is simultaneously regular for both
endpoint patch quotients and the transverse middle, and which lies inside the
two uniform spatial-regularity radii.  Thus the two `PatchSpatiallyRegular`
fields of the endpoint-stability constructor are automatic once the cutoffs,
localizers, and middle have been chosen. -/
theorem exists_common_regular_spatial_value
    (κ₀ : FiberSign.PTCutoff S₀) (κ₁ : FiberSign.PTCutoff S₁)
    (P₀ : FiberSign.PTCutoff.EndpointPatchLocalizer S₀ κ₀)
    (P₁ : FiberSign.PTCutoff.EndpointPatchLocalizer S₁ κ₁)
    (H : CollaredSphereHomotopy (m + 2)) :
    ∃ y : F, y ≠ 0 ∧ ‖y‖ < 1 ∧
      IsRegularValueOn
        (FiberSign.PTCutoff.patchQuotient S₀ κ₀ P₀)
        (FiberSign.PTCutoff.patchTransition S₀ κ₀ P₀) y ∧
      IsRegularValueOn
        (FiberSign.PTCutoff.patchQuotient S₁ κ₁ P₁)
        (FiberSign.PTCutoff.patchTransition S₁ κ₁ P₁) y ∧
      IsRegularValue H.horizontal y ∧
      FiberSign.PTCutoff.PatchSpatiallyRegular S₀ κ₀ P₀ y ∧
      FiberSign.PTCutoff.PatchSpatiallyRegular S₁ κ₁ P₁ y := by
  obtain ⟨ε₀, hε₀, hsp₀⟩ :=
    FiberSign.PTCutoff.exists_patchSpatiallyRegular_radius S₀ κ₀ P₀
  obtain ⟨ε₁, hε₁, hsp₁⟩ :=
    FiberSign.PTCutoff.exists_patchSpatiallyRegular_radius S₁ κ₁ P₁
  let r : ℝ := min ε₀ (min ε₁ 1)
  have hr : 0 < r := by
    exact lt_min hε₀ (lt_min hε₁ zero_lt_one)
  obtain ⟨y, hypos, hyr, hreg₀, hreg₁, hregH⟩ :=
    FiberSign.PTCutoff.exists_common_regular_value_lt
      S₀ S₁ κ₀ κ₁ P₀ P₁ H (by omega) r hr
  have hyr₀ : ‖y‖ < ε₀ := hyr.trans_le (min_le_left ε₀ (min ε₁ 1))
  have hyr₁ : ‖y‖ < ε₁ := hyr.trans_le
    ((min_le_right ε₀ (min ε₁ 1)).trans (min_le_left ε₁ 1))
  have hyrOne : ‖y‖ < 1 := hyr.trans_le
    ((min_le_right ε₀ (min ε₁ 1)).trans (min_le_right ε₁ 1))
  exact ⟨y, norm_pos_iff.mp hypos, hyrOne, hreg₀, hreg₁, hregH,
    hsp₀ y hyr₀, hsp₁ y hyr₁⟩


-- @@ L78-152 verbatim
/-- Exact four-obligation constructor for the Cassini endpoint witness.

The two `PatchSpatiallyRegular` arguments are the source/target analytic
estimates.  The two `DefiningMapHomotopy` arguments are the source/target
same-fiber comparisons.  Their sign-pattern hypotheses are pointwise and are
automatic once the homotopies remain in the positive sheet. -/
def ofPatchedDefiningMapHomotopies
    (κ₀ : FiberSign.PTCutoff S₀) (κ₁ : FiberSign.PTCutoff S₁)
    (P₀ : FiberSign.PTCutoff.EndpointPatchLocalizer S₀ κ₀)
    (P₁ : FiberSign.PTCutoff.EndpointPatchLocalizer S₁ κ₁)
    (H : CollaredSphereHomotopy (m + 2))
    (y₀ y₁ y : F) (hy0 : y ≠ 0) (hylt : ‖y‖ < 1)
    (hregular₀ : IsRegularValueOn
      (FiberSign.PTCutoff.patchQuotient S₀ κ₀ P₀)
      (FiberSign.PTCutoff.patchTransition S₀ κ₀ P₀) y₀)
    (hregular₁ : IsRegularValueOn
      (FiberSign.PTCutoff.patchQuotient S₁ κ₁ P₁)
      (FiberSign.PTCutoff.patchTransition S₁ κ₁ P₁) y₁)
    (hregular : IsRegularValue H.horizontal y)
    (hsp₀ : FiberSign.PTCutoff.PatchSpatiallyRegular S₀ κ₀ P₀ y₀)
    (hsp₁ : FiberSign.PTCutoff.PatchSpatiallyRegular S₁ κ₁ P₁ y₁)
    (D₀ : DefiningMapHomotopy
      (FiberSign.PTCutoff.patchTargetLevelSet S₀ κ₀ P₀ y₀ hregular₀)
      (H.sourceLevelSet y hy0 hregular))
    (D₁ : DefiningMapHomotopy
      (FiberSign.PTCutoff.patchTargetLevelSet S₁ κ₁ P₁ y₁ hregular₁)
      (H.targetLevelSet y hy0 hregular))
    (hsource : ∀ x ∈ (H.sourceLevelSet y hy0 hregular).fiber,
      (0 < (FiberSign.PTCutoff.patchTargetSign
          S₀ κ₀ P₀ y₀ hregular₀).restrict D₀.fiber_subset x ↔
        0 < H.sourceSign y hy0 hregular hylt x))
    (htarget : ∀ x ∈ (H.targetLevelSet y hy0 hregular).fiber,
      (0 < (FiberSign.PTCutoff.patchTargetSign
          S₁ κ₁ P₁ y₁ hregular₁).restrict D₁.fiber_subset x ↔
        0 < H.targetSign y hy0 hregular hylt x)) :
    CassiniPTEndpointStability m hm
      (H.sourceSign y hy0 hregular hylt)
      (H.targetSign y hy0 hregular hylt)
      (H.toPTTransverseHomotopyData y hy0 hregular hylt) := by
  let Cpatch₀ := FiberSign.PTCutoff.patchSignedCobordism
    S₀ κ₀ P₀ y₀ hregular₀
  let Cpatch₁ := FiberSign.PTCutoff.patchSignedCobordism
    S₁ κ₁ P₁ y₁ hregular₁
  let Ccompare₀ := signedEndpointConnectorOfDefiningMapHomotopy D₀ _ _ hsource
  let Ccompare₁ := signedEndpointConnectorOfDefiningMapHomotopy D₁ _ _ htarget
  refine {
    sourceConnector := SignedFramedLevelCobordism.trans Cpatch₀ Ccompare₀
    targetConnector := SignedFramedLevelCobordism.trans Cpatch₁ Ccompare₁
    sourceRegular := ?_
    targetRegular := ?_
    sourcePositive := ?_
    targetPositive := ?_
  }
  · exact SignedFramedLevelCobordism.regularSlab_trans Cpatch₀ Ccompare₀
      (FiberSign.PTCutoff.patchSignedCobordism_regularSlab_of_patchSpatiallyRegular
        S₀ κ₀ P₀ y₀ hregular₀ hsp₀)
      (signedEndpointConnectorOfDefiningMapHomotopy_regularSlab
        D₀ _ _ hsource)
  · exact SignedFramedLevelCobordism.regularSlab_trans Cpatch₁ Ccompare₁
      (FiberSign.PTCutoff.patchSignedCobordism_regularSlab_of_patchSpatiallyRegular
        S₁ κ₁ P₁ y₁ hregular₁ hsp₁)
      (signedEndpointConnectorOfDefiningMapHomotopy_regularSlab
        D₁ _ _ htarget)
  · intro x hx
    apply (hsource x hx).mp
    change 0 < FiberSign.PTCutoff.patchTargetSign
      S₀ κ₀ P₀ y₀ hregular₀ x
    exact FiberSign.PTCutoff.patchTargetSign_positive_of_allPositive
      κ₀ P₀ y₀ hregular₀ x (D₀.fiber_subset hx)
  · intro x hx
    apply (htarget x hx).mp
    change 0 < FiberSign.PTCutoff.patchTargetSign
      S₁ κ₁ P₁ y₁ hregular₁ x
    exact FiberSign.PTCutoff.patchTargetSign_positive_of_allPositive
      κ₁ P₁ y₁ hregular₁ x (D₁.fiber_subset hx)


-- @@ L154-154 verbatim
end CassiniPTEndpointStability


-- @@ L156-156 verbatim
end Submission
