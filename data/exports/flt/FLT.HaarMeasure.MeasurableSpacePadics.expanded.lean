/-
Copyright (c) 2024 Yaël Dillies, David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, David Loeffler
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.NumberTheory.Padics.ProperSpace
import FLT.Mathlib.NumberTheory.Padics.PadicIntegers


-- @@ L12-17 verbatim
/-!
# Measurability and measures on the p-adics

This file endows `ℤ_[p]` and `ℚ_[p]` with their Borel sigma-algebra and their Haar measure that
makes `ℤ_[p]` (or the copy of `ℤ_[p]` inside `ℚ_[p]`) have norm `1`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open MeasureTheory Measure TopologicalSpace Topology


-- @@ L23-23 verbatim
variable {p : ℕ} [Fact p.Prime]


-- @@ L25-25 verbatim
namespace Padic


-- @@ L27-27 verbatim
noncomputable instance instMeasurableSpace : MeasurableSpace ℚ_[p] := borel _

-- @@ L28-30 verbatim
instance instBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

-- Should we more generally make a map from `CompactOpens` to `PositiveCompacts`?

-- @@ L31-40 verbatim
/-- The unit ball as a compact set with nonempty interior. -/
def unitBallPositiveCompact : PositiveCompacts ℚ_[p] where
  carrier := {y | ‖y‖ ≤ 1}
  isCompact' := by simpa only [Metric.closedBall, dist_zero_right] using
    isCompact_closedBall (0 : ℚ_[p]) 1
  interior_nonempty' := by
    rw [IsOpen.interior_eq]
    · exact ⟨0, by simp⟩
    · simpa only [Metric.closedBall, dist_zero_right] using
        IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero


-- @@ L42-43 verbatim
noncomputable instance instMeasureSpace : MeasureSpace ℚ_[p] :=
  ⟨addHaarMeasure unitBallPositiveCompact⟩


-- @@ L45-46 verbatim
instance instIsAddHaarMeasure : IsAddHaarMeasure (volume : Measure ℚ_[p]) :=
  isAddHaarMeasure_addHaarMeasure _


-- @@ L48-48 verbatim
lemma volume_closedBall_one : volume {x : ℚ_[p] | ‖x‖ ≤ 1} = 1 := addHaarMeasure_self


-- @@ L50-50 verbatim
end Padic


-- @@ L52-52 verbatim
namespace PadicInt


-- @@ L54-54 verbatim
noncomputable instance instMeasurableSpace : MeasurableSpace ℤ_[p] := Subtype.instMeasurableSpace

-- @@ L55-55 verbatim
instance instBorelSpace : BorelSpace ℤ_[p] := Subtype.borelSpace _


-- @@ L57-58 verbatim
lemma isMeasurableEmbedding_coe : MeasurableEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
  convert isOpenEmbedding_coe.measurableEmbedding


-- @@ L60-61 verbatim
lemma isMeasurableEmbedding_coeRingHom : MeasurableEmbedding (Coe.ringHom (p := p)) :=
  (coe_coeRingHom (p := p)) ▸ isMeasurableEmbedding_coe


-- @@ L63-63 verbatim
noncomputable instance instMeasureSpace : MeasureSpace ℤ_[p] := ⟨addHaarMeasure ⊤⟩


-- @@ L65-66 verbatim
instance instIsAddHaarMeasure : IsAddHaarMeasure (volume : Measure ℤ_[p]) :=
  isAddHaarMeasure_addHaarMeasure _


-- @@ L68-68 verbatim
@[simp] lemma volume_univ : volume (Set.univ : Set ℤ_[p]) = 1 := addHaarMeasure_self


-- @@ L70-71 verbatim
instance instIsFiniteMeasure : IsFiniteMeasure (volume : Measure ℤ_[p]) where
  measure_univ_lt_top := by simp


-- @@ L73-82 verbatim
lemma volume_coe_univ :
    volume ((↑) '' (Set.univ : Set ℤ_[p]) : Set ℚ_[p]) = volume (Set.univ : Set ℤ_[p]) := by
  simp only [volume_univ, ← Padic.volume_closedBall_one (p := p)]
  -- ❌️ at reducible transparency,
  --   ℤ_[p]
  -- and
  --   { x : ℚ_[p] // Membership.mem (γ := Set ℚ_[p]) (fun x ↦ Real.le✝ ‖x‖ 1) x }
  -- are not defeq, but they are at default transparency.
  erw [Subtype.coe_image_univ]
  rfl


-- @@ L84-99 verbatim
set_option backward.isDefEq.respectTransparency false in
-- https://github.com/ImperialCollegeLondon/FLT/issues/278
@[simp] lemma volume_coe (s : Set ℤ_[p]) : volume ((↑) '' s : Set ℚ_[p]) = volume s := by
  have h := volume_coe_univ (p := p)
  rw [← (coe_coeRingHom (p := p)), ← isMeasurableEmbedding_coeRingHom.comap_apply] at h ⊢
  have := IsAddLeftInvariant.comap volume
    (f := Coe.ringHom.toAddMonoidHom)
    (isMeasurableEmbedding_coeRingHom (p := p))
  have := IsFiniteMeasureOnCompacts.comap' volume
    (continuous_iff_le_induced.mpr fun _ h ↦ h)
    (isMeasurableEmbedding_coeRingHom (p := p))
  rw [isAddLeftInvariant_eq_smul (comap Coe.ringHom volume) (volume : Measure ℤ_[p])] at h ⊢
  suffices (comap (Coe.ringHom (p := p)) volume).addHaarScalarFactor volume = 1 by
    simp [-coe_coeRingHom, this]
  simpa only [Measure.smul_apply, volume_univ, ENNReal.smul_def, smul_eq_mul, mul_one,
    ENNReal.coe_eq_one] using h


-- @@ L101-101 verbatim
end PadicInt
