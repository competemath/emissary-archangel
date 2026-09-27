/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledRay


-- @@ L11-11 verbatim
/-! Exact transfer of relative propagation to physical time and its actual profile. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section



-- @@ L19-19 verbatim
namespace EulerPacketMovingFrame


-- @@ L21-21 verbatim
open Set


-- @@ L23-24 verbatim
/-- Scaled time, given by `(a/ε)*(t-t₀)`. -/
def scaledTime (t₀ a ε t : ℝ) : ℝ := (a/ε)*(t-t₀)


-- @@ L26-27 verbatim
/-- Physical profile, given by `Z (scaledTime t₀ a ε t)`. -/
def physicalProfile (Z : ℝ → ℝ) (t₀ a ε t : ℝ) : ℝ := Z (scaledTime t₀ a ε t)


-- @@ L29-33 verbatim
theorem physicalTime_scaledTime {t₀ a ε t : ℝ} (ha : a ≠ 0) (hε : ε ≠ 0) :
    physicalTime t₀ a ε (scaledTime t₀ a ε t) = t := by
  unfold physicalTime scaledTime
  field_simp
  ring


-- @@ L35-39 verbatim
theorem scaledTime_physicalTime {t₀ a ε τ : ℝ} (ha : a ≠ 0) (hε : ε ≠ 0) :
    scaledTime t₀ a ε (physicalTime t₀ a ε τ) = τ := by
  unfold physicalTime scaledTime
  field_simp
  ring


-- @@ L41-44 verbatim
theorem scaledTime_strictMono {t₀ a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    StrictMono (scaledTime t₀ a ε) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hst t₀) (div_pos ha hε)


-- @@ L46-54 verbatim
theorem scaledTime_mem {t₀ a ε T t : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (ht : t ∈ Icc t₀ (physicalTime t₀ a ε T)) :
    scaledTime t₀ a ε t ∈ Icc 0 T := by
  have hm := (scaledTime_strictMono (t₀ := t₀) ha hε).monotone
  have hl := hm ht.1
  have hr := hm ht.2
  simp only [scaledTime, sub_self, mul_zero] at hl
  rw [scaledTime_physicalTime (ne_of_gt ha) (ne_of_gt hε)] at hr
  exact ⟨hl, hr⟩


-- @@ L56-63 verbatim
theorem physicalProfile_continuousOn {Z : ℝ → ℝ} {t₀ a ε T : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hZ : ContinuousOn Z (Icc 0 T)) :
    ContinuousOn (physicalProfile Z t₀ a ε) (Icc t₀ (physicalTime t₀ a ε T)) := by
  apply hZ.comp
  · unfold scaledTime
    fun_prop
  · intro t ht
    exact scaledTime_mem ha hε ht


-- @@ L65-69 verbatim
theorem physicalProfile_positive {Z : ℝ → ℝ} {t₀ a ε T : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hZ : ∀ t ∈ Icc 0 T, 0 < Z t) :
    ∀ t ∈ Icc t₀ (physicalTime t₀ a ε T), 0 < physicalProfile Z t₀ a ε t := by
  intro t ht
  exact hZ _ (scaledTime_mem ha hε ht)


-- @@ L71-86 verbatim
/-- This is only the exact change of the time variable in an already
proved propagator estimate; its profile ratio is preserved. -/
theorem physical_propagation_of_scaled {E : Type*} [NormedAddCommGroup E]
    (w : ℝ → E) (Z : ℝ → ℝ) {t₀ a ε T C : ℝ}
    (ha : 0 < a) (hε : 0 < ε)
    (hbound : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      ‖w (physicalTime t₀ a ε t)‖ ≤ C * (Z t / Z s) * ‖w (physicalTime t₀ a ε s)‖) :
    ∀ s t, s ∈ Icc t₀ (physicalTime t₀ a ε T) →
      t ∈ Icc t₀ (physicalTime t₀ a ε T) → s ≤ t →
      ‖w t‖ ≤ C*(physicalProfile Z t₀ a ε t/physicalProfile Z t₀ a ε s)*‖w s‖ := by
  intro s t hs ht hst
  have hs' := scaledTime_mem ha hε hs
  have ht' := scaledTime_mem ha hε ht
  have hst' := (scaledTime_strictMono (t₀ := t₀) ha hε).monotone hst
  have h := hbound _ _ hs'.1 hst' ht'.2
  simpa only [physicalTime_scaledTime (ne_of_gt ha) (ne_of_gt hε), physicalProfile] using h


-- @@ L88-88 verbatim
end EulerPacketMovingFrame
