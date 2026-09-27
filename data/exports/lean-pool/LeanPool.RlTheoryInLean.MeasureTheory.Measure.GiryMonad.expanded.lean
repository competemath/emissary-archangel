/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L11-13 verbatim
/-!
# LeanPool.RlTheoryInLean.MeasureTheory.Measure.GiryMonad
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open MeasureTheory MeasureTheory.Measure  ProbabilityTheory Finset NNReal ENNReal Preorder Filter


-- @@ L19-19 verbatim
namespace MeasureTheory.Measure


-- @@ L21-21 verbatim
variable {α β γ : Type*}

-- @@ L22-22 verbatim
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]


-- @@ L24-32 verbatim
lemma ae_join_of_ae_ae
  {m : Measure (Measure α)}
  {p : α → Prop} (hp : MeasurableSet {a | p a})
  (h : ∀ᵐ μ ∂m, ∀ᵐ a ∂μ, p a) :
  ∀ᵐ a ∂m.join, p a := by
  apply ae_iff.mpr
  rw [show {a | ¬p a} = {a | p a}ᶜ from rfl, join_apply hp.compl,
      ← lintegral_zero (μ := m)]
  exact lintegral_congr_ae (h.mono fun μ hμ => ae_iff.mp hμ)


-- @@ L34-48 verbatim
lemma ae_bind_of_ae_ae
  {m : Measure α}
  {p : β → Prop} {hp : MeasurableSet {a | p a}}
  {f : α → Measure β}
  (hf : AEMeasurable f m)
  (h : ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b) :
  ∀ᵐ b ∂m.bind f, p b := by
  unfold Measure.bind
  apply ae_join_of_ae_ae hp
  have hmeas : MeasurableSet {ν : Measure β | ∀ᵐ b ∂ν, p b} := by
    rw [show {ν : Measure β | ∀ᵐ b ∂ν, p b} =
          (fun ν : Measure β => ν {a | ¬ p a}) ⁻¹' {0} from by
      ext ν; simp [ae_iff]]
    exact (Measure.measurable_measure.mp measurable_id _ hp.compl) (measurableSet_singleton 0)
  exact (ae_map_iff hf hmeas).mpr h



-- @@ L51-51 verbatim
end MeasureTheory.Measure
