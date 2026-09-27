/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformHarmonicInteraction
public import LeanPool.NavierStokesAndEuler.NavierStokes.StateReindex
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds


-- @@ L13-20 verbatim
/-!
# Exact transport of mean bounds and residual coefficient classes

Pullback along `e : D ≃ₗᵢ[ℝ] E` uses the actual state/context construction
from `StateReindex`.  Every derivative norm and every scalar majorant is
unchanged.  In particular, uniform constants are chosen before the label
both before and after reassociation.
-/


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace NavierStokes.MeanBoundsReindex


-- @@ L29-29 verbatim
open Set Function Filter WeightedClasses LabelSumBounds

-- @@ L30-30 verbatim
open scoped ContDiff Topology


-- @@ L32-33 verbatim
variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L35-39 verbatim
theorem strip_roundtrip (e : D ≃ₗᵢ[ℝ] E) (s : StripData D) :
    ParticularWaveBounds.reindexStrip e (ParticularWaveBounds.reindexStrip e.symm s) = s := by
  cases s
  simp only [ParticularWaveBounds.reindexStrip, preimage_preimage, e.symm_apply_apply]
  rfl


-- @@ L41-44 verbatim
theorem majorant_pull (e : D ≃ₗᵢ[ℝ] E) (s : StripData E) (w : ℕ → E → ℝ)
    (α C : ℝ) (p n : ℕ) (x : D) :
    majorant (ParticularWaveBounds.reindexStrip e s) (fun k y => w k (e y)) α C p n x =
      majorant s w α C p n (e x) := rfl


-- @@ L46-65 verbatim
/-- The same numerical `C,p` works on both sides, including all derivatives
up to the supplied order.  This is stronger than a fresh existence bound. -/
theorem finiteJet_bound_pull_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : D ≃ₗᵢ[ℝ] E) (s : StripData E) (w : ℕ → E → ℝ)
    (f : ℕ → E → F) (α C : ℝ) (p m : ℕ) :
    (∀ n x, x ∈ (ParticularWaveBounds.reindexStrip e s).domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (fun y => f n (e y)) x‖ ≤
        majorant (ParticularWaveBounds.reindexStrip e s) (fun k y => w k (e y)) α C p n x) ↔
    (∀ n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ majorant s w α C p n x) := by
  constructor
  · intro h n x hx j hj
    have hh := h n (e.symm x) (by change e (e.symm x) ∈ s.domain; simpa using hx) j hj
    change ‖iteratedFDeriv ℝ j (f n ∘ e) (e.symm x)‖ ≤ _ at hh
    rw [e.norm_iteratedFDeriv_comp_right] at hh
    simpa only [majorant_pull, e.apply_symm_apply] using hh
  · intro h n x hx j hj
    change ‖iteratedFDeriv ℝ j (f n ∘ e) x‖ ≤ _
    rw [e.norm_iteratedFDeriv_comp_right, majorant_pull]
    exact h n (e x) hx j hj


-- @@ L67-68 verbatim
theorem bandBound_pull_iff (e : D ≃ₗᵢ[ℝ] E) (s : StripData E) (β : ℝ) (a : ℕ → ℝ) :
    BandBound (ParticularWaveBounds.reindexStrip e s) β a ↔ BandBound s β a := Iff.rfl


-- @@ L70-73 verbatim
theorem meanClass_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E} {α : ℝ}
    {f : MeanIncrementBounds.Field E} (hf : MeanClass s α f) :
    MeanClass (ParticularWaveBounds.reindexStrip e s) α (StateReindex.field e f) :=
  ParticularWaveBounds.memClass_reindex e hf


-- @@ L75-78 verbatim
theorem unweightedClass_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E} {α : ℝ}
    {f : MeanIncrementBounds.Field E} (hf : UnweightedClass s α f) :
    UnweightedClass (ParticularWaveBounds.reindexStrip e s) α (StateReindex.field e f) :=
  ParticularWaveBounds.memClass_reindex e hf


-- @@ L80-88 verbatim
theorem operatorBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {o : MeanIncrementBounds.Operators E} {κ : ℝ}
    (ho : MeanIncrementBounds.OperatorBounds s o κ) :
    MeanIncrementBounds.OperatorBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.operators e o) κ := by
  refine ⟨ho.epsilon_eq, ?_, ?_, ho.radialFrequency, ho.fastCoefficient,
    ho.kappa_nonneg, fun x hx => ho.weight_le_one (e x) hx⟩
  · exact unweightedClass_pull e ho.radialProfile
  · exact unweightedClass_pull e ho.invRadius


-- @@ L90-95 verbatim
theorem baseBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {b : MeanIncrementBounds.Triple E} (hb : MeanIncrementBounds.BaseBounds s b) :
    MeanIncrementBounds.BaseBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.triple e b) :=
  ⟨unweightedClass_pull e hb.radial, unweightedClass_pull e hb.angular,
    unweightedClass_pull e hb.axial⟩


-- @@ L97-101 verbatim
theorem meanCumulativeBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {b : MeanIncrementBounds.Triple E} (hb : MeanIncrementBounds.CumulativeBounds s b) :
    MeanIncrementBounds.CumulativeBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.triple e b) :=
  ⟨meanClass_pull e hb.radial, meanClass_pull e hb.angular, meanClass_pull e hb.axial⟩


-- @@ L103-107 verbatim
theorem incrementBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E} {H : ℝ}
    {b : MeanIncrementBounds.Triple E} (hb : MeanIncrementBounds.IncrementBounds s H b) :
    MeanIncrementBounds.IncrementBounds (ParticularWaveBounds.reindexStrip e s) H
      (StateReindex.triple e b) :=
  ⟨meanClass_pull e hb.radial, meanClass_pull e hb.angular, meanClass_pull e hb.axial⟩


-- @@ L109-113 verbatim
theorem context_operatorBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {c : CorrectionState.Context E} {κ : ℝ}
    (ho : MeanIncrementBounds.OperatorBounds s c.operators κ) :
    MeanIncrementBounds.OperatorBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.context e c).operators κ := operatorBounds_pull e ho


-- @@ L115-118 verbatim
theorem context_baseBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {c : CorrectionState.Context E} (hb : MeanIncrementBounds.BaseBounds s c.base) :
    MeanIncrementBounds.BaseBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.context e c).base := baseBounds_pull e hb


-- @@ L120-124 verbatim
theorem cumulativeBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {u : CorrectionState.State E} (hu : CorrectionState.CumulativeBounds s u) :
    CorrectionState.CumulativeBounds (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.state e u) :=
  ⟨meanCumulativeBounds_pull e hu.velocity, meanClass_pull e hu.pressure⟩


-- @@ L126-135 verbatim
theorem meanResidualBounds_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {σ : ℝ} {c : CorrectionState.Context E} {u : CorrectionState.State E}
    (hu : CorrectionState.MeanResidualBounds s σ c u) :
    CorrectionState.MeanResidualBounds (ParticularWaveBounds.reindexStrip e s) σ
      (StateReindex.context e c) (StateReindex.state e u) := by
  constructor
  · simp only [StateReindex.meanGoodResidual_pull]
    exact meanClass_pull e hu.angular
  · simp only [StateReindex.meanGoodResidual_pull]
    exact meanClass_pull e hu.axial


-- @@ L137-137 verbatim
/-! ## Returning solver classes to the original chart -/


-- @@ L139-145 verbatim
theorem memClass_return {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : D ≃ₗᵢ[ℝ] E) {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f : ℕ → E → F}
    (hf : MemClass (ParticularWaveBounds.reindexStrip e.symm s)
      (fun n y => w n (e.symm y)) α f) :
    MemClass s w α (fun n x => f n (e x)) := by
  have hh := ParticularWaveBounds.memClass_reindex e hf
  simpa only [strip_roundtrip, e.symm_apply_apply] using hh


-- @@ L147-156 verbatim
/-- Returning a uniform class retains the same constants chosen before
both the label and the band. -/
theorem uniformClass_return {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : D ≃ₗᵢ[ℝ] E) {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    {f : ι → ℕ → E → F}
    (hf : UniformClass (ParticularWaveBounds.reindexStrip e.symm s)
      (fun l n y => w l n (e.symm y)) α f) :
    UniformClass s w α (fun l n x => f l n (e x)) := by
  have hh := UniformBlockBounds.uniform_reindex e hf
  simpa only [strip_roundtrip, e.symm_apply_apply] using hh


-- @@ L158-164 verbatim
theorem context_operatorBounds_return (e : D ≃ₗᵢ[ℝ] E) {s : StripData D}
    {c : CorrectionState.Context D} {κ : ℝ}
    (ho : MeanIncrementBounds.OperatorBounds (ParticularWaveBounds.reindexStrip e.symm s)
      (StateReindex.context e.symm c).operators κ) :
    MeanIncrementBounds.OperatorBounds s c.operators κ := by
  have hh := context_operatorBounds_pull e ho
  simpa only [strip_roundtrip, StateReindex.context_roundtrip] using hh


-- @@ L166-171 verbatim
theorem context_baseBounds_return (e : D ≃ₗᵢ[ℝ] E) {s : StripData D}
    {c : CorrectionState.Context D}
    (hb : MeanIncrementBounds.BaseBounds (ParticularWaveBounds.reindexStrip e.symm s)
      (StateReindex.context e.symm c).base) : MeanIncrementBounds.BaseBounds s c.base := by
  have hh := context_baseBounds_pull e hb
  simpa only [strip_roundtrip, StateReindex.context_roundtrip] using hh


-- @@ L173-178 verbatim
theorem cumulativeBounds_return (e : D ≃ₗᵢ[ℝ] E) {s : StripData D}
    {u : CorrectionState.State D}
    (hu : CorrectionState.CumulativeBounds (ParticularWaveBounds.reindexStrip e.symm s)
      (StateReindex.state e.symm u)) : CorrectionState.CumulativeBounds s u := by
  have hh := cumulativeBounds_pull e hu
  simpa only [strip_roundtrip, StateReindex.state_roundtrip] using hh


-- @@ L180-180 verbatim
/-! ## Uniform classes of the actual harmonic residual -/


-- @@ L182-190 verbatim
theorem residualBlock_return (e : D ≃ₗᵢ[ℝ] E)
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (G A : HarmonicResidual.BlockCoefficients D) :
    StateReindex.block e
      (HarmonicResidual.residualBlock (StateReindex.context e.symm c) (StateReindex.state e.symm u)
        (StateReindex.block e.symm b) (StateReindex.blockCoefficients e.symm G)
        (StateReindex.blockCoefficients e.symm A)) =
      HarmonicResidual.residualBlock c u b G A := by
  rw [StateReindex.residualBlock_pull, StateReindex.block_roundtrip]


-- @@ L192-200 verbatim
/-- Arbitrary solver block families return with their original common
weight and exponent.  Uniformity over labels is retained. -/
theorem uniformVelocity_return {ι : Type*} (e : D ≃ₗᵢ[ℝ] E) {s : StripData D}
    {P : ι → ℕ → D → ℝ} {α : ℝ} {b : ι → CorrectionState.HarmonicBlock E}
    (hb : UniformHarmonicInteraction.UniformVelocity
      (ParticularWaveBounds.reindexStrip e.symm s) (fun l n y => P l n (e.symm y)) α b) :
    UniformHarmonicInteraction.UniformVelocity s P α (fun l => StateReindex.block e (b l)) := by
  intro i j hj
  exact uniformClass_return e (hb i j hj)


-- @@ L202-208 verbatim
theorem uniformVelocity_pull {ι : Type*} (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {P : ι → ℕ → E → ℝ} {α : ℝ} {b : ι → CorrectionState.HarmonicBlock E}
    (hb : UniformHarmonicInteraction.UniformVelocity s P α b) :
    UniformHarmonicInteraction.UniformVelocity (ParticularWaveBounds.reindexStrip e s)
      (fun l n x => P l n (e x)) α (fun l => StateReindex.block e (b l)) := by
  intro i j hj
  exact UniformBlockBounds.block_velocity_reindex e i j (hb i j hj)


-- @@ L210-223 verbatim
theorem residualBlock_velocity_uniform_pull {ι : Type*} (e : D ≃ₗᵢ[ℝ] E)
    {s : StripData E} {w : ι → ℕ → E → ℝ} {α : ℝ}
    (c : CorrectionState.Context E) (u : CorrectionState.State E)
    (b : ι → CorrectionState.HarmonicBlock E) (G A : ι → HarmonicResidual.BlockCoefficients E)
    (i : Fin 3) (j : ℤ)
    (hb : UniformClass s w α
      (fun l n x => (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).velocity n i j x)) :
    UniformClass (ParticularWaveBounds.reindexStrip e s) (fun l n x => w l n (e x)) α
      (fun l n x => (HarmonicResidual.residualBlock (StateReindex.context e c)
        (StateReindex.state e u) (StateReindex.block e (b l))
        (StateReindex.blockCoefficients e (G l)) (StateReindex.blockCoefficients e (A l))).velocity
            n i j x) := by
  simpa only [StateReindex.residualBlock_pull, StateReindex.strip] using
    UniformBlockBounds.block_velocity_reindex e i j hb


-- @@ L225-238 verbatim
/-- The actual residual is sent to the new chart along with its context,
state, carrier and both excluded error coefficient families. -/
theorem residualBlock_uniform_pull {ι : Type*} (e : D ≃ₗᵢ[ℝ] E)
    {s : StripData E} {P : ι → ℕ → E → ℝ} {α : ℝ}
    (c : CorrectionState.Context E) (u : CorrectionState.State E)
    (b : ι → CorrectionState.HarmonicBlock E) (G A : ι → HarmonicResidual.BlockCoefficients E)
    (hb : UniformHarmonicInteraction.UniformVelocity s P α
      (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A l))) :
    UniformHarmonicInteraction.UniformVelocity (ParticularWaveBounds.reindexStrip e s)
      (fun l n x => P l n (e x)) α
      (fun l => HarmonicResidual.residualBlock (StateReindex.context e c)
        (StateReindex.state e u) (StateReindex.block e (b l))
        (StateReindex.blockCoefficients e (G l)) (StateReindex.blockCoefficients e (A l))) := by
  simpa only [StateReindex.residualBlock_pull] using uniformVelocity_pull e hb


-- @@ L240-257 verbatim
theorem residualBlock_velocity_uniform_return {ι : Type*} (e : D ≃ₗᵢ[ℝ] E)
    {s : StripData D} {w : ι → ℕ → D → ℝ} {α : ℝ}
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : ι → CorrectionState.HarmonicBlock D) (G A : ι → HarmonicResidual.BlockCoefficients D)
    (i : Fin 3) (j : ℤ)
    (hb : UniformClass (ParticularWaveBounds.reindexStrip e.symm s)
      (fun l n y => w l n (e.symm y)) α
      (fun l n y => (HarmonicResidual.residualBlock (StateReindex.context e.symm c)
        (StateReindex.state e.symm u) (StateReindex.block e.symm (b l))
        (StateReindex.blockCoefficients e.symm (G l))
        (StateReindex.blockCoefficients e.symm (A l))).velocity n i j y)) :
    UniformClass s w α
      (fun l n x => (HarmonicResidual.residualBlock c u (b l) (G l) (A l)).velocity n i j x) := by
  have hh := uniformClass_return e hb
  apply hh.congr
  intro l n x hx
  exact congrArg (fun B : CorrectionState.HarmonicBlock D => B.velocity n i j x)
    (residualBlock_return e c u (b l) (G l) (A l))


-- @@ L259-273 verbatim
/-- Actual residual classes proved in the associated solver chart return
to the original state without an extra operator-bounds hypothesis. -/
theorem residualBlock_uniform_return {ι : Type*} (e : D ≃ₗᵢ[ℝ] E)
    {s : StripData D} {P : ι → ℕ → D → ℝ} {α : ℝ}
    (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (b : ι → CorrectionState.HarmonicBlock D) (G A : ι → HarmonicResidual.BlockCoefficients D)
    (hb : UniformHarmonicInteraction.UniformVelocity (ParticularWaveBounds.reindexStrip e.symm s)
      (fun l n y => P l n (e.symm y)) α
      (fun l => HarmonicResidual.residualBlock (StateReindex.context e.symm c)
        (StateReindex.state e.symm u) (StateReindex.block e.symm (b l))
        (StateReindex.blockCoefficients e.symm (G l))
        (StateReindex.blockCoefficients e.symm (A l)))) :
    UniformHarmonicInteraction.UniformVelocity s P α
      (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A l)) := by
  simpa only [residualBlock_return] using uniformVelocity_return e hb


-- @@ L275-275 verbatim
section Association


-- @@ L277-277 verbatim
variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]


-- @@ L279-297 verbatim
/-- The exact association used by `CyclePoint` and the particular solver. -/
theorem residualBlock_liftAssoc_uniform_return {ι : Type*}
    {s : StripData (PressureStream.Lift S)} {P : ι → ℕ → PressureStream.Lift S → ℝ} {α : ℝ}
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S))
    (b : ι → CorrectionState.HarmonicBlock (PressureStream.Lift S))
    (G A : ι → HarmonicResidual.BlockCoefficients (PressureStream.Lift S))
    (hb : UniformHarmonicInteraction.UniformVelocity
      (ParticularWaveBounds.reindexStrip (ParticularWaveBounds.liftAssoc S).symm s)
      (fun l n y => P l n ((ParticularWaveBounds.liftAssoc S).symm y)) α
      (fun l => HarmonicResidual.residualBlock
        (StateReindex.context (ParticularWaveBounds.liftAssoc S).symm c)
        (StateReindex.state (ParticularWaveBounds.liftAssoc S).symm u)
        (StateReindex.block (ParticularWaveBounds.liftAssoc S).symm (b l))
        (StateReindex.blockCoefficients (ParticularWaveBounds.liftAssoc S).symm (G l))
        (StateReindex.blockCoefficients (ParticularWaveBounds.liftAssoc S).symm (A l)))) :
    UniformHarmonicInteraction.UniformVelocity s P α
      (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A l)) :=
  residualBlock_uniform_return (ParticularWaveBounds.liftAssoc S) c u b G A hb


-- @@ L299-299 verbatim
end Association


-- @@ L301-301 verbatim
end NavierStokes.MeanBoundsReindex
