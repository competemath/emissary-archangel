/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedAxisPreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.CutStageEstimates


-- @@ L12-21 verbatim
/-!
# Direct angular diagonal from local raw data

The raw angular means need be smooth only where the actual physical
similarity parameter is below `qbig`.  All cutoffs use the same sequence.
Its first support lies strictly inside that raw domain.  Above the raw
domain every cutoff vanishes on one common neighborhood, so the original
sum itself is smooth and divergence-free on the whole preterminal region.
No global smooth replacement of the raw scalar is chosen.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace NavierStokes.LocalAngularDiagonal


-- @@ L30-30 verbatim
open Set Function Filter ProblemStatement

-- @@ L31-31 verbatim
open scoped Topology ContDiff BigOperators


-- @@ L33-36 verbatim
/-- The actual similarity parameter depends only on physical time and the
axial coordinate, and not on radius or angle. -/
noncomputable def slowQ (h : ℝ) (s : DirectAngularDiagonal.Slow) : ℝ :=
  SimilarityCoordinates.coordinateQ (2 * h) (1 - s.1, s.2)


-- @@ L38-40 verbatim
/-- Local slow domain, given by `{s | s.1 < 1 ∧ slowQ h s < qbig}`. -/
noncomputable def localSlowDomain (h qbig : ℝ) : Set DirectAngularDiagonal.Slow :=
  {s | s.1 < 1 ∧ slowQ h s < qbig}


-- @@ L42-43 verbatim
theorem slowQ_physical (h : ℝ) (w : SpaceTime) :
    slowQ h (DirectAngularDiagonal.slowPoint w) = PhysicalWaveSum.physicalQ h w := rfl


-- @@ L45-49 verbatim
theorem slowQ_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {s : DirectAngularDiagonal.Slow} (hs : s.1 < 1) : ContDiffAt ℝ ∞ (slowQ h) s := by
  exact (SimilarityCoordinates.coordinateQ_smooth (by linarith : 0 < 2 * h)
    (by linarith : 2 * h < 1) (p := (1 - s.1, s.2)) (sub_pos.mpr hs)).comp s
    ((contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd)


-- @@ L51-56 verbatim
theorem localSlowDomain_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (qbig : ℝ) :
    IsOpen (localSlowDomain h qbig) := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  exact Filter.inter_mem (DirectAngularDiagonal.preterminalSlow_open.mem_nhds hs.1)
    ((slowQ_smoothAt hh hh1 hs.1).continuousAt (gt_mem_nhds hs.2))


-- @@ L58-60 verbatim
theorem physicalDomain_eq_localDomain (h qbig : ℝ) :
    DirectAngularDiagonal.physicalDomain (localSlowDomain h qbig) =
      MixedAxisPreservation.localDomain h qbig := rfl


-- @@ L62-64 verbatim
theorem physicalDomain_eq_physicalSublevel (h qbig : ℝ) :
    DirectAngularDiagonal.physicalDomain (localSlowDomain h qbig) =
      CutStageEstimates.physicalSublevel h qbig := rfl


-- @@ L66-67 verbatim
theorem localSlowDomain_subset (h qbig : ℝ) :
    localSlowDomain h qbig ⊆ DirectAngularDiagonal.preterminalSlow := fun _ hs => hs.1


-- @@ L69-69 verbatim
variable {h qbig : ℝ}


-- @@ L71-74 verbatim
/-- The literal uncut direct angular fields used in the diagonal. -/
noncomputable def rawSeries
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig)) : ℕ → VelocityField :=
  fun j => DirectAngularDiagonal.angularField (D j).scalar


-- @@ L76-78 verbatim
theorem rawSeries_eq
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig)) (j : ℕ) :
    rawSeries D j = DirectAngularDiagonal.angularField (D j).scalar := rfl


-- @@ L80-83 verbatim
theorem rawSeries_smooth (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig)) (j : ℕ) :
    ContDiffOn ℝ ∞ (rawSeries D j) (CutStageEstimates.physicalSublevel h qbig) :=
  (D j).field_smooth (localSlowDomain_open hh hh1 qbig)


-- @@ L85-90 verbatim
/-- Axis preservation uses exactly the same local scalars and support,
without imposing global raw smoothness. -/
noncomputable def angularSupport
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig)) :
    ℕ → MixedAxisPreservation.AngularSupport (MixedAxisPreservation.localDomain h qbig) :=
  fun j => MixedAxisPreservation.AngularSupport.ofAngularData (D j) (fun _ hw => hw)


-- @@ L92-94 verbatim
theorem angularSupport_field
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig)) (j : ℕ) :
    (angularSupport D j).field = rawSeries D j := rfl


-- @@ L96-99 verbatim
theorem angularSum_eq_potentialSum
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig)) (a : ℕ → ℝ) :
    DirectAngularDiagonal.angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar) =
      SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) (rawSeries D) := rfl


-- @@ L101-104 verbatim
theorem angularSum_eq_directDiagonal
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig)) (a : ℕ → ℝ) :
    DirectAngularDiagonal.angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar) =
      MixedAxisPreservation.directDiagonal h (angularSupport D) a := rfl


-- @@ L106-106 verbatim
/-! ## One common zero neighborhood above the cutoff support -/


-- @@ L108-117 verbatim
theorem cutStages_zero_germ {a : ℕ → ℝ} (ha0 : 0 < a 0) (ham : ∀ j, a 0 ≤ a j)
    {q : SpaceTime → ℝ} {w : SpaceTime} (hq : ContinuousAt q w)
    (hlarge : 1 / a 0 < q w) (F : ℕ → VelocityField) :
    ∀ᶠ y in 𝓝 w, ∀ j, SolenoidalDiagonal.cutStage a q F j y = 0 := by
  filter_upwards [hq (lt_mem_nhds hlarge)] with y hy
  intro j
  have haj := ha0.trans_le (ham j)
  have hz := SmoothCutoffs.scaledCutoff_zero_of_inv_le haj
    ((one_div_le_one_div_of_le ha0 (ham j)).trans hy.le)
  simp only [SolenoidalDiagonal.cutStage, hz, zero_smul]


-- @@ L119-124 verbatim
theorem sum_zero_germ {a : ℕ → ℝ} (ha0 : 0 < a 0) (ham : ∀ j, a 0 ≤ a j)
    {q : SpaceTime → ℝ} {w : SpaceTime} (hq : ContinuousAt q w)
    (hlarge : 1 / a 0 < q w) (F : ℕ → VelocityField) :
    SolenoidalDiagonal.potentialSum a q F =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [cutStages_zero_germ ha0 ham hq hlarge F] with y hy
  simp only [SolenoidalDiagonal.potentialSum, hy, tsum_zero]


-- @@ L126-133 verbatim
theorem angularSum_zero_germ (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig))
    {a : ℕ → ℝ} (ha0 : 0 < a 0) (ham : ∀ j, a 0 ≤ a j) (hgap : 1 / a 0 < qbig)
    {w : SpaceTime} (ht : w.1 < 1) (hq : qbig ≤ PhysicalWaveSum.physicalQ h w) :
    DirectAngularDiagonal.angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar)
      =ᶠ[𝓝 w] fun _ => 0 :=
  sum_zero_germ ha0 ham (PhysicalWaveSum.physicalQ_smoothAt hh hh1 ht).continuousAt
    (hgap.trans_le hq) (rawSeries D)


-- @@ L135-139 verbatim
theorem spatialCut_zero_germ {f : VelocityField} {w : SpaceTime}
    (hf : f =ᶠ[𝓝 w] fun _ => 0) :
    SpatialLocalization.cutPotential f =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [hf] with y hy
  simp only [SpatialLocalization.cutPotential, hy, smul_zero]


-- @@ L141-141 verbatim
/-! ## Smoothness on the whole preterminal region -/


-- @@ L143-157 verbatim
theorem angularSum_smoothAt (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig))
    {a : ℕ → ℝ} (hat : Tendsto a atTop atTop) (ha0 : 0 < a 0)
    (ham : ∀ j, a 0 ≤ a j) (hgap : 1 / a 0 < qbig)
    {w : SpaceTime} (ht : w.1 < 1) :
    ContDiffAt ℝ ∞
      (DirectAngularDiagonal.angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar)) w
          := by
  by_cases hq : PhysicalWaveSum.physicalQ h w < qbig
  · exact (DirectAngularDiagonal.angularSum_smooth (localSlowDomain_open hh hh1 qbig) D hat
      (fun _ hx => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hx.1).contDiffWithinAt)
      (fun _ hx => PhysicalWaveSum.physicalQ_pos hh hh1 hx.1)).contDiffAt
      ((MixedAxisPreservation.localDomain_open hh hh1 qbig).mem_nhds ⟨ht, hq⟩)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (angularSum_zero_germ hh hh1 D ha0 ham hgap ht (le_of_not_gt hq))


-- @@ L159-166 verbatim
theorem angularSum_smooth (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig))
    {a : ℕ → ℝ} (hat : Tendsto a atTop atTop) (ha0 : 0 < a 0)
    (ham : ∀ j, a 0 ≤ a j) (hgap : 1 / a 0 < qbig) :
    ContDiffOn ℝ ∞
      (DirectAngularDiagonal.angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar))
      PhysicalWaveSum.preterminal :=
  fun _ ht => (angularSum_smoothAt hh hh1 D hat ha0 ham hgap ht).contDiffWithinAt


-- @@ L168-171 verbatim
theorem qCoefficient_smooth (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (DirectAngularDiagonal.qCoefficient h)
      (DirectAngularDiagonal.positiveDomain (localSlowDomain h qbig)) :=
  (DirectAngularDiagonal.qCoefficient_smooth hh hh1).mono (fun _ hp => ⟨hp.1.1, hp.2⟩)


-- @@ L173-177 verbatim
theorem physicalQ_smooth (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (fun w => DirectAngularDiagonal.qCoefficient h (DirectAngularDiagonal.cylPoint
        w))
      (DirectAngularDiagonal.physicalDomain (localSlowDomain h qbig)) :=
  fun _ hw => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 hw.1).contDiffWithinAt


-- @@ L179-193 verbatim
theorem angularSum_divergence (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig))
    {a : ℕ → ℝ} (hat : Tendsto a atTop atTop) (ha0 : 0 < a 0)
    (ham : ∀ j, a 0 ≤ a j) (hgap : 1 / a 0 < qbig)
    {w : SpaceTime} (ht : w.1 < 1) :
    spatialDivergence
      (DirectAngularDiagonal.angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar))
      w.1 w.2 = 0 := by
  by_cases hq : PhysicalWaveSum.physicalQ h w < qbig
  · exact DirectAngularDiagonal.angularSum_divergence (localSlowDomain_open hh hh1 qbig) D hat
      (DirectAngularDiagonal.qCoefficient h) (qCoefficient_smooth hh hh1) (physicalQ_smooth hh hh1)
      (fun _ hx => PhysicalWaveSum.physicalQ_pos hh hh1 hx.1) (x := w) ⟨ht, hq⟩
  · rw [DirectAngularDiagonal.divergence_congr
      (angularSum_zero_germ hh hh1 D ha0 ham hgap ht (le_of_not_gt hq))]
    simp [spatialDivergence, spatialDerivative]


-- @@ L195-212 verbatim
/-- Multiplication by the existing axisymmetric spatial cutoff preserves
divergence of the same local-data diagonal on every preterminal point. -/
theorem spatialCut_angularSum_divergence (hh : 0 < h) (hh1 : h < 1 / 2)
    (D : ℕ → DirectAngularDiagonal.AngularData (localSlowDomain h qbig))
    {a : ℕ → ℝ} (hat : Tendsto a atTop atTop) (ha0 : 0 < a 0)
    (ham : ∀ j, a 0 ≤ a j) (hgap : 1 / a 0 < qbig)
    (t : ℝ) (ht : t < 1) (x : Space) :
    spatialDivergence (SpatialLocalization.cutPotential
      (DirectAngularDiagonal.angularSum a (PhysicalWaveSum.physicalQ h) (fun j => (D j).scalar))) t
          x = 0 := by
  by_cases hq : PhysicalWaveSum.physicalQ h (t, x) < qbig
  · exact DirectAngularDiagonal.spatialCut_angularSum_divergence
      (localSlowDomain_open hh hh1 qbig) D hat (DirectAngularDiagonal.qCoefficient h)
      (qCoefficient_smooth hh hh1) (physicalQ_smooth hh hh1)
      (fun _ hx => PhysicalWaveSum.physicalQ_pos hh hh1 hx.1) (x := (t, x)) ⟨ht, hq⟩
  · rw [DirectAngularDiagonal.divergence_congr (spatialCut_zero_germ
      (angularSum_zero_germ hh hh1 D ha0 ham hgap (w := (t, x)) ht (le_of_not_gt hq)))]
    simp [spatialDivergence, spatialDerivative]


-- @@ L214-214 verbatim
end NavierStokes.LocalAngularDiagonal
