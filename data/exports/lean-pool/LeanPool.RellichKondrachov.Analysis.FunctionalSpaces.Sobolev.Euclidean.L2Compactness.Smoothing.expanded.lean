/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict
public import Mathlib.Analysis.Convolution


-- @@ L11-23 verbatim
/-!
# `L²` compactness criterion: smoothing setup (Euclidean)

This file provides the basic “extend by zero + smooth by convolution” infrastructure used in the
Fréchet–Kolmogorov / Riesz–Kolmogorov approach to Euclidean Rellich–Kondrachov.

## Main results

- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.extendByZeroL2`:
  extend `u : L²(volume.restrict K)` by zero to an element of `L²(volume)`.
- `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothL2`:
  a smoothing operator obtained by convolution with a compactly supported continuous kernel `ψ`.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace RellichKondrachov

-- @@ L28-28 verbatim
namespace Analysis

-- @@ L29-29 verbatim
namespace FunctionalSpaces

-- @@ L30-30 verbatim
namespace Sobolev

-- @@ L31-31 verbatim
namespace Euclidean

-- @@ L32-32 verbatim
namespace L2Compactness


-- @@ L34-34 verbatim
open scoped ENNReal MeasureTheory Topology Convolution Pointwise

-- @@ L35-35 verbatim
open MeasureTheory Set


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
section


-- @@ L41-41 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


-- @@ L43-44 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceSmoothing : MeasurableSpace E := borel E

-- @@ L45-45 verbatim
local instance instBorelSpaceSmoothing : BorelSpace E := ⟨rfl⟩

-- @@ L46-47 verbatim
local instance instOpensMeasurableSpaceSmoothing : OpensMeasurableSpace E := by
  infer_instance

-- @@ L48-49 verbatim
local instance instMeasurableAddSmoothing : MeasurableAdd E := by
  infer_instance


-- @@ L51-56 verbatim
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private lemma tsupport_indicator_subset_closure (s : Set E) (f : E → ℝ) :
    tsupport (s.indicator f) ⊆ closure s := by
  -- `Function.support (s.indicator f) ⊆ s`, hence the topological support is contained in
  -- `closure s`.
  simpa [tsupport] using closure_mono (Set.support_indicator_subset (s := s) (f := f))


-- @@ L58-65 verbatim
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private lemma hasCompactSupport_indicator_of_isCompact (s : Set E) (hs : IsCompact s) (f : E → ℝ) :
    HasCompactSupport (s.indicator f) := by
  have hs_closed : IsClosed s := hs.isClosed
  -- `tsupport (s.indicator f)` is closed and contained in the compact set `s`.
  refine hs.of_isClosed_subset (isClosed_tsupport _) ?_
  have : tsupport (s.indicator f) ⊆ closure s := tsupport_indicator_subset_closure (E := E) s f
  simpa [hs_closed.closure_eq] using this


-- @@ L67-67 verbatim
end


-- @@ L69-69 verbatim
section Volume


-- @@ L71-73 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- `volume` is the canonical Haar measure on finite-dimensional real vector spaces.

-- @@ L74-75 verbatim
/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceSmoothing1 : MeasurableSpace E := borel E

-- @@ L76-76 verbatim
local instance instBorelSpaceSmoothing1 : BorelSpace E := ⟨rfl⟩

-- @@ L77-78 verbatim
local instance instOpensMeasurableSpaceSmoothing1 : OpensMeasurableSpace E := by
  infer_instance

-- @@ L79-80 verbatim
local instance instMeasurableAddSmoothing1 : MeasurableAdd E := by
  infer_instance


-- @@ L82-82 verbatim
variable {K : Set E}


-- @@ L84-86 verbatim
/-- Extend an `L²` function on `K` by zero to a pointwise function on the ambient space. -/
def extendByZeroFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  K.indicator fun x : E => u x


-- @@ L88-94 verbatim
lemma hasCompactSupport_extendByZeroFun (hK : IsCompact K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (extendByZeroFun (K := K) u) := by
  classical
  -- The indicator is pointwise supported in `K`.
  simpa [extendByZeroFun] using
    (hasCompactSupport_indicator_of_isCompact (E := E) (s := K) hK (f := fun x => u x))


-- @@ L96-108 verbatim
/-- `extendByZeroFun` packaged as an element of `L²(volume)`. -/
noncomputable def extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (E →₂[(volume : Measure E)] ℝ) := by
  classical
  have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
    MeasureTheory.Lp.memLp u
  have hm :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u) (2 : ℝ≥0∞) (volume : Measure E) := by
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  exact hm.toLp (extendByZeroFun (K := K) u)


-- @@ L110-115 verbatim
lemma extendByZeroL2_ae_eq (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
      extendByZeroFun (E := E) (K := K) u := by
  classical
  simp [extendByZeroL2, MeasureTheory.MemLp.coeFn_toLp]


-- @@ L117-136 verbatim
lemma extendByZeroL2_eq_extendByZeroₗᵢ (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    extendByZeroL2 (E := E) (K := K) hKm u =
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  refine MeasureTheory.Lp.ext ?_
  have h1 :
      (extendByZeroL2 (E := E) (K := K) hKm u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u :=
    extendByZeroL2_ae_eq (E := E) (K := K) hKm u
  have h2 :
      ((MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u : E → ℝ) =ᵐ[(volume : Measure E)]
        extendByZeroFun (E := E) (K := K) u := by
    exact
      (MeasureTheory.Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure E)) (E := ℝ)
        (p := (2 : ℝ≥0∞)) (s := K) hKm u)
  exact h1.trans h2.symm


-- @@ L138-150 verbatim
lemma norm_extendByZeroL2 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ = ‖u‖ := by
  classical
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  calc
    ‖extendByZeroL2 (E := E) (K := K) hKm u‖ =
        ‖(MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
          (s := K) hKm) u‖ := by
          simp [extendByZeroL2_eq_extendByZeroₗᵢ (E := E) (K := K) hKm u]
    _ = ‖u‖ :=
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm).norm_map u

-- @@ L151-151 verbatim
variable (ψ : E → ℝ)


-- @@ L153-155 verbatim
/-- Smoothing by convolution with a fixed kernel `ψ`, applied to the zero-extension from `K`. -/
def smoothFun (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : E → ℝ :=
  (extendByZeroFun (K := K) u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ


-- @@ L157-179 verbatim
lemma continuous_smoothFun
    (hKm : MeasurableSet K) (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Continuous (smoothFun (K := K) ψ u) := by
  -- `extendByZeroFun u` is `L²`, hence locally integrable; convolution with a compactly supported
  -- continuous kernel is continuous.
  have hf_memLp :
      MeasureTheory.MemLp (extendByZeroFun (K := K) u)
        (2 : ℝ≥0∞) (volume : Measure E) := by
    have hu : MeasureTheory.MemLp (fun x : E => u x) (2 : ℝ≥0∞) (volume.restrict K) :=
      MeasureTheory.Lp.memLp u
    simpa [extendByZeroFun] using
      (MeasureTheory.memLp_indicator_iff_restrict (μ := (volume : Measure E)) (p := (2 : ℝ≥0∞))
          (s := K) (f := fun x : E => u x) hKm).2 hu
  have hf_loc :
      MeasureTheory.LocallyIntegrable (extendByZeroFun (K := K) u)
        (volume : Measure E) := by
    have h12 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
    exact hf_memLp.locallyIntegrable h12
  simpa [smoothFun] using
    (hψcs.continuous_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hf_loc hψc)


-- @@ L181-188 verbatim
lemma hasCompactSupport_smoothFun (hK : IsCompact K) (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    HasCompactSupport (smoothFun (K := K) ψ u) := by
  have hf : HasCompactSupport (extendByZeroFun (K := K) u) :=
    hasCompactSupport_extendByZeroFun (K := K) hK u
  simpa [smoothFun] using
    (hf.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hψcs)


-- @@ L190-204 verbatim
lemma support_smoothFun_subset_add_tsupport
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    Function.support (smoothFun (E := E) (K := K) ψ u) ⊆ K + tsupport ψ := by
  classical
  have hsupp :
      Function.support (smoothFun (E := E) (K := K) ψ u) ⊆
        Function.support (extendByZeroFun (E := E) (K := K) u) + Function.support ψ := by
    simpa [smoothFun] using
      (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))
        (f := extendByZeroFun (E := E) (K := K) u) (g := ψ))
  have h1 : Function.support (extendByZeroFun (E := E) (K := K) u) ⊆ K := by
    simp [extendByZeroFun]
  have h2 : Function.support ψ ⊆ tsupport ψ := by
    simpa [tsupport] using (subset_closure : Function.support ψ ⊆ closure (Function.support ψ))
  exact hsupp.trans (add_subset_add h1 h2)


-- @@ L206-215 verbatim
/-- `smoothFun` packaged as an element of `L²(volume)`. -/
noncomputable def smoothL2 (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) : (E →₂[(volume : Measure E)] ℝ) :=
  let hs : HasCompactSupport (smoothFun (K := K) ψ u) :=
    hasCompactSupport_smoothFun (K := K) ψ hK hψcs u
  let hm : MeasureTheory.MemLp (smoothFun (K := K) ψ u) (2 : ℝ≥0∞) (volume : Measure E) := by
    have hc : Continuous (smoothFun (K := K) ψ u) := continuous_smoothFun (K := K) ψ hKm hψc hψcs u
    exact hc.memLp_of_hasCompactSupport (μ := (volume : Measure E)) hs
  hm.toLp (smoothFun (K := K) ψ u)


-- @@ L217-223 verbatim
lemma smoothL2_ae_eq (hK : IsCompact K) (hKm : MeasurableSet K) (hψc : Continuous ψ)
    (hψcs : HasCompactSupport ψ)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    (smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u : E → ℝ) =ᵐ[(volume : Measure E)]
      smoothFun (E := E) (K := K) ψ u := by
  classical
  simp [smoothL2, MeasureTheory.MemLp.coeFn_toLp]

-- @@ L224-224 verbatim
end Volume


-- @@ L226-226 verbatim
end


-- @@ L228-228 verbatim
end L2Compactness

-- @@ L229-229 verbatim
end Euclidean

-- @@ L230-230 verbatim
end Sobolev

-- @@ L231-231 verbatim
end FunctionalSpaces

-- @@ L232-232 verbatim
end Analysis

-- @@ L233-233 verbatim
end RellichKondrachov
