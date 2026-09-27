/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVorticity
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerMaximal
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerContinuation


-- @@ L13-16 verbatim
/-! The actual nonnegative vorticity density of a maximal Euler solution
has an infinite extended integral whenever its genuine partial vorticity
integrals are unbounded. The only unboundedness input is the explicit
family statement used by the BKM continuation argument. -/


-- @@ L18-18 verbatim
section


-- @@ L20-22 verbatim
/-! Actual vorticity supremum norms and their partial integrals on a
half-open maximal Euler interval. All quantities agree exactly with
the genuine smooth solutions on every shorter closed interval. -/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace EulerOrdinarySobolev.FiniteLifespan


-- @@ L30-32 verbatim
open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerVectorCalculus EulerMeanCutoffCurl
  EulerVolterraConvolution EulerContinuousTimeIntegral

-- @@ L33-33 verbatim
open scoped ContDiff Topology


-- @@ L35-35 verbatim
variable {A : SmoothL2Field Space} (L : FiniteLifespan A)


-- @@ L37-50 verbatim
theorem vorticityIntegral_agrees (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (hST : S ≤ T)
    (t : Icc (0 : ℝ) S) :
    (L.evolution S hS hSL).vorticityIntegral t =
      (L.evolution T hT hTL).vorticityIntegral ⟨t,t.property.1,t.property.2.trans hST⟩ := by
  apply intervalIntegral.integral_congr
  intro r hr
  have hrs : r ∈ Icc (0 : ℝ) (t : ℝ) := by simpa only [uIcc_of_le t.property.1] using hr
  have hrS : r ∈ Icc (0 : ℝ) S := ⟨hrs.1,hrs.2.trans t.property.2⟩
  have hrT : r ∈ Icc (0 : ℝ) T := ⟨hrs.1,hrS.2.trans hST⟩
  change vorticityNorm ((L.evolution S hS hSL).velocity (projIcc 0 S hS.le r)) =
    vorticityNorm ((L.evolution T hT hTL).velocity (projIcc 0 T hT.le r))
  rw [projIcc_of_mem hS.le hrS,projIcc_of_mem hT.le hrT,
    L.evolution_agrees_at S T hS hT hSL hTL r hrs.1 hrS.2 hrT.2]


-- @@ L52-59 verbatim
theorem vorticityIntegral_agrees_at (S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hSL : S < L.duration) (hTL : T < L.duration) (t : ℝ)
    (ht0 : 0 ≤ t) (htS : t ≤ S) (htT : t ≤ T) :
    (L.evolution S hS hSL).vorticityIntegral ⟨t,ht0,htS⟩=
      (L.evolution T hT hTL).vorticityIntegral ⟨t,ht0,htT⟩ := by
  rcases le_total S T with hST | hTS
  · exact L.vorticityIntegral_agrees S T hS hT hSL hTL hST ⟨t,ht0,htS⟩
  · exact (L.vorticityIntegral_agrees T S hT hS hTL hSL hTS ⟨t,ht0,htT⟩).symm


-- @@ L61-62 verbatim
/-- Maximal vorticity norm, given by `vorticityNorm (L.maximalField t)`. -/
def maximalVorticityNorm (t : L.Time) : ℝ := vorticityNorm (L.maximalField t)


-- @@ L64-65 verbatim
theorem maximalVorticityNorm_nonneg (t : L.Time) : 0 ≤ L.maximalVorticityNorm t :=
  vorticityNorm_nonneg _


-- @@ L67-69 verbatim
theorem maximalVorticityNorm_le_iff (t : L.Time) (K : ℝ) :
    L.maximalVorticityNorm t ≤ K ↔ ∀ x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ K :=
  vorticityNorm_le_iff _ K


-- @@ L71-72 verbatim
theorem maximalVorticityNorm_continuous : Continuous L.maximalVorticityNorm :=
  vorticityNorm_continuous L.maximalField L.maximalField_jet_continuous


-- @@ L74-79 verbatim
theorem maximalVorticityNorm_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalVorticityNorm (L.shorterTime S hSL t)=(L.evolution S hS hSL).vorticityNormPath t := by
  change vorticityNorm (L.maximalField (L.shorterTime S hSL t))=_
  rw [L.maximalField_eq_evolution S hS hSL t]
  rfl


-- @@ L81-84 verbatim
/-- Maximal vorticity integral as an element of `ℝ`. -/
def maximalVorticityIntegral (t : L.Time) : ℝ :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).vorticityIntegral (L.intermediateTime t)


-- @@ L86-93 verbatim
theorem maximalVorticityIntegral_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalVorticityIntegral (L.shorterTime S hSL t) =
      (L.evolution S hS hSL).vorticityIntegral t :=
  L.vorticityIntegral_agrees_at (L.intermediateHorizon (L.shorterTime S hSL t)) S
    (L.intermediateHorizon_pos (L.shorterTime S hSL t)) hS
    (L.intermediateHorizon_lt (L.shorterTime S hSL t)) hSL t t.property.1
    (L.time_lt_intermediateHorizon (L.shorterTime S hSL t)).le t.property.2


-- @@ L95-97 verbatim
theorem maximalVorticityIntegral_nonneg (t : L.Time) : 0 ≤ L.maximalVorticityIntegral t :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).vorticityIntegral_nonneg (L.intermediateTime t)


-- @@ L99-101 verbatim
theorem maximalVorticityIntegral_initial : L.maximalVorticityIntegral L.initialTime=0 :=
  (L.evolution (L.intermediateHorizon L.initialTime) (L.intermediateHorizon_pos L.initialTime)
    (L.intermediateHorizon_lt L.initialTime)).vorticityIntegral_initial


-- @@ L103-110 verbatim
theorem maximalVorticityIntegral_continuous : Continuous L.maximalVorticityIntegral := by
  apply L.continuous_of_shorter_restrictions
  intro S hS hSL
  have he : (fun t : Icc (0 : ℝ) S => L.maximalVorticityIntegral (L.shorterTime S hSL t)) =
      (L.evolution S hS hSL).vorticityIntegral :=
    funext (L.maximalVorticityIntegral_eq_evolution S hS hSL)
  rw [he]
  exact (L.evolution S hS hSL).vorticityIntegral_continuous


-- @@ L112-124 verbatim
theorem maximalVorticityIntegral_mono : Monotone L.maximalVorticityIntegral := by
  intro s t hst
  let R := L.intermediateHorizon t
  have hR : 0 < R := L.intermediateHorizon_pos t
  have hRL : R < L.duration := L.intermediateHorizon_lt t
  have htR : (t : ℝ) ≤ R := (L.time_lt_intermediateHorizon t).le
  have hsR : (s : ℝ) ≤ R := (show (s : ℝ) ≤ t from hst).trans htR
  have hs := L.maximalVorticityIntegral_eq_evolution R hR hRL ⟨s,s.property.1,hsR⟩
  have ht := L.maximalVorticityIntegral_eq_evolution R hR hRL ⟨t,t.property.1,htR⟩
  change L.maximalVorticityIntegral s=_ at hs
  change L.maximalVorticityIntegral t=_ at ht
  rw [hs,ht]
  exact (L.evolution R hR hRL).vorticityIntegral_mono _ _ hst


-- @@ L126-138 verbatim
theorem vorticityIntegral_eventually_large_of_unbounded
    (hunbounded : ∀ G : ℝ, ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
      (t : Icc (0 : ℝ) S), G < (L.evolution S hS hSL).vorticityIntegral t)
    (G : ℝ) :
    ∃ (R : ℝ) (_hR : 0 < R) (_hRL : R < L.duration),
      ∀ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration), R ≤ S →
        G < (L.evolution S hS hSL).vorticityIntegral ⟨S,hS.le,le_rfl⟩ := by
  obtain ⟨R,hR,hRL,t,ht⟩ := hunbounded G
  refine ⟨R,hR,hRL,?_⟩
  intro S hS hSL hRS
  rw [L.vorticityIntegral_agrees R S hR hS hRL hSL hRS t] at ht
  exact ht.trans_le ((L.evolution S hS hSL).vorticityIntegral_mono
    ⟨t,t.property.1,t.property.2.trans hRS⟩ ⟨S,hS.le,le_rfl⟩ (t.property.2.trans hRS))


-- @@ L140-152 verbatim
theorem maximalVorticityIntegral_tendsto_atTop
    (hunbounded : ∀ G : ℝ, ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
      (t : Icc (0 : ℝ) S), G < (L.evolution S hS hSL).vorticityIntegral t) :
    Tendsto L.maximalVorticityIntegral (atTop : Filter L.Time) atTop := by
  apply tendsto_atTop.mpr
  intro G
  obtain ⟨R,hR,hRL,hlarge⟩ := L.vorticityIntegral_eventually_large_of_unbounded hunbounded G
  filter_upwards [eventually_ge_atTop (⟨R,hR.le,hRL⟩ : L.Time)] with t ht
  have htpos : 0 < (t : ℝ) := hR.trans_le ht
  have he := L.maximalVorticityIntegral_eq_evolution t htpos t.property.2 ⟨t,t.property.1,le_rfl⟩
  change L.maximalVorticityIntegral t=_ at he
  rw [he]
  exact (hlarge t htpos t.property.2 ht).le


-- @@ L154-154 verbatim
end EulerOrdinarySobolev.FiniteLifespan


-- @@ L156-156 verbatim
end

-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end


-- @@ L161-161 verbatim
section


-- @@ L163-166 verbatim
/-! Unbounded finite partial integrals of a nonnegative function force
its extended integral on the half-open interval to be infinite. Local
integrability is explicit, so no totalized real integral is used as a
substitute for an improper integral. -/


-- @@ L168-168 verbatim
@[expose] public section


-- @@ L170-170 verbatim
noncomputable section


-- @@ L172-172 verbatim
namespace EulerNonnegativeImproperIntegral


-- @@ L174-174 verbatim
open Set MeasureTheory

-- @@ L175-175 verbatim
open scoped ENNReal


-- @@ L177-185 verbatim
theorem ofReal_partial_le_lintegral (f : ℝ → ℝ) {S T : ℝ}
    (hS : 0 ≤ S) (hST : S < T) (hf : IntervalIntegrable f volume 0 S)
    (hnonneg : ∀ x ∈ Ioc (0 : ℝ) S, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in (0 : ℝ)..S, f x) ≤
      ∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x) := by
  rw [intervalIntegral.integral_of_le hS,
    ofReal_integral_eq_lintegral_ofReal hf.1
      (ae_restrict_of_forall_mem measurableSet_Ioc hnonneg)]
  exact lintegral_mono_set (fun _ hx => ⟨hx.1.le,hx.2.trans_lt hST⟩)


-- @@ L187-198 verbatim
theorem lintegral_eq_top_of_unbounded_partials (f : ℝ → ℝ) (T : ℝ)
    (hf : ∀ S : ℝ, 0 < S → S < T → IntervalIntegrable f volume 0 S)
    (hnonneg : ∀ x ∈ Ico (0 : ℝ) T, 0 ≤ f x)
    (hunbounded : ∀ K : ℝ, ∃ S : ℝ, 0 < S ∧ S < T ∧
      K < ∫ x in (0 : ℝ)..S, f x) :
    (∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x))=⊤ := by
  by_contra hfinite
  obtain ⟨S,hS,hST,hK⟩ := hunbounded
    (∫⁻ x in Ico (0 : ℝ) T, ENNReal.ofReal (f x)).toReal
  have hb := ofReal_partial_le_lintegral f hS.le hST (hf S hS hST)
    (fun x hx => hnonneg x ⟨hx.1.le,hx.2.trans_lt hST⟩)
  exact (not_lt_of_ge hb) ((ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr hK)


-- @@ L200-200 verbatim
end EulerNonnegativeImproperIntegral


-- @@ L202-202 verbatim
end

-- @@ L203-203 verbatim
end


-- @@ L205-205 verbatim
end


-- @@ L207-207 verbatim
@[expose] public section


-- @@ L209-209 verbatim
noncomputable section


-- @@ L211-211 verbatim
namespace EulerOrdinarySobolev.FiniteLifespan


-- @@ L213-215 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanCutoffCurl
  EulerVolterraConvolution EulerContinuousTimeIntegral

-- @@ L216-216 verbatim
open scoped ENNReal


-- @@ L218-218 verbatim
variable {A : SmoothL2Field Space} (L : FiniteLifespan A)


-- @@ L220-224 verbatim
/-- The true vorticity supremum on the lifespan, extended by zero only
to make the ambient real-time integral available. -/
def maximalVorticityDensity (r : ℝ) : ℝ := by
  classical
  exact if hr : r ∈ Ico (0 : ℝ) L.duration then L.maximalVorticityNorm ⟨r,hr⟩ else 0


-- @@ L226-231 verbatim
theorem maximalVorticityDensity_nonneg (r : ℝ) : 0 ≤ L.maximalVorticityDensity r := by
  classical
  unfold maximalVorticityDensity
  split
  · exact L.maximalVorticityNorm_nonneg _
  · exact le_rfl


-- @@ L233-235 verbatim
theorem maximalVorticityDensity_measurable : Measurable L.maximalVorticityDensity := by
  classical
  exact L.maximalVorticityNorm_continuous.measurable.dite measurable_const measurableSet_Ico


-- @@ L237-240 verbatim
theorem maximalVorticityDensity_eq (t : L.Time) :
    L.maximalVorticityDensity t=L.maximalVorticityNorm t := by
  classical
  simp only [maximalVorticityDensity,dite_eq_left t.property]


-- @@ L242-245 verbatim
theorem maximalVorticityDensity_le_iff (t : L.Time) (K : ℝ) :
    L.maximalVorticityDensity t ≤ K ↔ ∀ x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ K := by
  rw [L.maximalVorticityDensity_eq]
  exact L.maximalVorticityNorm_le_iff t K


-- @@ L247-253 verbatim
theorem maximalVorticityDensity_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalVorticityDensity t=(L.evolution S hS hSL).vorticityNormPath t := by
  classical
  have ht : (t : ℝ) ∈ Ico (0 : ℝ) L.duration := ⟨t.property.1,t.property.2.trans_lt hSL⟩
  rw [maximalVorticityDensity,dite_eq_left ht]
  exact L.maximalVorticityNorm_eq_evolution S hS hSL t


-- @@ L255-265 verbatim
theorem maximalVorticityDensity_continuousOn (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) :
    ContinuousOn L.maximalVorticityDensity (Icc (0 : ℝ) S) := by
  have hc : Continuous (fun r : ℝ =>
      (L.evolution S hS hSL).vorticityNormPath (projIcc 0 S hS.le r)) :=
    (L.evolution S hS hSL).vorticityNormPath.continuous.comp continuous_projIcc
  apply hc.continuousOn.congr
  intro r hr
  change L.maximalVorticityDensity r =
    (L.evolution S hS hSL).vorticityNormPath (projIcc 0 S hS.le r)
  rw [projIcc_of_mem hS.le hr]
  exact L.maximalVorticityDensity_eq_evolution S hS hSL ⟨r,hr⟩


-- @@ L267-269 verbatim
theorem maximalVorticityDensity_intervalIntegrable (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) : IntervalIntegrable L.maximalVorticityDensity volume 0 S :=
  (L.maximalVorticityDensity_continuousOn S hS hSL).intervalIntegrable_of_Icc hS.le


-- @@ L271-283 verbatim
theorem maximalVorticityDensity_integral_eq_evolution (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) (t : Icc (0 : ℝ) S) :
    (∫ r in (0 : ℝ)..(t : ℝ), L.maximalVorticityDensity r) =
      (L.evolution S hS hSL).vorticityIntegral t := by
  apply intervalIntegral.integral_congr
  intro r hr
  have hrt : r ∈ Icc (0 : ℝ) (t : ℝ) := by
    simpa only [uIcc_of_le t.property.1] using hr
  have hrS : r ∈ Icc (0 : ℝ) S := ⟨hrt.1,hrt.2.trans t.property.2⟩
  change L.maximalVorticityDensity r =
    (L.evolution S hS hSL).vorticityNormPath (projIcc 0 S hS.le r)
  rw [projIcc_of_mem hS.le hrS]
  exact L.maximalVorticityDensity_eq_evolution S hS hSL ⟨r,hrS⟩


-- @@ L285-288 verbatim
theorem maximalVorticityDensity_integral_eq (t : L.Time) :
    (∫ r in (0 : ℝ)..(t : ℝ), L.maximalVorticityDensity r)=L.maximalVorticityIntegral t :=
  L.maximalVorticityDensity_integral_eq_evolution (L.intermediateHorizon t)
    (L.intermediateHorizon_pos t) (L.intermediateHorizon_lt t) (L.intermediateTime t)


-- @@ L290-305 verbatim
/-- This is the improper integral as an extended nonnegative integral,
not the totalized real Bochner integral at the singular endpoint. -/
theorem maximalVorticity_lintegral_eq_top
    (hunbounded : ∀ G : ℝ, ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
      (t : Icc (0 : ℝ) S), G < (L.evolution S hS hSL).vorticityIntegral t) :
    (∫⁻ r in Ico (0 : ℝ) L.duration, ENNReal.ofReal (L.maximalVorticityDensity r))=⊤ := by
  apply EulerNonnegativeImproperIntegral.lintegral_eq_top_of_unbounded_partials
    L.maximalVorticityDensity L.duration
    L.maximalVorticityDensity_intervalIntegrable
    (fun r _ => L.maximalVorticityDensity_nonneg r)
  intro K
  obtain ⟨S,hS,hSL,t,hK⟩ := hunbounded K
  refine ⟨S,hS,hSL,?_⟩
  rw [L.maximalVorticityDensity_integral_eq_evolution S hS hSL ⟨S,hS.le,le_rfl⟩]
  exact hK.trans_le ((L.evolution S hS hSL).vorticityIntegral_mono
    t ⟨S,hS.le,le_rfl⟩ t.property.2)


-- @@ L307-307 verbatim
end EulerOrdinarySobolev.FiniteLifespan
