/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.DivergenceFreeIntegrand


-- @@ L10-29 verbatim
/-!
# The integrand of the weak momentum identity

The weak momentum clause of `def:sws` pairs an identity with an integrability
side condition on its integrand, stated on the closed support of the
vector-valued test field `φ`.  The integrand has five terms: the time
derivative term `uᵢ ∂ₜφᵢ`, the nonlinear term `uᵢ uⱼ ∂ⱼφᵢ`, the viscous term
`Duᵢⱼ ∂ⱼφᵢ`, the pressure term `p ∂ᵢφᵢ` and the force term `fᵢ φᵢ`.

This file proves that side condition from the data clauses alone.  The closed
support is compact, so Lebesgue measure restricted to it is finite; on a finite
measure every exponent above `1` is integrable, and a product of two square
integrable factors is integrable by the Cauchy-Schwarz inequality.  That is all
the nonlinear term needs: no parabolic interpolation enters here, because the
test field confines the integral to a set of finite measure.  Each term is then
an integrable field times a bounded derivative of the test field.

Nothing about the identities of `def:sws` is used, so the conclusion is
available while those identities are still being established.
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
open MeasureTheory MeasureTheory.Measure Set Filter

-- @@ L34-34 verbatim
open scoped ENNReal NNReal Topology

-- @@ L35-35 verbatim
open CKN.Foundation.Parabolic



-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
namespace CKN


-- @@ L42-42 verbatim
variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}

-- @@ L43-43 verbatim
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}

-- @@ L44-44 verbatim
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}


-- @@ L46-46 verbatim
/-! ### Components of a vector-valued test field -/


-- @@ L48-56 verbatim
/-- Each component of a vector-valued space-time test field is a scalar
space-time test field on the same carrier. -/
theorem component_mem_spaceTimeTestFunction {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) (i : Fin 3) :
    (fun w : Vec3 × ℝ => φ w i) ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
  obtain ⟨hd, hc, hs⟩ := hφ
  refine ⟨(ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).contDiff.comp hd, ?_, ?_⟩
  · exact hc.comp_left (g := fun v : Vec3 => v i) rfl
  · exact (tsupport_component_subset φ i fun z hz => by rw [hz]; rfl).trans hs


-- @@ L58-58 verbatim
/-! ### The fields of the momentum integrand on a compact set -/


-- @@ L60-60 verbatim
variable {K : Set ParabolicPoint}


-- @@ L62-72 verbatim
/-- A product of two velocity components is integrable on a compact subset of
the carrier: both factors are square integrable there, and the Cauchy-Schwarz
inequality pairs the exponents `2` and `2` into `1`. -/
theorem velocity_pair_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) (i j : Fin 3) :
    IntegrableOn (fun z => u z i * u z j) K volume := by
  have hu : MemLp u 2 (volume.restrict K) :=
    velocity_memLp_two_on_compact_of_data hdata hK hKsub
  exact (hu.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)).integrable_mul
    (hu.continuousLinearMap_comp (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ))


-- @@ L74-84 verbatim
/-- Each entry of the velocity gradient is integrable on a compact subset of
the carrier. -/
theorem gradient_entry_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) (i j : Fin 3) :
    IntegrableOn (fun z => Du z i j) K volume := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict_of_isCompact hK
  exact (((gradient_memLp_two_on_compact_of_data hdata hK hKsub).continuousLinearMap_comp
    (ContinuousLinearMap.proj i : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
    (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)).integrable (by norm_num)


-- @@ L86-96 verbatim
/-- The pressure is integrable on a compact subset of the carrier: it is
`L^{3/2}` there and the restricted measure is finite. -/
theorem pressure_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    IntegrableOn p K volume := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict_of_isCompact hK
  refine (pressure_memLp_threeHalves_on_compact_of_data hdata hK hKsub).integrable ?_
  rw [ENNReal.one_le_ofReal]
  norm_num


-- @@ L98-110 verbatim
/-- Each component of the force is integrable on a compact subset of the
carrier: it is `L^q` there with `q > 5 / 2 > 1`, and the restricted measure is
finite. -/
theorem force_component_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) (i : Fin 3) :
    IntegrableOn (fun z => f z i) K volume := by
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict_of_isCompact hK
  refine ((force_memLp_on_compact_of_data hdata hK hKsub).continuousLinearMap_comp
    (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)).integrable ?_
  rw [ENNReal.one_le_ofReal]
  linarith only [hdata.five_halves_lt_exponent]


-- @@ L112-112 verbatim
/-! ### The five terms of the momentum integrand -/


-- @@ L114-114 verbatim
section Terms


-- @@ L116-118 verbatim
variable (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
  (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I)
  {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I)


-- @@ L120-120 verbatim
include hdata hK hKsub hφ


-- @@ L122-132 verbatim
/-- The time-derivative term of the momentum integrand is integrable on a
compact subset of the carrier. -/
theorem momentum_timeTerm_integrableOn_of_data :
    IntegrableOn (fun z => ∑ i, u z i * timePartial (fun w => φ w i) z) K volume := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hcomp
  exact (velocity_component_integrableOn_compact_of_data hdata hK hKsub i).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => timePartial (fun w => φ w i) z)
    (contDiff_timePartial hcomp.1).continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)


-- @@ L134-146 verbatim
/-- The nonlinear term of the momentum integrand is integrable on a compact
subset of the carrier. -/
theorem momentum_nonlinearTerm_integrableOn_of_data :
    IntegrableOn
      (fun z => ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z) K volume := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hcomp j
  exact (velocity_pair_integrableOn_compact_of_data hdata hK hKsub i j).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => spatialPartial (fun w => φ w i) j z)
    (spatialPartial_contDiff hcomp.1 j).continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)


-- @@ L148-160 verbatim
/-- The viscous term of the momentum integrand is integrable on a compact
subset of the carrier. -/
theorem momentum_viscousTerm_integrableOn_of_data :
    IntegrableOn
      (fun z => ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z) K volume := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  refine integrable_finsetSum Finset.univ fun j _ => ?_
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hcomp j
  exact (gradient_entry_integrableOn_compact_of_data hdata hK hKsub i j).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => spatialPartial (fun w => φ w i) j z)
    (spatialPartial_contDiff hcomp.1 j).continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)


-- @@ L162-176 verbatim
/-- The pressure term of the momentum integrand is integrable on a compact
subset of the carrier. -/
theorem momentum_pressureTerm_integrableOn_of_data :
    IntegrableOn
      (fun z => p z * ∑ i, spatialPartial (fun w => φ w i) i z) K volume := by
  have hterms : IntegrableOn
      (fun z => ∑ i, p z * spatialPartial (fun w => φ w i) i z) K volume := by
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    have hcomp := component_mem_spaceTimeTestFunction hφ i
    obtain ⟨C, hC⟩ := exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hcomp i
    exact (pressure_integrableOn_compact_of_data hdata hK hKsub).mul_bdd
      (c := C) (g := fun z : ParabolicPoint => spatialPartial (fun w => φ w i) i z)
      (spatialPartial_contDiff hcomp.1 i).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z)
  simpa only [← Finset.mul_sum] using hterms


-- @@ L178-188 verbatim
/-- The force term of the momentum integrand is integrable on a compact subset
of the carrier. -/
theorem momentum_forceTerm_integrableOn_of_data :
    IntegrableOn (fun z => ∑ i, f z i * φ z i) K volume := by
  refine integrable_finsetSum Finset.univ fun i _ => ?_
  have hcomp := component_mem_spaceTimeTestFunction hφ i
  obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hcomp
  exact (force_component_integrableOn_compact_of_data hdata hK hKsub i).mul_bdd
    (c := C) (g := fun z : ParabolicPoint => φ z i)
    hcomp.1.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hC z)


-- @@ L190-190 verbatim
end Terms


-- @@ L192-192 verbatim
/-! ### The momentum integrand -/


-- @@ L194-213 verbatim
/-- The integrand of the weak momentum clause of `def:sws` is integrable on the
closed support of the test field.  Only the data clauses are used. -/
theorem momentum_integrand_integrableOn_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {φ : Vec3 × ℝ → Vec3} (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) Ω I) :
    IntegrableOn (fun z =>
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i) (tsupport φ) volume := by
  have hK : IsCompact (tsupport (show ParabolicPoint → Vec3 from φ)) :=
    isCompact_tsupport_parabolic hφ.2.1
  have hKsub : tsupport (show ParabolicPoint → Vec3 from φ) ⊆ spaceTimeSet Ω I :=
    tsupport_parabolic_subset_spaceTimeSet hφ
  exact ((((momentum_timeTerm_integrableOn_of_data hdata hK hKsub hφ).neg.sub
    (momentum_nonlinearTerm_integrableOn_of_data hdata hK hKsub hφ)).add
    (momentum_viscousTerm_integrableOn_of_data hdata hK hKsub hφ)).sub
    (momentum_pressureTerm_integrableOn_of_data hdata hK hKsub hφ)).sub
    (momentum_forceTerm_integrableOn_of_data hdata hK hKsub hφ)


-- @@ L215-215 verbatim
end CKN
