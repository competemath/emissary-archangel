/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.ComparatorSobolevEvolution
public import LeanPool.NavierStokesAndEuler.Euler.EulerC1Breakdown
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryMaximalVorticityIntegral
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.EulerC1Limsup
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerBKM
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerKineticEnergy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryL2Integration
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVorticity


-- @@ L18-19 verbatim
/-! The canonical maximal solution in the reference's ordinary-function
Sobolev class. All regularity is inherited from its existing shorter evolutions. -/


-- @@ L21-21 verbatim
section


-- @@ L23-24 verbatim
/-! The canonical maximal fields in the challenge's position-first, real-time
convention. Extension by zero outside the lifespan has no role in the equation. -/


-- @@ L26-26 verbatim
section


-- @@ L28-29 verbatim
/-! The extended spatial suprema in the independent challenge agree with the
ordinary development's bounded-function norms on every smooth Sobolev slice. -/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-37 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSobolevBoundedField
  EulerMeanBoundary EulerMeanCutoffCurl

-- @@ L38-38 verbatim
open scoped ENNReal Topology ContDiff BoundedContinuousFunction


-- @@ L40-40 verbatim
namespace Euler.ComparatorBridge


-- @@ L42-45 verbatim
theorem vorticity_eq_vectorCurl (u : Space → Space) (hu : ContDiff ℝ ∞ u) :
    Euler.vorticity u = vectorCurl u := by
  funext x
  exact (vectorCurl_eq_matrix u x (hu.differentiable (by simp) x)).symm


-- @@ L47-51 verbatim
theorem iSup_ofReal_norm_boundedContinuousFunction
    {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    (f : X →ᵇ V) :
    (⨆ x, ENNReal.ofReal ‖f x‖) = ENNReal.ofReal ‖f‖ := by
  simpa only [ofReal_norm] using f.enorm_eq_iSup_enorm.symm


-- @@ L53-62 verbatim
theorem velocityC1Norm_eq (A : SmoothL2Field Space) :
    Euler.velocityC1Norm A.field =
      ENNReal.ofReal (‖finiteField A‖ + ‖finiteField A.derivative‖) := by
  unfold Euler.velocityC1Norm
  rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  congr 1
  · simpa only [finiteField_apply] using
      iSup_ofReal_norm_boundedContinuousFunction (finiteField A)
  · simpa only [finiteField_apply, SmoothL2Field.derivative] using
      iSup_ofReal_norm_boundedContinuousFunction (finiteField A.derivative)


-- @@ L64-70 verbatim
theorem vorticityNorm_eq (A : SmoothL2Field Space) :
    Euler.vorticityNorm A.field = ENNReal.ofReal (EulerOrdinarySobolev.vorticityNorm A) := by
  unfold Euler.vorticityNorm EulerOrdinarySobolev.vorticityNorm
  rw [vorticity_eq_vectorCurl A.field A.smooth]
  simpa only [finiteField_apply, EulerOrdinarySobolev.vorticityField_apply] using
    iSup_ofReal_norm_boundedContinuousFunction
      (finiteField (EulerOrdinarySobolev.vorticityField A))


-- @@ L72-72 verbatim
end Euler.ComparatorBridge


-- @@ L74-74 verbatim
end

-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
end


-- @@ L79-79 verbatim
@[expose] public section


-- @@ L81-81 verbatim
noncomputable section


-- @@ L83-84 verbatim
open Set Filter MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerMeanSobolevBoundedField

-- @@ L85-85 verbatim
open scoped ENNReal Topology ContDiff


-- @@ L87-87 verbatim
namespace Euler.ComparatorBridge


-- @@ L89-89 verbatim
variable {A : SmoothL2Field Space} (L : FiniteLifespan A)


-- @@ L91-93 verbatim
/-- Maximal velocity extension, with branches according to `ht : t ∈ Ico (0 : ℝ) L.duration`. -/
def maximalVelocityExtension (x : Space) (t : ℝ) : Space :=
  if ht : t ∈ Ico (0 : ℝ) L.duration then L.maximalVelocity ⟨t, ht⟩ x else 0


-- @@ L95-97 verbatim
/-- Maximal pressure extension, with branches according to `ht : t ∈ Ico (0 : ℝ) L.duration`. -/
def maximalPressureExtension (x : Space) (t : ℝ) : ℝ :=
  if ht : t ∈ Ico (0 : ℝ) L.duration then L.maximalPressure ⟨t, ht⟩ x else 0


-- @@ L99-102 verbatim
theorem maximalVelocityExtension_eq (t : L.Time) :
    (maximalVelocityExtension L · (t : ℝ)) = L.maximalVelocity t := by
  funext x
  simp only [maximalVelocityExtension, dite_eq_left t.property]


-- @@ L104-107 verbatim
theorem maximalPressureExtension_eq (t : L.Time) :
    (maximalPressureExtension L · (t : ℝ)) = L.maximalPressure t := by
  funext x
  simp only [maximalPressureExtension, dite_eq_left t.property]


-- @@ L109-110 verbatim
theorem maximalVelocityExtension_initial : (maximalVelocityExtension L · 0) = A.field :=
  (maximalVelocityExtension_eq L L.initialTime).trans L.maximalVelocity_initial


-- @@ L112-115 verbatim
theorem maximalVelocityExtension_memLp (t : ℝ) (ht : t ∈ Ico 0 L.duration) :
    MemLp (maximalVelocityExtension L · t) 2 volume := by
  rw [maximalVelocityExtension_eq L ⟨t, ht⟩]
  exact (L.maximalField ⟨t, ht⟩).memLp


-- @@ L117-120 verbatim
theorem maximalVelocityExtension_divergence (t : ℝ) (ht : t ∈ Ico 0 L.duration)
    (x : Space) : Euler.divergence (maximalVelocityExtension L · t) x = 0 := by
  rw [maximalVelocityExtension_eq L ⟨t, ht⟩]
  exact L.maximalVelocity_divergence ⟨t, ht⟩ x


-- @@ L122-126 verbatim
theorem velocityC1Norm_maximal (t : L.Time) :
    Euler.velocityC1Norm (maximalVelocityExtension L · (t : ℝ)) =
      ENNReal.ofReal (L.maximalC1Norm t) := by
  rw [maximalVelocityExtension_eq]
  exact velocityC1Norm_eq (L.maximalField t)


-- @@ L128-132 verbatim
theorem vorticityNorm_maximal (t : L.Time) :
    Euler.vorticityNorm (maximalVelocityExtension L · (t : ℝ)) =
      ENNReal.ofReal (L.maximalVorticityNorm t) := by
  rw [maximalVelocityExtension_eq]
  exact vorticityNorm_eq (L.maximalField t)


-- @@ L134-138 verbatim
theorem vorticityNorm_maximal_density (t : ℝ) (ht : t ∈ Ico 0 L.duration) :
    Euler.vorticityNorm (maximalVelocityExtension L · t) =
      ENNReal.ofReal (L.maximalVorticityDensity t) := by
  exact (vorticityNorm_maximal L ⟨t, ht⟩).trans
    (congrArg ENNReal.ofReal (L.maximalVorticityDensity_eq ⟨t, ht⟩)).symm


-- @@ L140-144 verbatim
theorem maximalField_kineticEnergy (t : L.Time) :
    ‖(L.maximalField t).toLp‖ ^ 2 = ‖A.toLp‖ ^ 2 := by
  change ‖((L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).velocity (L.intermediateTime t)).toLp‖ ^ 2 = _
  rw [Evolution.kineticEnergy_conserved, L.evolution_initial]


-- @@ L146-156 verbatim
theorem maximalVelocityExtension_energy (t : ℝ) (ht : t ∈ Ico 0 L.duration) :
    (∫ x, ‖maximalVelocityExtension L x t‖ ^ 2) = ‖A.toLp‖ ^ 2 := by
  have he := field_inner (L.maximalField ⟨t, ht⟩) (L.maximalField ⟨t, ht⟩)
  have hf : (∫ x, ‖(L.maximalField ⟨t, ht⟩).field x‖ ^ 2) =
      ‖(L.maximalField ⟨t, ht⟩).toLp‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using he.symm
  have hx := congrFun (maximalVelocityExtension_eq L ⟨t, ht⟩)
  calc
    _ = ∫ x, ‖(L.maximalField ⟨t, ht⟩).field x‖ ^ 2 :=
      integral_congr_ae (Eventually.of_forall (fun x => congrArg (fun a : Space => ‖a‖ ^ 2) (hx x)))
    _ = ‖A.toLp‖ ^ 2 := hf.trans (maximalField_kineticEnergy L ⟨t, ht⟩)


-- @@ L158-164 verbatim
theorem maximalVelocityExtension_bounded_energy :
    ∃ E : ℝ, ∀ t ∈ Ico (0 : ℝ) L.duration,
      (∫ x, ‖maximalVelocityExtension L x t‖ ^ 2) < E := by
  refine ⟨‖A.toLp‖ ^ 2 + 1, ?_⟩
  intro t ht
  rw [maximalVelocityExtension_energy L t ht]
  exact lt_add_one _


-- @@ L166-177 verbatim
theorem maximalVelocityExtension_c1_locally_bounded
    (S : ℝ) (_hS : 0 < S) (hSL : S < L.duration) :
    (⨆ t ∈ Icc (0 : ℝ) S, Euler.velocityC1Norm (maximalVelocityExtension L · t)) < ⊤ := by
  have hc : Continuous (fun t : Icc (0 : ℝ) S =>
      L.maximalC1Norm (L.shorterTime S hSL t)) :=
    L.maximalC1Norm_continuous.comp
      (continuous_subtype_val.subtype_mk (fun t => ⟨t.property.1, t.property.2.trans_lt hSL⟩))
  obtain ⟨M, hM⟩ := (isCompact_range hc).bddAbove
  apply lt_of_le_of_lt (b := ENNReal.ofReal M) _ ENNReal.ofReal_lt_top
  refine iSup_le (fun t => iSup_le (fun ht => ?_))
  exact (velocityC1Norm_maximal L (L.shorterTime S hSL ⟨t, ht⟩)).le.trans
    (ENNReal.ofReal_le_ofReal (hM ⟨⟨t, ht⟩, rfl⟩))


-- @@ L179-191 verbatim
theorem maximalVelocityExtension_vorticity_locally_integrable
    (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) :
    (∫⁻ t in Ico (0 : ℝ) S, Euler.vorticityNorm (maximalVelocityExtension L · t)) < ⊤ := by
  have he : (∫⁻ t in Ico (0 : ℝ) S, Euler.vorticityNorm (maximalVelocityExtension L · t)) =
      ∫⁻ t in Ico (0 : ℝ) S, ENNReal.ofReal (L.maximalVorticityDensity t) := by
    apply setLIntegral_congr_fun measurableSet_Ico
    intro t ht
    exact vorticityNorm_maximal_density L t ⟨ht.1, ht.2.trans hSL⟩
  rw [he, ← ofReal_integral_eq_lintegral_ofReal
    ((L.maximalVorticityDensity_continuousOn S hS hSL).integrableOn_Icc.mono_set
      Ico_subset_Icc_self)
    (Eventually.of_forall L.maximalVorticityDensity_nonneg)]
  exact ENNReal.ofReal_lt_top


-- @@ L193-197 verbatim
theorem maximalVelocityExtension_c1_limsup :
    Filter.limsup (fun t : ℝ => Euler.velocityC1Norm (maximalVelocityExtension L · t))
      (𝓝[<] L.duration) = ⊤ := by
  rw [← L.map_time_atTop, ← Filter.limsup_comp]
  simpa only [Function.comp_def, velocityC1Norm_maximal] using L.maximalC1Norm_limsup_atTop


-- @@ L199-202 verbatim
theorem maximalVelocityExtension_vorticity_integral :
    (∫⁻ t in Ico (0 : ℝ) L.duration, Euler.vorticityNorm (maximalVelocityExtension L · t)) = ⊤ := by
  rw [setLIntegral_congr_fun measurableSet_Ico (vorticityNorm_maximal_density L)]
  exact L.vorticity_lintegral_eq_top


-- @@ L204-204 verbatim
end Euler.ComparatorBridge


-- @@ L206-206 verbatim
end

-- @@ L207-207 verbatim
end


-- @@ L209-209 verbatim
end


-- @@ L211-211 verbatim
@[expose] public section


-- @@ L213-213 verbatim
noncomputable section


-- @@ L215-216 verbatim
open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev

-- @@ L217-217 verbatim
open scoped Topology ContDiff


-- @@ L219-219 verbatim
namespace Euler.ComparatorBridge


-- @@ L221-221 verbatim
variable {A : SmoothL2Field Space} (L : FiniteLifespan A)


-- @@ L223-225 verbatim
/-- Maximal derivative field, given by `eulerRhs (L.maximalField t) (L.maximalPressureField t)`. -/
def maximalDerivativeField (t : L.Time) : SmoothL2Field Space :=
  eulerRhs (L.maximalField t) (L.maximalPressureField t)


-- @@ L227-232 verbatim
theorem maximalDerivativeField_eq_evolution (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) (t : Icc (0 : ℝ) S) :
    maximalDerivativeField L (L.shorterTime S hSL t) =
      (L.evolution S hS hSL).derivative t := by
  rw [maximalDerivativeField, L.maximalField_eq_evolution S hS hSL,
    L.maximalPressureField_eq_evolution S hS hSL, Evolution.derivative_eq_eulerRhs]


-- @@ L234-239 verbatim
theorem maximalDerivativeField_jet_continuous (n : ℕ) :
    Continuous (fun t : L.Time => (maximalDerivativeField L t).jetLp n) := by
  apply L.continuous_of_shorter_restrictions
  intro S hS hSL
  simp only [maximalDerivativeField_eq_evolution L S hS hSL]
  exact (L.evolution S hS hSL).derivative_continuous n


-- @@ L241-243 verbatim
/-- Maximal derivative extension, with branches according to `ht : t ∈ Ico (0 : ℝ) L.duration`. -/
def maximalDerivativeExtension (x : Space) (t : ℝ) : Space :=
  if ht : t ∈ Ico (0 : ℝ) L.duration then (maximalDerivativeField L ⟨t, ht⟩).field x else 0


-- @@ L245-248 verbatim
theorem maximalDerivativeExtension_eq (t : L.Time) :
    (maximalDerivativeExtension L · (t : ℝ)) = (maximalDerivativeField L t).field := by
  funext x
  simp only [maximalDerivativeExtension, dite_eq_left t.property]


-- @@ L250-254 verbatim
theorem maximalVelocityExtension_eq_evolution (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) (t : Icc (0 : ℝ) S) :
    (maximalVelocityExtension L · (t : ℝ)) = ((L.evolution S hS hSL).velocity t).field :=
  (maximalVelocityExtension_eq L (L.shorterTime S hSL t)).trans
    (L.maximalVelocity_eq_evolution S hS hSL t)


-- @@ L256-259 verbatim
theorem maximalVelocityExtension_sobolevSmooth :
    Euler.SobolevSmoothOn (Ico 0 L.duration) (maximalVelocityExtension L) :=
  sobolevSmoothOn_of_path L.maximalField L.maximalField_jet_continuous _
    (maximalVelocityExtension_eq L)


-- @@ L261-264 verbatim
theorem maximalDerivativeExtension_sobolevSmooth :
    Euler.SobolevSmoothOn (Ico 0 L.duration) (maximalDerivativeExtension L) :=
  sobolevSmoothOn_of_path (maximalDerivativeField L)
    (maximalDerivativeField_jet_continuous L) _ (maximalDerivativeExtension_eq L)


-- @@ L266-288 verbatim
theorem maximalVelocityExtension_hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 L.duration) :
    HasDerivAt (fun s => Euler.toL2 (maximalVelocityExtension L · s))
      (Euler.toL2 (maximalDerivativeExtension L · t)) t := by
  let s : L.Time := ⟨t, ht.1.le, ht.2⟩
  let S := L.intermediateHorizon s
  have hS : 0 < S := L.intermediateHorizon_pos s
  have hSL : S < L.duration := L.intermediateHorizon_lt s
  have htS : t < S := L.time_lt_intermediateHorizon s
  let r : Icc (0 : ℝ) S := ⟨t, ht.1.le, htS.le⟩
  have hd := ((L.evolution S hS hSL).velocityPath_hasDerivWithinAt r).hasDerivAt
    (Icc_mem_nhds ht.1 htS)
  rw [Evolution.velocityPath_extend] at hd
  have he : Euler.toL2 (maximalDerivativeExtension L · t) =
      ((L.evolution S hS hSL).derivative r).toLp := by
    change Euler.toL2 (maximalDerivativeExtension L ·
      (L.shorterTime S hSL r : ℝ)) = _
    rw [maximalDerivativeExtension_eq L (L.shorterTime S hSL r), toL2_field,
      maximalDerivativeField_eq_evolution L S hS hSL]
  rw [he]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 htS] with u hu
  rw [maximalVelocityExtension_eq_evolution L S hS hSL ⟨u, hu.1.le, hu.2.le⟩,
    toL2_field, projIcc_of_mem hS.le ⟨hu.1.le, hu.2.le⟩]


-- @@ L290-313 verbatim
theorem maximal_sobolevSolution :
    EulerSobolevExistenceAndSmoothnessR3On (Ico 0 L.duration) A.field
      (maximalVelocityExtension L) (maximalPressureExtension L) := by
  refine ⟨fun x t ht => maximalVelocityExtension_divergence L t ht x,
    fun x => congrFun (maximalVelocityExtension_initial L) x,
    maximalVelocityExtension_sobolevSmooth L, ?_, maximalDerivativeExtension L,
    maximalDerivativeExtension_sobolevSmooth L, ?_, ?_⟩
  · intro t ht
    have hi : t ∈ Ico 0 L.duration := interior_subset ht
    rw [maximalPressureExtension_eq L ⟨t, hi⟩]
    exact (L.maximalPressure_spec ⟨t, hi⟩).1.differentiable (by simp)
  · intro t ht
    exact maximalVelocityExtension_hasDerivAt L t (by simpa only [interior_Ico] using ht)
  · intro x t ht
    have hi : t ∈ Ico 0 L.duration := interior_subset ht
    have hd := congrFun (maximalDerivativeExtension_eq L ⟨t, hi⟩) x
    have hv := congrFun (maximalVelocityExtension_eq L ⟨t, hi⟩) x
    rw [hd, hv, maximalVelocityExtension_eq L ⟨t, hi⟩,
      maximalPressureExtension_eq L ⟨t, hi⟩, maximalDerivativeField, eulerRhs_field,
      (L.maximalPressure_spec ⟨t, hi⟩).2.2 x]
    change (-fderiv ℝ (L.maximalField ⟨t, hi⟩).field x
      ((L.maximalField ⟨t, hi⟩).field x) - (L.maximalPressureField ⟨t, hi⟩).field x) +
      fderiv ℝ (L.maximalField ⟨t, hi⟩).field x ((L.maximalField ⟨t, hi⟩).field x) = _
    abel


-- @@ L315-319 verbatim
theorem maximal_sobolev_existence_iff (T : ℝ) (hT : 0 < T) :
    (∃ v p, EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) A.field v p) ↔
      T < L.duration := by
  rw [exists_sobolevSolution_iff A T hT, L.hasScalarEulerEvolution_iff]
  exact and_iff_right hT


-- @@ L321-321 verbatim
end Euler.ComparatorBridge
