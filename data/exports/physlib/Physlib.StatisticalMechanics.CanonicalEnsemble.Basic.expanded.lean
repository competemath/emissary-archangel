/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Physlib.Thermodynamics.Temperature.Basic

-- @@ L10-101 verbatim
/-!
# Canonical Ensemble: Core Definitions

A *canonical ensemble* describes a system in thermal equilibrium with a heat bath at fixed
temperature `T`. This file gives a measure–theoretic, semi–classical formalization intended to
work uniformly for discrete (counting measure) and continuous (Lebesgue–type) models.

## 1. Semi–Classical Normalization

Classical phase–space integrals produce *dimensionful* quantities. To obtain dimensionless
thermodynamic objects (and an absolute entropy) we introduce:

* `phaseSpaceUnit : ℝ` (physically Planck's constant `h`);
* `dof : ℕ` the number of degrees of freedom.

The *physical* partition function is obtained from the *mathematical* one by dividing by
`phaseSpaceUnit ^ dof`. This yields the standard semi–classical correction preventing
ambiguities such as the Gibbs paradox.

## 2. Mathematical vs Physical Quantities

We keep both layers:

* Mathematical / raw:
  - `mathematicalPartitionFunction (T)` : ∫ exp(-β E) dμ
  - `probability` (density w.r.t. `μ`)
  - `differentialEntropy` (can be negative, unit–dependent)

* Physical / dimensionless:
  - `partitionFunction` : `Z = Z_math / h^dof`
  - `physicalProbability` : dimensionless density
  - `helmholtzFreeEnergy` : `F = -kB T log Z`
  - `thermodynamicEntropy` : absolute entropy `(U - F)/T = -kB ∫ ρ_phys log ρ_phys`

Each physical quantity is expressed explicitly in terms of its mathematical ancestor.

## 3. Core Structure

We assume `phaseSpaceUnit > 0` and `μ` σ–finite. No probability assumption is imposed:
normalization is recovered via the Boltzmann weighted measure.

## 4. Boltzmann & Probability Measures

* `μBolt T` : Boltzmann (unnormalized) measure `withDensity exp(-β E)`
* `μProd T` : normalized probability measure (rescaled `μBolt T`)
* `probability T i` : the density `exp(-β E(i)) / Z_math`
* `physicalProbability` : `probability * (phase_space_unit ^ dof)`

## 5. Energies & Entropies

* `meanEnergy` : expectation of energy under `μProd`.
* `differentialEntropy` : `-kB ∫ log(probability) dμProd`
* `thermodynamicEntropy` : `-kB ∫ log(physicalProbability) dμProd`
  (proved later to coincide with the textbook `(U - F)/T`).

A helper lemma supplies positivity of the partition function under mild assumptions and
non–negativity criteria for the entropy when `probability ≤ 1` (automatic in finite discrete
settings, not in general continuous ones).

## 6. Algebraic Operations

We construct composite ensembles:

* Addition `(𝓒₁ + 𝓒₂)` on product microstates: energies add, measures take product,
  degrees of freedom add, and (physically) the same `phaseSpaceUnit` is reused.
* Multiplicity `nsmul n 𝓒`: `n` distinguishable, non–interacting copies (product of `n` copies).
* Transport along measurable equivalences via `congr`.

These operations respect partition functions, free energies, and (under suitable hypotheses)
mean energies and integrability.

## 7. Notational & Implementation Notes

* We work over an arbitrary measurable type `ι`, allowing both finite and continuous models.
* `β` is accessed through the `Temperature` structure (`T.β`).
* Most positivity / finiteness conditions are hypotheses on lemmas instead of global axioms,
  enabling reuse in formal derivations of fluctuation and response identities.

## 8. References

* L. D. Landau & E. M. Lifshitz, Statistical Physics, Part 1. [ref: landau_statphys1]
* D. Tong, Cambridge Lecture Notes (sections on canonical ensemble).
  - https://www.damtp.cam.ac.uk/user/tong/statphys/one.pdf [ref: tong_statphys_notes_one]
  - https://www.damtp.cam.ac.uk/user/tong/statphys/two.pdf [ref: tong_statphys_notes_two]

## 9. Roadmap

Subsequent files (`Lemmas.lean`) prove:
* Relations among entropies and free energies.
* Fundamental identity `F = U - T S`.
* Derivative (response) formulas: `U = -∂_β log Z`.
-/


-- @@ L103-103 verbatim
@[expose] public section


-- @@ L105-105 verbatim
open MeasureTheory Real Temperature

-- @@ L106-106 verbatim
open scoped Temperature


-- @@ L108-128 verbatim
/-- A Canonical ensemble is described by a type `ι`, corresponding to the type of microstates,
and a map `ι → ℝ` which associates which each microstate an energy
and physical constants needed to define dimensionless thermodynamic quantities. -/
structure CanonicalEnsemble (ι : Type) [MeasurableSpace ι] : Type where
  /-- The energy of associated with a microstate of the canonical ensemble. -/
  energy : ι → ℝ
  /-- The number of degrees of freedom, used to make the partition function dimensionless.
  For a classical system of N particles in 3D, this is `3N`. For a system of N spins,
  this is typically `0` as the state space is already discrete. -/
  dof : ℕ
  /-- The unit of action used to make the phase space volume dimensionless.
  This constant is necessary to define an absolute (rather than relative) thermodynamic
  entropy. In the semi-classical approach, this unit is identified with Planck's constant `h`.
  For discrete systems with a counting measure, this unit should be set to `1`. -/
  phaseSpaceunit : ℝ := 1
  /-- Assumption that the phase space unit is positive. -/
  hPos : 0 < phaseSpaceunit := by positivity
  energy_measurable : Measurable energy
  /-- The measure on the indexing set of microstates. -/
  μ : MeasureTheory.Measure ι := by volume_tac
  [μ_sigmaFinite : SigmaFinite μ]


-- @@ L130-130 verbatim
namespace CanonicalEnsemble

-- @@ L131-131 verbatim
open Real Temperature


-- @@ L133-134 verbatim
variable {ι ι1 : Type} [MeasurableSpace ι]
  [MeasurableSpace ι1] (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)


-- @@ L136-136 verbatim
instance : SigmaFinite 𝓒.μ := 𝓒.μ_sigmaFinite


-- @@ L138-142 verbatim
@[ext]
lemma ext {𝓒 𝓒' : CanonicalEnsemble ι} (h_energy : 𝓒.energy = 𝓒'.energy)
    (h_dof : 𝓒.dof = 𝓒'.dof) (h_h : 𝓒.phaseSpaceunit = 𝓒'.phaseSpaceunit)
    (h_μ : 𝓒.μ = 𝓒'.μ) : 𝓒 = 𝓒' := by
  cases 𝓒; cases 𝓒'; simp_all


-- @@ L144-145 verbatim
@[fun_prop]
lemma energy_measurable' : Measurable 𝓒.energy := 𝓒.energy_measurable


-- @@ L147-159 verbatim
/-- The addition of two `CanonicalEnsemble`. The degrees of freedom are added.
Note: This is only physically meaningful if the two systems share the same `phase_space_unit`. -/
noncomputable instance {ι1 ι2 : Type} [MeasurableSpace ι1] [MeasurableSpace ι2] :
    HAdd (CanonicalEnsemble ι1) (CanonicalEnsemble ι2)
    (CanonicalEnsemble (ι1 × ι2)) where
  hAdd := fun 𝓒1 𝓒2 => {
    energy := fun (i : ι1 × ι2) => 𝓒1.energy i.1 + 𝓒2.energy i.2
    dof := 𝓒1.dof + 𝓒2.dof
    phaseSpaceunit := 𝓒1.phaseSpaceunit
    hPos := 𝓒1.hPos
    μ := 𝓒1.μ.prod 𝓒2.μ
    energy_measurable := by fun_prop
  }


-- @@ L161-166 verbatim
/-- The canonical ensemble with no microstates. -/
def empty : CanonicalEnsemble Empty where
  energy := isEmptyElim
  dof := 0
  μ := 0
  energy_measurable := by fun_prop


-- @@ L168-180 verbatim
/-- Given a measurable equivalence `e : ι1 ≃ᵐ ι`, this is the corresponding canonical ensemble
on `ι1`. The physical properties (`dof`, `phase_space_unit`) are unchanged. -/
noncomputable def congr (e : ι1 ≃ᵐ ι) : CanonicalEnsemble ι1 where
  energy := fun i => 𝓒.energy (e i)
  dof := 𝓒.dof
  phaseSpaceunit := 𝓒.phaseSpaceunit
  hPos := 𝓒.hPos
  μ := 𝓒.μ.map e.symm
  energy_measurable := by
    apply Measurable.comp
    · fun_prop
    · exact MeasurableEquiv.measurable e
  μ_sigmaFinite := MeasurableEquiv.sigmaFinite_map e.symm


-- @@ L182-185 verbatim
@[simp]
lemma congr_energy_comp_symmm (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).energy ∘ e.symm = 𝓒.energy := by
  simp [congr, Function.comp_def]


-- @@ L187-195 verbatim
/-- Scalar multiplication of `CanonicalEnsemble`, defined such that
`nsmul n 𝓒` represents `n` non-interacting, distinguishable copies of the ensemble `𝓒`. -/
noncomputable def nsmul (n : ℕ) (𝓒 : CanonicalEnsemble ι) : CanonicalEnsemble (Fin n → ι) where
  energy := fun f => ∑ i, 𝓒.energy (f i)
  dof := n * 𝓒.dof
  phaseSpaceunit := 𝓒.phaseSpaceunit
  hPos := 𝓒.hPos
  μ := MeasureTheory.Measure.pi fun _ => 𝓒.μ
  energy_measurable := by fun_prop


-- @@ L197-200 verbatim
set_option linter.unusedVariables false in
/-- The microstates of a canonical ensemble. -/
@[nolint unusedArguments]
abbrev microstates (𝓒 : CanonicalEnsemble ι) : Type := ι


-- @@ L202-202 verbatim
/-! ## Properties of physical parameters -/


-- @@ L204-206 verbatim
@[simp]
lemma dof_add (𝓒1 : CanonicalEnsemble ι) (𝓒2 : CanonicalEnsemble ι1) :
    (𝓒1 + 𝓒2).dof = 𝓒1.dof + 𝓒2.dof := rfl


-- @@ L208-210 verbatim
@[simp]
lemma phase_space_unit_add (𝓒1 : CanonicalEnsemble ι) (𝓒2 : CanonicalEnsemble ι1) :
    (𝓒1 + 𝓒2).phaseSpaceunit = 𝓒1.phaseSpaceunit := rfl


-- @@ L212-213 verbatim
@[simp]
lemma dof_nsmul (n : ℕ) : (nsmul n 𝓒).dof = n * 𝓒.dof := rfl


-- @@ L215-217 verbatim
@[simp]
lemma phase_space_unit_nsmul (n : ℕ) :
    (nsmul n 𝓒).phaseSpaceunit = 𝓒.phaseSpaceunit := rfl


-- @@ L219-221 verbatim
@[simp]
lemma dof_congr (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).dof = 𝓒.dof := rfl


-- @@ L223-225 verbatim
@[simp]
lemma phase_space_unit_congr (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).phaseSpaceunit = 𝓒.phaseSpaceunit := rfl


-- @@ L227-227 verbatim
/-! ## The measure -/


-- @@ L229-229 verbatim
lemma μ_add : (𝓒 + 𝓒1).μ = 𝓒.μ.prod 𝓒1.μ := rfl


-- @@ L231-231 verbatim
lemma μ_nsmul (n : ℕ) : (nsmul n 𝓒).μ = MeasureTheory.Measure.pi fun _ => 𝓒.μ := rfl


-- @@ L233-234 verbatim
lemma μ_nsmul_zero_eq : (nsmul 0 𝓒).μ = Measure.pi (fun _ => 0) :=
  congrArg Measure.pi (Subsingleton.elim _ _)


-- @@ L236-240 verbatim
/-!

## The energy of the microstates

-/


-- @@ L242-244 verbatim
@[simp]
lemma energy_add_apply (i : microstates (𝓒 + 𝓒1)) :
    (𝓒 + 𝓒1).energy i = 𝓒.energy i.1 + 𝓒1.energy i.2 := rfl


-- @@ L246-248 verbatim
@[simp]
lemma energy_nsmul_apply (n : ℕ) (f : Fin n → microstates 𝓒) :
    (nsmul n 𝓒).energy f = ∑ i, 𝓒.energy (f i) := rfl


-- @@ L250-252 verbatim
@[simp]
lemma energy_congr_apply (e : ι1 ≃ᵐ ι) (i : ι1) :
    (𝓒.congr e).energy i = 𝓒.energy (e i) := rfl


-- @@ L254-254 verbatim
/-! ## Induction for nsmul -/


-- @@ L256-256 verbatim
open MeasureTheory


-- @@ L258-264 verbatim
lemma nsmul_succ (n : ℕ) [SigmaFinite 𝓒.μ] : nsmul n.succ 𝓒 = (𝓒 + nsmul n 𝓒).congr
    (MeasurableEquiv.piFinSuccAbove (fun _ => ι) 0) := by
  ext1
  · exact funext fun x => Fin.sum_univ_succAbove (fun i => 𝓒.energy (x i)) 0
  · simp [Nat.succ_mul, add_comm]
  · simp
  · exact (((measurePreserving_piFinSuccAbove (fun _ => 𝓒.μ) 0).symm _).map_eq).symm


-- @@ L266-270 verbatim
/-!

## Non zero nature of the measure

-/


-- @@ L272-275 verbatim
instance [NeZero 𝓒.μ] [NeZero 𝓒1.μ] : NeZero (𝓒 + 𝓒1).μ := by
  refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
  rw [μ_add, ← Set.univ_prod_univ, Measure.prod_prod]
  exact NeZero.ne _


-- @@ L277-279 verbatim
instance μ_neZero_congr [NeZero 𝓒.μ] (e : ι1 ≃ᵐ ι) :
    NeZero (𝓒.congr e).μ :=
  ⟨(Measure.map_ne_zero_iff e.symm.measurable.aemeasurable).mpr (NeZero.ne _)⟩


-- @@ L281-284 verbatim
instance [NeZero 𝓒.μ] (n : ℕ) : NeZero (nsmul n 𝓒).μ := by
  refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
  rw [μ_nsmul, Measure.pi_univ]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Measure.measure_univ_ne_zero.mpr (NeZero.ne _)


-- @@ L286-290 verbatim
/-!

## The Boltzmann measure

-/


-- @@ L292-294 verbatim
/-- The Boltzmann measure on the space of microstates. -/
noncomputable def μBolt (T : Temperature) : MeasureTheory.Measure ι :=
  𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- T.β * 𝓒.energy i)))


-- @@ L296-298 verbatim
instance (T : Temperature) : SigmaFinite (𝓒.μBolt T) :=
  inferInstanceAs
    (SigmaFinite (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β T * 𝓒.energy i)))))


-- @@ L300-309 verbatim
@[simp]
lemma μBolt_add (T : Temperature) :
    (𝓒 + 𝓒1).μBolt T = (𝓒.μBolt T).prod (𝓒1.μBolt T) := by
  simp_rw [μBolt, μ_add]
  rw [MeasureTheory.prod_withDensity]
  · congr with i
    rw [← ENNReal.ofReal_mul (exp_nonneg _), ← Real.exp_add]
    simp only [energy_add_apply, mul_add]
  · fun_prop
  · fun_prop


-- @@ L311-319 verbatim
lemma μBolt_congr (e : ι1 ≃ᵐ ι) (T : Temperature) : (𝓒.congr e).μBolt T =
    (𝓒.μBolt T).map e.symm := by
  simp [congr, μBolt]
  refine Measure.ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul₀, lintegral_map, lintegral_map,
    lintegral_withDensity_eq_lintegral_mul₀]
  · congr with i
    simp
  all_goals fun_prop


-- @@ L321-329 verbatim
lemma μBolt_nsmul [SigmaFinite 𝓒.μ] (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).μBolt T = MeasureTheory.Measure.pi fun _ => (𝓒.μBolt T) := by
  induction n with
  | zero =>
    simp [nsmul, μBolt]
    exact congrArg Measure.pi (Subsingleton.elim _ _)
  | succ n ih =>
    rw [nsmul_succ, μBolt_congr, μBolt_add, ih]
    exact ((measurePreserving_piFinSuccAbove (fun _ => 𝓒.μBolt T) 0).symm _).map_eq


-- @@ L331-335 verbatim
lemma μBolt_ne_zero_of_μ_ne_zero (T : Temperature) (h : 𝓒.μ ≠ 0) :
    𝓒.μBolt T ≠ 0 := by
  have hm : AEMeasurable (fun i => ENNReal.ofReal (exp (- T.β * 𝓒.energy i))) 𝓒.μ := by fun_prop
  rw [μBolt, ne_eq, withDensity_eq_zero_iff hm, Filter.EventuallyEq, ae_iff]
  simpa [ENNReal.ofReal_eq_zero, exp_pos] using h


-- @@ L337-340 verbatim
instance (T : Temperature) [NeZero 𝓒.μ] : NeZero (𝓒.μBolt T) := by
  refine { out := ?_ }
  apply μBolt_ne_zero_of_μ_ne_zero
  exact Ne.symm (NeZero.ne' 𝓒.μ)


-- @@ L342-344 verbatim
instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [IsFiniteMeasure (𝓒1.μBolt T)] :
    IsFiniteMeasure ((𝓒 + 𝓒1).μBolt T) := by
  simp only [μBolt_add]; infer_instance


-- @@ L346-348 verbatim
instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] (n : ℕ) :
    IsFiniteMeasure ((nsmul n 𝓒).μBolt T) := by
  simp [μBolt_nsmul]; infer_instance


-- @@ L350-354 verbatim
/-!

## The Mathematical Partition Function

-/


-- @@ L356-359 verbatim
/-- The mathematical partition function, defined as the integral of the Boltzmann factor.
This quantity may have physical dimensions. See `CanonicalEnsemble.partitionFunction` for
the dimensionless physical version. -/
noncomputable def mathematicalPartitionFunction (T : Temperature) : ℝ := (𝓒.μBolt T).real Set.univ


-- @@ L361-367 verbatim
lemma mathematicalPartitionFunction_eq_integral (T : Temperature) :
    mathematicalPartitionFunction 𝓒 T = ∫ i, exp (- T.β * 𝓒.energy i) ∂𝓒.μ := by
  rw [mathematicalPartitionFunction, measureReal_def, μBolt, withDensity_apply _ .univ,
    setLIntegral_univ, ← integral_toReal]
  · simp [ENNReal.toReal_ofReal, exp_nonneg]
  · fun_prop
  · exact .of_forall fun i => ENNReal.ofReal_lt_top


-- @@ L369-373 verbatim
lemma mathematicalPartitionFunction_add {T : Temperature} :
    (𝓒 + 𝓒1).mathematicalPartitionFunction T =
    𝓒.mathematicalPartitionFunction T * 𝓒1.mathematicalPartitionFunction T := by
  simp_rw [mathematicalPartitionFunction, μBolt_add]
  rw [← measureReal_prod_prod, Set.univ_prod_univ]


-- @@ L375-378 verbatim
@[simp]
lemma mathematicalPartitionFunction_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).mathematicalPartitionFunction T = 𝓒.mathematicalPartitionFunction T := by
  simp [mathematicalPartitionFunction, μBolt_congr, measureReal_def, MeasurableEquiv.map_apply]


-- @@ L380-383 verbatim
/-- The `mathematicalPartitionFunction_nsmul` function of `n` copies of a canonical ensemble. -/
lemma mathematicalPartitionFunction_nsmul (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).mathematicalPartitionFunction T = (𝓒.mathematicalPartitionFunction T) ^ n := by
  simp [mathematicalPartitionFunction, μBolt_nsmul, measureReal_def, Measure.pi_univ]


-- @@ L385-386 verbatim
lemma mathematicalPartitionFunction_nonneg (T : Temperature) :
    0 ≤ 𝓒.mathematicalPartitionFunction T := measureReal_nonneg


-- @@ L388-394 verbatim
lemma mathematicalPartitionFunction_eq_zero_iff (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] :
    mathematicalPartitionFunction 𝓒 T = 0 ↔ 𝓒.μ = 0 := by
  rw [mathematicalPartitionFunction, measureReal_def, ENNReal.toReal_eq_zero_iff]
  simp only [measure_ne_top, or_false]
  rw [μBolt, MeasureTheory.withDensity_apply_eq_zero']
  · simp [ENNReal.ofReal_eq_zero, exp_pos]
  · fun_prop


-- @@ L396-396 verbatim
open NNReal


-- @@ L398-401 verbatim
lemma mathematicalPartitionFunction_comp_ofβ_apply (β : ℝ≥0) :
    𝓒.mathematicalPartitionFunction (ofβ β) =
    (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β * 𝓒.energy i)))).real Set.univ := by
  simp only [mathematicalPartitionFunction, μBolt, β_ofβ, neg_mul]


-- @@ L403-408 verbatim
/-- The partition function is strictly positive provided the underlying
measure is non-zero and the Boltzmann measure is finite. -/
lemma mathematicalPartitionFunction_pos (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    0 < 𝓒.mathematicalPartitionFunction T := by
  simp [mathematicalPartitionFunction]


-- @@ L410-410 verbatim
open NNReal Constants


-- @@ L412-412 verbatim
/-! ## The probability density -/


-- @@ L414-420 verbatim
/-- The probability density function of the canonical ensemble.
Note: In the general measure-theoretic case, this is a density with respect to the
underlying measure `𝓒.μ` and is not necessarily less than or equal to 1. In the
case of a finite ensemble with the counting measure, this value corresponds to the
probability of the microstate. -/
noncomputable def probability (T : Temperature) (i : ι) : ℝ :=
  (exp (- T.β * 𝓒.energy i)) / 𝓒.mathematicalPartitionFunction T


-- @@ L422-422 verbatim
/-! ## The probability measure -/


-- @@ L424-426 verbatim
lemma probability_add {T : Temperature} (i : ι × ι1) :
    (𝓒 + 𝓒1).probability T i = 𝓒.probability T i.1 * 𝓒1.probability T i.2 := by
  simp [probability, mathematicalPartitionFunction_add, mul_add, Real.exp_add, div_mul_div_comm]


-- @@ L428-431 verbatim
@[simp]
lemma probability_congr (e : ι1 ≃ᵐ ι) (T : Temperature) (i : ι1) :
    (𝓒.congr e).probability T i = 𝓒.probability T (e i) := by
  simp [probability]


-- @@ L433-441 verbatim
lemma probability_nsmul (n : ℕ) (T : Temperature) (f : Fin n → ι) :
    (nsmul n 𝓒).probability T f = ∏ i, 𝓒.probability T (f i) := by
  induction n with
  | zero => simp [probability, mathematicalPartitionFunction_nsmul]
  | succ n ih =>
    rw [nsmul_succ, probability_congr, probability_add]
    simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero,
      Fin.consEquiv_symm_apply, ih]
    exact (Fin.prod_univ_succAbove (fun i => 𝓒.probability T (f i)) 0).symm


-- @@ L443-446 verbatim
/-- The probability measure associated with the Boltzmann distribution of a
  canonical ensemble. -/
noncomputable def μProd (T : Temperature) : MeasureTheory.Measure ι :=
  (𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T


-- @@ L448-449 verbatim
instance (T : Temperature) : SigmaFinite (𝓒.μProd T) :=
  inferInstanceAs (SigmaFinite ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T))


-- @@ L451-453 verbatim
instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)]
  [NeZero 𝓒.μ] : IsProbabilityMeasure (𝓒.μProd T) := inferInstanceAs <|
  IsProbabilityMeasure ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T)


-- @@ L455-456 verbatim
instance {T} : IsFiniteMeasure (𝓒.μProd T) :=
  inferInstanceAs (IsFiniteMeasure ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T))


-- @@ L458-463 verbatim
lemma μProd_add {T : Temperature} [IsFiniteMeasure (𝓒.μBolt T)]
    [IsFiniteMeasure (𝓒1.μBolt T)] : (𝓒 + 𝓒1).μProd T = (𝓒.μProd T).prod (𝓒1.μProd T) := by
  rw [μProd, μProd, μProd, μBolt_add, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  congr 1
  rw [← ENNReal.mul_inv (.inr (measure_ne_top _ _)) (.inl (measure_ne_top _ _)),
    ← Measure.prod_prod, Set.univ_prod_univ]


-- @@ L465-467 verbatim
lemma μProd_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).μProd T = (𝓒.μProd T).map e.symm := by
  rw [μProd, μProd, μBolt_congr, Measure.map_smul, MeasurableEquiv.map_apply, Set.preimage_univ]


-- @@ L469-477 verbatim
lemma μProd_nsmul (n : ℕ) (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] :
    (nsmul n 𝓒).μProd T = MeasureTheory.Measure.pi fun _ => 𝓒.μProd T := by
  induction n with
  | zero =>
    simp [nsmul, μProd, μBolt]
    exact congrArg Measure.pi (Subsingleton.elim _ _)
  | succ n ih =>
    rw [nsmul_succ, μProd_congr, μProd_add, ih]
    exact ((measurePreserving_piFinSuccAbove (fun _ => 𝓒.μProd T) 0).symm _).map_eq


-- @@ L479-483 verbatim
/-!

## Integrability of energy

-/


-- @@ L485-491 verbatim
@[fun_prop]
lemma integrable_energy_add (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)]
    [IsFiniteMeasure (𝓒1.μBolt T)]
    (h : Integrable 𝓒.energy (𝓒.μProd T)) (h1 : Integrable 𝓒1.energy (𝓒1.μProd T)) :
    Integrable (𝓒 + 𝓒1).energy ((𝓒 + 𝓒1).μProd T) := by
  rw [μProd_add]
  exact (h.comp_fst _).fun_add (h1.comp_snd _)


-- @@ L493-498 verbatim
@[fun_prop]
lemma integrable_energy_congr (T : Temperature) (e : ι1 ≃ᵐ ι)
    (h : Integrable 𝓒.energy (𝓒.μProd T)) :
    Integrable (𝓒.congr e).energy ((𝓒.congr e).μProd T) := by
  rw [μProd_congr]
  exact (integrable_map_equiv e.symm _).mpr (by simpa only [congr_energy_comp_symmm] using h)


-- @@ L500-509 verbatim
@[fun_prop]
lemma integrable_energy_nsmul (n : ℕ) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)]
    (h : Integrable 𝓒.energy (𝓒.μProd T)) :
    Integrable (nsmul n 𝓒).energy ((nsmul n 𝓒).μProd T) := by
  induction n with
  | zero => simp [nsmul]
  | succ n ih =>
    rw [nsmul_succ]
    exact integrable_energy_congr _ _ _ (integrable_energy_add _ _ _ h ih)


-- @@ L511-515 verbatim
/-!

## The mean energy

-/


-- @@ L517-518 verbatim
/-- The mean energy of the canonical ensemble at temperature `T`. -/
noncomputable def meanEnergy (T : Temperature) : ℝ := ∫ i, 𝓒.energy i ∂𝓒.μProd T


-- @@ L520-522 verbatim
/-- The mean square energy ⟨E²⟩ of the canonical ensemble at temperature T. -/
noncomputable def meanSquareEnergy (T : Temperature) : ℝ :=
  ∫ i, (𝓒.energy i)^2 ∂ 𝓒.μProd T


-- @@ L524-526 verbatim
/-- Energy variance at temperature `T`. -/
noncomputable def energyVariance (T : Temperature) : ℝ :=
  ∫ i, (𝓒.energy i - 𝓒.meanEnergy T)^2 ∂ 𝓒.μProd T


-- @@ L528-537 verbatim
lemma meanEnergy_add {T : Temperature}
    [IsFiniteMeasure (𝓒1.μBolt T)] [IsFiniteMeasure (𝓒.μBolt T)]
    [NeZero 𝓒.μ] [NeZero 𝓒1.μ]
    (h1 : Integrable 𝓒.energy (𝓒.μProd T))
    (h2 : Integrable 𝓒1.energy (𝓒1.μProd T)) :
    (𝓒 + 𝓒1).meanEnergy T = 𝓒.meanEnergy T + 𝓒1.meanEnergy T := by
  have hI := integrable_energy_add 𝓒 𝓒1 T h1 h2
  rw [μProd_add] at hI
  rw [meanEnergy, μProd_add, integral_prod _ hI]
  simp [integral_add (integrable_const _) h2, integral_add h1 (integrable_const _), meanEnergy]


-- @@ L539-542 verbatim
lemma meanEnergy_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).meanEnergy T = 𝓒.meanEnergy T := by
  simp only [meanEnergy, μProd_congr]
  exact MeasurePreserving.integral_comp' ⟨e.measurable, e.map_map_symm⟩ 𝓒.energy


-- @@ L544-554 verbatim
lemma meanEnergy_nsmul (n : ℕ) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h1 : Integrable 𝓒.energy (𝓒.μProd T)) :
    (nsmul n 𝓒).meanEnergy T = n * 𝓒.meanEnergy T := by
  induction n with
  | zero => simp [nsmul, meanEnergy]
  | succ n ih =>
    rw [nsmul_succ, meanEnergy_congr,
      meanEnergy_add _ _ h1 (integrable_energy_nsmul 𝓒 n T h1), ih]
    push_cast
    ring


-- @@ L556-560 verbatim
/-!

## The differential entropy

-/


-- @@ L562-566 verbatim
/-- The (differential) entropy of the canonical ensemble. In the continuous case, this quantity
is not absolute but depends on the choice of units for the measure. It can be negative.
See `thermodynamicEntropy` for the absolute physical quantity. -/
noncomputable def differentialEntropy (T : Temperature) : ℝ :=
  - kB * ∫ i, log (probability 𝓒 T i) ∂𝓒.μProd T


-- @@ L568-575 verbatim
/-- Probabilities are non-negative, assuming a positive partition function. -/
-- `unusedArguments` (newly flagged under v4.32.0): the finiteness / non-zero
-- instances are part of the intended interface but not needed by this proof.
@[nolint unusedArguments]
lemma probability_nonneg
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 ≤ 𝓒.probability T i :=
  div_nonneg (exp_nonneg _) (𝓒.mathematicalPartitionFunction_nonneg T)


-- @@ L577-581 verbatim
/-- Probabilities are strictly positive. -/
lemma probability_pos
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 < 𝓒.probability T i :=
  div_pos (exp_pos _) (𝓒.mathematicalPartitionFunction_pos T)


-- @@ L583-595 verbatim
/-- General entropy non-negativity under a pointwise upper bound `probability ≤ 1`.
This assumption holds automatically in the finite/counting case (since sums bound each term),
but can fail in general (continuous) settings; hence we separate it as a hypothesis.
Finite case: see `CanonicalEnsemble.entropy_nonneg` in `Finite`. -/
lemma differentialEntropy_nonneg_of_prob_le_one
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hInt : Integrable (fun i => Real.log (𝓒.probability T i)) (𝓒.μProd T))
    (hP_le_one : ∀ i, 𝓒.probability T i ≤ 1) :
    0 ≤ 𝓒.differentialEntropy T := by
  rw [differentialEntropy]
  refine mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr kB_nonneg) ?_
  simpa using integral_mono_ae hInt (integrable_const 0) (Filter.Eventually.of_forall fun i =>
    Real.log_nonpos (𝓒.probability_nonneg T i) (hP_le_one i))


-- @@ L597-603 verbatim
/-!

## Thermodynamic Quantities

These are the dimensionless physical quantities derived from the mathematical definitions
by incorporating the phase space volume `𝓒.phaseSpaceUnit ^ 𝓒.dof`.
-/


-- @@ L605-605 verbatim
open Constants


-- @@ L607-609 verbatim
/-- The dimensionless thermodynamic partition function, `Z = Z_math / h^dof`. -/
noncomputable def partitionFunction (T : Temperature) : ℝ :=
  𝓒.mathematicalPartitionFunction T / (𝓒.phaseSpaceunit ^ 𝓒.dof)


-- @@ L611-614 verbatim
@[simp]
lemma partitionFunction_def (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    𝓒.partitionFunction T =
      𝓒.mathematicalPartitionFunction T / (𝓒.phaseSpaceunit ^ 𝓒.dof) := rfl


-- @@ L616-620 verbatim
lemma partitionFunction_pos
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    0 < 𝓒.partitionFunction T :=
  div_pos (𝓒.mathematicalPartitionFunction_pos T) (pow_pos 𝓒.hPos _)


-- @@ L622-625 verbatim
lemma partitionFunction_congr
    (𝓒 : CanonicalEnsemble ι) (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).partitionFunction T = 𝓒.partitionFunction T := by
  simp [partitionFunction]


-- @@ L627-633 verbatim
lemma partitionFunction_add
    (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)
    (T : Temperature)
    (h : 𝓒.phaseSpaceunit = 𝓒1.phaseSpaceunit) :
    (𝓒 + 𝓒1).partitionFunction T
      = 𝓒.partitionFunction T * 𝓒1.partitionFunction T := by
  simp [partitionFunction, mathematicalPartitionFunction_add, h, pow_add, div_mul_div_comm]


-- @@ L635-639 verbatim
lemma partitionFunction_nsmul
    (𝓒 : CanonicalEnsemble ι) (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).partitionFunction T
      = (𝓒.partitionFunction T) ^ n := by
  simp [partitionFunction, mathematicalPartitionFunction_nsmul, pow_mul', div_pow]


-- @@ L641-644 verbatim
lemma partitionFunction_dof_zero
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (h : 𝓒.dof = 0) :
    𝓒.partitionFunction T = 𝓒.mathematicalPartitionFunction T := by
  simp [partitionFunction, h]


-- @@ L646-649 verbatim
lemma partitionFunction_phase_space_unit_one
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (h : 𝓒.phaseSpaceunit = 1) :
    𝓒.partitionFunction T = 𝓒.mathematicalPartitionFunction T := by
  simp [partitionFunction, h]


-- @@ L651-658 verbatim
lemma log_partitionFunction
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    Real.log (𝓒.partitionFunction T)
      = Real.log (𝓒.mathematicalPartitionFunction T)
        - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
  rw [partitionFunction, Real.log_div (𝓒.mathematicalPartitionFunction_pos T).ne'
    (pow_pos 𝓒.hPos _).ne', Real.log_pow]


-- @@ L660-668 verbatim
/-- A rewriting form convenient under a coercion to a temperature obtained from an inverse
temperature. -/
lemma log_partitionFunction_ofβ
    (𝓒 : CanonicalEnsemble ι) (β : ℝ≥0)
    [IsFiniteMeasure (𝓒.μBolt (ofβ β))] [NeZero 𝓒.μ] :
    Real.log (𝓒.partitionFunction (ofβ β))
      = Real.log (𝓒.mathematicalPartitionFunction (ofβ β))
        - (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit :=
  log_partitionFunction (𝓒:=𝓒) (T:=ofβ β)


-- @@ L670-675 verbatim
/-- The logarithm of the mathematical partition function as an integral. -/
lemma log_mathematicalPartitionFunction_eq
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    Real.log (𝓒.mathematicalPartitionFunction T)
      = Real.log (∫ i, Real.exp (- T.β * 𝓒.energy i) ∂ 𝓒.μ) := by
  simp [mathematicalPartitionFunction_eq_integral]


-- @@ L677-680 verbatim
/-- The Helmholtz free energy, `F = -k_B T log(Z)`. This is the central
quantity from which other thermodynamic properties are derived. -/
noncomputable def helmholtzFreeEnergy (T : Temperature) : ℝ :=
  - kB * T.val * Real.log (𝓒.partitionFunction T)


-- @@ L682-685 verbatim
@[simp]
lemma helmholtzFreeEnergy_def
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) :
    𝓒.helmholtzFreeEnergy T = - kB * T.val * Real.log (𝓒.partitionFunction T) := rfl


-- @@ L687-690 verbatim
lemma helmholtzFreeEnergy_congr
    (𝓒 : CanonicalEnsemble ι) (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).helmholtzFreeEnergy T = 𝓒.helmholtzFreeEnergy T := by
  simp [helmholtzFreeEnergy]


-- @@ L692-696 verbatim
lemma helmholtzFreeEnergy_dof_zero
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (h : 𝓒.dof = 0) :
    𝓒.helmholtzFreeEnergy T
      = -kB * T.val * Real.log (𝓒.mathematicalPartitionFunction T) := by
  simp [helmholtzFreeEnergy, partitionFunction, h]


-- @@ L698-702 verbatim
lemma helmholtzFreeEnergy_phase_space_unit_one
    (𝓒 : CanonicalEnsemble ι) (T : Temperature) (h : 𝓒.phaseSpaceunit = 1) :
    𝓒.helmholtzFreeEnergy T
      = -kB * T.val * Real.log (𝓒.mathematicalPartitionFunction T) := by
  simp [helmholtzFreeEnergy, partitionFunction, h]


-- @@ L704-714 verbatim
lemma helmholtzFreeEnergy_add
    (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [IsFiniteMeasure (𝓒1.μBolt T)]
    [NeZero 𝓒.μ] [NeZero 𝓒1.μ]
    (h : 𝓒.phaseSpaceunit = 𝓒1.phaseSpaceunit) :
    (𝓒 + 𝓒1).helmholtzFreeEnergy T
      = 𝓒.helmholtzFreeEnergy T + 𝓒1.helmholtzFreeEnergy T := by
  simp only [helmholtzFreeEnergy]
  rw [partitionFunction_add _ _ _ h,
    Real.log_mul (partitionFunction_pos 𝓒 T).ne' (partitionFunction_pos 𝓒1 T).ne']
  ring


-- @@ L716-721 verbatim
lemma helmholtzFreeEnergy_nsmul
    (𝓒 : CanonicalEnsemble ι) (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).helmholtzFreeEnergy T
      = n * 𝓒.helmholtzFreeEnergy T := by
  simp only [helmholtzFreeEnergy, partitionFunction_nsmul, Real.log_pow]
  ring


-- @@ L723-727 verbatim
/-- The dimensionless physical probability density. This is is the probability density w.r.t. the
measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the
probability density `ρ_phys = ρ_math * h^dof` dimensionless. -/
noncomputable def physicalProbability (T : Temperature) (i : ι) : ℝ :=
  𝓒.probability T i * (𝓒.phaseSpaceunit ^ 𝓒.dof)


-- @@ L729-732 verbatim
@[simp]
lemma physicalProbability_def (T : Temperature) (i : ι) :
    𝓒.physicalProbability T i
      = 𝓒.probability T i * (𝓒.phaseSpaceunit ^ 𝓒.dof) := rfl


-- @@ L734-737 verbatim
lemma physicalProbability_measurable (T : Temperature) :
    Measurable (𝓒.physicalProbability T) := by
  unfold physicalProbability probability
  fun_prop


-- @@ L739-742 verbatim
lemma physicalProbability_nonneg
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 ≤ 𝓒.physicalProbability T i :=
  mul_nonneg (𝓒.probability_nonneg T i) (pow_nonneg 𝓒.hPos.le _)


-- @@ L744-747 verbatim
lemma physicalProbability_pos
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 < 𝓒.physicalProbability T i :=
  mul_pos (𝓒.probability_pos T i) (pow_pos 𝓒.hPos _)


-- @@ L749-754 verbatim
lemma log_physicalProbability
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    Real.log (𝓒.physicalProbability T i)
      = Real.log (𝓒.probability T i) + (𝓒.dof : ℝ) * Real.log 𝓒.phaseSpaceunit := by
  rw [physicalProbability, Real.log_mul (𝓒.probability_pos T i).ne' (pow_pos 𝓒.hPos _).ne',
    Real.log_pow]


-- @@ L756-762 verbatim
lemma integral_probability
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    (∫ i, 𝓒.probability T i ∂ 𝓒.μ) = 1 := by
  simp only [probability, div_eq_mul_inv, integral_mul_const,
    ← mathematicalPartitionFunction_eq_integral]
  exact mul_inv_cancel₀ (𝓒.mathematicalPartitionFunction_pos T).ne'


-- @@ L764-770 verbatim
/-- Normalization of the dimensionless physical probability density over the base measure. -/
lemma integral_physicalProbability_base
    (𝓒 : CanonicalEnsemble ι) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    (∫ i, 𝓒.physicalProbability T i ∂ 𝓒.μ)
      = 𝓒.phaseSpaceunit ^ 𝓒.dof := by
  simp [physicalProbability, integral_mul_const, integral_probability]


-- @@ L772-775 verbatim
lemma physicalProbability_dof_zero
    (T : Temperature) (h : 𝓒.dof = 0) (i : ι) :
    𝓒.physicalProbability T i = 𝓒.probability T i := by
  simp [physicalProbability, h]


-- @@ L777-780 verbatim
lemma physicalProbability_phase_space_unit_one
    (T : Temperature) (h : 𝓒.phaseSpaceunit = 1) (i : ι) :
    𝓒.physicalProbability T i = 𝓒.probability T i := by
  simp [physicalProbability, h]


-- @@ L782-785 verbatim
lemma physicalProbability_congr (e : ι1 ≃ᵐ ι) (T : Temperature) (i : ι1) :
    (𝓒.congr e).physicalProbability T i
      = 𝓒.physicalProbability T (e i) := by
  simp [physicalProbability, probability]


-- @@ L787-794 verbatim
lemma physicalProbability_add
    {ι1} [MeasurableSpace ι1]
    (𝓒1 : CanonicalEnsemble ι1) (T : Temperature) (i : ι × ι1)
    (h : 𝓒.phaseSpaceunit = 𝓒1.phaseSpaceunit) :
    (𝓒 + 𝓒1).physicalProbability T i
      = 𝓒.physicalProbability T i.1 * 𝓒1.physicalProbability T i.2 := by
  simp [physicalProbability, probability_add, phase_space_unit_add, dof_add, h, pow_add,
    mul_mul_mul_comm]


-- @@ L796-800 verbatim
/-- The absolute thermodynamic entropy, defined from its statistical mechanical foundation as
the Gibbs-Shannon entropy of the dimensionless physical probability distribution.
This corresponds to Landau & Lifshitz, Statistical Physics, §7, Eq. 7.12. -/
noncomputable def thermodynamicEntropy (T : Temperature) : ℝ :=
  -kB * ∫ i, Real.log (𝓒.physicalProbability T i) ∂(𝓒.μProd T)


-- @@ L802-804 verbatim
@[simp]
lemma thermodynamicEntropy_def (T : Temperature) :
    𝓒.thermodynamicEntropy T = -kB * ∫ i, Real.log (𝓒.physicalProbability T i) ∂ 𝓒.μProd T := rfl


-- @@ L806-806 verbatim
end CanonicalEnsemble
