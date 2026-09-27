/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


-- Import our functional analysis utilities
module

-- Bochner library provides the cylinder σ-algebra MeasurableSpace instance on WeakDual
public import LeanPool.OSforGFF.Minlos.NuclearSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import LeanPool.OSforGFF.General.FunctionalAnalysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial


-- @@ L21-31 verbatim
/-!
# Basic Definitions

Core type definitions for the formalization:

- `SpaceTime` = EuclideanSpace ℝ (Fin 4), the Euclidean 4-space ℝ⁴
- `OSforGFF.TestFunction` / `TestFunctionℂ` = real/complex Schwartz functions on ℝ⁴
- `FieldConfiguration` = tempered distributions S'(ℝ⁴) (WeakDual of Schwartz space)
- `distributionPairing` / `distributionPairingℂReal` = ⟨ω, f⟩ pairings
- `GJGeneratingFunctional` = Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
-/


-- @@ L33-33 verbatim
@[expose] public section


-- @@ L35-39 verbatim
/-- Spacetime dimension. Currently set to 4 (Euclidean ℝ⁴).
    Changing this value requires corresponding changes throughout the project;
    see `docs/dimension_dependence.md` for a detailed inventory.
-/
abbrev STDimension := 4

-- @@ L40-41 verbatim
/-- The `SpaceTime` declaration. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin STDimension)


-- @@ L43-43 verbatim
noncomputable instance : InnerProductSpace ℝ SpaceTime := by infer_instance


-- @@ L45-47 verbatim
/-- The `getTimeComponent` declaration. -/
abbrev getTimeComponent (x : SpaceTime) : ℝ :=
 x ⟨0, by simp +arith⟩


-- @@ L49-49 verbatim
open MeasureTheory NNReal ENNReal Complex

-- @@ L50-52 verbatim
open TopologicalSpace Measure

-- Also open FunLike for SchwartzMap function application

-- @@ L53-53 verbatim
open DFunLike (coe)


-- @@ L55-55 verbatim
noncomputable section


-- @@ L57-57 verbatim
variable {𝕜 : Type} [RCLike 𝕜]


-- @@ L59-62 verbatim
/-- The `μ` declaration. -/
abbrev μ : Measure SpaceTime := volume    -- Lebesgue, just named “μ”

/- Distributions and test functions -/


-- @@ L64-65 verbatim
/-- The `OSforGFF.TestFunction` declaration. -/
abbrev OSforGFF.TestFunction : Type := SchwartzMap SpaceTime ℝ

-- @@ L66-67 verbatim
/-- Test functions over an arbitrary scalar field. -/
abbrev TestFunction𝕜 : Type := SchwartzMap SpaceTime 𝕜

-- @@ L68-69 verbatim
/-- The `TestFunctionℂ` declaration. -/
abbrev TestFunctionℂ := TestFunction𝕜 (𝕜 := ℂ)


-- @@ L71-71 verbatim
example : AddCommGroup TestFunctionℂ := by infer_instance

-- @@ L72-74 verbatim
example : Module ℂ TestFunctionℂ := by infer_instance

/- Space-time and test function setup -/


-- @@ L76-78 verbatim
variable (x : SpaceTime)

/- Probability distribution over field configurations (distributions) -/

-- @@ L79-80 verbatim
/-- Continuous bilinear pointwise multiplication on complex scalars. -/
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ


-- @@ L82-84 verbatim
/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))




-- @@ L88-94 verbatim
/-! ## Glimm-Jaffe Distribution Framework

The proper mathematical foundation for quantum field theory uses
tempered distributions as field configurations, following Glimm and Jaffe.
This section adds the distribution-theoretic definitions alongside
the existing L2 framework for comparison and gradual transition.
-/


-- @@ L96-106 verbatim
/-- Field configurations as tempered distributions (dual to Schwartz space).
    This follows the Glimm-Jaffe approach where the field measure is supported
    on the space of distributions, not L2 functions.

    Using WeakDual gives the correct weak-* topology on the dual space.
-/
abbrev FieldConfiguration := WeakDual ℝ (SchwartzMap SpaceTime ℝ)

-- MeasurableSpace on FieldConfiguration = WeakDual ℝ OSforGFF.TestFunction
-- is the cylinder σ-algebra
-- provided by the bochner library: ⨆ f, (borel ℝ).comap (eval f)


-- @@ L108-114 verbatim
/-- The fundamental pairing between a field configuration (distribution) and a test function.
    This is ⟨ω, f⟩ in the Glimm-Jaffe notation.

    Note: FieldConfiguration = WeakDual ℝ (SchwartzMap SpaceTime ℝ) has the correct
    weak-* topology, making evaluation maps x ↦ ω(x) continuous for each test function x.
-/
def distributionPairing (ω : FieldConfiguration) (f : OSforGFF.TestFunction) : ℝ := ω f


-- @@ L116-117 verbatim
@[simp] lemma distributionPairing_add (ω₁ ω₂ : FieldConfiguration) (a : OSforGFF.TestFunction) :
    distributionPairing (ω₁ + ω₂) a = distributionPairing ω₁ a + distributionPairing ω₂ a := rfl


-- @@ L119-123 verbatim
@[simp] lemma distributionPairing_smul (s : ℝ) (ω : FieldConfiguration)
    (a : OSforGFF.TestFunction) :
    distributionPairing (s • ω) a = s * distributionPairing ω a :=
  -- This follows from the definition of scalar multiplication in WeakDual
  rfl


-- @@ L125-128 verbatim
lemma pairing_smul_real (ω : FieldConfiguration) (s : ℝ) (a : OSforGFF.TestFunction) :
  ω (s • a) = s * (ω a) :=
  -- This follows from the linearity of the dual pairing
  map_smul ω s a


-- @@ L130-141 verbatim
/-- The `distributionPairingCLM` declaration. -/
@[simp] def distributionPairingCLM (a : OSforGFF.TestFunction) : FieldConfiguration →L[ℝ] ℝ where
  toFun ω := distributionPairing ω a
  map_add' ω₁ ω₂ := by
    -- WeakDual addition is pointwise: (ω₁ + ω₂) a = ω₁ a + ω₂ a
    rfl
  map_smul' s ω := by
    -- WeakDual scalar multiplication is pointwise: (s • ω) a = s * (ω a)
    rfl
  cont := by
    -- The evaluation map is continuous by definition of WeakDual topology
    exact WeakDual.eval_continuous a


-- @@ L143-144 verbatim
lemma distributionPairingCLM_apply (a : OSforGFF.TestFunction) (ω : FieldConfiguration) :
    distributionPairingCLM a ω = distributionPairing ω a := rfl


-- @@ L146-146 verbatim
variable [SigmaFinite μ]


-- @@ L148-153 verbatim
/-! ## Glimm-Jaffe Generating Functional

The generating functional in the distribution framework:
Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
where the integral is over field configurations ω (distributions).
-/


-- @@ L155-160 verbatim
/-- The Glimm-Jaffe generating functional: Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
    This is the fundamental object in constructive QFT.
-/
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : OSforGFF.TestFunction) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure


-- @@ L162-190 verbatim
/-- Helper function to create a Schwartz map from a complex test function by applying a
    continuous linear map.
    This factors out the common pattern for extracting real/imaginary parts.
-/
def schwartzCompCLM (f : TestFunctionℂ) (L : ℂ →L[ℝ] ℝ) : OSforGFF.TestFunction :=
  SchwartzMap.mk (fun x => L (f x)) (by
    -- L is a continuous linear map, hence smooth
    exact ContDiff.comp L.contDiff f.smooth'
  ) (by
    -- Polynomial growth: since |L(z)| ≤ ||L|| * |z|, derivatives are controlled
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    use C * ‖L‖
    intro x
    -- iteratedFDeriv of L ∘ f equals L.compContinuousMultilinearMap (iteratedFDeriv f)
    rw [show (fun y => L (f y)) = L ∘ f.toFun from rfl,
      ContinuousLinearMap.iteratedFDeriv_comp_left L f.smooth'.contDiffAt
        (WithTop.coe_le_coe.mpr le_top)]
    -- Use the norm bound: ‖L.compContinuousMultilinearMap m‖ ≤ ‖L‖ * ‖m‖
    calc ‖x‖ ^ k * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x)‖
        ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f.toFun x‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
          · exact pow_nonneg (norm_nonneg _) _
      _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖) := by ring
      _ ≤ ‖L‖ * C := by
          apply mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
      _ = C * ‖L‖ := by ring
  )


-- @@ L192-192 verbatim
omit [SigmaFinite μ]


-- @@ L194-196 verbatim
/-- Evaluate `schwartzCompCLM` pointwise. -/
@[simp] lemma schwartz_comp_clm_apply (f : TestFunctionℂ) (L : ℂ →L[ℝ] ℝ) (x : SpaceTime) :
  (schwartzCompCLM f L) x = L (f x) := rfl


-- @@ L198-203 verbatim
/-- Decompose a complex test function into its real and imaginary parts as real test functions.
    This is more efficient than separate extraction functions.
-/
def complexTestFunctionDecompose (f : TestFunctionℂ) :
    OSforGFF.TestFunction × OSforGFF.TestFunction :=
  (schwartzCompCLM f Complex.reCLM, schwartzCompCLM f Complex.imCLM)


-- @@ L205-209 verbatim
/-- First component of the decomposition evaluates to the real part pointwise. -/
@[simp] lemma complex_testfunction_decompose_fst_apply
  (f : TestFunctionℂ) (x : SpaceTime) :
  (complexTestFunctionDecompose f).1 x = (f x).re := by
  simp [complexTestFunctionDecompose]


-- @@ L211-215 verbatim
/-- Second component of the decomposition evaluates to the imaginary part pointwise. -/
@[simp] lemma complex_testfunction_decompose_snd_apply
  (f : TestFunctionℂ) (x : SpaceTime) :
  (complexTestFunctionDecompose f).2 x = (f x).im := by
  simp [complexTestFunctionDecompose]


-- @@ L217-221 verbatim
/-- Coerced-to-ℂ version (useful for complex-side algebra). -/
lemma complex_testfunction_decompose_fst_apply_coe
  (f : TestFunctionℂ) (x : SpaceTime) :
  ((complexTestFunctionDecompose f).1 x : ℂ) = ((f x).re : ℂ) := by
  simp [complexTestFunctionDecompose]


-- @@ L223-227 verbatim
/-- Coerced-to-ℂ version (useful for complex-side algebra). -/
lemma complex_testfunction_decompose_snd_apply_coe
  (f : TestFunctionℂ) (x : SpaceTime) :
  ((complexTestFunctionDecompose f).2 x : ℂ) = ((f x).im : ℂ) := by
  simp [complexTestFunctionDecompose]


-- @@ L229-235 verbatim
/-- Recomposition at a point via the decomposition. -/
lemma complex_testfunction_decompose_recompose
  (f : TestFunctionℂ) (x : SpaceTime) :
  f x = ((complexTestFunctionDecompose f).1 x : ℂ)
          + Complex.I * ((complexTestFunctionDecompose f).2 x : ℂ) := by
  -- Reduce to the standard identity z = re z + i im z
  simpa [mul_comm] using (Complex.re_add_im (f x)).symm


-- @@ L237-245 verbatim
/-- Complex version of the pairing: real field configuration with complex test function
    We extend the pairing by treating the complex test function as f(x) = f_re(x) + i*f_im(x)
    and defining ⟨ω, f⟩ = ⟨ω, f_re⟩ + i*⟨ω, f_im⟩
-/
def distributionPairingℂReal (ω : FieldConfiguration) (f : TestFunctionℂ) : ℂ :=
  -- Extract real and imaginary parts using our efficient decomposition
  let ⟨f_re, f_im⟩ := complexTestFunctionDecompose f
  -- Pair with the real field configuration and combine
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)


-- @@ L247-250 verbatim
/-- Complex version of the generating functional -/
def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure FieldConfiguration)
  (J : TestFunctionℂ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂReal ω J)) ∂dμ_config.toMeasure


-- @@ L252-255 verbatim
/-- The mean field in the Glimm-Jaffe framework -/
def GJMean (dμ_config : ProbabilityMeasure FieldConfiguration)
  (φ : OSforGFF.TestFunction) : ℝ :=
  ∫ ω, distributionPairing ω φ ∂dμ_config.toMeasure


-- @@ L257-257 verbatim
/-! ## Spatial Geometry and Energy Operators -/


-- @@ L259-260 verbatim
/-- Spatial coordinates: ℝ^{d-1} (space without time) as EuclideanSpace for L2 norm -/
abbrev SpatialCoords := EuclideanSpace ℝ (Fin (STDimension - 1))


-- @@ L262-263 verbatim
/-- L² space on spatial slices (real-valued) -/
abbrev SpatialL2 := Lp ℝ 2 (volume : Measure SpatialCoords)


-- @@ L265-268 verbatim
/-- Extract spatial part of spacetime coordinate -/
def spatialPart (x : SpaceTime) : SpatialCoords :=
  (EuclideanSpace.equiv (Fin (STDimension - 1)) ℝ).symm
    (fun i => x ⟨i.val + 1, by simp [STDimension]; omega⟩)


-- @@ L270-272 verbatim
/-- The energy function `spatialEnergy m k = √(‖k‖² + m²)` on spatial momentum space. -/
def spatialEnergy (m : ℝ) (k : SpatialCoords) : ℝ :=
  Real.sqrt (‖k‖^2 + m^2)


-- @@ L274-274 verbatim
end
