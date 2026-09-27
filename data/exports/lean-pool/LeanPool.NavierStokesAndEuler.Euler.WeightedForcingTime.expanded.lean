/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.FiniteMetricEnergy
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import Mathlib.MeasureTheory.Function.L2Space


-- @@ L13-13 verbatim
/-! Actual finite weighted forcing norms in the Bochner time space. -/


-- @@ L15-15 verbatim
section


-- @@ L17-17 verbatim
/-! Actual L²-time convergence of finite Hilbert forcing norms. -/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerFamilyNormTime


-- @@ L25-25 verbatim
open MeasureTheory InnerProductSpace EulerTimeLp EulerFiniteMetricEnergy

-- @@ L26-26 verbatim
open scoped Topology


-- @@ L28-28 verbatim
variable {I H : Type*} [Fintype I] [NormedAddCommGroup H] [NormedSpace ℝ H]


-- @@ L30-32 verbatim
/-- The ordinary finite family as its genuine Hilbert-sum norm model. -/
def familyHilbertMap : (I → H) →L[ℝ] PiLp 2 (fun _ : I => H) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => H)).symm.toContinuousLinearMap


-- @@ L34-37 verbatim
/-- The actual root of the sum of squares equals the genuine finite L²-product norm. -/
theorem familyNorm_eq_piLp (u : I → H) : familyNorm u = ‖familyHilbertMap u‖ := by
  rw [PiLp.norm_eq_of_L2]
  rfl


-- @@ L39-45 verbatim
/-- The finite forcing norm is Lipschitz, with a fixed base-cardinality constant. -/
theorem familyNorm_lipschitz : LipschitzWith ‖(familyHilbertMap : (I → H) →L[ℝ] PiLp 2 (fun _ : I
    => H))‖₊
    (familyNorm : (I → H) → ℝ) := by
  have h := lipschitzWith_one_norm.comp (familyHilbertMap : (I → H) →L[ℝ] PiLp 2 (fun _ : I =>
      H)).lipschitzWith
  simpa only [one_mul, Function.comp_def, ← familyNorm_eq_piLp] using h


-- @@ L47-49 verbatim
/-- The actual scalar finite-family norm represented in Bochner L² time. -/
def familyNormTime (T : ℝ) (u : TimeLp T (I → H)) : TimeLp T ℝ :=
  familyNorm_lipschitz.compLp (by simp [familyNorm, familySquaredNorm]) u


-- @@ L51-54 verbatim
/-- This scalar Bochner element is the literal family forcing norm almost everywhere. -/
theorem familyNormTime_ae (T : ℝ) (u : TimeLp T (I → H)) :
    (familyNormTime T u : ℝ → ℝ) =ᵐ[timeMeasure T] fun t => familyNorm (u t) :=
  familyNorm_lipschitz.coeFn_compLp (by simp [familyNorm, familySquaredNorm]) u


-- @@ L56-61 verbatim
/-- Strong L²-time forcing convergence gives strong convergence of its actual finite-family norm. -/
theorem familyNormTime_tendsto (T : ℝ) (u : ℕ → TimeLp T (I → H)) (v : TimeLp T (I → H))
    (hu : Filter.Tendsto u Filter.atTop (𝓝 v)) :
    Filter.Tendsto (fun n => familyNormTime T (u n)) Filter.atTop (𝓝 (familyNormTime T v)) :=
  (familyNorm_lipschitz.continuous_compLp (by
      simp [familyNorm, familySquaredNorm])).continuousAt.tendsto.comp hu


-- @@ L63-79 verbatim
/-- Weighted time integrals of actual family forcing norms pass through strong L² approximations. -/
theorem integral_familyNorm_tendsto (T : ℝ) (a : TimeLp T ℝ)
    (u : ℕ → TimeLp T (I → H)) (v : TimeLp T (I → H))
    (hu : Filter.Tendsto u Filter.atTop (𝓝 v)) :
    Filter.Tendsto (fun n => ∫ t, a t * familyNorm (u n t) ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ t, a t * familyNorm (v t) ∂timeMeasure T)) := by
  have he (f : TimeLp T (I → H)) : ⟪a, familyNormTime T f⟫_ℝ =
      ∫ t, a t * familyNorm (f t) ∂timeMeasure T := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [familyNormTime_ae T f] with t ht
    rw [ht]
    simp [RCLike.inner_apply, mul_comm]
  have h : Filter.Tendsto (fun n => ⟪a, familyNormTime T (u n)⟫_ℝ) Filter.atTop (𝓝 ⟪a,
      familyNormTime T v⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds (familyNormTime_tendsto T u v hu)
  simpa only [he] using h


-- @@ L81-81 verbatim
end EulerFamilyNormTime


-- @@ L83-83 verbatim
end

-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end


-- @@ L88-88 verbatim
@[expose] public section


-- @@ L90-90 verbatim
noncomputable section


-- @@ L92-92 verbatim
namespace EulerWeightedForcingTime


-- @@ L94-95 verbatim
open MeasureTheory Set EulerTimeLp EulerVolterraConvolution EulerFamilyNormTime
    EulerFiniteMetricEnergy

-- @@ L96-96 verbatim
open scoped Topology


-- @@ L98-98 verbatim
variable {A I H : Type*} [Fintype A] [Fintype I] [NormedAddCommGroup H] [NormedSpace ℝ H]


-- @@ L100-104 verbatim
/-- Multiplication by a continuous scalar time weight as a genuine Bochner operator. -/
def scalarTimeMultiplier (T : ℝ) (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, ℝ)) : TimeLp T ℝ →L[ℝ] TimeLp T
    ℝ :=
  timeMultiplier T hT (⟨fun t => w t • ContinuousLinearMap.id ℝ ℝ,
    w.continuous.smul continuous_const⟩ : C(Icc (0 : ℝ) T, ℝ →L[ℝ] ℝ))


-- @@ L106-112 verbatim
/-- The actual scalar multiplier has its literal weighted representative. -/
theorem scalarTimeMultiplier_ae (T : ℝ) (hT : 0 ≤ T) (w : C(Icc (0 : ℝ) T, ℝ)) (u : TimeLp T ℝ) :
    (scalarTimeMultiplier T hT w u : ℝ → ℝ) =ᵐ[timeMeasure T] fun t => extendPath T hT w t * u t :=
        by
  exact timeMultiplier_ae T hT
    (⟨fun t => w t • ContinuousLinearMap.id ℝ ℝ, w.continuous.smul continuous_const⟩ :
      C(Icc (0 : ℝ) T, ℝ →L[ℝ] ℝ)) u


-- @@ L114-117 verbatim
/-- The genuine finite weighted sum of actual forcing norms represented in L² time. -/
def weightedForcingTime (T : ℝ) (hT : 0 ≤ T) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → TimeLp T (I → H)) : TimeLp T ℝ :=
  ∑ i, scalarTimeMultiplier T hT (w i) (familyNormTime T (F i))


-- @@ L119-135 verbatim
/-- The actual Bochner forcing sum is the literal finite weighted family norm almost everywhere. -/
theorem weightedForcingTime_ae (T : ℝ) (hT : 0 ≤ T) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → TimeLp T (I → H)) :
    (weightedForcingTime T hT w F : ℝ → ℝ) =ᵐ[timeMeasure T]
      fun t => ∑ i, extendPath T hT (w i) t * familyNorm (F i t) := by
  have hsingle (i : A) :
      (scalarTimeMultiplier T hT (w i) (familyNormTime T (F i)) : ℝ → ℝ) =ᵐ[timeMeasure T]
        fun t => extendPath T hT (w i) t * familyNorm (F i t) := by
    filter_upwards [scalarTimeMultiplier_ae T hT (w i) (familyNormTime T (F i)), familyNormTime_ae
        T (F i)]
      with t h1 h2
    rw [h1, h2]
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset A)
    (fun i => scalarTimeMultiplier T hT (w i) (familyNormTime T (F i))), ae_all_iff.mpr hsingle]
    with t ht hh
  rw [weightedForcingTime, ht]
  exact Finset.sum_congr rfl (fun i _ => hh i)


-- @@ L137-145 verbatim
/-- Actual finite weighted forcing sums converge strongly with the actual L² forcing fields. -/
theorem weightedForcingTime_tendsto (T : ℝ) (hT : 0 ≤ T) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : ℕ → A → TimeLp T (I → H)) (f : A → TimeLp T (I → H))
    (hF : ∀ i, Filter.Tendsto (fun n => F n i) Filter.atTop (𝓝 (f i))) :
    Filter.Tendsto (fun n => weightedForcingTime T hT w (F n)) Filter.atTop
      (𝓝 (weightedForcingTime T hT w f)) := by
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    (scalarTimeMultiplier T hT (w i)).continuous.continuousAt.tendsto.comp
      (familyNormTime_tendsto T (fun n => F n i) (f i) (hF i)))


-- @@ L147-150 verbatim
/-- The literal weighted forcing norm along continuous time paths. -/
def weightedForcingPath (T : ℝ) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → C(Icc (0 : ℝ) T, I → H)) : C(Icc (0 : ℝ) T, ℝ) :=
  ∑ i, w i * ⟨fun t => familyNorm (F i t), familyNorm_lipschitz.continuous.comp (F i).continuous⟩


-- @@ L152-157 verbatim
/-- The bundled weighted forcing path evaluates to its literal finite norm sum. -/
theorem weightedForcingPath_apply (T : ℝ) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → C(Icc (0 : ℝ) T, I → H)) (t : Icc (0 : ℝ) T) :
    weightedForcingPath T w F t = ∑ i, w i t * familyNorm (F i t) := by
  simp only [weightedForcingPath, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
      ContinuousMap.coe_mk]


-- @@ L159-174 verbatim
/-- Continuous forcing paths have exactly the same weighted norm in the genuine Bochner
construction. -/
theorem weightedForcingTime_pathLp (T : ℝ) (hT : 0 ≤ T) (w : A → C(Icc (0 : ℝ) T, ℝ))
    (F : A → C(Icc (0 : ℝ) T, I → H)) :
    weightedForcingTime T hT w (fun i => pathLp T hT (F i)) = pathLp T hT (weightedForcingPath T w
        F) := by
  apply Lp.ext
  filter_upwards [weightedForcingTime_ae T hT w (fun i => pathLp T hT (F i)),
    ae_all_iff.mpr (fun i => pathLp_ae T hT (F i)), pathLp_ae T hT (weightedForcingPath T w F)]
    with t h1 h2 h3
  rw [h1, h3]
  change (∑ i, extendPath T hT (w i) t * familyNorm (pathLp T hT (F i) t)) =
    weightedForcingPath T w F (projIcc 0 T hT t)
  rw [weightedForcingPath_apply]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => extendPath T hT (w i) t * familyNorm x)
      (h2 i))


-- @@ L176-176 verbatim
end EulerWeightedForcingTime
