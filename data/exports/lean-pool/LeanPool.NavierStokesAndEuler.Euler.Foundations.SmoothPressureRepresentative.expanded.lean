/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierUniform
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDerivativeNorm


-- @@ L17-17 verbatim
/-! Actual C∞ representatives obtained from all-order strong cylinder jets. -/


-- @@ L19-19 verbatim
section


-- @@ L21-21 verbatim
/-! Smoothness of uniform limits of complete Fréchet derivative towers. -/


-- @@ L23-23 verbatim
section


-- @@ L25-25 verbatim
/-! Full Fréchet tensor convergence from the genuine cylinder derivative words. -/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace EulerMollifierTensors


-- @@ L33-33 verbatim
open MeasureTheory Filter EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates

-- @@ L34-34 verbatim
open EulerLiftedGradientSpace EulerMetricTransport EulerSobolevDerivativeNorm

-- @@ L35-35 verbatim
open scoped ContDiff Topology


-- @@ L37-37 verbatim
variable (period : ℝ)


-- @@ L39-56 verbatim
/-- The operator norm of a difference of derivative tensors is controlled by the finite coordinate
sum. -/
theorem tensor_difference_le_word_sum (m : ℕ) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z‖ ≤
    ∑ w : Fin m → Fin 4,
      ‖iteratedFieldDerivative period w f (euclideanCover period z + x) -
        iteratedFieldDerivative period w g (euclideanCover period z + x)‖ := by
  have h := multilinear_norm_le_coordinate_sum 4 m
    (iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z)
  simpa only [sub_apply,
    ← euclideanLift_iteratedFieldDerivative period _ f hf,
    ← euclideanLift_iteratedFieldDerivative period _ g hg,
    euclideanLift_eq_translated_cover, translated] using h


-- @@ L58-93 verbatim
/-- Uniform Cauchy convergence of every coordinate word gives uniform Cauchy convergence of the full
tensor. -/
theorem tensor_uniformCauchy_of_words (m : ℕ) (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ w : Fin m → Fin 4,
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (x : LiftDomain period) :
    UniformCauchySeqOn
      (fun k => iteratedFDeriv ℝ m (euclideanLift period (f k) x)) atTop Set.univ := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hc : 0 < (4 : ℝ)^m := pow_pos (by norm_num) _
  have hsmall := fun w : Fin m → Fin 4 =>
    Metric.uniformCauchySeqOn_iff.mp (hC w) (ε / (4 : ℝ)^m) (div_pos hε hc)
  choose N hN using hsmall
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk l hl z _
  have hword (w : Fin m → Fin 4) :
      ‖iteratedFieldDerivative period w (f k) (euclideanCover period z + x) -
        iteratedFieldDerivative period w (f l) (euclideanCover period z + x)‖ < ε / (4 : ℝ)^m := by
    simpa only [dist_eq_norm] using hN w k
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hk) l
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hl)
      (euclideanCover period z + x) (Set.mem_univ _)
  rw [dist_eq_norm]
  apply (tensor_difference_le_word_sum period m (f k) (f l) (hf k) (hf l) x z).trans_lt
  calc
    _ < ∑ _w : Fin m → Fin 4, ε / (4 : ℝ)^m := by
      apply Finset.sum_lt_sum (fun w _ => (hword w).le)
      exact ⟨fun _ => 0, Finset.mem_univ _, hword _⟩
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
      push_cast
      exact mul_div_cancel₀ ε hc.ne'


-- @@ L95-95 verbatim
end EulerMollifierTensors


-- @@ L97-97 verbatim
end

-- @@ L98-98 verbatim
end


-- @@ L100-100 verbatim
end


-- @@ L102-102 verbatim
section


-- @@ L104-106 verbatim
/-!
# Smooth Uniform Limit
-/


-- @@ L108-108 verbatim
@[expose] public section


-- @@ L110-110 verbatim
noncomputable section


-- @@ L112-112 verbatim
namespace EulerSmoothUniformLimit


-- @@ L114-114 verbatim
open Filter

-- @@ L115-115 verbatim
open scoped ContDiff Topology


-- @@ L117-118 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]


-- @@ L120-141 verbatim
/-- An infinite compatible derivative tower is smooth at every level. -/
theorem contDiff_of_derivative_tower (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hJ : ∀ n x, HasFDerivAt (J n) (L n (J (n + 1) x)) x) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  have hfinite : ∀ k : ℕ, ∀ n, ContDiff ℝ k (J n) := by
    intro k
    induction k with
    | zero =>
      intro n
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun x => (hJ n x).continuousAt))
    | succ k ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hJ n x).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (J n) = fun x => L n (J (n + 1) x) :=
        funext (fun x => (hJ n x).fderiv)
      rw [he]
      exact (L n).contDiff.comp (ih (n + 1))
  intro n
  exact contDiff_infty.mpr (fun k => hfinite k n)


-- @@ L143-154 verbatim
/-- Uniform limits of a compatible smooth derivative tower are again smooth.
This is the completion step for Sobolev mollifications. -/
theorem contDiff_of_uniform_derivative_limits
    (f : ∀ n, ℕ → E → F n) (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hlim : ∀ n, TendstoUniformly (f n) (J n) atTop) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  apply contDiff_of_derivative_tower J L
  intro n x
  have hd := (L n).uniformContinuous.comp_tendstoUniformly (hlim (n + 1))
  exact hasFDerivAt_of_tendstoUniformly hd (hf n) (fun y => (hlim n).tendsto_at y) x


-- @@ L156-173 verbatim
/-- Completeness constructs every limit in a uniformly Cauchy derivative tower;
the limit and all of its compatible derivatives are smooth. -/
theorem exists_smooth_limit_of_uniform_cauchy_tower [∀ n, CompleteSpace (F n)]
    (f : ∀ n, ℕ → E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hC : ∀ n, UniformCauchySeqOn (f n) atTop Set.univ) :
    ∃ J : ∀ n, E → F n,
      (∀ n, TendstoUniformly (f n) (J n) atTop) ∧ (∀ n, ContDiff ℝ ∞ (J n)) := by
  have hp : ∀ n x, ∃ v : F n, Tendsto (fun k => f n k x) atTop (nhds v) := by
    intro n x
    exact cauchy_map_iff_exists_tendsto.mp ((hC n).cauchy_map (Set.mem_univ x))
  choose J hJ using hp
  have hlim : ∀ n, TendstoUniformly (f n) (J n) atTop := by
    intro n
    rw [← tendstoUniformlyOn_univ]
    exact (hC n).tendstoUniformlyOn_of_tendsto (fun x _ => hJ n x)
  exact ⟨J, hlim, contDiff_of_uniform_derivative_limits f J L hf hlim⟩


-- @@ L175-175 verbatim
end EulerSmoothUniformLimit


-- @@ L177-177 verbatim
end

-- @@ L178-178 verbatim
end


-- @@ L180-180 verbatim
end


-- @@ L182-182 verbatim
@[expose] public section


-- @@ L184-184 verbatim
noncomputable section


-- @@ L186-186 verbatim
namespace EulerSmoothTensorLimit


-- @@ L188-188 verbatim
open Filter

-- @@ L189-189 verbatim
open scoped ContDiff Topology


-- @@ L191-192 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


-- @@ L194-214 verbatim
/-- A uniformly Cauchy sequence at every actual Fréchet derivative order has a genuine smooth limit.
-/
theorem exists_smooth_limit (f : ℕ → E → F) (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hC : ∀ m, UniformCauchySeqOn (fun k => iteratedFDeriv ℝ m (f k)) atTop Set.univ) :
    ∃ g : E → F, TendstoUniformly f g atTop ∧ ContDiff ℝ ∞ g := by
  let L (m : ℕ) : (E [×(m+1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×m]→L[ℝ] F)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E)
        F).toContinuousLinearEquiv.toContinuousLinearMap
  have hD (m k : ℕ) (x : E) : HasFDerivAt (iteratedFDeriv ℝ m (f k))
      (L m (iteratedFDeriv ℝ (m+1) (f k) x)) x := by
    have hd := (hf k).differentiable_iteratedFDeriv
      (show (m : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.natCast_lt_top m) x
    exact hd.hasFDerivAt
  obtain ⟨J, hJ, hJs⟩ := EulerSmoothUniformLimit.exists_smooth_limit_of_uniform_cauchy_tower
    (fun m k => iteratedFDeriv ℝ m (f k)) L hD hC
  let A := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨fun x => A (J 0 x), ?_, A.contDiff.comp (hJs 0)⟩
  have h := A.uniformContinuous.comp_tendstoUniformly (hJ 0)
  simpa only [A, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply] using h


-- @@ L216-216 verbatim
section Cylinder


-- @@ L218-218 verbatim
open EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev EulerLiftedGradientSpace

-- @@ L219-219 verbatim
open EulerMetricTransport EulerMollifierTensors


-- @@ L221-247 verbatim
/-- A pointwise cylinder limit is C∞ when every coordinate derivative word is uniformly Cauchy. -/
theorem cylinder_smooth_of_uniformCauchy_words (period : ℝ)
    (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ m (w : Fin m → Fin 4),
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (g : LiftDomain period → Vector3)
    (hpoint : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := by
  intro x
  obtain ⟨G, hG, hGs⟩ := exists_smooth_limit
    (fun k => euclideanLift period (f k) x)
    (fun k => euclideanLift_smooth period (f k) (hf k) x)
    (fun m => tensor_uniformCauchy_of_words period m f hf (hC m) x)
  have he : euclideanLift period g x = G := by
    funext z
    have hp : Tendsto (fun k => euclideanLift period (f k) x z) atTop
        (𝓝 (euclideanLift period g x z)) := by
      simpa only [euclideanLift_eq_translated_cover, translated] using
        hpoint (euclideanCover period z + x)
    exact tendsto_nhds_unique hp (hG.tendsto_at z)
  have hlocal : localFieldLift period g x = G ∘ coordinateEquiv.symm := by
    rw [← he]
    funext v
    simp only [euclideanLift, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hlocal]
  exact hGs.comp coordinateEquiv.symm.contDiff


-- @@ L249-249 verbatim
end Cylinder


-- @@ L251-251 verbatim
end EulerSmoothTensorLimit


-- @@ L253-253 verbatim
end

-- @@ L254-254 verbatim
end


-- @@ L256-256 verbatim
end


-- @@ L258-258 verbatim
@[expose] public section


-- @@ L260-260 verbatim
noncomputable section


-- @@ L262-262 verbatim
namespace EulerSmoothPressureRepresentative


-- @@ L264-265 verbatim
open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMollifierRepresentative EulerMollifierUniform

-- @@ L266-266 verbatim
open scoped ContDiff Topology


-- @@ L268-268 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L270-287 verbatim
/-- All-order strong cylinder jets produce an actual C∞ representative of the L² field. -/
theorem exists_smooth_representative (U : LiftL2 period)
    (J : ∀ s : ℕ, SpatialJet period standardDirection s U) :
    ∃ g : LiftDomain period → Vector3,
      (∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) ∧
      (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  let w : Fin 0 → Fin 4 := Fin.elim0
  obtain ⟨g, hg⟩ := exists_smoothMollifier_word_uniform_limit period U (J 3) w
  have hpoint : ∀ x, Filter.Tendsto (fun n => smoothMollifier period n U x)
      Filter.atTop (𝓝 (g x)) := fun x => hg.tendsto_at x
  have hC : ∀ m (v : Fin m → Fin 4), UniformCauchySeqOn
      (fun n => iteratedFieldDerivative period v (smoothMollifier period n U)) Filter.atTop
          Set.univ :=
    fun m v => smoothMollifier_word_uniformCauchy period U (J (m + 3)) v
  refine ⟨g, ?_, ?_⟩
  · exact EulerSmoothTensorLimit.cylinder_smooth_of_uniformCauchy_words period
      (fun n => smoothMollifier period n U) (fun n => smoothMollifier_smooth period n U) hC g hpoint
  · simpa only [SpatialJet.word_zero] using smoothMollifier_word_limit_ae period U (J 3) w g hg


-- @@ L289-300 verbatim
/-- The genuine coercive pressure inverse has a C∞ representative when its actual coefficients
and forcing possess strong derivative jets at every finite order. -/
theorem exists_smooth_pressure (A : SmoothCoefficient period) (f : LiftL2 period)
    (K : ∀ s : ℕ, CoefficientJet period standardDirection s A)
    (J : ∀ s : ℕ, SpatialJet period standardDirection s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ (A.coefficient x v) v) :
    ∃ p : LiftDomain period → Vector3,
      (∀ x, ContDiff ℝ ∞ (localFieldLift period p x)) ∧
      (A.pressure κ m c hc hpos f : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p :=
  exists_smooth_representative period (A.pressure κ m c hc hpos f)
    (fun s => (J s).solvePressure (K s) κ m c hc hpos)


-- @@ L302-302 verbatim
end EulerSmoothPressureRepresentative
