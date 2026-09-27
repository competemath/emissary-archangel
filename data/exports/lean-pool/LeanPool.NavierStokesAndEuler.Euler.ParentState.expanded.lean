/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerChild
public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerSobolev
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketScaledBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
import LeanPool.NavierStokesAndEuler.Euler.SmoothL2ScalingContinuity
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketParity
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketJoinedInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionData
import LeanPool.NavierStokesAndEuler.Euler.PacketForwardInitializedCorrectionParity
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedCorrectionParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2CoefficientPath
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.FlowL2Transport
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalContinuity
public import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
import LeanPool.NavierStokesAndEuler.Euler.PacketVolumeDivergence
public import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowGevrey
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedGradientSpace
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import LeanPool.NavierStokesAndEuler.ForMathlib.StronglyMeasurable
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import LeanPool.NavierStokesAndEuler.Euler.LpDominatedConvergence


-- @@ L38-40 verbatim
/-! The recursive physical state consists of the actual Euler solution,
its all-order Sobolev fields, its particle-label bounds, and its symmetry.
Restriction and the exact packet construction preserve these data. -/


-- @@ L42-42 verbatim
section


-- @@ L44-46 verbatim
/-! Spatial Sobolev paths for the actual inverse parent flow. Its
measure preservation, smoothness, derivative bounds and jet continuity
are all derived from the source deformation and inverse identities. -/


-- @@ L48-48 verbatim
section


-- @@ L50-52 verbatim
/-! Strong Sobolev continuity under genuine varying volume-preserving
maps. Faà di Bruno gives actual derivative tensors, and dominated
convergence handles the bounded, pointwise continuous coefficients. -/


-- @@ L54-54 verbatim
section


-- @@ L56-58 verbatim
/-! Bounded pointwise operator fields act on actual L² classes. Joint
continuity of the coefficients, with a uniform bound, gives strong
continuity even when uniform convergence of coefficients is unavailable. -/


-- @@ L60-60 verbatim
@[expose] public section


-- @@ L62-62 verbatim
noncomputable section


-- @@ L64-64 verbatim
namespace EulerLpPointwiseMultiplier


-- @@ L66-66 verbatim
open MeasureTheory Filter

-- @@ L67-67 verbatim
open scoped Topology


-- @@ L69-73 verbatim
variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure X) (A : X → E →L[ℝ] F)
  (hA : AEStronglyMeasurable A μ) (C : ℝ) (hC : ∀ x, ‖A x‖ ≤ C)


-- @@ L75-81 verbatim
include hA hC in
theorem apply_memLp (u : Lp E 2 μ) : MemLp (fun x => A x (u x)) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := C)
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable u))
  · exact Eventually.of_forall (fun x => ((A x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (u x))))


-- @@ L83-85 verbatim
/-- Apply Lᵖ, given by `(apply_memLp μ A hA C hC u).toLp (fun x => A x (u x))`. -/
def applyLp (u : Lp E 2 μ) : Lp F 2 μ :=
  (apply_memLp μ A hA C hC u).toLp (fun x => A x (u x))


-- @@ L87-89 verbatim
theorem applyLp_ae (u : Lp E 2 μ) :
    (applyLp μ A hA C hC u : X → F) =ᵐ[μ] fun x => A x (u x) :=
  (apply_memLp μ A hA C hC u).coeFn_toLp


-- @@ L91-97 verbatim
theorem applyLp_norm_le (u : Lp E 2 μ) :
    ‖applyLp μ A hA C hC u‖ ≤ C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applyLp_ae μ A hA C hC u] with x hx
  rw [hx]
  exact ((A x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (u x)))


-- @@ L99-116 verbatim
/-- Linear, bundling `toFun`, `map_add`, `map_smul`. -/
def linear : Lp E 2 μ →ₗ[ℝ] Lp F 2 μ where
  toFun := applyLp μ A hA C hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [applyLp_ae μ A hA C hC (u+v), applyLp_ae μ A hA C hC u,
      applyLp_ae μ A hA C hC v, Lp.coeFn_add u v,
      Lp.coeFn_add (applyLp μ A hA C hC u) (applyLp μ A hA C hC v)]
      with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1,h5,h4,h2,h3,map_add]
  map_smul' r u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [applyLp_ae μ A hA C hC (r • u), applyLp_ae μ A hA C hC u,
      Lp.coeFn_smul r u,Lp.coeFn_smul r (applyLp μ A hA C hC u)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply] at h3 h4
    rw [h1,h4,h3,h2,map_smul]


-- @@ L118-120 verbatim
/-- Operator, given by `(linear μ A hA C hC).mkContinuous C (applyLp_norm_le μ A hA C hC)`. -/
def operator : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (linear μ A hA C hC).mkContinuous C (applyLp_norm_le μ A hA C hC)


-- @@ L122-124 verbatim
theorem operator_ae (u : Lp E 2 μ) :
    (operator μ A hA C hC u : X → F) =ᵐ[μ] fun x => A x (u x) :=
  applyLp_ae μ A hA C hC u


-- @@ L126-127 verbatim
theorem operator_bound (u : Lp E 2 μ) : ‖operator μ A hA C hC u‖ ≤ C*‖u‖ :=
  applyLp_norm_le μ A hA C hC u


-- @@ L129-131 verbatim
variable {K : Type*} [TopologicalSpace K] [FirstCountableTopology K]
  (B : K → X → E →L[ℝ] F) (hB : ∀ t, AEStronglyMeasurable (B t) μ)
  (hBt : ∀ x, Continuous (fun t => B t x)) (hBC : ∀ t x, ‖B t x‖ ≤ C)


-- @@ L133-155 verbatim
include hBt in
theorem operator_strongly_continuous (u : Lp E 2 μ) :
    Continuous (fun t => operator μ (B t) (hB t) C (hBC t) u) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply EulerLpConvergence.tendsto_of_dominated μ
    (fun t => operator μ (B t) (hB t) C (hBC t) u)
    (operator μ (B t₀) (hB t₀) C (hBC t₀) u)
    (fun t x => B t x (u x)) (fun x => B t₀ x (u x))
    (fun t => operator_ae μ (B t) (hB t) C (hBC t) u)
    (operator_ae μ (B t₀) (hB t₀) C (hBC t₀) u)
    (fun x => (2*C)*‖u x‖) ((Lp.memLp u).norm.const_mul (2*C))
  · apply Eventually.of_forall
    intro t
    apply Eventually.of_forall
    intro x
    calc
      _ ≤ ‖B t x (u x)‖ + ‖B t₀ x (u x)‖ := norm_sub_le _ _
      _ ≤ C*‖u x‖ + C*‖u x‖ := add_le_add
        (((B t x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hBC t x) (norm_nonneg _)))
        (((B t₀ x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hBC t₀ x) (norm_nonneg _)))
      _ = _ := by ring
  · exact Eventually.of_forall (fun x => ((hBt x).clm_apply continuous_const).tendsto t₀)


-- @@ L157-182 verbatim
include hBt in
theorem operator_path_continuous (u : K → Lp E 2 μ) (hu : Continuous u) :
    Continuous (fun t => operator μ (B t) (hB t) C (hBC t) (u t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h₁ : Tendsto (fun t => C*‖u t-u t₀‖) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero,mul_zero] using ((hu.tendsto t₀).sub_const (u
        t₀)).norm.const_mul C
  have h₂ : Tendsto (fun t => ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
      operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero] using
      (((operator_strongly_continuous μ C B hB hBt hBC (u t₀)).tendsto t₀).sub_const
        (operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀))).norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa only [add_zero] using h₁.add h₂)
  intro t
  calc
    _ ≤ ‖operator μ (B t) (hB t) C (hBC t) (u t) -
        operator μ (B t) (hB t) C (hBC t) (u t₀)‖ +
      ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
        operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C*‖u t-u t₀‖ +
      ‖operator μ (B t) (hB t) C (hBC t) (u t₀) -
        operator μ (B t₀) (hB t₀) C (hBC t₀) (u t₀)‖ := add_le_add (by
      rw [← map_sub]
      exact operator_bound μ (B t) (hB t) C (hBC t) (u t-u t₀)) le_rfl


-- @@ L184-184 verbatim
end EulerLpPointwiseMultiplier


-- @@ L186-186 verbatim
end

-- @@ L187-187 verbatim
end


-- @@ L189-189 verbatim
end


-- @@ L191-191 verbatim
@[expose] public section


-- @@ L193-193 verbatim
noncomputable section


-- @@ L195-195 verbatim
namespace EulerVolumeSobolevPath


-- @@ L197-198 verbatim
open MeasureTheory Filter EulerLiftedGradientSpace
  EulerLpPointwiseMultiplier

-- @@ L199-199 verbatim
open scoped Topology ContDiff


-- @@ L201-202 verbatim
/-- Tensor: an abbreviation for `Vector3 [×n]→L[ℝ] Vector3`. -/
abbrev Tensor (n : ℕ) := Vector3 [×n]→L[ℝ] Vector3


-- @@ L204-205 verbatim
/-- Cache the standard `NormedAddCommGroup (Tensor n)` instance to shorten typeclass synthesis. -/
local instance instVolumeSobolevPath1 (n : ℕ) : NormedAddCommGroup (Tensor n) := inferInstance

-- @@ L206-207 verbatim
/-- Cache the standard `NormedSpace ℝ (Tensor n)` instance to shorten typeclass synthesis. -/
local instance instVolumeSobolevPath2 (n : ℕ) : NormedSpace ℝ (Tensor n) := inferInstance

-- @@ L208-211 verbatim
/-- Cache the standard `NormedAddCommGroup (Tensor a →L[ℝ] Tensor b)` instance to shorten
typeclass synthesis. -/
local instance instVolumeSobolevPath3 (a b : ℕ) : NormedAddCommGroup (Tensor a →L[ℝ] Tensor b) :=
    inferInstance

-- @@ L212-215 verbatim
/-- Cache the standard `NormedSpace ℝ (Tensor a →L[ℝ] Tensor b)` instance to shorten typeclass
synthesis. -/
local instance instVolumeSobolevPath4 (a b : ℕ) : NormedSpace ℝ (Tensor a →L[ℝ] Tensor b) :=
    inferInstance

-- @@ L216-219 verbatim
local instance instVolumeSobolevPath5 (a b : ℕ) : SecondCountableTopologyEither Vector3 (Tensor a
    →L[ℝ] Tensor b)
    :=
  ⟨Or.inl inferInstance⟩


-- @@ L221-223 verbatim
variable {K : Type*} [TopologicalSpace K]
  (Y : C(K, C(Vector3, Vector3))) (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (u : ∀ i : ℕ, C(K, Lp (Tensor i) 2 (volume : Measure Vector3)))


-- @@ L225-228 verbatim
/-- Pulled jet path, bundling `toFun`, `continuous_toFun`. -/
def pulledJetPath (i : ℕ) : C(K,Lp (Tensor i) 2 (volume : Measure Vector3)) where
  toFun t := Lp.compMeasurePreserving (Y t) (hmp t) (u i t)
  continuous_toFun := (u i).continuous.compMeasurePreservingLp Y.continuous hmp (by norm_num)


-- @@ L230-236 verbatim
theorem pulledJetPath_ae (g : K → Vector3 → Vector3)
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t))
    (i : ℕ) (t : K) :
    (pulledJetPath Y hmp u i t : Vector3 → Tensor i) =ᵐ[volume]
      fun x => iteratedFDeriv ℝ i (g t) (Y t x) :=
  (Lp.coeFn_compMeasurePreserving (u i t) (hmp t)).trans
    ((hmp t).quasiMeasurePreserving.ae_eq_comp (hu i t))


-- @@ L238-238 verbatim
variable {n : ℕ}


-- @@ L240-245 verbatim
/-- Partition coefficient, given by `(c.compAlongOrderedFinpartitionL ℝ Vector3 Vector3
Vector3).flipMultilinear (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x)`. -/
def partitionCoefficient (c : OrderedFinpartition n) (t : K) (x : Vector3) :
    Tensor c.length →L[ℝ] Tensor n :=
  (c.compAlongOrderedFinpartitionL ℝ Vector3 Vector3 Vector3).flipMultilinear
    (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x)


-- @@ L247-250 verbatim
theorem partitionCoefficient_apply (c : OrderedFinpartition n) (t : K) (x : Vector3)
    (v : Tensor c.length) :
    partitionCoefficient Y c t x v = c.compAlongOrderedFinpartition v
      (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) := rfl


-- @@ L252-254 verbatim
/-- Partition bound, given by `∏ i : Fin c.length, D^(c.partSize i)`. -/
def partitionBound (D : ℝ) (c : OrderedFinpartition n) : ℝ :=
  ∏ i : Fin c.length, D^(c.partSize i)


-- @@ L256-259 verbatim
variable (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : K × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D ^ i)


-- @@ L261-265 verbatim
include hJ in
theorem partitionCoefficient_continuous (c : OrderedFinpartition n) :
    Continuous (Function.uncurry (partitionCoefficient Y c)) := by
  exact (c.compAlongOrderedFinpartitionL ℝ Vector3 Vector3 Vector3).flipMultilinear.cont.comp
    (continuous_pi (fun i => hJ (c.partSize i) (c.partSize_pos i) (c.partSize_le i)))


-- @@ L267-270 verbatim
include hJ in
theorem partitionCoefficient_aestronglyMeasurable (c : OrderedFinpartition n) (t : K) :
    AEStronglyMeasurable (partitionCoefficient Y c t) volume :=
  ((partitionCoefficient_continuous Y hJ c).uncurry_left t).aestronglyMeasurable_of_secondCountable


-- @@ L272-284 verbatim
include hD hB in
theorem partitionCoefficient_bound (c : OrderedFinpartition n) (t : K) (x : Vector3) :
    ‖partitionCoefficient Y c t x‖ ≤ partitionBound D c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg (fun i _ => pow_nonneg hD _))
  intro v
  rw [partitionCoefficient_apply]
  calc
    _ ≤ ‖v‖ * ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) (Y t) x‖ :=
      c.norm_compAlongOrderedFinpartition_le _ _
    _ ≤ ‖v‖ * partitionBound D c := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => hB (c.partSize i) (c.partSize_pos i) (c.partSize_le i) t x)) (norm_nonneg _)
    _ = _ := mul_comm _ _


-- @@ L286-286 verbatim
variable [FirstCountableTopology K]


-- @@ L288-299 verbatim
/-- Partition path, bundling `toFun`, `continuous_toFun`. -/
def partitionPath (c : OrderedFinpartition n) :
    C(K,Lp (Tensor n) 2 (volume : Measure Vector3)) where
  toFun t := operator volume (partitionCoefficient Y c t)
    (partitionCoefficient_aestronglyMeasurable Y hJ c t)
    (partitionBound D c) (partitionCoefficient_bound Y D hD hB c t) (pulledJetPath Y hmp u c.length
        t)
  continuous_toFun := operator_path_continuous volume (partitionBound D c) (partitionCoefficient Y
      c)
    (fun t => partitionCoefficient_aestronglyMeasurable Y hJ c t)
    (fun _ => (partitionCoefficient_continuous Y hJ c).comp (continuous_id.prodMk continuous_const))
    (partitionCoefficient_bound Y D hD hB c) _ (pulledJetPath Y hmp u c.length).continuous


-- @@ L301-312 verbatim
theorem partitionPath_ae (g : K → Vector3 → Vector3)
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t))
    (c : OrderedFinpartition n) (t : K) :
    (partitionPath Y hmp u D hD hJ hB c t : Vector3 → Tensor n) =ᵐ[volume]
      fun x => c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (g t) (Y t x))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) := by
  have h := operator_ae volume (partitionCoefficient Y c t)
    (partitionCoefficient_aestronglyMeasurable Y hJ c t)
    (partitionBound D c) (partitionCoefficient_bound Y D hD hB c t) (pulledJetPath Y hmp u c.length
        t)
  filter_upwards [h,pulledJetPath_ae Y hmp u g hu c.length t] with x hx hy
  exact hx.trans (by rw [hy,partitionCoefficient_apply])


-- @@ L314-316 verbatim
/-- Tensor path, given by `∑ c : OrderedFinpartition n, partitionPath Y hmp u D hD hJ hB c`. -/
def tensorPath : C(K,Lp (Tensor n) 2 (volume : Measure Vector3)) :=
  ∑ c : OrderedFinpartition n, partitionPath Y hmp u D hD hJ hB c


-- @@ L318-339 verbatim
theorem tensorPath_ae (g : K → Vector3 → Vector3)
    (hg : ∀ t, ContDiff ℝ ∞ (g t)) (hY : ∀ t, ContDiff ℝ ∞ (Y t))
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t)) (t : K) :
    (tensorPath Y hmp u D hD hJ hB t : Vector3 → Tensor n) =ᵐ[volume]
      iteratedFDeriv ℝ n (g t ∘ Y t) := by
  have hterms : ∀ᵐ x ∂volume, ∀ c : OrderedFinpartition n,
      (partitionPath Y hmp u D hD hJ hB c t) x =
      c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length (g t) (Y t x))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (Y t) x) :=
    ae_all_iff.mpr (fun c => partitionPath_ae Y hmp u D hD hJ hB g hu c t)
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun c : OrderedFinpartition n =>
    partitionPath Y hmp u D hD hJ hB c t)
  filter_upwards [hterms,hsum] with x hx hs
  simp only [tensorPath,ContinuousMap.sum_apply]
  rw [hs]
  simp only [Finset.sum_apply]
  rw [iteratedFDeriv_comp (i := n) ((hg t).contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by simp))
    ((hY t).contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by simp)) le_rfl]
  simp only [FormalMultilinearSeries.taylorComp,
      FormalMultilinearSeries.compAlongOrderedFinpartition,
    ftaylorSeries]
  exact Finset.sum_congr rfl (fun c _ => hx c)


-- @@ L341-341 verbatim
end EulerVolumeSobolevPath


-- @@ L343-343 verbatim
end

-- @@ L344-344 verbatim
end


-- @@ L346-346 verbatim
end


-- @@ L348-348 verbatim
section


-- @@ L350-351 verbatim
/-! Actual all-order field towers retain their spatial Sobolev regularity
after a smooth volume-preserving change of coordinates. -/


-- @@ L353-353 verbatim
section


-- @@ L355-356 verbatim
/-! Actual Sobolev integrability under a smooth volume-preserving change
of variables, with an explicit finite-order composition constant. -/


-- @@ L358-358 verbatim
@[expose] public section


-- @@ L360-360 verbatim
noncomputable section


-- @@ L362-362 verbatim
namespace EulerVolumeSobolevComposition


-- @@ L364-364 verbatim
open Set MeasureTheory EulerLiftedGradientSpace

-- @@ L365-365 verbatim
open scoped ContDiff NNReal ENNReal


-- @@ L367-369 verbatim
variable (f g : Vector3 → Vector3) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
  (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
  (hjet : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i)


-- @@ L371-382 verbatim
include hf hg hjet in
theorem compositionTensor_pointwise (x : Vector3) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      ((n.factorial : ℝ)*D^n) * ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖ := by
  have h := norm_iteratedFDeriv_comp_le hg hf (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω)) x
    (C := ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) (D := D)
    (fun i hi => Finset.single_le_sum
      (f := fun j : Fin (n+1) => ‖iteratedFDeriv ℝ j.val g (f x)‖)
      (fun _ _ => norm_nonneg _)
      (Finset.mem_univ (⟨i,by omega⟩ : Fin (n+1))))
    (fun i h1 hi => hjet i h1 hi x)
  exact h.trans_eq (by ring)


-- @@ L384-385 verbatim
variable (hmp : MeasurePreserving f volume volume)
  (hLp : ∀ i, i ≤ n → MemLp (iteratedFDeriv ℝ i g) 2 volume)


-- @@ L387-390 verbatim
include hmp hLp in
theorem composedJetNorm_memLp (i : Fin (n + 1)) :
    MemLp (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume :=
  ((hLp i (by omega)).norm).comp_measurePreserving hmp


-- @@ L392-404 verbatim
include hf hg hD hjet hmp hLp in
theorem compositionTensor_memLp :
    MemLp (iteratedFDeriv ℝ n (g ∘ f)) 2 volume := by
  have hs : MemLp (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume :=
    memLp_finsetSum _ (fun i _ => composedJetNorm_memLp f g n hmp hLp i)
  have hc : Continuous (iteratedFDeriv ℝ n (g ∘ f)) :=
    (hg.comp hf).continuous_iteratedFDeriv (by simp)
  apply (hs.const_mul ((n.factorial : ℝ)*D^n)).of_le
    hc.aestronglyMeasurable_of_secondCountable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))]
  exact compositionTensor_pointwise f g hf hg n D hjet x


-- @@ L406-410 verbatim
/-- Composition tensor Lᵖ, given by `(compositionTensor_memLp f g hf hg n D hD hjet hmp
hLp).toLp (iteratedFDeriv ℝ n (g ∘ f))`. -/
def compositionTensorLp :
    Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3) :=
  (compositionTensor_memLp f g hf hg n D hD hjet hmp hLp).toLp (iteratedFDeriv ℝ n (g ∘ f))


-- @@ L412-454 verbatim
theorem compositionTensorLp_norm_le :
    ‖compositionTensorLp f g hf hg n D hD hjet hmp hLp‖ ≤
      ((n.factorial : ℝ)*D^n) * ∑ i : Fin (n+1),
        (eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume).toReal := by
  let β : ℝ≥0 := ⟨(n.factorial : ℝ)*D^n,by positivity⟩
  have hA : eLpNorm (iteratedFDeriv ℝ n (g ∘ f)) 2 volume ≤
      (β : ℝ≥0∞)*eLpNorm (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (compositionTensor_memLp f g hf hg n D hD hjet hmp hLp).aestronglyMeasurable
    filter_upwards [] with x
    apply NNReal.coe_le_coe.mp
    change ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ ((n.factorial : ℝ)*D^n) *
      ‖∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖‖
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact compositionTensor_pointwise f g hf hg n D hjet x
  have he : (fun x => ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val g (f x)‖) =
      ∑ i : Fin (n+1), (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he] at hA
  have hB : eLpNorm (∑ i : Fin (n+1), fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume ≤
      ∑ i : Fin (n+1), eLpNorm (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume :=
    eLpNorm_sum_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hc (i : Fin (n+1)) : eLpNorm (fun x => ‖iteratedFDeriv ℝ i.val g (f x)‖) 2 volume =
      eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume := by
    change eLpNorm ((fun y => ‖iteratedFDeriv ℝ i.val g y‖) ∘ f) 2 volume = _
    rw [eLpNorm_comp_measurePreserving (hLp i (by
        omega)).aestronglyMeasurable.norm hmp,
      eLpNorm_norm _ (hLp i (by omega)).aestronglyMeasurable]
  simp_rw [hc] at hB
  have hAB : eLpNorm (iteratedFDeriv ℝ n (g ∘ f)) 2 volume ≤
      (β : ℝ≥0∞)*∑ i : Fin (n+1), eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume := by
    exact hA.trans (mul_le_mul le_rfl hB (by positivity) (by positivity))
  have hfin : (β : ℝ≥0∞)*∑ i : Fin (n+1),
      eLpNorm (iteratedFDeriv ℝ i.val g) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.sum_ne_top.2 (fun i _ => (hLp i (by omega)).eLpNorm_ne_top))
  have hR := ENNReal.toReal_mono hfin hAB
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun (i : Fin (n+1)) _ => (hLp i.val (by omega)).eLpNorm_ne_top)] at hR
  have hβ : (β : ℝ) = (n.factorial : ℝ)*D^n := rfl
  rw [hβ] at hR
  simpa only [compositionTensorLp,Lp.norm_toLp] using hR


-- @@ L456-456 verbatim
end EulerVolumeSobolevComposition


-- @@ L458-458 verbatim
end

-- @@ L459-459 verbatim
end


-- @@ L461-461 verbatim
end


-- @@ L463-463 verbatim
@[expose] public section


-- @@ L465-465 verbatim
noncomputable section


-- @@ L467-467 verbatim
namespace EulerVolumeSobolevPath


-- @@ L469-469 verbatim
open MeasureTheory EulerVolumeSobolevComposition EulerMetricTransport EulerLiftedGradientSpace

-- @@ L470-470 verbatim
open scoped ContDiff


-- @@ L472-478 verbatim
variable {K : Type*} [TopologicalSpace K] [FirstCountableTopology K]
  (Y : C(K, C(Vector3, Vector3))) (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (u : ∀ i : ℕ, C(K, Lp (Tensor i) 2 (volume : Measure Vector3))) {n : ℕ}
  (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : K × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D ^ i)


-- @@ L480-504 verbatim
theorem tensorPath_norm_le (g : K → Vector3 → Vector3)
    (hg : ∀ t, ContDiff ℝ ∞ (g t)) (hY : ∀ t, ContDiff ℝ ∞ (Y t))
    (hu : ∀ i t, (u i t : Vector3 → Tensor i) =ᵐ[volume] iteratedFDeriv ℝ i (g t)) (t : K) :
    ‖tensorPath Y hmp u D hD hJ hB t‖ ≤
      ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1), ‖u i.val t‖ := by
  have hLp : ∀ i, i ≤ n → MemLp (iteratedFDeriv ℝ i (g t)) 2 volume :=
    fun i _ => (memLp_congr_ae (hu i t)).mp (Lp.memLp (u i t))
  let V := compositionTensorLp (Y t) (g t) (hY t) (hg t) n D hD
    (fun i h1 hi => hB i h1 hi t) (hmp t) hLp
  have he : tensorPath Y hmp u D hD hJ hB t = V := by
    apply Lp.ext
    exact (tensorPath_ae Y hmp u D hD hJ hB g hg hY hu t).trans
      (compositionTensor_memLp (Y t) (g t) (hY t) (hg t) n D hD
        (fun i h1 hi => hB i h1 hi t) (hmp t) hLp).coeFn_toLp.symm
  rw [he]
  calc
    ‖V‖ ≤ ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1),
        (eLpNorm (iteratedFDeriv ℝ i.val (g t)) 2 volume).toReal :=
      compositionTensorLp_norm_le (Y t) (g t) (hY t) (hg t) n D hD
        (fun i h1 hi => hB i h1 hi t) (hmp t) hLp
    _ = _ := by
      apply congrArg (((n.factorial : ℝ) * D ^ n) * ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [Lp.norm_def,eLpNorm_congr_ae (hu i.val t)]


-- @@ L506-506 verbatim
end EulerVolumeSobolevPath


-- @@ L508-508 verbatim
namespace EulerAllOrderCorrectionData.FieldTower


-- @@ L510-511 verbatim
open Set MeasureTheory EulerMetricTransport EulerCylinderPhysicalTensor EulerCylinderSobolevSpace
  EulerLiftedGradientSpace

-- @@ L512-512 verbatim
open scoped ContDiff


-- @@ L514-521 verbatim
variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)
  (k : ℝ) (m : Vector3)
  (Y : C(Icc (0 : ℝ) T, C(Vector3, Vector3)))
  (hmp : ∀ t, MeasurePreserving (Y t) volume volume)
  (n : ℕ) (D : ℝ) (hD : 0 ≤ D)
  (hJ : ∀ i, 1 ≤ i → i ≤ n →
    Continuous (fun z : Icc (0 : ℝ) T × Vector3 => iteratedFDeriv ℝ i (Y z.1) z.2))
  (hB : ∀ i, 1 ≤ i → i ≤ n → ∀ t x, ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ D ^ i)


-- @@ L523-525 verbatim
/-- Volume point field, given by `A.physicalPointField k m t ∘ Y t`. -/
def volumePointField (t : Icc (0 : ℝ) T) : Vector3 → Vector3 :=
  A.physicalPointField k m t ∘ Y t


-- @@ L527-531 verbatim
/-- Volume tensor path, given by `EulerVolumeSobolevPath.tensorPath Y hmp (fun i =>
A.physicalTensorPath k m i) D hD hJ hB`. -/
def volumeTensorPath : C(Icc (0 : ℝ) T,
    Lp (Vector3 [×n]→L[ℝ] Vector3) 2 (volume : Measure Vector3)) :=
  EulerVolumeSobolevPath.tensorPath Y hmp (fun i => A.physicalTensorPath k m i) D hD hJ hB


-- @@ L533-535 verbatim
theorem volumePointField_smooth (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (A.volumePointField k m Y t) :=
  (A.physicalPointField_smooth k m t).comp (hY t)


-- @@ L537-542 verbatim
theorem volumeTensorPath_ae (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    (A.volumeTensorPath k m Y hmp n D hD hJ hB t : Vector3 → (Vector3 [×n]→L[ℝ] Vector3)) =ᵐ[volume]
      iteratedFDeriv ℝ n (A.volumePointField k m Y t) :=
  EulerVolumeSobolevPath.tensorPath_ae Y hmp (fun i => A.physicalTensorPath k m i) D hD hJ hB
    (A.physicalPointField k m) (A.physicalPointField_smooth k m) hY
    (A.physicalTensorPath_ae k m) t


-- @@ L544-553 verbatim
theorem volumeTensorPath_norm_le (hY : ∀ t, ContDiff ℝ ∞ (Y t)) (t : Icc (0 : ℝ) T) :
    ‖A.volumeTensorPath k m Y hmp n D hD hJ hB t‖ ≤
      ((n.factorial : ℝ)*D^n)*∑ i : Fin (n+1),
        frequencyFactor k m^i.val*(4 : ℝ)^i.val*Real.sqrt (2/P+2*P)*‖A.realization (i.val+1) t‖ :=
            by
  have h := EulerVolumeSobolevPath.tensorPath_norm_le Y hmp (fun i => A.physicalTensorPath k m i)
    D hD hJ hB (A.physicalPointField k m) (A.physicalPointField_smooth k m) hY
    (A.physicalTensorPath_ae k m) t
  exact h.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => A.physicalTensorValue_norm_le k m i.val t)) (by positivity))


-- @@ L555-555 verbatim
end EulerAllOrderCorrectionData.FieldTower


-- @@ L557-557 verbatim
end

-- @@ L558-558 verbatim
end


-- @@ L560-560 verbatim
end


-- @@ L562-562 verbatim
section


-- @@ L564-565 verbatim
/-! A finite-order Sobolev composition constant obtained from the actual
parent deformation. No inverse-flow derivative budget is assumed. -/


-- @@ L567-567 verbatim
@[expose] public section


-- @@ L569-569 verbatim
noncomputable section


-- @@ L571-571 verbatim
namespace EulerPacketInverseFlowGevrey


-- @@ L573-573 verbatim
open Set EulerSmoothLimit EulerGevrey EulerPacketPiola

-- @@ L574-574 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L576-578 verbatim
/-- Finite order constant, given by `1+9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2`. -/
def finiteOrderConstant (C R : ℝ) (n : ℕ) : ℝ :=
  1+9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2


-- @@ L580-584 verbatim
theorem sourceInverseRadius_one_le (C R : ℝ) (hR : 0 ≤ R) :
    1 ≤ sourceInverseRadius C R := by
  unfold sourceInverseRadius
  have h : 0 ≤ 18*C^2*R := by positivity
  linarith


-- @@ L586-591 verbatim
theorem finiteOrderConstant_one_le (C R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    1 ≤ finiteOrderConstant C R n := by
  have hL := (sourceInverseRadius_pos C R hR).le
  unfold finiteOrderConstant
  have h : 0 ≤ 9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2 := by positivity
  linarith


-- @@ L593-602 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x) = x)
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)


-- @@ L604-623 verbatim
include hX hY hXY hR hC hdet hF in
theorem inverseFlow_finiteOrderBound (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ i (Y t) x‖ ≤ (finiteOrderConstant C R n)^i := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hjn : j ≤ n := by omega
  have hL := sourceInverseRadius_one_le C R hR
  have hD := finiteOrderConstant_one_le C R hR n
  have hfac : (j.factorial : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hjn
  have hbound : 9*C^2*(sourceInverseRadius C R)^j*(j.factorial : ℝ)^2 ≤
      9*C^2*(sourceInverseRadius C R)^n*(n.factorial : ℝ)^2 := by
    gcongr
  calc
    _ ≤ 9*C^2*(sourceInverseRadius C R)^j*(j.factorial : ℝ)^2 :=
      inverseFlow_gevrey D X Y hX hY hXY R C hR hC hdet hF j t x
    _ ≤ finiteOrderConstant C R n := by
      exact hbound.trans (by unfold finiteOrderConstant; linarith)
    _ = (finiteOrderConstant C R n)^1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ hD hi


-- @@ L625-625 verbatim
end EulerPacketInverseFlowGevrey


-- @@ L627-627 verbatim
end

-- @@ L628-628 verbatim
end


-- @@ L630-630 verbatim
end


-- @@ L632-632 verbatim
@[expose] public section


-- @@ L634-634 verbatim
noncomputable section


-- @@ L636-636 verbatim
namespace EulerPacketSourceVolumeSobolev


-- @@ L638-640 verbatim
open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerFlowL2Transport EulerPacketInverseFlowGevrey EulerPacketPiola
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerGevrey

-- @@ L641-641 verbatim
open scoped ContDiff


-- @@ L643-654 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  (Z : FieldTower P D.T) (k : ℝ) (m : Space)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hYjoint : Continuous (Function.uncurry Y))
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)


-- @@ L656-662 verbatim
include hX hYX hXY hYjoint hdet in
theorem inversePath_volume (t : Icc (0 : ℝ) D.T) :
    MeasurePreserving (inversePath Y hYjoint t) volume volume := by
  apply inversePath_measurePreserving X Y (fun s x => D.F.field s x) hX hYX hXY hYjoint
  intro s x
  rw [← EulerPacketVolumeDivergence.operatorMatrix_det]
  exact hdet s x


-- @@ L664-672 verbatim
/-- Tensor path, constructed using `Z.volumeTensorPath`. -/
def tensorPath (n : ℕ) :
    C(Icc (0 : ℝ) D.T,Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)) :=
  Z.volumeTensorPath k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)


-- @@ L674-684 verbatim
theorem tensorPath_ae (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t :
      Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n (fun x => Z.pointField t (cylinderGraph P k m (Y t x))) :=
  Z.volumeTensorPath_ae k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)
    (continuousInverse_contDiff D X Y hX hXY hYjoint) t


-- @@ L686-696 verbatim
theorem tensorPath_norm_le (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    ‖tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t‖ ≤
      ((n.factorial : ℝ)*(finiteOrderConstant C R n)^n)*∑ i : Fin (n+1),
        frequencyFactor k m^i.val*(4 : ℝ)^i.val*Real.sqrt (2/P+2*P)*‖Z.realization (i.val+1) t‖ :=
  Z.volumeTensorPath_norm_le k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)
    (continuousInverse_contDiff D X Y hX hXY hYjoint) t


-- @@ L698-698 verbatim
end EulerPacketSourceVolumeSobolev


-- @@ L700-700 verbatim
end

-- @@ L701-701 verbatim
end


-- @@ L703-703 verbatim
end


-- @@ L705-705 verbatim
section


-- @@ L707-709 verbatim
/-! Actual Eulerian reconstructions have every spatial derivative in L²,
continuously in time. Sobolev embedding also supplies bounded smooth
coefficient paths for the velocity and pressure force. -/


-- @@ L711-711 verbatim
section


-- @@ L713-715 verbatim
/-! Reconstruction W=κFz is a genuine all-order field tower. Its graph
restriction and its actual inverse-flow pullback are continuous spatial L²
paths, with no independent integrability assumption on the perturbation. -/


-- @@ L717-717 verbatim
@[expose] public section


-- @@ L719-719 verbatim
noncomputable section


-- @@ L721-721 verbatim
namespace EulerPacketPhysicalField


-- @@ L723-725 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerAllOrderCorrectionData EulerPacketCorrectionCoefficients
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerFlowL2Transport


-- @@ L727-729 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (κ : ℝ) (Z : FieldTower P D.T)


-- @@ L731-734 verbatim
/-- Reconstructed tower, given by `(Z.multiply ((frameCoefficient D).toCoefficientTower P)).smul
κ`. -/
def reconstructedTower : FieldTower P D.T :=
  (Z.multiply ((frameCoefficient D).toCoefficientTower P)).smul κ


-- @@ L736-740 verbatim
theorem reconstructedTower_pointField (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (reconstructedTower D P κ Z).pointField t x =
      κ • D.F.field t x.1 (Z.pointField t x) := by
  rw [reconstructedTower,FieldTower.smul_pointField,FieldTower.multiply_pointField]
  rfl


-- @@ L742-746 verbatim
/-- Graph path, given by `(reconstructedTower D P κ Z).canonicalGraphWordPath (physicalPhase P k
D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0`. -/
def graphPath (k : ℝ) : C(Icc (0 : ℝ) D.T,Lp Space 2 (volume : Measure Space)) :=
  (reconstructedTower D P κ Z).canonicalGraphWordPath
    (physicalPhase P k D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0


-- @@ L748-754 verbatim
theorem graphPath_ae (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    (graphPath D P κ Z k t : Space → Space) =ᵐ[volume]
      fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x)) := by
  have h := (reconstructedTower D P κ Z).canonicalGraphWordPath_ae
    (physicalPhase P k D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0 t
  simpa only [graphPath,EulerCylinderSobolev.iteratedFieldDerivative_zero,
    reconstructedTower_pointField,physicalPhase,cylinderGraph] using h


-- @@ L756-759 verbatim
/-- Graph tensor path, given by `(reconstructedTower D P κ Z).physicalTensorPath k D.m₀ n`. -/
def graphTensorPath (k : ℝ) (n : ℕ) :
    C(Icc (0 : ℝ) D.T,Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)) :=
  (reconstructedTower D P κ Z).physicalTensorPath k D.m₀ n


-- @@ L761-770 verbatim
theorem graphTensorPath_ae (k : ℝ) (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (graphTensorPath D P κ Z k n t : Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n
        (fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x))) := by
  have h := (reconstructedTower D P κ Z).physicalTensorPath_ae k D.m₀ n t
  have he : (reconstructedTower D P κ Z).physicalPointField k D.m₀ t =
      fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x)) :=
    funext (fun x => reconstructedTower_pointField D P κ Z t (cylinderGraph P k D.m₀ x))
  rw [he] at h
  exact h


-- @@ L772-777 verbatim
variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (D.F.field t x).det = 1)


-- @@ L779-782 verbatim
/-- Eulerian path, given by `transportPath X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet
(graphPath D P κ Z k)`. -/
def eulerianPath (k : ℝ) : C(Icc (0 : ℝ) D.T,Lp Space 2 (volume : Measure Space)) :=
  transportPath X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet (graphPath D P κ Z k)


-- @@ L784-789 verbatim
theorem eulerianPath_ae (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    (eulerianPath D P κ Z X Y hX hYX hXY hY hdet k t : Space → Space) =ᵐ[volume]
      fun x => κ • D.F.field t (Y t x)
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  transportPath_ae X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet
    (graphPath D P κ Z k) _ (graphPath_ae D P κ Z k) t


-- @@ L791-793 verbatim
theorem eulerianPath_norm (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    ‖eulerianPath D P κ Z X Y hX hYX hXY hY hdet k t‖ = ‖graphPath D P κ Z k t‖ :=
  transportPath_norm X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet (graphPath D P κ Z k) t


-- @@ L795-795 verbatim
end EulerPacketPhysicalField


-- @@ L797-797 verbatim
end

-- @@ L798-798 verbatim
end


-- @@ L800-800 verbatim
end


-- @@ L802-802 verbatim
section


-- @@ L804-806 verbatim
/-! The actual source-flow pullback is a smooth spatial L² field at
every time. Its tensor paths also give a bounded smooth coefficient
path, with continuity in the uniform norm at every spatial order. -/


-- @@ L808-808 verbatim
@[expose] public section


-- @@ L810-810 verbatim
noncomputable section


-- @@ L812-812 verbatim
namespace EulerPacketSourceVolumeSobolev


-- @@ L814-817 verbatim
open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerFlowL2Transport EulerPacketInverseFlowGevrey EulerPacketPiola
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerGevrey
  EulerLpTranslation EulerMeanCoefficients

-- @@ L818-818 verbatim
open scoped ContDiff


-- @@ L820-831 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  (Z : FieldTower P D.T) (k : ℝ) (m : Space)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hYjoint : Continuous (Function.uncurry Y))
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)


-- @@ L833-840 verbatim
/-- Smooth field, bundling `field`, `smooth`, `integrable`. -/
def smoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space where
  field x := Z.pointField t (cylinderGraph P k m (Y t x))
  smooth := (Z.physicalPointField_smooth k m t).comp
    (continuousInverse_contDiff D X Y hX hXY hYjoint t)
  integrable n :=
    (Lp.memLp (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t)).ae_eq
      (tensorPath_ae D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t)


-- @@ L842-847 verbatim
theorem smoothField_jetLp (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF t).jetLp n =
      tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t := by
  apply Lp.ext
  exact (SmoothL2Field.jetLp_ae _ n).trans
    (tensorPath_ae D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t).symm


-- @@ L849-853 verbatim
theorem smoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t => (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF t).jetLp n)
        := by
  simp only [smoothField_jetLp]
  exact (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n).continuous


-- @@ L855-859 verbatim
/-- Smooth coefficient path, constructed using `EulerMeanSobolevBoundedField.coefficientPath`. -/
def smoothCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerMeanSobolevBoundedField.coefficientPath
    (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF)
    (smoothField_jetLp_continuous D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF)


-- @@ L861-864 verbatim
theorem smoothCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (smoothCoefficientPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF).field t x =
      Z.pointField t (cylinderGraph P k m (Y t x)) :=
  EulerMeanSobolevBoundedField.coefficientPath_apply _ _ t x


-- @@ L866-866 verbatim
end EulerPacketSourceVolumeSobolev


-- @@ L868-868 verbatim
end

-- @@ L869-869 verbatim
end


-- @@ L871-871 verbatim
end


-- @@ L873-873 verbatim
@[expose] public section


-- @@ L875-875 verbatim
noncomputable section


-- @@ L877-877 verbatim
namespace EulerPacketPhysicalField


-- @@ L879-881 verbatim
open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerPacketCorrectionCoefficients EulerGraphPressurePotential EulerGevrey
  EulerLpTranslation EulerMeanCoefficients EulerPacketPiola


-- @@ L883-885 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (κ : ℝ) (Z : FieldTower P D.T)


-- @@ L887-890 verbatim
/-- Pressure force tower, given by `(Z.multiply ((inverseCoefficient
D).adjoint.toCoefficientTower P)).smul κ`. -/
def pressureForceTower : FieldTower P D.T :=
  (Z.multiply ((inverseCoefficient D).adjoint.toCoefficientTower P)).smul κ


-- @@ L892-897 verbatim
theorem pressureForceTower_pointField (t : Icc (0 : ℝ) D.T)
    (x : EulerLiftedGradientSpace.LiftDomain P) :
    (pressureForceTower D P κ Z).pointField t x =
      κ • (D.FInv.field t x.1).adjoint (Z.pointField t x) := by
  rw [pressureForceTower, FieldTower.smul_pointField, FieldTower.multiply_pointField]
  rfl


-- @@ L899-907 verbatim
variable (k : ℝ) (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)


-- @@ L909-913 verbatim
/-- Eulerian smooth field, given by `EulerPacketSourceVolumeSobolev.smoothField D
(reconstructedTower D P κ Z) k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF t`. -/
def eulerianSmoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space :=
  EulerPacketSourceVolumeSobolev.smoothField D (reconstructedTower D P κ Z) k D.m₀
    X Y hX hYX hXY hY R C hR hC hdet hF t


-- @@ L915-918 verbatim
theorem eulerianSmoothField_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (eulerianSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).field x =
      κ • D.F.field t (Y t x) (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  reconstructedTower_pointField D P κ Z t (cylinderGraph P k D.m₀ (Y t x))


-- @@ L920-924 verbatim
theorem eulerianSmoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t =>
      (eulerianSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).jetLp n) :=
  EulerPacketSourceVolumeSobolev.smoothField_jetLp_continuous D (reconstructedTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF n


-- @@ L926-930 verbatim
/-- Eulerian coefficient path, given by `EulerPacketSourceVolumeSobolev.smoothCoefficientPath D
(reconstructedTower D P κ Z) k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF`. -/
def eulerianCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerPacketSourceVolumeSobolev.smoothCoefficientPath D (reconstructedTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF


-- @@ L932-937 verbatim
theorem eulerianCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (eulerianCoefficientPath D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF).field t x =
      κ • D.F.field t (Y t x) (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) := by
  rw [eulerianCoefficientPath, EulerPacketSourceVolumeSobolev.smoothCoefficientPath_apply,
    reconstructedTower_pointField]
  rfl


-- @@ L939-943 verbatim
/-- Pressure force smooth field, given by `EulerPacketSourceVolumeSobolev.smoothField D
(pressureForceTower D P κ Z) k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF t`. -/
def pressureForceSmoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space :=
  EulerPacketSourceVolumeSobolev.smoothField D (pressureForceTower D P κ Z) k D.m₀
    X Y hX hYX hXY hY R C hR hC hdet hF t


-- @@ L945-949 verbatim
theorem pressureForceSmoothField_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (pressureForceSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).field x =
      κ • (D.FInv.field t (Y t x)).adjoint
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  pressureForceTower_pointField D P κ Z t (cylinderGraph P k D.m₀ (Y t x))


-- @@ L951-955 verbatim
theorem pressureForceSmoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t =>
      (pressureForceSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).jetLp n) :=
  EulerPacketSourceVolumeSobolev.smoothField_jetLp_continuous D (pressureForceTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF n


-- @@ L957-962 verbatim
/-- Pressure force coefficient path, given by
`EulerPacketSourceVolumeSobolev.smoothCoefficientPath D (pressureForceTower D P κ Z) k D.m₀
X Y hX hYX hXY hY R C hR hC hdet hF`. -/
def pressureForceCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerPacketSourceVolumeSobolev.smoothCoefficientPath D (pressureForceTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF


-- @@ L964-970 verbatim
theorem pressureForceCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (pressureForceCoefficientPath D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF).field t x =
      κ • (D.FInv.field t (Y t x)).adjoint
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) := by
  rw [pressureForceCoefficientPath, EulerPacketSourceVolumeSobolev.smoothCoefficientPath_apply,
    pressureForceTower_pointField]
  rfl


-- @@ L972-972 verbatim
end EulerPacketPhysicalField


-- @@ L974-974 verbatim
end

-- @@ L975-975 verbatim
end


-- @@ L977-977 verbatim
end


-- @@ L979-979 verbatim
section


-- @@ L981-983 verbatim
/-! Actual odd parent fields supply the parity data for both initialized
packet branches. The resulting corrected coefficient, and hence the
actual next particle map, retain oddness without a new symmetry premise. -/


-- @@ L985-985 verbatim
section


-- @@ L987-989 verbatim
/-! The actual corrected lifted velocity is odd when its prescribed
correction data have the checked parity. Passing from L² symmetry to
the canonical point field supplies symmetry of the real flow coefficient. -/


-- @@ L991-991 verbatim
@[expose] public section


-- @@ L993-993 verbatim
noncomputable section


-- @@ L995-995 verbatim
namespace EulerAllOrderCorrectionData.FieldTower


-- @@ L997-997 verbatim
open Set EulerLiftedGradientSpace EulerCylinderReflection EulerCorrectionAssembly


-- @@ L999-999 verbatim
variable {P T : ℝ} [Fact (0 < P)] (A : FieldTower P T)


-- @@ L1001-1005 verbatim
theorem pointField_odd
    (ho : ∀ t, -reflection P (A.field t) = A.field t) (t : Icc (0 : ℝ) T) :
    Function.Odd (A.pointField t) :=
  continuous_representative_odd P (A.field t) (A.pointField t) (ho t)
    (Continuous.uncurry_left t A.pointField_joint_continuous) (A.pointField_ae t)


-- @@ L1007-1007 verbatim
end EulerAllOrderCorrectionData.FieldTower


-- @@ L1009-1009 verbatim
namespace EulerAllOrderDriftCorrection


-- @@ L1011-1013 verbatim
open Set EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerCylinderReflection
  EulerCorrectionAssembly EulerPacketCylinderField EulerPacketProfileRecursion
  EulerMetricTransport EulerLiftedSmoothTimeField


-- @@ L1015-1016 verbatim
variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A)


-- @@ L1018-1022 verbatim
theorem Budget.correctedFieldTower_odd (E : ParityData P A) (t : Icc (0 : ℝ) T) :
    -reflection P ((B.correctedFieldTower P).field t)=(B.correctedFieldTower P).field t := by
  change -reflection P (A.approximation.field t+B.commonPath P t) =
    A.approximation.field t+B.commonPath P t
  rw [map_add,neg_add,E.approximation,B.commonPath_odd P E]


-- @@ L1024-1034 verbatim
theorem Budget.liftedPacketCoefficient_odd {raw : VectorField}
    (G : Field P T raw) (hG : A.approximation = G.toFieldTower)
    (E : ParityData P A) (t : Icc (0 : ℝ) T) :
    Function.Odd ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) := by
  intro z
  rw [B.liftedPacketCoefficient_eq_corrected P G hG,
    B.liftedPacketCoefficient_eq_corrected P G hG]
  have hc : coveringMap P (-z) = -coveringMap P z := by
    simp only [coveringMap,Prod.fst_neg,Prod.snd_neg,AddCircle.coe_neg,Prod.neg_mk]
  rw [hc,(B.correctedFieldTower P).pointField_odd (B.correctedFieldTower_odd P E) t]
  exact (EulerLiftedTransportTrace.transportLinear A.κ A.direction).map_neg _


-- @@ L1036-1036 verbatim
end EulerAllOrderDriftCorrection


-- @@ L1038-1038 verbatim
end

-- @@ L1039-1039 verbatim
end


-- @@ L1041-1041 verbatim
end


-- @@ L1043-1043 verbatim
@[expose] public section


-- @@ L1045-1045 verbatim
noncomputable section


-- @@ L1047-1047 verbatim
namespace EulerParentPacketFrames.OddData


-- @@ L1049-1052 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerPacketTerminalDatum
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCorrectionAssembly
  EulerTimeIntervalRestriction EulerGraphInvariantFlow EulerAllOrderCorrectionData
  EulerAllOrderDriftCorrection


-- @@ L1054-1058 verbatim
variable {A : Parent} (O : OddData A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ S) (α : ℝ)


-- @@ L1060-1060 verbatim
include O hSym


-- @@ L1062-1068 verbatim
theorem forwardCorrectionParity (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    ParityData period
      (forwardInitializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS) rfl
        δ hδ ξ hs α (A.sourceAgreement m hm R S hS H) N hN k hk) :=
  forwardInitializedCorrectionParityData (A.meanData H) (A.transverseData m hm R S hS) rfl
    δ hδ ξ hs α (O.meanEvenData H) hSym O.frame_even O.strain_even
    (A.sourceAgreement m hm R S hS H) N hN k hk


-- @@ L1070-1081 verbatim
theorem joinedCorrectionParity (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
    (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k) :
    ParityData period
      (initializedCorrectionData (A.meanData H) (A.transverseData m hm R S hS) rfl
        τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α
        (A.sourceAgreement m hm R S hS H) N hN k hk) := by
  apply initializedCorrectionParityData (A.meanData H) (A.transverseData m hm R S hS) rfl
    τ hτ hτT (A.historyOn H m hm R S hS τ hτ hτT) δ hδ ξ hs α
    (O.meanEvenData H) hSym O.frame_even O.strain_even
    _ (A.sourceAgreement m hm R S hS H) N hN k hk
  intro t x
  exact O.curvature_even (initialInclusion A.T τ hτT.le t) x


-- @@ L1083-1094 verbatim
omit hSym [CompleteSpace U] in
theorem childOfPacket {P : ℝ} [Fact (0 < P)] {C : EulerAllOrderCorrectionData.Data P A.T}
    (B : Budget P A.T_pos C) (E : ParityData P C)
    {raw : VectorField} (V : Field P A.T raw) (hV : C.approximation = V.toFieldTower)
    (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
    (k : ℝ) (hgraph : ∀ t z, graphConstraint k C.direction (G.A.field t z) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1) :
    OddData (A.child G k C.direction hgraph nextEll hnext hnext1) := by
  apply O.child G _ k C.direction hgraph nextEll hnext hnext1
  intro t
  rw [hG]
  exact B.liftedPacketCoefficient_odd P V hV E t


-- @@ L1096-1096 verbatim
end EulerParentPacketFrames.OddData


-- @@ L1098-1098 verbatim
end

-- @@ L1099-1099 verbatim
end


-- @@ L1101-1101 verbatim
end


-- @@ L1103-1103 verbatim
section


-- @@ L1105-1107 verbatim
/-! Actual physical L² fields of a packet over a parent. The genuine
inverse and the proved parent label bound supply all reconstruction
regularity, and the physical spatial scale is retained exactly. -/


-- @@ L1109-1109 verbatim
@[expose] public section


-- @@ L1111-1111 verbatim
noncomputable section


-- @@ L1113-1113 verbatim
namespace EulerParentPacketFrames


-- @@ L1115-1117 verbatim
open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPacketPhysicalField EulerAllOrderCorrectionData EulerPacketParentLabelBounds
  EulerTransverseFrameCoordinates EulerGraphPressurePotential


-- @@ L1119-1119 verbatim
namespace ParticleInverse


-- @@ L1121-1121 verbatim
variable {A : Parent} (I : ParticleInverse A)


-- @@ L1123-1126 verbatim
theorem normalized_scaled (t : Icc (0 : ℝ) A.T) (x : Space) :
    I.normalized t (A.ell⁻¹ • x)=A.ell⁻¹ • I.field t x := by
  simp only [normalized,Parent.packetInverse,projIcc_of_mem A.T_pos.le t.property,
    smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]


-- @@ L1128-1128 verbatim
end ParticleInverse


-- @@ L1130-1130 verbatim
namespace LabelData


-- @@ L1132-1136 verbatim
variable {A : Parent} (L : LabelData A) (I : ParticleInverse A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  (P : ℝ) [Fact (0 < P)] (κ : ℝ) (Z : FieldTower P A.T) (k : ℝ)


-- @@ L1138-1145 verbatim
/-- Packet velocity field, constructed using `scaleField`. -/
def packetVelocityField (t : Icc (0 : ℝ) A.T) : SmoothL2Field Space :=
  scaleField A.ell A.ell_pos
    (eulerianSmoothField (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound t)


-- @@ L1147-1154 verbatim
/-- Packet force field, constructed using `scaleField`. -/
def packetForceField (t : Icc (0 : ℝ) A.T) : SmoothL2Field Space :=
  scaleField A.ell A.ell_pos
    (pressureForceSmoothField (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound t)


-- @@ L1156-1162 verbatim
theorem packetVelocityField_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    (L.packetVelocityField I m hm J support hSupport P κ Z k t).field x =
      A.ell • (κ • A.frame.field t (A.ell⁻¹ • I.field t x)
        (Z.pointField t (cylinderGraph P k m (A.ell⁻¹ • I.field t x)))) := by
  rw [packetVelocityField,scaleField_apply]
  erw [eulerianSmoothField_apply,I.normalized_scaled]
  rfl


-- @@ L1164-1170 verbatim
theorem packetForceField_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    (L.packetForceField I m hm J support hSupport P κ Z k t).field x =
      A.ell • (κ • (A.inverse.field t (A.ell⁻¹ • I.field t x)).adjoint
        (Z.pointField t (cylinderGraph P k m (A.ell⁻¹ • I.field t x)))) := by
  rw [packetForceField,scaleField_apply]
  erw [pressureForceSmoothField_apply,I.normalized_scaled]
  rfl


-- @@ L1172-1179 verbatim
theorem packetVelocityField_continuous (n : ℕ) :
    Continuous (fun t => (L.packetVelocityField I m hm J support hSupport P κ Z k t).jetLp n) :=
  continuous_jetLp_scaleField A.ell A.ell_pos A.ell_le_one _
    (eulerianSmoothField_jetLp_continuous (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound) n


-- @@ L1181-1188 verbatim
theorem packetForceField_continuous (n : ℕ) :
    Continuous (fun t => (L.packetForceField I m hm J support hSupport P κ Z k t).jetLp n) :=
  continuous_jetLp_scaleField A.ell A.ell_pos A.ell_le_one _
    (pressureForceSmoothField_jetLp_continuous (A.transverseData m hm J support hSupport) P κ Z k
      (fun s x => A.packetPosition (s,x)) I.normalized A.packetPosition_spatial
      I.normalized_left I.normalized_right I.normalized_continuous
      L.scaledRadius (frameAmplitude L.K) L.scaledRadius_nonneg (frameAmplitude_nonneg L.K)
      A.frame_det L.frame_scaled_bound) n


-- @@ L1190-1190 verbatim
end LabelData

-- @@ L1191-1191 verbatim
end EulerParentPacketFrames


-- @@ L1193-1193 verbatim
end

-- @@ L1194-1194 verbatim
end


-- @@ L1196-1196 verbatim
end


-- @@ L1198-1198 verbatim
section


-- @@ L1200-1202 verbatim
/-! The constructed child Euler evolution remains in the actual
all-order spatial Sobolev class. Its fields are the parent fields plus
the very same exact packet used in the particle-map construction. -/


-- @@ L1204-1204 verbatim
@[expose] public section


-- @@ L1206-1206 verbatim
noncomputable section


-- @@ L1208-1208 verbatim
namespace EulerParentPacketFrames.SobolevData


-- @@ L1210-1212 verbatim
open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerLpTranslation EulerLpTranslation.SmoothL2Field


-- @@ L1214-1227 verbatim
variable {A : Parent} {E : Evolution A} (F : SobolevData E) (L : LabelData A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)


-- @@ L1229-1255 verbatim
/-- Child, bundling `velocity`, `force`, `velocity_match`, `force_match` and the required
compatibility proofs. -/
def child : SobolevData
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1) where
  velocity t := addField (F.velocity t)
    (L.packetVelocityField E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).velocity k t)
  force t := addField (F.force t)
    (L.packetForceField E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).pressure k t)
  velocity_match t x := by
    erw [Evolution.child_velocity,A.exactPacketVelocity_eq_corrected]
    erw [addField_field,L.packetVelocityField_apply]
    change E.velocity (t,x)+_=(F.velocity t).field x+_
    erw [F.velocity_match]
    rfl
  force_match t x := by
    erw [Evolution.child_force]
    erw [Parent.exactPacketForce,addField_field,F.force_match,L.packetForceField_apply]
    simp only [ExactLiftedPacket.graphPressure,map_smul]
    rfl
  velocity_continuous := continuous_jetLp_addField _ _ F.velocity_continuous
    (L.packetVelocityField_continuous E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).velocity k)
  force_continuous := continuous_jetLp_addField _ _ F.force_continuous
    (L.packetForceField_continuous E.inverse m hm J support hSupport P κ
      (exactPacketOfResidual P B residual).pressure k)


-- @@ L1257-1257 verbatim
end EulerParentPacketFrames.SobolevData


-- @@ L1259-1259 verbatim
end

-- @@ L1260-1260 verbatim
end


-- @@ L1262-1262 verbatim
end


-- @@ L1264-1264 verbatim
@[expose] public section


-- @@ L1266-1266 verbatim
noncomputable section


-- @@ L1268-1268 verbatim
namespace EulerParentPacketFrames


-- @@ L1270-1272 verbatim
open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerCorrectionAssembly


-- @@ L1274-1282 verbatim
/-- Smooth state data, collecting `evolution`, `regularity`, `labels`, `odd`. -/
structure SmoothState (A : Parent) where
  /-- Evolution of `SmoothState`, of type `Evolution A`. -/
  evolution : Evolution A
  /-- Regularity of `SmoothState`, of type `SobolevData evolution`. -/
  regularity : SobolevData evolution
  /-- Label type of `SmoothState`, of type `LabelData A`. -/
  labels : LabelData A
  odd : OddData A


-- @@ L1284-1284 verbatim
namespace SmoothState


-- @@ L1286-1286 verbatim
variable {A : Parent} (S : SmoothState A)


-- @@ L1288-1294 verbatim
/-- Restrict time, bundling `evolution`, `regularity`, `labels`, `odd`. -/
def restrictTime (T : ℝ) (hT : 0 < T) (hTA : T ≤ A.T) :
    SmoothState (A.restrictTime T hT hTA) where
  evolution := S.evolution.restrictTime T hT hTA
  regularity := S.regularity.restrictTime T hT hTA
  labels := S.labels.restrictTime T hT hTA
  odd := S.odd.restrictTime T hT hTA


-- @@ L1296-1309 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z = V.toFieldTower)
  (symmetry : ParityData P (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)


-- @@ L1311-1319 verbatim
/-- Packet child, bundling `evolution`, `regularity`, `labels`, `odd`. -/
def packetChild (labels : LabelData (A.child G k m hgraph nextEll hnext hnext1)) :
    SmoothState (A.child G k m hgraph nextEll hnext hnext1) where
  evolution := S.evolution.child m hm J support hSupport B residual V hV G hG k hk hgraph
    nextEll hnext hnext1
  regularity := S.regularity.child S.labels m hm J support hSupport B residual V hV G hG k hk hgraph
    nextEll hnext hnext1
  labels := labels
  odd := S.odd.childOfPacket B symmetry V hV G hG k hgraph nextEll hnext hnext1


-- @@ L1321-1321 verbatim
end SmoothState

-- @@ L1322-1322 verbatim
end EulerParentPacketFrames
