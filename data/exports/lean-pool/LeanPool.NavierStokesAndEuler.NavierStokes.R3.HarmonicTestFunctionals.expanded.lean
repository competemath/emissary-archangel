/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierSobolevWeights
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SchwartzCompactApproximation
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactSchwartz
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff


-- @@ L21-28 verbatim
/-!
# Harmonic functionals bounded in an inhomogeneous Fourier Sobolev norm

A complex-linear Schwartz functional bounded by the Fourier `H³` norm is
represented in polynomially weighted `L²`. If it annihilates Laplacians, its
representing function vanishes away from the origin. Since volume has no atom
at the origin, the whole functional vanishes.
-/


-- @@ L30-30 verbatim
section


-- @@ L32-39 verbatim
/-!
# Weak uniqueness for the weighted Fourier representation

Compact smooth functions are Schwartz functions, so a locally integrable
function annihilating every Schwartz test vanishes almost everywhere. Applied
to the weighted conjugate of an `L²` function, this removes the Fourier
Laplacian multiplier away from its single zero at the origin.
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
noncomputable section


-- @@ L45-45 verbatim
open Set MeasureTheory

-- @@ L46-46 verbatim
open scoped ContDiff ENNReal


-- @@ L48-48 verbatim
namespace NavierStokesR3.WeakFourierUniqueness


-- @@ L50-50 verbatim
open ProblemStatement


-- @@ L52-65 verbatim
/-- The real-test fundamental lemma, with multiplication written in `ℂ`. -/
theorem ae_eq_zero_of_integral_real_test_mul_eq_zero
    (h : Space → ℂ) (hh : LocallyIntegrable h (volume : Measure Space))
    (hzero : ∀ g : Space → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      (∫ x : Space, (g x : ℂ) * h x) = 0) :
    h =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hh
  intro g hg hs
  have hsmul : (fun x : Space => g x • h x) =
      (fun x : Space => (g x : ℂ) * h x) := by
    funext x
    apply Complex.ext <;> simp
  rw [hsmul]
  exact hzero g hg hs


-- @@ L67-81 verbatim
/-- A locally integrable function is determined by its Schwartz pairings. -/
theorem ae_eq_zero_of_integral_schwartz_test_mul_eq_zero
    (h : Space → ℂ) (hh : LocallyIntegrable h (volume : Measure Space))
    (hzero : ∀ ψ : Comparison.ComplexTest, (∫ x : Space, h x * ψ x) = 0) :
    h =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_real_test_mul_eq_zero h hh
  intro g hg hs
  have hgC : ContDiff ℝ ∞ (fun x : Space => (g x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  have hsC : HasCompactSupport (fun x : Space => (g x : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have htest :=
    hzero (CompactSchwartz.ofCompactSupport (fun x : Space => (g x : ℂ)) hgC hsC)
  change (∫ x : Space, h x * (g x : ℂ)) = 0 at htest
  simpa only [mul_comm] using htest


-- @@ L83-99 verbatim
/-- Polynomial weights preserve the local integrability of an `L²` function. -/
theorem locallyIntegrable_weighted_star (q : Lp ℂ 2 (volume : Measure Space)) :
    LocallyIntegrable (fun ξ : Space =>
      star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ))
      (volume : Measure Space) := by
  have hqstar : LocallyIntegrable (fun ξ : Space => star (q ξ))
      (volume : Measure Space) :=
    (Complex.conjCLE.toContinuousLinearMap.comp_memLp q).locallyIntegrable (by norm_num)
  have hw : Continuous (fun ξ : Space => (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp
      ((continuous_const.add (continuous_norm.pow 2)).pow 2)
  have hn : Continuous (fun ξ : Space => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp (continuous_norm.pow 2)
  exact locallyIntegrableOn_univ.mp
    (((hqstar.locallyIntegrableOn univ).mul_continuousOn hw.continuousOn
      isClosed_univ.isLocallyClosed).mul_continuousOn hn.continuousOn
      isClosed_univ.isLocallyClosed)


-- @@ L101-128 verbatim
/-- If the weighted Fourier Laplacian pairings of an `L²` function vanish,
the function is zero in `L²`. No regularity beyond membership in `L²` is used. -/
theorem eq_zero_of_integral_weight_normSq_test_eq_zero
    (q : Lp ℂ 2 (volume : Measure Space))
    (hq : ∀ ψ : Comparison.ComplexTest,
      (∫ ξ : Space, star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) * ψ ξ) = 0) :
    q = 0 := by
  have hz : (fun ξ : Space =>
      star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ))
      =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_schwartz_test_mul_eq_zero _
      (locallyIntegrable_weighted_star q) hq
  have hne : ∀ᵐ ξ : Space ∂volume, ξ ≠ 0 := by
    simp [ae_iff]
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz, hne] with ξ hξ hξne
  have hwR : (1 + ‖ξ‖ ^ 2) ^ 2 ≠ (0 : ℝ) :=
    pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)))
  have hw : (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hwR
  have hnR : ‖ξ‖ ^ 2 ≠ (0 : ℝ) :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hξne)
  have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hnR
  have hs : star (q ξ) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hξ).resolve_right hn)).resolve_right hw
  simpa only [star_star, star_zero, Pi.zero_apply] using congrArg star hs


-- @@ L130-130 verbatim
end NavierStokesR3.WeakFourierUniqueness


-- @@ L132-132 verbatim
end

-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
end


-- @@ L137-137 verbatim
section


-- @@ L139-145 verbatim
/-!
# Hilbert-space representation of a functional bounded through an embedding

A linear functional on a complex vector space that is bounded in the norm of an
injective linear map into a Hilbert space is represented by an inner product in
that Hilbert space. No topology on the source vector space is needed.
-/


-- @@ L147-147 verbatim
@[expose] public section


-- @@ L149-149 verbatim
namespace NavierStokesR3.HilbertFunctionalExtension


-- @@ L151-151 verbatim
universe u v


-- @@ L153-153 verbatim
variable {E : Type u} [AddCommGroup E] [Module ℂ E]

-- @@ L154-155 verbatim
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]


-- @@ L157-181 verbatim
/-- Transfer a functional to the range of an injective linear map, extend it by
Hahn–Banach, and represent the extension by the Hilbert-space inner product. -/
theorem exists_inner_representation (B : E →ₗ[ℂ] H)
    (hB : Function.Injective B) (F : E →ₗ[ℂ] ℂ) {C : ℝ}
    (hbound : ∀ x : E, ‖F x‖ ≤ C * ‖B x‖) :
    ∃ q : H, ∀ x : E, F x = @inner ℂ H _ q (B x) := by
  classical
  let e : E ≃ₗ[ℂ] LinearMap.range B := LinearEquiv.ofInjective B hB
  let f : LinearMap.range B →ₗ[ℂ] ℂ := F.comp e.symm.toLinearMap
  have he (z : LinearMap.range B) : B (e.symm z) = (z : H) := by
    change ((e (e.symm z) : LinearMap.range B) : H) = (z : H)
    rw [e.apply_symm_apply]
  have hf : ∀ z : LinearMap.range B, ‖f z‖ ≤ C * ‖z‖ := by
    intro z
    change ‖F (e.symm z)‖ ≤ C * ‖(z : H)‖
    simpa only [he] using hbound (e.symm z)
  let fc : LinearMap.range B →L[ℂ] ℂ := f.mkContinuous C hf
  obtain ⟨G, hG, _⟩ := exists_extension_norm_eq (LinearMap.range B) fc
  refine ⟨(InnerProductSpace.toDual ℂ H).symm G, ?_⟩
  intro x
  rw [InnerProductSpace.toDual_symm_apply]
  calc
    F x = fc (e x) := by simp [fc, f]
    _ = G ((e x : LinearMap.range B) : H) := (hG (e x)).symm
    _ = G (B x) := rfl


-- @@ L183-183 verbatim
end NavierStokesR3.HilbertFunctionalExtension


-- @@ L185-185 verbatim
end


-- @@ L187-187 verbatim
end


-- @@ L189-189 verbatim
@[expose] public section


-- @@ L191-191 verbatim
noncomputable section


-- @@ L193-193 verbatim
open MeasureTheory


-- @@ L195-195 verbatim
namespace NavierStokesR3.HarmonicTestFunctionals


-- @@ L197-197 verbatim
open ProblemStatement Comparison


-- @@ L199-200 verbatim
/-- Frequency L²: an abbreviation for `Lp ℂ 2 (volume : Measure Space)`. -/
abbrev FrequencyL2 := Lp ℂ 2 (volume : Measure Space)


-- @@ L202-213 verbatim
/-- The `H³` bound supplies a Hilbert-space representative after a polynomial
Fourier embedding. No Fourier transform of arbitrary `L²` functions is needed. -/
theorem exists_inner_representation_of_fourierHNormSq_bound
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ)) :
    ∃ q : FrequencyL2, ∀ ψ : ComplexTest,
      F ψ = @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B ψ) := by
  apply HilbertFunctionalExtension.exists_inner_representation
    FourierSobolevWeights.B FourierSobolevWeights.B_injective F
  · intro ψ
    exact (hbound ψ).trans (mul_le_mul_of_nonneg_left
      (FourierSobolevWeights.sqrt_fourierHNormSq_three_le_norm_B ψ) hC)


-- @@ L215-225 verbatim
/-- In particular, a functional with the stated Fourier bound is continuous
for the Schwartz topology. -/
theorem continuous_of_fourierHNormSq_bound
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ)) :
    Continuous F := by
  obtain ⟨q, hq⟩ := exists_inner_representation_of_fourierHNormSq_bound F hC hbound
  have hc : Continuous (fun ψ : ComplexTest =>
      @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B ψ)) :=
    continuous_const.inner FourierSobolevWeights.continuous_B
  exact hc.congr fun ψ => (hq ψ).symm


-- @@ L227-257 verbatim
/-- A weighted `L²` representative that annihilates ordinary Laplacians is zero. -/
theorem representative_eq_zero_of_harmonic
    (q : FrequencyL2)
    (hq : ∀ ψ : ComplexTest,
      @inner ℂ FrequencyL2 _ q (FourierSobolevWeights.B (laplacianCLM ψ)) = 0) :
    q = 0 := by
  apply WeakFourierUniqueness.eq_zero_of_integral_weight_normSq_test_eq_zero q
  intro φ
  obtain ⟨ψ, hψ⟩ := (FourierTransform.fourierCLE ℂ ComplexTest).surjective φ
  change EulerSobolev.schwartzFourier ψ = φ at hψ
  have hzero := hq ψ
  rw [FourierSobolevWeights.inner_B_eq_integral] at hzero
  let c : ℂ := -(4 * (Real.pi : ℂ) ^ 2)
  have hc : c ≠ 0 := by
    dsimp [c]
    apply neg_ne_zero.mpr
    apply mul_ne_zero (by norm_num)
    exact pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
  have hi : (fun ξ : Space => star (q ξ) *
      (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        EulerSobolev.schwartzFourier (laplacianCLM ψ) ξ) =
      (fun ξ : Space => c • (star (q ξ) *
        (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) * φ ξ)) := by
    funext ξ
    rw [fourier_laplacianCLM_apply, hψ]
    simp only [smul_eq_mul, c]
    ring
  rw [hi, integral_smul] at hzero
  change c * (∫ ξ : Space, star (q ξ) *
    (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ) * φ ξ) = 0 at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hc


-- @@ L259-271 verbatim
/-- A harmonic Schwartz functional bounded in Fourier `H⁻³` vanishes. -/
theorem eq_zero_of_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, F (laplacianCLM ψ) = 0) : F = 0 := by
  obtain ⟨q, hq⟩ := exists_inner_representation_of_fourierHNormSq_bound F hC hbound
  have hqzero : q = 0 := representative_eq_zero_of_harmonic q (fun ψ => by
    rw [← hq]
    exact hharmonic ψ)
  ext ψ
  change F ψ = 0
  rw [hq, hqzero]
  simp


-- @@ L273-286 verbatim
/-- The pressure-recovery form: harmonicity need only be known against compactly
supported tests. The Fourier bound supplies the continuity needed to pass to
all Schwartz tests. No pressure pairing outside compact support is assumed. -/
theorem eq_zero_of_compact_harmonic
    (F : ComplexTest →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ψ : ComplexTest, ‖F ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ))
    (hharmonic : ∀ ψ : ComplexTest, HasCompactSupport (ψ : Space → ℂ) →
      F (laplacianCLM ψ) = 0) : F = 0 := by
  apply eq_zero_of_harmonic F hC hbound
  intro ψ
  exact SchwartzCompactApproximation.continuous_zero_of_compactSupport
    (fun φ : ComplexTest => F (laplacianCLM φ))
    ((continuous_of_fourierHNormSq_bound F hC hbound).comp laplacianCLM.continuous)
    hharmonic ψ


-- @@ L288-288 verbatim
end NavierStokesR3.HarmonicTestFunctionals


-- @@ L290-290 verbatim
namespace NavierStokesR3.TemporalTestUniqueness


-- @@ L292-292 verbatim
open Set Filter

-- @@ L293-293 verbatim
open scoped Topology ContDiff


-- @@ L295-307 verbatim
/-- Continuity turns the distributional fundamental lemma into equality at
every time of the open interval. The tests are real, and values may be complex. -/
theorem eq_zero_on_open_of_tests {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ}
    (hf : ContinuousOn f U)
    (htest : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
      (∫ t : ℝ, a t • f t) = 0) :
    ∀ t ∈ U, f t = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrableOn hU.measurableSet) htest
  have hrestr : f =ᵐ[volume.restrict U] (fun _ => (0 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hU.measurableSet] with t ht htU
    exact ht htU
  exact Measure.eqOn_open_of_ae_eq hrestr hU hf continuousOn_const


-- @@ L309-309 verbatim
end NavierStokesR3.TemporalTestUniqueness
