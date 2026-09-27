/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedUniformCosts
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedParameterBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactShearError
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceUniformEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedRadiusPolynomial
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryProfileEnvelope
import LeanPool.NavierStokesAndEuler.Euler.PacketPressureScaleCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedProfiles
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSupport
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRemainder
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldPhysicalSobolev
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialFields
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalL2
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFrequencyBounds
import Mathlib.Algebra.Order.Star.Real
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteAssemblyBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteSumBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds


-- @@ L34-35 verbatim
/-! Genuine parent/geometry inputs for an initial increment. The high and
mean fields below are the actual solved profiles, not prescribed bounds. -/


-- @@ L37-37 verbatim
section


-- @@ L39-40 verbatim
/-! The high initial increment retains its small amplitude, while the
mean initial increment is O(k⁻²) without any oscillatory-graph loss. -/


-- @@ L42-42 verbatim
section


-- @@ L44-45 verbatim
/-! Initial high and mean estimates retain their distinct small factors.
The only truncation-dependent quantity is the already controlled tail base. -/


-- @@ L47-47 verbatim
@[expose] public section


-- @@ L49-49 verbatim
noncomputable section


-- @@ L51-51 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L53-53 verbatim
open Set Finset EulerPacketProfileRecursion EulerPacketPointJets EulerFiniteGrades


-- @@ L55-56 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d : ℕ} {R A γ : ℝ}


-- @@ L58-61 verbatim
theorem WordBound.normalize_amplitude (hG : G.WordBound q R (γ * A) d) (hγ : 0 < γ) :
    (G.smul γ⁻¹).WordBound q R A d := by
  have h := hG.smul γ⁻¹
  simpa only [abs_of_pos (inv_pos.mpr hγ),← mul_assoc,inv_mul_cancel₀ hγ.ne',one_mul] using h


-- @@ L63-70 verbatim
theorem WordBound.restore_amplitude (hG : (G.smul γ⁻¹).WordBound q R A d) (hγ : 0 < γ) :
    G.WordBound q R (γ*A) d := by
  have h := hG.smul γ
  rw [abs_of_pos hγ] at h
  apply h.ofRawEq G
  intro t x θ
  change raw (t,(x,θ)) = γ • (γ⁻¹ • raw (t,(x,θ)))
  rw [smul_smul,mul_inv_cancel₀ hγ.ne',one_smul]


-- @@ L72-97 verbatim
theorem wordBound_evaluate_low_high_scaled (N : ℕ) (hN : 1 ≤ N) (κ B C₁ C₂ γ : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hγ : 0 < γ) (hsmall : κ * B ≤ 1 / 2)
    (f : ℕ → VectorField) (H : ∀ i, Field P T (f i)) (q : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ (t : Icc (0 : ℝ) T) x θ, f 0 (t, (x, θ)) = 0)
    (hone : (H 1).WordBound q R (γ * C₁) 0) (htwo : (H 2).WordBound q R (γ * C₂) 0)
    (htail : ∀ n, 3 ≤ n → n ≤ N + 1 → (H n).WordBound q R (γ * B ^ (n + 1)) 0) :
    (evaluateFamily (N+1) κ f H).WordBound q R
      (γ*(κ*C₁+κ^2*C₂+2*B*(κ*B)^3)) 0 := by
  let J (i : ℕ) := (H i).smul γ⁻¹
  have h := wordBound_evaluate_low_high N hN κ B C₁ C₂ hκ hB hsmall
    (fun i => γ⁻¹ • f i) J q R hR
    (fun t x θ => by change γ⁻¹ • f 0 (t,(x,θ)) = 0; rw [hzero t x θ,smul_zero])
    (hone.normalize_amplitude hγ) (htwo.normalize_amplitude hγ)
    (fun n hn hNn => (htail n hn hNn).normalize_amplitude hγ)
  have hs := h.smul γ
  rw [abs_of_pos hγ] at hs
  apply hs.ofRawEq
  intro t x θ
  change (∑ i ∈ range (N+1+1), κ^i • f i (t,(x,θ))) =
    γ • (∑ i ∈ range (N+1+1), κ^i • (γ⁻¹ • f i (t,(x,θ))))
  rw [smul_sum]
  apply sum_congr rfl
  intro i _
  rw [smul_smul,smul_smul]
  congr 1
  field_simp


-- @@ L99-99 verbatim
end EulerPacketCylinderField.Field


-- @@ L101-101 verbatim
namespace EulerPacketInitial


-- @@ L103-105 verbatim
open Set Finset EulerSmoothLimit EulerPacketProfileRecursion EulerPacketPointJets
  EulerPacketCylinderField EulerPacketTimeProfile EulerPacketShiftArithmetic EulerFiniteGrades
  EulerPacketCoarseMajorant


-- @@ L107-112 verbatim
variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {N : ℕ}
  {a : ℕ → Profile} {support : Set Space}
  (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
  (S : Scales (Icc (0 : ℝ) T)) (R : ℝ)
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0) (t : Icc (0 : ℝ) T)


-- @@ L114-114 verbatim
include hG hR ha


-- @@ L116-153 verbatim
theorem highGrade_bound (n : ℕ) :
    (highGradeField G t n).WordBound 6 R (S.growth t*(3*S.H0^(2*n))) (highShift n) := by
  have hH := S.H0_pos.le
  have hγ := (S.growth_pos t).le
  have hf (i : ℕ) (hi : i ≤ N) :
      ((G i hi).high.freeze t).WordBound 6 R (S.growth t*S.H0^(2*i)) (highShift i) := by
    by_cases hi0 : i=0
    · subst i
      exact (Field.wordBound_of_zero _ (fun _ _ _ => by
          rw [ha]; rfl) 6 R (highShift 0)).mono_amplitude
        (zero_le_one.trans hR) (by positivity)
    · apply ((hG i hi (by omega)).high_freeze t).mono_amplitude (zero_le_one.trans hR)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ S.H0_one_le (by omega : 2*i-2 ≤ 2*i)) hγ
  have hc (i : ℕ) (hi : i ≤ N) :
      ((G i hi).corrector.freeze t).WordBound 6 R (S.growth t*S.H0^(2*i)) (highShift i) := by
    by_cases hi0 : i=0
    · subst i
      exact (Field.wordBound_of_zero _ (fun _ _ _ => by
          rw [ha]; rfl) 6 R (highShift 0)).mono_amplitude
        (zero_le_one.trans hR) (by positivity)
    · apply ((hG i hi (by omega)).corrector_freeze t).mono_amplitude (zero_le_one.trans hR)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ S.H0_one_le (by omega : 2*i-2 ≤ 2*i)) hγ
  have hf' := Field.wordBound_truncateFamily N _ (fun i hi => (G i hi).high.freeze t)
    6 R (fun i => S.growth t*S.H0^(2*i)) highShift (zero_le_one.trans hR)
    (fun i => mul_nonneg hγ (pow_nonneg hH _)) hf
  have hc' := Field.wordBound_truncateFamily N _ (fun i hi => (G i hi).corrector.freeze t)
    6 R (fun i => S.growth t*S.H0^(2*i)) highShift (zero_le_one.trans hR)
    (fun i => mul_nonneg hγ (pow_nonneg hH _)) hc
  cases n with
  | zero => exact (hf' 0).mono_amplitude (zero_le_one.trans hR) (by norm_num; linarith)
  | succ n =>
    have hh := (hc' n).mono_shift hR (mul_nonneg hγ (pow_nonneg hH _))
      (show highShift n ≤ highShift (n+1) by unfold highShift; omega)
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ S.H0_one_le (by
        omega : 2*n ≤ 2*(n+1))) hγ
    exact ((hf' (n+1)).add hh).mono_amplitude (zero_le_one.trans hR) (by
      have := mul_nonneg hγ (pow_nonneg hH (2*(n+1)))
      nlinarith)


-- @@ L155-170 verbatim
theorem meanGrade_bound (n : ℕ) :
    (meanGradeField G t n).WordBound 6 R (3*S.H0^(2*n)) (highShift n) := by
  apply Field.wordBound_truncateFamily N _ _ 6 R (fun i => 3*S.H0^(2*i)) highShift
    (zero_le_one.trans hR) (fun i => mul_nonneg (by norm_num) (pow_nonneg S.H0_pos.le _))
  intro i hi
  by_cases hi0 : i=0
  · subst i
    exact (Field.wordBound_of_zero _ (fun _ _ _ => by
        rw [ha]; rfl) 6 R (highShift 0)).mono_amplitude
      (zero_le_one.trans hR) (by norm_num)
  · have h := ((hG i hi (by omega)).mean_freeze t).mono_shift hR (S.mean_pos i t).le
      (show meanShift i ≤ highShift i by unfold meanShift highShift; omega)
    apply h.mono_amplitude (zero_le_one.trans hR)
    have hp := S.mean_le_coarse i t
    have hH := pow_nonneg S.H0_pos.le (2*i)
    nlinarith


-- @@ L172-194 verbatim
theorem high_bound (hN : 1 ≤ N) (C κ : ℝ) (hC : 1 ≤ C) (hκ : 0 ≤ κ)
    (hsmall : κ * tailBase R S.H0 C N ≤ 1 / 2) :
    (highField G t κ).WordBound 6 (4*R)
      (S.growth t*(κ*fixedVelocityGradeCost R S.H0 1+κ^2*fixedVelocityGradeCost R S.H0 2 +
        2*tailBase R S.H0 C N*(κ*tailBase R S.H0 C N)^3)) 0 := by
  apply Field.wordBound_evaluate_low_high_scaled N hN κ (tailBase R S.H0 C N)
    (fixedVelocityGradeCost R S.H0 1) (fixedVelocityGradeCost R S.H0 2) (S.growth t)
    hκ (tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N) (S.growth_pos t) hsmall
    _ _ 6 (4*R) (by linarith)
  · intro s x θ
    have hz : timeSlice t (a 0).high = 0 := by rw [ha]; rfl
    rw [highGrade,assemble_zero N _ _ hz]
    rfl
  · exact (((highGrade_bound G S R hG hR ha t 1).normalize_amplitude (S.growth_pos
      t)).fixed_velocity_grade
      (zero_le_one.trans hR) S.H0_pos.le).restore_amplitude (S.growth_pos t)
  · exact (((highGrade_bound G S R hG hR ha t 2).normalize_amplitude (S.growth_pos
      t)).fixed_velocity_grade
      (zero_le_one.trans hR) S.H0_pos.le).restore_amplitude (S.growth_pos t)
  · intro n _ hn
    exact (((highGrade_bound G S R hG hR ha t n).normalize_amplitude (S.growth_pos
        t)).coarse_velocity_grade
      hR S.H0_one_le C hC N hN (by omega)).restore_amplitude (S.growth_pos t)


-- @@ L196-211 verbatim
theorem mean_bound (hN : 1 ≤ N) (ha1 : (a 1).mean = 0) (C κ : ℝ) (hC : 1 ≤ C) (hκ : 0 ≤ κ)
    (hsmall : κ * tailBase R S.H0 C N ≤ 1 / 2) :
    (meanField G t κ).WordBound 6 (4*R)
      (κ^2*fixedVelocityGradeCost R S.H0 2 +
        2*tailBase R S.H0 C N*(κ*tailBase R S.H0 C N)^3) 0 := by
  have h := Field.wordBound_evaluate_low_high N hN κ (tailBase R S.H0 C N)
    0 (fixedVelocityGradeCost R S.H0 2) hκ
    (tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N) hsmall
    (meanGrade N t a) (meanGradeField G t) 6 (4*R) (by linarith)
    (by intro s x θ; simp only [meanGrade,truncate_of_le N 0 _ (Nat.zero_le N)]; rw [ha]; rfl)
    (Field.wordBound_of_zero _
      (by intro s x θ; simp only [meanGrade,truncate_of_le N 1 _ hN]; rw [ha1]; rfl) 6 (4*R) 0)
    ((meanGrade_bound G S R hG hR ha t 2).fixed_velocity_grade (zero_le_one.trans hR) S.H0_pos.le)
    (fun n _ hn => (meanGrade_bound G S R hG hR ha t n).coarse_velocity_grade
      hR S.H0_one_le C hC N hN (by omega))
  simpa only [meanField,mean,mul_zero,zero_add] using h


-- @@ L213-213 verbatim
end EulerPacketInitial


-- @@ L215-215 verbatim
end

-- @@ L216-216 verbatim
end


-- @@ L218-218 verbatim
end


-- @@ L220-220 verbatim
@[expose] public section


-- @@ L222-222 verbatim
noncomputable section


-- @@ L224-224 verbatim
namespace EulerPacketInitial


-- @@ L226-228 verbatim
open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketTimeProfile EulerPacketCoarseMajorant EulerPacketFiniteFrequency
  EulerPacketTailBound EulerPhysicalL2Scaling EulerCylinderPhysicalTensor EulerCylinderCoordinates


-- @@ L230-231 verbatim
/-- High cost, given by `fixedVelocityGradeCost R H 1+fixedVelocityGradeCost R H 2+1`. -/
def highCost (R H : ℝ) : ℝ := fixedVelocityGradeCost R H 1+fixedVelocityGradeCost R H 2+1

-- @@ L232-233 verbatim
/-- Mean cost, given by `fixedVelocityGradeCost R H 2+2`. -/
def meanCost (R H : ℝ) : ℝ := fixedVelocityGradeCost R H 2+2


-- @@ L235-239 verbatim
theorem highCost_nonneg (R H : ℝ) (hR : 0 ≤ R) : 0 ≤ highCost R H := by
  have h1 := fixedVelocityGradeCost_nonneg R H hR 1
  have h2 := fixedVelocityGradeCost_nonneg R H hR 2
  unfold highCost
  positivity


-- @@ L241-244 verbatim
theorem meanCost_nonneg (R H : ℝ) (hR : 0 ≤ R) : 0 ≤ meanCost R H := by
  have h2 := fixedVelocityGradeCost_nonneg R H hR 2
  unfold meanCost
  positivity


-- @@ L246-253 verbatim
variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {N : ℕ}
  {a : ℕ → Profile} {support : Set Space}
  (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
  (S : Scales (Icc (0 : ℝ) T)) (R : ℝ)
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0) (t : Icc (0 : ℝ) T)
  (hN : 1 ≤ N) (C k : ℝ) (hC : 1 ≤ C) (hk : 4 ≤ k)
  (hbase : tailBase R S.H0 C N ≤ k ^ (1 / 100 : ℝ))


-- @@ L255-255 verbatim
include hG hR ha hN hC hk hbase


-- @@ L257-274 verbatim
theorem high_frequency_bound :
    (highField G t k⁻¹).WordBound 6 (4*R) (S.growth t*highCost R S.H0) 0 := by
  have hk0 : 0 < k := by linarith
  have hB0 := tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N
  have hsmall : k⁻¹*tailBase R S.H0 C N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using grade_ratio_le_half k (tailBase R S.H0 C N) hk hbase
  have h := high_bound G S R hG hR ha t hN C k⁻¹ hC (inv_nonneg.mpr hk0.le) hsmall
  have h4 := fourth_power_le_frequency k _ (by linarith) hB0 hbase
  have hc1 := fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 1
  have hc2 := fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 2
  have hn := normalized_low_high_le k (tailBase R S.H0 C N)
    (fixedVelocityGradeCost R S.H0 1) (fixedVelocityGradeCost R S.H0 2) (by linarith) hc2 h4
  apply h.mono_amplitude (by linarith)
  apply mul_le_mul_of_nonneg_left _ (S.growth_pos t).le
  apply le_trans _ hn
  apply le_mul_of_one_le_left
  · positivity
  · linarith


-- @@ L276-285 verbatim
theorem mean_frequency_bound (ha1 : (a 1).mean = 0) :
    (meanField G t k⁻¹).WordBound 6 (4*R) (meanCost R S.H0/k^2) 0 := by
  have hk0 : 0 < k := by linarith
  have hB0 := tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N
  have hsmall : k⁻¹*tailBase R S.H0 C N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using grade_ratio_le_half k (tailBase R S.H0 C N) hk hbase
  have h := mean_bound G S R hG hR ha t hN ha1 C k⁻¹ hC (inv_nonneg.mpr hk0.le) hsmall
  have h4 := fourth_power_le_frequency k _ (by linarith) hB0 hbase
  exact h.mono_amplitude (by linarith)
    (remainder_low_high_le k _ (fixedVelocityGradeCost R S.H0 2) hk0 h4)


-- @@ L287-298 verbatim
theorem high_physical_bound (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (m : Space) (s : ℕ) :
    derivativeSum s (scale ell (fun x : Space => high N k⁻¹ t a (t,(x,k*inner ℝ m x)))) ≤
      (ell⁻¹)^s*k^s*S.growth t*(highCost R S.H0 *
        physicalDerivativeCost P (4*R) (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖m‖)) s) :=
            by
  have h := high_frequency_bound G S R hG hR ha t hN C k hC hk hbase
  have hs := h.scaled_graph_derivativeSum_le (by linarith)
    (mul_nonneg (S.growth_pos t).le (highCost_nonneg R S.H0 (zero_le_one.trans hR)))
    t ell hell hell1 k m (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖m‖)) k
    (by positivity) (by linarith) (frequencyFactor_le_linear k (by linarith) m) s
  exact hs.trans_eq (by ring)


-- @@ L300-315 verbatim
theorem mean_physical_bound (ha1 : (a 1).mean = 0) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (m : Space) (s : ℕ) :
    derivativeSum s (scale ell (fun x : Space => mean N k⁻¹ t a (t,(x,k*inner ℝ m x)))) ≤
      (ell⁻¹)^s/k^2*(meanCost R S.H0 *
        physicalDerivativeCost P (4*R) ‖coordinateEquiv.symm.toContinuousLinearMap‖ s) := by
  have h := mean_frequency_bound G S R hG hR ha t hN C k hC hk hbase ha1
  have hs := h.scaled_graph_derivativeSum_le (by linarith)
    (div_nonneg (meanCost_nonneg R S.H0 (zero_le_one.trans hR)) (sq_nonneg k))
    t ell hell hell1 0 m ‖coordinateEquiv.symm.toContinuousLinearMap‖ 1
    (norm_nonneg _) le_rfl (by simp [frequencyFactor]) s
  have he : (fun x : Space => mean N k⁻¹ t a (t,(x,k*inner ℝ m x))) =
      (fun x : Space => mean N k⁻¹ t a (t,(x,0*inner ℝ m x))) := by
    funext x
    rw [mean_angle G t k⁻¹ t x (k*inner ℝ m x),zero_mul]
  rw [he]
  exact hs.trans_eq (by rw [one_pow]; ring)


-- @@ L317-317 verbatim
end EulerPacketInitial


-- @@ L319-319 verbatim
end

-- @@ L320-320 verbatim
end


-- @@ L322-322 verbatim
end


-- @@ L324-324 verbatim
section


-- @@ L326-327 verbatim
/-! Source (22) for the literal initialized packet. The constants at
each fixed Sobolev order are independent of its truncation and frequency. -/


-- @@ L329-329 verbatim
@[expose] public section


-- @@ L331-331 verbatim
noncomputable section


-- @@ L333-333 verbatim
namespace EulerPacketCylinderField


-- @@ L335-335 verbatim
open Set


-- @@ L337-341 verbatim
theorem timeProfileChange_initial {T T' : ℝ} (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (g : C(Icc (0 : ℝ) T, ℝ)) (h : T = T') :
    timeProfileChange g h ⟨0,le_rfl,hT'⟩ = g ⟨0,le_rfl,hT⟩ := by
  subst T'
  rfl


-- @@ L343-343 verbatim
end EulerPacketCylinderField


-- @@ L345-345 verbatim
namespace EulerPacketTerminalDatum


-- @@ L347-350 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
      EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerPhysicalL2Scaling EulerCylinderCoordinates


-- @@ L352-356 verbatim
variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)


-- @@ L358-362 verbatim
/-- Initialized initial high, given by `scale M.ℓ (fun x => EulerPacketInitial.high N k⁻¹ 0
(initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))`. -/
def initializedInitialHigh (N : ℕ) (k : ℝ) : Space → Space :=
  scale M.ℓ (fun x => EulerPacketInitial.high N k⁻¹ 0
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))


-- @@ L364-368 verbatim
/-- Initialized initial mean, given by `scale M.ℓ (fun x => EulerPacketInitial.mean N k⁻¹ 0
(initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))`. -/
def initializedInitialMean (N : ℕ) (k : ℝ) : Space → Space :=
  scale M.ℓ (fun x => EulerPacketInitial.mean N k⁻¹ 0
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α) (0,(x,k*inner ℝ D.m₀ x)))


-- @@ L370-378 verbatim
include hTime in
theorem initializedInitialHigh_support
    (hS : D.support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (N : ℕ) (k : ℝ) :
    tsupport (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k) ⊆
      Metric.closedBall 0 (M.ℓ/2) := by
  have h := EulerPacketInitial.high_scaled_support
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹ k D.m₀ M.ℓ M.ℓ_pos (1/2) hS
  simpa only [initializedInitialHigh,div_eq_mul_inv,one_mul] using h


-- @@ L380-389 verbatim
include hTime in
theorem initializedInitialMean_support (N : ℕ) (k : ℝ) :
    tsupport (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k) ⊆
      Metric.closedBall 0 2 := by
  apply EulerPacketInitial.mean_scaled_support k⁻¹ k D.m₀ M.ℓ M.ℓ_pos
  intro i _ θ
  exact joinedSource_mean_initial_support period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    rfl i θ


-- @@ L391-398 verbatim
include hTime in
theorem initializedInitial_common_support
    (hS : D.support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (N : ℕ) (k : ℝ) :
    tsupport (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k) ⊆ Metric.closedBall 0 2 ∧
      tsupport (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k) ⊆ Metric.closedBall 0 2 := by
  refine ⟨(initializedInitialHigh_support M D hTime τ hτ hτT B δ hδ ξ hs α hS N k).trans ?_,
    initializedInitialMean_support M D hTime τ hτ hτT B δ hδ ξ hs α N k⟩
  exact Metric.closedBall_subset_closedBall (by have := M.ℓ_le_one; linarith)


-- @@ L400-415 verbatim
include hTime in
theorem initializedInitialMean_zero (hL : M.L = 0) (N : ℕ) (k : ℝ) :
    initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k = 0 := by
  funext x
  change M.ℓ • EulerPacketInitial.mean N k⁻¹ 0
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α)
    (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))) = 0
  rw [EulerPacketInitial.mean_eq]
  simp only [EulerPacketPointJets.fieldSum,EulerFiniteGrades.evaluate,EulerPacketInitial.timeSlice]
  have hz (i : ℕ) := joinedSource_mean_initial_zero period M D hTime τ hτ hτT B
    (joinedTerminalPrimary period M D τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    (joinedTerminalPrimaryWitness period M D hTime τ hτ hτT B (initialData D δ hδ (α • ξ) hs))
    rfl hL i (M.ℓ⁻¹ • x) (k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))
  simp only [show ∀ i, (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α i).mean
      (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x))) = 0 from hz,
    smul_zero,Finset.sum_const_zero]


-- @@ L417-430 verbatim
variable
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)


-- @@ L432-438 verbatim
include hgrowth in
theorem initialized_growth_initial : S.growth ⟨0,le_rfl,M.T_pos.le⟩=α := by
  have he := congrArg (fun g : C(Icc (0 : ℝ) D.T,ℝ) => g ⟨0,le_rfl,D.T_pos.le⟩) hgrowth
  rw [timeProfileChange_initial M.T_pos.le D.T_pos.le] at he
  have hp : L.fullProfile ⟨0,le_rfl,D.T_pos.le⟩=1 :=
    EulerElapsedTimePathGluing.profile_left D.T τ hτ.le hτT.le L.g L.initial_one ⟨0,le_rfl,hτ.le⟩
  simpa only [ContinuousMap.smul_apply,smul_eq_mul,hp,mul_one] using he


-- @@ L440-440 verbatim
include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth


-- @@ L442-456 verbatim
theorem initializedInitialHigh_Hm (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) (s : ℕ) :
    derivativeSum s (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k) ≤
      (M.ℓ⁻¹)^s*k^s*α*(EulerPacketInitial.highCost L.R S.H0 *
        physicalDerivativeCost period (4*L.R)
          (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖D.m₀‖)) s) := by
  let G := fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  have h := EulerPacketInitial.high_physical_bound G S L.R hG L.radius_bounds.1
    (initializedProfiles_zero M D τ hτ hτT B δ hδ ξ hs α) ⟨0,le_rfl,M.T_pos.le⟩
    hN BC.termCost k BC.one_le_termCost hk hbase M.ℓ M.ℓ_pos M.ℓ_le_one D.m₀ s
  simpa only [initializedInitialHigh,initialized_growth_initial M D hTime τ hτ hτT B α L S hgrowth]
      using h


-- @@ L458-471 verbatim
theorem initializedInitialMean_Hm (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) (s : ℕ) :
    derivativeSum s (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k) ≤
      (M.ℓ⁻¹)^s/k^2*(EulerPacketInitial.meanCost L.R S.H0 *
        physicalDerivativeCost period (4*L.R) ‖coordinateEquiv.symm.toContinuousLinearMap‖ s) := by
  let G := fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i
  have hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S L.R i :=
    fun i _ hi => initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth i hi
  exact EulerPacketInitial.mean_physical_bound G S L.R hG L.radius_bounds.1
    (initializedProfiles_zero M D τ hτ hτT B δ hδ ξ hs α) ⟨0,le_rfl,M.T_pos.le⟩
    hN BC.termCost k BC.one_le_termCost hk hbase
    (initializedProfiles_one_mean M D τ hτ hτT B δ hδ ξ hs α)
    M.ℓ M.ℓ_pos M.ℓ_le_one D.m₀ s


-- @@ L473-473 verbatim
end EulerPacketTerminalDatum


-- @@ L475-475 verbatim
end

-- @@ L476-476 verbatim
end


-- @@ L478-478 verbatim
end


-- @@ L480-480 verbatim
section


-- @@ L482-483 verbatim
/-! The actual chosen primary amplitude has exponential initial decay.
Its prefactor is a fixed polynomial in the same source parameters. -/


-- @@ L485-485 verbatim
@[expose] public section


-- @@ L487-487 verbatim
noncomputable section


-- @@ L489-489 verbatim
namespace EulerPacketInitialAmplitude


-- @@ L491-491 verbatim
open EulerPolynomialCost EulerParentInitializedRadius


-- @@ L493-494 verbatim
/-- Envelope, given by `4*X^2*(1+sourceEnvelope X)`. -/
def envelope (X : ℝ) : ℝ := 4*X^2*(1+sourceEnvelope X)

-- @@ L495-496 verbatim
/-- Polynomial, given by `4*Polynomial.X^2*(1+sourcePolynomial)`. -/
def polynomial : Polynomial ℝ := 4*Polynomial.X^2*(1+sourcePolynomial)

-- @@ L497-498 verbatim
/-- Bound constant, given by `coefficientCost polynomial`. -/
def boundConstant : ℝ := coefficientCost polynomial

-- @@ L499-500 verbatim
/-- Degree, given by `polynomial.natDegree`. -/
def degree : ℕ := polynomial.natDegree


-- @@ L502-502 verbatim
theorem constant_pos : 0 < boundConstant := coefficientCost_pos _


-- @@ L504-506 verbatim
theorem polynomial_eval (X : ℝ) : polynomial.eval X=envelope X := by
  simp only [polynomial,envelope,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_add,Polynomial.eval_one,sourcePolynomial_eval]


-- @@ L508-510 verbatim
theorem envelope_bound (X : ℝ) (hX : 1 ≤ X) : envelope X ≤ boundConstant*X^degree := by
  rw [← polynomial_eval]
  exact (le_abs_self _).trans (eval_bound polynomial X hX)


-- @@ L512-517 verbatim
theorem horizon_le_cost (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    H ≤ 560*H^10/ε := by
  have hp : H ≤ H^10 := by simpa only [pow_one] using pow_le_pow_right₀ hH (by norm_num : 1 ≤ 10)
  apply (le_div_iff₀ hε).mpr
  have hm : H*ε ≤ H := (mul_le_mul_of_nonneg_left hε1 (zero_le_one.trans hH)).trans_eq (mul_one _)
  nlinarith only [hp,hm,pow_nonneg (zero_le_one.trans hH) 10]


-- @@ L519-519 verbatim
end EulerPacketInitialAmplitude


-- @@ L521-521 verbatim
namespace EulerPacketSourceGeometry.Guards


-- @@ L523-524 verbatim
open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketInitialAmplitude
  EulerPacketUniformSource EulerParentInitializedRadius EulerPacketPressureScale EulerGevrey


-- @@ L526-530 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (J : Guards hτ hτT P H)
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT H (Fin 4) 6)


-- @@ L532-561 verbatim
theorem primaryAmplitude_polynomial (X x : ℝ) (hX : 1 ≤ X)
    (hH : P.horizon ≤ X) (hh : J.hchild ≤ X) (hδ : J.δ ≤ 1)
    (hC : L.C₀ ≤ sourceEnvelope X) (hσ : P.sigma * x ≤ 2) :
    J.primaryAmplitude hball ≤ boundConstant*X^degree*Real.exp (-x/8) := by
  have hF : ∀ t y, ‖D.F.field t y‖ ≤ L.C₀ := by
    intro t y
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using L.frame_bound 0 t y
  have hf := (P.rayScale_inv_le_frameBound hτ hτT).trans
    (D.frameBound_le_of_frame L.C₀ L.C₀_nonneg hF)
  have hf0 : 0 ≤ (P.rayScale hτ hτT)⁻¹ :=
    (inv_pos.mpr (rayScale_pos hτ hτT P)).le
  have hfS : (P.rayScale hτ hτT)⁻¹ ≤ 1+sourceEnvelope X := by linarith only [hf,hC]
  have hX0 := zero_le_one.trans hX
  have hS := zero_le_one.trans (sourceEnvelope_one X hX)
  have hH0 := zero_le_one.trans J.horizon_lower
  have hc0 := J.child_nonneg
  have hd0 := J.delta_nonneg
  have hpref : 4*P.horizon*J.δ*J.hchild/P.rayScale hτ hτT ≤ envelope X := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ 4*X*1*X*(1+sourceEnvelope X) := by gcongr
      _ = _ := by unfold envelope; ring
  have hs := sigma_exponential_bound P.sigma x J.sigma_pos hσ
  have hp := J.primaryAmplitude_exponential hball
  apply hp.trans
  apply (mul_le_mul hpref hs (Real.exp_pos _).le ?_).trans
  · exact mul_le_mul_of_nonneg_right (envelope_bound X hX) (Real.exp_pos _).le
  · unfold envelope
    positivity


-- @@ L563-566 verbatim
omit [CompleteSpace U] in
include J in
theorem horizon_le_growthCost : P.horizon ≤ 560*P.horizon^10/P.epsilon :=
  horizon_le_cost P.horizon P.epsilon J.horizon_lower J.epsilon_pos J.epsilon_small


-- @@ L568-568 verbatim
end EulerPacketSourceGeometry.Guards


-- @@ L570-570 verbatim
namespace EulerPacketSourceGeometry.ForwardGuards


-- @@ L572-573 verbatim
open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketInitialAmplitude
  EulerPacketUniformSource EulerParentInitializedRadius EulerPacketPressureScale


-- @@ L575-577 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (J : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ J.radius)


-- @@ L579-597 verbatim
theorem primaryAmplitude_polynomial (X x : ℝ) (hX : 1 ≤ X)
    (hH : P.horizon ≤ X) (hh : J.hchild ≤ X) (hδ : J.δ ≤ 1) (hσ : P.sigma * x ≤ 2) :
    J.primaryAmplitude hball ≤ boundConstant*X^degree*Real.exp (-x/8) := by
  have hS := zero_le_one.trans (sourceEnvelope_one X hX)
  have hX0 := zero_le_one.trans hX
  have hH0 := zero_le_one.trans J.horizon_lower
  have hc0 := J.child_nonneg
  have hd0 := J.delta_nonneg
  have hpref : 4*P.horizon*J.δ*J.hchild ≤ envelope X := by
    calc
      _ ≤ 4*X*1*X := by gcongr
      _ ≤ 4*X*1*X*(1+sourceEnvelope X) := by nlinarith only [mul_nonneg (sq_nonneg X) hS]
      _ = _ := by unfold envelope; ring
  have hs := sigma_exponential_bound P.sigma x J.sigma_pos hσ
  apply (J.primaryAmplitude_exponential hball).trans
  apply (mul_le_mul hpref hs (Real.exp_pos _).le ?_).trans
  · exact mul_le_mul_of_nonneg_right (envelope_bound X hX) (Real.exp_pos _).le
  · unfold envelope
    positivity


-- @@ L599-602 verbatim
include J hball in
theorem horizon_le_growthCost : P.horizon ≤ 560*P.horizon^10/P.epsilon := by
  have he : P.epsilon ≤ 1 := (J.lowGeometry hball).epsilon_le_one
  exact horizon_le_cost P.horizon P.epsilon J.horizon_lower J.epsilon_pos he


-- @@ L604-604 verbatim
end EulerPacketSourceGeometry.ForwardGuards


-- @@ L606-606 verbatim
end

-- @@ L607-607 verbatim
end


-- @@ L609-609 verbatim
end


-- @@ L611-611 verbatim
section


-- @@ L613-615 verbatim
/-! At each fixed Sobolev order, the two actual initial-increment costs
are fixed polynomials in the source primitives. Frequency and amplitude
are kept outside these polynomials. -/


-- @@ L617-617 verbatim
@[expose] public section


-- @@ L619-619 verbatim
noncomputable section


-- @@ L621-621 verbatim
namespace EulerPacketInitialCost


-- @@ L623-624 verbatim
open Finset EulerPhysicalL2Scaling EulerPacketTerminalDatum EulerPacketInitial
  EulerPacketPhysicalCost EulerPacketFiveCost EulerPacketCorrectionOutput EulerPolynomialCost


-- @@ L626-628 verbatim
/-- Jet polynomial map, given by `∑ n ∈ range (s+1), R^n*Polynomial.C ((n.factorial : ℝ)^2)`. -/
def jetPolynomialMap (R : Polynomial ℝ) (s : ℕ) : Polynomial ℝ :=
  ∑ n ∈ range (s+1), R^n*Polynomial.C ((n.factorial : ℝ)^2)


-- @@ L630-633 verbatim
theorem jetPolynomialMap_eval (R : Polynomial ℝ) (s : ℕ) (X : ℝ) :
    (jetPolynomialMap R s).eval X=jetPolynomial (R.eval X) s := by
  simp only [jetPolynomialMap,jetPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_C]


-- @@ L635-639 verbatim
/-- Physical polynomial, given by `∑ n ∈ range (s+1), Polynomial.C ((4*C)^n*Real.sqrt
(2/period+2*period)) * jetPolynomialMap R (n+1)`. -/
def physicalPolynomial (R : Polynomial ℝ) (C : ℝ) (s : ℕ) : Polynomial ℝ :=
  ∑ n ∈ range (s+1), Polynomial.C ((4*C)^n*Real.sqrt (2/period+2*period)) *
    jetPolynomialMap R (n+1)


-- @@ L641-644 verbatim
theorem physicalPolynomial_eval (R : Polynomial ℝ) (C : ℝ) (s : ℕ) (X : ℝ) :
    (physicalPolynomial R C s).eval X=physicalDerivativeCost period (R.eval X) C s := by
  simp only [physicalPolynomial,physicalDerivativeCost,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,jetPolynomialMap_eval]


-- @@ L646-651 verbatim
theorem jetPolynomial_mono {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) (s : ℕ) :
    jetPolynomial R s ≤ jetPolynomial S s := by
  unfold jetPolynomial
  apply sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hRS n) (sq_nonneg _)


-- @@ L653-664 verbatim
theorem physicalDerivativeCost_mono {R S C D : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hRS : R ≤ S) (hCD : C ≤ D) (s : ℕ) :
    physicalDerivativeCost period R C s ≤ physicalDerivativeCost period S D s := by
  unfold physicalDerivativeCost
  apply sum_le_sum
  intro n _
  have hj := jetPolynomial_mono hR hRS (n+1)
  have hj0 := jetPolynomial_nonneg R hR (n+1)
  have hj1 := hj0.trans hj
  have hD := hC.trans hCD
  have hs := Real.sqrt_nonneg (2/period+2*period)
  gcongr


-- @@ L666-669 verbatim
/-- Envelope, given by `1+(highCost X X+meanCost X X)*physicalDerivativeCost period (4*X)
(coordinateCost*2) s`. -/
def envelope (s : ℕ) (X : ℝ) : ℝ :=
  1+(highCost X X+meanCost X X)*physicalDerivativeCost period (4*X) (coordinateCost*2) s


-- @@ L671-675 verbatim
/-- Polynomial, given by `1+(gradePolynomial 1+2*gradePolynomial 2+3) * physicalPolynomial
(4*Polynomial.X) (coordinateCost*2) s`. -/
def polynomial (s : ℕ) : Polynomial ℝ :=
  1+(gradePolynomial 1+2*gradePolynomial 2+3) *
    physicalPolynomial (4*Polynomial.X) (coordinateCost*2) s


-- @@ L677-682 verbatim
theorem polynomial_eval (s : ℕ) (X : ℝ) : (polynomial s).eval X=envelope s X := by
  unfold polynomial envelope highCost meanCost
  simp only [Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_one,Polynomial.eval_ofNat,physicalPolynomial_eval,
    Polynomial.eval_X,gradePolynomial_eval]
  ring


-- @@ L684-710 verbatim
theorem costs_le_envelope (s : ℕ) (R H X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hRX : R ≤ X) (hHX : H ≤ X) :
    highCost R H*physicalDerivativeCost period (4*R) (coordinateCost*2) s ≤ envelope s X ∧
    meanCost R H*physicalDerivativeCost period (4*R) coordinateCost s ≤ envelope s X := by
  have hX := hR.trans hRX
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have h1 := gradeCost_mono R H X hR hH hRX hHX 1
  have h2 := gradeCost_mono R H X hR hH hRX hHX 2
  have hhigh : highCost R H ≤ highCost X X := by unfold highCost; linarith
  have hmean : meanCost R H ≤ meanCost X X := by unfold meanCost; linarith
  have hd1 := physicalDerivativeCost_mono (by positivity : 0 ≤ 4*R)
    (by positivity : 0 ≤ coordinateCost*2) (by linarith : 4*R ≤ 4*X) le_rfl s
  have hd2 := physicalDerivativeCost_mono (by positivity : 0 ≤ 4*R)
    hc (by linarith : 4*R ≤ 4*X) (by linarith : coordinateCost ≤ coordinateCost*2) s
  have hv := highCost_nonneg X X hX
  have hm := meanCost_nonneg X X hX
  have hd := physicalDerivativeCost_nonneg period (4*X) (coordinateCost*2) (by
      positivity) (by positivity) s
  have hh := mul_le_mul hhigh hd1
    (physicalDerivativeCost_nonneg period (4*R) (coordinateCost*2) (by
        positivity) (by positivity) s) hv
  have hm' := mul_le_mul hmean hd2
    (physicalDerivativeCost_nonneg period (4*R) coordinateCost (by positivity) hc s) hm
  unfold envelope
  constructor
  · nlinarith only [hh,mul_nonneg hm hd]
  · nlinarith only [hm',mul_nonneg hv hd]


-- @@ L712-716 verbatim
/-- Source polynomial as an element of `Polynomial ℝ`. -/
def sourcePolynomial (s : ℕ) : Polynomial ℝ :=
  (polynomial s).comp ((1+Polynomial.X+EulerPacketRadiusPolynomial.radiusPolynomial +
    EulerPacketCorrectionPrimitive.primitivePolynomial period).comp
        EulerPacketUniformSource.profilePolynomial)


-- @@ L718-719 verbatim
/-- Source constant, given by `coefficientCost (sourcePolynomial s)`. -/
def sourceConstant (s : ℕ) : ℝ := coefficientCost (sourcePolynomial s)

-- @@ L720-721 verbatim
/-- Source power, given by `(sourcePolynomial s).natDegree`. -/
def sourcePower (s : ℕ) : ℕ := (sourcePolynomial s).natDegree


-- @@ L723-723 verbatim
theorem sourceConstant_pos (s : ℕ) : 0 < sourceConstant s := coefficientCost_pos _


-- @@ L725-732 verbatim
theorem sourcePolynomial_eval (s : ℕ) (X : ℝ) :
    (sourcePolynomial s).eval X =
      envelope s (EulerPacketInitializedCost.envelope (EulerPacketUniformSource.profileEnvelope X))
          := by
  simp only [sourcePolynomial,Polynomial.eval_comp,polynomial_eval,Polynomial.eval_add,
    Polynomial.eval_one,Polynomial.eval_X,EulerPacketRadiusPolynomial.radiusPolynomial_eval,
    EulerPacketCorrectionPrimitive.primitivePolynomial_eval,
    EulerPacketUniformSource.profilePolynomial_eval,EulerPacketInitializedCost.envelope]


-- @@ L734-738 verbatim
theorem source_bound (s : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    envelope s (EulerPacketInitializedCost.envelope (EulerPacketUniformSource.profileEnvelope X)) ≤
      sourceConstant s*X^sourcePower s := by
  rw [← sourcePolynomial_eval]
  exact (le_abs_self _).trans (eval_bound (sourcePolynomial s) X hX)


-- @@ L740-740 verbatim
end EulerPacketInitialCost


-- @@ L742-742 verbatim
end

-- @@ L743-743 verbatim
end


-- @@ L745-745 verbatim
end


-- @@ L747-747 verbatim
section


-- @@ L749-751 verbatim
/-! The exact correction has zero initial value, so the two actual
compactly supported initial increments are precisely the finite-packet
high and mean fields whose physical Sobolev bounds were proved above. -/


-- @@ L753-753 verbatim
@[expose] public section


-- @@ L755-755 verbatim
noncomputable section


-- @@ L757-757 verbatim
namespace EulerPacketTerminalDatum


-- @@ L759-761 verbatim
open Set MeasureTheory EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPhysicalL2Scaling EulerAllOrderDriftCorrection EulerPacketCoordinates


-- @@ L763-767 verbatim
variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)


-- @@ L769-780 verbatim
theorem initializedInitial_split (N : ℕ) (k : ℝ) :
    scale M.ℓ (fun x => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (0,(x,k*inner ℝ D.m₀ x))) =
      initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k +
      initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k := by
  funext x
  have h := congrFun (EulerPacketInitial.packet_split N k⁻¹ 0
    (initializedProfiles M D τ hτ hτT B δ hδ ξ hs α))
    (0,(M.ℓ⁻¹ • x,k*inner ℝ D.m₀ (M.ℓ⁻¹ • x)))
  simp only [EulerPacketInitial.timeSlice,Pi.add_apply] at h
  simpa only [initializedInitialHigh,initializedInitialMean,scale,Pi.add_apply,
    smul_add,initializedVelocity] using congrArg (fun v : Space => M.ℓ • v) h


-- @@ L782-790 verbatim
include hTime in
theorem initializedInitialHigh_memLp (N n : ℕ) (k : ℝ) :
    MemLp (iteratedFDeriv ℝ n (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k)) 2 volume :=
        by
  let G := EulerPacketInitial.highField
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹
  exact scale_jet_memLp M.ℓ M.ℓ_pos _ (G.raw_graph_contDiff ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀) n
    (G.raw_graph_tensor_memLp ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀ n)


-- @@ L792-800 verbatim
include hTime in
theorem initializedInitialMean_memLp (N n : ℕ) (k : ℝ) :
    MemLp (iteratedFDeriv ℝ n (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k)) 2 volume :=
        by
  let G := EulerPacketInitial.meanField
    (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
    ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹
  exact scale_jet_memLp M.ℓ M.ℓ_pos _ (G.raw_graph_contDiff ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀) n
    (G.raw_graph_tensor_memLp ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀ n)


-- @@ L802-809 verbatim
include hTime in
theorem initializedInitial_compact
    (hS : D.support ⊆ Metric.closedBall 0 (1 / 2 : ℝ)) (N : ℕ) (k : ℝ) :
    HasCompactSupport (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k) ∧
      HasCompactSupport (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k) := by
  have h := initializedInitial_common_support M D hTime τ hτ hτT B δ hδ ξ hs α hS N k
  exact ⟨(isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) h.1,
    (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) h.2⟩


-- @@ L811-813 verbatim
variable (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
  (Q : Budget period D.T_pos
    (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk))


-- @@ L815-820 verbatim
theorem initializedExactPhysicalVelocity_initial (x : Space) :
    initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk Q
      ⟨0,le_rfl,D.T_pos.le⟩ id x =
      initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹ (0,(x,k*inner ℝ D.m₀ x)) := by
  rw [initializedExactPhysicalVelocity_eq,Q.pointField_initial,map_zero,smul_zero,add_zero]
  rfl


-- @@ L822-829 verbatim
theorem initializedExactPhysicalVelocity_initial_split :
    scale M.ℓ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q ⟨0,le_rfl,D.T_pos.le⟩ id) =
      initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k +
      initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k := by
  rw [funext (initializedExactPhysicalVelocity_initial M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q)]
  exact initializedInitial_split M D τ hτ hτT B δ hδ ξ hs α N k


-- @@ L831-831 verbatim
end EulerPacketTerminalDatum


-- @@ L833-833 verbatim
end

-- @@ L834-834 verbatim
end


-- @@ L836-836 verbatim
end


-- @@ L838-838 verbatim
section


-- @@ L840-841 verbatim
/-! Source-only initial estimates for the actual packet constructed from
a parent and its activation geometry. No initial-field estimate is an input. -/


-- @@ L843-843 verbatim
section


-- @@ L845-846 verbatim
/-! The actual initial increments for the canonical uniformly selected
packet satisfy source (22), with fixed-order polynomial costs. -/


-- @@ L848-848 verbatim
@[expose] public section


-- @@ L850-850 verbatim
noncomputable section


-- @@ L852-852 verbatim
namespace EulerPacketTerminalDatum


-- @@ L854-857 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCorrectionConstants EulerPacketCorrectionScalar EulerPacketSourceFrequency
  EulerPacketCorrectionCoefficients

-- @@ L858-858 verbatim
open scoped ContDiff


-- @@ L860-876 verbatim
variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (W : ℝ)
  (hW : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB
    (joinedCoefficientBudget period M D hTime τ hτ hτT B NB) δ ξ W)
  (hprofile : ∀ t, α * L.fullProfile t ≤ W)
  (k : ℝ) (hk : 4 ≤ k)
  (hfrequency :
      EulerPacketInitializedCost.uniformConstant * W ^ EulerPacketInitializedCost.uniformPower ≤
    smallPower k)


-- @@ L878-878 verbatim
open EulerPhysicalL2Scaling EulerPacketPhysicalCost EulerCylinderCoordinates


-- @@ L880-880 verbatim
include hδ1 hα L NB LM hW hprofile hk hfrequency


-- @@ L882-923 verbatim
theorem initialized_uniform_initial_bounds (s : ℕ) :
    derivativeSum s (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s*k^s*α*EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) ∧
    derivativeSum s (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s/k^2*EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) := by
  let BC := joinedCoefficientBudget period M D hTime τ hτ hτT B NB
  let L' := initializedJoinedBudget LM L NB BC δ ξ
  let H' := initializedPrimaryBudget LM L NB BC δ ξ
  let NB' := initializedNormalBudget LM L NB BC δ ξ
  let LM' := initializedMeanBudget LM L NB BC δ ξ
  have guards := initializedRadius_guards LM L NB BC δ ξ
  let S := Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime.symm α hα
  have hH0 : S.H0 ≤ W := Scales.ofTimeProfile_H0_le L.fullProfile L.fullProfile_pos
    hTime.symm α hα W hW.one hprofile
  have hgrowth : timeProfileChange S.growth hTime=α • L'.fullProfile :=
    Scales.ofTimeProfile_growth L.fullProfile L.fullProfile_pos hTime.symm α hα
  have costs := EulerPacketInitializedCost.initialized_five_costs_bound
    LM L NB BC δ ξ W S.H0 hδ hW S.H0_pos.le hH0
  have hbase : EulerPacketCoarseMajorant.tailBase L'.R S.H0 BC.termCost (truncation k) ≤ k^(1/100 :
      ℝ) :=
    tailBase_frequency L'.R S.H0 BC.termCost k BC.termCost_nonneg (by
        linarith) (costs.1.trans hfrequency)
  have hn := (truncation_bounds k (by linarith)).1
  have hh := initializedInitialHigh_Hm M D hTime τ hτ hτT B δ hδ ξ hs α
    L' H' NB' guards.1 LM' guards.2.1 BC guards.2.2.2.2.2 guards.2.2.2.2.1
    hδ1 hα guards.2.2.2.1 guards.2.2.1 S hgrowth (truncation k) hn k hk hbase s
  have hm := initializedInitialMean_Hm M D hTime τ hτ hτT B δ hδ ξ hs α
    L' H' NB' guards.1 LM' guards.2.1 BC guards.2.2.2.2.2 guards.2.2.2.2.1
    hδ1 hα guards.2.2.2.1 guards.2.2.1 S hgrowth (truncation k) hn k hk hbase s
  have hb := EulerPacketInitializedCost.actual_parameters LM L NB BC δ ξ W S.H0 hδ hW hH0
  have hp := EulerPacketInitialCost.costs_le_envelope s L'.R S.H0
    (EulerPacketInitializedCost.envelope W) (zero_le_one.trans L'.radius_bounds.1) S.H0_pos.le
    hb.2.1 hb.2.2.1
  have hhigh : EulerPacketInitial.highCost L'.R S.H0 *
      physicalDerivativeCost period (4*L'.R)
        (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖D.m₀‖)) s ≤
      EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) := by
    simpa only [D.m₀_unit,show (1 : ℝ)+1=2 by norm_num,coordinateCost] using hp.1
  have hell : 0 ≤ M.ℓ⁻¹ := (inv_pos.mpr M.ℓ_pos).le
  have hk0 : 0 ≤ k := by linarith
  exact ⟨hh.trans (mul_le_mul_of_nonneg_left hhigh (by positivity)),
    hm.trans (mul_le_mul_of_nonneg_left hp.2 (by positivity))⟩


-- @@ L925-929 verbatim
variable (Cagree : SourceCoefficientAgreement M D)
  (hX : 64 ≤ expansion k) (hlog : 1 ≤ Real.log k)
  (Ξ : Icc (0 : ℝ) D.T → Space → Space) (hΞ : ∀ t, ContDiff ℝ ∞ (Ξ t))
  (hF : ∀ t x, fderiv ℝ (Ξ t) x = D.F.field t x)
  (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)


-- @@ L931-932 verbatim
local notation "Q" => initializedUniformBudget M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
  L NB LM Cagree W hW hprofile k hk hX hlog hfrequency Ξ hΞ hF hdet


-- @@ L934-947 verbatim
theorem initializedUniformBudget_initial (s : ℕ) :
    scale M.ℓ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree (truncation k) (truncation_bounds k (by linarith)).1 k hk Q
      ⟨0,le_rfl,D.T_pos.le⟩ id) =
      initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α (truncation k) k +
      initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α (truncation k) k ∧
    derivativeSum s (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s*k^s*α*EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) ∧
    derivativeSum s (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s/k^2*EulerPacketInitialCost.envelope s (EulerPacketInitializedCost.envelope W) :=
  ⟨initializedExactPhysicalVelocity_initial_split M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree (truncation k) (truncation_bounds k (by linarith)).1 k hk Q,
   initialized_uniform_initial_bounds M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
    L NB LM W hW hprofile k hk hfrequency s⟩


-- @@ L949-949 verbatim
end EulerPacketTerminalDatum


-- @@ L951-951 verbatim
end

-- @@ L952-952 verbatim
end


-- @@ L954-954 verbatim
end


-- @@ L956-956 verbatim
section


-- @@ L958-959 verbatim
/-! Fixed-order source polynomial bounds for the literal initial increments.
These use the same finite frequency guard as the constructed exact packet. -/


-- @@ L961-961 verbatim
@[expose] public section


-- @@ L963-963 verbatim
noncomputable section


-- @@ L965-965 verbatim
namespace EulerPacketUniformSource


-- @@ L967-975 verbatim
theorem initial_frequency_guard (X k : ℝ) (hX : 1 ≤ X)
    (h : frequencyConstant * X ^ frequencyPower ≤ EulerPacketSourceFrequency.smallPower k) :
    EulerPacketInitializedCost.uniformConstant *
      (profileEnvelope X)^EulerPacketInitializedCost.uniformPower ≤
        EulerPacketSourceFrequency.smallPower k := by
  have hW := (profileEnvelope_bounds X hX).1
  exact (EulerPacketInitializedOutputCost.envelope_components _ (zero_le_one.trans hW)).1.trans
    ((EulerPacketInitializedOutputCost.envelope_bound _ hW).trans
      ((frequency_bound X hX).trans h))


-- @@ L977-977 verbatim
end EulerPacketUniformSource


-- @@ L979-979 verbatim
namespace EulerPacketTerminalDatum


-- @@ L981-983 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketCorrectionCoefficients EulerPhysicalL2Scaling
  EulerPacketUniformSource EulerPacketInitialCost EulerPacketSourceFrequency


-- @@ L985-999 verbatim
variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ) (hα : 0 < α)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  {Rm : ℝ} (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (X : ℝ) (hX : 1 ≤ X)
  (hW : EulerPacketRadiusPolynomial.RadiusPrimitives LM L NB
    (joinedCoefficientBudget period M D hTime τ hτ hτT B NB) δ ξ (profileEnvelope X))
  (hprofile : ∀ t, α * L.fullProfile t ≤ profileEnvelope X)
  (k : ℝ) (hk : 4 ≤ k)
  (hfrequency : frequencyConstant * X ^ frequencyPower ≤ smallPower k)


-- @@ L1001-1001 verbatim
include hδ1 hα L NB LM hX hW hprofile hk hfrequency


-- @@ L1003-1014 verbatim
theorem initialized_initial_polynomial_bounds (s : ℕ) :
    derivativeSum s (initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s*k^s*α*(sourceConstant s*X^sourcePower s) ∧
    derivativeSum s (initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α (truncation k) k) ≤
      (M.ℓ⁻¹)^s/k^2*(sourceConstant s*X^sourcePower s) := by
  have h := initialized_uniform_initial_bounds M D hTime τ hτ hτT B δ hδ hδ1 ξ hs α hα
    L NB LM (profileEnvelope X) hW hprofile k hk (initial_frequency_guard X k hX hfrequency) s
  have hc := source_bound s X hX
  have hell : 0 ≤ M.ℓ⁻¹ := (inv_pos.mpr M.ℓ_pos).le
  have hk0 : 0 ≤ k := by linarith only [hk]
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_left hc (by positivity)),
    h.2.trans (mul_le_mul_of_nonneg_left hc (by positivity))⟩


-- @@ L1016-1016 verbatim
end EulerPacketTerminalDatum


-- @@ L1018-1018 verbatim
end

-- @@ L1019-1019 verbatim
end


-- @@ L1021-1021 verbatim
end


-- @@ L1023-1023 verbatim
@[expose] public section


-- @@ L1025-1025 verbatim
noncomputable section


-- @@ L1027-1027 verbatim
namespace EulerParentPacketFrames.LabelData


-- @@ L1029-1032 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerParentInitializedRadius EulerPacketUniformSource
  EulerPacketTerminalDatum EulerPacketCylinderField EulerMeanHarmonic EulerPhysicalL2Scaling
  EulerPacketSourceFrequency


-- @@ L1034-1044 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {G : Parent} (L : LabelData G) (H : LowBounds G)
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < G.T)
  (P : ParentFrame (G.transverseData m hm R S hS) τ)
  (J : Guards hτ hτT P (G.historyOn H m hm R S hS τ hτ hτT))
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (Ti TiTotal : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
  (hT1 : G.T ≤ 1) (hTiTotal : G.T⁻¹ ≤ TiTotal)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
  (hsub : S ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))


-- @@ L1046-1047 verbatim
local notation "A" => L.geometryInputs H m hm R S hS τ hτ hτT P J hball Ti TiTotal
  hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball

-- @@ L1048-1050 verbatim
local notation "BC" => joinedCoefficientBudget period (G.meanData H)
  (G.transverseData m hm R S hS) rfl τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT)
  (JoinedInputs.normal A)


-- @@ L1052-1074 verbatim
theorem geometry_initial_primitives (ξ : U) (hδ : 0 < J.δ) :
    let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
    1 ≤ X ∧ P.horizon ≤ X ∧ J.hchild ≤ X ∧
      EulerPacketRadiusPolynomial.RadiusPrimitives (A).mean (A).linear (A).normal BC J.δ ξ
        (sourceEnvelope X) := by
  let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
  have hL0 : 0 ≤ H.L := (mul_nonneg boundaryLocalizationC1_nonneg H.Bc_nonneg).trans H.L_lower
  obtain ⟨hx,hK,hI,hIT,hC,hB,hD,hN⟩ := parameterSize_bounds L.K Ti TiTotal
    (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖ (zero_le_one.trans L.K_one)
    ((inv_pos.mpr hτ).le.trans hTi) ((inv_pos.mpr G.T_pos).le.trans hTiTotal)
    J.growth_constant_pos.le hL0 hδ (norm_nonneg ξ)
  have hbase : parameterSize L.K Ti TiTotal (560*P.horizon^10/P.epsilon) H.L J.δ ‖ξ‖ ≤ X :=
    le_add_of_nonneg_right J.child_nonneg
  have hX : 1 ≤ X := hx.trans hbase
  have hhX : J.hchild ≤ X := le_add_of_nonneg_left (zero_le_one.trans hx)
  have hp := L.joined_radius_primitives H m hm R S hS τ hτ hτT Ti
    (560*P.horizon^10/P.epsilon) hτ1 hTi J.growth_constant_pos.le
    (J.sourceGrowthProfile hball) (J.sourceGrowthProfile_positive hball)
    (J.sourceGrowthProfile_initial hball) Ω hΩ hΩo hsub hΩball
    (J.sourceGrowthProfile_propagator hball) TiTotal hT1 hTiTotal J.δ ξ X
    (hK.trans hbase) (hI.trans hbase) (hIT.trans hbase) (hC.trans hbase)
    (hB.trans hbase) (hD.trans hbase) (hN.trans hbase)
  exact ⟨hX,J.horizon_le_growthCost.trans (hC.trans hbase),hhX,hp⟩


-- @@ L1076-1076 verbatim
include hτ1 hTi hT1 hTiTotal hΩ hΩo hsub hΩball


-- @@ L1078-1085 verbatim
theorem geometry_initial_amplitude (ξ : U) (hδ : 0 < J.δ) (hδ1 : J.δ ≤ 1)
    (x : ℝ) (hσ : P.sigma * x ≤ 2) :
    let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
    J.primaryAmplitude hball ≤ EulerPacketInitialAmplitude.boundConstant *
      X^EulerPacketInitialAmplitude.degree*Real.exp (-x/8) := by
  obtain ⟨hX,hH,hh,hp⟩ := L.geometry_initial_primitives H m hm R S hS τ hτ hτT P J hball
    Ti TiTotal hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball ξ hδ
  exact J.primaryAmplitude_polynomial hball (A).linear _ x hX hH hh hδ1 hp.joined_frame hσ


-- @@ L1087-1130 verbatim
theorem geometry_initial_bounds (ξ : U) (hs : tsupport EulerSpatialCutoffs.innerCutoff ⊆ S)
    (hδ : 0 < J.δ) (hδ1 : J.δ ≤ 1) (hh : 0 < J.hchild)
    (x : ℝ) (hσ : P.sigma * x ≤ 2) (k : ℝ) (hk : 4 ≤ k)
    (hfrequency : frequencyConstant *
      (L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ) ^ frequencyPower ≤
          smallPower
          k)
    (s : ℕ) :
    let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
    derivativeSum s (initializedInitialHigh (G.meanData H) (G.transverseData m hm R S hS)
      τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) J.δ hδ ξ hs
      (J.primaryAmplitude hball) (truncation k) k) ≤
      (G.ell⁻¹)^s*k^s*(EulerPacketInitialAmplitude.boundConstant *
        EulerPacketInitialCost.sourceConstant s *
        X^(EulerPacketInitialAmplitude.degree+EulerPacketInitialCost.sourcePower s))*Real.exp
            (-x/8) ∧
    derivativeSum s (initializedInitialMean (G.meanData H) (G.transverseData m hm R S hS)
      τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) J.δ hδ ξ hs
      (J.primaryAmplitude hball) (truncation k) k) ≤
      (G.ell⁻¹)^s/k^2*(EulerPacketInitialCost.sourceConstant s *
        X^EulerPacketInitialCost.sourcePower s) := by
  let X := L.geometryParameterSize H m hm R S hS τ hτ hτT P J Ti TiTotal ξ
  have hp := L.geometry_uniform_primitives H m hm R S hS τ hτ hτT P J hball
    Ti TiTotal hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball ξ hδ hδ1
  have hx := L.geometry_initial_primitives H m hm R S hS τ hτ hτT P J hball
    Ti TiTotal hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball ξ hδ
  have ha := L.geometry_initial_amplitude H m hm R S hS τ hτ hτT P J hball
    Ti TiTotal hτ1 hTi hT1 hTiTotal Ω hΩ hΩo hsub hΩball ξ hδ hδ1 x hσ
  have hb := initialized_initial_polynomial_bounds (G.meanData H) (G.transverseData m hm R S hS)
    rfl τ hτ hτT (G.historyOn H m hm R S hS τ hτ hτT) J.δ hδ hδ1 ξ hs
    (J.primaryAmplitude hball) (J.primaryAmplitude_pos hball hδ hh)
    (A).linear (A).normal (A).mean X hx.1 hp.1 hp.2.1 k hk hfrequency s
  have hell : 0 ≤ G.ell⁻¹ := (inv_pos.mpr G.ell_pos).le
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hX0 : 0 ≤ X := zero_le_one.trans hx.1
  have hC0 := (EulerPacketInitialCost.sourceConstant_pos s).le
  refine ⟨hb.1.trans ?_,hb.2⟩
  calc
    _ ≤ (G.ell⁻¹)^s*k^s*(EulerPacketInitialAmplitude.boundConstant *
        X^EulerPacketInitialAmplitude.degree*Real.exp (-x/8)) *
        (EulerPacketInitialCost.sourceConstant s*X^EulerPacketInitialCost.sourcePower s) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha (by positivity)) (by positivity)
    _ = _ := by rw [pow_add]; ring


-- @@ L1132-1132 verbatim
end EulerParentPacketFrames.LabelData


-- @@ L1134-1134 verbatim
end

-- @@ L1135-1135 verbatim
end


-- @@ L1137-1137 verbatim
end


-- @@ L1139-1139 verbatim
section


-- @@ L1141-1142 verbatim
/-! Ordinary smooth square-integrable fields realizing both actual
initial increments, with the same concrete high and mean functions. -/


-- @@ L1144-1144 verbatim
@[expose] public section


-- @@ L1146-1146 verbatim
noncomputable section


-- @@ L1148-1148 verbatim
namespace EulerPacketTerminalDatum


-- @@ L1150-1151 verbatim
open Set MeasureTheory EulerSmoothLimit EulerSpatialCutoffs EulerTransversePacketProvider
  EulerPacketCylinderField EulerPacketProfileRecursion EulerPhysicalL2Scaling EulerLpTranslation


-- @@ L1153-1157 verbatim
variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)


-- @@ L1159-1167 verbatim
/-- Initialized initial high field, bundling `field`, `smooth`, `let`, `integrable`. -/
def initializedInitialHighField (N : ℕ) (k : ℝ) : SmoothL2Field Space where
  field := initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k
  smooth := by
    let G := EulerPacketInitial.highField
      (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
      ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹
    exact scale_contDiff M.ℓ _ (G.raw_graph_contDiff ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀)
  integrable n := initializedInitialHigh_memLp M D hTime τ hτ hτT B δ hδ ξ hs α N n k


-- @@ L1169-1177 verbatim
/-- Initialized initial mean field, bundling `field`, `smooth`, `let`, `integrable`. -/
def initializedInitialMeanField (N : ℕ) (k : ℝ) : SmoothL2Field Space where
  field := initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k
  smooth := by
    let G := EulerPacketInitial.meanField
      (fun i (_ : i ≤ N) => initializedProfileWitness M D hTime τ hτ hτT B δ hδ ξ hs α i)
      ⟨0,le_rfl,M.T_pos.le⟩ k⁻¹
    exact scale_contDiff M.ℓ _ (G.raw_graph_contDiff ⟨0,le_rfl,M.T_pos.le⟩ k D.m₀)
  integrable n := initializedInitialMean_memLp M D hTime τ hτ hτT B δ hδ ξ hs α N n k


-- @@ L1179-1181 verbatim
theorem initializedInitialHighField_field (N : ℕ) (k : ℝ) :
    (initializedInitialHighField M D hTime τ hτ hτT B δ hδ ξ hs α N k).field =
      initializedInitialHigh M D τ hτ hτT B δ hδ ξ hs α N k := rfl


-- @@ L1183-1185 verbatim
theorem initializedInitialMeanField_field (N : ℕ) (k : ℝ) :
    (initializedInitialMeanField M D hTime τ hτ hτT B δ hδ ξ hs α N k).field =
      initializedInitialMean M D τ hτ hτT B δ hδ ξ hs α N k := rfl


-- @@ L1187-1187 verbatim
end EulerPacketTerminalDatum


-- @@ L1189-1189 verbatim
end

-- @@ L1190-1190 verbatim
end


-- @@ L1192-1192 verbatim
end


-- @@ L1194-1194 verbatim
@[expose] public section


-- @@ L1196-1196 verbatim
noncomputable section


-- @@ L1198-1198 verbatim
namespace EulerPacketInitial


-- @@ L1200-1203 verbatim
open Set EulerSmoothLimit EulerSpatialCutoffs EulerParentPacketFrames
  EulerTransversePacketProvider EulerPacketSourceGeometry EulerPacketCylinderField
  EulerPacketTerminalDatum EulerPacketUniformSource EulerPhysicalL2Scaling
  EulerPacketSourceFrequency EulerLpTranslation EulerAllOrderDriftCorrection


-- @@ L1205-1247 verbatim
/-- Input data, collecting `parent`, `label`, `low`, `normal`, `normal_unit`, `coordinates` and
their compatibility conditions. -/
structure Input (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] where
  /-- Parent of `Input`, of type `Parent`. -/
  parent : Parent
  /-- Label of `Input`, of type `LabelData parent`. -/
  label : LabelData parent
  /-- Low of `Input`, of type `LowBounds parent`. -/
  low : LowBounds parent
  /-- Normal of `Input`, of type `Space`. -/
  normal : Space
  normal_unit : ‖normal‖=1
  /-- Coordinates of `Input`, of type `U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane
  normal`. -/
  coordinates : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane normal
  /-- Support set of `Input`, of type `Set Space`. -/
  support : Set Space
  support_compact : IsCompact support
  /-- History time of `Input`, of type `ℝ`. -/
  historyTime : ℝ
  history_pos : 0 < historyTime
  history_lt : historyTime < parent.T
  total_le_one : parent.T ≤ 1
  /-- Frame supplied by `Input`. -/
  frame : ParentFrame (parent.transverseData normal normal_unit coordinates support
      support_compact) historyTime
  /-- Geometry supplied by `Input`. -/
  geometry : Guards history_pos history_lt frame
    (parent.historyOn low normal normal_unit coordinates support support_compact historyTime
        history_pos history_lt)
  halfBall : (1/2 : ℝ) ≤ geometry.radius
  /-- Neighborhood of `Input`, of type `Set Space`. -/
  neighborhood : Set Space
  neighborhood_measurable : MeasurableSet neighborhood
  neighborhood_open : IsOpen neighborhood
  support_subset : support ⊆ neighborhood
  neighborhood_bound : ∀ x ∈ neighborhood, ‖x‖ ≤ (1/2 : ℝ)
  /-- Terminal of `Input`, of type `U`. -/
  terminal : U
  cutoff_support : tsupport innerCutoff ⊆ support
  delta_pos : 0 < geometry.δ
  delta_le_one : geometry.δ ≤ 1
  child_pos : 0 < geometry.hchild


-- @@ L1249-1249 verbatim
namespace Input


-- @@ L1251-1252 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : Input U)


-- @@ L1254-1257 verbatim
/-- Data: an abbreviation for `A.parent.transverseData A.normal A.normal_unit A.coordinates
A.support A.support_compact`. -/
abbrev data : Data U := A.parent.transverseData A.normal A.normal_unit A.coordinates A.support
    A.support_compact

-- @@ L1258-1259 verbatim
/-- Mean data: an abbreviation for `A.parent.meanData A.low`. -/
abbrev meanData : EulerMeanPacketProvider.Data := A.parent.meanData A.low

-- @@ L1260-1264 verbatim
/-- History: an abbreviation for `A.parent.historyOn A.low A.normal A.normal_unit A.coordinates
A.support A.support_compact A.historyTime A.history_pos A.history_lt`. -/
abbrev history : HistoryData (A.data.initial A.historyTime A.history_pos A.history_lt.le) :=
  A.parent.historyOn A.low A.normal A.normal_unit A.coordinates A.support A.support_compact
    A.historyTime A.history_pos A.history_lt


-- @@ L1266-1269 verbatim
/-- Parameter size, constructed using `A.label.geometryParameterSize`. -/
def parameterSize : ℝ := A.label.geometryParameterSize A.low A.normal A.normal_unit A.coordinates
  A.support A.support_compact A.historyTime A.history_pos A.history_lt A.frame A.geometry
  A.historyTime⁻¹ A.parent.T⁻¹ A.terminal


-- @@ L1271-1272 verbatim
/-- Alpha, given by `A.geometry.primaryAmplitude A.halfBall`. -/
def alpha : ℝ := A.geometry.primaryAmplitude A.halfBall


-- @@ L1274-1275 verbatim
theorem alpha_pos : 0 < A.alpha := A.geometry.primaryAmplitude_pos A.halfBall A.delta_pos
    A.child_pos


-- @@ L1277-1278 verbatim
/-- Frequency guard, given by `frequencyConstant*A.parameterSize^frequencyPower ≤ smallPower k`. -/
def frequencyGuard (k : ℝ) : Prop := frequencyConstant*A.parameterSize^frequencyPower ≤ smallPower k


-- @@ L1280-1283 verbatim
/-- High, constructed using `initializedInitialHigh`. -/
def high (k : ℝ) : Space → Space :=
  initializedInitialHigh A.meanData A.data A.historyTime A.history_pos A.history_lt A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k


-- @@ L1285-1288 verbatim
/-- Mean, constructed using `initializedInitialMean`. -/
def mean (k : ℝ) : Space → Space :=
  initializedInitialMean A.meanData A.data A.historyTime A.history_pos A.history_lt A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k


-- @@ L1290-1294 verbatim
/-- High field, constructed using `initializedInitialHighField`. -/
def highField (k : ℝ) : SmoothL2Field Space :=
  initializedInitialHighField A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
      A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k


-- @@ L1296-1300 verbatim
/-- Mean field, constructed using `initializedInitialMeanField`. -/
def meanField (k : ℝ) : SmoothL2Field Space :=
  initializedInitialMeanField A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
      A.history
    A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha (truncation k) k


-- @@ L1302-1302 verbatim
theorem highField_field (k : ℝ) : (A.highField k).field=A.high k := rfl

-- @@ L1303-1303 verbatim
theorem meanField_field (k : ℝ) : (A.meanField k).field=A.mean k := rfl


-- @@ L1305-1310 verbatim
theorem parameterSize_one : 1 ≤ A.parameterSize :=
  (A.label.geometry_initial_primitives A.low A.normal A.normal_unit A.coordinates
    A.support A.support_compact A.historyTime A.history_pos A.history_lt A.frame A.geometry
    A.halfBall A.historyTime⁻¹ A.parent.T⁻¹ (A.history_lt.le.trans A.total_le_one) le_rfl
    A.total_le_one le_rfl A.neighborhood A.neighborhood_measurable A.neighborhood_open
    A.support_subset A.neighborhood_bound A.terminal A.delta_pos).1


-- @@ L1312-1327 verbatim
theorem initial_bounds (x : ℝ) (hσ : A.frame.sigma * x ≤ 2) (k : ℝ)
    (hk : 4 ≤ k) (hfrequency : A.frequencyGuard k) (s : ℕ) :
    derivativeSum s (A.high k) ≤
      (A.parent.ell⁻¹)^s*k^s*(EulerPacketInitialAmplitude.boundConstant *
        EulerPacketInitialCost.sourceConstant s *
        A.parameterSize^(EulerPacketInitialAmplitude.degree+EulerPacketInitialCost.sourcePower s)) *
        Real.exp (-x/8) ∧
    derivativeSum s (A.mean k) ≤
      (A.parent.ell⁻¹)^s/k^2*(EulerPacketInitialCost.sourceConstant s *
        A.parameterSize^EulerPacketInitialCost.sourcePower s) :=
  A.label.geometry_initial_bounds A.low A.normal A.normal_unit A.coordinates
    A.support A.support_compact A.historyTime A.history_pos A.history_lt A.frame A.geometry
    A.halfBall A.historyTime⁻¹ A.parent.T⁻¹ (A.history_lt.le.trans A.total_le_one) le_rfl
    A.total_le_one le_rfl A.neighborhood A.neighborhood_measurable A.neighborhood_open
    A.support_subset A.neighborhood_bound A.terminal A.cutoff_support A.delta_pos A.delta_le_one
    A.child_pos x hσ k hk hfrequency s


-- @@ L1329-1336 verbatim
theorem initial_support (k : ℝ) :
    tsupport (A.high k) ⊆ Metric.closedBall 0 2 ∧ tsupport (A.mean k) ⊆ Metric.closedBall 0 2 := by
  apply initializedInitial_common_support A.meanData A.data rfl A.historyTime A.history_pos
      A.history_lt
    A.history A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha ?_ (truncation k) k
  intro x hx
  have hb := A.neighborhood_bound x (A.support_subset hx)
  simpa only [Metric.mem_closedBall,dist_zero_right] using hb


-- @@ L1338-1341 verbatim
/-- Agreement: an abbreviation for `A.parent.sourceAgreement A.normal A.normal_unit
A.coordinates A.support A.support_compact A.low`. -/
abbrev agreement : SourceCoefficientAgreement A.meanData A.data :=
  A.parent.sourceAgreement A.normal A.normal_unit A.coordinates A.support A.support_compact A.low


-- @@ L1343-1357 verbatim
theorem sameQ_initial (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k)
    (Q : Budget period A.data.T_pos
      (initializedCorrectionData A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
          A.history
        A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement (truncation k) hn
            k hk)) :
    scale A.parent.ell
      (initializedExactPhysicalVelocity A.meanData A.data rfl A.historyTime A.history_pos
          A.history_lt
        A.history A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement
        (truncation k) hn k hk Q ⟨0,le_rfl,A.data.T_pos.le⟩ id)=A.high k+A.mean k :=
  initializedExactPhysicalVelocity_initial_split A.meanData A.data rfl A.historyTime A.history_pos
      A.history_lt
    A.history A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement (truncation
        k) hn k hk Q


-- @@ L1359-1359 verbatim
end Input

-- @@ L1360-1360 verbatim
end EulerPacketInitial
