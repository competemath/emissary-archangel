/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Star.Real
meta import Lean.Meta.Tactic.NormCast
import Mathlib.Tactic.Bound


-- @@ L14-14 verbatim
/-! The actual continuous time weights for the high and mean packet grades. -/


-- @@ L16-16 verbatim
section


-- @@ L18-18 verbatim
/-! Exact time-profile bookkeeping for the high, mean, and previous-corrector terms. -/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace EulerPacketTimeProfile


-- @@ L24-25 verbatim
/-- Mean scale, given by `H^(2*p-2)`. -/
def meanScale (H : ℝ) (p : ℕ) : ℝ := H^(2*p-2)

-- @@ L26-27 verbatim
/-- High scale, given by `γ*meanScale H p`. -/
def highScale (γ H : ℝ) (p : ℕ) : ℝ := γ*meanScale H p


-- @@ L29-29 verbatim
theorem meanScale_pos (H : ℝ) (hH : 0 < H) (p : ℕ) : 0 < meanScale H p := pow_pos hH _

-- @@ L30-31 verbatim
theorem highScale_pos (γ H : ℝ) (hγ : 0 < γ) (hH : 0 < H) (p : ℕ) :
    0 < highScale γ H p := mul_pos hγ (meanScale_pos H hH p)


-- @@ L33-35 verbatim
theorem meanScale_mono (H : ℝ) (hH : 1 ≤ H) {i j : ℕ} (hij : i ≤ j) :
    meanScale H i ≤ meanScale H j :=
  pow_le_pow_right₀ hH (by omega : 2*i-2 ≤ 2*j-2)


-- @@ L37-39 verbatim
theorem highScale_mono (γ H : ℝ) (hγ : 0 ≤ γ) (hH : 1 ≤ H) {i j : ℕ} (hij : i ≤ j) :
    highScale γ H i ≤ highScale γ H j :=
  mul_le_mul_of_nonneg_left (meanScale_mono H hH hij) hγ


-- @@ L41-46 verbatim
theorem meanScale_slow_identity (H : ℝ) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*meanScale H j*H^2 = meanScale H p := by
  simp only [meanScale,← pow_add]
  congr 1
  omega


-- @@ L48-56 verbatim
theorem slow_mean_mean (H : ℝ) (hH : 1 ≤ H) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*meanScale H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hs : (1 : ℝ) ≤ H^2 := by nlinarith
  calc
    _ ≤ (meanScale H i*meanScale H j)*H^2 :=
      le_mul_of_one_le_right (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _)) hs
    _ = _ := meanScale_slow_identity H i j p hi hj hp


-- @@ L58-68 verbatim
theorem slow_high_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    highScale γ H i*highScale γ H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  calc
    _ = γ^2*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ H^2*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hγ hγH 2)
        (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = meanScale H i*meanScale H j*H^2 := by ring
    _ = _ := meanScale_slow_identity H i j p hi hj hp


-- @@ L70-81 verbatim
theorem slow_high_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    highScale γ H i*highScale γ H j ≤ highScale γ H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hh : H ≤ H^2 := by nlinarith
  have hγ2 : γ^2 ≤ γ*H^2 := by nlinarith [mul_nonneg hγ (sub_nonneg.mpr (hγH.trans hh))]
  calc
    _ = γ^2*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ (γ*H^2)*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right hγ2 (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = γ*(meanScale H i*meanScale H j*H^2) := by ring
    _ = _ := congrArg (γ * ·) (meanScale_slow_identity H i j p hi hj hp)


-- @@ L83-87 verbatim
theorem slow_mean_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*highScale γ H j ≤ highScale γ H p := by
  have h := mul_le_mul_of_nonneg_left (slow_mean_mean H hH i j p hi hj hp) hγ
  simpa only [highScale,mul_left_comm] using h


-- @@ L89-99 verbatim
theorem slow_mean_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) :
    meanScale H i*highScale γ H j ≤ meanScale H p := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hh : γ ≤ H^2 := by nlinarith
  calc
    _ = γ*(meanScale H i*meanScale H j) := by unfold highScale; ring
    _ ≤ H^2*(meanScale H i*meanScale H j) :=
      mul_le_mul_of_nonneg_right hh (mul_nonneg (pow_nonneg hH0 _) (pow_nonneg hH0 _))
    _ = meanScale H i*meanScale H j*H^2 := by ring
    _ = _ := meanScale_slow_identity H i j p hi hj hp


-- @@ L101-108 verbatim
theorem fast_mean_high (γ H : ℝ) (i j p : ℕ)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    meanScale H i*highScale γ H j = highScale γ H p := by
  unfold highScale meanScale
  rw [mul_left_comm,← pow_add]
  congr 1
  congr 1
  omega


-- @@ L110-113 verbatim
theorem fast_corrector_high_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H j ≤ meanScale H p :=
  slow_high_high_mean γ H hγ hγH hH (i-1) j p (by omega) hj (by omega)


-- @@ L115-118 verbatim
theorem fast_corrector_high_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H j ≤ highScale γ H p :=
  slow_high_high_high γ H hγ hγH hH (i-1) j p (by omega) hj (by omega)


-- @@ L120-124 verbatim
theorem fast_corrector_corrector_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H (j-1) ≤ meanScale H p :=
  (slow_high_high_mean γ H hγ hγH hH (i-1) (j-1) (p-1) (by omega) (by omega) (by omega)).trans
    (meanScale_mono H hH (Nat.sub_le p 1))


-- @@ L126-130 verbatim
theorem fast_corrector_corrector_high (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i + j = p + 1) :
    highScale γ H (i-1)*highScale γ H (j-1) ≤ highScale γ H p :=
  (slow_high_high_high γ H hγ hγH hH (i-1) (j-1) (p-1) (by omega) (by omega) (by omega)).trans
    (highScale_mono γ H hγ hH (Nat.sub_le p 1))


-- @@ L132-135 verbatim
theorem previous_linear_mean (γ H : ℝ) (hγ : 0 ≤ γ) (hγH : γ ≤ H) (hH : 1 ≤ H)
    (p : ℕ) (hp : 2 ≤ p) : highScale γ H (p-1) ≤ meanScale H p := by
  have h := slow_mean_high_mean γ H hγ hγH hH 1 (p-1) p (by omega) (by omega) (by omega)
  simpa only [meanScale,show 2*1-2=0 by omega,pow_zero,one_mul] using h


-- @@ L137-137 verbatim
end EulerPacketTimeProfile


-- @@ L139-139 verbatim
end


-- @@ L141-141 verbatim
end


-- @@ L143-143 verbatim
@[expose] public section


-- @@ L145-145 verbatim
noncomputable section


-- @@ L147-147 verbatim
namespace EulerPacketTimeProfile


-- @@ L149-149 verbatim
open Set


-- @@ L151-151 verbatim
variable (K : Type*) [TopologicalSpace K]


-- @@ L153-161 verbatim
/-- Scales data, collecting `growth`, `growth_pos`, `H0`, `H0_one_le`, `growth_le`. -/
structure Scales where
  /-- Growth of `Scales`, of type `C(K,ℝ)`. -/
  growth : C(K,ℝ)
  growth_pos : ∀ t, 0 < growth t
  /-- H0 of `Scales`, of type `ℝ`. -/
  H0 : ℝ
  H0_one_le : 1 ≤ H0
  growth_le : ∀ t, growth t ≤ H0


-- @@ L163-163 verbatim
namespace Scales


-- @@ L165-165 verbatim
variable {K}


-- @@ L167-174 verbatim
/-- Compactness supplies the single grade-independent upper scale. -/
def ofGrowth [CompactSpace K] (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) : Scales K where
  growth := g
  growth_pos := hg
  H0 := max 1 ‖g‖
  H0_one_le := le_max_left _ _
  growth_le t := (le_trans (le_abs_self (g t))
    (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm t)).trans (le_max_right _ _)


-- @@ L176-176 verbatim
variable (S : Scales K)


-- @@ L178-179 verbatim
/-- Mean, given by `ContinuousMap.const K (meanScale S.H0 p)`. -/
def mean (p : ℕ) : C(K,ℝ) := ContinuousMap.const K (meanScale S.H0 p)

-- @@ L180-181 verbatim
/-- High, given by `S.growth*S.mean p`. -/
def high (p : ℕ) : C(K,ℝ) := S.growth*S.mean p


-- @@ L183-183 verbatim
@[simp] theorem mean_apply (p : ℕ) (t : K) : S.mean p t = meanScale S.H0 p := rfl

-- @@ L184-184 verbatim
@[simp] theorem high_apply (p : ℕ) (t : K) : S.high p t = highScale (S.growth t) S.H0 p := rfl


-- @@ L186-186 verbatim
theorem H0_pos : 0 < S.H0 := zero_lt_one.trans_le S.H0_one_le

-- @@ L187-187 verbatim
theorem mean_pos (p : ℕ) (t : K) : 0 < S.mean p t := meanScale_pos S.H0 S.H0_pos p

-- @@ L188-189 verbatim
theorem high_pos (p : ℕ) (t : K) : 0 < S.high p t :=
  highScale_pos (S.growth t) S.H0 (S.growth_pos t) S.H0_pos p


-- @@ L191-192 verbatim
theorem mean_mono {i j : ℕ} (hij : i ≤ j) (t : K) : S.mean i t ≤ S.mean j t :=
  meanScale_mono S.H0 S.H0_one_le hij


-- @@ L194-195 verbatim
theorem high_mono {i j : ℕ} (hij : i ≤ j) (t : K) : S.high i t ≤ S.high j t :=
  highScale_mono (S.growth t) S.H0 (S.growth_pos t).le S.H0_one_le hij


-- @@ L197-198 verbatim
theorem high_one (t : K) : S.high 1 t = S.growth t := by
  simp only [high_apply,highScale,meanScale,show 2*1-2=0 by omega,pow_zero,mul_one]


-- @@ L200-201 verbatim
theorem slow_mean_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.mean j t ≤ S.mean p t := slow_mean_mean S.H0 S.H0_one_le i j p hi hj hp


-- @@ L203-206 verbatim
theorem slow_high_high_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.high i t*S.high j t ≤ S.mean p t :=
  slow_high_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp


-- @@ L208-211 verbatim
theorem slow_high_high_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.high i t*S.high j t ≤ S.high p t :=
  slow_high_high_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp


-- @@ L213-216 verbatim
theorem slow_mean_high_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.high j t ≤ S.mean p t :=
  slow_mean_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp


-- @@ L218-220 verbatim
theorem slow_mean_high_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.high j t ≤ S.high p t :=
  slow_mean_high_high (S.growth t) S.H0 (S.growth_pos t).le S.H0_one_le i j p hi hj hp


-- @@ L222-224 verbatim
theorem fast_mean_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) (t : K) :
    S.mean i t*S.high j t = S.high p t :=
  fast_mean_high (S.growth t) S.H0 i j p hi hj hp


-- @@ L226-229 verbatim
theorem fast_corrector_high_mean_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high j t ≤ S.mean p t :=
  fast_corrector_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp


-- @@ L231-234 verbatim
theorem fast_corrector_high_high_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high j t ≤ S.high p t :=
  fast_corrector_high_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp


-- @@ L236-239 verbatim
theorem fast_corrector_corrector_mean_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high (j-1) t ≤ S.mean p t :=
  fast_corrector_corrector_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp


-- @@ L241-244 verbatim
theorem fast_corrector_corrector_high_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high (j-1) t ≤ S.high p t :=
  fast_corrector_corrector_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp


-- @@ L246-247 verbatim
theorem previous_linear_mean_bound (p : ℕ) (hp : 2 ≤ p) (t : K) : S.high (p-1) t ≤ S.mean p t :=
  previous_linear_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le p hp


-- @@ L249-249 verbatim
end Scales

-- @@ L250-250 verbatim
end EulerPacketTimeProfile
