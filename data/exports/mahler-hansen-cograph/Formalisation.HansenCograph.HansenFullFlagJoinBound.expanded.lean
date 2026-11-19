/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenPortalJoinLayer
import Formalisation.HansenCograph.PortalPolynomialNormalizedCorrelation


-- @@ L9-16 verbatim
/-!
# The normalized Hansen full-flag join inequality

This file turns the exact portal-vector convolution and the analytic
correlation inequality into the normalized full-flag inequality.  The
monotonicity hypotheses are kept explicit here; the diamond-switch layer
supplies them for cographs.
-/


-- @@ L18-18 verbatim
open Set SimpleGraph


-- @@ L20-20 verbatim
namespace HansenCograph


-- @@ L22-22 verbatim
universe u v


-- @@ L24-30 verbatim
/-- The full-flag count divided by the conjectured sharp lower bound in the
Hansen dimension `|V| + 1`. -/
noncomputable def hansenFullFlagRatio
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  (hansenFullFlagCount G : ℝ) /
    (2 ^ (Fintype.card V + 1) * ((Fintype.card V + 1).factorial : ℝ))


-- @@ L32-49 verbatim
/-- The normalized full-flag count is the factorial-normalized mass of the
positive portal vector, with the remaining power of two made explicit. -/
theorem hansenFullFlagRatio_eq_portalVector_mass
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hG : UniformFlagCard (HansenCombinatorialFace G)
      (Fintype.card V + 3)) :
    hansenFullFlagRatio G =
      (∑ k ∈ Finset.range (Fintype.card V + 1),
          (HansenCombinatorialFace.hansenPortalVector G k : ℝ)) /
        (2 ^ Fintype.card V *
          ((Fintype.card V + 1).factorial : ℝ)) := by
  rw [hansenFullFlagRatio,
    HansenCombinatorialFace.hansenFullFlagCount_eq_two_mul_positivePortalFlagCount,
    HansenCombinatorialFace.hansenPositivePortalFlagCount_eq_sum_portalVector hG]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  rw [pow_succ]
  ring


-- @@ L51-57 verbatim
/-- Hansen polarity preserves the normalized full-flag count. -/
@[simp] theorem hansenFullFlagRatio_compl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    hansenFullFlagRatio Gᶜ = hansenFullFlagRatio G := by
  unfold hansenFullFlagRatio
  rw [hansenFullFlagCount_compl]


-- @@ L59-163 expanded
/-- Correlation of the two portal polynomials proves normalized
supermultiplicativity at a graph join. -/
theorem hansenFullFlagRatio_join_ge {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : UniformFlagCard (HansenCombinatorialFace A) (Fintype.card V + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (Fintype.card W + 3))
    (hmonoA :
      MonotoneOn
        (portalPolynomial (Fintype.card V)
          (fun k ↦ (HansenCombinatorialFace.hansenPortalVector A k : ℝ)))
        (Icc (0 : ℝ) 1))
    (hmonoB :
      MonotoneOn
        (portalPolynomial (Fintype.card W)
          (fun k ↦ (HansenCombinatorialFace.hansenPortalVector B k : ℝ)))
        (Icc (0 : ℝ) 1)) :
    hansenFullFlagRatio A * hansenFullFlagRatio B ≤ hansenFullFlagRatio (graphJoin A B) := by
  classical
  let n := Fintype.card V
  let m := Fintype.card W
  let a : ℕ → ℝ := fun k ↦ (HansenCombinatorialFace.hansenPortalVector A k : ℝ)
  let b : ℕ → ℝ := fun k ↦ (HansenCombinatorialFace.hansenPortalVector B k : ℝ)
  have hmass :=
    portalShuffleConvolution_mass_normalized_ge (n := n) (m := m) (a := a) (b := b) hmonoA hmonoB
  have hposA := HansenCombinatorialFace.hansenPositivePortalFlagCount_eq_sum_portalVector hA
  have hposB := HansenCombinatorialFace.hansenPositivePortalFlagCount_eq_sum_portalVector hB
  have hjoinUniform : UniformFlagCard (HansenCombinatorialFace (graphJoin A B)) (n + m + 3) :=
    by
    have h := UniformFlagCard.hansenJoin A B hA hB
    have hlen :
      (Fintype.card V + 3) + (Fintype.card W + 3) - 3 = Fintype.card V + Fintype.card W + 3 := by
      omega
    rw [hlen] at h
    exact h
  have hposJoin :=
    HansenCombinatorialFace.hansenPositivePortalFlagCount_eq_sum_portalVector hjoinUniform
  have hconv (s : ℕ) :
    (HansenCombinatorialFace.hansenPortalVector (graphJoin A B) s : ℝ) =
      portalShuffleConvolution n m a b s :=
    by
    exact
      HansenCombinatorialFace.hansenPortalVector_join_cast_eq_portalShuffleConvolution A B hA hB s
  rw [show
      hansenFullFlagRatio A = (∑ k ∈ Finset.range (n + 1), a k) / (2 ^ n * ((n + 1).factorial : ℝ))
      by
      rw [hansenFullFlagRatio,
        HansenCombinatorialFace.hansenFullFlagCount_eq_two_mul_positivePortalFlagCount, hposA]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
      change (2 * ∑ k ∈ Finset.range (n + 1), a k) / (2 ^ (n + 1) * ((n + 1).factorial : ℝ)) = _
      rw [pow_succ]
      ring,
    show
      hansenFullFlagRatio B = (∑ l ∈ Finset.range (m + 1), b l) / (2 ^ m * ((m + 1).factorial : ℝ))
      by
      rw [hansenFullFlagRatio,
        HansenCombinatorialFace.hansenFullFlagCount_eq_two_mul_positivePortalFlagCount, hposB]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
      change (2 * ∑ l ∈ Finset.range (m + 1), b l) / (2 ^ (m + 1) * ((m + 1).factorial : ℝ)) = _
      rw [pow_succ]
      ring,
    show
      hansenFullFlagRatio (graphJoin A B) =
        (∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
          (2 ^ (n + m) * ((n + m + 1).factorial : ℝ))
      by
      rw [hansenFullFlagRatio,
        HansenCombinatorialFace.hansenFullFlagCount_eq_two_mul_positivePortalFlagCount, hposJoin]
      simp only [Fintype.card_sum, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
      simp_rw [hconv]
      change
        (2 * ∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
            (2 ^ (n + m + 1) * ((n + m + 1).factorial : ℝ)) =
          _
      rw [pow_succ]
      ring]
  have hpow : (0 : ℝ) < 2 ^ (n + m) := by positivity
  calc
    ((∑ k ∈ Finset.range (n + 1), a k) / (2 ^ n * ((n + 1).factorial : ℝ))) *
          ((∑ l ∈ Finset.range (m + 1), b l) / (2 ^ m * ((m + 1).factorial : ℝ))) =
        (((∑ k ∈ Finset.range (n + 1), a k) / ((n + 1).factorial : ℝ)) *
            ((∑ l ∈ Finset.range (m + 1), b l) / ((m + 1).factorial : ℝ))) /
          2 ^ (n + m) :=
      by
      rw [pow_add]
      ring
    _ ≤
        ((∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
            ((n + m + 1).factorial : ℝ)) /
          2 ^ (n + m) :=
      (div_le_div_of_nonneg_right hmass hpow.le)
    _ =
        (∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
          (2 ^ (n + m) * ((n + m + 1).factorial : ℝ)) :=
      by ring


-- @@ L165-248 expanded
/-- If both portal vectors increase strictly between their endpoints, then
normalized full-flag supermultiplicativity at the join is strict. -/
theorem hansenFullFlagRatio_join_gt {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : UniformFlagCard (HansenCombinatorialFace A) (Fintype.card V + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (Fintype.card W + 3))
    (hmonoA :
      MonotoneOn
        (portalPolynomial (Fintype.card V)
          (fun k ↦ (HansenCombinatorialFace.hansenPortalVector A k : ℝ)))
        (Icc (0 : ℝ) 1))
    (hmonoB :
      MonotoneOn
        (portalPolynomial (Fintype.card W)
          (fun k ↦ (HansenCombinatorialFace.hansenPortalVector B k : ℝ)))
        (Icc (0 : ℝ) 1))
    (hstrictA :
      HansenCombinatorialFace.hansenPortalVector A 0 <
        HansenCombinatorialFace.hansenPortalVector A (Fintype.card V))
    (hstrictB :
      HansenCombinatorialFace.hansenPortalVector B 0 <
        HansenCombinatorialFace.hansenPortalVector B (Fintype.card W)) :
    hansenFullFlagRatio A * hansenFullFlagRatio B < hansenFullFlagRatio (graphJoin A B) := by
  classical
  let n := Fintype.card V
  let m := Fintype.card W
  let a : ℕ → ℝ := fun k ↦ (HansenCombinatorialFace.hansenPortalVector A k : ℝ)
  let b : ℕ → ℝ := fun k ↦ (HansenCombinatorialFace.hansenPortalVector B k : ℝ)
  have hmass :=
    portalShuffleConvolution_mass_normalized_gt (n := n) (m := m) (a := a) (b := b) hmonoA hmonoB
      (by dsimp [a, n]; exact_mod_cast hstrictA) (by dsimp [b, m]; exact_mod_cast hstrictB)
  have hjoinUniform :
    UniformFlagCard (HansenCombinatorialFace (graphJoin A B)) (Fintype.card (V ⊕ W) + 3) :=
    by
    have h := UniformFlagCard.hansenJoin A B hA hB
    have hlen : (Fintype.card V + 3) + (Fintype.card W + 3) - 3 = Fintype.card (V ⊕ W) + 3 :=
      by
      simp only [Fintype.card_sum]
      omega
    rw [hlen] at h
    exact h
  have hconv (s : ℕ) :
    (HansenCombinatorialFace.hansenPortalVector (graphJoin A B) s : ℝ) =
      portalShuffleConvolution n m a b s :=
    by
    exact
      HansenCombinatorialFace.hansenPortalVector_join_cast_eq_portalShuffleConvolution A B hA hB s
  rw [hansenFullFlagRatio_eq_portalVector_mass A hA, hansenFullFlagRatio_eq_portalVector_mass B hB,
    hansenFullFlagRatio_eq_portalVector_mass (graphJoin A B) hjoinUniform]
  simp only [Fintype.card_sum]
  simp_rw [hconv]
  change
    ((∑ k ∈ Finset.range (n + 1), a k) / (2 ^ n * ((n + 1).factorial : ℝ))) *
        ((∑ l ∈ Finset.range (m + 1), b l) / (2 ^ m * ((m + 1).factorial : ℝ))) <
      (∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
        (2 ^ (n + m) * ((n + m + 1).factorial : ℝ))
  have hpow : (0 : ℝ) < 2 ^ (n + m) := by positivity
  calc
    ((∑ k ∈ Finset.range (n + 1), a k) / (2 ^ n * ((n + 1).factorial : ℝ))) *
          ((∑ l ∈ Finset.range (m + 1), b l) / (2 ^ m * ((m + 1).factorial : ℝ))) =
        (((∑ k ∈ Finset.range (n + 1), a k) / ((n + 1).factorial : ℝ)) *
            ((∑ l ∈ Finset.range (m + 1), b l) / ((m + 1).factorial : ℝ))) /
          2 ^ (n + m) :=
      by
      rw [pow_add]
      ring
    _ <
        ((∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
            ((n + m + 1).factorial : ℝ)) /
          2 ^ (n + m) :=
      (div_lt_div_of_pos_right hmass hpow)
    _ =
        (∑ s ∈ Finset.range (n + m + 1), portalShuffleConvolution n m a b s) /
          (2 ^ (n + m) * ((n + m + 1).factorial : ℝ)) :=
      by ring


-- @@ L250-277 expanded
/-- The union inequality is the join inequality in the polar orientation. -/
theorem hansenFullFlagRatio_sum_ge {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : UniformFlagCard (HansenCombinatorialFace A) (Fintype.card V + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (Fintype.card W + 3))
    (hmonoA :
      MonotoneOn
        (portalPolynomial (Fintype.card V)
          (fun k ↦ (HansenCombinatorialFace.hansenPortalVector Aᶜ k : ℝ)))
        (Icc (0 : ℝ) 1))
    (hmonoB :
      MonotoneOn
        (portalPolynomial (Fintype.card W)
          (fun k ↦ (HansenCombinatorialFace.hansenPortalVector Bᶜ k : ℝ)))
        (Icc (0 : ℝ) 1)) :
    hansenFullFlagRatio A * hansenFullFlagRatio B ≤ hansenFullFlagRatio (A ⊕g B) :=
  by
  have hAc := UniformFlagCard.hansenCompl A hA
  have hBc := UniformFlagCard.hansenCompl B hB
  calc
    hansenFullFlagRatio A * hansenFullFlagRatio B =
        hansenFullFlagRatio Aᶜ * hansenFullFlagRatio Bᶜ :=
      by simp
    _ ≤ hansenFullFlagRatio (graphJoin Aᶜ Bᶜ) :=
      (hansenFullFlagRatio_join_ge Aᶜ Bᶜ hAc hBc hmonoA hmonoB)
    _ = hansenFullFlagRatio (A ⊕g B) := by rw [← compl_sum_eq_join, hansenFullFlagRatio_compl]


-- @@ L279-311 expanded
/-- Strictness at a union follows when both complementary portal vectors
increase strictly between their endpoints. -/
theorem hansenFullFlagRatio_sum_gt {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : UniformFlagCard (HansenCombinatorialFace A) (Fintype.card V + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (Fintype.card W + 3))
    (hmonoA :
      MonotoneOn
        (portalPolynomial (Fintype.card V)
          (fun k ↦ (HansenCombinatorialFace.hansenPortalVector Aᶜ k : ℝ)))
        (Icc (0 : ℝ) 1))
    (hmonoB :
      MonotoneOn
        (portalPolynomial (Fintype.card W)
          (fun k ↦ (HansenCombinatorialFace.hansenPortalVector Bᶜ k : ℝ)))
        (Icc (0 : ℝ) 1))
    (hstrictA :
      HansenCombinatorialFace.hansenPortalVector Aᶜ 0 <
        HansenCombinatorialFace.hansenPortalVector Aᶜ (Fintype.card V))
    (hstrictB :
      HansenCombinatorialFace.hansenPortalVector Bᶜ 0 <
        HansenCombinatorialFace.hansenPortalVector Bᶜ (Fintype.card W)) :
    hansenFullFlagRatio A * hansenFullFlagRatio B < hansenFullFlagRatio (A ⊕g B) :=
  by
  have hAc := UniformFlagCard.hansenCompl A hA
  have hBc := UniformFlagCard.hansenCompl B hB
  calc
    hansenFullFlagRatio A * hansenFullFlagRatio B =
        hansenFullFlagRatio Aᶜ * hansenFullFlagRatio Bᶜ :=
      by simp
    _ < hansenFullFlagRatio (graphJoin Aᶜ Bᶜ) :=
      (hansenFullFlagRatio_join_gt Aᶜ Bᶜ hAc hBc hmonoA hmonoB hstrictA hstrictB)
    _ = hansenFullFlagRatio (A ⊕g B) := by rw [← compl_sum_eq_join, hansenFullFlagRatio_compl]


-- @@ L313-313 verbatim
end HansenCograph
