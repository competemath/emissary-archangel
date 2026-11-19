/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.Section
import Formalisation.Mathlib.Analysis.Convex.JoinVolume
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


-- @@ L11-11 verbatim
set_option linter.unusedSectionVars false

-- @@ L12-12 verbatim
set_option linter.unusedFintypeInType false

-- @@ L13-13 verbatim
set_option linter.unusedDecidableInType false


-- @@ L15-15 verbatim
open scoped BigOperators Pointwise

-- @@ L16-16 verbatim
open Set

-- @@ L17-17 verbatim
open MeasureTheory

-- @@ L18-18 verbatim
open SimpleGraph


-- @@ L20-20 verbatim
universe u v w


-- @@ L22-22 verbatim
namespace HansenCograph


-- @@ L24-26 verbatim
/-!
## N(G) and Beta-integral normalization
-/


-- @@ L28-28 verbatim
section NInvariant


-- @@ L30-30 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L32-39 verbatim
/--
Orthant-normalized Hansen volume invariant

    N(G) = 2 * sum_S nu(G[S]) nu(G[Sᶜ]).
-/
noncomputable def N (G : SimpleGraph V) : ℝ :=
  2 * ∑ s ∈ Finset.univ.powerset,
    nuInduced G s * nuInduced G sᶜ


-- @@ L41-48 verbatim
theorem N_nonneg (G : SimpleGraph V) :
    0 ≤ N G := by
  classical
  unfold N
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (nu_nonneg _) (nu_nonneg _)


-- @@ L50-67 verbatim
theorem N_pos (G : SimpleGraph V) :
    0 < N G := by
  classical
  have hterm :
      0 < nuInduced G ∅ * nuInduced G (∅ : Finset V)ᶜ :=
    mul_pos (nu_pos _) (nu_pos _)
  have hle :
      nuInduced G ∅ * nuInduced G (∅ : Finset V)ᶜ ≤
        ∑ s ∈ Finset.univ.powerset,
          nuInduced G s * nuInduced G sᶜ := by
    apply Finset.single_le_sum
      (s := Finset.univ.powerset)
      (f := fun s => nuInduced G s * nuInduced G sᶜ)
    · intro s hs
      exact mul_nonneg (nu_nonneg _) (nu_nonneg _)
    · simp
  unfold N
  nlinarith


-- @@ L69-104 verbatim
/-- Beta integral for integer exponents. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b)
      =
    (a.factorial : ℝ) * (b.factorial : ℝ) /
      ((a + b + 1).factorial : ℝ) := by
  apply Complex.ofReal_injective
  conv_lhs => rw [← intervalIntegral.integral_ofReal]
  have h : 0 < ((b : ℂ) + 1).re := by
    simp
    linarith
  calc
    (∫ x in (0 : ℝ)..1,
        ((x ^ a * (1 - x) ^ b : ℝ) : ℂ)) =
        Complex.betaIntegral ((a : ℂ) + 1) ((b : ℂ) + 1) := by
      rw [Complex.betaIntegral]
      apply intervalIntegral.integral_congr
      intro x hx
      simp [Complex.ofReal_pow]
    _ = Complex.Gamma ((a : ℂ) + 1) * Complex.Gamma ((b : ℂ) + 1) /
        Complex.Gamma (((a : ℂ) + 1) + ((b : ℂ) + 1)) := by
      exact Complex.betaIntegral_eq_Gamma_mul_div _ _
        (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity) h
    _ = ((a.factorial : ℝ) * (b.factorial : ℝ) /
        ((a + b + 1).factorial : ℝ) : ℂ) := by
      have hab : ((a : ℂ) + 1) + ((b : ℂ) + 1) =
          ((a + b + 1 : ℕ) : ℂ) + 1 := by
        push_cast
        ring
      rw [Complex.Gamma_nat_eq_factorial a,
        Complex.Gamma_nat_eq_factorial b, hab,
        Complex.Gamma_nat_eq_factorial (a + b + 1)]
      push_cast
      rfl
  push_cast
  rfl


-- @@ L106-140 verbatim
/--
Exactly normalized identity

    N(G) = 2 (m+1)! ∫_0^1 q_G(x) dx.
-/
theorem N_eq_two_factorial_mul_integral_q (G : SimpleGraph V) :
    N G =
      2 * ((Fintype.card V + 1).factorial : ℝ) *
        (∫ x in (0 : ℝ)..1, q G x) := by
  classical
  unfold N q qCoeff
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [mul_assoc]
    simp_rw [intervalIntegral.integral_const_mul]
    simp_rw [integral_pow_mul_one_sub_pow]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hsle : s.card ≤ Fintype.card V := Finset.card_le_univ s
    have hsum : s.card + (Fintype.card V - s.card) + 1 =
        Fintype.card V + 1 := by
      omega
    rw [hsum]
    have hsf : (s.card.factorial : ℝ) ≠ 0 := by positivity
    have hcf : ((Fintype.card V - s.card).factorial : ℝ) ≠ 0 := by positivity
    have hmf : ((Fintype.card V + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · intro s hs
    exact (by fun_prop : Continuous (fun x : ℝ =>
      nuInduced G s * nuInduced G sᶜ /
          ((s.card.factorial : ℝ) *
            ((Fintype.card V - s.card).factorial : ℝ)) *
        x ^ s.card * (1 - x) ^ (Fintype.card V - s.card))).intervalIntegrable
          (μ := volume) 0 1


-- @@ L142-148 verbatim
theorem integral_q_pos (G : SimpleGraph V) :
    0 < ∫ x in (0 : ℝ)..1, q G x := by
  have hN := N_pos G
  rw [N_eq_two_factorial_mul_integral_q] at hN
  have hfac : 0 < ((Fintype.card V + 1).factorial : ℝ) := by
    positivity
  nlinarith


-- @@ L150-150 verbatim
end NInvariant


-- @@ L152-172 verbatim
/-!
## Disjoint union and join identities

The mathematical identities are

  q_{A ⊔ B} = q_A q_B

and

  N(A ∨ B) = N(A)N(B)/2.

The normalized stable-volume primitives behind them are:

  nu(A ⊔ B)
    = binom(a+b,a) nu(A)nu(B),

  nu(A ∨ B)
    = nu(A)nu(B).

The first comes from Cartesian products; the second from free sums.
-/


-- @@ L174-174 verbatim
section UnionJoin


-- @@ L176-176 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]

-- @@ L177-177 verbatim
variable {W : Type v} [Fintype W] [DecidableEq W]


-- @@ L179-187 verbatim
/-- Split coordinates indexed by a sum into its two coordinate blocks. -/
def sumCoordinateSplit :
    ((V ⊕ W) → ℝ) ≃ₗ[ℝ] ((V → ℝ) × (W → ℝ)) where
  toFun x := (fun v => x (.inl v), fun w => x (.inr w))
  invFun p := Sum.elim p.1 p.2
  left_inv x := by ext z; cases z <;> rfl
  right_inv p := by ext z <;> rfl
  map_add' x y := by ext z <;> rfl
  map_smul' a x := by ext z <;> rfl


-- @@ L189-191 verbatim
/-- The vertices in the left summand of a finite set on a sum type. -/
noncomputable def sumLeftPart (s : Finset (V ⊕ W)) : Finset V :=
  s.preimage Sum.inl Sum.inl_injective.injOn


-- @@ L193-195 verbatim
/-- The vertices in the right summand of a finite set on a sum type. -/
noncomputable def sumRightPart (s : Finset (V ⊕ W)) : Finset W :=
  s.preimage Sum.inr Sum.inr_injective.injOn


-- @@ L197-200 verbatim
/-- Combine finite sets in the two summands. -/
def sumFinset (s : Finset V) (t : Finset W) : Finset (V ⊕ W) :=
  s.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    t.map ⟨Sum.inr, Sum.inr_injective⟩


-- @@ L202-205 verbatim
@[simp]
theorem mem_sumLeftPart (s : Finset (V ⊕ W)) (v : V) :
    v ∈ sumLeftPart s ↔ Sum.inl v ∈ s := by
  simp [sumLeftPart]


-- @@ L207-210 verbatim
@[simp]
theorem mem_sumRightPart (s : Finset (V ⊕ W)) (w : W) :
    w ∈ sumRightPart s ↔ Sum.inr w ∈ s := by
  simp [sumRightPart]


-- @@ L212-215 verbatim
@[simp]
theorem inl_mem_sumFinset (s : Finset V) (t : Finset W) (v : V) :
    Sum.inl v ∈ sumFinset s t ↔ v ∈ s := by
  simp [sumFinset]


-- @@ L217-220 verbatim
@[simp]
theorem inr_mem_sumFinset (s : Finset V) (t : Finset W) (w : W) :
    Sum.inr w ∈ sumFinset s t ↔ w ∈ t := by
  simp [sumFinset]


-- @@ L222-229 verbatim
theorem sum_left_indep (A : SimpleGraph V) (B : SimpleGraph W)
    {s : Finset (V ⊕ W)}
    (hs : (A ⊕g B).IsIndepSet (↑s : Set (V ⊕ W))) :
    A.IsIndepSet (↑(sumLeftPart s) : Set V) := by
  intro u hu v hv huv hadj
  exact hs (by simpa using hu) (by simpa using hv)
    (fun h => huv (Sum.inl_injective h))
    (by simpa [SimpleGraph.sum_adj] using hadj)


-- @@ L231-238 verbatim
theorem sum_right_indep (A : SimpleGraph V) (B : SimpleGraph W)
    {s : Finset (V ⊕ W)}
    (hs : (A ⊕g B).IsIndepSet (↑s : Set (V ⊕ W))) :
    B.IsIndepSet (↑(sumRightPart s) : Set W) := by
  intro u hu v hv huv hadj
  exact hs (by simpa using hu) (by simpa using hv)
    (fun h => huv (Sum.inr_injective h))
    (by simpa [SimpleGraph.sum_adj] using hadj)


-- @@ L240-262 verbatim
theorem sumFinset_indep (A : SimpleGraph V) (B : SimpleGraph W)
    {s : Finset V} {t : Finset W}
    (hs : A.IsIndepSet (↑s : Set V))
    (ht : B.IsIndepSet (↑t : Set W)) :
    (A ⊕g B).IsIndepSet (↑(sumFinset s t) : Set (V ⊕ W)) := by
  intro x hx y hy hxy
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          intro hadj
          exact hs (by simpa using hx) (by simpa using hy)
            (fun h => hxy (congrArg Sum.inl h))
            (by simpa [SimpleGraph.sum_adj] using hadj)
      | inr w => simp [SimpleGraph.sum_adj]
  | inr u =>
      cases y with
      | inl v => simp [SimpleGraph.sum_adj]
      | inr w =>
          intro hadj
          exact ht (by simpa using hx) (by simpa using hy)
            (fun h => hxy (congrArg Sum.inr h))
            (by simpa [SimpleGraph.sum_adj] using hadj)


-- @@ L264-267 verbatim
theorem sumCoordinateSplit_indicator (s : Finset (V ⊕ W)) :
    sumCoordinateSplit (indicator s) =
      (indicator (sumLeftPart s), indicator (sumRightPart s)) := by
  ext z <;> simp [sumCoordinateSplit, indicator]


-- @@ L269-273 verbatim
theorem sumCoordinateSplit_sumFinset_indicator
    (s : Finset V) (t : Finset W) :
    sumCoordinateSplit (indicator (sumFinset s t)) =
      (indicator s, indicator t) := by
  ext z <;> simp [sumCoordinateSplit, indicator]


-- @@ L275-292 verbatim
theorem sumCoordinateSplit_image_stableIndicators
    (A : SimpleGraph V) (B : SimpleGraph W) :
    sumCoordinateSplit '' stableIndicators (A ⊕g B) =
      stableIndicators A ×ˢ stableIndicators B := by
  ext p
  constructor
  · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
    rw [sumCoordinateSplit_indicator]
    exact ⟨⟨sumLeftPart s, sum_left_indep A B hs, rfl⟩,
      ⟨sumRightPart s, sum_right_indep A B hs, rfl⟩⟩
  · rcases p with ⟨x, y⟩
    rintro ⟨⟨s, hs, hx⟩, ⟨t, ht, hy⟩⟩
    change (x, y) ∈ sumCoordinateSplit '' stableIndicators (A ⊕g B)
    dsimp at hx hy
    rw [hx, hy]
    refine ⟨indicator (sumFinset s t), ?_, ?_⟩
    · exact ⟨sumFinset s t, sumFinset_indep A B hs ht, rfl⟩
    · exact sumCoordinateSplit_sumFinset_indicator s t


-- @@ L294-306 verbatim
theorem sumCoordinateSplit_image_stab
    (A : SimpleGraph V) (B : SimpleGraph W) :
    sumCoordinateSplit '' stab (A ⊕g B) = stab A ×ˢ stab B := by
  unfold stab
  calc
    sumCoordinateSplit '' convexHull ℝ (stableIndicators (A ⊕g B)) =
        convexHull ℝ (sumCoordinateSplit '' stableIndicators (A ⊕g B)) :=
      LinearMap.image_convexHull sumCoordinateSplit.toLinearMap _
    _ = convexHull ℝ (stableIndicators A ×ˢ stableIndicators B) := by
      rw [sumCoordinateSplit_image_stableIndicators]
    _ = convexHull ℝ (stableIndicators A) ×ˢ
        convexHull ℝ (stableIndicators B) :=
      convexHull_prod _ _


-- @@ L308-314 verbatim
theorem sumCoordinateSplit_measurePreserving :
    MeasurePreserving (sumCoordinateSplit : ((V ⊕ W) → ℝ) →
      ((V → ℝ) × (W → ℝ))) := by
  simpa [sumCoordinateSplit, MeasurableEquiv.sumPiEquivProdPi,
    Equiv.sumPiEquivProdPi] using
      (volume_measurePreserving_sumPiEquivProdPi
        (fun _ : V ⊕ W => ℝ))


-- @@ L316-329 verbatim
theorem stab_sum_eq_split_preimage (A : SimpleGraph V) (B : SimpleGraph W) :
    stab (A ⊕g B) =
      (sumCoordinateSplit : ((V ⊕ W) → ℝ) →
        ((V → ℝ) × (W → ℝ))) ⁻¹' (stab A ×ˢ stab B) := by
  ext x
  constructor
  · intro hx
    rw [← sumCoordinateSplit_image_stab A B]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← sumCoordinateSplit_image_stab A B] at hx
    rcases hx with ⟨y, hy, hxy⟩
    have : y = x := sumCoordinateSplit.injective hxy
    simpa [this] using hy


-- @@ L331-337 verbatim
theorem volume_stab_sum (A : SimpleGraph V) (B : SimpleGraph W) :
    volume (stab (A ⊕g B)) = volume (stab A) * volume (stab B) := by
  have hpre := sumCoordinateSplit_measurePreserving.measure_preimage_emb
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : V ⊕ W => ℝ)).measurableEmbedding (stab A ×ˢ stab B)
  rw [stab_sum_eq_split_preimage A B]
  rw [hpre, Measure.volume_eq_prod, Measure.prod_prod]


-- @@ L339-354 verbatim
theorem nu_sum (A : SimpleGraph V) (B : SimpleGraph W) :
    nu (A ⊕g B)
      =
    (Nat.choose (Fintype.card V + Fintype.card W) (Fintype.card V) : ℝ) *
      nu A * nu B := by
  have hfac :
      (((Fintype.card V + Fintype.card W).factorial : ℕ) : ℝ) =
        (Nat.choose (Fintype.card V + Fintype.card W)
            (Fintype.card V) : ℝ) *
          (Fintype.card V).factorial * (Fintype.card W).factorial := by
    norm_cast
    simpa using (Nat.choose_mul_factorial_mul_factorial
      (show Fintype.card V ≤ Fintype.card V + Fintype.card W by omega)).symm
  unfold nu
  rw [Fintype.card_sum, volume_stab_sum, ENNReal.toReal_mul, hfac]
  ring


-- @@ L356-357 verbatim
/-- Embed the left coordinate space as the left axis of the product. -/
def productAxisLeft (x : V → ℝ) : (V → ℝ) × (W → ℝ) := (x, 0)


-- @@ L359-360 verbatim
/-- Embed the right coordinate space as the right axis of the product. -/
def productAxisRight (y : W → ℝ) : (V → ℝ) × (W → ℝ) := (0, y)


-- @@ L362-365 verbatim
def productAxisLeftLinear : (V → ℝ) →ₗ[ℝ] ((V → ℝ) × (W → ℝ)) where
  toFun := productAxisLeft
  map_add' x y := by ext <;> simp [productAxisLeft]
  map_smul' a x := by ext <;> simp [productAxisLeft]


-- @@ L367-370 verbatim
def productAxisRightLinear : (W → ℝ) →ₗ[ℝ] ((V → ℝ) × (W → ℝ)) where
  toFun := productAxisRight
  map_add' x y := by ext <;> simp [productAxisRight]
  map_smul' a x := by ext <;> simp [productAxisRight]


-- @@ L372-382 expanded
@[simp]
theorem graphJoin_adj_inl_inl (A : SimpleGraph V) (B : SimpleGraph W) (u v : V) :
    (graphJoin A B).Adj (.inl u) (.inl v) ↔ A.Adj u v :=
  by
  simp only [graphJoin, SimpleGraph.compl_adj, ne_eq, SimpleGraph.sum_adj, Sum.inl.injEq]
  constructor
  · rintro ⟨huv, h⟩
    by_contra hn
    exact h ⟨huv, hn⟩
  · intro hadj
    exact ⟨hadj.ne, fun h => h.2 hadj⟩


-- @@ L384-394 expanded
@[simp]
theorem graphJoin_adj_inr_inr (A : SimpleGraph V) (B : SimpleGraph W) (u v : W) :
    (graphJoin A B).Adj (.inr u) (.inr v) ↔ B.Adj u v :=
  by
  simp only [graphJoin, SimpleGraph.compl_adj, ne_eq, SimpleGraph.sum_adj, Sum.inr.injEq]
  constructor
  · rintro ⟨huv, h⟩
    by_contra hn
    exact h ⟨huv, hn⟩
  · intro hadj
    exact ⟨hadj.ne, fun h => h.2 hadj⟩


-- @@ L396-400 expanded
@[simp]
theorem graphJoin_adj_inl_inr (A : SimpleGraph V) (B : SimpleGraph W) (u : V) (w : W) :
    (graphJoin A B).Adj (.inl u) (.inr w) :=
  by
  simp only [graphJoin, SimpleGraph.compl_adj, SimpleGraph.sum_adj, not_false_eq_true]
  exact ⟨Sum.inl_ne_inr, trivial⟩


-- @@ L402-405 expanded
@[simp]
theorem graphJoin_adj_inr_inl (A : SimpleGraph V) (B : SimpleGraph W) (w : W) (u : V) :
    (graphJoin A B).Adj (.inr w) (.inl u) :=
  (graphJoin_adj_inl_inr A B u w).symm


-- @@ L407-413 expanded
theorem join_left_indep (A : SimpleGraph V) (B : SimpleGraph W) {s : Finset (V ⊕ W)}
    (hs : (graphJoin A B).IsIndepSet (↑s : Set (V ⊕ W))) :
    A.IsIndepSet (↑(sumLeftPart s) : Set V) :=
  by
  intro u hu v hv huv hadj
  exact
    hs (by simpa using hu) (by simpa using hv) (fun h => huv (Sum.inl_injective h))
      (by simpa using hadj)


-- @@ L415-421 expanded
theorem join_right_indep (A : SimpleGraph V) (B : SimpleGraph W) {s : Finset (V ⊕ W)}
    (hs : (graphJoin A B).IsIndepSet (↑s : Set (V ⊕ W))) :
    B.IsIndepSet (↑(sumRightPart s) : Set W) :=
  by
  intro u hu v hv huv hadj
  exact
    hs (by simpa using hu) (by simpa using hv) (fun h => huv (Sum.inr_injective h))
      (by simpa using hadj)


-- @@ L423-432 expanded
theorem join_indep_right_empty (A : SimpleGraph V) (B : SimpleGraph W) {s : Finset (V ⊕ W)}
    (hs : (graphJoin A B).IsIndepSet (↑s : Set (V ⊕ W))) (hl : sumLeftPart s ≠ ∅) :
    sumRightPart s = ∅ := by
  ext w
  simp only [Finset.notMem_empty, iff_false]
  intro hw
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hl
  exact hs (by simpa using hu) (by simpa using hw) Sum.inl_ne_inr (graphJoin_adj_inl_inr A B u w)


-- @@ L434-447 expanded
theorem join_sumFinset_left_indep (A : SimpleGraph V) (B : SimpleGraph W) {s : Finset V}
    (hs : A.IsIndepSet (↑s : Set V)) :
    (graphJoin A B).IsIndepSet (↑(sumFinset s (∅ : Finset W)) : Set (V ⊕ W)) :=
  by
  intro x hx y hy hxy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      intro hadj
      exact
        hs (by simpa using hx) (by simpa using hy) (fun h => hxy (congrArg Sum.inl h))
          (by simpa using hadj)
    | inr w => simp at hy
  | inr u => simp at hx


-- @@ L449-462 expanded
theorem join_sumFinset_right_indep (A : SimpleGraph V) (B : SimpleGraph W) {t : Finset W}
    (ht : B.IsIndepSet (↑t : Set W)) :
    (graphJoin A B).IsIndepSet (↑(sumFinset (∅ : Finset V) t) : Set (V ⊕ W)) :=
  by
  intro x hx y hy hxy
  cases x with
  | inl u => simp at hx
  | inr u =>
    cases y with
    | inl v => simp at hy
    | inr w =>
      intro hadj
      exact
        ht (by simpa using hx) (by simpa using hy) (fun h => hxy (congrArg Sum.inr h))
          (by simpa using hadj)


-- @@ L464-491 expanded
theorem sumCoordinateSplit_image_stableIndicators_join (A : SimpleGraph V) (B : SimpleGraph W) :
    sumCoordinateSplit '' stableIndicators (graphJoin A B) =
      (productAxisLeft '' stableIndicators A) ∪ (productAxisRight '' stableIndicators B) :=
  by
  ext p
  constructor
  · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
    rw [sumCoordinateSplit_indicator]
    by_cases hl : sumLeftPart s = ∅
    · right
      refine ⟨indicator (sumRightPart s), ⟨sumRightPart s, join_right_indep A B hs, rfl⟩, ?_⟩
      simp [productAxisRight, hl]
    · left
      have hr := join_indep_right_empty A B hs hl
      refine ⟨indicator (sumLeftPart s), ⟨sumLeftPart s, join_left_indep A B hs, rfl⟩, ?_⟩
      simp [productAxisLeft, hr]
  · rintro (⟨x, ⟨s, hs, rfl⟩, rfl⟩ | ⟨y, ⟨t, ht, rfl⟩, rfl⟩)
    · refine ⟨indicator (sumFinset s (∅ : Finset W)), ?_, ?_⟩
      · exact ⟨sumFinset s ∅, join_sumFinset_left_indep A B hs, rfl⟩
      · rw [sumCoordinateSplit_sumFinset_indicator]
        simp [productAxisLeft]
    · refine ⟨indicator (sumFinset (∅ : Finset V) t), ?_, ?_⟩
      · exact ⟨sumFinset ∅ t, join_sumFinset_right_indep A B ht, rfl⟩
      · rw [sumCoordinateSplit_sumFinset_indicator]
        simp [productAxisRight]


-- @@ L493-497 verbatim
theorem stableIndicators_nonempty (G : SimpleGraph V) :
    (stableIndicators G).Nonempty := by
  refine ⟨0, ∅, ?_, ?_⟩
  · simp
  · exact indicator_empty.symm


-- @@ L499-535 expanded
/-- The stable-set polytope of a graph join is the free sum of the factors. -/
theorem sumCoordinateSplit_image_stab_join (A : SimpleGraph V) (B : SimpleGraph W) :
    sumCoordinateSplit '' stab (graphJoin A B) =
      convexJoin ℝ (productAxisLeft '' stab A) (productAxisRight '' stab B) :=
  by
  unfold stab
  calc
    sumCoordinateSplit '' convexHull ℝ (stableIndicators (graphJoin A B)) =
        convexHull ℝ (sumCoordinateSplit '' stableIndicators (graphJoin A B)) :=
      LinearMap.image_convexHull sumCoordinateSplit.toLinearMap _
    _ =
        convexHull ℝ
          ((productAxisLeft '' stableIndicators A) ∪ (productAxisRight '' stableIndicators B)) :=
      by rw [sumCoordinateSplit_image_stableIndicators_join]
    _ =
        convexJoin ℝ (convexHull ℝ (productAxisLeft '' stableIndicators A))
          (convexHull ℝ (productAxisRight '' stableIndicators B)) :=
      (convexHull_union ((stableIndicators_nonempty A).image productAxisLeft)
        ((stableIndicators_nonempty B).image productAxisRight))
    _ =
        convexJoin ℝ (productAxisLeft '' convexHull ℝ (stableIndicators A))
          (productAxisRight '' convexHull ℝ (stableIndicators B)) :=
      by
      have hleft :
        convexHull ℝ ((productAxisLeft (V := V) (W := W)) '' stableIndicators A) =
          (productAxisLeft (V := V) (W := W)) '' convexHull ℝ (stableIndicators A) :=
        by exact (LinearMap.image_convexHull (productAxisLeftLinear (V := V) (W := W)) _).symm
      have hright :
        convexHull ℝ ((productAxisRight (V := V) (W := W)) '' stableIndicators B) =
          (productAxisRight (V := V) (W := W)) '' convexHull ℝ (stableIndicators B) :=
        by exact (LinearMap.image_convexHull (productAxisRightLinear (V := V) (W := W)) _).symm
      rw [hleft, hright]


-- @@ L537-568 verbatim
theorem interior_stab_nonempty (G : SimpleGraph V) :
    (interior (stab G)).Nonempty := by
  let c : ℝ := 1 / ((Fintype.card V : ℝ) + 1)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  let U : Set (V → ℝ) :=
    {x | ∀ v, x v ∈ Set.Ioo (0 : ℝ) c}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ v : V,
        (fun x : V → ℝ => x v) ⁻¹' Set.Ioo (0 : ℝ) c by
      ext x
      simp [U]]
    apply isOpen_iInter_of_finite
    intro v
    exact isOpen_Ioo.preimage (continuous_apply v)
  have hUne : U.Nonempty := by
    refine ⟨fun _ => c / 2, ?_⟩
    intro v
    constructor <;> dsimp <;> linarith
  have hUstab : U ⊆ stab G := by
    intro x hx
    apply smallCube_subset_stab G
    constructor
    · intro v
      exact le_of_lt (hx v).1
    · intro v
      exact le_of_lt (hx v).2
  rcases hUne with ⟨x, hx⟩
  refine ⟨x, interior_mono hUstab ?_⟩
  rw [mem_interior_iff_mem_nhds]
  exact hUopen.mem_nhds hx


-- @@ L570-585 expanded
theorem stab_join_eq_split_preimage (A : SimpleGraph V) (B : SimpleGraph W) :
    stab (graphJoin A B) =
      (sumCoordinateSplit : ((V ⊕ W) → ℝ) → ((V → ℝ) × (W → ℝ))) ⁻¹'
        (convexJoin ℝ (productAxisLeft '' stab A) (productAxisRight '' stab B)) :=
  by
  ext x
  constructor
  · intro hx
    rw [← sumCoordinateSplit_image_stab_join A B]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← sumCoordinateSplit_image_stab_join A B] at hx
    rcases hx with ⟨y, hy, hxy⟩
    have : y = x := sumCoordinateSplit.injective hxy
    simpa [this] using hy


-- @@ L587-621 expanded
theorem nu_join (A : SimpleGraph V) (B : SimpleGraph W) : nu (graphJoin A B) = nu A * nu B :=
  by
  have hpre :=
    sumCoordinateSplit_measurePreserving.measure_preimage_emb
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : V ⊕ W => ℝ)).measurableEmbedding
      (convexJoin ℝ (productAxisLeft '' stab A) (productAxisRight '' stab B))
  have hvol :
    volume (stab (graphJoin A B)) =
      volume (convexJoin ℝ (productAxisLeft '' stab A) (productAxisRight '' stab B)) :=
    by
    rw [stab_join_eq_split_preimage A B]
    exact hpre
  have hjoin :=
    volume_convexJoin_productAxis_toReal (stab A) (stab B) (convex_stab A) (convex_stab B)
      (zero_mem_stab A) (zero_mem_stab B) (interior_stab_nonempty A) (interior_stab_nonempty B)
  have hjoin' :
    (volume (convexJoin ℝ (productAxisLeft '' stab A) (productAxisRight '' stab B))).toReal =
      ((Fintype.card V).factorial : ℝ) * ((Fintype.card W).factorial : ℝ) /
            ((Fintype.card V + Fintype.card W).factorial : ℝ) *
          (volume (stab A)).toReal *
        (volume (stab B)).toReal :=
    by
    change
      (volume
            (convexJoin ℝ ((fun x : V → ℝ => (x, 0)) '' stab A)
              ((fun y : W → ℝ => (0, y)) '' stab B))).toReal =
        _
    exact hjoin
  change
    (Fintype.card (V ⊕ W)).factorial * (volume (stab (graphJoin A B))).toReal =
      ((Fintype.card V).factorial * (volume (stab A)).toReal) *
        ((Fintype.card W).factorial * (volume (stab B)).toReal)
  rw [Fintype.card_sum, hvol, hjoin']
  have hfac : ((Fintype.card V + Fintype.card W).factorial : ℝ) ≠ 0 := by positivity
  field_simp


-- @@ L623-626 verbatim
private theorem sumLeftPart_sumFinset (s : Finset V) (t : Finset W) :
    sumLeftPart (sumFinset s t) = s := by
  ext v
  simp


-- @@ L628-631 verbatim
private theorem sumRightPart_sumFinset (s : Finset V) (t : Finset W) :
    sumRightPart (sumFinset s t) = t := by
  ext w
  simp


-- @@ L633-636 verbatim
private theorem sumFinset_parts (s : Finset (V ⊕ W)) :
    sumFinset (sumLeftPart s) (sumRightPart s) = s := by
  ext z
  cases z <;> simp


-- @@ L638-644 verbatim
@[simp]
private theorem card_sumFinset (s : Finset V) (t : Finset W) :
    (sumFinset s t).card = s.card + t.card := by
  unfold sumFinset
  rw [Finset.card_union_of_disjoint]
  · simp
  · simp [Finset.disjoint_left]


-- @@ L646-649 verbatim
private theorem compl_sumFinset (s : Finset V) (t : Finset W) :
    (sumFinset s t)ᶜ = sumFinset sᶜ tᶜ := by
  ext z
  cases z <;> simp


-- @@ L651-679 verbatim
private theorem sum_powerset_sumFinset
    (f : Finset (V ⊕ W) → ℝ) :
    ∑ u ∈ (Finset.univ : Finset (V ⊕ W)).powerset, f u =
      ∑ s ∈ (Finset.univ : Finset V).powerset,
        ∑ t ∈ (Finset.univ : Finset W).powerset,
          f (sumFinset s t) := by
  classical
  rw [← Finset.sum_product
    (Finset.univ : Finset V).powerset
    (Finset.univ : Finset W).powerset
    (fun p => f (sumFinset p.1 p.2))]
  apply Finset.sum_bij
      (fun u _ => (sumLeftPart u, sumRightPart u))
  · intro u hu
    simp
  · intro u₁ hu₁ u₂ hu₂ h
    have hleft : sumLeftPart u₁ = sumLeftPart u₂ := congrArg Prod.fst h
    have hright : sumRightPart u₁ = sumRightPart u₂ := congrArg Prod.snd h
    calc
      u₁ = sumFinset (sumLeftPart u₁) (sumRightPart u₁) :=
        (sumFinset_parts u₁).symm
      _ = sumFinset (sumLeftPart u₂) (sumRightPart u₂) := by
        rw [hleft, hright]
      _ = u₂ := sumFinset_parts u₂
  · rintro ⟨s, t⟩ hst
    refine ⟨sumFinset s t, by simp, ?_⟩
    simp [sumLeftPart_sumFinset, sumRightPart_sumFinset]
  · intro u hu
    rw [sumFinset_parts]


-- @@ L681-712 verbatim
private def inducedSumFinsetIso
    (A : SimpleGraph V) (B : SimpleGraph W)
    (s : Finset V) (t : Finset W) :
    inducedFinset (A ⊕g B) (sumFinset s t) ≃g
      inducedFinset A s ⊕g inducedFinset B t := by
  classical
  let e :
      {z : V ⊕ W // z ∈ sumFinset s t} ≃
        ({v : V // v ∈ s} ⊕ {w : W // w ∈ t}) :=
    { toFun := fun z => by
        rcases z with ⟨z, hz⟩
        cases z with
        | inl v => exact Sum.inl ⟨v, (inl_mem_sumFinset s t v).mp hz⟩
        | inr w => exact Sum.inr ⟨w, (inr_mem_sumFinset s t w).mp hz⟩
      invFun := fun z =>
        match z with
        | Sum.inl v => ⟨Sum.inl v.1, (inl_mem_sumFinset s t v.1).mpr v.2⟩
        | Sum.inr w => ⟨Sum.inr w.1, (inr_mem_sumFinset s t w.1).mpr w.2⟩
      left_inv := by
        rintro ⟨z, hz⟩
        cases z <;> rfl
      right_inv := by
        intro z
        cases z with
        | inl v => rcases v with ⟨v, hv⟩; rfl
        | inr w => rcases w with ⟨w, hw⟩; rfl }
  exact
    { toEquiv := e
      map_rel_iff' := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        cases x <;> cases y <;>
          simp [e, inducedFinset, SimpleGraph.sum_adj] }


-- @@ L714-745 expanded
private def inducedJoinFinsetIso (A : SimpleGraph V) (B : SimpleGraph W) (s : Finset V)
    (t : Finset W) :
    inducedFinset (graphJoin A B) (sumFinset s t) ≃g
      graphJoin (inducedFinset A s) (inducedFinset B t) :=
  by
  classical
  let e : { z : V ⊕ W // z ∈ sumFinset s t } ≃ ({ v : V // v ∈ s } ⊕ { w : W // w ∈ t }) :=
    { toFun := fun z => by
        rcases z with ⟨z, hz⟩
        cases z with
        | inl v => exact Sum.inl ⟨v, (inl_mem_sumFinset s t v).mp hz⟩
        | inr w => exact Sum.inr ⟨w, (inr_mem_sumFinset s t w).mp hz⟩
      invFun := fun z =>
        match z with
        | Sum.inl v => ⟨Sum.inl v.1, (inl_mem_sumFinset s t v.1).mpr v.2⟩
        | Sum.inr w => ⟨Sum.inr w.1, (inr_mem_sumFinset s t w.1).mpr w.2⟩
      left_inv := by
        rintro ⟨z, hz⟩
        cases z <;> rfl
      right_inv := by
        intro z
        cases z with
        | inl v => rcases v with ⟨v, hv⟩; rfl
        | inr w => rcases w with ⟨w, hw⟩; rfl }
  exact
    { toEquiv := e
      map_rel_iff' := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        cases x <;> cases y <;> simp [e, inducedFinset] }


-- @@ L747-755 verbatim
private theorem nuInduced_sumFinset
    (A : SimpleGraph V) (B : SimpleGraph W)
    (s : Finset V) (t : Finset W) :
    nuInduced (A ⊕g B) (sumFinset s t) =
      (Nat.choose (s.card + t.card) s.card : ℝ) *
        nuInduced A s * nuInduced B t := by
  unfold nuInduced
  rw [nu_iso (inducedSumFinsetIso A B s t), nu_sum]
  simp


-- @@ L757-763 expanded
private theorem nuInduced_joinFinset (A : SimpleGraph V) (B : SimpleGraph W) (s : Finset V)
    (t : Finset W) : nuInduced (graphJoin A B) (sumFinset s t) = nuInduced A s * nuInduced B t :=
  by
  unfold nuInduced
  rw [nu_iso (inducedJoinFinsetIso A B s t), nu_join]


-- @@ L765-796 verbatim
/-- Exact coefficient factorization for a disjoint union. -/
theorem qCoeff_sumFinset
    (A : SimpleGraph V) (B : SimpleGraph W)
    (s : Finset V) (t : Finset W) :
    qCoeff (A ⊕g B) (sumFinset s t) = qCoeff A s * qCoeff B t := by
  classical
  have hsle : s.card ≤ Fintype.card V := Finset.card_le_univ s
  have htle : t.card ≤ Fintype.card W := Finset.card_le_univ t
  have hremaining :
      Fintype.card V + Fintype.card W - (s.card + t.card) =
        (Fintype.card V - s.card) + (Fintype.card W - t.card) := by
    omega
  have hfac (a b : ℕ) :
      (((a + b).factorial : ℕ) : ℝ) =
        (Nat.choose (a + b) a : ℝ) * a.factorial * b.factorial := by
    norm_cast
    simpa using
      (Nat.choose_mul_factorial_mul_factorial
        (show a ≤ a + b by omega)).symm
  unfold qCoeff
  rw [compl_sumFinset, card_sumFinset, Fintype.card_sum, hremaining,
    nuInduced_sumFinset, nuInduced_sumFinset,
    Finset.card_compl, Finset.card_compl,
    hfac s.card t.card,
    hfac (Fintype.card V - s.card) (Fintype.card W - t.card)]
  have hs : (s.card.factorial : ℝ) ≠ 0 := by positivity
  have ht : (t.card.factorial : ℝ) ≠ 0 := by positivity
  have hsc : ((Fintype.card V - s.card).factorial : ℝ) ≠ 0 := by positivity
  have htc : ((Fintype.card W - t.card).factorial : ℝ) ≠ 0 := by positivity
  have hchoose (a b : ℕ) : (Nat.choose (a + b) a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : a ≤ a + b)))
  field_simp [hchoose]


-- @@ L798-836 expanded
/-- Exact coefficient transform for a graph join.  The two reciprocal binomial
factors are the join kernel in the cotree section-array recurrence.
-/
theorem qCoeff_joinFinset (A : SimpleGraph V) (B : SimpleGraph W) (s : Finset V) (t : Finset W) :
    qCoeff (graphJoin A B) (sumFinset s t) =
      qCoeff A s * qCoeff B t /
        ((Nat.choose (s.card + t.card) s.card : ℝ) *
          (Nat.choose ((Fintype.card V - s.card) + (Fintype.card W - t.card))
              (Fintype.card V - s.card) :
            ℝ)) :=
  by
  classical
  have hsle : s.card ≤ Fintype.card V := Finset.card_le_univ s
  have htle : t.card ≤ Fintype.card W := Finset.card_le_univ t
  have hremaining :
    Fintype.card V + Fintype.card W - (s.card + t.card) =
      (Fintype.card V - s.card) + (Fintype.card W - t.card) :=
    by omega
  have hfac (a b : ℕ) :
    (((a + b).factorial : ℕ) : ℝ) = (Nat.choose (a + b) a : ℝ) * a.factorial * b.factorial :=
    by
    norm_cast
    simpa using (Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)).symm
  unfold qCoeff
  rw [compl_sumFinset, card_sumFinset, Fintype.card_sum, hremaining, nuInduced_joinFinset,
    nuInduced_joinFinset, hfac s.card t.card,
    hfac (Fintype.card V - s.card) (Fintype.card W - t.card)]
  have hs : (s.card.factorial : ℝ) ≠ 0 := by positivity
  have ht : (t.card.factorial : ℝ) ≠ 0 := by positivity
  have hsc : ((Fintype.card V - s.card).factorial : ℝ) ≠ 0 := by positivity
  have htc : ((Fintype.card W - t.card).factorial : ℝ) ≠ 0 := by positivity
  have hchoose (a b : ℕ) : (Nat.choose (a + b) a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : a ≤ a + b)))
  field_simp [hchoose]


-- @@ L838-860 verbatim
/--
The exact section-product identity for disjoint union.
-/
theorem q_sum (A : SimpleGraph V) (B : SimpleGraph W) (x : ℝ) :
    q (A ⊕g B) x = q A x * q B x := by
  classical
  unfold q
  rw [sum_powerset_sumFinset]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [qCoeff_sumFinset, card_sumFinset, Fintype.card_sum]
  have hremaining :
      Fintype.card V + Fintype.card W - (s.card + t.card) =
        (Fintype.card V - s.card) + (Fintype.card W - t.card) := by
    have hsle : s.card ≤ Fintype.card V := Finset.card_le_univ s
    have htle : t.card ≤ Fintype.card W := Finset.card_le_univ t
    omega
  rw [hremaining, pow_add, pow_add]
  ring


-- @@ L862-888 expanded
/-- Normalized join identity.
-/
theorem N_join (A : SimpleGraph V) (B : SimpleGraph W) : N (graphJoin A B) = N A * N B / 2 := by
  classical
  unfold N
  rw [sum_powerset_sumFinset]
  simp_rw [compl_sumFinset, nuInduced_joinFinset]
  have hfactor :
    ∑ s ∈ (Finset.univ : Finset V).powerset,
        ∑ t ∈ (Finset.univ : Finset W).powerset,
          (nuInduced A s * nuInduced B t) * (nuInduced A sᶜ * nuInduced B tᶜ) =
      (∑ s ∈ (Finset.univ : Finset V).powerset, nuInduced A s * nuInduced A sᶜ) *
        (∑ t ∈ (Finset.univ : Finset W).powerset, nuInduced B t * nuInduced B tᶜ) :=
    by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hfactor]
  ring


-- @@ L890-890 verbatim
end UnionJoin


-- @@ L892-892 verbatim
end HansenCograph
