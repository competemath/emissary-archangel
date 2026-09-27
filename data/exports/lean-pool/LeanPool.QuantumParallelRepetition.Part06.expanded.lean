/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import LeanPool.QuantumParallelRepetition.Part05


-- @@ L10-10 verbatim
/-! # Quantum parallel repetition, part 06 -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace QuantumParallelRepetition


-- @@ L18-18 verbatim
open scoped ComplexOrder Matrix BigOperators InnerProductSpace

-- @@ L19-19 verbatim
open Complex Matrix Finset


-- @@ L21-21 verbatim
section


-- @@ L23-24 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L27-27 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L29-29 verbatim
variable {X Y A B : Type*}

-- @@ L30-30 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L32-70 verbatim
theorem exactAliceQuestionConditionalWeight_sum
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) :
    (∑ q : ExactFullQuestion X Y n,
      if exactRevealCode D seed q = history ∧
        q.1 seed.coordinate.val = x then
        exactPriorQuestionWeight G n q /
          exactAliceQuestionMass G n D seed history x
      else 0) =
      if exactAliceQuestionMass G n D seed history x = 0
      then 0 else 1 := by
  classical
  calc
    (∑ q : ExactFullQuestion X Y n,
      if exactRevealCode D seed q = history ∧
        q.1 seed.coordinate.val = x then
        exactPriorQuestionWeight G n q /
          exactAliceQuestionMass G n D seed history x
      else 0) =
      (∑ q : ExactFullQuestion X Y n,
        if exactRevealCode D seed q = history ∧
          q.1 seed.coordinate.val = x then
          exactPriorQuestionWeight G n q
        else 0) /
          exactAliceQuestionMass G n D seed history x := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro q _
            split <;> simp
    _ = exactAliceQuestionMass G n D seed history x /
          exactAliceQuestionMass G n D seed history x := by
            rfl
    _ = _ := by
      split_ifs with zero
      · simp only [zero, div_zero]
      · exact div_self zero


-- @@ L72-110 verbatim
theorem exactBobQuestionConditionalWeight_sum
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) :
    (∑ q : ExactFullQuestion X Y n,
      if exactRevealCode D seed q = history ∧
        q.2 seed.coordinate.val = y then
        exactPriorQuestionWeight G n q /
          exactBobQuestionMass G n D seed history y
      else 0) =
      if exactBobQuestionMass G n D seed history y = 0
      then 0 else 1 := by
  classical
  calc
    (∑ q : ExactFullQuestion X Y n,
      if exactRevealCode D seed q = history ∧
        q.2 seed.coordinate.val = y then
        exactPriorQuestionWeight G n q /
          exactBobQuestionMass G n D seed history y
      else 0) =
      (∑ q : ExactFullQuestion X Y n,
        if exactRevealCode D seed q = history ∧
          q.2 seed.coordinate.val = y then
          exactPriorQuestionWeight G n q
        else 0) /
          exactBobQuestionMass G n D seed history y := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro q _
            split <;> simp
    _ = exactBobQuestionMass G n D seed history y /
          exactBobQuestionMass G n D seed history y := by
            rfl
    _ = _ := by
      split_ifs with zero
      · simp only [zero, div_zero]
      · exact div_self zero


-- @@ L112-173 verbatim
theorem exactAliceQuestionFilter_complement_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {i : Fin n // i ∈ D} → A)
    (x : X) :
    (1 - exactAliceQuestionFilter
      G n S D seed history answer x).PosSemidef := by
  classical
  let w : ExactFullQuestion X Y n → ℝ := fun q =>
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x then
      exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x
    else 0
  let E : ExactFullQuestion X Y n →
      Matrix S.Alice S.Alice ℂ := fun q =>
    conditionedAliceEffect G n S D answer q.1
  have weights_nonnegative (q : ExactFullQuestion X Y n) :
      0 ≤ w q := by
    dsimp [w]
    split
    · exact div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg G n D seed history x)
    · exact le_rfl
  have weights_sum : (∑ q, w q) ≤ 1 := by
    change
      (∑ q : ExactFullQuestion X Y n,
        if exactRevealCode D seed q = history ∧
          q.1 seed.coordinate.val = x then
          exactPriorQuestionWeight G n q /
            exactAliceQuestionMass G n D seed history x
        else 0) ≤ 1
    rw [exactAliceQuestionConditionalWeight_sum
      G n D seed history x]
    split <;> norm_num
  have filter_eq :
      exactAliceQuestionFilter
          G n S D seed history answer x =
        ∑ q, w q • E q := by
    unfold exactAliceQuestionFilter
    apply Finset.sum_congr rfl
    intro q _
    dsimp [w, E]
    split <;> simp
  have split :
      1 - (∑ q, w q • E q) =
        (1 - (∑ q, w q)) •
            (1 : Matrix S.Alice S.Alice ℂ) +
          ∑ q, w q • (1 - E q) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    module
  rw [filter_eq, split]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr weights_sum)
  · apply Matrix.posSemidef_sum Finset.univ
    intro q _
    exact (conditionedAliceEffect_complement_positive
      G n S D answer q.1).smul (weights_nonnegative q)


-- @@ L175-236 verbatim
theorem exactBobQuestionFilter_complement_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {i : Fin n // i ∈ D} → B)
    (y : Y) :
    (1 - exactBobQuestionFilter
      G n S D seed history answer y).PosSemidef := by
  classical
  let w : ExactFullQuestion X Y n → ℝ := fun q =>
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y then
      exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y
    else 0
  let E : ExactFullQuestion X Y n →
      Matrix S.Bob S.Bob ℂ := fun q =>
    conditionedBobEffect G n S D answer q.2
  have weights_nonnegative (q : ExactFullQuestion X Y n) :
      0 ≤ w q := by
    dsimp [w]
    split
    · exact div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg G n D seed history y)
    · exact le_rfl
  have weights_sum : (∑ q, w q) ≤ 1 := by
    change
      (∑ q : ExactFullQuestion X Y n,
        if exactRevealCode D seed q = history ∧
          q.2 seed.coordinate.val = y then
          exactPriorQuestionWeight G n q /
            exactBobQuestionMass G n D seed history y
        else 0) ≤ 1
    rw [exactBobQuestionConditionalWeight_sum
      G n D seed history y]
    split <;> norm_num
  have filter_eq :
      exactBobQuestionFilter
          G n S D seed history answer y =
        ∑ q, w q • E q := by
    unfold exactBobQuestionFilter
    apply Finset.sum_congr rfl
    intro q _
    dsimp [w, E]
    split <;> simp
  have split :
      1 - (∑ q, w q • E q) =
        (1 - (∑ q, w q)) •
            (1 : Matrix S.Bob S.Bob ℂ) +
          ∑ q, w q • (1 - E q) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    module
  rw [filter_eq, split]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr weights_sum)
  · apply Matrix.posSemidef_sum Finset.univ
    intro q _
    exact (conditionedBobEffect_complement_positive
      G n S D answer q.2).smul (weights_nonnegative q)


-- @@ L238-269 verbatim
theorem exactAliceMeanFilter_complement_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {i : Fin n // i ∈ D} → A)
    (y : Y) :
    (1 - exactAliceMeanFilter
      G n S D seed history answer y).PosSemidef := by
  classical
  let w : X → ℝ := G.conditionalXGivenY y
  let E : X → Matrix S.Alice S.Alice ℂ := fun x =>
    exactAliceQuestionFilter G n S D seed history answer x
  have weights_sum : (∑ x, w x) ≤ 1 :=
    G.conditionalXGivenY_sum_le_one y
  have split :
      1 - (∑ x, w x • E x) =
        (1 - (∑ x, w x)) •
            (1 : Matrix S.Alice S.Alice ℂ) +
          ∑ x, w x • (1 - E x) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    module
  change (1 - ∑ x, w x • E x).PosSemidef
  rw [split]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr weights_sum)
  · apply Matrix.posSemidef_sum Finset.univ
    intro x _
    exact (exactAliceQuestionFilter_complement_posSemidef
      G n S D seed history answer x).smul
        (G.conditionalXGivenY_nonneg y x)


-- @@ L271-302 verbatim
theorem exactBobMeanFilter_complement_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {i : Fin n // i ∈ D} → B)
    (x : X) :
    (1 - exactBobMeanFilter
      G n S D seed history answer x).PosSemidef := by
  classical
  let w : Y → ℝ := G.conditionalYGivenX x
  let E : Y → Matrix S.Bob S.Bob ℂ := fun y =>
    exactBobQuestionFilter G n S D seed history answer y
  have weights_sum : (∑ y, w y) ≤ 1 :=
    G.conditionalYGivenX_sum_le_one x
  have split :
      1 - (∑ y, w y • E y) =
        (1 - (∑ y, w y)) •
            (1 : Matrix S.Bob S.Bob ℂ) +
          ∑ y, w y • (1 - E y) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    module
  change (1 - ∑ y, w y • E y).PosSemidef
  rw [split]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr weights_sum)
  · apply Matrix.posSemidef_sum Finset.univ
    intro y _
    exact (exactBobQuestionFilter_complement_posSemidef
      G n S D seed history answer y).smul
        (G.conditionalYGivenX_nonneg x y)


-- @@ L304-334 verbatim
theorem exactFairAliceMean_spectral_entropy_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    -bornTracePairing S.state.matrix
        (cfc (fun z : ℝ => z * Real.log z)
          (exactAliceMeanFilter
            G n S D r.seed r.history r.aliceAnswer y))
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y) ≤
      Real.negMulLog
        (bornTracePairing S.state.matrix
          (exactAliceMeanFilter
            G n S D r.seed r.history r.aliceAnswer y)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y)) := by
  classical
  exact source_equation_nineteen_alice S.state
    (exactAliceMeanFilter
      G n S D r.seed r.history r.aliceAnswer y)
    (exactAliceMeanFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer y)
    (exactAliceMeanFilter_complement_posSemidef
      G n S D r.seed r.history r.aliceAnswer y)
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_complement_posSemidef
      G n S D r.seed r.history r.bobAnswer y)


-- @@ L336-366 verbatim
theorem exactFairBobMean_spectral_entropy_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    -bornTracePairing S.state.matrix
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)
        (cfc (fun z : ℝ => z * Real.log z)
          (exactBobMeanFilter
            G n S D r.seed r.history r.bobAnswer x)) ≤
      Real.negMulLog
        (bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobMeanFilter
            G n S D r.seed r.history r.bobAnswer x)) := by
  classical
  exact source_equation_nineteen_bob S.state
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_complement_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactBobMeanFilter
      G n S D r.seed r.history r.bobAnswer x)
    (exactBobMeanFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer x)
    (exactBobMeanFilter_complement_posSemidef
      G n S D r.seed r.history r.bobAnswer x)


-- @@ L368-411 verbatim
theorem exactFairAliceHistoryHighOperatorPotential_nonpos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairAliceHistoryHighOperatorPotential
      G n S D r ≤ 0 := by
  classical
  unfold exactFairAliceHistoryHighOperatorPotential
  apply Finset.sum_nonpos
  intro y _
  apply mul_nonpos_of_nonneg_of_nonpos (G.marginalY_nonneg y)
  calc
    bornTracePairing S.state.matrix
        (∑ x : X, G.conditionalXGivenY y x •
          cfc (fun z : ℝ => z * Real.log z)
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x))
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y) =
      ∑ x : X, G.conditionalXGivenY y x *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x))
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
              simp only [map_sum, map_smul, LinearMap.sum_apply,
                LinearMap.smul_apply, smul_eq_mul]
    _ ≤ 0 := by
      apply Finset.sum_nonpos
      intro x _
      exact mul_nonpos_of_nonneg_of_nonpos
        (G.conditionalXGivenY_nonneg y x)
        (matrixLogEntropy_born_nonpos_left S.state
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y)
          (exactAliceQuestionFilter_posSemidef
            G n S D r.seed r.history r.aliceAnswer x)
          (exactAliceQuestionFilter_complement_posSemidef
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter_posSemidef
            G n S D r.seed r.history r.bobAnswer y))


-- @@ L413-455 verbatim
theorem exactFairBobHistoryHighOperatorPotential_nonpos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairBobHistoryHighOperatorPotential
      G n S D r ≤ 0 := by
  classical
  unfold exactFairBobHistoryHighOperatorPotential
  apply Finset.sum_nonpos
  intro x _
  apply mul_nonpos_of_nonneg_of_nonpos (G.marginalX_nonneg x)
  calc
    bornTracePairing S.state.matrix
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)
        (∑ y : Y, G.conditionalYGivenX x y •
          cfc (fun z : ℝ => z * Real.log z)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y)) =
      ∑ y : Y, G.conditionalYGivenX x y *
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (cfc (fun z : ℝ => z * Real.log z)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y)) := by
              simp only [map_sum, map_smul, smul_eq_mul]
    _ ≤ 0 := by
      apply Finset.sum_nonpos
      intro y _
      exact mul_nonpos_of_nonneg_of_nonpos
        (G.conditionalYGivenX_nonneg x y)
        (matrixLogEntropy_born_nonpos_right S.state
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y)
          (exactAliceQuestionFilter_posSemidef
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter_posSemidef
            G n S D r.seed r.history r.bobAnswer y)
          (exactBobQuestionFilter_complement_posSemidef
            G n S D r.seed r.history r.bobAnswer y))


-- @@ L457-477 verbatim
theorem exactFairAliceHistoryLowOperatorPotential_neg_le_entropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    -exactFairAliceHistoryLowOperatorPotential G n S D r ≤
      ∑ y : Y, G.marginalY y *
        Real.negMulLog
          (bornTracePairing S.state.matrix
            (exactAliceMeanFilter
              G n S D r.seed r.history r.aliceAnswer y)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y)) := by
  classical
  unfold exactFairAliceHistoryLowOperatorPotential
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro y _
  have bound := mul_le_mul_of_nonneg_left
    (exactFairAliceMean_spectral_entropy_le G n S D r y)
    (G.marginalY_nonneg y)
  linarith


-- @@ L479-499 verbatim
theorem exactFairBobHistoryLowOperatorPotential_neg_le_entropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    -exactFairBobHistoryLowOperatorPotential G n S D r ≤
      ∑ x : X, G.marginalX x *
        Real.negMulLog
          (bornTracePairing S.state.matrix
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x)
            (exactBobMeanFilter
              G n S D r.seed r.history r.bobAnswer x)) := by
  classical
  unfold exactFairBobHistoryLowOperatorPotential
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro x _
  have bound := mul_le_mul_of_nonneg_left
    (exactFairBobMean_spectral_entropy_le G n S D r x)
    (G.marginalX_nonneg x)
  linarith


-- @@ L501-528 verbatim
theorem exactReverseAliceFilterHighOperatorPotential_nonpos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceFilterHighOperatorPotential
      G n S D side context marker ≤ 0 := by
  classical
  unfold exactReverseAliceFilterHighOperatorPotential
  dsimp only
  apply Finset.sum_nonpos
  intro history _
  apply Finset.sum_nonpos
  intro aliceAnswer _
  apply Finset.sum_nonpos
  intro bobAnswer _
  split
  · exact mul_nonpos_of_nonneg_of_nonpos
      (exactRevealMass_nonneg G n D
        (exactReverseBobMarkerDecode side context marker)
        history)
      (exactFairAliceHistoryHighOperatorPotential_nonpos
        G n S D
        ⟨exactReverseBobMarkerDecode side context marker,
          history, aliceAnswer, bobAnswer⟩)
  · exact le_rfl


-- @@ L530-557 verbatim
theorem exactReverseBobFilterHighOperatorPotential_nonpos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobFilterHighOperatorPotential
      G n S D side context marker ≤ 0 := by
  classical
  unfold exactReverseBobFilterHighOperatorPotential
  dsimp only
  apply Finset.sum_nonpos
  intro history _
  apply Finset.sum_nonpos
  intro aliceAnswer _
  apply Finset.sum_nonpos
  intro bobAnswer _
  split
  · exact mul_nonpos_of_nonneg_of_nonpos
      (exactRevealMass_nonneg G n D
        (exactReverseAliceMarkerDecode side context marker)
        history)
      (exactFairBobHistoryHighOperatorPotential_nonpos
        G n S D
        ⟨exactReverseAliceMarkerDecode side context marker,
          history, aliceAnswer, bobAnswer⟩)
  · exact le_rfl


-- @@ L559-559 verbatim
end


-- @@ L561-561 verbatim
section


-- @@ L563-564 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L567-567 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L569-569 verbatim
variable {X Y A B : Type*}

-- @@ L570-570 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L572-580 verbatim
private def exactJointPrefixQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (fixedX fixedY : Finset (Fin n))
    (knownX : Fin n → X) (knownY : Fin n → Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    if (∀ j : Fin n, j ∈ fixedX → xs j = knownX j) ∧
       (∀ j : Fin n, j ∈ fixedY → ys j = knownY j) then
      (G.repeat n).questionWeight xs ys
    else 0


-- @@ L582-593 verbatim
private def exactJointPrefixAliceOperatorMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n))
    (answer : {j : Fin n // j ∈ D} → A)
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    if (∀ j : Fin n, j ∈ fixedX → xs j = knownX j) ∧
       (∀ j : Fin n, j ∈ fixedY → ys j = knownY j) then
      (G.repeat n).questionWeight xs ys •
        conditionedAliceEffect G n S D answer xs
    else 0


-- @@ L595-606 verbatim
private def exactJointPrefixBobOperatorMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n))
    (answer : {j : Fin n // j ∈ D} → B)
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    if (∀ j : Fin n, j ∈ fixedX → xs j = knownX j) ∧
       (∀ j : Fin n, j ∈ fixedY → ys j = knownY j) then
      (G.repeat n).questionWeight xs ys •
        conditionedBobEffect G n S D answer ys
    else 0


-- @@ L608-640 verbatim
private theorem exactJointPrefixQuestionMass_eq_sum_alice
    (G : Game X Y A B) (n : ℕ)
    (fixedX fixedY : Finset (Fin n))
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    exactJointPrefixQuestionMass
        G n fixedX fixedY knownX knownY =
      ∑ ys : Fin n → Y,
        if ∀ j : Fin n, j ∈ fixedY → ys j = knownY j then
          exactFixedAliceQuestionMass
            G n fixedX knownX ys
        else 0 := by
  classical
  unfold exactJointPrefixQuestionMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ys _
  unfold exactFixedAliceQuestionMass
  by_cases compatible :
      ∀ j : Fin n, j ∈ fixedY → ys j = knownY j
  · rw [ite_eq_left compatible]
    apply Finset.sum_congr rfl
    intro xs _
    by_cases alice_compatible :
        ∀ j : Fin n, j ∈ fixedX → xs j = knownX j
    · rw [ite_eq_left ⟨alice_compatible, compatible⟩,
        ite_eq_left alice_compatible]
    · rw [ite_eq_right (fun h => alice_compatible h.1),
        ite_eq_right alice_compatible]
  · rw [ite_eq_right compatible]
    apply Finset.sum_eq_zero
    intro xs _
    rw [ite_eq_right]
    exact fun h => compatible h.2


-- @@ L642-673 verbatim
private theorem exactJointPrefixQuestionMass_eq_sum_bob
    (G : Game X Y A B) (n : ℕ)
    (fixedX fixedY : Finset (Fin n))
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    exactJointPrefixQuestionMass
        G n fixedX fixedY knownX knownY =
      ∑ xs : Fin n → X,
        if ∀ j : Fin n, j ∈ fixedX → xs j = knownX j then
          exactFixedBobQuestionMass
            G n fixedY xs knownY
        else 0 := by
  classical
  unfold exactJointPrefixQuestionMass
  apply Finset.sum_congr rfl
  intro xs _
  unfold exactFixedBobQuestionMass
  by_cases compatible :
      ∀ j : Fin n, j ∈ fixedX → xs j = knownX j
  · rw [ite_eq_left compatible]
    apply Finset.sum_congr rfl
    intro ys _
    by_cases bob_compatible :
        ∀ j : Fin n, j ∈ fixedY → ys j = knownY j
    · rw [ite_eq_left ⟨compatible, bob_compatible⟩,
        ite_eq_left bob_compatible]
    · rw [ite_eq_right (fun h => bob_compatible h.2),
        ite_eq_right bob_compatible]
  · rw [ite_eq_right compatible]
    apply Finset.sum_eq_zero
    intro ys _
    rw [ite_eq_right]
    exact fun h => compatible h.1


-- @@ L675-698 verbatim
private theorem exactJointPrefixQuestionMass_insert_alice
    (G : Game X Y A B) (n : ℕ)
    (fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (fresh : j ∉ fixedX) (opposite_fixed : j ∈ fixedY)
    (knownX : Fin n → X) (knownY : Fin n → Y) (x : X) :
    exactJointPrefixQuestionMass G n
        (insert j fixedX) fixedY
        (Function.update knownX j x) knownY =
      G.conditionalXGivenY (knownY j) x *
        exactJointPrefixQuestionMass G n
          fixedX fixedY knownX knownY := by
  classical
  rw [exactJointPrefixQuestionMass_eq_sum_alice,
    exactJointPrefixQuestionMass_eq_sum_alice,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys _
  by_cases compatible :
      ∀ k : Fin n, k ∈ fixedY → ys k = knownY k
  · rw [ite_eq_left compatible, ite_eq_left compatible,
      exactFixedAliceQuestionMass_insert
        G n fixedX j fresh knownX ys x,
      compatible j opposite_fixed]
  · simp only [compatible, ↓reduceIte, mul_zero]


-- @@ L700-723 verbatim
private theorem exactJointPrefixQuestionMass_insert_bob
    (G : Game X Y A B) (n : ℕ)
    (fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (opposite_fixed : j ∈ fixedX) (fresh : j ∉ fixedY)
    (knownX : Fin n → X) (knownY : Fin n → Y) (y : Y) :
    exactJointPrefixQuestionMass G n
        fixedX (insert j fixedY)
        knownX (Function.update knownY j y) =
      G.conditionalYGivenX (knownX j) y *
        exactJointPrefixQuestionMass G n
          fixedX fixedY knownX knownY := by
  classical
  rw [exactJointPrefixQuestionMass_eq_sum_bob,
    exactJointPrefixQuestionMass_eq_sum_bob,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  by_cases compatible :
      ∀ k : Fin n, k ∈ fixedX → xs k = knownX k
  · rw [ite_eq_left compatible, ite_eq_left compatible,
      exactFixedBobQuestionMass_insert
        G n fixedY j fresh xs knownY y,
      compatible j opposite_fixed]
  · simp only [compatible, ↓reduceIte, mul_zero]


-- @@ L725-755 verbatim
private theorem exactJointPrefixQuestionAtom_zero_of_mass_zero
    (G : Game X Y A B) (n : ℕ)
    (fixedX fixedY : Finset (Fin n))
    (knownX : Fin n → X) (knownY : Fin n → Y)
    (zero : exactJointPrefixQuestionMass
      G n fixedX fixedY knownX knownY = 0)
    (xs : Fin n → X) (ys : Fin n → Y) :
    (if (∀ j : Fin n, j ∈ fixedX → xs j = knownX j) ∧
        (∀ j : Fin n, j ∈ fixedY → ys j = knownY j) then
       (G.repeat n).questionWeight xs ys
     else 0) = 0 := by
  unfold exactJointPrefixQuestionMass at zero
  have row_nonnegative (xx : Fin n → X) :
      0 ≤ ∑ yy : Fin n → Y,
        if (∀ j : Fin n, j ∈ fixedX → xx j = knownX j) ∧
           (∀ j : Fin n, j ∈ fixedY → yy j = knownY j) then
          (G.repeat n).questionWeight xx yy
        else 0 := by
    apply Finset.sum_nonneg
    intro yy _
    split
    · exact (G.repeat n).weight_nonneg xx yy
    · exact le_rfl
  have row_zero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun xx _ => row_nonnegative xx)).mp zero xs
      (Finset.mem_univ xs)
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun yy _ => by
      split
      · exact (G.repeat n).weight_nonneg xs yy
      · exact le_rfl)).mp row_zero ys (Finset.mem_univ ys)


-- @@ L757-780 verbatim
private theorem exactJointPrefixAliceOperatorMass_zero_of_mass_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n))
    (answer : {j : Fin n // j ∈ D} → A)
    (knownX : Fin n → X) (knownY : Fin n → Y)
    (zero : exactJointPrefixQuestionMass
      G n fixedX fixedY knownX knownY = 0) :
    exactJointPrefixAliceOperatorMass
      G n S D fixedX fixedY answer knownX knownY = 0 := by
  unfold exactJointPrefixAliceOperatorMass
  apply Finset.sum_eq_zero
  intro xs _
  apply Finset.sum_eq_zero
  intro ys _
  have atom := exactJointPrefixQuestionAtom_zero_of_mass_zero
    G n fixedX fixedY knownX knownY zero xs ys
  by_cases compatible :
      (∀ j : Fin n, j ∈ fixedX → xs j = knownX j) ∧
      (∀ j : Fin n, j ∈ fixedY → ys j = knownY j)
  · have weight_zero : (G.repeat n).questionWeight xs ys = 0 := by
      simpa only [ite_eq_left compatible] using atom
    rw [ite_eq_left compatible, weight_zero]
    exact zero_smul ℝ (conditionedAliceEffect G n S D answer xs)
  · rw [ite_eq_right compatible]


-- @@ L782-805 verbatim
private theorem exactJointPrefixBobOperatorMass_zero_of_mass_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n))
    (answer : {j : Fin n // j ∈ D} → B)
    (knownX : Fin n → X) (knownY : Fin n → Y)
    (zero : exactJointPrefixQuestionMass
      G n fixedX fixedY knownX knownY = 0) :
    exactJointPrefixBobOperatorMass
      G n S D fixedX fixedY answer knownX knownY = 0 := by
  unfold exactJointPrefixBobOperatorMass
  apply Finset.sum_eq_zero
  intro xs _
  apply Finset.sum_eq_zero
  intro ys _
  have atom := exactJointPrefixQuestionAtom_zero_of_mass_zero
    G n fixedX fixedY knownX knownY zero xs ys
  by_cases compatible :
      (∀ j : Fin n, j ∈ fixedX → xs j = knownX j) ∧
      (∀ j : Fin n, j ∈ fixedY → ys j = knownY j)
  · have weight_zero : (G.repeat n).questionWeight xs ys = 0 := by
      simpa only [ite_eq_left compatible] using atom
    rw [ite_eq_left compatible, weight_zero]
    exact zero_smul ℝ (conditionedBobEffect G n S D answer ys)
  · rw [ite_eq_right compatible]


-- @@ L807-870 verbatim
private theorem exactJointPrefixAliceOperatorMass_sum_insert
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (fresh : j ∉ fixedX)
    (answer : {k : Fin n // k ∈ D} → A)
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    (∑ x : X,
      exactJointPrefixAliceOperatorMass G n S D
        (insert j fixedX) fixedY answer
        (Function.update knownX j x) knownY) =
      exactJointPrefixAliceOperatorMass G n S D
        fixedX fixedY answer knownX knownY := by
  classical
  unfold exactJointPrefixAliceOperatorMass
  calc
    (∑ x : X, ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      if (∀ k : Fin n, k ∈ insert j fixedX →
          xs k = (Function.update knownX j x) k) ∧
         (∀ k : Fin n, k ∈ fixedY → ys k = knownY k) then
        (G.repeat n).questionWeight xs ys •
          conditionedAliceEffect G n S D answer xs
      else 0) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y, ∑ x : X,
        if (∀ k : Fin n, k ∈ insert j fixedX →
            xs k = (Function.update knownX j x) k) ∧
           (∀ k : Fin n, k ∈ fixedY → ys k = knownY k) then
          (G.repeat n).questionWeight xs ys •
            conditionedAliceEffect G n S D answer xs
        else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro xs _
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro ys _
      simp_rw [exactFixedQuestionPrefix_insert_iff
        fixedX j fresh xs knownX]
      by_cases compatible :
          (∀ k : Fin n, k ∈ fixedX → xs k = knownX k) ∧
          (∀ k : Fin n, k ∈ fixedY → ys k = knownY k)
      · rw [ite_eq_left compatible]
        calc
          _ = (if
              (xs j = xs j ∧
                (∀ k : Fin n, k ∈ fixedX → xs k = knownX k)) ∧
                (∀ k : Fin n, k ∈ fixedY → ys k = knownY k)
              then (G.repeat n).questionWeight xs ys •
                conditionedAliceEffect G n S D answer xs
              else 0) := by
                apply Finset.sum_eq_single (xs j)
                · intro x _ different
                  rw [ite_eq_right]
                  exact fun h => different h.1.1.symm
                · intro absent
                  exact (absent (Finset.mem_univ (xs j))).elim
          _ = _ := ite_eq_left ⟨⟨rfl, compatible.1⟩, compatible.2⟩
      · rw [ite_eq_right compatible]
        apply Finset.sum_eq_zero
        intro x _
        rw [ite_eq_right]
        exact fun h => compatible ⟨h.1.2, h.2⟩


-- @@ L872-935 verbatim
private theorem exactJointPrefixBobOperatorMass_sum_insert
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (fresh : j ∉ fixedY)
    (answer : {k : Fin n // k ∈ D} → B)
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    (∑ y : Y,
      exactJointPrefixBobOperatorMass G n S D
        fixedX (insert j fixedY) answer
        knownX (Function.update knownY j y)) =
      exactJointPrefixBobOperatorMass G n S D
        fixedX fixedY answer knownX knownY := by
  classical
  unfold exactJointPrefixBobOperatorMass
  calc
    (∑ y : Y, ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      if (∀ k : Fin n, k ∈ fixedX → xs k = knownX k) ∧
         (∀ k : Fin n, k ∈ insert j fixedY →
           ys k = (Function.update knownY j y) k) then
        (G.repeat n).questionWeight xs ys •
          conditionedBobEffect G n S D answer ys
      else 0) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y, ∑ y : Y,
        if (∀ k : Fin n, k ∈ fixedX → xs k = knownX k) ∧
           (∀ k : Fin n, k ∈ insert j fixedY →
             ys k = (Function.update knownY j y) k) then
          (G.repeat n).questionWeight xs ys •
            conditionedBobEffect G n S D answer ys
        else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro xs _
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro xs _
      apply Finset.sum_congr rfl
      intro ys _
      simp_rw [exactFixedQuestionPrefix_insert_iff
        fixedY j fresh ys knownY]
      by_cases compatible :
          (∀ k : Fin n, k ∈ fixedX → xs k = knownX k) ∧
          (∀ k : Fin n, k ∈ fixedY → ys k = knownY k)
      · rw [ite_eq_left compatible]
        calc
          _ = (if
              (∀ k : Fin n, k ∈ fixedX → xs k = knownX k) ∧
                (ys j = ys j ∧
                  (∀ k : Fin n, k ∈ fixedY → ys k = knownY k))
              then (G.repeat n).questionWeight xs ys •
                conditionedBobEffect G n S D answer ys
              else 0) := by
                apply Finset.sum_eq_single (ys j)
                · intro y _ different
                  rw [ite_eq_right]
                  exact fun h => different h.2.1.symm
                · intro absent
                  exact (absent (Finset.mem_univ (ys j))).elim
          _ = _ := ite_eq_left ⟨compatible.1, ⟨rfl, compatible.2⟩⟩
      · rw [ite_eq_right compatible]
        apply Finset.sum_eq_zero
        intro y _
        rw [ite_eq_right]
        exact fun h => compatible ⟨h.1, h.2.2⟩


-- @@ L937-946 verbatim
private def exactJointPrefixAliceOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n))
    (answer : {j : Fin n // j ∈ D} → A)
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    Matrix S.Alice S.Alice ℂ :=
  (exactJointPrefixQuestionMass
    G n fixedX fixedY knownX knownY)⁻¹ •
    exactJointPrefixAliceOperatorMass
      G n S D fixedX fixedY answer knownX knownY


-- @@ L948-957 verbatim
private def exactJointPrefixBobOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n))
    (answer : {j : Fin n // j ∈ D} → B)
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    Matrix S.Bob S.Bob ℂ :=
  (exactJointPrefixQuestionMass
    G n fixedX fixedY knownX knownY)⁻¹ •
    exactJointPrefixBobOperatorMass
      G n S D fixedX fixedY answer knownX knownY


-- @@ L959-1034 verbatim
private theorem exactJointPrefixAliceOperatorFilter_martingale
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (fresh : j ∉ fixedX) (opposite_fixed : j ∈ fixedY)
    (answer : {k : Fin n // k ∈ D} → A)
    (knownX : Fin n → X) (knownY : Fin n → Y)
    (supported : exactJointPrefixQuestionMass
      G n fixedX fixedY knownX knownY ≠ 0) :
    (∑ x : X, G.conditionalXGivenY (knownY j) x •
      exactJointPrefixAliceOperatorFilter G n S D
        (insert j fixedX) fixedY answer
        (Function.update knownX j x) knownY) =
      exactJointPrefixAliceOperatorFilter G n S D
        fixedX fixedY answer knownX knownY := by
  classical
  unfold exactJointPrefixAliceOperatorFilter
  calc
    (∑ x : X, G.conditionalXGivenY (knownY j) x •
      ((exactJointPrefixQuestionMass G n
        (insert j fixedX) fixedY
        (Function.update knownX j x) knownY)⁻¹ •
        exactJointPrefixAliceOperatorMass G n S D
          (insert j fixedX) fixedY answer
          (Function.update knownX j x) knownY)) =
      ∑ x : X,
        (exactJointPrefixQuestionMass
          G n fixedX fixedY knownX knownY)⁻¹ •
          exactJointPrefixAliceOperatorMass G n S D
            (insert j fixedX) fixedY answer
            (Function.update knownX j x) knownY := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases child_zero :
          exactJointPrefixQuestionMass G n
            (insert j fixedX) fixedY
            (Function.update knownX j x) knownY = 0
      · have matrix_zero :=
          exactJointPrefixAliceOperatorMass_zero_of_mass_zero
            G n S D (insert j fixedX) fixedY answer
            (Function.update knownX j x) knownY child_zero
        rw [matrix_zero]
        simp only [smul_zero]
      · have insertion := exactJointPrefixQuestionMass_insert_alice
          G n fixedX fixedY j fresh opposite_fixed knownX knownY x
        have conditional :
            exactJointPrefixQuestionMass G n
                (insert j fixedX) fixedY
                (Function.update knownX j x) knownY /
              exactJointPrefixQuestionMass
                G n fixedX fixedY knownX knownY =
                G.conditionalXGivenY (knownY j) x := by
          rw [insertion]
          field_simp
        have coefficient :
            G.conditionalXGivenY (knownY j) x *
              (exactJointPrefixQuestionMass G n
                (insert j fixedX) fixedY
                (Function.update knownX j x) knownY)⁻¹ =
              (exactJointPrefixQuestionMass
                G n fixedX fixedY knownX knownY)⁻¹ := by
          rw [← conditional]
          field_simp
        rw [smul_smul, coefficient]
    _ = (exactJointPrefixQuestionMass
          G n fixedX fixedY knownX knownY)⁻¹ •
        (∑ x : X,
          exactJointPrefixAliceOperatorMass G n S D
            (insert j fixedX) fixedY answer
            (Function.update knownX j x) knownY) := by
          rw [Finset.smul_sum]
    _ = (exactJointPrefixQuestionMass
          G n fixedX fixedY knownX knownY)⁻¹ •
        exactJointPrefixAliceOperatorMass G n S D
          fixedX fixedY answer knownX knownY := by
          rw [exactJointPrefixAliceOperatorMass_sum_insert
            G n S D fixedX fixedY j fresh answer knownX knownY]


-- @@ L1036-1111 verbatim
private theorem exactJointPrefixBobOperatorFilter_martingale
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (opposite_fixed : j ∈ fixedX) (fresh : j ∉ fixedY)
    (answer : {k : Fin n // k ∈ D} → B)
    (knownX : Fin n → X) (knownY : Fin n → Y)
    (supported : exactJointPrefixQuestionMass
      G n fixedX fixedY knownX knownY ≠ 0) :
    (∑ y : Y, G.conditionalYGivenX (knownX j) y •
      exactJointPrefixBobOperatorFilter G n S D
        fixedX (insert j fixedY) answer
        knownX (Function.update knownY j y)) =
      exactJointPrefixBobOperatorFilter G n S D
        fixedX fixedY answer knownX knownY := by
  classical
  unfold exactJointPrefixBobOperatorFilter
  calc
    (∑ y : Y, G.conditionalYGivenX (knownX j) y •
      ((exactJointPrefixQuestionMass G n
        fixedX (insert j fixedY)
        knownX (Function.update knownY j y))⁻¹ •
        exactJointPrefixBobOperatorMass G n S D
          fixedX (insert j fixedY) answer
          knownX (Function.update knownY j y))) =
      ∑ y : Y,
        (exactJointPrefixQuestionMass
          G n fixedX fixedY knownX knownY)⁻¹ •
          exactJointPrefixBobOperatorMass G n S D
            fixedX (insert j fixedY) answer
            knownX (Function.update knownY j y) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases child_zero :
          exactJointPrefixQuestionMass G n
            fixedX (insert j fixedY)
            knownX (Function.update knownY j y) = 0
      · have matrix_zero :=
          exactJointPrefixBobOperatorMass_zero_of_mass_zero
            G n S D fixedX (insert j fixedY) answer
            knownX (Function.update knownY j y) child_zero
        rw [matrix_zero]
        simp only [smul_zero]
      · have insertion := exactJointPrefixQuestionMass_insert_bob
          G n fixedX fixedY j opposite_fixed fresh knownX knownY y
        have conditional :
            exactJointPrefixQuestionMass G n
                fixedX (insert j fixedY)
                knownX (Function.update knownY j y) /
              exactJointPrefixQuestionMass
                G n fixedX fixedY knownX knownY =
                G.conditionalYGivenX (knownX j) y := by
          rw [insertion]
          field_simp
        have coefficient :
            G.conditionalYGivenX (knownX j) y *
              (exactJointPrefixQuestionMass G n
                fixedX (insert j fixedY)
                knownX (Function.update knownY j y))⁻¹ =
              (exactJointPrefixQuestionMass
                G n fixedX fixedY knownX knownY)⁻¹ := by
          rw [← conditional]
          field_simp
        rw [smul_smul, coefficient]
    _ = (exactJointPrefixQuestionMass
          G n fixedX fixedY knownX knownY)⁻¹ •
        (∑ y : Y,
          exactJointPrefixBobOperatorMass G n S D
            fixedX (insert j fixedY) answer
            knownX (Function.update knownY j y)) := by
          rw [Finset.smul_sum]
    _ = (exactJointPrefixQuestionMass
          G n fixedX fixedY knownX knownY)⁻¹ •
        exactJointPrefixBobOperatorMass G n S D
          fixedX fixedY answer knownX knownY := by
          rw [exactJointPrefixBobOperatorMass_sum_insert
            G n S D fixedX fixedY j fresh answer knownX knownY]


-- @@ L1113-1113 verbatim
end


-- @@ L1115-1115 verbatim
section


-- @@ L1117-1118 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L1121-1121 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L1123-1123 verbatim
variable {X Y A B : Type*}

-- @@ L1124-1124 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L1126-1130 verbatim
private def exactFairAliceQuestionMask
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) : Finset (Fin n) :=
  (D ∪ (exactLeft seed.coordinate seed.partition).image
    Subtype.val) ∪ (exactRightPrefix seed).image Subtype.val


-- @@ L1132-1136 verbatim
private def exactFairBobQuestionMask
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) : Finset (Fin n) :=
  (D ∪ (exactRight seed.coordinate seed.partition).image
    Subtype.val) ∪ (exactLeftPrefix seed).image Subtype.val


-- @@ L1138-1228 verbatim
private theorem exactRevealCode_eq_iff_fair_question_masks
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q q' : ExactFullQuestion X Y n) :
    exactRevealCode D seed q' =
        exactRevealCode D seed q ↔
      (∀ j : Fin n,
        j ∈ exactFairAliceQuestionMask D seed →
          q'.1 j = q.1 j) ∧
      (∀ j : Fin n,
        j ∈ exactFairBobQuestionMask D seed →
          q'.2 j = q.2 j) := by
  classical
  constructor
  · intro same
    have aliceD := congrArg
      (fun h : ExactRevealHistory X Y D seed =>
        h.aliceConditioned) same
    have bobD := congrArg
      (fun h : ExactRevealHistory X Y D seed =>
        h.bobConditioned) same
    have aliceL := congrArg
      (fun h : ExactRevealHistory X Y D seed =>
        h.aliceLeft) same
    have bobR := congrArg
      (fun h : ExactRevealHistory X Y D seed =>
        h.bobRight) same
    have bobLP := congrArg
      (fun h : ExactRevealHistory X Y D seed =>
        h.bobLeftPrefix) same
    have aliceRP := congrArg
      (fun h : ExactRevealHistory X Y D seed =>
        h.aliceRightPrefix) same
    constructor
    · intro j hj
      change j ∈ (D ∪
        (exactLeft seed.coordinate seed.partition).image
          Subtype.val) ∪
        (exactRightPrefix seed).image Subtype.val at hj
      rcases Finset.mem_union.mp hj with hmain | hprefix
      · rcases Finset.mem_union.mp hmain with hD | hleft
        · exact congrFun aliceD ⟨j, hD⟩
        · obtain ⟨k, hk, samej⟩ := Finset.mem_image.mp hleft
          subst j
          exact congrFun aliceL ⟨k, hk⟩
      · obtain ⟨k, hk, samej⟩ := Finset.mem_image.mp hprefix
        subst j
        exact congrFun aliceRP ⟨k, hk⟩
    · intro j hj
      change j ∈ (D ∪
        (exactRight seed.coordinate seed.partition).image
          Subtype.val) ∪
        (exactLeftPrefix seed).image Subtype.val at hj
      rcases Finset.mem_union.mp hj with hmain | hprefix
      · rcases Finset.mem_union.mp hmain with hD | hright
        · exact congrFun bobD ⟨j, hD⟩
        · obtain ⟨k, hk, samej⟩ := Finset.mem_image.mp hright
          subst j
          exact congrFun bobR ⟨k, hk⟩
      · obtain ⟨k, hk, samej⟩ := Finset.mem_image.mp hprefix
        subst j
        exact congrFun bobLP ⟨k, hk⟩
  · rintro ⟨alice, bob⟩
    unfold exactRevealCode
    congr 1
    · funext j
      exact alice j.val <|
        Finset.mem_union_left _ <|
          Finset.mem_union_left _ j.property
    · funext j
      exact bob j.val <|
        Finset.mem_union_left _ <|
          Finset.mem_union_left _ j.property
    · funext j
      exact alice j.val.val <|
        Finset.mem_union_left _ <|
          Finset.mem_union_right _ <|
            Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩
    · funext j
      exact bob j.val.val <|
        Finset.mem_union_left _ <|
          Finset.mem_union_right _ <|
            Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩
    · funext j
      exact bob j.val.val <|
        Finset.mem_union_right _ <|
          Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩
    · funext j
      exact alice j.val.val <|
        Finset.mem_union_right _ <|
          Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩


-- @@ L1230-1290 verbatim
private theorem exactAliceQuestionMass_eq_jointPrefixQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) :
    exactAliceQuestionMass G n D seed
        (exactRevealCode D seed q)
        (q.1 seed.coordinate.val) =
      exactJointPrefixQuestionMass G n
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (exactFairBobQuestionMask D seed) q.1 q.2 := by
  classical
  unfold exactAliceQuestionMass
    exactJointPrefixQuestionMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have same :
      (exactRevealCode D seed (xs, ys) =
          exactRevealCode D seed q ∧
        xs seed.coordinate.val = q.1 seed.coordinate.val) ↔
      ((∀ j : Fin n,
        j ∈ insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed) →
          xs j = q.1 j) ∧
       (∀ j : Fin n,
        j ∈ exactFairBobQuestionMask D seed →
          ys j = q.2 j)) := by
    constructor
    · rintro ⟨history, distinguished⟩
      obtain ⟨alice, bob⟩ :=
        (exactRevealCode_eq_iff_fair_question_masks
          D seed q (xs, ys)).mp history
      refine ⟨?_, bob⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with samej | hj
      · subst j
        exact distinguished
      · exact alice j hj
    · rintro ⟨alice, bob⟩
      refine ⟨(exactRevealCode_eq_iff_fair_question_masks
        D seed q (xs, ys)).mpr ⟨?_, bob⟩, ?_⟩
      · intro j hj
        exact alice j (Finset.mem_insert_of_mem hj)
      · exact alice seed.coordinate.val
          (Finset.mem_insert_self _ _)
  by_cases compatible :
      (∀ j : Fin n,
        j ∈ insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed) →
          xs j = q.1 j) ∧
      (∀ j : Fin n,
        j ∈ exactFairBobQuestionMask D seed →
          ys j = q.2 j)
  · rw [ite_eq_left (same.mpr compatible), ite_eq_left compatible]
    rfl
  · rw [ite_eq_right (fun h => compatible (same.mp h)),
      ite_eq_right compatible]


-- @@ L1292-1352 verbatim
private theorem exactBobQuestionMass_eq_jointPrefixQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) :
    exactBobQuestionMass G n D seed
        (exactRevealCode D seed q)
        (q.2 seed.coordinate.val) =
      exactJointPrefixQuestionMass G n
        (exactFairAliceQuestionMask D seed)
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed)) q.1 q.2 := by
  classical
  unfold exactBobQuestionMass
    exactJointPrefixQuestionMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have same :
      (exactRevealCode D seed (xs, ys) =
          exactRevealCode D seed q ∧
        ys seed.coordinate.val = q.2 seed.coordinate.val) ↔
      ((∀ j : Fin n,
        j ∈ exactFairAliceQuestionMask D seed →
          xs j = q.1 j) ∧
       (∀ j : Fin n,
        j ∈ insert seed.coordinate.val
          (exactFairBobQuestionMask D seed) →
          ys j = q.2 j)) := by
    constructor
    · rintro ⟨history, distinguished⟩
      obtain ⟨alice, bob⟩ :=
        (exactRevealCode_eq_iff_fair_question_masks
          D seed q (xs, ys)).mp history
      refine ⟨alice, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with samej | hj
      · subst j
        exact distinguished
      · exact bob j hj
    · rintro ⟨alice, bob⟩
      refine ⟨(exactRevealCode_eq_iff_fair_question_masks
        D seed q (xs, ys)).mpr ⟨alice, ?_⟩, ?_⟩
      · intro j hj
        exact bob j (Finset.mem_insert_of_mem hj)
      · exact bob seed.coordinate.val
          (Finset.mem_insert_self _ _)
  by_cases compatible :
      (∀ j : Fin n,
        j ∈ exactFairAliceQuestionMask D seed →
          xs j = q.1 j) ∧
      (∀ j : Fin n,
        j ∈ insert seed.coordinate.val
          (exactFairBobQuestionMask D seed) →
          ys j = q.2 j)
  · rw [ite_eq_left (same.mpr compatible), ite_eq_left compatible]
    rfl
  · rw [ite_eq_right (fun h => compatible (same.mp h)),
      ite_eq_right compatible]


-- @@ L1354-1424 verbatim
private theorem exactAliceQuestionFilter_eq_jointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → A) :
    exactAliceQuestionFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.1 seed.coordinate.val) =
      exactJointPrefixAliceOperatorFilter G n S D
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (exactFairBobQuestionMask D seed)
        answer q.1 q.2 := by
  classical
  unfold exactAliceQuestionFilter
  rw [exactAliceQuestionMass_eq_jointPrefixQuestionMass
    G n D seed q]
  unfold exactJointPrefixAliceOperatorFilter
    exactJointPrefixAliceOperatorMass
  rw [Fintype.sum_prod_type]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have same :
      (exactRevealCode D seed (xs, ys) =
          exactRevealCode D seed q ∧
        xs seed.coordinate.val = q.1 seed.coordinate.val) ↔
      ((∀ j : Fin n,
        j ∈ insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed) →
          xs j = q.1 j) ∧
       (∀ j : Fin n,
        j ∈ exactFairBobQuestionMask D seed →
          ys j = q.2 j)) := by
    constructor
    · rintro ⟨history, distinguished⟩
      obtain ⟨alice, bob⟩ :=
        (exactRevealCode_eq_iff_fair_question_masks
          D seed q (xs, ys)).mp history
      refine ⟨?_, bob⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with samej | hj
      · subst j
        exact distinguished
      · exact alice j hj
    · rintro ⟨alice, bob⟩
      refine ⟨(exactRevealCode_eq_iff_fair_question_masks
        D seed q (xs, ys)).mpr ⟨?_, bob⟩, ?_⟩
      · intro j hj
        exact alice j (Finset.mem_insert_of_mem hj)
      · exact alice seed.coordinate.val
          (Finset.mem_insert_self _ _)
  by_cases compatible :
      (∀ j : Fin n,
        j ∈ insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed) →
          xs j = q.1 j) ∧
      (∀ j : Fin n,
        j ∈ exactFairBobQuestionMask D seed →
          ys j = q.2 j)
  · rw [ite_eq_left (same.mpr compatible), ite_eq_left compatible,
      smul_smul]
    unfold exactPriorQuestionWeight
    rw [div_eq_mul_inv]
    congr 1
    ring
  · rw [ite_eq_right (fun h => compatible (same.mp h)),
      ite_eq_right compatible, smul_zero]


-- @@ L1426-1496 verbatim
private theorem exactBobQuestionFilter_eq_jointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → B) :
    exactBobQuestionFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.2 seed.coordinate.val) =
      exactJointPrefixBobOperatorFilter G n S D
        (exactFairAliceQuestionMask D seed)
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed))
        answer q.1 q.2 := by
  classical
  unfold exactBobQuestionFilter
  rw [exactBobQuestionMass_eq_jointPrefixQuestionMass
    G n D seed q]
  unfold exactJointPrefixBobOperatorFilter
    exactJointPrefixBobOperatorMass
  rw [Fintype.sum_prod_type]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have same :
      (exactRevealCode D seed (xs, ys) =
          exactRevealCode D seed q ∧
        ys seed.coordinate.val = q.2 seed.coordinate.val) ↔
      ((∀ j : Fin n,
        j ∈ exactFairAliceQuestionMask D seed →
          xs j = q.1 j) ∧
       (∀ j : Fin n,
        j ∈ insert seed.coordinate.val
          (exactFairBobQuestionMask D seed) →
          ys j = q.2 j)) := by
    constructor
    · rintro ⟨history, distinguished⟩
      obtain ⟨alice, bob⟩ :=
        (exactRevealCode_eq_iff_fair_question_masks
          D seed q (xs, ys)).mp history
      refine ⟨alice, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with samej | hj
      · subst j
        exact distinguished
      · exact bob j hj
    · rintro ⟨alice, bob⟩
      refine ⟨(exactRevealCode_eq_iff_fair_question_masks
        D seed q (xs, ys)).mpr ⟨alice, ?_⟩, ?_⟩
      · intro j hj
        exact bob j (Finset.mem_insert_of_mem hj)
      · exact bob seed.coordinate.val
          (Finset.mem_insert_self _ _)
  by_cases compatible :
      (∀ j : Fin n,
        j ∈ exactFairAliceQuestionMask D seed →
          xs j = q.1 j) ∧
      (∀ j : Fin n,
        j ∈ insert seed.coordinate.val
          (exactFairBobQuestionMask D seed) →
          ys j = q.2 j)
  · rw [ite_eq_left (same.mpr compatible), ite_eq_left compatible,
      smul_smul]
    unfold exactPriorQuestionWeight
    rw [div_eq_mul_inv]
    congr 1
    ring
  · rw [ite_eq_right (fun h => compatible (same.mp h)),
      ite_eq_right compatible, smul_zero]


-- @@ L1498-1498 verbatim
end


-- @@ L1500-1500 verbatim
section


-- @@ L1502-1503 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L1506-1506 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L1508-1508 verbatim
variable {X Y A B : Type*}

-- @@ L1509-1509 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L1511-1545 verbatim
private theorem exactJointPrefixAliceOperatorMass_eq_sum_bobMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n))
    (answer : {j : Fin n // j ∈ D} → A)
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    exactJointPrefixAliceOperatorMass
        G n S D fixedX fixedY answer knownX knownY =
      ∑ xs : Fin n → X,
        if ∀ j : Fin n, j ∈ fixedX → xs j = knownX j then
          exactFixedBobQuestionMass
              G n fixedY xs knownY •
            conditionedAliceEffect G n S D answer xs
        else 0 := by
  classical
  unfold exactJointPrefixAliceOperatorMass
  apply Finset.sum_congr rfl
  intro xs _
  by_cases compatible :
      ∀ j : Fin n, j ∈ fixedX → xs j = knownX j
  · rw [ite_eq_left compatible]
    unfold exactFixedBobQuestionMass
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro ys _
    by_cases bob_compatible :
        ∀ j : Fin n, j ∈ fixedY → ys j = knownY j
    · rw [ite_eq_left ⟨compatible, bob_compatible⟩,
        ite_eq_left bob_compatible]
    · rw [ite_eq_right (fun h => bob_compatible h.2),
        ite_eq_right bob_compatible, zero_smul]
  · rw [ite_eq_right compatible]
    apply Finset.sum_eq_zero
    intro ys _
    rw [ite_eq_right]
    exact fun h => compatible h.1


-- @@ L1547-1582 verbatim
private theorem exactJointPrefixBobOperatorMass_eq_sum_aliceMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n))
    (answer : {j : Fin n // j ∈ D} → B)
    (knownX : Fin n → X) (knownY : Fin n → Y) :
    exactJointPrefixBobOperatorMass
        G n S D fixedX fixedY answer knownX knownY =
      ∑ ys : Fin n → Y,
        if ∀ j : Fin n, j ∈ fixedY → ys j = knownY j then
          exactFixedAliceQuestionMass
              G n fixedX knownX ys •
            conditionedBobEffect G n S D answer ys
        else 0 := by
  classical
  unfold exactJointPrefixBobOperatorMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ys _
  by_cases compatible :
      ∀ j : Fin n, j ∈ fixedY → ys j = knownY j
  · rw [ite_eq_left compatible]
    unfold exactFixedAliceQuestionMass
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro xs _
    by_cases alice_compatible :
        ∀ j : Fin n, j ∈ fixedX → xs j = knownX j
    · rw [ite_eq_left ⟨alice_compatible, compatible⟩,
        ite_eq_left alice_compatible]
    · rw [ite_eq_right (fun h => alice_compatible h.1),
        ite_eq_right alice_compatible, zero_smul]
  · rw [ite_eq_right compatible]
    apply Finset.sum_eq_zero
    intro xs _
    rw [ite_eq_right]
    exact fun h => compatible h.2


-- @@ L1584-1608 verbatim
private theorem exactJointPrefixAliceOperatorMass_insert_bob
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (opposite_fixed : j ∈ fixedX) (fresh : j ∉ fixedY)
    (answer : {k : Fin n // k ∈ D} → A)
    (knownX : Fin n → X) (knownY : Fin n → Y) (y : Y) :
    exactJointPrefixAliceOperatorMass G n S D
        fixedX (insert j fixedY) answer
        knownX (Function.update knownY j y) =
      G.conditionalYGivenX (knownX j) y •
        exactJointPrefixAliceOperatorMass G n S D
          fixedX fixedY answer knownX knownY := by
  classical
  rw [exactJointPrefixAliceOperatorMass_eq_sum_bobMass,
    exactJointPrefixAliceOperatorMass_eq_sum_bobMass,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  by_cases compatible :
      ∀ k : Fin n, k ∈ fixedX → xs k = knownX k
  · rw [ite_eq_left compatible, ite_eq_left compatible,
      exactFixedBobQuestionMass_insert
        G n fixedY j fresh xs knownY y,
      compatible j opposite_fixed, smul_smul]
  · rw [ite_eq_right compatible, ite_eq_right compatible, smul_zero]


-- @@ L1610-1634 verbatim
private theorem exactJointPrefixBobOperatorMass_insert_alice
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (fresh : j ∉ fixedX) (opposite_fixed : j ∈ fixedY)
    (answer : {k : Fin n // k ∈ D} → B)
    (knownX : Fin n → X) (knownY : Fin n → Y) (x : X) :
    exactJointPrefixBobOperatorMass G n S D
        (insert j fixedX) fixedY answer
        (Function.update knownX j x) knownY =
      G.conditionalXGivenY (knownY j) x •
        exactJointPrefixBobOperatorMass G n S D
          fixedX fixedY answer knownX knownY := by
  classical
  rw [exactJointPrefixBobOperatorMass_eq_sum_aliceMass,
    exactJointPrefixBobOperatorMass_eq_sum_aliceMass,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ys _
  by_cases compatible :
      ∀ k : Fin n, k ∈ fixedY → ys k = knownY k
  · rw [ite_eq_left compatible, ite_eq_left compatible,
      exactFixedAliceQuestionMass_insert
        G n fixedX j fresh knownX ys x,
      compatible j opposite_fixed, smul_smul]
  · rw [ite_eq_right compatible, ite_eq_right compatible, smul_zero]


-- @@ L1636-1667 verbatim
private theorem exactJointPrefixAliceOperatorFilter_insert_bob
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (opposite_fixed : j ∈ fixedX) (fresh : j ∉ fixedY)
    (answer : {k : Fin n // k ∈ D} → A)
    (knownX : Fin n → X) (knownY : Fin n → Y) (y : Y)
    (edge : G.conditionalYGivenX (knownX j) y ≠ 0) :
    exactJointPrefixAliceOperatorFilter G n S D
        fixedX (insert j fixedY) answer
        knownX (Function.update knownY j y) =
      exactJointPrefixAliceOperatorFilter G n S D
        fixedX fixedY answer knownX knownY := by
  unfold exactJointPrefixAliceOperatorFilter
  rw [exactJointPrefixQuestionMass_insert_bob
      G n fixedX fixedY j opposite_fixed fresh knownX knownY y,
    exactJointPrefixAliceOperatorMass_insert_bob
      G n S D fixedX fixedY j opposite_fixed fresh answer
      knownX knownY y,
    smul_smul]
  have coefficient :
      (G.conditionalYGivenX (knownX j) y *
        exactJointPrefixQuestionMass G n
          fixedX fixedY knownX knownY)⁻¹ *
        G.conditionalYGivenX (knownX j) y =
      (exactJointPrefixQuestionMass G n
        fixedX fixedY knownX knownY)⁻¹ := by
    by_cases zero :
        exactJointPrefixQuestionMass
          G n fixedX fixedY knownX knownY = 0
    · simp only [zero, mul_zero, _root_.inv_zero, zero_mul]
    · field_simp
  rw [coefficient]


-- @@ L1669-1700 verbatim
private theorem exactJointPrefixBobOperatorFilter_insert_alice
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D fixedX fixedY : Finset (Fin n)) (j : Fin n)
    (fresh : j ∉ fixedX) (opposite_fixed : j ∈ fixedY)
    (answer : {k : Fin n // k ∈ D} → B)
    (knownX : Fin n → X) (knownY : Fin n → Y) (x : X)
    (edge : G.conditionalXGivenY (knownY j) x ≠ 0) :
    exactJointPrefixBobOperatorFilter G n S D
        (insert j fixedX) fixedY answer
        (Function.update knownX j x) knownY =
      exactJointPrefixBobOperatorFilter G n S D
        fixedX fixedY answer knownX knownY := by
  unfold exactJointPrefixBobOperatorFilter
  rw [exactJointPrefixQuestionMass_insert_alice
      G n fixedX fixedY j fresh opposite_fixed knownX knownY x,
    exactJointPrefixBobOperatorMass_insert_alice
      G n S D fixedX fixedY j fresh opposite_fixed answer
      knownX knownY x,
    smul_smul]
  have coefficient :
      (G.conditionalXGivenY (knownY j) x *
        exactJointPrefixQuestionMass G n
          fixedX fixedY knownX knownY)⁻¹ *
        G.conditionalXGivenY (knownY j) x =
      (exactJointPrefixQuestionMass G n
        fixedX fixedY knownX knownY)⁻¹ := by
    by_cases zero :
        exactJointPrefixQuestionMass
          G n fixedX fixedY knownX knownY = 0
    · simp only [zero, mul_zero, _root_.inv_zero, zero_mul]
    · field_simp
  rw [coefficient]


-- @@ L1702-1702 verbatim
end


-- @@ L1704-1704 verbatim
section


-- @@ L1706-1707 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L1710-1710 verbatim
open QuantumParallelRepetition.ClassicalInformation


-- @@ L1712-1712 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L1714-1714 verbatim
variable {X Y A B : Type*}

-- @@ L1715-1715 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L1717-1732 verbatim
theorem groupedMass_expectation
    {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
    (code : Ω → T) (weight : Ω → ℝ) (f : T → ℝ) :
    (∑ t : T, groupedMass code weight t * f t) =
      ∑ outcome : Ω, weight outcome * f (code outcome) := by
  classical
  unfold groupedMass
  simp only [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [Finset.sum_eq_single (code outcome)]
  · simp only [↓reduceIte]
  · intro t _ different
    simp only [different.symm, ↓reduceIte, zero_mul]
  · simp only [mem_univ, not_true_eq_false, ↓reduceIte, mul_eq_zero, IsEmpty.forall_iff]


-- @@ L1734-1766 verbatim
theorem exactJointQuestionMass_eq_groupedMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) :
    exactJointQuestionMass
        G n D seed history x y =
      groupedMass
        (fun q : ExactFullQuestion X Y n =>
          (exactRevealCode D seed q,
            q.1 seed.coordinate.val,
            q.2 seed.coordinate.val))
        (exactPriorQuestionWeight G n)
        (history, x, y) := by
  classical
  unfold exactJointQuestionMass groupedMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases compatible :
      exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x ∧
      q.2 seed.coordinate.val = y
  · rw [ite_eq_left compatible, ite_eq_left]
    exact Prod.ext compatible.1
      (Prod.ext compatible.2.1 compatible.2.2)
  · rw [ite_eq_right compatible, ite_eq_right]
    intro h
    exact compatible
      ⟨congrArg (fun t => t.1) h,
        congrArg (fun t => t.2.1) h,
        congrArg (fun t => t.2.2) h⟩


-- @@ L1768-1810 verbatim
theorem exactFairJointQuestionExpectation_reindex
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (f : ExactRevealHistory X Y D seed → X → Y → ℝ) :
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ x : X, ∑ y : Y,
        exactRevealMass G n D seed history *
          G.questionWeight x y * f history x y) =
      ∑ q : ExactFullQuestion X Y n,
        exactPriorQuestionWeight G n q *
          f (exactRevealCode D seed q)
            (q.1 seed.coordinate.val)
            (q.2 seed.coordinate.val) := by
  classical
  let code : ExactFullQuestion X Y n →
      ExactRevealHistory X Y D seed × X × Y :=
    fun q => (exactRevealCode D seed q,
      q.1 seed.coordinate.val, q.2 seed.coordinate.val)
  have expectation := groupedMass_expectation
    code (exactPriorQuestionWeight G n)
    (fun t : ExactRevealHistory X Y D seed × X × Y =>
      f t.1 t.2.1 t.2.2)
  simp only [Fintype.sum_prod_type] at expectation
  calc
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ x : X, ∑ y : Y,
        exactRevealMass G n D seed history *
          G.questionWeight x y * f history x y) =
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ x : X, ∑ y : Y,
        groupedMass code (exactPriorQuestionWeight G n)
          (history, x, y) * f history x y := by
        apply Finset.sum_congr rfl
        intro history _
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [← exactJointQuestionMass_eq_groupedMass]
        rw [exactJointQuestionMass_eq_reveal_mul_question]
    _ = _ := by
      simpa only [Fintype.sum_prod_type, code] using expectation


-- @@ L1812-1812 verbatim
end


-- @@ L1814-1814 verbatim
section


-- @@ L1816-1817 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L1820-1820 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L1822-1822 verbatim
variable {X Y A B : Type*}

-- @@ L1823-1823 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L1825-1876 verbatim
theorem exactFairAliceHistoryHighOperatorPotential_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairAliceHistoryHighOperatorPotential G n S D r =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x))
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
  classical
  unfold exactFairAliceHistoryHighOperatorPotential
  simp only [map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  calc
    (∑ y : Y, G.marginalY y *
      (∑ x : X, G.conditionalXGivenY y x *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x))
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y))) =
      ∑ y : Y, ∑ x : X,
        (G.marginalY y * G.conditionalXGivenY y x) *
          bornTracePairing S.state.matrix
            (cfc (fun z : ℝ => z * Real.log z)
              (exactAliceQuestionFilter
                G n S D r.seed r.history r.aliceAnswer x))
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = ∑ y : Y, ∑ x : X, G.questionWeight x y *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x))
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro x _
        rw [← G.marginalY_mul_conditionalXGivenY x y]
    _ = _ := Finset.sum_comm


-- @@ L1878-1899 verbatim
theorem exactFairBobHistoryHighOperatorPotential_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairBobHistoryHighOperatorPotential G n S D r =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (cfc (fun z : ℝ => z * Real.log z)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y)) := by
  classical
  unfold exactFairBobHistoryHighOperatorPotential
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← G.marginalX_mul_conditionalYGivenX x y]
  ring


-- @@ L1901-1934 verbatim
theorem exactFairAliceHistoryLowOperatorPotential_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairAliceHistoryLowOperatorPotential G n S D r =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (exactAliceMeanFilter
              G n S D r.seed r.history r.aliceAnswer y))
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
  classical
  unfold exactFairAliceHistoryLowOperatorPotential
  calc
    (∑ y : Y, G.marginalY y *
      bornTracePairing S.state.matrix
        (cfc (fun z : ℝ => z * Real.log z)
          (exactAliceMeanFilter
            G n S D r.seed r.history r.aliceAnswer y))
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y)) =
      ∑ y : Y, ∑ x : X, G.questionWeight x y *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (exactAliceMeanFilter
              G n S D r.seed r.history r.aliceAnswer y))
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
        apply Finset.sum_congr rfl
        intro y _
        unfold Game.marginalY
        rw [Finset.sum_mul]
    _ = _ := Finset.sum_comm


-- @@ L1936-1953 verbatim
theorem exactFairBobHistoryLowOperatorPotential_eq_joint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairBobHistoryLowOperatorPotential G n S D r =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (cfc (fun z : ℝ => z * Real.log z)
            (exactBobMeanFilter
              G n S D r.seed r.history r.bobAnswer x)) := by
  classical
  unfold exactFairBobHistoryLowOperatorPotential
  apply Finset.sum_congr rfl
  intro x _
  unfold Game.marginalX
  rw [Finset.sum_mul]


-- @@ L1955-2068 verbatim
theorem exactFairAcceptedJointStatistic_reindex
    (G : Game X Y A B) (n : ℕ) (_ : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (f : ExactRevealHistory X Y D seed →
      ({j : Fin n // j ∈ D} → A) →
      ({j : Fin n // j ∈ D} → B) → X → Y → ℝ) :
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            (∑ x : X, ∑ y : Y,
              G.questionWeight x y *
                f history aliceAnswer bobAnswer x y)
        else 0) =
      ∑ q : ExactFullQuestion X Y n,
        exactPriorQuestionWeight G n q *
          (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
           ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
            if exactHistoryAccepted G n D
              ⟨seed, exactRevealCode D seed q,
                aliceAnswer, bobAnswer⟩ then
              f (exactRevealCode D seed q)
                aliceAnswer bobAnswer
                (q.1 seed.coordinate.val)
                (q.2 seed.coordinate.val)
            else 0) := by
  classical
  have expectation := exactFairJointQuestionExpectation_reindex
    G n D seed (fun history x y =>
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          f history aliceAnswer bobAnswer x y
        else 0)
  calc
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            (∑ x : X, ∑ y : Y,
              G.questionWeight x y *
                f history aliceAnswer bobAnswer x y)
        else 0) =
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
      ∑ x : X, ∑ y : Y,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            G.questionWeight x y *
            f history aliceAnswer bobAnswer x y
        else 0 := by
          apply Finset.sum_congr rfl
          intro history _
          apply Finset.sum_congr rfl
          intro aliceAnswer _
          apply Finset.sum_congr rfl
          intro bobAnswer _
          by_cases accepted : exactHistoryAccepted G n D
              ⟨seed, history, aliceAnswer, bobAnswer⟩
          · simp only [ite_eq_left accepted, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            ring
          · simp only [accepted, ↓reduceIte, sum_const_zero]
    _ = ∑ history : ExactRevealHistory X Y D seed,
      ∑ x : X, ∑ y : Y,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            G.questionWeight x y *
            f history aliceAnswer bobAnswer x y
        else 0 := by
          apply Finset.sum_congr rfl
          intro history _
          exact finite_sum_four_swap _
    _ = ∑ history : ExactRevealHistory X Y D seed,
      ∑ x : X, ∑ y : Y,
        exactRevealMass G n D seed history *
          G.questionWeight x y *
          (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
           ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
            if exactHistoryAccepted G n D
              ⟨seed, history, aliceAnswer, bobAnswer⟩ then
              f history aliceAnswer bobAnswer x y
            else 0) := by
          apply Finset.sum_congr rfl
          intro history _
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro aliceAnswer _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro bobAnswer _
          by_cases accepted : exactHistoryAccepted G n D
              ⟨seed, history, aliceAnswer, bobAnswer⟩
          · rw [ite_eq_left accepted, ite_eq_left accepted]
          · rw [ite_eq_right accepted, ite_eq_right accepted, mul_zero]
    _ = _ := expectation


-- @@ L2070-2070 verbatim
end


-- @@ L2072-2072 verbatim
section


-- @@ L2074-2075 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L2078-2078 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L2080-2080 verbatim
variable {X Y A B : Type*}

-- @@ L2081-2081 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L2083-2106 verbatim
private def exactReverseAliceHighQuestionPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ q : ExactFullQuestion X Y n,
    exactPriorQuestionWeight G n q *
      (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
       ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ then
          bornTracePairing S.state.matrix
            (cfc (fun z : ℝ => z * Real.log z)
              (exactAliceQuestionFilter G n S D seed
                (exactRevealCode D seed q)
                aliceAnswer (q.1 seed.coordinate.val)))
            (exactBobQuestionFilter G n S D seed
              (exactRevealCode D seed q)
              bobAnswer (q.2 seed.coordinate.val))
        else 0)


-- @@ L2108-2131 verbatim
private def exactReverseAliceLowQuestionPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ q : ExactFullQuestion X Y n,
    exactPriorQuestionWeight G n q *
      (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
       ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ then
          bornTracePairing S.state.matrix
            (cfc (fun z : ℝ => z * Real.log z)
              (exactAliceMeanFilter G n S D seed
                (exactRevealCode D seed q)
                aliceAnswer (q.2 seed.coordinate.val)))
            (exactBobQuestionFilter G n S D seed
              (exactRevealCode D seed q)
              bobAnswer (q.2 seed.coordinate.val))
        else 0)


-- @@ L2133-2156 verbatim
private def exactReverseBobHighQuestionPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ q : ExactFullQuestion X Y n,
    exactPriorQuestionWeight G n q *
      (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
       ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ then
          bornTracePairing S.state.matrix
            (exactAliceQuestionFilter G n S D seed
              (exactRevealCode D seed q)
              aliceAnswer (q.1 seed.coordinate.val))
            (cfc (fun z : ℝ => z * Real.log z)
              (exactBobQuestionFilter G n S D seed
                (exactRevealCode D seed q)
                bobAnswer (q.2 seed.coordinate.val)))
        else 0)


-- @@ L2158-2181 verbatim
private def exactReverseBobLowQuestionPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ q : ExactFullQuestion X Y n,
    exactPriorQuestionWeight G n q *
      (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
       ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ then
          bornTracePairing S.state.matrix
            (exactAliceQuestionFilter G n S D seed
              (exactRevealCode D seed q)
              aliceAnswer (q.1 seed.coordinate.val))
            (cfc (fun z : ℝ => z * Real.log z)
              (exactBobMeanFilter G n S D seed
                (exactRevealCode D seed q)
                bobAnswer (q.1 seed.coordinate.val)))
        else 0)


-- @@ L2183-2252 verbatim
private theorem exactReverseAliceHighOperatorPotential_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceFilterHighOperatorPotential
        G n S D side context marker =
      exactReverseAliceHighQuestionPotential
        G n S D side context marker := by
  classical
  unfold exactReverseAliceFilterHighOperatorPotential
    exactReverseAliceHighQuestionPotential
  dsimp only
  calc
    (∑ history : ExactRevealHistory X Y D
        (exactReverseBobMarkerDecode side context marker),
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨exactReverseBobMarkerDecode side context marker,
            history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D
            (exactReverseBobMarkerDecode side context marker)
            history *
          exactFairAliceHistoryHighOperatorPotential G n S D
            ⟨exactReverseBobMarkerDecode side context marker,
              history, aliceAnswer, bobAnswer⟩
        else 0) =
      ∑ history : ExactRevealHistory X Y D
        (exactReverseBobMarkerDecode side context marker),
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨exactReverseBobMarkerDecode side context marker,
            history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D
            (exactReverseBobMarkerDecode side context marker)
            history *
            (∑ x : X, ∑ y : Y, G.questionWeight x y *
              bornTracePairing S.state.matrix
                (cfc (fun z : ℝ => z * Real.log z)
                  (exactAliceQuestionFilter G n S D
                    (exactReverseBobMarkerDecode side context marker)
                    history aliceAnswer x))
                (exactBobQuestionFilter G n S D
                  (exactReverseBobMarkerDecode side context marker)
                  history bobAnswer y))
        else 0 := by
          apply Finset.sum_congr rfl
          intro history _
          apply Finset.sum_congr rfl
          intro aliceAnswer _
          apply Finset.sum_congr rfl
          intro bobAnswer _
          split
          · rw [exactFairAliceHistoryHighOperatorPotential_eq_joint]
          · rfl
    _ = _ := exactFairAcceptedJointStatistic_reindex
      G n S D (exactReverseBobMarkerDecode side context marker)
      (fun history aliceAnswer bobAnswer x y =>
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (exactAliceQuestionFilter G n S D
              (exactReverseBobMarkerDecode side context marker)
              history aliceAnswer x))
          (exactBobQuestionFilter G n S D
            (exactReverseBobMarkerDecode side context marker)
            history bobAnswer y))


-- @@ L2254-2323 verbatim
private theorem exactReverseAliceLowOperatorPotential_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceFilterLowOperatorPotential
        G n S D side context marker =
      exactReverseAliceLowQuestionPotential
        G n S D side context marker := by
  classical
  unfold exactReverseAliceFilterLowOperatorPotential
    exactReverseAliceLowQuestionPotential
  dsimp only
  calc
    (∑ history : ExactRevealHistory X Y D
        (exactReverseBobMarkerDecode side context marker),
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨exactReverseBobMarkerDecode side context marker,
            history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D
            (exactReverseBobMarkerDecode side context marker)
            history *
          exactFairAliceHistoryLowOperatorPotential G n S D
            ⟨exactReverseBobMarkerDecode side context marker,
              history, aliceAnswer, bobAnswer⟩
        else 0) =
      ∑ history : ExactRevealHistory X Y D
        (exactReverseBobMarkerDecode side context marker),
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨exactReverseBobMarkerDecode side context marker,
            history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D
            (exactReverseBobMarkerDecode side context marker)
            history *
            (∑ x : X, ∑ y : Y, G.questionWeight x y *
              bornTracePairing S.state.matrix
                (cfc (fun z : ℝ => z * Real.log z)
                  (exactAliceMeanFilter G n S D
                    (exactReverseBobMarkerDecode side context marker)
                    history aliceAnswer y))
                (exactBobQuestionFilter G n S D
                  (exactReverseBobMarkerDecode side context marker)
                  history bobAnswer y))
        else 0 := by
          apply Finset.sum_congr rfl
          intro history _
          apply Finset.sum_congr rfl
          intro aliceAnswer _
          apply Finset.sum_congr rfl
          intro bobAnswer _
          split
          · rw [exactFairAliceHistoryLowOperatorPotential_eq_joint]
          · rfl
    _ = _ := exactFairAcceptedJointStatistic_reindex
      G n S D (exactReverseBobMarkerDecode side context marker)
      (fun history aliceAnswer bobAnswer x y =>
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (exactAliceMeanFilter G n S D
              (exactReverseBobMarkerDecode side context marker)
              history aliceAnswer y))
          (exactBobQuestionFilter G n S D
            (exactReverseBobMarkerDecode side context marker)
            history bobAnswer y))


-- @@ L2325-2394 verbatim
private theorem exactReverseBobHighOperatorPotential_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobFilterHighOperatorPotential
        G n S D side context marker =
      exactReverseBobHighQuestionPotential
        G n S D side context marker := by
  classical
  unfold exactReverseBobFilterHighOperatorPotential
    exactReverseBobHighQuestionPotential
  dsimp only
  calc
    (∑ history : ExactRevealHistory X Y D
        (exactReverseAliceMarkerDecode side context marker),
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨exactReverseAliceMarkerDecode side context marker,
            history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D
            (exactReverseAliceMarkerDecode side context marker)
            history *
          exactFairBobHistoryHighOperatorPotential G n S D
            ⟨exactReverseAliceMarkerDecode side context marker,
              history, aliceAnswer, bobAnswer⟩
        else 0) =
      ∑ history : ExactRevealHistory X Y D
        (exactReverseAliceMarkerDecode side context marker),
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨exactReverseAliceMarkerDecode side context marker,
            history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D
            (exactReverseAliceMarkerDecode side context marker)
            history *
            (∑ x : X, ∑ y : Y, G.questionWeight x y *
              bornTracePairing S.state.matrix
                (exactAliceQuestionFilter G n S D
                  (exactReverseAliceMarkerDecode side context marker)
                  history aliceAnswer x)
                (cfc (fun z : ℝ => z * Real.log z)
                  (exactBobQuestionFilter G n S D
                    (exactReverseAliceMarkerDecode side context marker)
                    history bobAnswer y)))
        else 0 := by
          apply Finset.sum_congr rfl
          intro history _
          apply Finset.sum_congr rfl
          intro aliceAnswer _
          apply Finset.sum_congr rfl
          intro bobAnswer _
          split
          · rw [exactFairBobHistoryHighOperatorPotential_eq_joint]
          · rfl
    _ = _ := exactFairAcceptedJointStatistic_reindex
      G n S D (exactReverseAliceMarkerDecode side context marker)
      (fun history aliceAnswer bobAnswer x y =>
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter G n S D
            (exactReverseAliceMarkerDecode side context marker)
            history aliceAnswer x)
          (cfc (fun z : ℝ => z * Real.log z)
            (exactBobQuestionFilter G n S D
              (exactReverseAliceMarkerDecode side context marker)
              history bobAnswer y)))


-- @@ L2396-2465 verbatim
private theorem exactReverseBobLowOperatorPotential_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobFilterLowOperatorPotential
        G n S D side context marker =
      exactReverseBobLowQuestionPotential
        G n S D side context marker := by
  classical
  unfold exactReverseBobFilterLowOperatorPotential
    exactReverseBobLowQuestionPotential
  dsimp only
  calc
    (∑ history : ExactRevealHistory X Y D
        (exactReverseAliceMarkerDecode side context marker),
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨exactReverseAliceMarkerDecode side context marker,
            history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D
            (exactReverseAliceMarkerDecode side context marker)
            history *
          exactFairBobHistoryLowOperatorPotential G n S D
            ⟨exactReverseAliceMarkerDecode side context marker,
              history, aliceAnswer, bobAnswer⟩
        else 0) =
      ∑ history : ExactRevealHistory X Y D
        (exactReverseAliceMarkerDecode side context marker),
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨exactReverseAliceMarkerDecode side context marker,
            history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D
            (exactReverseAliceMarkerDecode side context marker)
            history *
            (∑ x : X, ∑ y : Y, G.questionWeight x y *
              bornTracePairing S.state.matrix
                (exactAliceQuestionFilter G n S D
                  (exactReverseAliceMarkerDecode side context marker)
                  history aliceAnswer x)
                (cfc (fun z : ℝ => z * Real.log z)
                  (exactBobMeanFilter G n S D
                    (exactReverseAliceMarkerDecode side context marker)
                    history bobAnswer x)))
        else 0 := by
          apply Finset.sum_congr rfl
          intro history _
          apply Finset.sum_congr rfl
          intro aliceAnswer _
          apply Finset.sum_congr rfl
          intro bobAnswer _
          split
          · rw [exactFairBobHistoryLowOperatorPotential_eq_joint]
          · rfl
    _ = _ := exactFairAcceptedJointStatistic_reindex
      G n S D (exactReverseAliceMarkerDecode side context marker)
      (fun history aliceAnswer bobAnswer x y =>
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter G n S D
            (exactReverseAliceMarkerDecode side context marker)
            history aliceAnswer x)
          (cfc (fun z : ℝ => z * Real.log z)
            (exactBobMeanFilter G n S D
              (exactReverseAliceMarkerDecode side context marker)
              history bobAnswer x)))


-- @@ L2467-2482 verbatim
private theorem exactReverseAliceFilterOperatorMarkerEntropy_eq_question_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceFilterOperatorMarkerEntropy
        G n S D side context marker =
      exactReverseAliceHighQuestionPotential
          G n S D side context marker -
        exactReverseAliceLowQuestionPotential
          G n S D side context marker := by
  rw [exactReverseAliceFilterOperatorMarkerEntropy_eq_sub,
    exactReverseAliceHighOperatorPotential_eq_question,
    exactReverseAliceLowOperatorPotential_eq_question]


-- @@ L2484-2499 verbatim
private theorem exactReverseBobFilterOperatorMarkerEntropy_eq_question_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobFilterOperatorMarkerEntropy
        G n S D side context marker =
      exactReverseBobHighQuestionPotential
          G n S D side context marker -
        exactReverseBobLowQuestionPotential
          G n S D side context marker := by
  rw [exactReverseBobFilterOperatorMarkerEntropy_eq_sub,
    exactReverseBobHighOperatorPotential_eq_question,
    exactReverseBobLowOperatorPotential_eq_question]


-- @@ L2501-2501 verbatim
end


-- @@ L2503-2503 verbatim
section


-- @@ L2505-2506 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L2509-2509 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L2511-2511 verbatim
variable {X Y A B : Type*}

-- @@ L2512-2512 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L2514-2523 verbatim
private def exactReverseContextQuestionPrefix
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter
    (fun j : {j : SourceRemainingCoordinate D // j ∈ side} =>
      (context.sideRank j).val < k)).image
    (fun j => j.val.val)


-- @@ L2525-2532 verbatim
private def exactReverseAlicePrefixXMask
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (k : ℕ) : Finset (Fin n) :=
  (D ∪ context.otherSide.image Subtype.val) ∪
    exactReverseContextQuestionPrefix D side context k


-- @@ L2534-2540 verbatim
private def exactReverseAliceFixedYMask
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side) : Finset (Fin n) :=
  (D ∪ side.image Subtype.val) ∪
    (exactReverseContextOtherPrefix context).image Subtype.val


-- @@ L2542-2548 verbatim
private def exactReverseBobFixedXMask
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side) : Finset (Fin n) :=
  (D ∪ side.image Subtype.val) ∪
    (exactReverseContextOtherPrefix context).image Subtype.val


-- @@ L2550-2557 verbatim
private def exactReverseBobPrefixYMask
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (k : ℕ) : Finset (Fin n) :=
  (D ∪ context.otherSide.image Subtype.val) ∪
    exactReverseContextQuestionPrefix D side context k


-- @@ L2559-2559 verbatim
end


-- @@ L2561-2561 verbatim
section


-- @@ L2563-2564 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L2567-2567 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L2569-2569 verbatim
variable {X Y A B : Type*}

-- @@ L2570-2570 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L2572-2587 verbatim
private theorem exactReverseContextQuestionPrefix_eq_image
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseContextQuestionPrefix
        D side context marker.val =
      (exactReverseContextPrefixBefore
        context marker).image Subtype.val := by
  classical
  unfold exactReverseContextQuestionPrefix
    exactReverseContextPrefixBefore
    exactOrderedSidePrefix
  rw [Finset.image_image]
  rfl


-- @@ L2589-2604 verbatim
private theorem exactReverseAlicePrefixXMask_eq_fair
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    exactReverseAlicePrefixXMask D
        (exactReverseRightSide seed)
        (exactReverseBobContext seed)
        (((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩).val) =
      exactFairAliceQuestionMask D seed := by
  classical
  unfold exactReverseAlicePrefixXMask
    exactFairAliceQuestionMask
  rw [exactReverseContextQuestionPrefix_eq_image,
    exactReverseBobContext_prefix_before_marked]
  rfl


-- @@ L2606-2621 verbatim
private theorem exactReverseAliceFixedYMask_eq_insert_fair
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    exactReverseAliceFixedYMask D
        (exactReverseRightSide seed)
        (exactReverseBobContext seed) =
      insert seed.coordinate.val
        (exactFairBobQuestionMask D seed) := by
  classical
  unfold exactReverseAliceFixedYMask
    exactFairBobQuestionMask
  rw [exactReverseBobContext_otherPrefix]
  unfold exactReverseRightSide
  rw [Finset.image_insert]
  ext j
  simp only [Finset.mem_union, Finset.mem_insert, or_assoc, or_left_comm]


-- @@ L2623-2638 verbatim
private theorem exactReverseBobFixedXMask_eq_insert_fair
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    exactReverseBobFixedXMask D
        (exactReverseLeftSide seed)
        (exactReverseAliceContext seed) =
      insert seed.coordinate.val
        (exactFairAliceQuestionMask D seed) := by
  classical
  unfold exactReverseBobFixedXMask
    exactFairAliceQuestionMask
  rw [exactReverseAliceContext_otherPrefix]
  unfold exactReverseLeftSide
  rw [Finset.image_insert]
  ext j
  simp only [Finset.mem_union, Finset.mem_insert, or_assoc, or_left_comm]


-- @@ L2640-2655 verbatim
private theorem exactReverseBobPrefixYMask_eq_fair
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    exactReverseBobPrefixYMask D
        (exactReverseLeftSide seed)
        (exactReverseAliceContext seed)
        (((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩).val) =
      exactFairBobQuestionMask D seed := by
  classical
  unfold exactReverseBobPrefixYMask
    exactFairBobQuestionMask
  rw [exactReverseContextQuestionPrefix_eq_image,
    exactReverseAliceContext_prefix_before_marked]
  rfl


-- @@ L2657-2657 verbatim
end


-- @@ L2659-2659 verbatim
section


-- @@ L2661-2662 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L2665-2665 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L2667-2667 verbatim
variable {X Y A B : Type*}

-- @@ L2668-2668 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L2670-2716 verbatim
private theorem exactReverseContextQuestionPrefix_succ
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseContextQuestionPrefix
        D side context (marker.val + 1) =
      insert (context.sideRank.symm marker).val.val
        (exactReverseContextQuestionPrefix
          D side context marker.val) := by
  classical
  ext j
  constructor
  · intro member
    obtain ⟨a, ha, equation⟩ := Finset.mem_image.mp member
    have lower := (Finset.mem_filter.mp ha).2
    have below : (context.sideRank a).val ≤ marker.val :=
      Nat.lt_succ_iff.mp (by simpa only [Nat.succ_eq_add_one, Order.lt_add_one_iff,
                               Fin.val_fin_le] using lower)
    rcases Nat.lt_or_eq_of_le below with earlier | same_rank
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr
          ⟨Finset.mem_univ a, earlier⟩, equation⟩
    · have same : context.sideRank a = marker :=
        Fin.ext same_rank
      have position : a = context.sideRank.symm marker := by
        apply context.sideRank.injective
        simpa only [Equiv.apply_symm_apply] using same
      subst a
      exact Finset.mem_insert.mpr (Or.inl equation.symm)
  · intro member
    rcases Finset.mem_insert.mp member with marked | earlier
    · subst j
      apply Finset.mem_image.mpr
      refine ⟨context.sideRank.symm marker, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Equiv.apply_symm_apply, lt_add_iff_pos_right, Order.lt_one_iff]
    · obtain ⟨a, ha, equation⟩ := Finset.mem_image.mp earlier
      apply Finset.mem_image.mpr
      refine ⟨a, ?_, equation⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ a,
        Nat.lt_trans (Finset.mem_filter.mp ha).2
          (Nat.lt_succ_self marker.val)⟩


-- @@ L2718-2739 verbatim
private theorem exactFairAliceQuestionMask_coordinate_not_mem
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    seed.coordinate.val ∉ exactFairAliceQuestionMask D seed := by
  classical
  intro member
  change seed.coordinate.val ∈
    (D ∪ (exactLeft seed.coordinate seed.partition).image
      Subtype.val) ∪
      (exactRightPrefix seed).image Subtype.val at member
  rcases Finset.mem_union.mp member with main | exposed
  · rcases Finset.mem_union.mp main with conditioned | left
    · exact (Finset.mem_sdiff.mp seed.coordinate.property).2 conditioned
    · obtain ⟨a, ha, same⟩ := Finset.mem_image.mp left
      have equal : a = seed.coordinate := Subtype.ext same
      exact exactLeft_coordinate_not_mem
        seed.coordinate seed.partition (equal ▸ ha)
  · obtain ⟨a, ha, same⟩ := Finset.mem_image.mp exposed
    have equal : a = seed.coordinate := Subtype.ext same
    have belongs := exactRightPrefix_subset seed ha
    exact exactRight_coordinate_not_mem
      seed.coordinate seed.partition (equal ▸ belongs)


-- @@ L2741-2762 verbatim
private theorem exactFairBobQuestionMask_coordinate_not_mem
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    seed.coordinate.val ∉ exactFairBobQuestionMask D seed := by
  classical
  intro member
  change seed.coordinate.val ∈
    (D ∪ (exactRight seed.coordinate seed.partition).image
      Subtype.val) ∪
      (exactLeftPrefix seed).image Subtype.val at member
  rcases Finset.mem_union.mp member with main | exposed
  · rcases Finset.mem_union.mp main with conditioned | right
    · exact (Finset.mem_sdiff.mp seed.coordinate.property).2 conditioned
    · obtain ⟨a, ha, same⟩ := Finset.mem_image.mp right
      have equal : a = seed.coordinate := Subtype.ext same
      exact exactRight_coordinate_not_mem
        seed.coordinate seed.partition (equal ▸ ha)
  · obtain ⟨a, ha, same⟩ := Finset.mem_image.mp exposed
    have equal : a = seed.coordinate := Subtype.ext same
    have belongs := exactLeftPrefix_subset seed ha
    exact exactLeft_coordinate_not_mem
      seed.coordinate seed.partition (equal ▸ belongs)


-- @@ L2764-2790 verbatim
private def exactReverseAliceAlignedCfcPrefixPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (k : ℕ) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    exactPriorQuestionWeight G n q *
      (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
       ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if ∀ j : {j : Fin n // j ∈ D},
          G.predicate (q.1 j.val) (q.2 j.val)
            (aliceAnswer j) (bobAnswer j) = true then
          bornTracePairing S.state.matrix
            (cfc (fun z : ℝ => z * Real.log z)
              (exactJointPrefixAliceOperatorFilter G n S D
                (exactReverseAlicePrefixXMask
                  D side context k)
                (exactReverseAliceFixedYMask D side context)
                aliceAnswer q.1 q.2))
            (exactJointPrefixBobOperatorFilter G n S D
              (exactReverseAlicePrefixXMask
                D side context k)
              (exactReverseAliceFixedYMask D side context)
              bobAnswer q.1 q.2)
        else 0)


-- @@ L2792-2818 verbatim
private def exactReverseBobAlignedCfcPrefixPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (k : ℕ) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    exactPriorQuestionWeight G n q *
      (∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
       ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if ∀ j : {j : Fin n // j ∈ D},
          G.predicate (q.1 j.val) (q.2 j.val)
            (aliceAnswer j) (bobAnswer j) = true then
          bornTracePairing S.state.matrix
            (exactJointPrefixAliceOperatorFilter G n S D
              (exactReverseBobFixedXMask D side context)
              (exactReverseBobPrefixYMask
                D side context k)
              aliceAnswer q.1 q.2)
            (cfc (fun z : ℝ => z * Real.log z)
              (exactJointPrefixBobOperatorFilter G n S D
                (exactReverseBobFixedXMask D side context)
                (exactReverseBobPrefixYMask
                  D side context k)
                bobAnswer q.1 q.2))
        else 0)


-- @@ L2820-2837 verbatim
private theorem exactReverseAliceAlignedCfcPrefixPotential_telescope
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side) :
    (∑ k ∈ Finset.range side.card,
      (exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context (k + 1) -
        exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context k)) =
      exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context side.card -
        exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context 0 :=
  history_forward_telescope
    (exactReverseAliceAlignedCfcPrefixPotential
      G n S D side context) side.card


-- @@ L2839-2856 verbatim
private theorem exactReverseBobAlignedCfcPrefixPotential_telescope
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side) :
    (∑ k ∈ Finset.range side.card,
      (exactReverseBobAlignedCfcPrefixPotential
          G n S D side context (k + 1) -
        exactReverseBobAlignedCfcPrefixPotential
          G n S D side context k)) =
      exactReverseBobAlignedCfcPrefixPotential
          G n S D side context side.card -
        exactReverseBobAlignedCfcPrefixPotential
          G n S D side context 0 :=
  history_forward_telescope
    (exactReverseBobAlignedCfcPrefixPotential
      G n S D side context) side.card


-- @@ L2858-2858 verbatim
end


-- @@ L2860-2860 verbatim
section


-- @@ L2862-2863 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L2866-2866 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L2868-2868 verbatim
variable {X Y A B : Type*}

-- @@ L2869-2869 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L2871-2881 verbatim
theorem exactPriorQuestion_coordinate_weight_ne_zero
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n)
    (supported : exactPriorQuestionWeight G n q ≠ 0)
    (j : Fin n) :
    G.questionWeight (q.1 j) (q.2 j) ≠ 0 := by
  intro zero
  apply supported
  unfold exactPriorQuestionWeight
  rw [Game.repeat_questionWeight]
  exact Finset.prod_eq_zero (Finset.mem_univ j) zero


-- @@ L2883-2931 verbatim
private theorem exactJointPrefixQuestionMass_pos_of_question
    (G : Game X Y A B) (n : ℕ)
    (fixedX fixedY : Finset (Fin n))
    (knownX : Fin n → X) (knownY : Fin n → Y)
    (positive : 0 < (G.repeat n).questionWeight knownX knownY) :
    0 < exactJointPrefixQuestionMass
      G n fixedX fixedY knownX knownY := by
  classical
  unfold exactJointPrefixQuestionMass
  have term_nonnegative (xs : Fin n → X) (ys : Fin n → Y) :
      0 ≤ if (∀ j : Fin n, j ∈ fixedX → xs j = knownX j) ∧
          (∀ j : Fin n, j ∈ fixedY → ys j = knownY j) then
        (G.repeat n).questionWeight xs ys
      else 0 := by
    split
    · exact (G.repeat n).weight_nonneg xs ys
    · exact le_rfl
  have row_nonnegative (xs : Fin n → X) :
      0 ≤ ∑ ys : Fin n → Y,
        if (∀ j : Fin n, j ∈ fixedX → xs j = knownX j) ∧
           (∀ j : Fin n, j ∈ fixedY → ys j = knownY j) then
          (G.repeat n).questionWeight xs ys
        else 0 :=
    Finset.sum_nonneg (fun ys _ => term_nonnegative xs ys)
  have own_compatible :
      (∀ j : Fin n, j ∈ fixedX → knownX j = knownX j) ∧
      (∀ j : Fin n, j ∈ fixedY → knownY j = knownY j) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  calc
    0 < (G.repeat n).questionWeight knownX knownY := positive
    _ = (if (∀ j : Fin n,
              j ∈ fixedX → knownX j = knownX j) ∧
            (∀ j : Fin n,
              j ∈ fixedY → knownY j = knownY j) then
          (G.repeat n).questionWeight knownX knownY
        else 0) := (ite_eq_left own_compatible).symm
    _ ≤ (∑ ys : Fin n → Y,
        if (∀ j : Fin n,
              j ∈ fixedX → knownX j = knownX j) ∧
            (∀ j : Fin n,
              j ∈ fixedY → ys j = knownY j) then
          (G.repeat n).questionWeight knownX ys
        else 0) :=
      Finset.single_le_sum
        (fun ys _ => term_nonnegative knownX ys)
        (Finset.mem_univ knownY)
    _ ≤ _ := Finset.single_le_sum
      (fun xs _ => row_nonnegative xs)
      (Finset.mem_univ knownX)


-- @@ L2933-2950 verbatim
theorem exactRevealCode_update_distinguished_alice
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) (x : X) :
    exactRevealCode D seed
        (Function.update q.1 seed.coordinate.val x, q.2) =
      exactRevealCode D seed q := by
  apply (exactRevealCode_eq_iff_fair_question_masks
    D seed q (Function.update q.1 seed.coordinate.val x, q.2)).mpr
  constructor
  · intro j hj
    have different : j ≠ seed.coordinate.val := by
      intro same
      exact exactFairAliceQuestionMask_coordinate_not_mem
        D seed (same ▸ hj)
    exact Function.update_of_ne different x q.1
  · intro j _
    rfl


-- @@ L2952-2969 verbatim
theorem exactRevealCode_update_distinguished_bob
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) (y : Y) :
    exactRevealCode D seed
        (q.1, Function.update q.2 seed.coordinate.val y) =
      exactRevealCode D seed q := by
  apply (exactRevealCode_eq_iff_fair_question_masks
    D seed q (q.1, Function.update q.2 seed.coordinate.val y)).mpr
  constructor
  · intro j _
    rfl
  · intro j hj
    have different : j ≠ seed.coordinate.val := by
      intro same
      exact exactFairBobQuestionMask_coordinate_not_mem
        D seed (same ▸ hj)
    exact Function.update_of_ne different y q.2


-- @@ L2971-3063 verbatim
private theorem exactFairAliceMeanFilter_eq_jointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → A)
    (supported : exactPriorQuestionWeight G n q ≠ 0) :
    exactAliceMeanFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.2 seed.coordinate.val) =
      exactJointPrefixAliceOperatorFilter G n S D
        (exactFairAliceQuestionMask D seed)
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed))
        answer q.1 q.2 := by
  classical
  have question_nonzero :
      (G.repeat n).questionWeight q.1 q.2 ≠ 0 := by
    simpa only [Game.repeat_questionWeight, ne_eq, exactPriorQuestionWeight] using supported
  have question_positive :
      0 < (G.repeat n).questionWeight q.1 q.2 :=
    lt_of_le_of_ne ((G.repeat n).weight_nonneg q.1 q.2)
      (Ne.symm question_nonzero)
  have register_positive := exactJointPrefixQuestionMass_pos_of_question
    G n (exactFairAliceQuestionMask D seed)
    (insert seed.coordinate.val
      (exactFairBobQuestionMask D seed))
    q.1 q.2 question_positive
  have tower := exactJointPrefixAliceOperatorFilter_martingale
    G n S D
    (exactFairAliceQuestionMask D seed)
    (insert seed.coordinate.val
      (exactFairBobQuestionMask D seed))
    seed.coordinate.val
    (exactFairAliceQuestionMask_coordinate_not_mem D seed)
    (Finset.mem_insert_self _ _)
    answer q.1 q.2 register_positive.ne'
  unfold exactAliceMeanFilter
  rw [← tower]
  apply Finset.sum_congr rfl
  intro x _
  by_cases missing : G.conditionalXGivenY (q.2 seed.coordinate.val) x = 0
  · simp only [missing, zero_smul]
  · have edge : G.questionWeight x (q.2 seed.coordinate.val) ≠ 0 := by
      intro zero
      apply missing
      simp only [Game.conditionalXGivenY, zero, zero_div]
    have mirror_edge :
        G.conditionalYGivenX x (q.2 seed.coordinate.val) ≠ 0 := by
      intro zero
      have factor := G.marginalX_mul_conditionalYGivenX
        x (q.2 seed.coordinate.val)
      rw [zero, mul_zero] at factor
      exact edge factor.symm
    have source :=
      exactAliceQuestionFilter_eq_jointPrefixOperatorFilter
        G n S D seed
        (Function.update q.1 seed.coordinate.val x, q.2) answer
    have source_filter :
        exactAliceQuestionFilter G n S D seed
          (exactRevealCode D seed q) answer x =
        exactJointPrefixAliceOperatorFilter G n S D
          (insert seed.coordinate.val
            (exactFairAliceQuestionMask D seed))
          (exactFairBobQuestionMask D seed) answer
          (Function.update q.1 seed.coordinate.val x) q.2 := by
      simpa only [
        exactRevealCode_update_distinguished_alice,
        Function.update_self] using source
    have stable :=
      exactJointPrefixAliceOperatorFilter_insert_bob
        G n S D
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (exactFairBobQuestionMask D seed)
        seed.coordinate.val
        (Finset.mem_insert_self _ _)
        (exactFairBobQuestionMask_coordinate_not_mem D seed)
        answer (Function.update q.1 seed.coordinate.val x) q.2
        (q.2 seed.coordinate.val)
        (by simpa only [Function.update_self] using mirror_edge)
    have equal :
        exactAliceQuestionFilter G n S D seed
          (exactRevealCode D seed q) answer x =
        exactJointPrefixAliceOperatorFilter G n S D
          (insert seed.coordinate.val
            (exactFairAliceQuestionMask D seed))
          (insert seed.coordinate.val
            (exactFairBobQuestionMask D seed))
          answer (Function.update q.1 seed.coordinate.val x) q.2 := by
      rw [source_filter]
      simpa only [Function.update_eq_self] using stable.symm
    rw [equal]


-- @@ L3065-3158 verbatim
private theorem exactFairBobMeanFilter_eq_jointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → B)
    (supported : exactPriorQuestionWeight G n q ≠ 0) :
    exactBobMeanFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.1 seed.coordinate.val) =
      exactJointPrefixBobOperatorFilter G n S D
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (exactFairBobQuestionMask D seed)
        answer q.1 q.2 := by
  classical
  have question_nonzero :
      (G.repeat n).questionWeight q.1 q.2 ≠ 0 := by
    simpa only [Game.repeat_questionWeight, ne_eq, exactPriorQuestionWeight] using supported
  have question_positive :
      0 < (G.repeat n).questionWeight q.1 q.2 :=
    lt_of_le_of_ne ((G.repeat n).weight_nonneg q.1 q.2)
      (Ne.symm question_nonzero)
  have register_positive := exactJointPrefixQuestionMass_pos_of_question
    G n
    (insert seed.coordinate.val
      (exactFairAliceQuestionMask D seed))
    (exactFairBobQuestionMask D seed)
    q.1 q.2 question_positive
  have tower := exactJointPrefixBobOperatorFilter_martingale
    G n S D
    (insert seed.coordinate.val
      (exactFairAliceQuestionMask D seed))
    (exactFairBobQuestionMask D seed)
    seed.coordinate.val
    (Finset.mem_insert_self _ _)
    (exactFairBobQuestionMask_coordinate_not_mem D seed)
    answer q.1 q.2 register_positive.ne'
  unfold exactBobMeanFilter
  rw [← tower]
  apply Finset.sum_congr rfl
  intro y _
  by_cases missing : G.conditionalYGivenX (q.1 seed.coordinate.val) y = 0
  · simp only [missing, zero_smul]
  · have edge : G.questionWeight (q.1 seed.coordinate.val) y ≠ 0 := by
      intro zero
      apply missing
      simp only [Game.conditionalYGivenX, zero, zero_div]
    have mirror_edge :
        G.conditionalXGivenY y (q.1 seed.coordinate.val) ≠ 0 := by
      intro zero
      have factor := G.marginalY_mul_conditionalXGivenY
        (q.1 seed.coordinate.val) y
      rw [zero, mul_zero] at factor
      exact edge factor.symm
    have source :=
      exactBobQuestionFilter_eq_jointPrefixOperatorFilter
        G n S D seed
        (q.1, Function.update q.2 seed.coordinate.val y) answer
    have source_filter :
        exactBobQuestionFilter G n S D seed
          (exactRevealCode D seed q) answer y =
        exactJointPrefixBobOperatorFilter G n S D
          (exactFairAliceQuestionMask D seed)
          (insert seed.coordinate.val
            (exactFairBobQuestionMask D seed)) answer
          q.1 (Function.update q.2 seed.coordinate.val y) := by
      simpa only [
        exactRevealCode_update_distinguished_bob,
        Function.update_self] using source
    have stable :=
      exactJointPrefixBobOperatorFilter_insert_alice
        G n S D
        (exactFairAliceQuestionMask D seed)
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed))
        seed.coordinate.val
        (exactFairAliceQuestionMask_coordinate_not_mem D seed)
        (Finset.mem_insert_self _ _)
        answer q.1 (Function.update q.2 seed.coordinate.val y)
        (q.1 seed.coordinate.val)
        (by simpa only [Function.update_self] using mirror_edge)
    have equal :
        exactBobQuestionFilter G n S D seed
          (exactRevealCode D seed q) answer y =
        exactJointPrefixBobOperatorFilter G n S D
          (insert seed.coordinate.val
            (exactFairAliceQuestionMask D seed))
          (insert seed.coordinate.val
            (exactFairBobQuestionMask D seed))
          answer q.1 (Function.update q.2 seed.coordinate.val y) := by
      rw [source_filter]
      simpa only [Function.update_eq_self] using stable.symm
    rw [equal]


-- @@ L3160-3160 verbatim
end


-- @@ L3162-3162 verbatim
section


-- @@ L3164-3165 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L3168-3168 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L3170-3170 verbatim
variable {X Y A B : Type*}

-- @@ L3171-3171 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L3173-3202 verbatim
theorem exactReverseBobMarker_induction
    {n : ℕ} (D : Finset (Fin n))
    (P : (side : Finset (SourceRemainingCoordinate D)) →
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side → Fin side.card → Prop)
    (allSeeds : ∀ seed : ExactRemainingSeed D,
      P (exactReverseRightSide seed)
        (exactReverseBobContext seed)
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩)) :
    ∀ (side : Finset (SourceRemainingCoordinate D))
      (context : ExactReverseSideContext
        (SourceRemainingCoordinate D) side)
      (marker : Fin side.card), P side context marker := by
  intro side context marker
  let seed := exactReverseBobMarkerDecode side context marker
  let motive :
      (Σ side : Finset (SourceRemainingCoordinate D),
        ExactReverseSideContext
          (SourceRemainingCoordinate D) side × Fin side.card) → Prop :=
    fun code => P code.1 code.2.1 code.2.2
  have actual : motive (exactReverseBobMarkerCode seed) :=
    allSeeds seed
  have inverse : exactReverseBobMarkerCode seed =
      ⟨side, context, marker⟩ := by
    exact exactReverseBobMarkerDecode_rightInverse
      side context marker
  rw [inverse] at actual
  exact actual


-- @@ L3204-3233 verbatim
theorem exactReverseAliceMarker_induction
    {n : ℕ} (D : Finset (Fin n))
    (P : (side : Finset (SourceRemainingCoordinate D)) →
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side → Fin side.card → Prop)
    (allSeeds : ∀ seed : ExactRemainingSeed D,
      P (exactReverseLeftSide seed)
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩)) :
    ∀ (side : Finset (SourceRemainingCoordinate D))
      (context : ExactReverseSideContext
        (SourceRemainingCoordinate D) side)
      (marker : Fin side.card), P side context marker := by
  intro side context marker
  let seed := exactReverseAliceMarkerDecode side context marker
  let motive :
      (Σ side : Finset (SourceRemainingCoordinate D),
        ExactReverseSideContext
          (SourceRemainingCoordinate D) side × Fin side.card) → Prop :=
    fun code => P code.1 code.2.1 code.2.2
  have actual : motive (exactReverseAliceMarkerCode seed) :=
    allSeeds seed
  have inverse : exactReverseAliceMarkerCode seed =
      ⟨side, context, marker⟩ := by
    exact exactReverseAliceMarkerDecode_rightInverse
      side context marker
  rw [inverse] at actual
  exact actual


-- @@ L3235-3251 verbatim
private theorem exactReverseAlicePrefixXMask_succ
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAlicePrefixXMask D side context
        (marker.val + 1) =
      insert (context.sideRank.symm marker).val.val
        (exactReverseAlicePrefixXMask D side context
          marker.val) := by
  classical
  unfold exactReverseAlicePrefixXMask
  rw [exactReverseContextQuestionPrefix_succ]
  ext j
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto


-- @@ L3253-3269 verbatim
private theorem exactReverseBobPrefixYMask_succ
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobPrefixYMask D side context
        (marker.val + 1) =
      insert (context.sideRank.symm marker).val.val
        (exactReverseBobPrefixYMask D side context
          marker.val) := by
  classical
  unfold exactReverseBobPrefixYMask
  rw [exactReverseContextQuestionPrefix_succ]
  ext j
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto


-- @@ L3271-3332 verbatim
private theorem exactReverseAliceLowQuestionPotential_eq_alignedPrefix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceLowQuestionPotential
        G n S D side context marker =
      exactReverseAliceAlignedCfcPrefixPotential
        G n S D side context marker.val := by
  classical
  apply exactReverseBobMarker_induction D
    (fun side context marker =>
      exactReverseAliceLowQuestionPotential
          G n S D side context marker =
        exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context marker.val)
  intro seed
  have decoded :=
    (exactReverseBobWeightedMarkerEquiv
      (M := SourceRemainingCoordinate D)).left_inv seed
  change
    exactReverseBobMarkerDecode
        (exactReverseRightSide seed)
        (exactReverseBobContext seed)
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩) = seed
    at decoded
  unfold exactReverseAliceLowQuestionPotential
    exactReverseAliceAlignedCfcPrefixPotential
  dsimp only
  rw [decoded,
    exactReverseAlicePrefixXMask_eq_fair,
    exactReverseAliceFixedYMask_eq_insert_fair]
  apply Finset.sum_congr rfl
  intro q _
  by_cases supported : exactPriorQuestionWeight G n q = 0
  · simp only [supported, zero_mul, Subtype.forall]
  · refine congrArg (_ * ·) ?_
    apply Finset.sum_congr rfl
    intro aliceAnswer _
    apply Finset.sum_congr rfl
    intro bobAnswer _
    by_cases accepted : ∀ j : {j : Fin n // j ∈ D},
      G.predicate (q.1 j.val) (q.2 j.val)
        (aliceAnswer j) (bobAnswer j) = true
    · have sourceAccepted : exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ := by
        exact accepted
      simp only [ite_eq_left sourceAccepted, ite_eq_left accepted]
      rw [exactFairAliceMeanFilter_eq_jointPrefixOperatorFilter
          G n S D seed q aliceAnswer supported,
        exactBobQuestionFilter_eq_jointPrefixOperatorFilter
          G n S D seed q bobAnswer]
    · have sourceRejected : ¬ exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ := by
        exact accepted
      simp only [ite_eq_right sourceRejected, ite_eq_right accepted]


-- @@ L3334-3395 verbatim
private theorem exactReverseBobLowQuestionPotential_eq_alignedPrefix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobLowQuestionPotential
        G n S D side context marker =
      exactReverseBobAlignedCfcPrefixPotential
        G n S D side context marker.val := by
  classical
  apply exactReverseAliceMarker_induction D
    (fun side context marker =>
      exactReverseBobLowQuestionPotential
          G n S D side context marker =
        exactReverseBobAlignedCfcPrefixPotential
          G n S D side context marker.val)
  intro seed
  have decoded :=
    (exactReverseAliceWeightedMarkerEquiv
      (M := SourceRemainingCoordinate D)).left_inv seed
  change
    exactReverseAliceMarkerDecode
        (exactReverseLeftSide seed)
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) = seed
    at decoded
  unfold exactReverseBobLowQuestionPotential
    exactReverseBobAlignedCfcPrefixPotential
  dsimp only
  rw [decoded,
    exactReverseBobFixedXMask_eq_insert_fair,
    exactReverseBobPrefixYMask_eq_fair]
  apply Finset.sum_congr rfl
  intro q _
  by_cases supported : exactPriorQuestionWeight G n q = 0
  · simp only [supported, zero_mul, Subtype.forall]
  · refine congrArg (_ * ·) ?_
    apply Finset.sum_congr rfl
    intro aliceAnswer _
    apply Finset.sum_congr rfl
    intro bobAnswer _
    by_cases accepted : ∀ j : {j : Fin n // j ∈ D},
      G.predicate (q.1 j.val) (q.2 j.val)
        (aliceAnswer j) (bobAnswer j) = true
    · have sourceAccepted : exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ := by
        exact accepted
      simp only [ite_eq_left sourceAccepted, ite_eq_left accepted]
      rw [exactAliceQuestionFilter_eq_jointPrefixOperatorFilter
          G n S D seed q aliceAnswer,
        exactFairBobMeanFilter_eq_jointPrefixOperatorFilter
          G n S D seed q bobAnswer supported]
    · have sourceRejected : ¬ exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ := by
        exact accepted
      simp only [ite_eq_right sourceRejected, ite_eq_right accepted]


-- @@ L3397-3397 verbatim
end


-- @@ L3399-3399 verbatim
section


-- @@ L3401-3402 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L3405-3405 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L3407-3407 verbatim
variable {X Y A B : Type*}

-- @@ L3408-3408 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L3410-3449 verbatim
private theorem exactAliceQuestionFilter_eq_fullJointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → A)
    (supported : exactPriorQuestionWeight G n q ≠ 0) :
    exactAliceQuestionFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.1 seed.coordinate.val) =
      exactJointPrefixAliceOperatorFilter G n S D
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed))
        answer q.1 q.2 := by
  classical
  have edge := exactPriorQuestion_coordinate_weight_ne_zero
    G n q supported seed.coordinate.val
  have conditional :
      G.conditionalYGivenX
        (q.1 seed.coordinate.val) (q.2 seed.coordinate.val) ≠ 0 := by
    intro zero
    have factor := G.marginalX_mul_conditionalYGivenX
      (q.1 seed.coordinate.val) (q.2 seed.coordinate.val)
    rw [zero, mul_zero] at factor
    exact edge factor.symm
  rw [exactAliceQuestionFilter_eq_jointPrefixOperatorFilter
    G n S D seed q answer]
  have stable :=
    exactJointPrefixAliceOperatorFilter_insert_bob
      G n S D
      (insert seed.coordinate.val
        (exactFairAliceQuestionMask D seed))
      (exactFairBobQuestionMask D seed)
      seed.coordinate.val
      (Finset.mem_insert_self _ _)
      (exactFairBobQuestionMask_coordinate_not_mem D seed)
      answer q.1 q.2 (q.2 seed.coordinate.val) conditional
  simpa only [Function.update_eq_self] using stable.symm


-- @@ L3451-3490 verbatim
private theorem exactBobQuestionFilter_eq_fullJointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → B)
    (supported : exactPriorQuestionWeight G n q ≠ 0) :
    exactBobQuestionFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.2 seed.coordinate.val) =
      exactJointPrefixBobOperatorFilter G n S D
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed))
        answer q.1 q.2 := by
  classical
  have edge := exactPriorQuestion_coordinate_weight_ne_zero
    G n q supported seed.coordinate.val
  have conditional :
      G.conditionalXGivenY
        (q.2 seed.coordinate.val) (q.1 seed.coordinate.val) ≠ 0 := by
    intro zero
    have factor := G.marginalY_mul_conditionalXGivenY
      (q.1 seed.coordinate.val) (q.2 seed.coordinate.val)
    rw [zero, mul_zero] at factor
    exact edge factor.symm
  rw [exactBobQuestionFilter_eq_jointPrefixOperatorFilter
    G n S D seed q answer]
  have stable :=
    exactJointPrefixBobOperatorFilter_insert_alice
      G n S D
      (exactFairAliceQuestionMask D seed)
      (insert seed.coordinate.val
        (exactFairBobQuestionMask D seed))
      seed.coordinate.val
      (exactFairAliceQuestionMask_coordinate_not_mem D seed)
      (Finset.mem_insert_self _ _)
      answer q.1 q.2 (q.1 seed.coordinate.val) conditional
  simpa only [Function.update_eq_self] using stable.symm


-- @@ L3492-3554 verbatim
private theorem exactReverseAliceHighQuestionPotential_eq_alignedPrefix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceHighQuestionPotential
        G n S D side context marker =
      exactReverseAliceAlignedCfcPrefixPotential
        G n S D side context (marker.val + 1) := by
  classical
  apply exactReverseBobMarker_induction D
    (fun side context marker =>
      exactReverseAliceHighQuestionPotential
          G n S D side context marker =
        exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context (marker.val + 1))
  intro seed
  have decoded :=
    (exactReverseBobWeightedMarkerEquiv
      (M := SourceRemainingCoordinate D)).left_inv seed
  change
    exactReverseBobMarkerDecode
        (exactReverseRightSide seed)
        (exactReverseBobContext seed)
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩) = seed
    at decoded
  unfold exactReverseAliceHighQuestionPotential
    exactReverseAliceAlignedCfcPrefixPotential
  dsimp only
  rw [decoded, exactReverseAlicePrefixXMask_succ,
    Equiv.symm_apply_apply,
    exactReverseAlicePrefixXMask_eq_fair,
    exactReverseAliceFixedYMask_eq_insert_fair]
  apply Finset.sum_congr rfl
  intro q _
  by_cases supported : exactPriorQuestionWeight G n q = 0
  · simp only [supported, zero_mul, Subtype.forall]
  · refine congrArg (_ * ·) ?_
    apply Finset.sum_congr rfl
    intro aliceAnswer _
    apply Finset.sum_congr rfl
    intro bobAnswer _
    by_cases accepted : ∀ j : {j : Fin n // j ∈ D},
      G.predicate (q.1 j.val) (q.2 j.val)
        (aliceAnswer j) (bobAnswer j) = true
    · have sourceAccepted : exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ := by
        exact accepted
      simp only [ite_eq_left sourceAccepted, ite_eq_left accepted]
      rw [exactAliceQuestionFilter_eq_fullJointPrefixOperatorFilter
          G n S D seed q aliceAnswer supported,
        exactBobQuestionFilter_eq_fullJointPrefixOperatorFilter
          G n S D seed q bobAnswer supported]
    · have sourceRejected : ¬ exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ := by
        exact accepted
      simp only [ite_eq_right sourceRejected, ite_eq_right accepted]


-- @@ L3556-3618 verbatim
private theorem exactReverseBobHighQuestionPotential_eq_alignedPrefix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobHighQuestionPotential
        G n S D side context marker =
      exactReverseBobAlignedCfcPrefixPotential
        G n S D side context (marker.val + 1) := by
  classical
  apply exactReverseAliceMarker_induction D
    (fun side context marker =>
      exactReverseBobHighQuestionPotential
          G n S D side context marker =
        exactReverseBobAlignedCfcPrefixPotential
          G n S D side context (marker.val + 1))
  intro seed
  have decoded :=
    (exactReverseAliceWeightedMarkerEquiv
      (M := SourceRemainingCoordinate D)).left_inv seed
  change
    exactReverseAliceMarkerDecode
        (exactReverseLeftSide seed)
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) = seed
    at decoded
  unfold exactReverseBobHighQuestionPotential
    exactReverseBobAlignedCfcPrefixPotential
  dsimp only
  rw [decoded, exactReverseBobPrefixYMask_succ,
    Equiv.symm_apply_apply,
    exactReverseBobFixedXMask_eq_insert_fair,
    exactReverseBobPrefixYMask_eq_fair]
  apply Finset.sum_congr rfl
  intro q _
  by_cases supported : exactPriorQuestionWeight G n q = 0
  · simp only [supported, zero_mul, Subtype.forall]
  · refine congrArg (_ * ·) ?_
    apply Finset.sum_congr rfl
    intro aliceAnswer _
    apply Finset.sum_congr rfl
    intro bobAnswer _
    by_cases accepted : ∀ j : {j : Fin n // j ∈ D},
      G.predicate (q.1 j.val) (q.2 j.val)
        (aliceAnswer j) (bobAnswer j) = true
    · have sourceAccepted : exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ := by
        exact accepted
      simp only [ite_eq_left sourceAccepted, ite_eq_left accepted]
      rw [exactAliceQuestionFilter_eq_fullJointPrefixOperatorFilter
          G n S D seed q aliceAnswer supported,
        exactBobQuestionFilter_eq_fullJointPrefixOperatorFilter
          G n S D seed q bobAnswer supported]
    · have sourceRejected : ¬ exactHistoryAccepted G n D
          ⟨seed, exactRevealCode D seed q,
            aliceAnswer, bobAnswer⟩ := by
        exact accepted
      simp only [ite_eq_right sourceRejected, ite_eq_right accepted]


-- @@ L3620-3635 verbatim
private theorem exactReverseAliceFilterOperatorMarkerEntropy_eq_aligned_step
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceFilterOperatorMarkerEntropy
        G n S D side context marker =
      exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context (marker.val + 1) -
        exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context marker.val := by
  rw [exactReverseAliceFilterOperatorMarkerEntropy_eq_question_sub,
    exactReverseAliceHighQuestionPotential_eq_alignedPrefix,
    exactReverseAliceLowQuestionPotential_eq_alignedPrefix]


-- @@ L3637-3652 verbatim
private theorem exactReverseBobFilterOperatorMarkerEntropy_eq_aligned_step
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobFilterOperatorMarkerEntropy
        G n S D side context marker =
      exactReverseBobAlignedCfcPrefixPotential
          G n S D side context (marker.val + 1) -
        exactReverseBobAlignedCfcPrefixPotential
          G n S D side context marker.val := by
  rw [exactReverseBobFilterOperatorMarkerEntropy_eq_question_sub,
    exactReverseBobHighQuestionPotential_eq_alignedPrefix,
    exactReverseBobLowQuestionPotential_eq_alignedPrefix]


-- @@ L3654-3691 verbatim
private theorem exactReverseAliceFilterOperatorMarkerEntropy_sum_telescope
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side) :
    (∑ marker : Fin side.card,
      exactReverseAliceFilterOperatorMarkerEntropy
        G n S D side context marker) =
      exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context side.card -
        exactReverseAliceAlignedCfcPrefixPotential
          G n S D side context 0 := by
  classical
  calc
    (∑ marker : Fin side.card,
      exactReverseAliceFilterOperatorMarkerEntropy
        G n S D side context marker) =
      ∑ marker : Fin side.card,
        (exactReverseAliceAlignedCfcPrefixPotential
            G n S D side context (marker.val + 1) -
          exactReverseAliceAlignedCfcPrefixPotential
            G n S D side context marker.val) := by
          apply Finset.sum_congr rfl
          intro marker _
          exact exactReverseAliceFilterOperatorMarkerEntropy_eq_aligned_step
            G n S D side context marker
    _ = ∑ k ∈ Finset.range side.card,
        (exactReverseAliceAlignedCfcPrefixPotential
            G n S D side context (k + 1) -
          exactReverseAliceAlignedCfcPrefixPotential
            G n S D side context k) := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_range.mp hk, ↓reduceDIte]
    _ = _ := exactReverseAliceAlignedCfcPrefixPotential_telescope
      G n S D side context


-- @@ L3693-3730 verbatim
private theorem exactReverseBobFilterOperatorMarkerEntropy_sum_telescope
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side) :
    (∑ marker : Fin side.card,
      exactReverseBobFilterOperatorMarkerEntropy
        G n S D side context marker) =
      exactReverseBobAlignedCfcPrefixPotential
          G n S D side context side.card -
        exactReverseBobAlignedCfcPrefixPotential
          G n S D side context 0 := by
  classical
  calc
    (∑ marker : Fin side.card,
      exactReverseBobFilterOperatorMarkerEntropy
        G n S D side context marker) =
      ∑ marker : Fin side.card,
        (exactReverseBobAlignedCfcPrefixPotential
            G n S D side context (marker.val + 1) -
          exactReverseBobAlignedCfcPrefixPotential
            G n S D side context marker.val) := by
          apply Finset.sum_congr rfl
          intro marker _
          exact exactReverseBobFilterOperatorMarkerEntropy_eq_aligned_step
            G n S D side context marker
    _ = ∑ k ∈ Finset.range side.card,
        (exactReverseBobAlignedCfcPrefixPotential
            G n S D side context (k + 1) -
          exactReverseBobAlignedCfcPrefixPotential
            G n S D side context k) := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_range.mp hk, ↓reduceDIte]
    _ = _ := exactReverseBobAlignedCfcPrefixPotential_telescope
      G n S D side context


-- @@ L3732-3732 verbatim
end


-- @@ L3734-3734 verbatim
section


-- @@ L3736-3737 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L3740-3740 verbatim
open QuantumParallelRepetition.ClassicalInformation


-- @@ L3742-3742 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L3744-3744 verbatim
variable {X Y A B : Type*}

-- @@ L3745-3745 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L3747-3754 verbatim
private abbrev ExactFixedSeedOutcomeTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :=
  ExactRevealHistory X Y D seed ×
    ({j : Fin n // j ∈ D} → A) ×
    ({j : Fin n // j ∈ D} → B) × X × Y


-- @@ L3756-3765 verbatim
private def exactFixedSeedOutcomeCode
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    ExactFixedSeedOutcomeTuple X Y A B D seed :=
  (exactRevealCode D seed (outcome.1, outcome.2.1),
    (fun j => outcome.2.2.1 j.val),
    (fun j => outcome.2.2.2 j.val),
    outcome.1 seed.coordinate.val,
    outcome.2.1 seed.coordinate.val)


-- @@ L3767-3813 verbatim
private theorem exactFixedSeedOutcomeCode_fiber_iff
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y)
    (outcome : ExactOutcome X Y A B n) :
    exactFixedSeedOutcomeCode D seed outcome =
        (history, aliceAnswer, bobAnswer, x, y) ↔
      exactLocallySampleableCode D (seed, outcome) =
        (seed.coordinate, x, y,
          (⟨seed, history, aliceAnswer, bobAnswer⟩ :
            ExactHistoryFlag X Y A B D)) := by
  rw [exactLocallySampleableCode_fixedSeed_fiber_iff
    D (⟨seed, history, aliceAnswer, bobAnswer⟩ :
      ExactHistoryFlag X Y A B D) x y outcome]
  constructor
  · intro same
    have hh := congrArg
      (fun t : ExactFixedSeedOutcomeTuple X Y A B D seed => t.1)
      same
    have ha := congrArg
      (fun t : ExactFixedSeedOutcomeTuple X Y A B D seed =>
        t.2.1) same
    have hb := congrArg
      (fun t : ExactFixedSeedOutcomeTuple X Y A B D seed =>
        t.2.2.1) same
    have hx := congrArg
      (fun t : ExactFixedSeedOutcomeTuple X Y A B D seed =>
        t.2.2.2.1) same
    have hy := congrArg
      (fun t : ExactFixedSeedOutcomeTuple X Y A B D seed =>
        t.2.2.2.2) same
    refine ⟨hh, hx, hy, ?_, ?_⟩
    · intro j
      exact congrFun ha j
    · intro j
      exact congrFun hb j
  · rintro ⟨hh, hx, hy, ha, hb⟩
    apply Prod.ext
    · exact hh
    · apply Prod.ext
      · exact funext ha
      · apply Prod.ext
        · exact funext hb
        · exact Prod.ext hx hy


-- @@ L3815-3846 verbatim
private theorem exactFixedSeedGroupedBornMass_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) :
    groupedMass
        (exactFixedSeedOutcomeCode
          (X := X) (Y := Y) (A := A) (B := B) D seed)
        (strategyEventLaw (G.repeat n) S).weight
        (history, aliceAnswer, bobAnswer, x, y) =
      exactFairFullOutcomeBornMass G n S D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ x y := by
  classical
  unfold groupedMass exactFairFullOutcomeBornMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases compatible :
      exactFixedSeedOutcomeCode D seed outcome =
        (history, aliceAnswer, bobAnswer, x, y)
  · rw [ite_eq_left compatible,
      ite_eq_left ((exactFixedSeedOutcomeCode_fiber_iff
        D seed history aliceAnswer bobAnswer x y outcome).mp compatible)]
  · rw [ite_eq_right compatible, ite_eq_right]
    intro incompatible
    exact compatible
      ((exactFixedSeedOutcomeCode_fiber_iff
        D seed history aliceAnswer bobAnswer x y outcome).mpr
        incompatible)


-- @@ L3848-3872 verbatim
private theorem exactFixedSeedOutcomeCode_accepted_iff
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    exactHistoryAccepted G n D
        ⟨seed,
          (exactFixedSeedOutcomeCode
            (X := X) (Y := Y) (A := A) (B := B) D seed outcome).1,
          (exactFixedSeedOutcomeCode
            (X := X) (Y := Y) (A := A) (B := B) D seed outcome).2.1,
          (exactFixedSeedOutcomeCode
            (X := X) (Y := Y) (A := A) (B := B) D seed outcome).2.2.1⟩ ↔
      outcome ∈ FiniteEventLaw.winEvent
        (repeatedCoordinateWin G n) D := by
  classical
  simp only [exactHistoryAccepted,
    exactFixedSeedOutcomeCode,
    exactRevealCode]
  rw [FiniteEventLaw.mem_winEvent_iff]
  constructor
  · intro accepted j member
    simpa only [repeatedCoordinateWin] using accepted ⟨j, member⟩
  · intro accepted j
    simpa only [repeatedCoordinateWin] using accepted j.val j.property


-- @@ L3874-3970 verbatim
theorem exactFairFullOutcomeBornMass_accepted_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          ∑ x : X, ∑ y : Y,
            exactFairFullOutcomeBornMass G n S D
              ⟨seed, history, aliceAnswer, bobAnswer⟩ x y
        else 0) = repeatedPostselectionMass G n S D := by
  classical
  let code := exactFixedSeedOutcomeCode
    (X := X) (Y := Y) (A := A) (B := B) D seed
  let payoff : ExactFixedSeedOutcomeTuple X Y A B D seed → ℝ :=
    fun t =>
      if exactHistoryAccepted G n D
        ⟨seed, t.1, t.2.1, t.2.2.1⟩ then 1 else 0
  have push := groupedMass_expectation
    code (strategyEventLaw (G.repeat n) S).weight payoff
  simp only [Fintype.sum_prod_type] at push
  calc
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          ∑ x : X, ∑ y : Y,
            exactFairFullOutcomeBornMass G n S D
              ⟨seed, history, aliceAnswer, bobAnswer⟩ x y
        else 0) =
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
      ∑ x : X, ∑ y : Y,
        groupedMass code (strategyEventLaw (G.repeat n) S).weight
          (history, aliceAnswer, bobAnswer, x, y) *
            payoff (history, aliceAnswer, bobAnswer, x, y) := by
        apply Finset.sum_congr rfl
        intro history _
        apply Finset.sum_congr rfl
        intro aliceAnswer _
        apply Finset.sum_congr rfl
        intro bobAnswer _
        by_cases accepted : exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
        · simp only [ite_eq_left accepted, payoff, mul_one]
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          exact (exactFixedSeedGroupedBornMass_eq
            G n S D seed history aliceAnswer bobAnswer x y).symm
        · simp only [accepted, ↓reduceIte, mul_zero, sum_const_zero, payoff]
    _ = ∑ outcome : ExactOutcome X Y A B n,
        (strategyEventLaw (G.repeat n) S).weight outcome *
          payoff (code outcome) := by
        simpa only [Fintype.sum_prod_type] using push
    _ = ∑ outcome : ExactOutcome X Y A B n,
        if outcome ∈ FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D then
          (strategyEventLaw (G.repeat n) S).weight outcome
        else 0 := by
        apply Finset.sum_congr rfl
        intro outcome _
        have acceptance := exactFixedSeedOutcomeCode_accepted_iff
          G n D seed outcome
        by_cases winning : outcome ∈ FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D
        · have accepted := acceptance.mpr winning
          simp only [accepted, ↓reduceIte, mul_one, winning, payoff, code]
        · have rejected : ¬ exactHistoryAccepted G n D
              ⟨seed,
                (exactFixedSeedOutcomeCode
                  (X := X) (Y := Y) (A := A) (B := B)
                  D seed outcome).1,
                (exactFixedSeedOutcomeCode
                  (X := X) (Y := Y) (A := A) (B := B)
                  D seed outcome).2.1,
                (exactFixedSeedOutcomeCode
                  (X := X) (Y := Y) (A := A) (B := B)
                  D seed outcome).2.2.1⟩ := by
            intro accepted
            exact winning (acceptance.mp accepted)
          simp only [rejected, ↓reduceIte, mul_zero, winning, payoff, code]
    _ = repeatedPostselectionMass G n S D := by
      change
        (∑ outcome : ExactOutcome X Y A B n,
          if outcome ∈ FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D then
            (strategyEventLaw (G.repeat n) S).weight outcome
          else 0) =
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      simp only [sum_ite_mem, univ_inter, FiniteEventLaw.eventMass]


-- @@ L3972-3972 verbatim
end


-- @@ L3974-3974 verbatim
section


-- @@ L3976-3977 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L3980-3980 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L3982-3982 verbatim
variable {X Y A B : Type*}

-- @@ L3983-3983 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L3985-4006 verbatim
private def exactReverseAliceAcceptedScalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        (∑ y : Y, G.marginalY y *
          Real.negMulLog
            (bornTracePairing S.state.matrix
              (exactAliceMeanFilter
                G n S D seed history aliceAnswer y)
              (exactBobQuestionFilter
                G n S D seed history bobAnswer y)))
    else 0


-- @@ L4008-4045 verbatim
private theorem exactReverseAliceLowOperatorPotential_neg_le_scalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    -exactReverseAliceFilterLowOperatorPotential
        G n S D side context marker ≤
      exactReverseAliceAcceptedScalarEntropy
        G n S D side context marker := by
  classical
  unfold exactReverseAliceFilterLowOperatorPotential
    exactReverseAliceAcceptedScalarEntropy
  dsimp only
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro history _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro aliceAnswer _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro bobAnswer _
  by_cases accepted : exactHistoryAccepted G n D
      ⟨exactReverseBobMarkerDecode side context marker,
        history, aliceAnswer, bobAnswer⟩
  · simp only [ite_eq_left accepted]
    have spectral := exactFairAliceHistoryLowOperatorPotential_neg_le_entropy
      G n S D
      ⟨exactReverseBobMarkerDecode side context marker,
        history, aliceAnswer, bobAnswer⟩
    have weighted := mul_le_mul_of_nonneg_left spectral
      (exactRevealMass_nonneg G n D
        (exactReverseBobMarkerDecode side context marker)
        history)
    linarith
  · simp only [accepted, ↓reduceIte, neg_zero, Std.le_refl]


-- @@ L4047-4066 verbatim
private theorem exactReverseAliceAlignedCfcPrefixPotential_last_nonpos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (nonempty : 0 < side.card) :
    exactReverseAliceAlignedCfcPrefixPotential
      G n S D side context side.card ≤ 0 := by
  classical
  let marker : Fin side.card := ⟨side.card - 1, Nat.sub_lt nonempty Nat.one_pos⟩
  have last : marker.val + 1 = side.card := by
    dsimp [marker]
    omega
  have high := exactReverseAliceFilterHighOperatorPotential_nonpos
    G n S D side context marker
  rw [exactReverseAliceHighOperatorPotential_eq_question,
    exactReverseAliceHighQuestionPotential_eq_alignedPrefix,
    last] at high
  exact high


-- @@ L4068-4089 verbatim
private theorem exactReverseAliceFilterOperatorMarkerEntropy_sum_le_scalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (nonempty : 0 < side.card) :
    (∑ marker : Fin side.card,
      exactReverseAliceFilterOperatorMarkerEntropy
        G n S D side context marker) ≤
      exactReverseAliceAcceptedScalarEntropy
        G n S D side context ⟨0, nonempty⟩ := by
  classical
  have last := exactReverseAliceAlignedCfcPrefixPotential_last_nonpos
    G n S D side context nonempty
  have low := exactReverseAliceLowOperatorPotential_neg_le_scalarEntropy
    G n S D side context ⟨0, nonempty⟩
  rw [exactReverseAliceFilterOperatorMarkerEntropy_sum_telescope]
  rw [exactReverseAliceLowOperatorPotential_eq_question,
    exactReverseAliceLowQuestionPotential_eq_alignedPrefix] at low
  dsimp only at low
  linarith


-- @@ L4091-4091 verbatim
end


-- @@ L4093-4093 verbatim
section


-- @@ L4095-4096 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L4099-4099 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L4101-4101 verbatim
variable {X Y A B : Type*}

-- @@ L4102-4102 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L4104-4125 verbatim
private def exactReverseBobAcceptedScalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        (∑ x : X, G.marginalX x *
          Real.negMulLog
            (bornTracePairing S.state.matrix
              (exactAliceQuestionFilter
                G n S D seed history aliceAnswer x)
              (exactBobMeanFilter
                G n S D seed history bobAnswer x)))
    else 0


-- @@ L4127-4161 verbatim
private theorem exactReverseBobFilterLowOperatorPotential_neg_le_scalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    -exactReverseBobFilterLowOperatorPotential
        G n S D side context marker ≤
      exactReverseBobAcceptedScalarEntropy
        G n S D side context marker := by
  classical
  unfold exactReverseBobFilterLowOperatorPotential
    exactReverseBobAcceptedScalarEntropy
  dsimp only
  simp_rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro history _
  apply Finset.sum_le_sum
  intro aliceAnswer _
  apply Finset.sum_le_sum
  intro bobAnswer _
  split
  · rename_i accepted
    have bound :=
      exactFairBobHistoryLowOperatorPotential_neg_le_entropy
        G n S D
        ⟨exactReverseAliceMarkerDecode side context marker,
          history, aliceAnswer, bobAnswer⟩
    have scaled := mul_le_mul_of_nonneg_left bound
      (exactRevealMass_nonneg G n D
        (exactReverseAliceMarkerDecode side context marker)
        history)
    simpa only [mul_neg] using scaled
  · simp only [neg_zero, Std.le_refl]


-- @@ L4163-4182 verbatim
private theorem exactReverseBobAlignedCfcPrefixPotential_terminal_nonpos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (sideNonempty : 0 < side.card) :
    exactReverseBobAlignedCfcPrefixPotential
      G n S D side context side.card ≤ 0 := by
  let marker : Fin side.card :=
    ⟨side.card - 1, Nat.sub_lt sideNonempty (by decide)⟩
  have step : marker.val + 1 = side.card := by
    dsimp [marker]
    omega
  have high := exactReverseBobFilterHighOperatorPotential_nonpos
    G n S D side context marker
  rw [exactReverseBobHighOperatorPotential_eq_question,
    exactReverseBobHighQuestionPotential_eq_alignedPrefix,
    step] at high
  exact high


-- @@ L4184-4219 verbatim
private theorem exactReverseBobFilterOperatorMarkerEntropy_sum_le_scalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (sideNonempty : 0 < side.card) :
    (∑ marker : Fin side.card,
      exactReverseBobFilterOperatorMarkerEntropy
        G n S D side context marker) ≤
      exactReverseBobAcceptedScalarEntropy
        G n S D side context ⟨0, sideNonempty⟩ := by
  let initial : Fin side.card := ⟨0, sideNonempty⟩
  have terminal :=
    exactReverseBobAlignedCfcPrefixPotential_terminal_nonpos
      G n S D side context sideNonempty
  have scalar :=
    exactReverseBobFilterLowOperatorPotential_neg_le_scalarEntropy
      G n S D side context initial
  have initialPotential :
      exactReverseBobFilterLowOperatorPotential
          G n S D side context initial =
        exactReverseBobAlignedCfcPrefixPotential
          G n S D side context 0 := by
    rw [exactReverseBobLowOperatorPotential_eq_question,
      exactReverseBobLowQuestionPotential_eq_alignedPrefix]
  rw [exactReverseBobFilterOperatorMarkerEntropy_sum_telescope]
  rw [initialPotential] at scalar
  change
    exactReverseBobAlignedCfcPrefixPotential
        G n S D side context side.card -
      exactReverseBobAlignedCfcPrefixPotential
        G n S D side context 0 ≤
      exactReverseBobAcceptedScalarEntropy
        G n S D side context initial
  linarith


-- @@ L4221-4221 verbatim
end


-- @@ L4223-4223 verbatim
section


-- @@ L4225-4226 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L4229-4229 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L4231-4231 verbatim
variable {X Y A B : Type*}

-- @@ L4232-4232 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L4234-4248 verbatim
theorem exactFairFullOutcomeBornMass_eq_reveal_question_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairFullOutcomeBornMass G n S D r x y =
      exactRevealMass G n D r.seed r.history *
        G.questionWeight x y *
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
  rw [exactFairFullOutcomeBornMass_eq_reveal_question_norm,
    exactUnnormalizedPsi_norm_sq]


-- @@ L4250-4268 verbatim
theorem exactFairAliceMeanBorn_eq_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    bornTracePairing S.state.matrix
        (exactAliceMeanFilter
          G n S D r.seed r.history r.aliceAnswer y)
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y) =
      ∑ x : X, G.conditionalXGivenY y x *
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
  unfold exactAliceMeanFilter
  simp only [map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]


-- @@ L4270-4287 verbatim
theorem exactFairBobMeanBorn_eq_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    bornTracePairing S.state.matrix
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)
        (exactBobMeanFilter
          G n S D r.seed r.history r.bobAnswer x) =
      ∑ y : Y, G.conditionalYGivenX x y *
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
  unfold exactBobMeanFilter
  simp only [map_sum, map_smul, smul_eq_mul]


-- @@ L4289-4347 verbatim
theorem exactFairAliceMeanBornMass_eq_fullOutcome_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactRevealMass G n D r.seed r.history *
        (∑ y : Y, G.marginalY y *
          bornTracePairing S.state.matrix
            (exactAliceMeanFilter
              G n S D r.seed r.history r.aliceAnswer y)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y)) =
      ∑ x : X, ∑ y : Y,
        exactFairFullOutcomeBornMass G n S D r x y := by
  classical
  calc
    exactRevealMass G n D r.seed r.history *
        (∑ y : Y, G.marginalY y *
          bornTracePairing S.state.matrix
            (exactAliceMeanFilter
              G n S D r.seed r.history r.aliceAnswer y)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y)) =
      ∑ y : Y, ∑ x : X,
        exactRevealMass G n D r.seed r.history *
          (G.marginalY y * G.conditionalXGivenY y x) *
          bornTracePairing S.state.matrix
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [exactFairAliceMeanBorn_eq_conditional,
          Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = ∑ x : X, ∑ y : Y,
        exactRevealMass G n D r.seed r.history *
          G.questionWeight x y *
          bornTracePairing S.state.matrix
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [G.marginalY_mul_conditionalXGivenY]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        exact (exactFairFullOutcomeBornMass_eq_reveal_question_born
          G n S D r x y).symm


-- @@ L4349-4406 verbatim
theorem exactFairBobMeanBornMass_eq_fullOutcome_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactRevealMass G n D r.seed r.history *
        (∑ x : X, G.marginalX x *
          bornTracePairing S.state.matrix
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x)
            (exactBobMeanFilter
              G n S D r.seed r.history r.bobAnswer x)) =
      ∑ x : X, ∑ y : Y,
        exactFairFullOutcomeBornMass G n S D r x y := by
  classical
  calc
    exactRevealMass G n D r.seed r.history *
        (∑ x : X, G.marginalX x *
          bornTracePairing S.state.matrix
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x)
            (exactBobMeanFilter
              G n S D r.seed r.history r.bobAnswer x)) =
      ∑ x : X, ∑ y : Y,
        exactRevealMass G n D r.seed r.history *
          (G.marginalX x * G.conditionalYGivenX x y) *
          bornTracePairing S.state.matrix
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [exactFairBobMeanBorn_eq_conditional,
          Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
    _ = ∑ x : X, ∑ y : Y,
        exactRevealMass G n D r.seed r.history *
          G.questionWeight x y *
          bornTracePairing S.state.matrix
            (exactAliceQuestionFilter
              G n S D r.seed r.history r.aliceAnswer x)
            (exactBobQuestionFilter
              G n S D r.seed r.history r.bobAnswer y) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [G.marginalX_mul_conditionalYGivenX]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        exact (exactFairFullOutcomeBornMass_eq_reveal_question_born
          G n S D r x y).symm


-- @@ L4408-4447 verbatim
theorem exactFairAliceMeanAcceptedBornMass_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            (∑ y : Y, G.marginalY y *
              bornTracePairing S.state.matrix
                (exactAliceMeanFilter
                  G n S D seed history aliceAnswer y)
                (exactBobQuestionFilter
                  G n S D seed history bobAnswer y))
        else 0) = repeatedPostselectionMass G n S D := by
  classical
  calc
    _ = ∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          ∑ x : X, ∑ y : Y,
            exactFairFullOutcomeBornMass G n S D
              ⟨seed, history, aliceAnswer, bobAnswer⟩ x y
        else 0 := by
      apply Finset.sum_congr rfl
      intro history _
      apply Finset.sum_congr rfl
      intro aliceAnswer _
      apply Finset.sum_congr rfl
      intro bobAnswer _
      split
      · exact exactFairAliceMeanBornMass_eq_fullOutcome_sum
          G n S D ⟨seed, history, aliceAnswer, bobAnswer⟩
      · rfl
    _ = _ := exactFairFullOutcomeBornMass_accepted_sum
      G n S D seed


-- @@ L4449-4488 verbatim
theorem exactFairBobMeanAcceptedBornMass_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            (∑ x : X, G.marginalX x *
              bornTracePairing S.state.matrix
                (exactAliceQuestionFilter
                  G n S D seed history aliceAnswer x)
                (exactBobMeanFilter
                  G n S D seed history bobAnswer x))
        else 0) = repeatedPostselectionMass G n S D := by
  classical
  calc
    _ = ∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          ∑ x : X, ∑ y : Y,
            exactFairFullOutcomeBornMass G n S D
              ⟨seed, history, aliceAnswer, bobAnswer⟩ x y
        else 0 := by
      apply Finset.sum_congr rfl
      intro history _
      apply Finset.sum_congr rfl
      intro aliceAnswer _
      apply Finset.sum_congr rfl
      intro bobAnswer _
      split
      · exact exactFairBobMeanBornMass_eq_fullOutcome_sum
          G n S D ⟨seed, history, aliceAnswer, bobAnswer⟩
      · rfl
    _ = _ := exactFairFullOutcomeBornMass_accepted_sum
      G n S D seed


-- @@ L4490-4490 verbatim
end


-- @@ L4492-4492 verbatim
section


-- @@ L4494-4495 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L4498-4498 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L4500-4500 verbatim
variable {X Y A B : Type*}

-- @@ L4501-4501 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L4503-4510 verbatim
private abbrev ExactFairAliceScalarAtom
    (X Y A B : Type*)
    [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :=
  ExactRevealHistory X Y D seed ×
    ({j : Fin n // j ∈ D} → A) ×
    ({j : Fin n // j ∈ D} → B) × Y


-- @@ L4512-4521 verbatim
private def exactFairAliceScalarCountingWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairAliceScalarAtom X Y A B D seed) : ℝ :=
  if exactHistoryAccepted G n D
    ⟨seed, atom.1, atom.2.1, atom.2.2.1⟩ then
    exactRevealMass G n D seed atom.1 *
      G.marginalY atom.2.2.2
  else 0


-- @@ L4523-4532 verbatim
private def exactFairAliceScalarBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairAliceScalarAtom X Y A B D seed) : ℝ :=
  bornTracePairing S.state.matrix
    (exactAliceMeanFilter
      G n S D seed atom.1 atom.2.1 atom.2.2.2)
    (exactBobQuestionFilter
      G n S D seed atom.1 atom.2.2.1 atom.2.2.2)


-- @@ L4534-4541 verbatim
private abbrev ExactFairBobScalarAtom
    (X Y A B : Type*)
    [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :=
  ExactRevealHistory X Y D seed ×
    ({j : Fin n // j ∈ D} → A) ×
    ({j : Fin n // j ∈ D} → B) × X


-- @@ L4543-4552 verbatim
private def exactFairBobScalarCountingWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairBobScalarAtom X Y A B D seed) : ℝ :=
  if exactHistoryAccepted G n D
    ⟨seed, atom.1, atom.2.1, atom.2.2.1⟩ then
    exactRevealMass G n D seed atom.1 *
      G.marginalX atom.2.2.2
  else 0


-- @@ L4554-4563 verbatim
private def exactFairBobScalarBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairBobScalarAtom X Y A B D seed) : ℝ :=
  bornTracePairing S.state.matrix
    (exactAliceQuestionFilter
      G n S D seed atom.1 atom.2.1 atom.2.2.2)
    (exactBobMeanFilter
      G n S D seed atom.1 atom.2.2.1 atom.2.2.2)


-- @@ L4565-4575 verbatim
private theorem exactFairAliceScalarCountingWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairAliceScalarAtom X Y A B D seed) :
    0 ≤ exactFairAliceScalarCountingWeight G n D seed atom := by
  unfold exactFairAliceScalarCountingWeight
  split
  · exact mul_nonneg (exactRevealMass_nonneg G n D seed atom.1)
      (G.marginalY_nonneg atom.2.2.2)
  · exact le_rfl


-- @@ L4577-4587 verbatim
private theorem exactFairBobScalarCountingWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairBobScalarAtom X Y A B D seed) :
    0 ≤ exactFairBobScalarCountingWeight G n D seed atom := by
  unfold exactFairBobScalarCountingWeight
  split
  · exact mul_nonneg (exactRevealMass_nonneg G n D seed atom.1)
      (G.marginalX_nonneg atom.2.2.2)
  · exact le_rfl


-- @@ L4589-4599 verbatim
private theorem exactFairAliceScalarBornMass_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairAliceScalarAtom X Y A B D seed) :
    0 ≤ exactFairAliceScalarBornMass G n S D seed atom := by
  exact trace_mul_posSemidef_nonneg S.state.positive
    ((exactAliceMeanFilter_posSemidef
      G n S D seed atom.1 atom.2.1 atom.2.2.2).kronecker
      (exactBobQuestionFilter_posSemidef
        G n S D seed atom.1 atom.2.2.1 atom.2.2.2))


-- @@ L4601-4611 verbatim
private theorem exactFairBobScalarBornMass_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairBobScalarAtom X Y A B D seed) :
    0 ≤ exactFairBobScalarBornMass G n S D seed atom := by
  exact trace_mul_posSemidef_nonneg S.state.positive
    ((exactAliceQuestionFilter_posSemidef
      G n S D seed atom.1 atom.2.1 atom.2.2.2).kronecker
      (exactBobMeanFilter_posSemidef
        G n S D seed atom.1 atom.2.2.1 atom.2.2.2))


-- @@ L4613-4656 verbatim
private theorem exactFairAliceScalarCountingWeight_sum_le
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ atom : ExactFairAliceScalarAtom X Y A B D seed,
      exactFairAliceScalarCountingWeight G n D seed atom) ≤
      fullHistoryAnswerCount (A := A) (B := B) D := by
  classical
  simp only [Fintype.sum_prod_type]
  calc
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
      ∑ y : Y,
        exactFairAliceScalarCountingWeight G n D seed
          (history, aliceAnswer, bobAnswer, y)) ≤
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ _aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ _bobAnswer : {j : Fin n // j ∈ D} → B,
      ∑ y : Y,
        exactRevealMass G n D seed history * G.marginalY y := by
      apply Finset.sum_le_sum
      intro history _
      apply Finset.sum_le_sum
      intro aliceAnswer _
      apply Finset.sum_le_sum
      intro bobAnswer _
      apply Finset.sum_le_sum
      intro y _
      unfold exactFairAliceScalarCountingWeight
      split
      · exact le_rfl
      · exact mul_nonneg
          (exactRevealMass_nonneg G n D seed history)
          (G.marginalY_nonneg y)
    _ = fullHistoryAnswerCount (A := A) (B := B) D *
        (∑ history : ExactRevealHistory X Y D seed,
          exactRevealMass G n D seed history) *
        (∑ y : Y, G.marginalY y) := by
      simp only [sum_const, card_univ, Fintype.card_pi, univ_eq_attach, prod_const, card_attach,
        nsmul_eq_mul, Nat.cast_pow, mul_sum, fullHistoryAnswerCount, mul_assoc, mul_comm]
    _ = _ := by
      rw [exactRevealMass_sum, G.marginalY_normalized]
      ring


-- @@ L4658-4701 verbatim
private theorem exactFairBobScalarCountingWeight_sum_le
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ atom : ExactFairBobScalarAtom X Y A B D seed,
      exactFairBobScalarCountingWeight G n D seed atom) ≤
      fullHistoryAnswerCount (A := A) (B := B) D := by
  classical
  simp only [Fintype.sum_prod_type]
  calc
    (∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
      ∑ x : X,
        exactFairBobScalarCountingWeight G n D seed
          (history, aliceAnswer, bobAnswer, x)) ≤
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ _aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ _bobAnswer : {j : Fin n // j ∈ D} → B,
      ∑ x : X,
        exactRevealMass G n D seed history * G.marginalX x := by
      apply Finset.sum_le_sum
      intro history _
      apply Finset.sum_le_sum
      intro aliceAnswer _
      apply Finset.sum_le_sum
      intro bobAnswer _
      apply Finset.sum_le_sum
      intro x _
      unfold exactFairBobScalarCountingWeight
      split
      · exact le_rfl
      · exact mul_nonneg
          (exactRevealMass_nonneg G n D seed history)
          (G.marginalX_nonneg x)
    _ = fullHistoryAnswerCount (A := A) (B := B) D *
        (∑ history : ExactRevealHistory X Y D seed,
          exactRevealMass G n D seed history) *
        (∑ x : X, G.marginalX x) := by
      simp only [sum_const, card_univ, Fintype.card_pi, univ_eq_attach, prod_const, card_attach,
        nsmul_eq_mul, Nat.cast_pow, mul_sum, fullHistoryAnswerCount, mul_assoc, mul_comm]
    _ = _ := by
      rw [exactRevealMass_sum, G.marginalX_normalized]
      ring


-- @@ L4703-4747 verbatim
private theorem exactFairAliceScalarBornMass_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ atom : ExactFairAliceScalarAtom X Y A B D seed,
      exactFairAliceScalarCountingWeight G n D seed atom *
        exactFairAliceScalarBornMass G n S D seed atom) =
      repeatedPostselectionMass G n S D := by
  classical
  calc
    (∑ atom : ExactFairAliceScalarAtom X Y A B D seed,
      exactFairAliceScalarCountingWeight G n D seed atom *
        exactFairAliceScalarBornMass G n S D seed atom) =
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            (∑ y : Y, G.marginalY y *
              bornTracePairing S.state.matrix
                (exactAliceMeanFilter
                  G n S D seed history aliceAnswer y)
                (exactBobQuestionFilter
                  G n S D seed history bobAnswer y))
        else 0 := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro history _
      apply Finset.sum_congr rfl
      intro aliceAnswer _
      apply Finset.sum_congr rfl
      intro bobAnswer _
      by_cases accepted : exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩
      · simp only [exactFairAliceScalarCountingWeight,
          exactFairAliceScalarBornMass,
          ite_eq_left accepted, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      · simp only [exactFairAliceScalarCountingWeight, accepted, ↓reduceIte, zero_mul,
          sum_const_zero]
    _ = _ := exactFairAliceMeanAcceptedBornMass_sum
      G n S D seed


-- @@ L4749-4793 verbatim
private theorem exactFairBobScalarBornMass_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    (∑ atom : ExactFairBobScalarAtom X Y A B D seed,
      exactFairBobScalarCountingWeight G n D seed atom *
        exactFairBobScalarBornMass G n S D seed atom) =
      repeatedPostselectionMass G n S D := by
  classical
  calc
    (∑ atom : ExactFairBobScalarAtom X Y A B D seed,
      exactFairBobScalarCountingWeight G n D seed atom *
        exactFairBobScalarBornMass G n S D seed atom) =
      ∑ history : ExactRevealHistory X Y D seed,
      ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
      ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
        if exactHistoryAccepted G n D
          ⟨seed, history, aliceAnswer, bobAnswer⟩ then
          exactRevealMass G n D seed history *
            (∑ x : X, G.marginalX x *
              bornTracePairing S.state.matrix
                (exactAliceQuestionFilter
                  G n S D seed history aliceAnswer x)
                (exactBobMeanFilter
                  G n S D seed history bobAnswer x))
        else 0 := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro history _
      apply Finset.sum_congr rfl
      intro aliceAnswer _
      apply Finset.sum_congr rfl
      intro bobAnswer _
      by_cases accepted : exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩
      · simp only [exactFairBobScalarCountingWeight,
          exactFairBobScalarBornMass,
          ite_eq_left accepted, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      · simp only [exactFairBobScalarCountingWeight, accepted, ↓reduceIte, zero_mul,
          sum_const_zero]
    _ = _ := exactFairBobMeanAcceptedBornMass_sum
      G n S D seed


-- @@ L4795-4811 verbatim
private theorem exactFairAliceScalarBornMass_le_one
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairAliceScalarAtom X Y A B D seed) :
    exactFairAliceScalarBornMass G n S D seed atom ≤ 1 := by
  exact bornTracePairing_contractions_le_one S.state
    (exactAliceMeanFilter
      G n S D seed atom.1 atom.2.1 atom.2.2.2)
    (exactAliceMeanFilter_complement_posSemidef
      G n S D seed atom.1 atom.2.1 atom.2.2.2)
    (exactBobQuestionFilter
      G n S D seed atom.1 atom.2.2.1 atom.2.2.2)
    (exactBobQuestionFilter_posSemidef
      G n S D seed atom.1 atom.2.2.1 atom.2.2.2)
    (exactBobQuestionFilter_complement_posSemidef
      G n S D seed atom.1 atom.2.2.1 atom.2.2.2)


-- @@ L4813-4829 verbatim
private theorem exactFairBobScalarBornMass_le_one
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (atom : ExactFairBobScalarAtom X Y A B D seed) :
    exactFairBobScalarBornMass G n S D seed atom ≤ 1 := by
  exact bornTracePairing_contractions_le_one S.state
    (exactAliceQuestionFilter
      G n S D seed atom.1 atom.2.1 atom.2.2.2)
    (exactAliceQuestionFilter_complement_posSemidef
      G n S D seed atom.1 atom.2.1 atom.2.2.2)
    (exactBobMeanFilter
      G n S D seed atom.1 atom.2.2.1 atom.2.2.2)
    (exactBobMeanFilter_posSemidef
      G n S D seed atom.1 atom.2.2.1 atom.2.2.2)
    (exactBobMeanFilter_complement_posSemidef
      G n S D seed atom.1 atom.2.2.1 atom.2.2.2)


-- @@ L4831-4848 verbatim
private def exactFairAliceSeedScalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) : ℝ :=
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
      ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        (∑ y : Y, G.marginalY y *
          Real.negMulLog
            (bornTracePairing S.state.matrix
              (exactAliceMeanFilter
                G n S D seed history aliceAnswer y)
              (exactBobQuestionFilter
                G n S D seed history bobAnswer y)))
    else 0


-- @@ L4850-4867 verbatim
private def exactFairBobSeedScalarEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) : ℝ :=
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
      ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        (∑ x : X, G.marginalX x *
          Real.negMulLog
            (bornTracePairing S.state.matrix
              (exactAliceQuestionFilter
                G n S D seed history aliceAnswer x)
              (exactBobMeanFilter
                G n S D seed history bobAnswer x)))
    else 0


-- @@ L4869-4896 verbatim
private theorem exactFairAliceSeedScalarEntropy_eq_weighted
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    exactFairAliceSeedScalarEntropy G n S D seed =
      ∑ atom : ExactFairAliceScalarAtom X Y A B D seed,
        exactFairAliceScalarCountingWeight G n D seed atom *
          Real.negMulLog
            (exactFairAliceScalarBornMass G n S D seed atom) := by
  classical
  unfold exactFairAliceSeedScalarEntropy
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro aliceAnswer _
  apply Finset.sum_congr rfl
  intro bobAnswer _
  by_cases accepted : exactHistoryAccepted G n D
    ⟨seed, history, aliceAnswer, bobAnswer⟩
  · simp only [ite_eq_left accepted,
      exactFairAliceScalarCountingWeight,
      exactFairAliceScalarBornMass,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  · simp only [accepted, ↓reduceIte, exactFairAliceScalarCountingWeight, zero_mul, sum_const_zero]


-- @@ L4898-4925 verbatim
private theorem exactFairBobSeedScalarEntropy_eq_weighted
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    exactFairBobSeedScalarEntropy G n S D seed =
      ∑ atom : ExactFairBobScalarAtom X Y A B D seed,
        exactFairBobScalarCountingWeight G n D seed atom *
          Real.negMulLog
            (exactFairBobScalarBornMass G n S D seed atom) := by
  classical
  unfold exactFairBobSeedScalarEntropy
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro aliceAnswer _
  apply Finset.sum_congr rfl
  intro bobAnswer _
  by_cases accepted : exactHistoryAccepted G n D
    ⟨seed, history, aliceAnswer, bobAnswer⟩
  · simp only [ite_eq_left accepted,
      exactFairBobScalarCountingWeight,
      exactFairBobScalarBornMass,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · simp only [accepted, ↓reduceIte, exactFairBobScalarCountingWeight, zero_mul, sum_const_zero]


-- @@ L4927-4967 verbatim
private theorem exactFairAliceSeedScalarEntropy_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (seed : ExactRemainingSeed D) :
    exactFairAliceSeedScalarEntropy G n S D seed ≤
      repeatedPostselectionMass G n S D *
        Real.log (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) := by
  classical
  let w := exactFairAliceScalarCountingWeight G n D seed
  let mass := exactFairAliceScalarBornMass G n S D seed
  let W : ℝ := ∑ atom : ExactFairAliceScalarAtom X Y A B D seed,
    w atom
  have moment :
      (∑ atom : ExactFairAliceScalarAtom X Y A B D seed,
        w atom * mass atom) = repeatedPostselectionMass G n S D :=
    exactFairAliceScalarBornMass_sum G n S D seed
  have lower : repeatedPostselectionMass G n S D ≤ W := by
    rw [← moment]
    apply Finset.sum_le_sum
    intro atom _
    exact mul_le_of_le_one_right
      (exactFairAliceScalarCountingWeight_nonneg G n D seed atom)
      (exactFairAliceScalarBornMass_le_one G n S D seed atom)
  have count : W ≤ fullHistoryAnswerCount (A := A) (B := B) D :=
    exactFairAliceScalarCountingWeight_sum_le G n D seed
  have estimate := finite_weighted_entropy_le_of_weight_bound
    (Finset.univ : Finset (ExactFairAliceScalarAtom X Y A B D seed))
    w mass
    (W := W)
    (N := fullHistoryAnswerCount (A := A) (B := B) D)
    (p := repeatedPostselectionMass G n S D)
    (fun atom _ =>
      exactFairAliceScalarCountingWeight_nonneg G n D seed atom)
    (fun atom _ =>
      exactFairAliceScalarBornMass_nonneg G n S D seed atom)
    (lt_of_lt_of_le positive lower)
    positive rfl moment count
  rw [exactFairAliceSeedScalarEntropy_eq_weighted]
  exact estimate


-- @@ L4969-5009 verbatim
private theorem exactFairBobSeedScalarEntropy_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (seed : ExactRemainingSeed D) :
    exactFairBobSeedScalarEntropy G n S D seed ≤
      repeatedPostselectionMass G n S D *
        Real.log (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) := by
  classical
  let w := exactFairBobScalarCountingWeight G n D seed
  let mass := exactFairBobScalarBornMass G n S D seed
  let W : ℝ := ∑ atom : ExactFairBobScalarAtom X Y A B D seed,
    w atom
  have moment :
      (∑ atom : ExactFairBobScalarAtom X Y A B D seed,
        w atom * mass atom) = repeatedPostselectionMass G n S D :=
    exactFairBobScalarBornMass_sum G n S D seed
  have lower : repeatedPostselectionMass G n S D ≤ W := by
    rw [← moment]
    apply Finset.sum_le_sum
    intro atom _
    exact mul_le_of_le_one_right
      (exactFairBobScalarCountingWeight_nonneg G n D seed atom)
      (exactFairBobScalarBornMass_le_one G n S D seed atom)
  have count : W ≤ fullHistoryAnswerCount (A := A) (B := B) D :=
    exactFairBobScalarCountingWeight_sum_le G n D seed
  have estimate := finite_weighted_entropy_le_of_weight_bound
    (Finset.univ : Finset (ExactFairBobScalarAtom X Y A B D seed))
    w mass
    (W := W)
    (N := fullHistoryAnswerCount (A := A) (B := B) D)
    (p := repeatedPostselectionMass G n S D)
    (fun atom _ =>
      exactFairBobScalarCountingWeight_nonneg G n D seed atom)
    (fun atom _ =>
      exactFairBobScalarBornMass_nonneg G n S D seed atom)
    (lt_of_lt_of_le positive lower)
    positive rfl moment count
  rw [exactFairBobSeedScalarEntropy_eq_weighted]
  exact estimate


-- @@ L5011-5025 verbatim
private theorem exactReverseAliceAcceptedScalarEntropy_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceAcceptedScalarEntropy
        G n S D side context marker ≤
      repeatedPostselectionMass G n S D *
        Real.log (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) := by
  exact exactFairAliceSeedScalarEntropy_le G n S D positive
    (exactReverseBobMarkerDecode side context marker)


-- @@ L5027-5041 verbatim
private theorem exactReverseBobAcceptedScalarEntropy_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobAcceptedScalarEntropy
        G n S D side context marker ≤
      repeatedPostselectionMass G n S D *
        Real.log (fullHistoryAnswerCount (A := A) (B := B) D /
          repeatedPostselectionMass G n S D) := by
  exact exactFairBobSeedScalarEntropy_le G n S D positive
    (exactReverseAliceMarkerDecode side context marker)


-- @@ L5043-5043 verbatim
end


-- @@ L5045-5045 verbatim
section


-- @@ L5047-5047 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L5049-5049 verbatim
variable {X Y A B : Type*}

-- @@ L5050-5050 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L5052-5053 verbatim
private def sourceAnswerAlphabetBound (A B : Type*) [Fintype A] [Fintype B] : ℝ :=
  max 1 ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))


-- @@ L5055-5058 verbatim
private theorem one_le_sourceAnswerAlphabetBound
    (A B : Type*) [Fintype A] [Fintype B] :
    1 ≤ sourceAnswerAlphabetBound A B := by
  exact le_max_left _ _


-- @@ L5060-5063 verbatim
private theorem sourceAnswerAlphabetBound_log_nonneg
    (A B : Type*) [Fintype A] [Fintype B] :
    0 ≤ Real.log (sourceAnswerAlphabetBound A B) := by
  exact Real.log_nonneg (one_le_sourceAnswerAlphabetBound A B)


-- @@ L5065-5072 verbatim
private theorem fullHistoryAnswerCount_le_sourceAnswerAlphabetBound_pow
    {n : ℕ} (D : Finset (Fin n)) :
    fullHistoryAnswerCount (A := A) (B := B) D ≤
      sourceAnswerAlphabetBound A B ^ D.card := by
  rw [fullHistoryAnswerCount_eq, ← mul_pow]
  exact pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (le_max_right 1 _) _


-- @@ L5074-5096 verbatim
theorem fullHistoryAnswerCount_pos_of_postselection
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D)
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    0 < fullHistoryAnswerCount (A := A) (B := B) D := by
  classical
  have hmass := fullHistoryAtomBornMass_sum G n S D L hL
  have hfirst :
      (∑ t : FullHistoryEntropyAtom X Y A B n D L,
        fullHistoryAtomCountingWeight G D L t *
          fullHistoryAtomBornMass G n S D L t) ≤
        ∑ t : FullHistoryEntropyAtom X Y A B n D L,
          fullHistoryAtomCountingWeight G D L t := by
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_of_le_one_right
      (fullHistoryAtomCountingWeight_nonneg G D L t)
      (fullHistoryAtomBornMass_le_one G n S D L t)
  have hsecond := fullHistoryAtomCountingWeight_sum_le G D L
  linarith


-- @@ L5098-5114 verbatim
theorem divisor_greedy_remaining_bounds
    {n q : ℕ} (hq : 2 ≤ q)
    {D : Finset (Fin n)} (hD : D.card < n / q) :
    0 < (Finset.univ \ D).card ∧
      n ≤ 2 * (Finset.univ \ D).card ∧
      D.card * q ≤ 2 * (Finset.univ \ D).card := by
  classical
  have hqpos : 0 < q := by omega
  have hdq : D.card * q < n :=
    divisor_greedy_card_mul_lt hqpos hD
  have htwo : D.card * 2 < n :=
    lt_of_le_of_lt (Nat.mul_le_mul_left D.card hq) hdq
  have hcard : (Finset.univ \ D).card + D.card = n := by
    simpa only [card_univ, Fintype.card_fin] using
      (Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ D))
  omega


-- @@ L5116-5215 verbatim
private theorem divisor_greedy_log_cost_per_remaining_le
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} (hη : 0 < η)
    {q : ℕ} (hq : 2 ≤ q)
    (D : Finset (Fin n))
    (hD : D.card < n / q)
    (hwitness :
      Real.exp (-(η / (4 * (q : ℝ))) * (n : ℝ)) <
        S.winProbability)
    (hmass :
      S.winProbability ≤
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) /
        ((Finset.univ \ D).card : ℝ) ≤
      (2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2) /
        (q : ℝ) := by
  classical
  let p : ℝ :=
    (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
  let m : ℕ := (Finset.univ \ D).card
  let k : ℝ := sourceAnswerAlphabetBound A B
  have hqpos : 0 < q := by omega
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hθ : 0 < S.winProbability :=
    lt_trans (Real.exp_pos _) hwitness
  have hp : 0 < p := lt_of_lt_of_le hθ hmass
  have hN : 0 < fullHistoryAnswerCount (A := A) (B := B) D :=
    fullHistoryAnswerCount_pos_of_postselection G n S D ∅
      (Finset.empty_subset _) hp
  have hklog : 0 ≤ Real.log k :=
    sourceAnswerAlphabetBound_log_nonneg A B
  have hcount :
      Real.log (fullHistoryAnswerCount (A := A) (B := B) D) ≤
        (D.card : ℝ) * Real.log k := by
    calc
      Real.log (fullHistoryAnswerCount (A := A) (B := B) D) ≤
          Real.log (k ^ D.card) :=
        Real.log_le_log hN
          (fullHistoryAnswerCount_le_sourceAnswerAlphabetBound_pow D)
      _ = (D.card : ℝ) * Real.log k := Real.log_pow _ _
  have hlogθ :
      Real.log (1 / S.winProbability) <
        (η / (4 * (q : ℝ))) * (n : ℝ) := by
    have hlog := (Real.lt_log_iff_exp_lt hθ).mpr hwitness
    rw [one_div, Real.log_inv]
    linarith
  have hlogp :
      Real.log (1 / p) ≤
        (η / (4 * (q : ℝ))) * (n : ℝ) := by
    exact (postselection_log_cost_le hθ hmass).trans hlogθ.le
  have htotal :
      Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D / p) ≤
        (D.card : ℝ) * Real.log k +
          (η / (4 * (q : ℝ))) * (n : ℝ) := by
    rw [Real.log_div hN.ne' hp.ne']
    rw [one_div, Real.log_inv] at hlogp
    linarith
  obtain ⟨hmnat, hnmnat, hdqmnat⟩ :=
    divisor_greedy_remaining_bounds hq hD
  have hm : 0 < (m : ℝ) := by
    exact_mod_cast hmnat
  have hnm : (n : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast hnmnat
  have hdqm :
      (D.card : ℝ) * (q : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast hdqmnat
  have hdratio :
      (D.card : ℝ) / (m : ℝ) ≤ 2 / (q : ℝ) := by
    exact (div_le_div_iff₀ hm hqreal).mpr hdqm
  have hnratio : (n : ℝ) / (m : ℝ) ≤ 2 := by
    exact (div_le_iff₀ hm).mpr hnm
  have hrate : 0 ≤ η / (4 * (q : ℝ)) := by positivity
  change
    Real.log (fullHistoryAnswerCount (A := A) (B := B) D / p) /
        (m : ℝ) ≤
      (2 * Real.log k + η / 2) / (q : ℝ)
  calc
    Real.log (fullHistoryAnswerCount (A := A) (B := B) D / p) /
        (m : ℝ) ≤
      ((D.card : ℝ) * Real.log k +
        (η / (4 * (q : ℝ))) * (n : ℝ)) / (m : ℝ) := by
        exact (div_le_div_iff_of_pos_right hm).mpr htotal
    _ = ((D.card : ℝ) / (m : ℝ)) * Real.log k +
        (η / (4 * (q : ℝ))) * ((n : ℝ) / (m : ℝ)) := by
          ring
    _ ≤ (2 / (q : ℝ)) * Real.log k +
        (η / (4 * (q : ℝ))) * 2 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hdratio hklog)
            (mul_le_mul_of_nonneg_left hnratio hrate)
    _ = (2 * Real.log k + η / 2) / (q : ℝ) := by
      field_simp
      ring


-- @@ L5217-5254 verbatim
private theorem exists_source_rounding_divisor
    (A B : Type*) [Fintype A] [Fintype B]
    {K η δ : ℝ}
    (hK : 0 ≤ K) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ q : ℕ, 2 ≤ q ∧
      8 * K *
          ((2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2) /
            (q : ℝ)) ≤
        δ ^ 2 := by
  let C : ℝ :=
    8 * K * (2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog := sourceAnswerAlphabetBound_log_nonneg A B
    positivity
  have hsquare : 0 < δ ^ 2 := sq_pos_of_pos hδ
  obtain ⟨q, hq⟩ := exists_nat_gt
    (max (2 : ℝ) (C / δ ^ 2))
  have htwo : (2 : ℝ) < (q : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hq
  have hqnat : 2 ≤ q := by
    have hstrict : 2 < q := by exact_mod_cast htwo
    omega
  have hqreal : 0 < (q : ℝ) := by positivity
  have hthreshold : C / δ ^ 2 < (q : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hq
  have hsmall : C / (q : ℝ) < δ ^ 2 := by
    apply (div_lt_iff₀ hqreal).mpr
    have hcross := (div_lt_iff₀ hsquare).mp hthreshold
    linarith [hC]
  refine ⟨q, hqnat, ?_⟩
  calc
    8 * K *
        ((2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2) /
          (q : ℝ)) = C / (q : ℝ) := by
      dsimp [C]
      ring
    _ ≤ δ ^ 2 := hsmall.le


-- @@ L5256-5334 verbatim
theorem arbitrarily_large_purified_divisor_greedy_conditioning_with_rounding
    (G : Game X Y A B)
    (hwitness : HasSubexponentialWitness (repeatedEntangledValue G))
    {η K δ : ℝ}
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ q : ℕ, 2 ≤ q ∧
      ∀ N₀ : ℕ, ∃ n : ℕ, N₀ < n ∧
        ∃ S : Strategy (G.repeat n),
          ∃ D : Finset (Fin n),
            Real.exp (-(η / (4 * (q : ℝ))) * (n : ℝ)) <
              (purifiedStrategy S).winProbability ∧
            D.card < n / q ∧
            (purifiedStrategy S).winProbability ≤
              (strategyEventLaw (G.repeat n) (purifiedStrategy S)).eventMass
                (FiniteEventLaw.winEvent
                  (repeatedCoordinateWin G n) D) ∧
            (∑ i ∈ Finset.univ \ D,
              FiniteEventLaw.failureMass
                (strategyEventLaw (G.repeat n) (purifiedStrategy S))
                (repeatedCoordinateWin G n) D i) <
              ((Finset.univ \ D).card : ℝ) *
                (η *
                  (strategyEventLaw (G.repeat n)
                    (purifiedStrategy S)).eventMass
                      (FiniteEventLaw.winEvent
                        (repeatedCoordinateWin G n) D)) ∧
            8 * K *
                Real.log
                  (fullHistoryAnswerCount (A := A) (B := B) D /
                    (strategyEventLaw (G.repeat n)
                      (purifiedStrategy S)).eventMass
                        (FiniteEventLaw.winEvent
                          (repeatedCoordinateWin G n) D)) /
                  ((Finset.univ \ D).card : ℝ) ≤
              δ ^ 2 := by
  classical
  obtain ⟨q, hq, hqcost⟩ :=
    exists_source_rounding_divisor A B hK hη hδ
  refine ⟨q, hq, ?_⟩
  intro N₀
  have hqpos : 0 < q := by omega
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hrate : 0 < η / (4 * (q : ℝ)) := by positivity
  obtain ⟨n, hn, S, hS⟩ :=
    arbitrarily_large_purifiedRepeatedStrategy_of_subexponentialWitness
      G hwitness hrate (max N₀ q)
  have hqn : q ≤ n :=
    (Nat.le_max_right N₀ q).trans (Nat.le_of_lt hn)
  obtain ⟨D, hD, hp, hfail⟩ :=
    repeatedStrategy_exists_divisor_greedy_conditioning G n
      (purifiedStrategy S) hη hη_one hqpos hqn hS
  refine ⟨n, (Nat.le_max_left N₀ q).trans_lt hn,
    S, D, hS, hD, hp, hfail, ?_⟩
  have hlog := divisor_greedy_log_cost_per_remaining_le
    G n (purifiedStrategy S) hη hq D hD hS hp
  calc
    8 * K *
        Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D /
            (strategyEventLaw (G.repeat n)
              (purifiedStrategy S)).eventMass
                (FiniteEventLaw.winEvent
                  (repeatedCoordinateWin G n) D)) /
            ((Finset.univ \ D).card : ℝ) =
        (8 * K) *
          (Real.log
            (fullHistoryAnswerCount (A := A) (B := B) D /
              (strategyEventLaw (G.repeat n)
                (purifiedStrategy S)).eventMass
                  (FiniteEventLaw.winEvent
                    (repeatedCoordinateWin G n) D)) /
            ((Finset.univ \ D).card : ℝ)) := by
      ring
    _ ≤ 8 * K *
        ((2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2) /
          (q : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ δ ^ 2 := hqcost


-- @@ L5336-5336 verbatim
end


-- @@ L5338-5338 verbatim
section


-- @@ L5340-5340 verbatim
open scoped BigOperators


-- @@ L5342-5342 verbatim
variable {X Y A B : Type*}

-- @@ L5343-5343 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L5345-5358 verbatim
theorem postselectionLogCost_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    0 ≤ postselectionLogCost G n S D := by
  have at_most_one : repeatedPostselectionMass G n S D ≤ 1 :=
    postselectionMass_le_one
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D
  have inverse_at_least_one :
      (1 : ℝ) ≤ 1 / repeatedPostselectionMass G n S D := by
    apply (le_div_iff₀ positive).2
    simpa only [one_mul] using at_most_one
  exact Real.log_nonneg inverse_at_least_one


-- @@ L5360-5390 verbatim
theorem answerLogCost_nonneg_of_postselection
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    0 ≤ answerLogCost (A := A) (B := B) D := by
  classical
  by_cases empty : D.card = 0
  · simp only [answerLogCost, empty, CharP.cast_eq_zero, zero_mul, Std.le_refl]
  have count_positive :=
    answerCount_pos_of_postselection G n S D positive
  rw [fullHistoryAnswerCount_eq, ← mul_pow] at count_positive
  have alphabet_nonnegative :
      0 ≤ (Fintype.card A : ℝ) * (Fintype.card B : ℝ) := by
    positivity
  have alphabet_positive :
      0 < (Fintype.card A : ℝ) * (Fintype.card B : ℝ) := by
    by_contra not_positive
    have zero :
        (Fintype.card A : ℝ) * (Fintype.card B : ℝ) = 0 :=
      le_antisymm (le_of_not_gt not_positive) alphabet_nonnegative
    simp only [zero, ne_eq, empty, not_false_eq_true, zero_pow,
      lt_self_iff_false] at count_positive
  have natural_positive :
      0 < Fintype.card A * Fintype.card B := by
    exact_mod_cast alphabet_positive
  have alphabet_at_least_one :
      (1 : ℝ) ≤ (Fintype.card A : ℝ) * (Fintype.card B : ℝ) := by
    exact_mod_cast natural_positive
  unfold answerLogCost
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg alphabet_at_least_one)


-- @@ L5392-5412 verbatim
theorem exactSourceClassicalInformationRate_le_three_martingaleRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    exactSourceClassicalInformationRate G n S D ≤
      3 * martingaleRate G n S D := by
  have answer_nonnegative :=
    answerLogCost_nonneg_of_postselection
      G n S D positive
  unfold exactSourceClassicalInformationRate
    martingaleRate
  have denominator_nonnegative :
      0 ≤ ((Finset.univ \ D).card : ℝ) := by positivity
  by_cases denominator_zero : ((Finset.univ \ D).card : ℝ) = 0
  · simp only [denominator_zero, div_zero, mul_zero, Std.le_refl]
  have denominator_positive :
      0 < ((Finset.univ \ D).card : ℝ) :=
    lt_of_le_of_ne denominator_nonnegative (Ne.symm denominator_zero)
  apply (div_le_iff₀ denominator_positive).2
  field_simp
  linarith


-- @@ L5414-5429 verbatim
theorem exactSourcePinskerRate_le_half_of_martingaleRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    {rateTolerance : ℝ} (rate_nonnegative : 0 ≤ rateTolerance)
    (rate_bound :
      martingaleRate G n S D ≤ rateTolerance ^ 2 / 8) :
    exactSourcePinskerRate G n S D ≤ rateTolerance / 2 := by
  unfold exactSourcePinskerRate
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have information :=
      exactSourceClassicalInformationRate_le_three_martingaleRate
        G n S D positive
    nlinarith


-- @@ L5431-5500 verbatim
theorem exact_arbitrarily_large_conditioning_of_subexponentialWitness
    (G : Game X Y A B)
    (witness : HasSubexponentialWitness (repeatedEntangledValue G))
    {failureTolerance rateTolerance : ℝ}
    (failure_positive : 0 < failureTolerance)
    (failure_at_most_one : failureTolerance ≤ 1)
    (rate_positive : 0 < rateTolerance)
    (lower : ℕ) :
    ∃ n : ℕ, lower < n ∧
      ∃ S : Strategy (G.repeat n),
        ∃ D : Finset (Fin n),
          0 < S.winProbability ∧
          0 < repeatedPostselectionMass G n S D ∧
          0 < (Finset.univ \ D).card ∧
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D < failureTolerance ∧
          martingaleRate G n S D ≤
            rateTolerance ^ 2 / 8 ∧
          exactSourcePinskerRate G n S D ≤
            rateTolerance / 2 := by
  classical
  obtain ⟨q, q_at_least_two, extract⟩ :=
    arbitrarily_large_purified_divisor_greedy_conditioning_with_rounding
      G witness (K := (1 : ℝ))
      failure_positive failure_at_most_one
      (by norm_num) rate_positive
  obtain ⟨n, beyond, S, D, winning, small, mass, failure, cost⟩ :=
    extract lower
  let actual : Strategy (G.repeat n) := purifiedStrategy S
  have actual_positive : 0 < actual.winProbability :=
    lt_trans (Real.exp_pos _) winning
  have postselection_positive :
      0 < repeatedPostselectionMass G n actual D := by
    exact lt_of_lt_of_le actual_positive mass
  have remaining_positive : 0 < (Finset.univ \ D).card :=
    (divisor_greedy_remaining_bounds q_at_least_two small).1
  have failure_small :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) actual)
          (repeatedCoordinateWin G n) D < failureTolerance := by
    apply uniformRemainingFailure_lt_of_failure_sum
      (strategyEventLaw (G.repeat n) actual)
      (repeatedCoordinateWin G n) D
      postselection_positive remaining_positive
    exact failure
  have scaled_rate :
      8 * martingaleRate G n actual D ≤ rateTolerance ^ 2 := by
    calc
      8 * martingaleRate G n actual D =
          8 * Real.log
            (fullHistoryAnswerCount (A := A) (B := B) D /
              repeatedPostselectionMass G n actual D) /
            ((Finset.univ \ D).card : ℝ) := by
              unfold martingaleRate
              rw [← martingale_log_cost_eq
                G n actual D postselection_positive]
              ring
      _ ≤ rateTolerance ^ 2 := by
        simpa only [repeatedPostselectionMass, postselectionMass, mul_one, actual] using cost
  have actual_rate :
      martingaleRate G n actual D ≤
        rateTolerance ^ 2 / 8 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    linarith
  exact ⟨n, beyond, actual, D, actual_positive,
    postselection_positive, remaining_positive, failure_small,
    actual_rate,
    exactSourcePinskerRate_le_half_of_martingaleRate
      G n actual D postselection_positive rate_positive.le actual_rate⟩


-- @@ L5502-5502 verbatim
end


-- @@ L5504-5504 verbatim
section


-- @@ L5506-5507 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace



-- @@ L5510-5510 verbatim
open QuantumParallelRepetition.ClassicalInformation


-- @@ L5512-5512 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L5514-5514 verbatim
variable {X Y A B : Type*}

-- @@ L5515-5515 verbatim
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]


-- @@ L5517-5554 verbatim
theorem exactReversePartitionInverseCard_le
    {M : Type*} [Fintype M] :
    (∑ side : Finset M,
      reversePartitionWeight side / (side.card : ℝ)) ≤
      2 / (Fintype.card M : ℝ) := by
  classical
  have point (side : Finset M) :
      reversePartitionWeight side / (side.card : ℝ) ≤
        forwardMarkedPartitionWeight M := by
    by_cases nonempty : side.Nonempty
    · obtain ⟨coordinate, member⟩ := nonempty
      have marked := reverseMarkedPartitionWeight_eq_forward member
      simpa only [reverseMarkedPartitionWeight, ite_eq_left member] using
        le_of_eq marked
    · have empty : side = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
      subst side
      have nonnegative : 0 ≤ forwardMarkedPartitionWeight M := by
        unfold forwardMarkedPartitionWeight
        exact div_nonneg
          (mul_nonneg (by norm_num) fairPartitionWeight_nonneg)
          (by exact_mod_cast Nat.zero_le (Fintype.card M))
      simpa only [reversePartitionWeight_empty, card_empty, CharP.cast_eq_zero, div_zero,
        ge_iff_le] using nonnegative
  calc
    (∑ side : Finset M,
      reversePartitionWeight side / (side.card : ℝ)) ≤
      ∑ _side : Finset M, forwardMarkedPartitionWeight M := by
        apply Finset.sum_le_sum
        intro side _
        exact point side
    _ = (2 / (Fintype.card M : ℝ)) *
          (∑ _side : Finset M, fairPartitionWeight M) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro side _
        unfold forwardMarkedPartitionWeight
        ring
    _ = _ := by rw [fairPartitionWeight_sum]; ring


-- @@ L5556-5585 verbatim
theorem exactReverseBobSeedInverseCard_le
    {M : Type*} [Fintype M] [DecidableEq M] :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed /
        ((exactReverseRightSide seed).card : ℝ)) ≤
      2 / (Fintype.card M : ℝ) := by
  classical
  have push := groupedMass_expectation
    (exactReverseRightSide (M := M))
    (exactSeedWeight (M := M))
    (fun side : Finset M => ((side.card : ℝ))⁻¹)
  calc
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed /
        ((exactReverseRightSide seed).card : ℝ)) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((exactReverseRightSide seed).card : ℝ)⁻¹ := by
        simp only [div_eq_mul_inv]
    _ = ∑ side : Finset M,
        groupedMass (exactReverseRightSide (M := M))
          (exactSeedWeight (M := M)) side *
          ((side.card : ℝ))⁻¹ := push.symm
    _ = ∑ side : Finset M,
        reversePartitionWeight side / (side.card : ℝ) := by
        apply Finset.sum_congr rfl
        intro side _
        rw [exactReverseBobSide_marginal]
        exact (div_eq_mul_inv _ _).symm
    _ ≤ _ := exactReversePartitionInverseCard_le


-- @@ L5587-5616 verbatim
theorem exactReverseAliceSeedInverseCard_le
    {M : Type*} [Fintype M] [DecidableEq M] :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed /
        ((exactReverseLeftSide seed).card : ℝ)) ≤
      2 / (Fintype.card M : ℝ) := by
  classical
  have push := groupedMass_expectation
    (exactReverseLeftSide (M := M))
    (exactSeedWeight (M := M))
    (fun side : Finset M => ((side.card : ℝ))⁻¹)
  calc
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed /
        ((exactReverseLeftSide seed).card : ℝ)) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((exactReverseLeftSide seed).card : ℝ)⁻¹ := by
        simp only [div_eq_mul_inv]
    _ = ∑ side : Finset M,
        groupedMass (exactReverseLeftSide (M := M))
          (exactSeedWeight (M := M)) side *
          ((side.card : ℝ))⁻¹ := push.symm
    _ = ∑ side : Finset M,
        reversePartitionWeight side / (side.card : ℝ) := by
        apply Finset.sum_congr rfl
        intro side _
        rw [exactReverseAliceSide_marginal]
        exact (div_eq_mul_inv _ _).symm
    _ ≤ _ := exactReversePartitionInverseCard_le


-- @@ L5618-5630 verbatim
theorem exactFairSourceScalarCost_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    0 ≤ repeatedPostselectionMass G n S D *
      Real.log (fullHistoryAnswerCount (A := A) (B := B) D /
        repeatedPostselectionMass G n S D) := by
  rw [martingale_log_cost_eq G n S D positive]
  exact mul_nonneg positive.le
    (add_nonneg
      (postselectionLogCost_nonneg G n S D positive)
      (answerLogCost_nonneg_of_postselection
        G n S D positive))


-- @@ L5632-5709 verbatim
theorem exactFairAcceptedAliceEntropy_le_sourceRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    exactFairAcceptedAliceEntropy G n S D ≤
      2 * (repeatedPostselectionMass G n S D *
        martingaleRate G n S D) := by
  classical
  let cost : ℝ := repeatedPostselectionMass G n S D *
    Real.log (fullHistoryAnswerCount (A := A) (B := B) D /
      repeatedPostselectionMass G n S D)
  have nonnegative : 0 ≤ cost :=
    exactFairSourceScalarCost_nonneg G n S D positive
  have mpositive : 0 < Fintype.card (SourceRemainingCoordinate D) := by
    simpa only [Fintype.card_coe, card_pos] using remaining
  unfold exactFairAcceptedAliceEntropy
  rw [exactFairAliceOperatorEntropy_reverse_marked_average
    G n S D mpositive]
  calc
    (∑ seed : ExactRemainingSeed D,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseRightSide seed).card,
          exactReverseAliceFilterOperatorMarkerEntropy
            G n S D
            (exactReverseRightSide seed)
            (exactReverseBobContext seed) marker) /
          ((exactReverseRightSide seed).card : ℝ))) ≤
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          (cost / ((exactReverseRightSide seed).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro seed _
      have nonempty : 0 < (exactReverseRightSide seed).card :=
        Finset.card_pos.mpr
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩
      have endpoint :=
        exactReverseAliceFilterOperatorMarkerEntropy_sum_le_scalarEntropy
          G n S D
          (exactReverseRightSide seed)
          (exactReverseBobContext seed) nonempty
      have scalar := exactReverseAliceAcceptedScalarEntropy_le
        G n S D positive
        (exactReverseRightSide seed)
        (exactReverseBobContext seed)
        ⟨0, nonempty⟩
      have total :
          (∑ marker : Fin (exactReverseRightSide seed).card,
            exactReverseAliceFilterOperatorMarkerEntropy
              G n S D (exactReverseRightSide seed)
                (exactReverseBobContext seed) marker) ≤ cost :=
        endpoint.trans scalar
      apply mul_le_mul_of_nonneg_left
        ((div_le_div_iff_of_pos_right
          (by exact_mod_cast nonempty)).mpr total)
        (exactSeedWeight_nonneg seed)
    _ = cost *
        (∑ seed : ExactRemainingSeed D,
          exactSeedWeight seed /
            ((exactReverseRightSide seed).card : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro seed _
      ring
    _ ≤ cost * (2 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (exactReverseBobSeedInverseCard_le
          (M := SourceRemainingCoordinate D)) nonnegative
    _ = 2 * (repeatedPostselectionMass G n S D *
        martingaleRate G n S D) := by
      dsimp [cost]
      rw [martingale_log_cost_eq G n S D positive]
      have cardinal : Fintype.card (SourceRemainingCoordinate D) =
          (Finset.univ \ D).card := by simp only [Fintype.card_coe]
      rw [cardinal]
      unfold martingaleRate
      ring


-- @@ L5711-5788 verbatim
theorem exactFairAcceptedBobEntropy_le_sourceRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    exactFairAcceptedBobEntropy G n S D ≤
      2 * (repeatedPostselectionMass G n S D *
        martingaleRate G n S D) := by
  classical
  let cost : ℝ := repeatedPostselectionMass G n S D *
    Real.log (fullHistoryAnswerCount (A := A) (B := B) D /
      repeatedPostselectionMass G n S D)
  have nonnegative : 0 ≤ cost :=
    exactFairSourceScalarCost_nonneg G n S D positive
  have mpositive : 0 < Fintype.card (SourceRemainingCoordinate D) := by
    simpa only [Fintype.card_coe, card_pos] using remaining
  unfold exactFairAcceptedBobEntropy
  rw [exactFairBobOperatorEntropy_reverse_marked_average
    G n S D mpositive]
  calc
    (∑ seed : ExactRemainingSeed D,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseLeftSide seed).card,
          exactReverseBobFilterOperatorMarkerEntropy
            G n S D
            (exactReverseLeftSide seed)
            (exactReverseAliceContext seed) marker) /
          ((exactReverseLeftSide seed).card : ℝ))) ≤
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          (cost / ((exactReverseLeftSide seed).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro seed _
      have nonempty : 0 < (exactReverseLeftSide seed).card :=
        Finset.card_pos.mpr
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩
      have endpoint :=
        exactReverseBobFilterOperatorMarkerEntropy_sum_le_scalarEntropy
          G n S D
          (exactReverseLeftSide seed)
          (exactReverseAliceContext seed) nonempty
      have scalar := exactReverseBobAcceptedScalarEntropy_le
        G n S D positive
        (exactReverseLeftSide seed)
        (exactReverseAliceContext seed)
        ⟨0, nonempty⟩
      have total :
          (∑ marker : Fin (exactReverseLeftSide seed).card,
            exactReverseBobFilterOperatorMarkerEntropy
              G n S D (exactReverseLeftSide seed)
                (exactReverseAliceContext seed) marker) ≤ cost :=
        endpoint.trans scalar
      apply mul_le_mul_of_nonneg_left
        ((div_le_div_iff_of_pos_right
          (by exact_mod_cast nonempty)).mpr total)
        (exactSeedWeight_nonneg seed)
    _ = cost *
        (∑ seed : ExactRemainingSeed D,
          exactSeedWeight seed /
            ((exactReverseLeftSide seed).card : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro seed _
      ring
    _ ≤ cost * (2 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (exactReverseAliceSeedInverseCard_le
          (M := SourceRemainingCoordinate D)) nonnegative
    _ = 2 * (repeatedPostselectionMass G n S D *
        martingaleRate G n S D) := by
      dsimp [cost]
      rw [martingale_log_cost_eq G n S D positive]
      have cardinal : Fintype.card (SourceRemainingCoordinate D) =
          (Finset.univ \ D).card := by simp only [Fintype.card_coe]
      rw [cardinal]
      unfold martingaleRate
      ring


-- @@ L5790-5800 verbatim
theorem exactFairOperatorEntropyBound_of_positive
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    ExactFairOperatorEntropyBound G n S D
      (martingaleRate G n S D) :=
  ⟨exactFairAcceptedAliceEntropy_le_sourceRate
      G n S D remaining positive,
    exactFairAcceptedBobEntropy_le_sourceRate
      G n S D remaining positive⟩


-- @@ L5802-5812 verbatim
theorem exactSourceStateDistanceBound_of_positive
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    ExactSourceStateDistanceBound G n S D
      (martingaleRate G n S D) :=
  exactSourceStateDistanceBound_of_fair_operator_entropy
    G n S D (martingaleRate G n S D) positive
    (exactFairOperatorEntropyBound_of_positive
      G n S D remaining positive)


-- @@ L5814-5814 verbatim
end


-- @@ L5816-5816 verbatim
section


-- @@ L5818-5818 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder


-- @@ L5820-5843 verbatim
theorem unconditionalLiterature_weightedNormMean_le_sqrtEnergy
    {ι : Type*} [Fintype ι]
    (weight value : ι → ℝ)
    (weight_nonnegative : ∀ i, 0 ≤ weight i)
    (weight_normalized : (∑ i, weight i) = 1)
    (value_nonnegative : ∀ i, 0 ≤ value i) :
    (∑ i, weight i * value i) ≤
      Real.sqrt (∑ i, weight i * value i ^ 2) := by
  classical
  have jensen := weighted_rpow_mean_le weight
    (fun i => value i ^ 2)
    weight_nonnegative weight_normalized
    (fun i => sq_nonneg (value i))
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  calc
    (∑ i, weight i * value i) =
        ∑ i, weight i * (value i ^ 2) ^ (1 / 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (value_nonnegative i)]
    _ ≤ (∑ i, weight i * value i ^ 2) ^ (1 / 2 : ℝ) := jensen
    _ = Real.sqrt (∑ i, weight i * value i ^ 2) := by
      rw [Real.sqrt_eq_rpow]


-- @@ L5845-5860 verbatim
theorem unconditionalLiterature_sqrt_two_mul_sqrt_thirtytwo
    (η : ℝ) :
    8 * Real.sqrt 2 * Real.sqrt (32 * η) =
      64 * Real.sqrt η := by
  calc
    8 * Real.sqrt 2 * Real.sqrt (32 * η) =
        8 * Real.sqrt ((2 : ℝ) * (32 * η)) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          ring
    _ = 8 * Real.sqrt ((64 : ℝ) * η) := by
          congr 2
          ring
    _ = 64 * Real.sqrt η := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
          norm_num
          ring


-- @@ L5862-5907 verbatim
theorem unconditionalLiterature_weightedAsynchronous_le
    {ι : Type*} [Fintype ι]
    (weight value asynchronous : ι → ℝ)
    (weight_nonnegative : ∀ i, 0 ≤ weight i)
    (weight_normalized : (∑ i, weight i) = 1)
    (value_nonnegative : ∀ i, 0 ≤ value i)
    (η δ : ℝ)
    (source_energy : (∑ i, weight i * value i ^ 2) ≤ 32 * η)
    (physical : ∀ i,
      asynchronous i ≤ 8 * Real.sqrt 2 * value i + δ) :
    (∑ i, weight i * asynchronous i) ≤
      64 * Real.sqrt η + δ := by
  classical
  have mean :=
    unconditionalLiterature_weightedNormMean_le_sqrtEnergy
      weight value weight_nonnegative weight_normalized
      value_nonnegative
  have distance :
      (∑ i, weight i * value i) ≤ Real.sqrt (32 * η) :=
    mean.trans (Real.sqrt_le_sqrt source_energy)
  calc
    (∑ i, weight i * asynchronous i) ≤
        ∑ i, weight i *
          (8 * Real.sqrt 2 * value i + δ) := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left
              (physical i) (weight_nonnegative i)
    _ = 8 * Real.sqrt 2 *
          (∑ i, weight i * value i) + δ := by
          calc
            (∑ i, weight i *
                (8 * Real.sqrt 2 * value i + δ)) =
                8 * Real.sqrt 2 *
                  (∑ i, weight i * value i) +
                    δ * (∑ i, weight i) := by
                      rw [Finset.mul_sum, Finset.mul_sum,
                        ← Finset.sum_add_distrib]
                      apply Finset.sum_congr rfl
                      intro i _
                      ring
            _ = _ := by rw [weight_normalized]; ring
    _ ≤ 8 * Real.sqrt 2 * Real.sqrt (32 * η) + δ := by
          gcongr
    _ = 64 * Real.sqrt η + δ := by
          rw [unconditionalLiterature_sqrt_two_mul_sqrt_thirtytwo]


-- @@ L5909-5909 verbatim
end


-- @@ L5911-5911 verbatim
section


-- @@ L5913-5913 verbatim
open WithLp

-- @@ L5914-5914 verbatim
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


-- @@ L5916-5927 verbatim
/--
The total probability mass of DSV density rational public multiscale first hit physical flag
mismatch.
-/
def dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass
    {A C : Type*} [Fintype A] [Fintype C] {L : ℕ}
    (alice : A → Fin (L + 1))
    (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C)) : ℝ :=
  ∑ a : A, ∑ b : C,
    ‖z (a, b)‖ ^ 2 *
      if alice a = bob b then (0 : ℝ) else 1


-- @@ L5929-5945 verbatim
theorem
    dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass_nonneg
    {A C : Type*} [Fintype A] [Fintype C] {L : ℕ}
    (alice : A → Fin (L + 1))
    (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C)) :
    0 ≤
      dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass
        alice bob z := by
  classical
  unfold
    dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> positivity


-- @@ L5947-5947 verbatim
end


-- @@ L5949-5949 verbatim
section


-- @@ L5951-5951 verbatim
open WithLp

-- @@ L5952-5952 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder


-- @@ L5954-5954 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L5956-6011 verbatim
theorem dSVDensityRationalHeterogeneousActualPhysicalState_apply
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ (a, b) =
      ∑ x : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L,
        ∑ y : DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
          (dSVDensityRationalHeterogeneousActualAliceUnitary
              N width schedule ξ :
            Matrix
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L)
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L) ℂ) a x *
          (dSVDensityRationalHeterogeneousActualBobUnitary
              N width schedule ζ :
            Matrix
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L)
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L) ℂ) b y *
          dSVUniformDensityThresholdWholeHistorySharedState
            N d L (x, y) := by
  classical
  unfold dSVDensityRationalHeterogeneousActualPhysicalState
  change
    (∑ q :
      DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L,
      ((dSVDensityRationalHeterogeneousActualAliceUnitary
            N width schedule ξ :
          Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) ⊗ₖ
        (dSVDensityRationalHeterogeneousActualBobUnitary
            N width schedule ζ :
          Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ)) (a, b) q *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L q) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rfl


-- @@ L6013-6053 verbatim
theorem dSVDensityRationalHeterogeneousActualPhysicalState_apply_zeroFlag
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ (a, b) =
      ∑ x : DSVUniformDensityIndependentHistoryLocalIndex
          (L + 1) N d,
        ∑ y : DSVUniformDensityIndependentHistoryLocalIndex
            (L + 1) N d,
          (dSVDensityRationalHeterogeneousActualAliceUnitary
              N width schedule ξ :
            Matrix
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L)
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L) ℂ) a ⟨0, x⟩ *
          (dSVDensityRationalHeterogeneousActualBobUnitary
              N width schedule ζ :
            Matrix
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L)
              (DSVUniformDensityThresholdWholeHistoryLocalIndex
                N d L) ℂ) b ⟨0, y⟩ *
          dSVUniformDensityIndependentSharedState
            (L + 1) N d (x, y) := by
  classical
  have split_zero (p q : Prop) [Decidable p] [Decidable q]
      (v : ℂ) :
      (if p ∧ q then v else 0) =
        if p then (if q then v else 0) else 0 := by
    split_ifs <;> simp_all
  rw [dSVDensityRationalHeterogeneousActualPhysicalState_apply]
  simp only [Fintype.sum_sigma]
  simp_rw [dSVUniformDensityCompletePureHistory_zeroFlag_apply,
    mul_ite, mul_zero]
  simp_rw [split_zero]
  simp only [Fin.val_eq_zero_iff, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ,
    ↓reduceIte]


-- @@ L6055-6113 verbatim
theorem dSVDensityRationalHeterogeneousActualSpectralStopping_apply
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1))
    (history input : Fin (L + 1) → β) :
    ((dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
        accepted *
      dSVDensityRationalFirstAcceptActualTensorBasis
        (L := L) U :
      Matrix.unitaryGroup (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
        ⟨flag, history⟩ ⟨0, input⟩ =
      if flag =
        dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history
      then ∏ i : Fin (L + 1),
        (U : Matrix β β ℂ) (history i) (input i)
      else 0 := by
  classical
  let T := dSVDensityRationalFirstAcceptActualTensorBasis
    (L := L) U
  let W := dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
    accepted
  let v : (Fin (L + 1) → β) → ℂ := fun h =>
    ∏ i : Fin (L + 1), (U : Matrix β β ℂ) (h i) (input i)
  have spectral_column :
      (fun q : (Σ _ : Fin (L + 1), Fin (L + 1) → β) =>
        (T : Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
          q ⟨0, input⟩) =
      fun q => if q.1 = 0 then v q.2 else 0 := by
    funext q
    rcases q with ⟨stop, copies⟩
    change
      (controlledFiniteTensorLocalUnitary
          (fun (_ : Fin (L + 1)) (_ : Fin (L + 1)) => U) :
        Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
          ⟨stop, copies⟩ ⟨0, input⟩ =
        if stop = 0 then v copies else 0
    rw [controlledFiniteTensorLocalUnitary_apply]
  change
    (W : Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
      (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ).mulVec
      (fun q =>
        (T : Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
          q ⟨0, input⟩)
      ⟨flag, history⟩ =
      if flag =
        dSVDensityRationalHeterogeneousActualFirstAccepted
          accepted history
      then v history else 0
  rw [spectral_column]
  exact
    dSVDensityRationalHeterogeneousActualFirstAcceptUnitary_zeroFlag
      accepted v flag history


-- @@ L6115-6174 verbatim
theorem dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_apply
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1))
    (output input : Fin (L + 1) → β) :
    (dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
        accepted U :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
      ⟨flag, output⟩ ⟨0, input⟩ =
      ∑ history : Fin (L + 1) → β,
        (∏ i : Fin (L + 1),
          star ((U : Matrix β β ℂ) (history i) (output i))) *
        (if flag =
          dSVDensityRationalHeterogeneousActualFirstAccepted
            accepted history
        then ∏ i : Fin (L + 1),
          (U : Matrix β β ℂ) (history i) (input i)
        else 0) := by
  classical
  have restoration (other : Fin (L + 1))
      (history : Fin (L + 1) → β) :
      (((dSVDensityRationalFirstAcceptActualTensorBasis
          (L := L) U)⁻¹ :
          Matrix.unitaryGroup
            (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) :
        Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
        ⟨flag, output⟩ ⟨other, history⟩ =
        if flag = other then
          ∏ i : Fin (L + 1),
            star ((U : Matrix β β ℂ) (history i) (output i))
        else 0 := by
    exact dSVUniformDensityFirstAcceptControlledTensor_inv_apply
      (fun (_ : Fin (L + 1)) (_ : Fin (L + 1)) => U)
      flag other output history
  unfold dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
  rw [mul_assoc]
  change
    ((((dSVDensityRationalFirstAcceptActualTensorBasis
          (L := L) U)⁻¹ :
        Matrix.unitaryGroup
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) :
        Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) *
      ((dSVDensityRationalHeterogeneousActualFirstAcceptUnitary
          accepted *
        dSVDensityRationalFirstAcceptActualTensorBasis
          (L := L) U :
        Matrix.unitaryGroup
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ) :
        Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
          (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ))
        ⟨flag, output⟩ ⟨0, input⟩ = _
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_comm]
  simp_rw [restoration,
    dSVDensityRationalHeterogeneousActualSpectralStopping_apply]
  simp only [RCLike.star_def, mul_ite, ite_mul, zero_mul, mul_zero, sum_ite_eq', mem_univ,
    ↓reduceIte]


-- @@ L6176-6200 verbatim
theorem
    dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_sourceProduct
    {β : Type*} [Fintype β] [DecidableEq β]
    {L : ℕ} (accepted : Fin L → β → Prop)
    (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1))
    (output input : Fin (L + 1) → β) :
    (dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
        accepted U :
      Matrix (Σ _ : Fin (L + 1), Fin (L + 1) → β)
        (Σ _ : Fin (L + 1), Fin (L + 1) → β) ℂ)
      ⟨flag, output⟩ ⟨0, input⟩ =
      ∏ i : Fin (L + 1),
        ∑ atom : β,
          star ((U : Matrix β β ℂ) atom (output i)) *
          (if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i atom
          then (U : Matrix β β ℂ) atom (input i)
          else 0) := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_apply]
  exact
    dSVDensityRationalHeterogeneousActualFirstAccepted_sourceProduct
      accepted flag
      (fun i atom => star ((U : Matrix β β ℂ) atom (output i)))
      (fun i atom => (U : Matrix β β ℂ) atom (input i))


-- @@ L6202-6214 verbatim
/-- The total probability mass of DSV density rational heterogeneous actual physical flag. -/
def dSVDensityRationalHeterogeneousActualPhysicalFlagMass
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (flagAlice flagBob : Fin (L + 1)) : ℝ :=
  ∑ alice : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d,
    ∑ bob : DSVUniformDensityIndependentHistoryLocalIndex
        (L + 1) N d,
      ‖dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ
          (⟨flagAlice, alice⟩, ⟨flagBob, bob⟩)‖ ^ 2


-- @@ L6216-6227 verbatim
/-- The total probability mass of DSV density rational heterogeneous actual asynchronous flag. -/
def dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass
    (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L => q.1)
    (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L => q.1)
    (dSVDensityRationalHeterogeneousActualPhysicalState
      N width schedule ξ ζ)


-- @@ L6229-6243 verbatim
theorem
    dSVDensityRationalHeterogeneousActualAsynchronousFlagMass_nonneg
    (N : ℕ) {S d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    0 ≤ dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
      N width schedule ξ ζ := by
  exact
    dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass_nonneg
      (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L => q.1)
      (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L => q.1)
      (dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ)


-- @@ L6245-6245 verbatim
end


-- @@ L6247-6247 verbatim
section


-- @@ L6249-6249 verbatim
open WithLp

-- @@ L6250-6250 verbatim
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


-- @@ L6252-6259 verbatim
theorem dSVDensityRationalCompleteStoppedOptionalLocalSchedule_before
    {L : ℕ} (j : Fin L) (i : Fin (L + 1))
    (earlier : i.val < j.val) :
    dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L j.succ i = some false := by
  have attempted : i.val < L := lt_trans earlier j.isLt
  simp only [dSVDensityRationalCompleteStoppedOptionalLocalSchedule, attempted, ↓reduceIte,
    Fin.succ_ne_zero, Fin.val_succ, Order.lt_add_one_iff, Order.add_one_le_iff, earlier]


-- @@ L6261-6270 verbatim
theorem dSVDensityRationalCompleteStoppedOptionalLocalSchedule_after
    {L : ℕ} (j : Fin L) (i : Fin (L + 1))
    (later : j.val < i.val) :
    dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L j.succ i = none := by
  have not_before : ¬ i.val < j.val := by omega
  have not_equal : i.val ≠ j.val := by omega
  simp only [dSVDensityRationalCompleteStoppedOptionalLocalSchedule, Fin.succ_ne_zero, ↓reduceIte,
    Fin.val_succ, Order.lt_add_one_iff, Order.add_one_le_iff, not_before,
    Nat.add_right_cancel_iff, not_equal, ite_self]


-- @@ L6272-6272 verbatim
end


-- @@ L6274-6274 verbatim
section


-- @@ L6276-6276 verbatim
open WithLp

-- @@ L6277-6277 verbatim
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


-- @@ L6279-6279 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L6281-6306 verbatim
theorem
    dSVDensityRationalFirstAcceptActualPredicateMask_eq_spectralMask
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) (outcome : Bool) :
    (Matrix.diagonal fun q :
        DSVUniformDensityThresholdLocalIndex N d =>
      if dSVDensityRationalProjectiveThresholdBin w N q.1
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues q.2) = outcome
      then (1 : ℂ) else 0) =
      dSVDensityRationalFirstAcceptLocalSpectralMask
        w N ξ outcome := by
  classical
  ext ⟨k, i⟩ ⟨l, j⟩
  by_cases flags : k = l
  · subst l
    by_cases atoms : i = j
    · subst j
      simp only [diagonal_apply_eq, dSVDensityRationalFirstAcceptLocalSpectralMask,
        blockDiagonal'_apply, ↓reduceDIte, cast_eq]
    · simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, atoms, and_false, not_false_eq_true,
        diagonal_apply_ne, dSVDensityRationalFirstAcceptLocalSpectralMask, blockDiagonal'_apply,
        ↓reduceDIte, cast_eq]
  · simp only [ne_eq, Sigma.mk.injEq, flags, heq_eq_eq, false_and, not_false_eq_true,
      diagonal_apply_ne, dSVDensityRationalFirstAcceptLocalSpectralMask, blockDiagonal'_apply,
      ↓reduceDIte]


-- @@ L6308-6338 verbatim
theorem dSVDensityRationalFirstAcceptActualOptionalOutcome_apply
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Option Bool)
    (alice bob : DSVUniformDensityThresholdLocalIndex N d) :
    dSVDensityRationalCompleteStoppedOptionalOutcome
        w N ξ ζ a b (alice, bob) =
      ∑ x : DSVUniformDensityThresholdLocalIndex N d,
        ∑ y : DSVUniformDensityThresholdLocalIndex N d,
          dSVDensityRationalCompleteStoppedOptionalLocalEffect
            w N ξ a alice x *
          (dSVDensityRationalCompleteStoppedOptionalLocalEffect
            w N ζ b).transpose bob y *
          dSVUniformDensityThresholdSharedState N d (x, y) := by
  classical
  unfold dSVDensityRationalCompleteStoppedOptionalOutcome
  change
    (∑ q :
      DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d,
      (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ξ a ⊗ₖ
        (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          w N ζ b).transpose) (alice, bob) q *
        dSVUniformDensityThresholdSharedState N d q) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rfl


-- @@ L6340-6340 verbatim
end


-- @@ L6342-6342 verbatim
section


-- @@ L6344-6344 verbatim
open WithLp

-- @@ L6345-6345 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder


-- @@ L6347-6347 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L6349-6356 verbatim
/--
The DSV density rational heterogeneous actual physical flag born copy width construction used in
the quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
    {S L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (i : Fin (L + 1)) : ℝ :=
  if active : i.val < L then width (schedule ⟨i.val, active⟩) else 0


-- @@ L6358-6366 verbatim
private def dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
    {β : Type*} [Fintype β] [DecidableEq β] {L : ℕ}
    (accepted : Fin L → β → Prop) (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1)) (i : Fin (L + 1)) : Matrix β β ℂ :=
  fun output input =>
    ∑ atom : β, star ((U : Matrix β β ℂ) atom output) *
      (if dSVDensityRationalHeterogeneousActualCopyCondition
          accepted flag i atom
       then (U : Matrix β β ℂ) atom input else 0)


-- @@ L6368-6384 verbatim
private theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix_eq_spectralMask
    {β : Type*} [Fintype β] [DecidableEq β] {L : ℕ}
    (accepted : Fin L → β → Prop) (U : Matrix.unitaryGroup β ℂ)
    (flag : Fin (L + 1)) (i : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
        accepted U flag i =
      (((U⁻¹ : Matrix.unitaryGroup β ℂ) : Matrix β β ℂ) *
        (Matrix.diagonal fun atom : β =>
          if dSVDensityRationalHeterogeneousActualCopyCondition
              accepted flag i atom then (1 : ℂ) else 0) *
        (U : Matrix β β ℂ)) := by
  classical
  ext output input
  simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix, RCLike.star_def,
    mul_ite, mul_zero, UnitaryGroup.inv_val, Matrix.mul_apply, star_apply, diagonal_apply,
    mul_one, sum_ite_eq', mem_univ, ↓reduceIte, ite_mul, zero_mul]


-- @@ L6386-6466 verbatim
theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyConditionMask
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (flag i : Fin (L + 1)) :
    (Matrix.diagonal fun q :
        DSVUniformDensityThresholdLocalIndex N d =>
      if dSVDensityRationalHeterogeneousActualCopyCondition
          (dSVDensityRationalHeterogeneousActualCopyAccepted
            width schedule ξ) flag i q
      then (1 : ℂ) else 0) =
      match
        dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L flag i with
      | none => 1
      | some outcome =>
        dSVDensityRationalFirstAcceptLocalSpectralMask
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ outcome := by
  classical
  by_cases active : i.val < L
  · induction flag using Fin.cases with
    | zero =>
        rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_zero,
          ite_eq_left active]
        simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth,
          dite_eq_left active]
        rw [← dSVDensityRationalFirstAcceptActualPredicateMask_eq_spectralMask
          (width (schedule ⟨i.val, active⟩)) N ξ false]
        congr 1
        funext q
        cases h : dSVDensityRationalProjectiveThresholdBin
            (width (schedule ⟨i.val, active⟩)) N q.1
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues q.2) <;>
          simp [dSVDensityRationalHeterogeneousActualCopyCondition,
            dSVDensityRationalHeterogeneousActualCopyAccepted,
            dSVDensityRationalCompletePhysicalStoppingCopyAccepted,
            active, h]
    | succ j =>
        rcases lt_trichotomy i.val j.val with earlier | equal | later
        · rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_before
            j i earlier]
          simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth,
            dite_eq_left active]
          rw [← dSVDensityRationalFirstAcceptActualPredicateMask_eq_spectralMask
            (width (schedule ⟨i.val, active⟩)) N ξ false]
          congr 1
          funext q
          cases h : dSVDensityRationalProjectiveThresholdBin
              (width (schedule ⟨i.val, active⟩)) N q.1
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues q.2) <;>
            simp [dSVDensityRationalHeterogeneousActualCopyCondition,
              dSVDensityRationalHeterogeneousActualCopyAccepted,
              dSVDensityRationalCompletePhysicalStoppingCopyAccepted,
              active, earlier, Fin.succ_ne_zero, h]
        · have selected : i = j.castSucc := Fin.ext equal
          subst i
          rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_hit]
          simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth,
            dite_eq_left active]
          have selectedIndex : (⟨j.castSucc.val, active⟩ : Fin L) = j :=
            Fin.ext rfl
          rw [selectedIndex]
          rw [← dSVDensityRationalFirstAcceptActualPredicateMask_eq_spectralMask
            (width (schedule j)) N ξ true]
          congr 1
          funext q
          simp only [dSVDensityRationalHeterogeneousActualCopyCondition, Fin.val_castSucc, j.isLt,
            ↓reduceDIte, Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ, lt_self_iff_false,
            dSVDensityRationalHeterogeneousActualCopyAccepted,
            dSVDensityRationalCompletePhysicalStoppingCopyAccepted, Fin.eta]
        · rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_after
            j i later]
          simp only [dSVDensityRationalHeterogeneousActualCopyCondition, active, ↓reduceDIte,
            Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ, Order.lt_add_one_iff,
            Order.add_one_le_iff, show ¬i.val < j.val by omega, Nat.add_right_cancel_iff,
            show i.val ≠ j.val by omega, diagonal_one]
  · simp only [dSVDensityRationalHeterogeneousActualCopyCondition, active, ↓reduceDIte,
      ↓reduceIte, diagonal_one, dSVDensityRationalCompleteStoppedOptionalLocalSchedule]


-- @@ L6468-6493 verbatim
private theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornAliceCopy_eq_optionalEffect
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (flag i : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
        (dSVDensityRationalHeterogeneousActualCopyAccepted
          width schedule ξ)
        (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ)
        flag i =
      dSVDensityRationalCompleteStoppedOptionalLocalEffect
        (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
          width schedule i) N ξ
        (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L flag i) := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix_eq_spectralMask,
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyConditionMask]
  cases h : dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L flag i with
  | none => simp [dSVDensityRationalCompleteStoppedOptionalLocalEffect]
  | some outcome =>
      simpa only [UnitaryGroup.inv_val, dSVDensityRationalCompleteStoppedOptionalLocalEffect]
        using
          (dSVDensityRationalFirstAcceptPhysicalEffect_eq_spectralMask
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ξ outcome).symm


-- @@ L6495-6524 verbatim
private theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornBobCopy_eq_optionalEffect
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d)
    (flag i : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
        (dSVDensityRationalHeterogeneousActualCopyAccepted
          width schedule ζ)
        ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹)
        flag i =
      (dSVDensityRationalCompleteStoppedOptionalLocalEffect
        (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
          width schedule i) N ζ
        (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L flag i)).transpose := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix_eq_spectralMask,
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyConditionMask]
  cases h : dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L flag i with
  | none => simp [dSVDensityRationalCompleteStoppedOptionalLocalEffect]
  | some outcome =>
      change
        _ = (transposePOVM
          (dSVDensityRationalCompleteProjectiveBinaryPOVM
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ζ)).effect outcome
      simpa only [inv_inv] using
        (dSVDensityRationalFirstAcceptPhysicalBobEffect_eq_spectralMask
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ζ outcome).symm


-- @@ L6526-6562 verbatim
theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornAlice_sourceProduct
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) (flag : Fin (L + 1))
    (output input : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d) :
    (dSVDensityRationalHeterogeneousActualAliceUnitary
        N width schedule ξ :
      Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
        (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ℂ)
        ⟨flag, output⟩ ⟨0, input⟩ =
      ∏ i : Fin (L + 1),
        dSVDensityRationalCompleteStoppedOptionalLocalEffect
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flag i) (output i) (input i) := by
  change
    (dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
      (dSVDensityRationalHeterogeneousActualCopyAccepted
        width schedule ξ)
      (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ) :
      Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
        (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ℂ)
      ⟨flag, output⟩ ⟨0, input⟩ = _
  rw [dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_sourceProduct]
  apply Finset.prod_congr rfl
  intro i _
  change
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
      (dSVDensityRationalHeterogeneousActualCopyAccepted
        width schedule ξ)
      (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ)
      flag i (output i) (input i) = _
  exact congrArg (fun M => M (output i) (input i))
    (dSVDensityRationalHeterogeneousActualPhysicalFlagBornAliceCopy_eq_optionalEffect
      width schedule ξ flag i)


-- @@ L6564-6600 verbatim
theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornBob_sourceProduct
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d) (flag : Fin (L + 1))
    (output input : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d) :
    (dSVDensityRationalHeterogeneousActualBobUnitary
        N width schedule ζ :
      Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
        (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ℂ)
        ⟨flag, output⟩ ⟨0, input⟩ =
      ∏ i : Fin (L + 1),
        (dSVDensityRationalCompleteStoppedOptionalLocalEffect
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ζ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flag i)).transpose (output i) (input i) := by
  change
    (dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary
      (dSVDensityRationalHeterogeneousActualCopyAccepted
        width schedule ζ)
      ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹) :
      Matrix (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
        (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ℂ)
      ⟨flag, output⟩ ⟨0, input⟩ = _
  rw [dSVDensityRationalHeterogeneousActualPhysicalLocalUnitary_sourceProduct]
  apply Finset.prod_congr rfl
  intro i _
  change
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyMatrix
      (dSVDensityRationalHeterogeneousActualCopyAccepted
        width schedule ζ)
      ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹)
      flag i (output i) (input i) = _
  exact congrArg (fun M => M (output i) (input i))
    (dSVDensityRationalHeterogeneousActualPhysicalFlagBornBobCopy_eq_optionalEffect
      width schedule ζ flag i)


-- @@ L6602-6664 verbatim
theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornState_allFlags
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (flagAlice flagBob : Fin (L + 1))
    (alice bob : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ
        (⟨flagAlice, alice⟩, ⟨flagBob, bob⟩) =
      ∏ i : Fin (L + 1),
        dSVDensityRationalCompleteStoppedOptionalOutcome
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ ζ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagAlice i)
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagBob i) (alice i, bob i) := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalState_apply_zeroFlag]
  simp_rw [dSVUniformDensityIndependentSharedState_apply,
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornAlice_sourceProduct,
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornBob_sourceProduct]
  calc
    _ = ∏ i : Fin (L + 1),
          ∑ x : DSVUniformDensityThresholdLocalIndex N d,
            ∑ y : DSVUniformDensityThresholdLocalIndex N d,
              dSVDensityRationalCompleteStoppedOptionalLocalEffect
                  (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
                    width schedule i) N ξ
                  (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
                    L flagAlice i) (alice i) x *
                (dSVDensityRationalCompleteStoppedOptionalLocalEffect
                  (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
                    width schedule i) N ζ
                  (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
                    L flagBob i)).transpose (bob i) y *
                dSVUniformDensityThresholdSharedState N d (x, y) :=
      dSVUniformDensityPhysicalMatched_doubleTensorSourceFactor
        (fun i =>
          dSVDensityRationalCompleteStoppedOptionalLocalEffect
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ξ
            (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
              L flagAlice i))
        (fun i =>
          (dSVDensityRationalCompleteStoppedOptionalLocalEffect
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ζ
            (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
              L flagBob i)).transpose)
        (dSVUniformDensityThresholdSharedState N d)
        alice bob
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        (dSVDensityRationalFirstAcceptActualOptionalOutcome_apply
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ ζ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagAlice i)
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagBob i) (alice i) (bob i)).symm


-- @@ L6666-6666 verbatim
end


-- @@ L6668-6668 verbatim
section


-- @@ L6670-6670 verbatim
open WithLp

-- @@ L6671-6671 verbatim
open scoped BigOperators ComplexOrder Kronecker MatrixOrder


-- @@ L6673-6804 verbatim
theorem dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply
    (B N d L m : ℕ)
    (U V : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    localUnitaryAction
      (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
        B N d L m
        (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
          B U))
      (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
        B N d L m
        (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
          B V))
      (dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
          B N d L m ((φ, a), i),
       dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
          B N d L m ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
      (∑ x : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L,
        ∑ y : DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
          (U : Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) a x *
          (V : Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) b y *
          dSVUniformDensityThresholdWholeHistorySharedState
            N d L (x, y)) *
      embezzlementState m (i, j) := by
  classical
  let H := DSVUniformDensityThresholdWholeHistoryLocalIndex
    N d L
  let P := DSVDensityRationalPublicLogPhaseHistoryLocalIndex
    B N d L
  let n := dSVDensityRationalPublicLogPhaseResidual B N d L m
  let e := dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
    B N d L m
  let A := dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    B N d L m
    (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      B U)
  let D := dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    B N d L m
    (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      B V)
  let source := dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
    B N d L m
  have left (χ : Fin B) (x : H) (k : Fin m) :
      (A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ)
        (e ((φ, a), i)) (e ((χ, x), k)) =
        if i = k then
          if φ = χ then (U : Matrix H H ℂ) a x else 0
        else 0 := by
    rw [dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply,
      dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary_apply]
  have right (χ : Fin B) (x : H) (k : Fin m) :
      (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ)
        (e ((ψ, b), j)) (e ((χ, x), k)) =
        if j = k then
          if ψ = χ then (V : Matrix H H ℂ) b x else 0
        else 0 := by
    rw [dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift_apply,
      dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary_apply]
  have resource (χ υ : Fin B) (x y : H) (k l : Fin m) :
      source (e ((χ, x), k), e ((υ, y), l)) =
        (if χ = υ then
          (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
        else 0) *
          dSVUniformDensityThresholdWholeHistorySharedState
            N d L (x, y) *
          embezzlementState m (k, l) :=
    dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
      B N d L m χ υ x y k l
  change
    (∑ q : Fin (d * n) × Fin (d * n),
      ((A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) ⊗ₖ
        (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ))
          (e ((φ, a), i), e ((ψ, b), j)) q * source q) = _
  calc
    _ =
      ∑ q : (P × Fin m) × (P × Fin m),
        ((A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) ⊗ₖ
          (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ))
          (e ((φ, a), i), e ((ψ, b), j)) (e q.1, e q.2) *
          source (e q.1, e q.2) :=
      (Equiv.sum_comp (Equiv.prodCongr e e)
        (fun q : Fin (d * n) × Fin (d * n) =>
          ((A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) ⊗ₖ
            (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ))
            (e ((φ, a), i), e ((ψ, b), j)) q *
            source q)).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
      dsimp only [P, DSVDensityRationalPublicLogPhaseHistoryLocalIndex]
      simp only [Fintype.sum_prod_type]
      change
        (∑ χ : Fin B,
          ∑ x : H,
            ∑ k : Fin m,
              ∑ υ : Fin B,
                ∑ y : H,
                  ∑ l : Fin m,
                    (A : Matrix (Fin (d * n)) (Fin (d * n)) ℂ)
                        (e ((φ, a), i)) (e ((χ, x), k)) *
                      (D : Matrix (Fin (d * n)) (Fin (d * n)) ℂ)
                        (e ((ψ, b), j)) (e ((υ, y), l)) *
                      source (e ((χ, x), k), e ((υ, y), l))) = _
      simp_rw [left, right, resource]
      simp only [mul_ite, ite_mul, zero_mul, mul_zero, ofReal_inv, mul_assoc, sum_ite_irrel,
        sum_ite_eq, mem_univ, ↓reduceIte, sum_const_zero, sum_mul]
      split_ifs
      · simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      · rfl


-- @@ L6806-6824 verbatim
/--
The DSV density rational heterogeneous target first spectral alice construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ :=
  dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m
    (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualAliceUnitary
        N width schedule ξ))


-- @@ L6826-6844 verbatim
/--
The DSV density rational heterogeneous target first spectral bob construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousTargetFirstSpectralBob
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ :=
  dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
    (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m
    (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualBobUnitary
        N width schedule ζ))


-- @@ L6846-6864 verbatim
/-- The source object for DSV density rational heterogeneous target first spectral physical. -/
def dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m) ×
       Fin (d *
         dSVDensityRationalPublicMultiscalePhaseResidual
           S B N d L m)) :=
  localUnitaryAction
    (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
      S B N d L m width schedule ξ)
    (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
      S B N d L m width schedule ζ)
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
      S B N d L m)


-- @@ L6866-6902 verbatim
theorem
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource_apply
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhase S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m
            (((Fintype.equivFin
                (DSVDensityRationalPublicMultiscalePhase S B)) φ,
              a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m
            (((Fintype.equivFin
                (DSVDensityRationalPublicMultiscalePhase S B)) ψ,
              b), j)) =
      (if φ = ψ then
        (((Real.sqrt ((B ^ S : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  unfold
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
    dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
    dSVDensityRationalHeterogeneousTargetFirstSpectralBob
    dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
    dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
    dSVDensityRationalPublicMultiscalePhaseResidual
  rw [dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply]
  rw [← dSVDensityRationalHeterogeneousActualPhysicalState_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq, Fintype.card_pi, Fintype.card_fin, prod_const,
    card_univ, Nat.cast_pow, ofReal_inv, ite_mul, zero_mul]


-- @@ L6904-6904 verbatim
end


-- @@ L6906-6906 verbatim
section


-- @@ L6908-6908 verbatim
open WithLp

-- @@ L6909-6909 verbatim
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


-- @@ L6911-6918 verbatim
/--
The finite equivalence encoding DSV density rational public bucket coherent phase sigma product.
-/
def dSVDensityRationalPublicBucketCoherentPhaseSigmaProductEquiv
    {H : Type*} (B m : ℕ) :
    (Σ _ : Fin B × H, Fin m) ≃
      (Fin B × H) × Fin m :=
  Equiv.sigmaEquivProd (Fin B × H) (Fin m)


-- @@ L6920-6936 verbatim
/-- The quantum state representing DSV density rational public multiscale bucket coherent sigma. -/
def dSVDensityRationalPublicMultiscaleBucketCoherentSigmaState
    {H : Type*} {m : ℕ} (S B : ℕ)
    (history : EuclideanSpace ℂ (H × H))
    (work : DSVDensityRationalPublicMultiscalePhaseIndex S B →
      H → H → EuclideanSpace ℂ (Fin m × Fin m)) :
    EuclideanSpace ℂ
      ((Σ _ :
          DSVDensityRationalPublicMultiscalePhaseIndex S B × H,
          Fin m) ×
       (Σ _ :
          DSVDensityRationalPublicMultiscalePhaseIndex S B × H,
          Fin m)) :=
  dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    (Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B))
    history work


-- @@ L6938-6962 verbatim
/-- The quantum state representing DSV density rational heterogeneous pure stopped sigma. -/
def dSVDensityRationalHeterogeneousPureStoppedSigmaState
    {S B N d L m : ℕ}
    (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (work :
      DSVDensityRationalPublicMultiscalePhaseIndex S B →
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L →
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L →
          EuclideanSpace ℂ (Fin m × Fin m)) :
    EuclideanSpace ℂ
      ((Σ _ :
        DSVDensityRationalPublicMultiscalePhaseIndex S B ×
          DSVUniformDensityThresholdWholeHistoryLocalIndex N d L,
        Fin m) ×
       (Σ _ :
        DSVDensityRationalPublicMultiscalePhaseIndex S B ×
          DSVUniformDensityThresholdWholeHistoryLocalIndex N d L,
        Fin m)) :=
  dSVDensityRationalPublicMultiscaleBucketCoherentSigmaState
    S B
    (dSVDensityRationalHeterogeneousActualPhysicalState
      N width schedule ξ ζ)
    work


-- @@ L6964-6975 verbatim
/--
The DSV density rational mixed canonical prefix pure harmonic tensor construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
    {N : ℕ} (n : ℕ)
    (z : EuclideanSpace ℂ (Fin N × Fin N)) :
    EuclideanSpace ℂ (Fin (N * n) × Fin (N * n)) :=
  toLp 2 fun q : Fin (N * n) × Fin (N * n) =>
    let a : Fin N × Fin n := finProdFinEquiv.symm q.1
    let b : Fin N × Fin n := finProdFinEquiv.symm q.2
    z (a.1, b.1) * embezzlementState n (a.2, b.2)


-- @@ L6977-6983 verbatim
theorem
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_unit
    {N n : ℕ} (z : BipartiteUnitVector N) :
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n z.val =
      tensorEmbezzlementTarget (n := n) z := by
  rfl


-- @@ L6985-7014 verbatim
theorem
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_sub
    {N : ℕ} (n : ℕ)
    (x y : EuclideanSpace ℂ (Fin N × Fin N)) :
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n (x - y) =
      dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n x -
        dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n y := by
  ext q
  change
    (x ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1) -
      y ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1)) *
        embezzlementState n
          ((finProdFinEquiv.symm q.1).2,
            (finProdFinEquiv.symm q.2).2) =
      x ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1) *
        embezzlementState n
          ((finProdFinEquiv.symm q.1).2,
            (finProdFinEquiv.symm q.2).2) -
      y ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1) *
        embezzlementState n
          ((finProdFinEquiv.symm q.1).2,
            (finProdFinEquiv.symm q.2).2)
  ring


-- @@ L7016-7070 verbatim
theorem
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_norm_sq
    {N n : ℕ} (positive : 0 < n)
    (z : EuclideanSpace ℂ (Fin N × Fin N)) :
    ‖dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
      n z‖ ^ 2 = ‖z‖ ^ 2 := by
  classical
  let e : ((Fin N × Fin N) × (Fin n × Fin n)) ≃
      (Fin (N * n) × Fin (N * n)) :=
    (Equiv.prodProdProdComm (Fin N) (Fin N) (Fin n) (Fin n)).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  have point (q : (Fin N × Fin N) × (Fin n × Fin n)) :
      dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n z (e q) =
        z q.1 * embezzlementState n q.2 := by
    rcases q with ⟨⟨a, b⟩, ⟨i, j⟩⟩
    change
      z ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).1,
          (finProdFinEquiv.symm (finProdFinEquiv (b, j))).1) *
        embezzlementState n
          ((finProdFinEquiv.symm (finProdFinEquiv (a, i))).2,
            (finProdFinEquiv.symm (finProdFinEquiv (b, j))).2) =
      z (a, b) * embezzlementState n (i, j)
    simp only [Equiv.symm_apply_apply]
  rw [EuclideanSpace.norm_sq_eq]
  calc
    (∑ q : Fin (N * n) × Fin (N * n),
        ‖dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n z q‖ ^ 2) =
      ∑ q : (Fin N × Fin N) × (Fin n × Fin n),
        ‖dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n z (e q)‖ ^ 2 :=
        (Equiv.sum_comp e
          (fun q : Fin (N * n) × Fin (N * n) =>
            ‖dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
              n z q‖ ^ 2)).symm
    _ = ∑ q : (Fin N × Fin N) × (Fin n × Fin n),
          ‖z q.1 * embezzlementState n q.2‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _
          rw [point q]
    _ = (∑ a : Fin N × Fin N, ‖z a‖ ^ 2) *
          (∑ b : Fin n × Fin n,
            ‖embezzlementState n b‖ ^ 2) := by
          rw [Fintype.sum_prod_type]
          simp_rw [norm_mul, mul_pow]
          exact (Fintype.sum_mul_sum
            (fun a : Fin N × Fin N => ‖z a‖ ^ 2)
            (fun b : Fin n × Fin n =>
              ‖embezzlementState n b‖ ^ 2)).symm
    _ = ‖z‖ ^ 2 := by
          rw [← EuclideanSpace.norm_sq_eq,
            ← EuclideanSpace.norm_sq_eq,
            embezzlementState_norm n positive]
          ring


-- @@ L7072-7084 verbatim
theorem
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_prefix_sub_norm_sq
    {N n : ℕ} (positive : 0 < n)
    (r s : Fin (N + 1)) :
    ‖dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n (dSVCanonicalFailurePrefix r) -
        dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
          n (dSVCanonicalFailurePrefix s)‖ ^ 2 =
      |(r.val : ℝ) - (s.val : ℝ)| := by
  rw [← dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_sub,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_norm_sq
      positive,
    dSVCanonicalFailurePrefix_sub_norm_sq]


-- @@ L7086-7101 verbatim
/--
The quantum state representing DSV density rational mixed canonical prefix physical accepted
sigma.
-/
def dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState
    {d N : ℕ} (w : ℝ) (n : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      ((Σ _ : Fin d, Fin (N * n)) ×
        (Σ _ : Fin d, Fin (N * n))) :=
  dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    (dSVDensityRationalLocalSpectralPairHistory N ξ ζ)
    (fun i j =>
      dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
          w N ξ ζ i j))


-- @@ L7103-7121 verbatim
theorem
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq
    {H : Type*} [Fintype H] {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history work‖ ^ 2 =
      ∑ i : H, ∑ j : H,
        ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2 := by
  have zero :
      dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
          history (fun _ _ => (0 : EuclideanSpace ℂ (Fin n × Fin n))) =
        0 := by
    ext q
    simp only [dSVUniformDensityCorrectedMatchedSigmaWeightedResidual, PiLp.zero_apply, mul_zero]
  have distance :=
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual_distance_sq
      history work (fun _ _ => (0 : EuclideanSpace ℂ (Fin n × Fin n)))
  simpa only [zero, sub_zero] using distance


-- @@ L7123-7147 verbatim
theorem
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_norm_sq
    {d N n : ℕ} {w : ℝ} (width : 0 < w)
    (grid : 0 < N) (residual : 0 < n)
    (ξ ζ : BipartiteUnitVector d) :
    ‖dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState
        (N := N) w n ξ ζ‖ ^ 2 =
      ‖dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ true true‖ ^ 2 := by
  unfold dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq]
  simp_rw [
    dSVDensityRationalLocalSpectralPairHistory_apply_norm_sq,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_norm_sq
      residual,
    dSVDensityRationalPhysicalMixedAcceptedPrefixWork_norm_sq]
  rw [dSVDensityRationalMixedAcceptedPrefix_norm_sq
    width grid ξ ζ]
  unfold dSVDensityRationalPrefixHarmonicSpectralOverlap
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


-- @@ L7149-7149 verbatim
end


-- @@ L7151-7151 verbatim
end QuantumParallelRepetition


-- @@ L7153-7153 verbatim
end
