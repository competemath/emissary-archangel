/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingTerm


-- @@ L10-18 verbatim
/-!
# Unbounded multi-index carry reduction (REF-18c2c4-L2c3d-4e)

The Dwork expansion ranges over all multi-indices `Fin f → ℕ`, not just
digit-bounded vectors.  This file supplies the purely combinatorial bridge
from those unbounded multi-indices to the existing digit-vector survivor
lemmas: cyclic base-`ℓ` carrying preserves the weighted value modulo
`ℓ ^ f - 1` and strictly lowers total weight until all entries are `< ℓ`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open scoped NumberField


-- @@ L26-26 verbatim
namespace BernoulliRegular


-- @@ L28-28 verbatim
namespace Furtwaengler


-- @@ L30-30 verbatim
universe u v w


-- @@ L32-32 verbatim
namespace MultiIndexCarry


-- @@ L34-36 verbatim
/-- Cyclic successor on `Fin f`.  The last index maps back to `0`. -/
def succCyclic {f : ℕ} (i : Fin f) : Fin f :=
  if h : (i : ℕ) + 1 < f then ⟨(i : ℕ) + 1, h⟩ else ⟨0, by omega⟩


-- @@ L38-43 verbatim
/-- One carry step: subtract `ℓ` at `i`, then add `1` at the cyclic
successor.  The second update is applied after the first, so the `f = 1`
case is handled uniformly. -/
def carryStep (ℓ : ℕ) {f : ℕ} (m : Fin f → ℕ) (i : Fin f) : Fin f → ℕ :=
  Function.update (Function.update m i (m i - ℓ)) (succCyclic i)
    (Function.update m i (m i - ℓ) (succCyclic i) + 1)


-- @@ L45-54 verbatim
/-- Updating a multi-index at `i` shifts its weight by the difference at `i`. -/
theorem multiIndexWeight_update_add_eq {f : ℕ}
    (m : Fin f → ℕ) (i : Fin f) (x : ℕ) :
    multiIndexWeight (Function.update m i x) + m i =
      multiIndexWeight m + x := by
  simp only [multiIndexWeight]
  rw [Finset.sum_update_of_mem (s := Finset.univ) (i := i) (f := m) (b := x)
    (by simp), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ m (Finset.mem_univ i)]
  omega


-- @@ L56-77 verbatim
/-- Updating a multi-index at `i` shifts its value by the difference at `i`, weighted
by `ℓ ^ i`. -/
theorem multiIndexValue_update_add_eq {ℓ f : ℕ}
    (m : Fin f → ℕ) (i : Fin f) (x : ℕ) :
    multiIndexValue ℓ (Function.update m i x) + m i * ℓ ^ (i : ℕ) =
      multiIndexValue ℓ m + x * ℓ ^ (i : ℕ) := by
  simp only [multiIndexValue]
  have hupdate :
      (fun j : Fin f => Function.update m i x j * ℓ ^ (j : ℕ)) =
        Function.update (fun j : Fin f => m j * ℓ ^ (j : ℕ)) i
          (x * ℓ ^ (i : ℕ)) := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
  rw [hupdate]
  rw [Finset.sum_update_of_mem (s := Finset.univ) (i := i)
    (f := fun j : Fin f => m j * ℓ ^ (j : ℕ)) (b := x * ℓ ^ (i : ℕ)) (by simp),
    Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ (fun j : Fin f => m j * ℓ ^ (j : ℕ)) (Finset.mem_univ i)]
  omega


-- @@ L79-100 verbatim
/-- The cyclic successor is multiplication by `ℓ` modulo `ℓ ^ f - 1` — the wrap-around
at the last index is exactly the relation `ℓ ^ f ≡ 1`. -/
theorem pow_succCyclic_modEq (ℓ : ℕ) (hℓ : 2 ≤ ℓ) {f : ℕ} (i : Fin f) :
    ℓ * ℓ ^ (i : ℕ) ≡ ℓ ^ (succCyclic i : ℕ) [MOD ℓ ^ f - 1] := by
  simp only [succCyclic]
  by_cases h : (i : ℕ) + 1 < f
  · rw [dif_pos h]
    rw [pow_succ, mul_comm]
  · rw [dif_neg h]
    have hi_eq : (i : ℕ) + 1 = f := by omega
    have hpow : ℓ * ℓ ^ (i : ℕ) = ℓ ^ f := by
      calc
        ℓ * ℓ ^ (i : ℕ) = ℓ ^ ((i : ℕ) + 1) := by
          rw [pow_succ, mul_comm]
        _ = ℓ ^ f := by rw [hi_eq]
    rw [hpow]
    change ℓ ^ f ≡ 1 [MOD ℓ ^ f - 1]
    have hpos : 0 < ℓ ^ f := Nat.pow_pos (a := ℓ) (n := f) (by omega)
    have hmod : (ℓ ^ f - 1) * 1 + 1 ≡ 1 [MOD ℓ ^ f - 1] :=
      Nat.ModEq.modulus_mul_add
    convert hmod using 1
    omega


-- @@ L102-115 verbatim
/-- A carry step trades `ℓ` units of weight at `i` for one unit at its successor. -/
theorem carryStep_weight_add_eq
    {ℓ f : ℕ} (m : Fin f → ℕ) (i : Fin f) (hi : ℓ ≤ m i) :
    multiIndexWeight (carryStep ℓ m i) + ℓ = multiIndexWeight m + 1 := by
  simp only [carryStep]
  set m₁ : Fin f → ℕ := Function.update m i (m i - ℓ)
  have h₁ : multiIndexWeight m₁ + m i = multiIndexWeight m + (m i - ℓ) := by
    simpa [m₁] using multiIndexWeight_update_add_eq m i (m i - ℓ)
  have h₂ :
      multiIndexWeight (Function.update m₁ (succCyclic i) (m₁ (succCyclic i) + 1)) +
          m₁ (succCyclic i) =
        multiIndexWeight m₁ + (m₁ (succCyclic i) + 1) := by
    simpa using multiIndexWeight_update_add_eq m₁ (succCyclic i) (m₁ (succCyclic i) + 1)
  omega


-- @@ L117-123 verbatim
/-- Hence, for `2 ≤ ℓ`, a carry step strictly decreases the weight — this is what makes
the carry recursion terminate. -/
theorem carryStep_weight_lt
    {ℓ f : ℕ} (hℓ : 2 ≤ ℓ) (m : Fin f → ℕ) (i : Fin f) (hi : ℓ ≤ m i) :
    multiIndexWeight (carryStep ℓ m i) < multiIndexWeight m := by
  have h := carryStep_weight_add_eq (ℓ := ℓ) m i hi
  omega


-- @@ L125-166 verbatim
/-- …while leaving the value unchanged modulo `ℓ ^ f - 1`. -/
theorem carryStep_value_modEq
    {ℓ f : ℕ} (hℓ : 2 ≤ ℓ) (m : Fin f → ℕ) (i : Fin f) (hi : ℓ ≤ m i) :
    multiIndexValue ℓ (carryStep ℓ m i) ≡ multiIndexValue ℓ m [MOD ℓ ^ f - 1] := by
  simp only [carryStep]
  set m₁ : Fin f → ℕ := Function.update m i (m i - ℓ)
  have h₁raw :
      multiIndexValue ℓ m₁ + m i * ℓ ^ (i : ℕ) =
        multiIndexValue ℓ m + (m i - ℓ) * ℓ ^ (i : ℕ) := by
    simpa [m₁] using multiIndexValue_update_add_eq (ℓ := ℓ) m i (m i - ℓ)
  have h₁ : multiIndexValue ℓ m =
      multiIndexValue ℓ m₁ + ℓ * ℓ ^ (i : ℕ) := by
    have hmi :
        (m i - ℓ) * ℓ ^ (i : ℕ) + ℓ * ℓ ^ (i : ℕ) =
          m i * ℓ ^ (i : ℕ) := by
      rw [← Nat.add_mul]
      have : m i - ℓ + ℓ = m i := Nat.sub_add_cancel hi
      rw [this]
    omega
  have h₂raw :
      multiIndexValue ℓ (Function.update m₁ (succCyclic i) (m₁ (succCyclic i) + 1)) +
          m₁ (succCyclic i) * ℓ ^ (succCyclic i : ℕ) =
        multiIndexValue ℓ m₁ +
          (m₁ (succCyclic i) + 1) * ℓ ^ (succCyclic i : ℕ) := by
    simpa using
      multiIndexValue_update_add_eq (ℓ := ℓ) m₁ (succCyclic i) (m₁ (succCyclic i) + 1)
  have h₂ :
      multiIndexValue ℓ (Function.update m₁ (succCyclic i) (m₁ (succCyclic i) + 1)) =
        multiIndexValue ℓ m₁ + ℓ ^ (succCyclic i : ℕ) := by
    have hms :
        (m₁ (succCyclic i) + 1) * ℓ ^ (succCyclic i : ℕ) =
          m₁ (succCyclic i) * ℓ ^ (succCyclic i : ℕ) +
            ℓ ^ (succCyclic i : ℕ) := by
      rw [Nat.add_mul, one_mul]
    rw [hms] at h₂raw
    omega
  calc
    multiIndexValue ℓ (Function.update m₁ (succCyclic i) (m₁ (succCyclic i) + 1))
        = multiIndexValue ℓ m₁ + ℓ ^ (succCyclic i : ℕ) := h₂
    _ ≡ multiIndexValue ℓ m₁ + ℓ * ℓ ^ (i : ℕ) [MOD ℓ ^ f - 1] :=
        Nat.ModEq.add_left (multiIndexValue ℓ m₁) (pow_succCyclic_modEq ℓ hℓ i).symm
    _ = multiIndexValue ℓ m := h₁.symm


-- @@ L168-213 verbatim
/-- Carry reduction produces a digit-bounded vector in the same residue
class modulo `ℓ ^ f - 1`, with no larger weight.  If the original
multi-index was not digit-bounded, the produced vector has strictly
smaller weight. -/
theorem exists_digitVec_modEq_of_multiIndex
    {ℓ f : ℕ} (hℓ : 2 ≤ ℓ) (m : Fin f → ℕ) :
    ∃ v : digitVec ℓ f,
      digitWeight v ≤ multiIndexWeight m ∧
      (¬ (∀ i, m i < ℓ) → digitWeight v < multiIndexWeight m) ∧
      digitValue v ≡ multiIndexValue ℓ m [MOD ℓ ^ f - 1] := by
  classical
  suffices hmain :
      ∀ W : ℕ, ∀ m : Fin f → ℕ, multiIndexWeight m = W →
        ∃ v : digitVec ℓ f,
          digitWeight v ≤ multiIndexWeight m ∧
          (¬ (∀ i, m i < ℓ) → digitWeight v < multiIndexWeight m) ∧
          digitValue v ≡ multiIndexValue ℓ m [MOD ℓ ^ f - 1] by
    exact hmain (multiIndexWeight m) m rfl
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ih =>
      intro m hmW
      by_cases hb : ∀ i, m i < ℓ
      · let v : digitVec ℓ f := ⟨m, hb⟩
        refine ⟨v, ?_, ?_, ?_⟩
        · rfl
        · intro hnot
          exact (hnot hb).elim
        · rfl
      · push Not at hb
        rcases hb with ⟨i, hi_not⟩
        have hi : ℓ ≤ m i := by omega
        set m' : Fin f → ℕ := carryStep ℓ m i
        have hlt : multiIndexWeight m' < W := by
          rw [← hmW]
          exact carryStep_weight_lt hℓ m i hi
        obtain ⟨v, hv_le, hv_strict, hv_mod⟩ := ih (multiIndexWeight m') hlt m' rfl
        refine ⟨v, ?_, ?_, ?_⟩
        · have hstep_lt : multiIndexWeight m' < multiIndexWeight m :=
            carryStep_weight_lt hℓ m i hi
          omega
        · intro _hnot
          have hstep_lt : multiIndexWeight m' < multiIndexWeight m :=
            carryStep_weight_lt hℓ m i hi
          omega
        · exact hv_mod.trans (by simpa [m'] using carryStep_value_modEq hℓ m i hi)


-- @@ L215-225 verbatim
/-- A digit vector congruent to a multi-index modulo `N` inherits its `N ∣ B + ·`
divisibility.  Setup-independent core of the two `…StickelbergerSetup` methods, with
the modulus `N` and arity `f` as plain arguments. -/
theorem multiIndex_divisibility_of_digitVec_modEq {ℓ f : ℕ} (N B : ℕ)
    {m : Fin f → ℕ} {v : digitVec ℓ f}
    (hmod : digitValue v ≡ multiIndexValue ℓ m [MOD N])
    (hdiv : N ∣ B + multiIndexValue ℓ m) :
    N ∣ B + digitValue v := by
  have h0 : B + multiIndexValue ℓ m ≡ 0 [MOD N] := (Nat.modEq_zero_iff_dvd).2 hdiv
  have hsum : B + digitValue v ≡ B + multiIndexValue ℓ m [MOD N] := Nat.ModEq.add_left B hmod
  exact (Nat.modEq_zero_iff_dvd).1 (hsum.trans h0)


-- @@ L227-227 verbatim
end MultiIndexCarry


-- @@ L229-229 verbatim
namespace TraceFormStickelbergerSetup


-- @@ L231-231 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L232-232 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L233-233 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L234-235 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']


-- @@ L237-237 verbatim
variable (S : TraceFormStickelbergerSetup ℓ p k K R')


-- @@ L239-246 verbatim
/-- A digit vector congruent to a multi-index modulo `#k - 1` inherits its
`(#k - 1) ∣ B + ·` divisibility. -/
theorem multiIndex_divisibility_of_digitVec_modEq
    (B : ℕ) {m : Fin S.f → ℕ} {v : digitVec ℓ S.f}
    (hmod : digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1])
    (hdiv : (Fintype.card k - 1) ∣ B + multiIndexValue ℓ m) :
    (Fintype.card k - 1) ∣ B + digitValue v :=
  MultiIndexCarry.multiIndex_divisibility_of_digitVec_modEq (Fintype.card k - 1) B hmod hdiv


-- @@ L248-267 verbatim
/-- No unbounded multi-index of weight below `S.stickOrd a` survives the
reciprocal residue-class divisibility test. -/
theorem no_survivor_multiIndex_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hm : multiIndexWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m) := by
  intro hdiv
  have hℓ : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  obtain ⟨v, hv_le, _, hv_mod⟩ :=
    MultiIndexCarry.exists_digitVec_modEq_of_multiIndex (ℓ := ℓ) hℓ m
  have hv_mod_card :
      digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1] := by
    simpa [S.card_k] using hv_mod
  have hdiv_v :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue v) :=
    S.multiIndex_divisibility_of_digitVec_modEq ((p - a) * S.stickD) hv_mod_card hdiv
  have hv_lt : digitWeight v < S.stickOrd a := lt_of_le_of_lt hv_le hm
  exact (S.no_survivor_of_weight_lt_stickOrd a ha₁ ha₂ v hv_lt) hdiv_v


-- @@ L269-307 verbatim
/-- At the leading weight, any surviving unbounded multi-index is already
digit-bounded and is the standard digit vector of `a * S.stickD`. -/
theorem unique_multiIndex_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hw : multiIndexWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m)) :
    multiIndexValue ℓ m = a * S.stickD ∧
      ∃ hm : ∀ i, m i < ℓ,
        (⟨m, hm⟩ : digitVec ℓ S.f) = S.standardDigitVec (a * S.stickD) := by
  have hℓ : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  obtain ⟨v, hv_le, hv_strict, hv_mod⟩ :=
    MultiIndexCarry.exists_digitVec_modEq_of_multiIndex (ℓ := ℓ) hℓ m
  have hv_mod_card :
      digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1] := by
    simpa [S.card_k] using hv_mod
  have hdiv_v :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue v) :=
    S.multiIndex_divisibility_of_digitVec_modEq ((p - a) * S.stickD) hv_mod_card hdiv
  have hv_not_lt : ¬ digitWeight v < S.stickOrd a := fun hv_lt =>
    (S.no_survivor_of_weight_lt_stickOrd a ha₁ ha₂ v hv_lt) hdiv_v
  have hm_bounded : ∀ i, m i < ℓ := by
    by_contra hnot
    have hv_lt_weight : digitWeight v < multiIndexWeight m := hv_strict hnot
    rw [hw] at hv_lt_weight
    exact hv_not_lt hv_lt_weight
  let dm : digitVec ℓ S.f := ⟨m, hm_bounded⟩
  have hdm_div :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue dm) := by
    simpa [dm, digitValue, multiIndexValue] using hdiv
  have hdm_wt : digitWeight dm = S.stickOrd a := by
    simpa [dm, digitWeight, multiIndexWeight] using hw
  have hdm_eq : dm = S.standardDigitVec (a * S.stickD) :=
    S.unique_survivor_at_stickOrd a ha₁ ha₂ dm hdm_wt hdm_div
  refine ⟨?_, hm_bounded, hdm_eq⟩
  change digitValue dm = a * S.stickD
  rw [hdm_eq]
  exact S.digitValue_standardDigitVec_eq a ha₁ ha₂


-- @@ L309-309 verbatim
end TraceFormStickelbergerSetup


-- @@ L311-311 verbatim
namespace ConductorFlexibleTraceFormStickelbergerSetup


-- @@ L313-313 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L314-314 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L315-315 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L316-316 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L318-318 verbatim
variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')


-- @@ L320-327 verbatim
/-- A digit vector congruent to a multi-index modulo `#k - 1` inherits its
`(#k - 1) ∣ B + ·` divisibility. -/
theorem multiIndex_divisibility_of_digitVec_modEq
    (B : ℕ) {m : Fin S.f → ℕ} {v : digitVec ℓ S.f}
    (hmod : digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1])
    (hdiv : (Fintype.card k - 1) ∣ B + multiIndexValue ℓ m) :
    (Fintype.card k - 1) ∣ B + digitValue v :=
  MultiIndexCarry.multiIndex_divisibility_of_digitVec_modEq (Fintype.card k - 1) B hmod hdiv


-- @@ L329-348 verbatim
/-- No unbounded multi-index of weight below `S.stickOrd a` survives the
conductor-flexible reciprocal residue-class divisibility test. -/
theorem no_survivor_multiIndex_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hm : multiIndexWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m) := by
  intro hdiv
  have hℓ : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  obtain ⟨v, hv_le, _, hv_mod⟩ :=
    MultiIndexCarry.exists_digitVec_modEq_of_multiIndex (ℓ := ℓ) hℓ m
  have hv_mod_card :
      digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1] := by
    simpa [S.card_k] using hv_mod
  have hdiv_v :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue v) :=
    S.multiIndex_divisibility_of_digitVec_modEq ((p - a) * S.stickD) hv_mod_card hdiv
  have hv_lt : digitWeight v < S.stickOrd a := lt_of_le_of_lt hv_le hm
  exact (S.no_survivor_of_weight_lt_stickOrd a ha₁ ha₂ v hv_lt) hdiv_v


-- @@ L350-389 verbatim
/-- At the leading weight, any surviving conductor-flexible unbounded
multi-index is already digit-bounded and is the standard digit vector of
`a * S.stickD`. -/
theorem unique_multiIndex_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hw : multiIndexWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m)) :
    multiIndexValue ℓ m = a * S.stickD ∧
      ∃ hm : ∀ i, m i < ℓ,
        (⟨m, hm⟩ : digitVec ℓ S.f) = S.standardDigitVec (a * S.stickD) := by
  have hℓ : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  obtain ⟨v, hv_le, hv_strict, hv_mod⟩ :=
    MultiIndexCarry.exists_digitVec_modEq_of_multiIndex (ℓ := ℓ) hℓ m
  have hv_mod_card :
      digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1] := by
    simpa [S.card_k] using hv_mod
  have hdiv_v :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue v) :=
    S.multiIndex_divisibility_of_digitVec_modEq ((p - a) * S.stickD) hv_mod_card hdiv
  have hv_not_lt : ¬ digitWeight v < S.stickOrd a := fun hv_lt =>
    (S.no_survivor_of_weight_lt_stickOrd a ha₁ ha₂ v hv_lt) hdiv_v
  have hm_bounded : ∀ i, m i < ℓ := by
    by_contra hnot
    have hv_lt_weight : digitWeight v < multiIndexWeight m := hv_strict hnot
    rw [hw] at hv_lt_weight
    exact hv_not_lt hv_lt_weight
  let dm : digitVec ℓ S.f := ⟨m, hm_bounded⟩
  have hdm_div :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue dm) := by
    simpa [dm, digitValue, multiIndexValue] using hdiv
  have hdm_wt : digitWeight dm = S.stickOrd a := by
    simpa [dm, digitWeight, multiIndexWeight] using hw
  have hdm_eq : dm = S.standardDigitVec (a * S.stickD) :=
    S.unique_survivor_at_stickOrd a ha₁ ha₂ dm hdm_wt hdm_div
  refine ⟨?_, hm_bounded, hdm_eq⟩
  change digitValue dm = a * S.stickD
  rw [hdm_eq]
  exact S.digitValue_standardDigitVec_eq a ha₁ ha₂


-- @@ L391-391 verbatim
end ConductorFlexibleTraceFormStickelbergerSetup


-- @@ L393-393 verbatim
namespace FullTeichStickelbergerSetup


-- @@ L395-395 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L396-396 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L397-397 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L398-399 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']


-- @@ L401-401 verbatim
variable (S : FullTeichStickelbergerSetup ℓ p k K R')


-- @@ L403-411 verbatim
/-- Full-Teich wrapper for unbounded multi-index no-survivor. -/
theorem no_survivor_multiIndex_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hm : multiIndexWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m) :=
  S.toTraceFormStickelbergerSetup.no_survivor_multiIndex_of_weight_lt_stickOrd
    a ha₁ ha₂ m hm


-- @@ L413-425 verbatim
/-- Full-Teich wrapper for uniqueness of the leading unbounded
multi-index survivor. -/
theorem unique_multiIndex_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hw : multiIndexWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m)) :
    multiIndexValue ℓ m = a * S.stickD ∧
      ∃ hm : ∀ i, m i < ℓ,
        (⟨m, hm⟩ : digitVec ℓ S.f) = S.standardDigitVec (a * S.stickD) :=
  S.toTraceFormStickelbergerSetup.unique_multiIndex_survivor_at_stickOrd
    a ha₁ ha₂ m hw hdiv


-- @@ L427-429 verbatim
/-- Bundle accessor for unbounded multi-indices of weight at most `N`. -/
def multiIndexLE (N : ℕ) : Finset (Fin S.f → ℕ) :=
  Furtwaengler.multiIndexLE S.f N


-- @@ L431-431 verbatim
end FullTeichStickelbergerSetup


-- @@ L433-433 verbatim
namespace ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L435-435 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L436-436 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L437-437 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L438-438 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L440-440 verbatim
variable (S : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')


-- @@ L442-451 verbatim
/-- Full-Teich wrapper for conductor-flexible unbounded multi-index
no-survivor. -/
theorem no_survivor_multiIndex_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hm : multiIndexWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m) :=
  S.toConductorFlexibleTraceFormStickelbergerSetup.no_survivor_multiIndex_of_weight_lt_stickOrd
    a ha₁ ha₂ m hm


-- @@ L453-465 verbatim
/-- Full-Teich wrapper for uniqueness of the conductor-flexible leading
unbounded multi-index survivor. -/
theorem unique_multiIndex_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hw : multiIndexWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m)) :
    multiIndexValue ℓ m = a * S.stickD ∧
      ∃ hm : ∀ i, m i < ℓ,
        (⟨m, hm⟩ : digitVec ℓ S.f) = S.standardDigitVec (a * S.stickD) :=
  S.toConductorFlexibleTraceFormStickelbergerSetup.unique_multiIndex_survivor_at_stickOrd
    a ha₁ ha₂ m hw hdiv


-- @@ L467-470 verbatim
/-- Bundle accessor for conductor-flexible unbounded multi-indices of weight
at most `N`. -/
def multiIndexLE (N : ℕ) : Finset (Fin S.f → ℕ) :=
  Furtwaengler.multiIndexLE S.f N


-- @@ L472-472 verbatim
end ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L474-474 verbatim
end Furtwaengler


-- @@ L476-476 verbatim
end BernoulliRegular
