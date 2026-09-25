/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

-- @@ L10-15 verbatim
/-!
# Basis of `LinSols`

We give a basis of vector space `LinSols`, and find the rank thereof.

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace PureU1


-- @@ L21-21 verbatim
open BigOperators Module


-- @@ L23-23 verbatim
variable {n : ℕ}

-- @@ L24-24 verbatim
namespace BasisLinear


-- @@ L26-34 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The basis elements as charges, defined to have a `1` in the `j`th position and a `-1` in the
last position. -/
def asCharges (j : Fin n) : (PureU1 n.succ).Charges :=
  (fun i =>
    if i = j.castSucc then 1
    else if i = Fin.last n then
        - 1
      else 0)


-- @@ L36-39 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma asCharges_eq_castSucc (j : Fin n) :
    asCharges j (Fin.castSucc j) = 1 := by
  simp [asCharges]


-- @@ L41-45 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma asCharges_ne_castSucc {k j : Fin n} (h : k ≠ j) :
    asCharges k ⟨j, by simp⟩= 0 := by
  simp [asCharges, Fin.ext_iff]
  grind


-- @@ L47-68 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The basis elements as `LinSols`. -/
@[simps!]
def asLinSols (j : Fin n) : (PureU1 n.succ).LinSols :=
  ⟨asCharges j, by
    intro i
    match i with
    | ⟨0, _⟩=>
    simp only [PureU1_linearACCs, accGrav,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_eq_single j]
    · simp only [asCharges, ↓reduceIte]
      have hn : ¬ (Fin.last n = Fin.castSucc j) := Fin.ne_of_gt j.prop
      split
      · rename_i ht
        exact (hn ht).elim
      · with_unfolding_all rfl
    · intro k _ hkj
      exact asCharges_ne_castSucc hkj.symm
    · intro hk
      simp at hk⟩


-- @@ L70-72 verbatim
lemma sum_of_vectors {n : ℕ} (f : Fin k → (PureU1 n).LinSols) (j : Fin n) :
    (∑ i : Fin k, (f i)).1 j = (∑ i : Fin k, (f i).1 j) :=
  sum_of_anomaly_free_linear (fun i => f i) j


-- @@ L74-112 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The coordinate map for the basis. -/
noncomputable
def coordinateMap : (PureU1 n.succ).LinSols ≃ₗ[ℚ] Fin n →₀ ℚ where
  toFun S := (Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin n)).symm (S.1 ∘ Fin.castSucc)
  map_add' S T := by
    rw [← map_add]
    rfl
  map_smul' a S := by
    rw [← map_smul]
    rfl
  invFun f := ∑ i : Fin n, f i • asLinSols i
  left_inv S := by
    simp only [Nat.succ_eq_add_one,
      Finsupp.linearEquivFunOnFinite_symm_apply, Function.comp_apply]
    apply pureU1_anomalyFree_ext
    intro j
    rw [sum_of_vectors]
    simp only [HSMul.hSMul, SMul.smul, asLinSols_val]
    rw [Finset.sum_eq_single j]
    · simp only [asCharges, ↓reduceIte, mul_one]
    · intro k _ hkj
      erw [asCharges_ne_castSucc hkj]
      exact Rat.mul_zero (S.val k.castSucc)
    · simp
  right_inv f := by
    simp only
    ext
    rename_i j
    simp only [Nat.succ_eq_add_one, Finsupp.linearEquivFunOnFinite_symm_apply,
      Function.comp_apply]
    rw [sum_of_vectors]
    simp only [HSMul.hSMul, SMul.smul,asLinSols_val]
    rw [Finset.sum_eq_single j]
    · simp only [asCharges, ↓reduceIte, mul_one]
    · intro k _ hkj
      erw [asCharges_ne_castSucc hkj]
      exact Rat.mul_zero (f k)
    · simp


-- @@ L114-117 verbatim
/-- The basis of `LinSols`. -/
noncomputable
def asBasis : Basis (Fin n) ℚ ((PureU1 n.succ).LinSols) where
  repr := coordinateMap


-- @@ L119-121 verbatim
/-- The module over `ℚ` defined by linear solutions to the pure `U(1)` ACCs is finite. -/
instance : Module.Finite ℚ ((PureU1 n.succ).LinSols) :=
  Module.Finite.of_basis asBasis


-- @@ L123-129 verbatim
/-- The module of solutions to the linear pure-U(1) acc has rank equal to `n`. -/
lemma finrank_AnomalyFreeLinear :
    Module.finrank ℚ (((PureU1 n.succ).LinSols)) = n := by
  have h := Module.mk_finrank_eq_card_basis (@asBasis n)
  simp only [Nat.succ_eq_add_one, Module.finrank_eq_rank, Cardinal.mk_fintype,
    Fintype.card_fin] at h
  exact Module.finrank_eq_of_rank_eq h


-- @@ L131-131 verbatim
end BasisLinear


-- @@ L133-133 verbatim
end PureU1
