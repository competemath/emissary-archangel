/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.LinearAlgebra.InvariantSubmodule.Eigenbasis
import RepresentationTheory.Alignment.Attribute


-- @@ L11-15 verbatim
/-!
# Invariant submodules of exterior powers

Invariant submodules of exterior powers under all linear equivalences.
-/


-- @@ L17-17 verbatim
open scoped TensorProduct BigOperators

-- @@ L18-18 verbatim
open Module


-- @@ L20-20 verbatim
namespace RepresentationTheory.LinearAlgebra.ExteriorPower.InvariantSubmodules


-- @@ L22-23 verbatim
variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]


-- @@ L25-25 verbatim
section Reindex


-- @@ L27-32 verbatim
private lemma prod_over_orderEmb {α : Type*} [LinearOrder α] {s : Finset α} {m : ℕ}
    (h : s.card = m) (f : α → k) :
    ∏ i : Fin m, f (s.orderEmbOfFin h i) = ∏ j ∈ s, f j := by
  rw [← Finset.prod_coe_sort s f, ← Equiv.prod_comp (s.orderIsoOfFin h).toEquiv (fun x : s => f x)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [Finset.coe_orderIsoOfFin_apply]


-- @@ L34-34 verbatim
end Reindex


-- @@ L36-36 verbatim
section ExteriorBasis


-- @@ L38-38 verbatim
variable {d n : ℕ}


-- @@ L40-46 verbatim
private lemma map_exteriorBasis (bV : Basis (Fin d) k V) (g : V →ₗ[k] V)
    (S : Set.powersetCard (Fin d) n) :
    exteriorPower.map n g (bV.exteriorPower n S) =
      exteriorPower.ιMulti k n (fun i => g (bV (S.val.orderEmbOfFin S.prop i))) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti]
  refine congrArg _ (funext (fun i => ?_))
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]


-- @@ L48-48 verbatim
end ExteriorBasis


-- @@ L50-50 verbatim
section DiagonalWeights


-- @@ L52-52 verbatim
variable {d n : ℕ}


-- @@ L54-54 verbatim
private noncomputable def diagWeight [CharZero k] (i : Fin d) : k := (2 : k) ^ (2 ^ (i : ℕ))


-- @@ L56-57 verbatim
private lemma diagWeight_ne_zero [CharZero k] (i : Fin d) : diagWeight (k := k) i ≠ 0 :=
  pow_ne_zero _ (by norm_num)


-- @@ L59-60 verbatim
private noncomputable def diagUnit [CharZero k] (i : Fin d) : kˣ :=
  Units.mk0 (diagWeight i) (diagWeight_ne_zero i)


-- @@ L62-63 verbatim
private noncomputable def diagEig [CharZero k] (S : Set.powersetCard (Fin d) n) : k :=
  ∏ j ∈ S.val, diagWeight (k := k) j


-- @@ L65-85 verbatim
private lemma diagEig_injective [CharZero k] :
    Function.Injective (diagEig (k := k) (d := d) (n := n)) := by
  intro S T h
  have hexp : ∀ U : Set.powersetCard (Fin d) n,
      diagEig (k := k) U = (2 : k) ^ (∑ j ∈ U.val, 2 ^ (j : ℕ)) := by
    intro U
    rw [diagEig, ← Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hexp, hexp] at h
  have hnat : (((2 : ℕ) ^ (∑ j ∈ S.val, 2 ^ (j : ℕ)) : ℕ) : k)
      = (((2 : ℕ) ^ (∑ j ∈ T.val, 2 ^ (j : ℕ)) : ℕ) : k) := by push_cast; exact h
  have hpow : (2 : ℕ) ^ (∑ j ∈ S.val, 2 ^ (j : ℕ)) = (2 : ℕ) ^ (∑ j ∈ T.val, 2 ^ (j : ℕ)) :=
    Nat.cast_injective hnat
  have hsum : (∑ j ∈ S.val, 2 ^ (j : ℕ)) = ∑ j ∈ T.val, 2 ^ (j : ℕ) :=
    Nat.pow_right_injective (le_refl 2) hpow
  have hmap : (S.val.map Fin.valEmbedding) = (T.val.map Fin.valEmbedding) := by
    apply Finset.equivBitIndices.symm.injective
    change (∑ i ∈ S.val.map Fin.valEmbedding, 2 ^ i) = ∑ i ∈ T.val.map Fin.valEmbedding, 2 ^ i
    rw [Finset.sum_map, Finset.sum_map]
    exact hsum
  exact Subtype.ext (Finset.map_injective Fin.valEmbedding hmap)


-- @@ L87-87 verbatim
end DiagonalWeights


-- @@ L89-89 verbatim
section Permutation


-- @@ L91-91 verbatim
variable {d n : ℕ}


-- @@ L93-107 verbatim
private lemma exists_perm_orderEmb (S T : Set.powersetCard (Fin d) n) :
    ∃ σ : Equiv.Perm (Fin d), ∀ i : Fin n,
      σ (S.val.orderEmbOfFin S.prop i) = T.val.orderEmbOfFin T.prop i := by
  classical
  let φ : {x // x ∈ S.val} ≃ {x // x ∈ T.val} :=
    (S.val.orderIsoOfFin S.prop).symm.toEquiv.trans (T.val.orderIsoOfFin T.prop).toEquiv
  refine ⟨φ.extendSubtype, fun i => ?_⟩
  have hmem : S.val.orderEmbOfFin S.prop i ∈ S.val := S.val.orderEmbOfFin_mem S.prop i
  rw [Equiv.extendSubtype_apply_of_mem φ _ hmem]
  change ((T.val.orderIsoOfFin T.prop)
      ((S.val.orderIsoOfFin S.prop).symm ⟨_, hmem⟩) : Fin d) = T.val.orderEmbOfFin T.prop i
  have hSi : ((S.val.orderIsoOfFin S.prop).symm ⟨S.val.orderEmbOfFin S.prop i, hmem⟩) = i := by
    rw [OrderIso.symm_apply_eq]
    exact Subtype.ext (Finset.coe_orderIsoOfFin_apply S.val S.prop i)
  rw [hSi, Finset.coe_orderIsoOfFin_apply]


-- @@ L109-109 verbatim
end Permutation


-- @@ L111-153 verbatim
/-- A submodule of an exterior power stable under every linear equivalence is either zero or the whole space. -/
@[source_ref "Chapter4/Problem4.12.3" (role := primary)]
theorem eq_bot_or_eq_top_of_exteriorPower_invariant [CharZero k] [Module.Finite k V] {n : ℕ}
    (W : Submodule k (⋀[k]^n V))
    (hW : ∀ g : V ≃ₗ[k] V, ∀ w ∈ W, exteriorPower.map n (g : V →ₗ[k] V) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  set d := finrank k V with hd
  let bV : Basis (Fin d) k V := finBasis k V
  let b : Basis (Set.powersetCard (Fin d) n) k (⋀[k]^n V) := bV.exteriorPower n
  let H : V ≃ₗ[k] V := bV.equiv (bV.unitsSMul diagUnit) (Equiv.refl _)
  set T : Module.End k (⋀[k]^n V) := exteriorPower.map n (H : V →ₗ[k] V) with hT_def
  have hH : ∀ j : Fin d, H (bV j) = diagWeight (k := k) j • bV j := by
    intro j
    simp only [H, Basis.equiv_apply, Equiv.refl_apply, Basis.unitsSMul_apply, Units.smul_def]
    rfl
  have hbS : ∀ S : Set.powersetCard (Fin d) n,
      b S = exteriorPower.ιMulti k n (fun i => bV (S.val.orderEmbOfFin S.prop i)) := by
    intro S
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    exact congrArg _ (funext (fun i => by
      rw [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]))
  have hTdiag : ∀ S, T (b S) = diagEig (k := k) S • b S := by
    intro S
    rw [hT_def, map_exteriorBasis bV (H : V →ₗ[k] V) S]
    rw [show (fun i => (H : V →ₗ[k] V) (bV (S.val.orderEmbOfFin S.prop i))) =
        (fun i => diagWeight (k := k) (S.val.orderEmbOfFin S.prop i) •
          bV (S.val.orderEmbOfFin S.prop i)) from funext (fun i => hH _)]
    rw [AlternatingMap.map_smul_univ, prod_over_orderEmb, hbS S]
    rfl
  have hinj : Function.Injective (diagEig (k := k) (d := d) (n := n)) := diagEig_injective
  have hWT : ∀ x ∈ W, T x ∈ W := fun x hx => hW H x hx
  refine RepresentationTheory.LinearAlgebra.InvariantSubmodule.Eigenbasis.eq_bot_or_top_of_invariant_of_eigenbasis_connected
    b hTdiag hinj hWT
    (fun _ _ => True) (fun s t => Relation.ReflTransGen.tail Relation.ReflTransGen.refl trivial)
    (fun S U hS _ => ?_)
  obtain ⟨σ, hσ⟩ := exists_perm_orderEmb S U
  have hmap : exteriorPower.map n (bV.equiv bV σ : V →ₗ[k] V) (b S) = b U := by
    rw [map_exteriorBasis bV (bV.equiv bV σ : V →ₗ[k] V) S, hbS U]
    refine congrArg _ (funext (fun i => ?_))
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, hσ i]
  rw [← hmap]
  exact hW (bV.equiv bV σ) (b S) hS


-- @@ L155-155 verbatim
end RepresentationTheory.LinearAlgebra.ExteriorPower.InvariantSubmodules
