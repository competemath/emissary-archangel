/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance

public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L13-18 verbatim
/-!
# Quantum Sets on Finite Products

This file restores the finite-product quantum set instance from upstream
`Monlib.LinearAlgebra.QuantumSet.Pi`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open scoped BigOperators InnerProductSpace


-- @@ L24-24 verbatim
section Pi


-- @@ L26-26 verbatim
variable {ι : Type*} {A : ι -> Type*}


-- @@ L28-30 verbatim
/-- The `L²` finite product of quantum sets. -/
abbrev PiQ (A : ι -> Type*) :=
  PiLp 2 A


-- @@ L32-32 verbatim
variable [hA : (i : ι) -> starAlgebra (A i)]


-- @@ L34-36 verbatim
@[reducible, default_instance]
noncomputable instance : Ring (PiQ A) :=
  (WithLp.equiv (2 : ENNReal) ((i : ι) -> A i)).ring


-- @@ L38-40 verbatim
@[reducible, default_instance]
noncomputable instance : Algebra ℂ (PiQ A) :=
  Equiv.algebra ℂ (WithLp.equiv (2 : ENNReal) ((i : ι) -> A i))


-- @@ L42-43 verbatim
instance : Star (PiQ A) where
  star x := WithLp.toLp (2 : ENNReal) (star x.ofLp)


-- @@ L45-48 verbatim
@[simp]
lemma PiLp.star_apply (x : PiQ A) (i : ι) :
    (star x) i = star (x i) :=
  rfl


-- @@ L50-53 verbatim
@[simp]
lemma PiLp.mul_apply_quantum (x y : PiQ A) (i : ι) :
    (x * y) i = x i * y i :=
  rfl


-- @@ L55-57 verbatim
lemma PiLp.mul_apply (x y : PiQ A) (i : ι) :
    (x * y) i = x i * y i :=
  PiLp.mul_apply_quantum x y i


-- @@ L59-68 verbatim
instance : StarRing (PiQ A) where
  star_involutive x := by
    ext i
    exact star_star (x i)
  star_mul x y := by
    ext i
    exact star_mul (x i) (y i)
  star_add x y := by
    ext i
    exact star_add (x i) (y i)


-- @@ L70-73 verbatim
instance : StarModule ℂ (PiQ A) where
  star_smul c x := by
    ext i
    exact star_smul c (x i)


-- @@ L75-79 verbatim
/-- The pointwise modular automorphism on a finite product quantum set. -/
noncomputable def Pi.modAut (r : ℝ) : PiQ A ≃ₐ[ℂ] PiQ A :=
  let e : PiQ A ≃ₐ[ℂ] ((i : ι) -> A i) :=
    Equiv.algEquiv ℂ (WithLp.equiv (2 : ENNReal) ((i : ι) -> A i))
  e.trans ((AlgEquiv.piCongrRight fun i => (hA i).modAut r).trans e.symm)


-- @@ L81-84 verbatim
@[simp]
lemma Pi.modAut_apply (r : ℝ) (x : PiQ A) (i : ι) :
    Pi.modAut r x i = (hA i).modAut r (x i) :=
  rfl


-- @@ L86-94 verbatim
@[reducible, instance]
noncomputable def piStarAlgebra : starAlgebra (PiQ A) where
  modAut r := Pi.modAut r
  modAut_trans r s := by
    ext x i
    simp [starAlgebra.modAut_apply_modAut, add_comm]
  modAut_star r x := by
    ext i
    simp [starAlgebra.modAut_star]


-- @@ L96-99 verbatim
@[simp]
lemma piStarAlgebra_modAut_apply (r : ℝ) (x : PiQ A) (i : ι) :
    piStarAlgebra.modAut r x i = (hA i).modAut r (x i) :=
  rfl


-- @@ L101-101 verbatim
variable [hQ : (i : ι) -> QuantumSet (A i)]

-- @@ L102-102 verbatim
variable [Fintype ι]


-- @@ L104-114 verbatim
noncomputable instance piInnerProductAlgebra : InnerProductAlgebra (PiQ A) where
  norm_smul_le := norm_smul_le
  norm_sq_eq_inner := norm_sq_eq_re_inner
  dist_eq x y := by
    rw [dist_eq_norm']
    congr 1
    ext i
    simp [sub_eq_add_neg, add_comm]
  conj_symm := inner_conj_symm
  add_left := inner_add_left
  smul_left := inner_smul_left


-- @@ L116-118 verbatim
theorem piInnerProductAlgebra_inner_apply (a b : PiQ A) :
    ⟪a, b⟫_ℂ = ∑ i, ⟪a i, b i⟫_ℂ := by
  rw [PiLp.inner_apply]


-- @@ L120-122 verbatim
theorem piInnerProductAlgebra.inner_apply (a b : PiQ A) :
    ⟪a, b⟫_ℂ = ∑ i, ⟪a i, b i⟫_ℂ :=
  piInnerProductAlgebra_inner_apply a b


-- @@ L124-152 verbatim
noncomputable instance Pi.quantumSet [Fact (∀ i, (hQ i).k = 0)] : QuantumSet (PiQ A) where
  modAut_isSymmetric r x y := by
    rw [piInnerProductAlgebra_inner_apply, piInnerProductAlgebra_inner_apply]
    simp_all
  k := 0
  inner_star_left x y z := by
    rw [piInnerProductAlgebra_inner_apply, piInnerProductAlgebra_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.mul_apply_quantum, PiLp.mul_apply_quantum, piStarAlgebra_modAut_apply,
      PiLp.star_apply]
    have hk : (hQ i).k = 0 := (Fact.out : ∀ i, (hQ i).k = 0) i
    simp_all
  inner_conj_left x y z := by
    rw [piInnerProductAlgebra_inner_apply, piInnerProductAlgebra_inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.mul_apply_quantum, PiLp.mul_apply_quantum, piStarAlgebra_modAut_apply,
      PiLp.star_apply]
    have hk : (hQ i).k = 0 := (Fact.out : ∀ i, (hQ i).k = 0) i
    simpa [hk] using (hQ i).inner_conj_left (x i) (y i) (z i)
  n := (i : ι) × n (A i)
  nIsFintype := by
    letI : (i : ι) -> Fintype (n (A i)) := fun i => (hQ i).nIsFintype
    infer_instance
  nIsDecidableEq := Classical.typeDecidableEq ((i : ι) × n (A i))
  onb := by
    letI : (i : ι) -> Fintype (n (A i)) := fun i => (hQ i).nIsFintype
    exact Pi.orthonormalBasis fun i => (hQ i).onb


-- @@ L154-154 verbatim
end Pi
