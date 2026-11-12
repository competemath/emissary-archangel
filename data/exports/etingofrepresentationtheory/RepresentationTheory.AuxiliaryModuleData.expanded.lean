/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.GeneralLinearGroup.Auxiliary
import RepresentationTheory.GeneralLinearGroup.WeightCharacter


-- @@ L12-12 verbatim
set_option linter.style.longLine false

-- @@ L13-13 verbatim
set_option linter.style.header false


-- @@ L15-15 verbatim
open CategoryTheory

-- @@ L16-16 verbatim
open scoped TensorProduct


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace RepresentationTheory.AuxiliaryModuleData


-- @@ L22-22 verbatim
variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]


-- @@ L24-26 verbatim
/-- An auxiliary type of labels for each natural-number index. -/
@[source_ref"Chapter5/Discussion_after_Definition5.23.1"(role:=supporting)]
def auxiliaryIndex (n : ℕ) := { lam : Fin n → ℤ // Antitone lam }


-- @@ L28-31 verbatim
/-- Associates a natural number to an auxiliary label. -/
def auxiliaryIndex.toNat : {n : ℕ} → auxiliaryIndex n → ℕ
  | 0, _ => 0
  | _ + 1, lam => (-(lam.val (Fin.last _))).toNat


-- @@ L33-35 verbatim
/-- Associates a natural number to an auxiliary label at a finite position. -/
def auxiliaryIndex.toNatAt {n : ℕ} (lam : auxiliaryIndex n) : Fin n → ℕ :=
  fun i => (lam.val i + lam.toNat).toNat


-- @@ L37-41 verbatim
/-- An auxiliary self-map of each index type. -/
def auxiliaryIndex.auxiliaryMap {n : ℕ} (lam : auxiliaryIndex n) : auxiliaryIndex n :=
  ⟨fun i => -lam.val (Fin.rev i), fun i j hij => by
    simp only [neg_le_neg_iff]
    exact lam.property (Fin.rev_anti hij)⟩


-- @@ L43-46 verbatim
/-- An auxiliary family of types parameterized by an index, a label, and an algebraically closed field. -/
noncomputable def auxiliaryFamily (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] : Type _ :=
  ↥(RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n lam.toNatAt)


-- @@ L48-53 verbatim
/-- The additive commutative group structure on each member of the auxiliary family. -/
noncomputable instance auxiliaryFamily.instAddCommGroup (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] : AddCommGroup (auxiliaryFamily n lam k) :=
  show AddCommGroup
      ↥(RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n lam.toNatAt) from
    inferInstance


-- @@ L55-60 verbatim
/-- The module structure on each member of the auxiliary family. -/
noncomputable instance auxiliaryFamily.instModule (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module k (auxiliaryFamily n lam k) :=
  show Module k
      ↥(RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n lam.toNatAt) from
    inferInstance


-- @@ L62-67 verbatim
/-- Each auxiliary family member is finite as a module over its coefficient field. -/
noncomputable instance auxiliaryFamily.finite (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module.Finite k (auxiliaryFamily n lam k) :=
  show Module.Finite k
      ↥(RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k n lam.toNatAt) from
    inferInstance


-- @@ L69-72 verbatim
/-- A second auxiliary family of types parameterized by an index, a label, and an algebraically closed field. -/
noncomputable def auxiliaryOtherFamily (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] : Type _ :=
  auxiliaryFamily n lam.auxiliaryMap k


-- @@ L74-77 verbatim
/-- The additive commutative group structure on each member of the second auxiliary family. -/
noncomputable instance auxiliaryOtherFamily.instAddCommGroup (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] : AddCommGroup (auxiliaryOtherFamily n lam k) :=
  auxiliaryFamily.instAddCommGroup n lam.auxiliaryMap k


-- @@ L79-82 verbatim
/-- The module structure on each member of the second auxiliary family. -/
noncomputable instance auxiliaryOtherFamily.instModule (n : ℕ) (lam : auxiliaryIndex n)
    (k : Type*) [Field k] [IsAlgClosed k] : Module k (auxiliaryOtherFamily n lam k) :=
  auxiliaryFamily.instModule n lam.auxiliaryMap k


-- @@ L84-86 verbatim
/-- Each auxiliary index type is countable. -/
instance auxiliaryIndex.countable (n : ℕ) : Countable (auxiliaryIndex n) :=
  Subtype.countable


-- @@ L88-105 verbatim
private theorem schurPoly_ne_zero (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N lam ≠ 0 := by
  intro h
  have hprod :=
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase N lam
  rw [h, zero_mul] at hprod
  have hstrict :
      StrictAnti (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam) := by
    intro i j hij
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase]
    have := hlam (le_of_lt hij)
    omega
  have hcoeff :=
    RepresentationTheory.SymmetricPolynomials.Alternant.coeff_det_alternantMatrix_of_strictAnti
      hstrict hstrict
  rw [if_pos rfl] at hcoeff
  rw [← hprod, MvPolynomial.coeff_zero] at hcoeff
  exact one_ne_zero hcoeff.symm


-- @@ L107-145 verbatim
set_option linter.style.maxHeartbeats false in
set_option synthInstance.maxHeartbeats 80000 in
/-- An auxiliary construction indexed by an antitone finite sequence is nontrivial. -/
theorem auxiliary_ne_bot_of_antitone (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N lam ≠ ⊥ := by
  intro h
  have hchar :
      RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter k N
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k N lam) = 0 := by
    unfold RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter
    apply Finset.sum_eq_zero
    intro μ _
    suffices Module.finrank k
        (RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightSpace k N
          (RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k N lam)
          (fun i => μ i)) = 0 by
      rw [this, Nat.cast_zero, zero_smul]
    have hsub :
        ∀ (a b : RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurSubmodule k N lam),
          a = b := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      ext
      rw [h] at ha hb
      simp only [Submodule.mem_bot] at ha hb
      simp [ha, hb]
    have hsub' :
        ∀ (a b :
          RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation k N lam),
          a = b := hsub
    rw [Module.finrank_eq_zero_iff]
    intro x
    have : x = 0 := by
      have := hsub' x.val 0
      exact Subtype.ext this
    exact ⟨1, one_ne_zero, by rw [this, smul_zero]⟩
  have hne := schurPoly_ne_zero N lam hlam
  rw [RepresentationTheory.GeneralLinearGroup.WeightCharacter.schurRepresentation_weightCharacter
    k N lam hlam] at hchar
  exact hne hchar


-- @@ L147-147 verbatim
end RepresentationTheory.AuxiliaryModuleData


-- @@ L149-150 verbatim
/-- The Schur submodule indexed by an antitone finite sequence is nontrivial. -/
alias _root_.RepresentationTheory.AuxiliaryModuleData.schurSubmodule_ne_bot_of_antitone := _root_.RepresentationTheory.AuxiliaryModuleData.auxiliary_ne_bot_of_antitone
