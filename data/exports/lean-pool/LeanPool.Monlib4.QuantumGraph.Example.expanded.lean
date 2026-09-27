/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

public import Mathlib.Analysis.InnerProductSpace.Adjoint

public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.DeltaForm
public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.SchurMul
public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Symm
import LeanPool.Monlib4.LinearAlgebra.End
import LeanPool.Monlib4.LinearAlgebra.Ips.Basic
import LeanPool.Monlib4.LinearAlgebra.Matrix.PiMat
import LeanPool.Monlib4.Preq.RCLikeLe
import Mathlib.Analysis.SpecialFunctions.Bernstein


-- @@ L21-26 verbatim
/-!
  # Basic examples on quantum adjacency matrices

  This file contains elementary examples of quantum adjacency matrices,
    such as the complete graph and the trivial graph.
-/


-- @@ L28-32 verbatim
@[expose] public section


-- import quantum_graph.basic
-- import quantum_graph.basic

-- @@ L33-33 verbatim
open TensorProduct Matrix


-- @@ L35-35 verbatim
open scoped TensorProduct BigOperators Kronecker Matrix


-- @@ L37-40 verbatim
variable {p : Type _} [Fintype p] [DecidableEq p] {n : p → Type _} [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)]
  {p₂ : Type*} [Fintype p₂] [DecidableEq p₂] {n₂ : p₂ → Type*} [∀ i, Fintype (n₂ i)]
  [∀ i, DecidableEq (n₂ i)]


-- @@ L42-42 verbatim
local notation "ℍ" => PiMat ℂ p n

-- @@ L43-43 verbatim
local notation "ℍ₂" => PiMat ℂ p₂ n₂


-- @@ L45-45 verbatim
local notation "l(" x ")" => x →ₗ[ℂ] x


-- @@ L47-48 verbatim
variable {φ : Π i : p, Module.Dual ℂ (Matrix (n i) (n i) ℂ)} {ψ : Π i,
  Module.Dual ℂ (Matrix (n₂ i) (n₂ i) ℂ)}


-- @@ L50-50 verbatim
local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y


-- @@ L52-52 expanded
local notation "m" => LinearMap.mul' ℂ (PiMat ℂ p n)


-- @@ L54-54 expanded
local notation "η" => Algebra.linearMap ℂ (PiMat ℂ p n)


-- @@ L56-56 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L58-59 expanded
local notation "υ" =>
  LinearEquiv.toLinearMap (TensorProduct.assoc ℂ (PiMat ℂ p n) (PiMat ℂ p n) (PiMat ℂ p n))


-- @@ L61-62 expanded
local notation "υ⁻¹" =>
  LinearEquiv.toLinearMap
    (LinearEquiv.symm (TensorProduct.assoc ℂ (PiMat ℂ p n) (PiMat ℂ p n) (PiMat ℂ p n)))


-- @@ L64-65 expanded
local notation "ϰ" => LinearEquiv.toLinearMap ((TensorProduct.comm ℂ (PiMat ℂ p n) ℂ))


-- @@ L67-68 expanded
local notation "ϰ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ (PiMat ℂ p n) ℂ))


-- @@ L70-71 expanded
local notation "τ" => LinearEquiv.toLinearMap (TensorProduct.lid ℂ (PiMat ℂ p n))


-- @@ L73-74 expanded
local notation "τ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ (PiMat ℂ p n)))


-- @@ L76-76 expanded
local notation "id" => (1 : PiMat ℂ p n →ₗ[ℂ] PiMat ℂ p n)


-- @@ L78-82 expanded
/-- The complete quantum adjacency map between two Hilbert spaces with chosen units. -/
noncomputable def Qam.completeGraph (E₁ E₂ : Type _) [One E₁] [One E₂] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] : E₂ →ₗ[ℂ] E₁ :=
  @rankOne ℂ _ _ _ _ _ _ _ (1 : E₁) (1 : E₂)


-- @@ L84-87 expanded
theorem Qam.completeGraph_eq {E₁ E₂ : Type _} [One E₁] [One E₂] [NormedAddCommGroup E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] :
    Qam.completeGraph E₁ E₂ = @rankOne ℂ _ _ _ _ _ _ _ (1 : E₁) (1 : E₂) :=
  rfl


-- @@ L89-90 verbatim
variable {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
  [hA : QuantumSet A] [hB : QuantumSet B]


-- @@ L92-98 verbatim
theorem Qam.completeGraph_eq' :
  Qam.completeGraph A B =
    Algebra.linearMap ℂ A ∘ₗ Coalgebra.counit := by
  rw [Coalgebra.counit_eq_bra_one]
  ext
  simp [Algebra.algebraMap_eq_smul_one]
  rfl


-- @@ L100-100 verbatim
open scoped schurMul

-- @@ L101-103 expanded
theorem Qam.Nontracial.CompleteGraph.qam :
    (schurMul (Qam.completeGraph A B) (Qam.completeGraph A B)) = Qam.completeGraph A B :=
  schurMul_one_one_left _


-- @@ L105-105 verbatim
open scoped FiniteDimensional


-- @@ L107-115 verbatim
lemma Qam.Nontracial.CompleteGraph.adjoint_eq {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂] [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂]
    [FiniteDimensional ℂ E₁] [FiniteDimensional ℂ E₂] :
  LinearMap.adjoint (Qam.completeGraph E₁ E₂) = Qam.completeGraph E₂ E₁ :=
by
  let := FiniteDimensional.complete ℂ E₁
  let := FiniteDimensional.complete ℂ E₂
  rw [completeGraph_eq, ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint]
  rfl


-- @@ L117-121 verbatim
theorem Qam.Nontracial.CompleteGraph.isSelfAdjoint {E : Type _} [One E] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] :
      _root_.IsSelfAdjoint (Qam.completeGraph E E) := by
  simp_rw [_root_.IsSelfAdjoint, Qam.completeGraph, LinearMap.star_eq_adjoint,
    ContinuousLinearMap.linearMap_adjoint, rankOne_adjoint]


-- @@ L123-126 verbatim
theorem Qam.Nontracial.CompleteGraph.isReal :
    LinearMap.IsReal (Qam.completeGraph A B) := by
  simp_rw [Qam.completeGraph, LinearMap.isReal_iff, rankOne_real, star_one,
    _root_.map_one]


-- @@ L128-130 verbatim
theorem Qam.Nontracial.CompleteGraph.symm_eq :
  symmMap ℂ _ _ (Qam.completeGraph A B) = Qam.completeGraph B A :=
by simp_rw [Qam.completeGraph, symmMap_rankOne_apply, star_one, _root_.map_one]

-- @@ L131-133 verbatim
theorem Qam.Nontracial.CompleteGraph.is_symm :
  symmMap ℂ _ _ (Qam.completeGraph A A) = Qam.completeGraph A A :=
Qam.Nontracial.CompleteGraph.symm_eq


-- @@ L135-139 expanded
theorem Qam.Nontracial.CompleteGraph.is_reflexive : schurMul (Qam.completeGraph A A) 1 = 1 :=
  by
  obtain ⟨α, β, hαβ⟩ := (1 : A →ₗ[ℂ] A).exists_sum_rankOne
  nth_rw 1 [hαβ]
  simp_rw [map_sum, Qam.completeGraph, schurMul.apply_rankOne, one_mul, ← hαβ]


-- @@ L141-145 expanded
/-- The trivial quantum graph on a quantum set with delta form. -/
noncomputable def Qam.trivialGraph (A : Type*) [starAlgebra A] [CoalgebraStruct ℂ A] [QuantumSet A]
    [QuantumSetDeltaForm A] : A →ₗ[ℂ] A :=
  ⅟(LinearMap.mul' ℂ A ∘ₗ Coalgebra.comul)


-- @@ L147-147 verbatim
variable {A : Type*} [ha : starAlgebra A] [hA : QuantumSet A]


-- @@ L149-149 verbatim
open scoped ComplexOrder


-- @@ L151-151 verbatim
section TrivialGraph


-- @@ L153-153 verbatim
variable [hAc : CoalgebraStruct ℂ A]


-- @@ L155-159 verbatim
private theorem starRingEnd_delta [hA2 : QuantumSetDeltaForm A] :
    (starRingEnd ℂ) hA2.delta = hA2.delta := by
  have := hA2.delta_pos
  rw [RCLike.pos_def, ← RCLike.conj_eq_iff_im] at this
  exact this.2


-- @@ L161-167 expanded
theorem Qam.trivialGraph_eq [hA2 : QuantumSetDeltaForm A] :
    Qam.trivialGraph A = hA2.delta⁻¹ • (1 : A →ₗ[ℂ] A) :=
  by
  simp_rw [Qam.trivialGraph]
  apply invOf_eq_right_inv
  rw [hA2.mul_comp_comul_eq, smul_mul_smul_comm, one_mul, mul_inv_cancel₀, one_smul]
  · exact ne_of_gt hA2.delta_pos


-- @@ L169-177 expanded
theorem Qam.Nontracial.TrivialGraph.qam [hA2 : QuantumSetDeltaForm A] :
    schurMul (Qam.trivialGraph A) (Qam.trivialGraph A) = Qam.trivialGraph A :=
  by
  rw [Qam.trivialGraph_eq]
  simp_rw [_root_.map_smul, LinearMap.smul_apply, smul_smul, schurMul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [TensorProduct.map_one, Module.End.one_eq_id, LinearMap.id_comp, hA2.mul_comp_comul_eq,
    smul_smul, mul_assoc]
  rw [inv_mul_cancel₀ _, mul_one, Module.End.one_eq_id]
  · exact ne_of_gt hA2.delta_pos


-- @@ L179-184 verbatim
theorem Qam.Nontracial.TrivialGraph.qam.is_self_adjoint [hA2 : QuantumSetDeltaForm A] :
    LinearMap.adjoint (Qam.trivialGraph A) = Qam.trivialGraph A := by
  simp_rw [Qam.trivialGraph_eq, LinearMap.adjoint_smul, LinearMap.adjoint_one, starRingEnd_apply,
    star_inv₀, ← starRingEnd_apply]
  congr 2
  exact starRingEnd_delta


-- @@ L186-192 expanded
theorem Qam.Nontracial.trivialGraph [hA2 : QuantumSetDeltaForm A] :
    schurMul (Qam.trivialGraph A) 1 = 1 :=
  by
  rw [Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply]
  simp only [schurMul, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [TensorProduct.map_one, Module.End.one_eq_id, LinearMap.id_comp, hA2.mul_comp_comul_eq,
    smul_smul, inv_mul_cancel₀ (ne_of_gt hA2.delta_pos), one_smul, Module.End.one_eq_id]


-- @@ L194-196 expanded
theorem Qam.refl_idempotent_one_one_of_delta [hA2 : QuantumSetDeltaForm A] :
    schurMul (1 : _) (1 : A →ₗ[ℂ] A) = hA2.delta • (1 : A →ₗ[ℂ] A) := by
  simp_rw [schurMul_apply_apply, TensorProduct.map_one, LinearMap.one_comp, hA2.mul_comp_comul_eq]


-- @@ L198-204 expanded
theorem Qam.Lm.Nontracial.is_unreflexive_iff_reflexive_add_one [hA2 : QuantumSetDeltaForm A]
    (x : A →ₗ[ℂ] A) : schurMul x 1 = 0 ↔ schurMul (hA2.delta⁻¹ • (x + 1)) 1 = 1 :=
  by
  simp_rw [_root_.map_smul, LinearMap.smul_apply, _root_.map_add, LinearMap.add_apply,
    Qam.refl_idempotent_one_one_of_delta, smul_add, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hA2.delta_pos), one_smul, add_eq_right]
  rw [smul_eq_zero_iff_right (inv_ne_zero (ne_of_gt hA2.delta_pos))]


-- @@ L206-206 verbatim
end TrivialGraph


-- @@ L208-210 expanded
theorem Qam.refl_idempotent_completeGraph_left (x : A →ₗ[ℂ] B) :
    schurMul (Qam.completeGraph B A) x = x :=
  schurMul_one_one_left _


-- @@ L212-214 expanded
theorem Qam.refl_idempotent_completeGraph_right (x : A →ₗ[ℂ] B) :
    schurMul x (Qam.completeGraph B A) = x :=
  schurMul_one_one_right _


-- @@ L216-221 verbatim
/-- The complement of a quantum adjacency map, relative to the complete graph. -/
noncomputable def Qam.complement' {E₁ E₂ : Type _} [One E₁] [One E₂]
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂]
  (x : E₂ →ₗ[ℂ] E₁) : E₂ →ₗ[ℂ] E₁ :=
Qam.completeGraph E₁ E₂ - x


-- @@ L223-230 expanded
theorem Qam.Nontracial.Complement'.qam (x : A →ₗ[ℂ] B) :
    schurMul x x = x ↔ schurMul (Qam.complement' x) (Qam.complement' x) = Qam.complement' x :=
  by
  simp only [Qam.complement', _root_.map_sub, LinearMap.sub_apply,
    Qam.refl_idempotent_completeGraph_left, Qam.refl_idempotent_completeGraph_right]
  simp only [sub_eq_self]
  simp only [sub_eq_zero, @eq_comm _ x]


-- @@ L232-236 verbatim
theorem Qam.Nontracial.Complement'.qam.isReal
    (x : A →ₗ[ℂ] B) : LinearMap.IsReal x ↔ LinearMap.IsReal (Qam.complement' x) := by
  simp only [Qam.complement', LinearMap.isReal_iff, LinearMap.real_sub,
    (LinearMap.isReal_iff _).mp (Qam.Nontracial.CompleteGraph.isReal)]
  simp only [sub_right_inj]


-- @@ L238-242 verbatim
theorem Qam.complement'_complement' {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂]
    (x : E₁ →ₗ[ℂ] E₂) : Qam.complement' (Qam.complement' x) = x :=
  sub_sub_cancel _ _


-- @@ L244-252 expanded
theorem Qam.Nontracial.Complement'.ir_reflexive (x : A →ₗ[ℂ] A) (α : Prop) [Decidable α] :
    schurMul x (1 : A →ₗ[ℂ] A) = ite α (1 : A →ₗ[ℂ] A) (0 : A →ₗ[ℂ] A) ↔
      schurMul (Qam.complement' x) (1 : A →ₗ[ℂ] A) = ite α (0 : A →ₗ[ℂ] A) (1 : A →ₗ[ℂ] A) :=
  by
  simp_rw [Qam.complement', _root_.map_sub, LinearMap.sub_apply,
    Qam.refl_idempotent_completeGraph_left]
  by_cases h : α <;> simp_rw [h]
  · simp_rw [ite_true, sub_eq_zero, eq_comm]
  · simp_rw [ite_false, sub_eq_self]


-- @@ L254-259 expanded
/-- A quantum adjacency map that is idempotent and reflexive. -/
class QamReflexive (x : A →ₗ[ℂ] A) : Prop where
  /-- Idempotence under Schur multiplication. -/
  toQam : schurMul x x = x
  /-- Reflexivity condition. -/
  toRefl : schurMul x 1 = 1


-- @@ L261-263 expanded
lemma QamReflexive_iff (x : A →ₗ[ℂ] A) : QamReflexive x ↔ schurMul x x = x ∧ schurMul x 1 = 1 :=
  ⟨fun h => ⟨h.toQam, h.toRefl⟩, fun h => ⟨h.1, h.2⟩⟩


-- @@ L265-270 expanded
/-- A quantum adjacency map that is idempotent and irreflexive. -/
class QamIrreflexive (x : A →ₗ[ℂ] A) : Prop where
  /-- Idempotence under Schur multiplication. -/
  toQam : schurMul x x = x
  /-- Irreflexivity condition. -/
  toIrrefl : schurMul x 1 = 0


-- @@ L272-274 expanded
lemma QamIrreflexive_iff (x : A →ₗ[ℂ] A) : QamIrreflexive x ↔ schurMul x x = x ∧ schurMul x 1 = 0 :=
  ⟨fun h => ⟨h.toQam, h.toIrrefl⟩, fun h => ⟨h.1, h.2⟩⟩


-- @@ L276-281 expanded
theorem Qam.complement'_is_irreflexive_iff (x : A →ₗ[ℂ] A) :
    QamIrreflexive (Qam.complement' x) ↔ QamReflexive x :=
  by
  have := Qam.Nontracial.Complement'.ir_reflexive x True
  simp_rw [ite_true] at this
  rw [QamReflexive_iff, QamIrreflexive_iff, ← Qam.Nontracial.Complement'.qam]
  simp_rw [this]


-- @@ L283-287 expanded
theorem Qam.complement'_is_reflexive_iff (x : A →ₗ[ℂ] A) :
    QamReflexive (Qam.complement' x) ↔ QamIrreflexive x :=
  by
  have := Qam.Nontracial.Complement'.ir_reflexive x False
  simp_rw [ite_false] at this
  rw [QamReflexive_iff, QamIrreflexive_iff, ← Qam.Nontracial.Complement'.qam, this]


-- @@ L289-293 expanded
/-- Complement relative to the trivial graph. -/
noncomputable def Qam.complement'' [QuantumSetDeltaForm A] (x : A →ₗ[ℂ] A) : A →ₗ[ℂ] A :=
  x - Qam.trivialGraph A


-- @@ L295-309 expanded
theorem Qam.complement''_is_irreflexive_iff [hA2 : QuantumSetDeltaForm A] {x : A →ₗ[ℂ] A}
    (hx : LinearMap.IsReal x) : QamIrreflexive (Qam.complement'' x) ↔ QamReflexive x :=
  by
  rw [QamReflexive_iff, QamIrreflexive_iff]
  have t1 := @Qam.Nontracial.TrivialGraph.qam A _ _ _
  have t2 := @Qam.Nontracial.trivialGraph A _ _ _
  have t3 : schurMul (Qam.complement'' x) 1 = 0 ↔ schurMul x 1 = 1 := by
    simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t2, sub_eq_zero]
  rw [t3]
  simp_rw [Qam.complement'', map_sub, LinearMap.sub_apply, t1, sub_sub]
  constructor <;> rintro ⟨h1, h2⟩
  all_goals
    exact
      ⟨by
        simp only [Qam.trivialGraph_eq, _root_.map_smul, LinearMap.smul_apply, h2,
          (schurMul_reflexive_of_isReal hx).mp h2, sub_self, add_zero, sub_left_inj] at h1 ⊢
        exact h1, h2⟩


-- @@ L311-314 expanded
/-- Complement operation producing the irreflexive complement. -/
noncomputable def Qam.irreflexiveComplement [QuantumSetDeltaForm A] (x : A →ₗ[ℂ] A) : A →ₗ[ℂ] A :=
  Qam.completeGraph A A - Qam.trivialGraph A - x


-- @@ L316-319 expanded
/-- Complement operation producing the reflexive complement. -/
noncomputable def Qam.reflexiveComplement [QuantumSetDeltaForm A] (x : A →ₗ[ℂ] A) : A →ₗ[ℂ] A :=
  Qam.completeGraph A A + Qam.trivialGraph A - x


-- @@ L321-326 verbatim
theorem Qam.Nontracial.trivialGraph.isReal [hA2 : QuantumSetDeltaForm A] :
    LinearMap.IsReal (Qam.trivialGraph A) := by
  rw [LinearMap.isReal_iff, Qam.trivialGraph_eq, LinearMap.real_smul, LinearMap.real_one,
    starRingEnd_apply, star_inv₀]
  congr
  exact starRingEnd_delta


-- @@ L328-334 expanded
theorem Qam.irreflexiveComplement.isReal [hA2 : QuantumSetDeltaForm A] {x : A →ₗ[ℂ] A}
    (hx : LinearMap.IsReal x) : LinearMap.IsReal (Qam.irreflexiveComplement x) := by
  rw [LinearMap.isReal_iff, Qam.irreflexiveComplement, LinearMap.real_sub, LinearMap.real_sub,
    (LinearMap.isReal_iff (Qam.completeGraph A A)).mp Qam.Nontracial.CompleteGraph.isReal,
    (LinearMap.isReal_iff (Qam.trivialGraph A)).mp Qam.Nontracial.trivialGraph.isReal,
    (LinearMap.isReal_iff x).mp hx]


-- @@ L336-342 expanded
theorem Qam.reflexiveComplement.isReal [hA2 : QuantumSetDeltaForm A] {x : A →ₗ[ℂ] A}
    (hx : LinearMap.IsReal x) : LinearMap.IsReal (Qam.reflexiveComplement x) := by
  rw [LinearMap.isReal_iff, Qam.reflexiveComplement, LinearMap.real_sub, LinearMap.real_add,
    (LinearMap.isReal_iff (Qam.completeGraph A A)).mp Qam.Nontracial.CompleteGraph.isReal,
    (LinearMap.isReal_iff (Qam.trivialGraph A)).mp Qam.Nontracial.trivialGraph.isReal,
    (LinearMap.isReal_iff x).mp hx]


-- @@ L344-346 expanded
theorem Qam.irreflexiveComplement_irreflexiveComplement [QuantumSetDeltaForm A] {x : A →ₗ[ℂ] A} :
    Qam.irreflexiveComplement (Qam.irreflexiveComplement x) = x :=
  sub_sub_cancel _ _


-- @@ L348-350 expanded
theorem Qam.reflexiveComplement_reflexiveComplement [QuantumSetDeltaForm A] {x : A →ₗ[ℂ] A} :
    Qam.reflexiveComplement (Qam.reflexiveComplement x) = x :=
  sub_sub_cancel _ _


-- @@ L352-354 verbatim
theorem Qam.trivialGraph_reflexiveComplement_eq_completeGraph [QuantumSetDeltaForm A] :
    Qam.reflexiveComplement (Qam.trivialGraph A) = Qam.completeGraph A A :=
by simp_rw [reflexiveComplement, add_sub_cancel_right]


-- @@ L356-358 verbatim
theorem Qam.completeGraph_reflexiveComplement_eq_trivialGraph [QuantumSetDeltaForm A] :
    Qam.reflexiveComplement (Qam.completeGraph A A) = Qam.trivialGraph A :=
  add_sub_cancel_left _ _


-- @@ L360-364 verbatim
theorem Qam.complement'_eq {E₁ E₂ : Type _} [NormedAddCommGroupOfRing E₁]
    [NormedAddCommGroupOfRing E₂]
    [InnerProductSpace ℂ E₁] [InnerProductSpace ℂ E₂] (a : E₂ →ₗ[ℂ] E₁) :
    Qam.complement' a = Qam.completeGraph E₁ E₂ - a :=
  rfl


-- @@ L366-373 expanded
theorem Qam.irreflexiveComplement_is_irreflexive_qam_iff_irreflexive_qam
    [hA2 : QuantumSetDeltaForm A] {x : A →ₗ[ℂ] A} (hx : LinearMap.IsReal x) :
    QamIrreflexive (Qam.irreflexiveComplement x) ↔ QamIrreflexive x :=
  by
  rw [Qam.irreflexiveComplement, sub_sub, ← Qam.complement'_eq, Qam.complement'_is_irreflexive_iff,
    ← Qam.complement''_is_irreflexive_iff, Qam.complement'', add_sub_cancel_left]
  ·
    rw [LinearMap.isReal_iff, LinearMap.real_add, x.isReal_iff.mp hx,
      (Qam.trivialGraph A).isReal_iff.mp Qam.Nontracial.trivialGraph.isReal]


-- @@ L375-380 expanded
theorem Qam.reflexive_complment_is_reflexive_qam_iff_reflexive_qam [hA2 : QuantumSetDeltaForm A]
    {x : A →ₗ[ℂ] A} (hx : LinearMap.IsReal x) :
    QamReflexive (Qam.reflexiveComplement x) ↔ QamReflexive x :=
  by
  rw [Qam.reflexiveComplement, ← sub_sub_eq_add_sub, ← Qam.complement'_eq,
    Qam.complement'_is_reflexive_iff]
  exact Qam.complement''_is_irreflexive_iff hx


-- @@ L383-386 verbatim
theorem QuantumSet.Psi_apply_completeGraph {A : Type*} {B : Type*} [starAlgebra A]
    [starAlgebra B] [QuantumSet A] [QuantumSet B] (t r : ℝ) :
  QuantumSet.Psi t r (Qam.completeGraph A B) = 1 :=
QuantumSet.Psi_apply_one_one _ _

-- @@ L387-390 verbatim
theorem QuantumSet.Psi_symm_one {A B : Type*} [starAlgebra A]
  [starAlgebra B] [QuantumSet A] [QuantumSet B] (t r : ℝ) :
  (QuantumSet.Psi t r).symm 1 = Qam.completeGraph A B :=
QuantumSet.Psi_symm_apply_one _ _
