/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Batteries.Data.Vector.Lemmas
public import VCVio.OracleComp.Constructions.SampleableType


-- @@ L11-15 verbatim
/-!
  # Prelude for Interactive (Oracle) Reductions

  This file contains preliminary definitions and instances that is used in defining I(O)Rs.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-23 verbatim
open OracleComp

-- -- Notation for sums (maybe not needed?)
-- @[inherit_doc] postfix:max "↪ₗ" => Sum.inl
-- @[inherit_doc] postfix:max "↪ᵣ" => Sum.inr


-- @@ L25-30 verbatim
/-- `⊕ᵥ` is notation for `Sum.rec`, the dependent elimination of `Sum.

This sends `(a : α) → γ (.inl a)` and `(b : β) → γ (.inr b)` to `(a : α ⊕ β) → γ a`. -/
infixr:35 " ⊕ᵥ " => Sum.rec

-- Figure out where to put this instance

-- @@ L31-32 verbatim
instance instDecidableEqOption {α : Type*} [DecidableEq α] :
    DecidableEq (Option α) := inferInstance


-- @@ L34-37 verbatim
/-- `VCVCompabible` is a type class for types that are finite, inhabited, and have decidable
  equality. These instances are needed when the type is used as the range of some `OracleSpec`. -/
class VCVCompatible (α : Type*) extends Fintype α, Inhabited α where
  [type_decidableEq' : DecidableEq α]


-- @@ L39-41 verbatim
instance {α : Type*} [VCVCompatible α] : DecidableEq α := VCVCompatible.type_decidableEq'

-- TODO: port first to batteries, second to mathlib


-- @@ L43-46 verbatim
@[simp]
theorem Vector.ofFn_get {α : Type*} {n : ℕ} (v : Vector α n) : Vector.ofFn (Vector.get v) = v := by
  ext
  simp [getElem]


-- @@ L48-49 verbatim
def Equiv.rootVectorEquivFin {α : Type*} {n : ℕ} : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩


-- @@ L51-52 verbatim
instance Vector.instFintype {α : Type*} {n : ℕ} [VCVCompatible α] : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.rootVectorEquivFin).symm


-- @@ L54-54 verbatim
instance {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Fin n → α) where


-- @@ L56-56 verbatim
instance {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Vector α n) where


-- @@ L58-59 verbatim
/-- `Sampleable` extends `VCVCompabible` with `SampleableType` -/
class Sampleable (α : Type) extends VCVCompatible α, SampleableType α


-- @@ L61-61 verbatim
instance {α : Type} [Sampleable α] : DecidableEq α := inferInstance


-- @@ L63-69 verbatim
/-- Enum type for the direction of a round in a protocol specification. It is either `.P_to_V`
(the prover sends a message to the verifier) or `.V_to_P` (the verifier sends a challenge to the
prover). -/
inductive Direction where
  | P_to_V  -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr


-- @@ L71-71 verbatim
namespace Direction


-- @@ L73-79 verbatim
/-- Equivalence between `Direction` and `Fin 2`, sending `V_to_P` to `0` and `P_to_V` to `1`
(the choice is essentially arbitrary). -/
def equivFin2 : Direction ≃ Fin 2 where
  toFun := fun dir => match dir with | .V_to_P => ⟨0, by decide⟩ | .P_to_V => ⟨1, by decide⟩
  invFun := fun n => match n with | ⟨0, _⟩ => .V_to_P | ⟨1, _⟩ => .P_to_V
  left_inv := fun dir => match dir with | .P_to_V => rfl | .V_to_P => rfl
  right_inv := fun n => match n with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl


-- @@ L81-87 verbatim
/-- Equivalence between `Direction` and `Bool`, sending `V_to_P` to `false` and `P_to_V` to `true`
(the choice is essentially arbitrary). -/
def equivBool : Direction ≃ Bool where
  toFun := fun dir => match dir with | .V_to_P => false | .P_to_V => true
  invFun := fun b => match b with | false => .V_to_P | true => .P_to_V
  left_inv := fun dir => match dir with | .P_to_V => rfl | .V_to_P => rfl
  right_inv := fun b => match b with | false => rfl | true => rfl


-- @@ L89-90 verbatim
/-- This allows us to write `0` for `.V_to_P` and `1` for `.P_to_V`. -/
instance : Coe (Fin 2) Direction := ⟨equivFin2.invFun⟩


-- @@ L92-98 verbatim
instance : Coe Bool Direction := ⟨equivBool.invFun⟩

lemma not_P_to_V_eq_V_to_P {x : Direction} (h : x ≠ .V_to_P) : x = .P_to_V := by
  cases x <;> simp_all

lemma not_V_to_P_eq_P_to_V {x : Direction} (h : x ≠ .P_to_V) : x = .V_to_P := by
  cases x <;> simp_all


-- @@ L100-100 verbatim
end Direction


-- @@ L102-104 verbatim
section Relation

-- TODO: use mathlib's `Rel` which will be `Set`-based in the next update


-- @@ L106-109 verbatim
/-- The associated language `Set α` for a relation `Set (α × β)`. -/
@[reducible]
def Set.language {α β} (rel : Set (α × β)) : Set α :=
  Prod.fst '' rel


-- @@ L111-114 verbatim
@[simp]
theorem Set.mem_language_iff {α β} (rel : Set (α × β)) (stmt : α) :
    stmt ∈ rel.language ↔ ∃ wit, (stmt, wit) ∈ rel := by
  simp [language]


-- @@ L116-119 verbatim
@[simp]
theorem Set.not_mem_language_iff {α β} (rel : Set (α × β)) (stmt : α) :
    stmt ∉ rel.language ↔ ∀ wit, (stmt, wit) ∉ rel := by
  simp [language]


-- @@ L121-124 verbatim
/-- The trivial relation on Boolean statement and unit witness, which outputs the Boolean (i.e.
  accepts or rejects). -/
def acceptRejectRel : Set (Bool × Unit) :=
  { (true, ()) }


-- @@ L126-128 verbatim
/-- The trivial relation on Boolean statement, no oracle statements, and unit witness. -/
def acceptRejectOracleRel : Set ((Bool × (∀ _ : Empty, Unit)) × Unit) :=
  { ((true, isEmptyElim), ()) }


-- @@ L130-132 verbatim
@[simp]
theorem acceptRejectRel_language : acceptRejectRel.language = { true } := by
  unfold Set.language acceptRejectRel; simp


-- @@ L134-137 verbatim
@[simp]
theorem acceptRejectOracleRel_language :
    acceptRejectOracleRel.language = { (true, isEmptyElim) } := by
  unfold Set.language acceptRejectOracleRel; simp


-- @@ L139-139 verbatim
end Relation
