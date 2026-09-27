/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/
module

public import Mathlib.Data.Finset.Image
public import LeanPool.ErdosTuzaValtr.Lib.Core.Rel3


-- @@ L11-15 verbatim
/-!
# LeanPool.ErdosTuzaValtr.Lib.List.Defs

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Lib.List.Defs`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
variable {α : Type _}


-- @@ L21-23 verbatim
/-- Local notion for a list whose elements all lie in a finset. -/
protected def List.In (l : List α) (S : Finset α) : Prop :=
  ∀ a : α, a ∈ l → a ∈ S


-- @@ L25-27 verbatim
/-- The image of a finset under the order-dual embedding. -/
protected def Finset.Mirror [LinearOrder α] (S : Finset α) : Finset αᵒᵈ :=
  Finset.image OrderDual.toDual S


-- @@ L29-31 verbatim
/-- The image of a finset of order-dual elements back under `ofDual`. -/
protected def Finset.ofMirror [LinearOrder α] (S : Finset αᵒᵈ) : Finset α :=
  Finset.image OrderDual.ofDual S


-- @@ L33-33 verbatim
namespace List


-- @@ L35-37 verbatim
/-- Flip a list of elements together with its order, landing in the order dual. -/
protected def Mirror (l : List α) : List αᵒᵈ :=
  (List.map OrderDual.toDual l).reverse


-- @@ L39-41 verbatim
/-- Recover a list from its mirror in the order dual. -/
protected def ofMirror (l : List αᵒᵈ) : List α :=
  (List.map OrderDual.ofDual l).reverse


-- @@ L43-43 verbatim
variable (R : α → α → α → Prop)


-- @@ L45-48 verbatim
/-- `Chain3 R a b l` means `R` holds for every three consecutive entries of `a :: b :: l`. -/
inductive Chain3 : α → α → List α → Prop
  | nil {a b : α} : Chain3 a b []
  | cons : ∀ {a b c : α} {l : List α}, R a b c → Chain3 b c l → Chain3 a b (c :: l)


-- @@ L50-54 verbatim
/-- `Chain3' R l` means `R` holds for every three consecutive entries of `l`. -/
def Chain3' : List α → Prop
  | nil => True
  | [_] => True
  | a :: b :: l => Chain3 R a b l


-- @@ L56-56 verbatim
variable {R}


-- @@ L58-60 verbatim
@[simp]
theorem chain3_cons {a b c : α} {l : List α} : Chain3 R a b (c :: l) ↔ R a b c ∧ Chain3 R b c l :=
  ⟨fun p => by cases p with | cons n p => exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩


-- @@ L62-63 verbatim
@[simp]
theorem chain3_nil {a b : α} : Chain3 R a b [] := Chain3.nil


-- @@ L65-66 verbatim
instance decidableChain3 [DecidableRel3 R] (a b : α) (l : List α) : Decidable (Chain3 R a b l) := by
  induction l generalizing a b <;> simp only [Chain3.nil, chain3_cons] <;> infer_instance


-- @@ L68-72 verbatim
instance decidableChain3' [DecidableRel3 R] (l : List α) : Decidable (Chain3' R l) := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
  · exact instDecidableTrue
  · exact instDecidableTrue
  · exact decidableChain3 a b l


-- @@ L74-74 verbatim
end List
