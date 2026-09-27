/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.SetTheory.Descriptive.Tree
public import Mathlib.Algebra.Group.End
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.General
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.Meta
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L19-23 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.Trees

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L25-25 verbatim
@[expose] public section



-- @@ L28-29 verbatim
namespace Descriptive.Tree
--TODO if continue commits, add newline between declarations before

-- @@ L30-30 verbatim
variable {A A' : Type*} (S T : tree A) (x y : List A)


-- @@ L32-33 verbatim
/-- Set of children of node x as elements of T -/
def ExtensionsAt {T : tree A} (x : T) := { a : A // x.val ++ [a] ∈ T }

-- @@ L34-34 verbatim
namespace ExtensionsAt

-- @@ L35-35 verbatim
variable {S T}

-- @@ L36-36 verbatim
variable {n : ℕ} {x : T} (a : ExtensionsAt x)

-- @@ L37-38 verbatim
/-- The underlying list of a child -/
def val' := x.val ++ [a.val]

-- @@ L39-40 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps coe] def valT' : T := ⟨a.val', a.prop⟩

-- @@ L41-41 verbatim
@[ext] lemma ext {a b : ExtensionsAt x} (h : a.val = b.val) : a = b := Subtype.ext h

-- @@ L42-43 verbatim
lemma ext_val' {a b : ExtensionsAt x} (h : a.val' = b.val') : a = b := by
  ext; simpa [val'] using h

-- @@ L44-45 verbatim
lemma ext_valT' {a b : ExtensionsAt x} (h : a.valT' = b.valT') : a = b :=
  ext_val' <| congr_arg Subtype.val h

-- @@ L46-52 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def drop {T : tree A} {n : ℕ} {x : T} :
  ExtensionsAt x ≃ ExtensionsAt (Tree.drop T n x) where --TODO fix T explicit
  toFun a := ⟨a.val, by simpa [← List.append_assoc] using a.prop⟩
  invFun a := ⟨a.val, by simpa [← List.append_assoc] using a.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

-- @@ L53-55 verbatim
@[simp] lemma val'_length :
  a.val' (A := no_index _).length (α := no_index _) = x.val.length (α := no_index _) + 1 := by
  simp [ExtensionsAt.val']

-- @@ L56-57 verbatim
lemma val'_get_last_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  a.val'[n]'(by simp [h]) = a.val := by simp [val', h]

-- @@ L58-59 verbatim
@[simp↓ 1100] lemma val'_get_last (a : ExtensionsAt x) :
  a.val' (A := no_index _)[x.val.length (α := no_index _)] = a.val := by simp [val']

-- @@ L60-61 verbatim
lemma val'_take_of_le (a : ExtensionsAt x) (h : n ≤ x.val.length) :
  a.val'.take n = x.val.take n := by simpa [val']

-- @@ L62-63 verbatim
lemma val'_take_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  a.val'.take n = x.val := by simp [val', h]

-- @@ L64-65 verbatim
@[simp↓ 1100] lemma val'_take (a : ExtensionsAt x) :
  a.val' (A := no_index _).take (x.val.length (α := no_index _)) = x.val := by simp [val']

-- @@ L66-67 verbatim
lemma valT'_take_of_le (a : ExtensionsAt x) (h : n ≤ x.val.length) :
  take n a.valT' = take n x := Subtype.ext <| a.val'_take_of_le h

-- @@ L68-69 verbatim
lemma valT'_take_of_eq (a : ExtensionsAt x) (h : n = x.val.length) :
  take n a.valT' = x := Subtype.ext <| a.val'_take_of_eq h

-- @@ L70-71 verbatim
@[simp↓ 1100] lemma valT'_take (a : ExtensionsAt x) :
  take (x.val.length (α := no_index _)) a.valT'  (A := no_index _) = x := Subtype.ext a.val'_take

-- @@ L72-72 verbatim
end ExtensionsAt


-- @@ L74-75 verbatim
/-- A tree is pruned if it has no leaves -/
def IsPruned : Prop := ∀ x : T, Nonempty (ExtensionsAt x)

-- @@ L76-78 verbatim
lemma IsPruned.sub {T : tree A} (h : IsPruned T) (x : List A) : IsPruned (subAt T x) := by
  intro ⟨y, h'⟩
  simpa only [ExtensionsAt, nonempty_subtype, List.append_assoc, mem_subAt] using h ⟨_, h'⟩

-- @@ L79-88 verbatim
lemma IsPruned.pullSub {T : tree A} (hP : IsPruned T) (x : List A) : IsPruned (pullSub T x) := by
  intro ⟨y, hy⟩; rcases lt_or_ge y.length x.length with h | h
  · rw [mem_pullSub_short (by omega), List.prefix_iff_eq_take] at hy; use x.get ⟨y.length, h⟩
    simp_rw (config := {singlePass := true}) [hy.1]
    conv => simp [h.le]
    constructor
    · rw [List.take_take]; apply List.take_prefix
    · rw [List.drop_take]; simpa [h] using hy.2
  · rw [mem_pullSub_long h] at hy; obtain ⟨z, hz, rfl⟩ := hy; obtain ⟨a, ha⟩ := hP ⟨z, hz⟩
    use a; simpa

-- @@ L89-89 verbatim
@[simp] lemma pullSub_ne {T : tree A} x : [] ∈ pullSub T x ↔ [] ∈ T := by simp [mem_pullSub_short]

-- @@ L90-91 verbatim
@[simp] lemma top_isPruned [h : Nonempty A] : IsPruned (⊤ : tree A) :=
  fun _ ↦ ⟨h.some, CompleteSublattice.mem_top⟩


-- @@ L93-99 verbatim
/-- Order elements of a tree by the prefix relation -/
@[simps] instance instPartialOrderTree (T : tree A) : PartialOrder T where
  le x y := x.val <+: y.val
  le_refl _ := List.prefix_refl _
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ h h' :=
    Subtype.ext <| List.IsPrefix.eq_of_length h <| h.length_le.antisymm h'.length_le

-- @@ L100-104 verbatim
lemma apply_append {S : tree A} {T : tree A'} (f : OrderHom S T)
  {x y : List A} (h : x ++ y ∈ S) :
  ∃ z, (f ⟨x ++ y, h⟩).val = f ⟨x, mem_of_append h⟩ ++ z :=
  let ⟨z, h⟩ := f.monotone (a := ⟨x, mem_of_append h⟩) (b := ⟨_, h⟩) ⟨y, rfl⟩
  ⟨z, h.symm⟩


-- @@ L106-106 verbatim
attribute [simp_lengths] take_coe drop_coe ExtensionsAt.valT'_coe ExtensionsAt.val'_length

-- @@ L107-107 verbatim
end Tree

-- @@ L108-108 verbatim
end Descriptive
