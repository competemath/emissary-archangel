/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši
-/
module

public import ArkLib.Data.Fin.Basic


-- @@ L10-12 verbatim
/-!
  # Lifting of `Fin`-indexed vectors
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace Fin


-- @@ L18-18 verbatim
section Lift


-- @@ L20-31 verbatim
variable {α : Type*}
         {m n : ℕ}

/-
  Basic ad-hoc lifting;
  - `liftF : (Fin n → α) → ℕ → α`
  - `liftF` : (ℕ → α) → Fin n → α
  These invert each other assuming appropriately-bounded domains.

  These are specialised versions of true lifts that uses `Nonempty` / `Inhabited`
  and take the complement of the finite set which is the domain of the function being lifted.
-/


-- @@ L33-33 verbatim
variable [Zero α] {f : ℕ → α} {f' : Fin n → α}


-- @@ L35-39 verbatim
/-- `liftF` lifts functions over domains `Fin n` to functions over domains `ℕ`
  by returning `0` on points `≥ n`.
-/
def liftF (f : Fin n → α) : ℕ → α :=
  fun m ↦ if h : m < n then f ⟨m, h⟩ else 0


-- @@ L41-45 verbatim
/-- `liftF'` lifts functions over domains `ℕ` to functions over domains `Fin n`
  by taking the obvious injection.
-/
def liftF' (f : ℕ → α) : Fin n → α :=
  fun m ↦ f m.1


-- @@ L47-47 verbatim
open Fin (liftF' liftF)


-- @@ L49-55 verbatim
@[simp]
lemma liftF_succ {f : Fin (n + 1) → α} : liftF f n = f ⟨n, Nat.lt_add_one _⟩ := by
  aesop (add simp liftF)

lemma liftF'_liftF_of_lt {k : Fin m} (h : k < n) :
    liftF' (n := m) (liftF (n := n) f') k = f' ⟨k, by omega⟩ := by
  aesop (add simp [liftF, liftF'])


-- @@ L57-60 verbatim
@[simp]
lemma liftF'_liftF_succ {f : Fin (n + 1) → α} {x : Fin n} :
    liftF' (liftF (n := n + 1) f) x = f x.castSucc := by
  aesop (add simp [liftF, liftF']) (add safe (by omega))


-- @@ L62-64 verbatim
@[simp]
lemma liftF'_liftF : Function.LeftInverse liftF' (liftF (α := α) (n := n)) := by
  aesop (add simp [Function.LeftInverse, liftF, liftF'])


-- @@ L66-70 verbatim
@[simp]
lemma liftF'_liftF_eq : liftF' (liftF f') = f' := by unfold liftF' liftF; simp

lemma liftF_liftF'_of_lt (h : m < n) : liftF (liftF' (n := n) f) m = f m := by
  aesop (add simp liftF)


-- @@ L72-88 verbatim
@[simp]
lemma liftF_liftF'_succ : liftF (liftF' (n := n + 1) f) n = f n := by
  aesop (add simp liftF)

lemma liftF_eval {f : Fin n → α} {i : Fin n} :
    liftF f i.val = f i := by
  aesop (add simp liftF)

lemma lt_of_liftF_ne_zero {f : Fin n → α} {i : ℕ}
    (h : liftF f i ≠ 0) : i < n := by
  aesop (add simp liftF)

lemma liftF_ne_zero_of_lt {i : ℕ} (h : i < n) : liftF f' i ≠ 0 ↔ f' ⟨i, h⟩ ≠ 0 := by
  aesop (add simp liftF)

lemma liftF_eq_of_lt {i : ℕ} (h : i < n) : liftF f' i = f' ⟨i, h⟩ := by
  aesop (add simp liftF)


-- @@ L90-92 verbatim
@[simp]
lemma liftF_zero_eq_zero : liftF (fun (_ : Fin n) ↦ (0 : α)) = (fun _ ↦ (0 : α)) := by
  aesop (add simp liftF)


-- @@ L94-96 verbatim
@[simp]
lemma liftF'_zero_eq_zero : liftF' (fun _ ↦ (0 : α)) = (fun (_ : Fin n) ↦ (0 : α)) := by
  aesop (add simp liftF')


-- @@ L98-98 verbatim
abbrev contract (m : ℕ) (f : Fin n → α) := liftF (liftF' (n := m) (liftF f))


-- @@ L100-104 verbatim
open Fin (contract)

lemma contract_eq_liftF_of_lt {k : ℕ} (h₁ : k < m) :
    contract m f' k = liftF f' k := by
  aesop (add simp [contract, liftF, liftF'])


-- @@ L106-106 verbatim
attribute [simp] contract.eq_def


-- @@ L108-108 verbatim
variable {F : Type*} [Semiring F] {p : Polynomial F}


-- @@ L110-114 verbatim
open Polynomial

lemma eval_liftF_of_lt {f : Fin m → F} (h : n < m) :
    eval (liftF f n) p = eval (f ⟨n, h⟩) p := by
  aesop (add simp liftF)


-- @@ L116-118 verbatim
@[simp]
lemma liftF'_p_coeff {p : F[X]} {k : ℕ} {i : Fin k} : liftF' p.coeff i = p.coeff i := by
  simp [liftF']


-- @@ L120-120 verbatim
end Lift


-- @@ L122-122 verbatim
end Fin
