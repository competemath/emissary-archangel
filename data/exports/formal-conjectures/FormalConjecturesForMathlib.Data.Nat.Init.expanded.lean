/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Data.Nat.Init


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Nat

-- @@ L23-23 verbatim
variable {a b c : ℕ}


-- @@ L25-26 verbatim
@[simp] protected lemma dvd_add_mul_self : a ∣ b + c * a ↔ a ∣ b := by
  rw [Nat.dvd_add_left (Nat.dvd_mul_left _ _)]


-- @@ L28-29 verbatim
@[simp] protected lemma dvd_add_self_mul : a ∣ b + a * c ↔ a ∣ b := by
  rw [Nat.mul_comm, Nat.dvd_add_mul_self]


-- @@ L31-32 verbatim
@[simp] protected lemma dvd_mul_self_add : a ∣ b * a + c ↔ a ∣ c := by
  rw [Nat.add_comm, Nat.dvd_add_mul_self]


-- @@ L34-35 verbatim
@[simp] protected lemma dvd_self_mul_add : a ∣ a * b + c ↔ a ∣ c := by
  rw [Nat.mul_comm, Nat.dvd_mul_self_add]


-- @@ L37-40 verbatim
@[simp] lemma dvd_sub_iff_right' (hab : a ∣ b) : a ∣ b - c ↔ a ∣ c ∨ b ≤ c := by
  obtain hbc | hcb := b.le_total c
  · simp [*]
  · simp +contextual [Nat.dvd_sub_iff_right, Nat.le_antisymm hcb, *]


-- @@ L42-45 verbatim
@[simp] lemma dvd_sub_iff_left' (hac : a ∣ c) : a ∣ b - c ↔ a ∣ b ∨ b ≤ c := by
  obtain hbc | hcb := b.le_total c
  · simp [*]
  · simp +contextual [Nat.dvd_sub_iff_left, ← Nat.le_antisymm hcb, *]


-- @@ L47-48 verbatim
@[simp] protected lemma dvd_sub_mul_self : a ∣ b - c * a ↔ a ∣ b ∨ b ≤ c * a := by
  rw [Nat.dvd_sub_iff_left' (Nat.dvd_mul_left _ _)]


-- @@ L50-51 verbatim
@[simp] protected lemma dvd_sub_self_mul : a ∣ b - a * c ↔ a ∣ b ∨ b ≤ c * a := by
  rw [Nat.mul_comm, Nat.dvd_sub_mul_self]


-- @@ L53-54 verbatim
@[simp] protected lemma dvd_mul_self_sub : a ∣ b * a - c ↔ a ∣ c ∨ b * a ≤ c := by
  rw [Nat.dvd_sub_iff_right' (Nat.dvd_mul_left _ _)]


-- @@ L56-57 verbatim
@[simp] protected lemma dvd_self_mul_sub : a ∣ a * b - c ↔ a ∣ c ∨ b * a ≤ c := by
  rw [Nat.mul_comm, Nat.dvd_mul_self_sub]


-- @@ L59-59 verbatim
end Nat
