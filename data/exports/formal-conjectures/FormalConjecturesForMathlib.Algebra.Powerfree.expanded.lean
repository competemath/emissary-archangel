/-
Copyright 2026 The Formal Conjectures Authors.

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


public import Mathlib.Algebra.Squarefree.Basic


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
variable {M M₀ : Type*} {r m : M} {k : ℕ}


-- @@ L25-25 verbatim
section Monoid

-- @@ L26-26 verbatim
variable [Monoid M]


-- @@ L28-29 verbatim
def Powerfree (k : ℕ) (m : M) : Prop :=
  ∀ ⦃x : M⦄, x ^ k ∣ m → IsUnit x


-- @@ L31-32 verbatim
theorem Powerfree.of_le {a b : ℕ} (hab : a ≤ b) (hm : Powerfree a m) :
  Powerfree b m := fun x hx => hm (dvd_of_mul_right_dvd (pow_mul_pow_sub x hab ▸ hx))


-- @@ L34-35 verbatim
theorem Powerfree.of_dvd (hrm : r ∣ m) (hm : Powerfree k m) :
    Powerfree k r := fun _ hx => hm (hx.trans hrm)


-- @@ L37-38 verbatim
theorem powerfree_congr (hrm : Associated r m) : Powerfree k r ↔ Powerfree k m :=
  ⟨fun h => h.of_dvd hrm.dvd', fun h => h.of_dvd hrm.dvd⟩


-- @@ L40-42 verbatim
@[simp]
theorem powerfree_neg [HasDistribNeg M] : Powerfree k (-m) ↔ Powerfree k m :=
  powerfree_congr (Associated.refl m).neg_left


-- @@ L44-47 verbatim
@[simp]
theorem powerfree_two {m : M} : Powerfree 2 m ↔ Squarefree m where
  mp h x hx := h (sq x ▸ hx)
  mpr h x hx := h x (sq x ▸ hx)


-- @@ L49-49 verbatim
end Monoid


-- @@ L51-51 verbatim
section CommMonoid

-- @@ L52-52 verbatim
variable [CommMonoid M]


-- @@ L54-55 verbatim
theorem IsUnit.powerfree (h : IsUnit m) (hk : k ≠ 0) :
    Powerfree k m := fun _ hx => (isUnit_pow_iff hk).1 (isUnit_of_dvd_unit hx h)


-- @@ L57-59 verbatim
@[simp]
theorem powerfree_one (hk : k ≠ 0) : Powerfree k (1 : M) :=
  isUnit_one.powerfree hk


-- @@ L61-70 verbatim
theorem Irreducible.powerfree (h : Irreducible m) (hk : 2 ≤ k) :
    Powerfree k m := by
  rintro y ⟨z, hz⟩
  induction k with
  | zero => grind
  | succ n ih =>
  rw [pow_succ, mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact (isUnit_pow_iff (by linarith)).1 hu
  · apply isUnit_of_mul_isUnit_left hu


-- @@ L72-72 verbatim
end CommMonoid


-- @@ L74-78 verbatim
@[simp]
theorem not_powerfree_zero [MonoidWithZero M₀] [Nontrivial M₀] (k : ℕ) :
    ¬ Powerfree k (0 : M₀) := by
  rw [Powerfree, not_forall]
  exact ⟨0, by simp⟩


-- @@ L80-81 verbatim
theorem Prime.powerfree [CommMonoidWithZero M₀] [IsCancelMulZero M₀] {m : M₀} (h : Prime m)
    (hk : 2 ≤ k) : Powerfree k m := h.irreducible.powerfree hk
