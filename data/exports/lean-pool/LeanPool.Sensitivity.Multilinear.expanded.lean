/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import LeanPool.Sensitivity.Defs
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs


-- @@ L12-27 verbatim
/-!
# Multilinear Representation and Degree

Every Boolean function `f : (Fin n → Bool) → Bool` has a unique multilinear
polynomial representation over `ℤ`. This file defines the Möbius coefficients
of that representation and the multilinear degree of `f`.

## Main definitions

* `LeanPoolSensitivity.indicator` — the indicator assignment of a finite set
  of coordinates.
* `LeanPoolSensitivity.boolToInt` — the integer encoding of a Boolean value.
* `LeanPoolSensitivity.BoolFun.moebius` — the Möbius coefficient
  `c_S(f) = ∑_{T ⊆ S} (-1)^{|S|-|T|} f(1_T)`.
* `LeanPoolSensitivity.BoolFun.degree` — the multilinear degree of `f`.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace LeanPoolSensitivity


-- @@ L33-33 verbatim
variable {n : ℕ}


-- @@ L35-38 verbatim
/-- The Boolean assignment that is `true` on coordinates in `S` and `false`
elsewhere. -/
def indicator (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)


-- @@ L40-43 verbatim
@[simp]
theorem indicator_mem {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = true ↔ i ∈ S := by
  simp [indicator]


-- @@ L45-48 verbatim
@[simp]
theorem indicator_not_mem {S : Finset (Fin n)} {i : Fin n} :
    indicator S i = false ↔ i ∉ S := by
  simp [indicator]


-- @@ L50-51 verbatim
/-- Integer encoding of a Boolean value: `true ↦ 1` and `false ↦ 0`. -/
def boolToInt (b : Bool) : ℤ := if b then 1 else 0


-- @@ L53-53 verbatim
@[simp] theorem boolToInt_true : boolToInt true = 1 := rfl

-- @@ L54-54 verbatim
@[simp] theorem boolToInt_false : boolToInt false = 0 := rfl


-- @@ L56-56 verbatim
namespace BoolFun


-- @@ L58-64 verbatim
/-- The Möbius coefficient of `f` at `S`: the coefficient of the monomial
`∏_{i ∈ S} x_i` in the unique multilinear polynomial representing `f`,
computed by inclusion–exclusion as
`c_S(f) = ∑_{T ⊆ S} (-1)^{|S|-|T|} f(1_T)`. -/
def moebius (f : BoolFun n) (S : Finset (Fin n)) : ℤ :=
  ∑ T ∈ S.powerset,
    (-1) ^ (S.card - T.card) * boolToInt (f (indicator T))


-- @@ L66-70 verbatim
/-- The multilinear degree of `f`: the maximum cardinality of `S` for which
the Möbius coefficient `c_S(f)` is nonzero. -/
noncomputable def degree (f : BoolFun n) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => f.moebius S ≠ 0)).sup
    Finset.card


-- @@ L72-77 verbatim
/-- The multilinear degree of `f` is at most `n`. -/
theorem degree_le (f : BoolFun n) : f.degree ≤ n := by
  apply Finset.sup_le
  intro S hS
  simp only [Finset.mem_filter] at hS
  simpa using Finset.card_le_univ S


-- @@ L79-90 verbatim
/-- If the multilinear degree is positive, there exists a "witness" set `S`
of cardinality equal to the degree at which the Möbius coefficient is
nonzero. -/
theorem exists_degree_witness (f : BoolFun n) (hd : 0 < f.degree) :
    ∃ S : Finset (Fin n), S.card = f.degree ∧ f.moebius S ≠ 0 := by
  unfold degree at hd ⊢
  set F := (Finset.univ : Finset (Finset (Fin n))).filter (fun S => f.moebius S ≠ 0)
  have hne : F.Nonempty := by
    by_contra h
    simp_all
  obtain ⟨S, hS, heq⟩ := Finset.exists_mem_eq_sup F hne Finset.card
  exact ⟨S, heq.symm, (Finset.mem_filter.mp hS).2⟩


-- @@ L92-92 verbatim
end BoolFun


-- @@ L94-94 verbatim
end LeanPoolSensitivity
