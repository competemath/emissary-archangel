/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.FieldStatistics.Basic
public import Mathlib.Analysis.Complex.Basic

-- @@ L10-24 verbatim
/-!

# Exchange sign for field statistics

Suppose we have two fields `φ` and `ψ`, and the term `φψ`, if we swap them
`ψφ`, we may pick up a sign. This sign is called the exchange sign.
This sign is `-1` if both fields `ψ` and `φ` are fermionic and `1` otherwise.

In this module we define the exchange sign for general field statistics,
and prove some properties of it. Importantly:
- It is symmetric `exchangeSign_symm`.
- When multiplied with itself it is `1` `exchangeSign_mul_self`.
- It is a cocycle `exchangeSign_cocycle`.

-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
namespace FieldStatistic


-- @@ L30-30 verbatim
variable {𝓕 : Type}


-- @@ L32-66 verbatim
/-- The exchange sign, `exchangeSign`, is defined as the group homomorphism

  `FieldStatistic →* FieldStatistic →* ℂ`,

  for which `exchangeSign a b` is `-1` if both `a` and `b` are `fermionic` and `1` otherwise.
  The exchange sign is the sign one picks up on exchanging an operator or field `φ₁` of statistic
  `a` with an operator or field `φ₂` of statistic `b`, i.e. `φ₁φ₂ → φ₂φ₁`.

  The notation `𝓢(a, b)` is used for the exchange sign of `a` and `b`. -/
def exchangeSign : FieldStatistic →* FieldStatistic →* ℂ where
  toFun a :=
    {
      toFun := fun b =>
        match a, b with
        | bosonic, _ => 1
        | _, bosonic => 1
        | fermionic, fermionic => -1
      map_one' := by
        fin_cases a
        <;> simp
      map_mul' := fun c b => by
        fin_cases a <;>
          fin_cases b <;>
          fin_cases c <;>
          simp
    }
  map_one' := by
    ext b
    fin_cases b
    <;> simp
  map_mul' c b := by
    ext a
    fin_cases a
    <;> fin_cases b <;> fin_cases c
    <;> simp


-- @@ L68-69 verbatim
@[inherit_doc exchangeSign]
scoped[FieldStatistic] notation "𝓢(" a "," b ")" => exchangeSign a b


-- @@ L71-73 verbatim
/-- The exchange sign is symmetric. -/
lemma exchangeSign_symm (a b : FieldStatistic) : 𝓢(a, b) = 𝓢(b, a) := by
  fin_cases a <;> fin_cases b <;> rfl


-- @@ L75-77 verbatim
@[simp]
lemma exchangeSign_bosonic (a : FieldStatistic) : 𝓢(a, bosonic) = 1 := by
  fin_cases a <;> rfl


-- @@ L79-81 verbatim
@[simp]
lemma bosonic_exchangeSign (a : FieldStatistic) : 𝓢(bosonic, a) = 1 := by
  rw [exchangeSign_symm, exchangeSign_bosonic]


-- @@ L83-85 verbatim
@[simp]
lemma fermionic_exchangeSign_fermionic : 𝓢(fermionic, fermionic) = - 1 := by
  rfl


-- @@ L87-89 verbatim
lemma exchangeSign_eq_if (a b : FieldStatistic) :
    𝓢(a, b) = if a = fermionic ∧ b = fermionic then - 1 else 1 := by
  fin_cases a <;> fin_cases b <;> rfl


-- @@ L91-93 verbatim
@[simp]
lemma exchangeSign_mul_self (a b : FieldStatistic) : 𝓢(a, b) * 𝓢(a, b) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [exchangeSign]


-- @@ L95-97 verbatim
@[simp]
lemma exchangeSign_mul_self_swap (a b : FieldStatistic) : 𝓢(a, b) * 𝓢(b, a) = 1 := by
  fin_cases a <;> fin_cases b <;> simp [exchangeSign]


-- @@ L99-102 verbatim
lemma exchangeSign_ofList_cons (a : FieldStatistic)
    (s : 𝓕 → FieldStatistic) (φ : 𝓕) (φs : List 𝓕) :
    𝓢(a, ofList s (φ :: φs)) = 𝓢(a, s φ) * 𝓢(a, ofList s φs) := by
  rw [ofList_cons_eq_mul, map_mul]


-- @@ L104-107 verbatim
/-- The exchange sign is a cocycle. -/
lemma exchangeSign_cocycle (a b c : FieldStatistic) :
    𝓢(a, b * c) * 𝓢(b, c) = 𝓢(a, b) * 𝓢(a * b, c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp


-- @@ L109-109 verbatim
end FieldStatistic
