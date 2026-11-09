/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.CyclotomicUnits.KummerLogFormal
public import BernoulliRegular.CyclotomicUnits.KummerLogNormalization
public import BernoulliRegular.CyclotomicUnits.KummerLogTrace


-- @@ L12-19 verbatim
/-!
# Kummer logarithm coefficient congruence

This file specializes the formal coefficient identity from `KummerLogFormal`
at the residue of the Kummer column.  The specialization is still a formal
mod-`p` statement; the final bridge to concrete matrix entries is recorded
separately so it cannot be hidden behind a bundled hypothesis.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open NumberField

-- @@ L26-26 verbatim
open NumberField.IsCMField

-- @@ L27-27 verbatim
open BernoulliRegular.Reflection.Local

-- @@ L28-28 verbatim
open scoped BigOperators NumberField


-- @@ L30-30 verbatim
namespace BernoulliRegular

-- @@ L31-31 verbatim
namespace CyclotomicUnits


-- @@ L33-33 verbatim
open PadicLogSetup PadicLogSetup.DworkParameter


-- @@ L35-35 verbatim
variable (p : ℕ) [Fact p.Prime]

-- @@ L36-36 verbatim
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L37-37 verbatim
variable [NumberField.IsCMField K]

-- @@ L38-40 verbatim
/-- Matrix row `j` corresponds to the mathematical index `j + 1`. -/
def kummerLogRowIndex (j : Fin (kummerLogRank p)) : ℕ :=
  (j : ℕ) + 1


-- @@ L42-46 verbatim
omit [Fact p.Prime] in
@[simp]
theorem kummerLogRowIndex_eq (j : Fin (kummerLogRank p)) :
    kummerLogRowIndex (p := p) j = (j : ℕ) + 1 :=
  rfl


-- @@ L48-51 verbatim
omit [Fact p.Prime] in
theorem kummerLogRowIndex_one_le (j : Fin (kummerLogRank p)) :
    1 ≤ kummerLogRowIndex (p := p) j := by
  simp [kummerLogRowIndex]


-- @@ L53-64 verbatim
omit [Fact p.Prime] in
theorem two_mul_kummerLogRowIndex_le_sub_three
    (j : Fin (kummerLogRank p)) :
    2 * kummerLogRowIndex (p := p) j ≤ p - 3 := by
  have hjle : (j : ℕ) + 1 ≤ kummerLogRank p :=
    Nat.succ_le_of_lt j.isLt
  have hmulrank : 2 * kummerLogRank p ≤ p - 3 := by
    simpa [kummerLogRank, Nat.mul_comm] using
      Nat.div_mul_le_self (p - 3) 2
  have hle : 2 * ((j : ℕ) + 1) ≤ 2 * kummerLogRank p :=
    Nat.mul_le_mul_left 2 hjle
  simpa [kummerLogRowIndex] using hle.trans hmulrank


-- @@ L66-70 verbatim
theorem rationalPadicIntegerToZMod_teichmuller_pow_sub_one
    (z : ZMod p) (n : ℕ) :
    rationalPadicIntegerToZMod p (rationalPadicTeichmuller p z ^ n - 1) =
      z ^ n - 1 := by
  rw [map_sub, map_pow, rationalPadicIntegerToZMod_teichmuller, map_one]


-- @@ L72-79 verbatim
theorem rationalPadicIntegerToZMod_teichmuller_kummerLogColumnIndex
    (hp_three : 3 ≤ p) (a : Fin (kummerLogRank p)) :
    rationalPadicIntegerToZMod p
        (rationalPadicTeichmuller p
          (kummerLogColumnIndex (p := p) hp_three a : ZMod p)) =
      (kummerLogColumnIndex (p := p) hp_three a : ZMod p) :=
  rationalPadicIntegerToZMod_teichmuller (p := p)
    (kummerLogColumnIndex (p := p) hp_three a : ZMod p)


-- @@ L81-92 verbatim
/-- The denominator units needed by the row selected in the Kummer matrix. -/
theorem formalKummerLogCoeffModP_column_denominators_isUnit
    (_hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    IsUnit (((Nat.factorial (2 * kummerLogRowIndex (p := p) j) : ℕ) :
        ZMod p)) ∧
      IsUnit (((_root_.bernoulli (2 * kummerLogRowIndex (p := p) j)).den :
        ℕ) : ZMod p) ∧
        IsUnit ((2 * kummerLogRowIndex (p := p) j : ℕ) : ZMod p) :=
  reducedKummerLogCoeffFactor_denominators_isUnit
    (p := p) (j := kummerLogRowIndex (p := p) j)
    (kummerLogRowIndex_one_le (p := p) j)
    (two_mul_kummerLogRowIndex_le_sub_three (p := p) j)


-- @@ L94-101 verbatim
/-- The unit factor for the selected matrix row is nonzero modulo `p`. -/
theorem formalKummerLogCoeffModP_column_unit_ne_zero
    (_hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) ≠ 0 :=
  formalKummerLogCoeffModP_unit_ne_zero
    (p := p) (j := kummerLogRowIndex (p := p) j)
    (kummerLogRowIndex_one_le (p := p) j)
    (two_mul_kummerLogRowIndex_le_sub_three (p := p) j)


-- @@ L103-115 verbatim
/-- CU-11e: specialization of the formal coefficient identity at the Kummer
column residue. -/
theorem formalKummerLogCoeffModP_eval_kummerLogColumnIndex
    (hp_three : 3 ≤ p) (_hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    Polynomial.eval (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) =
      (kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
          bernoulliFactor p (kummerLogRowIndex (p := p) j)) *
        ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
            (2 * kummerLogRowIndex (p := p) j) - 1) :=
  formalKummerLogCoeffModP_eval p (kummerLogRowIndex (p := p) j)
    (kummerLogColumnIndex (p := p) hp_three a : ZMod p)


-- @@ L117-124 verbatim
/-- The right-hand side of Kummer's logarithm coefficient congruence for the
selected row and column. -/
def kummerLogCoeffCongrRhs
    (hp_three : 3 ≤ p) (j a : Fin (kummerLogRank p)) : ZMod p :=
  kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
    bernoulliFactor p (kummerLogRowIndex (p := p) j) *
      ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
        (2 * kummerLogRowIndex (p := p) j) - 1)


-- @@ L126-136 verbatim
/-- Formal coefficient congruence after specializing the scalar at the Kummer
column residue, in the normalized-family coefficient convention. -/
theorem formalKummerLogCoeff_congr
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    Polynomial.eval (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) =
      kummerLogCoeffCongrRhs (p := p) hp_three j a := by
  rw [formalKummerLogCoeffModP_eval_kummerLogColumnIndex
    (p := p) (hp_three := hp_three) (_hp_five := hp_five)]
  rfl


-- @@ L138-150 verbatim
/-- Final normalized-family coefficient API: the formal Kummer coefficient
specializes with unit factor `kummerLogUnitFactor = -((2*j)!)⁻¹`. -/
theorem normalizedKummerLogCoeff_congr
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    Polynomial.eval (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) =
      kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
        bernoulliFactor p (kummerLogRowIndex (p := p) j) *
          ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
            (2 * kummerLogRowIndex (p := p) j) - 1) :=
  formalKummerLogCoeffModP_eval_kummerLogColumnIndex
    (p := p) hp_three hp_five j a


-- @@ L152-157 verbatim
/-- The unit factor appearing in the row of the formal Kummer congruence is
nonzero. -/
theorem kummerLogCoeffCongrRhs_unit_ne_zero
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) ≠ 0 :=
  formalKummerLogCoeffModP_column_unit_ne_zero (p := p) hp_five j


-- @@ L159-164 verbatim
/-- The squared-family unit factor.  The normalized `C⁺` coefficient uses
`kummerLogUnitFactor`; the currently implemented concrete logarithm columns
come from the squared real cyclotomic-unit family, so their exact coefficient
has this extra factor `2`. -/
def squaredKummerLogUnitFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  (2 : ZMod p) * kummerLogUnitFactor p j


-- @@ L166-172 verbatim
theorem two_zmod_ne_zero_of_five_le (hp_five : 5 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hp_dvd : p ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd
  omega


-- @@ L174-177 verbatim
/-- The extra squared-family factor `2` is a unit modulo `p`. -/
theorem two_zmod_isUnit_of_five_le (hp_five : 5 ≤ p) :
    IsUnit (2 : ZMod p) :=
  isUnit_iff_ne_zero.mpr (two_zmod_ne_zero_of_five_le (p := p) hp_five)


-- @@ L179-185 verbatim
/-- The squared-family unit factor is nonzero in the Kummer row range. -/
theorem squaredKummerLogUnitFactor_ne_zero
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    squaredKummerLogUnitFactor p (kummerLogRowIndex (p := p) j) ≠ 0 :=
  mul_ne_zero
    (two_zmod_ne_zero_of_five_le (p := p) hp_five)
    (kummerLogCoeffCongrRhs_unit_ne_zero (p := p) hp_five j)


-- @@ L187-192 verbatim
/-- The squared-family unit factor is a unit in the Kummer row range. -/
theorem squaredKummerLogUnitFactor_isUnit
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    IsUnit (squaredKummerLogUnitFactor p (kummerLogRowIndex (p := p) j)) :=
  isUnit_iff_ne_zero.mpr
    (squaredKummerLogUnitFactor_ne_zero (p := p) hp_five j)


-- @@ L194-198 verbatim
/-- The determinant-scale factor contributed by multiplying every concrete
Kummer logarithm entry by `2` is nonzero. -/
theorem two_pow_kummerLogRank_zmod_ne_zero (hp_five : 5 ≤ p) :
    (2 : ZMod p) ^ kummerLogRank p ≠ 0 :=
  pow_ne_zero _ (two_zmod_ne_zero_of_five_le (p := p) hp_five)


-- @@ L200-205 verbatim
/-- The determinant-scale factor contributed by the squared-family `2` is a
unit. -/
theorem two_pow_kummerLogRank_zmod_isUnit (hp_five : 5 ≤ p) :
    IsUnit ((2 : ZMod p) ^ kummerLogRank p) :=
  isUnit_iff_ne_zero.mpr
    (two_pow_kummerLogRank_zmod_ne_zero (p := p) hp_five)


-- @@ L207-221 verbatim
omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- Multiplying every entry of a square matrix over `ZMod p` by the
squared-family factor `2` does not affect determinant nonvanishing. -/
theorem matrix_det_two_smul_ne_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hp_five : 5 ≤ p) (M : Matrix ι ι (ZMod p)) :
    Matrix.det ((2 : ZMod p) • M) ≠ 0 ↔ Matrix.det M ≠ 0 := by
  rw [Matrix.det_smul]
  constructor
  · intro h hM
    exact h (by simp [hM])
  · intro hM
    exact mul_ne_zero
      (pow_ne_zero _ (two_zmod_ne_zero_of_five_le (p := p) hp_five)) hM


-- @@ L223-230 verbatim
/-- The right-hand side for the currently implemented squared-family
logarithm columns. -/
def squaredKummerLogCoeffCongrRhs
    (hp_three : 3 ≤ p) (j a : Fin (kummerLogRank p)) : ZMod p :=
  squaredKummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
    bernoulliFactor p (kummerLogRowIndex (p := p) j) *
      ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
        (2 * kummerLogRowIndex (p := p) j) - 1)


-- @@ L232-238 verbatim
theorem squaredKummerLogCoeffCongrRhs_eq_two_mul
    (hp_three : 3 ≤ p) (j a : Fin (kummerLogRank p)) :
    squaredKummerLogCoeffCongrRhs (p := p) hp_three j a =
      (2 : ZMod p) * kummerLogCoeffCongrRhs (p := p) hp_three j a := by
  simp [squaredKummerLogCoeffCongrRhs, squaredKummerLogUnitFactor,
    kummerLogCoeffCongrRhs]
  ring


-- @@ L240-251 verbatim
/-- Formal assembled congruence in the squared-family normalization.  This is
the exact formal coefficient shape matching a column already rewritten as
`2 * log Q_a(varpi)`. -/
theorem formalSquaredKummerLogCoeff_congr
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    (2 : ZMod p) *
        Polynomial.eval (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
          (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) =
      squaredKummerLogCoeffCongrRhs (p := p) hp_three j a := by
  rw [formalKummerLogCoeff_congr (p := p) hp_three hp_five j a,
    squaredKummerLogCoeffCongrRhs_eq_two_mul]


-- @@ L253-253 verbatim
end CyclotomicUnits

-- @@ L254-254 verbatim
end BernoulliRegular


-- @@ L256-256 verbatim
end
