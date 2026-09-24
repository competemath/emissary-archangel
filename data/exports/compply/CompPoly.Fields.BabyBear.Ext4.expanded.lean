/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension
public import CompPoly.Fields.BabyBear.Basic
public import Mathlib.Tactic.ReduceModChar


-- @@ L12-26 verbatim
/-!
# The degree-4 extension of BabyBear

`BabyBear[X] / (X^4 - 11)`, the challenge field used alongside the BabyBear base field in
RISC Zero and Plonky3.

Irreducibility of `X^4 - 11` is discharged by
`Polynomial.irreducible_X_pow_four_sub_C_of_card`, whose two hypotheses are single
exponentiations in the base field: `11^((p^4-1)/4) = 1` and `11^((p^2-1)/4) ≠ 1`.

## Main definitions

* `BabyBear.ext4Params`: the `BinomialParams` for `X^4 - 11`.
* `BabyBear.Ext4`: the extension field itself.
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
namespace BabyBear


-- @@ L32-32 verbatim
open CompPoly.Extension Polynomial


-- @@ L34-41 verbatim
/--
The base-field cardinality as a bare numeral.

`reduce_mod_char` reads the modulus syntactically, so the irreducibility proof below needs a
numeral rather than the expression `fieldSize`. `qNum_eq` pins this second spelling to the first,
so the two cannot drift apart silently.
-/
private abbrev qNum : ℕ := 2013265921


-- @@ L43-43 verbatim
private theorem qNum_eq : qNum = fieldSize := by norm_num


-- @@ L45-51 verbatim
/-- The parameters of the quartic extension `BabyBear[X] / (X^4 - 11)`. -/
def ext4Params : BinomialParams Field where
  d := 4
  W := 11
  two_le := by norm_num
  q := fieldSize
  card_eq := ZMod.card _


-- @@ L53-53 verbatim
@[simp] theorem ext4Params_d : ext4Params.d = 4 := rfl

-- @@ L54-54 verbatim
@[simp] theorem ext4Params_W : ext4Params.W = 11 := rfl

-- @@ L55-55 verbatim
@[simp] theorem ext4Params_q : ext4Params.q = fieldSize := rfl


-- @@ L57-66 verbatim
/-- `X^4 - 11` is irreducible over BabyBear, by the collapsed Rabin criterion. -/
theorem ext4Params_poly_irreducible : Irreducible ext4Params.poly := by
  rw [BinomialParams.poly]
  refine irreducible_X_pow_four_sub_C_of_card (q := qNum) (ZMod.card _) (by decide)
    (by norm_num) (by norm_num) ?_ ?_
  · show (11 : ZMod qNum) ^ ((qNum ^ 4 - 1) / 4) = 1
    reduce_mod_char
  · show (11 : ZMod qNum) ^ ((qNum ^ 2 - 1) / 4) ≠ 1
    reduce_mod_char
    decide


-- @@ L68-68 verbatim
instance : Fact (Irreducible ext4Params.poly) := ⟨ext4Params_poly_irreducible⟩


-- @@ L70-72 verbatim
/-- The irreducibility fact in the form the general framework's `Field` instance consumes. -/
instance : Fact (Irreducible ext4Params.toExtensionParams.poly) :=
  ⟨ext4Params.toExtensionParams_poly ▸ ext4Params_poly_irreducible⟩


-- @@ L74-75 verbatim
/-- The degree-4 extension field of BabyBear. -/
abbrev Ext4 : Type := CompPoly.Extension.Ext ext4Params.toExtensionParams


-- @@ L77-78 verbatim
/-- The adjoined fourth root of `11`, as an element of `Ext4`. -/
def ext4Gen : Ext4 := Ext.gen


-- @@ L80-88 verbatim
/--
`ext4Gen` is the framework's `Ext.gen`.

Deliberately **not** `@[simp]`: as a rewrite it fires before `ext4Gen_pow_four` can match, which
would knock that lemma out of the simp set. Use `simp [ext4Gen_eq_gen]` to reach the general
`Ext.gen` lemmas (`Ext.coeff_gen`, `Ext.gen_pow_d`) when the specialized ones below are not
enough.
-/
theorem ext4Gen_eq_gen : ext4Gen = Ext.gen := rfl


-- @@ L90-92 verbatim
/-- `ext4Gen` maps to the adjoined root of the specification. -/
@[simp] theorem toQuot_ext4Gen : Ext.toQuot ext4Gen = Ext.rt ext4Params.toExtensionParams :=
  Ext.toQuot_gen


-- @@ L94-96 verbatim
/-- **The defining relation**, as a theorem rather than only an executable check. -/
@[simp] theorem ext4Gen_pow_four : ext4Gen ^ 4 = Ext.ofBase (11 : Field) :=
  Ext.gen_pow_d_binomial ext4Params


-- @@ L98-100 verbatim
/-- `ext4Gen` is a root of `X^4 - 11`, in the form `aeval` expects. -/
theorem aeval_ext4Gen : aeval ext4Gen ext4Params.poly = 0 := by
  rw [← ext4Params.toExtensionParams_poly]; exact Ext.aeval_gen_poly


-- @@ L102-102 verbatim
@[simp] theorem card_ext4 : Fintype.card Ext4 = fieldSize ^ 4 := Ext.card_ext


-- @@ L104-104 verbatim
end BabyBear
