/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension
public import CompPoly.Fields.KoalaBear.Basic
public import Mathlib.Tactic.ReduceModChar


-- @@ L12-28 verbatim
/-!
# The degree-4 extension of KoalaBear

`KoalaBear[X] / (X^4 - 3)`, the challenge field used alongside the KoalaBear base field in
Plonky3-style STARKs.

Irreducibility of `X^4 - 3` is discharged by `Polynomial.irreducible_X_pow_four_sub_C_of_card`,
whose two hypotheses are single exponentiations in the base field:
`3^((p^4-1)/4) = 1` and `3^((p^2-1)/4) ≠ 1`. Both are closed by `reduce_mod_char`, which does
modular repeated squaring at elaboration time — no `native_decide`, and no generated
certificate file.

## Main definitions

* `KoalaBear.ext4Params`: the `BinomialParams` for `X^4 - 3`.
* `KoalaBear.Ext4`: the extension field itself.
-/


-- @@ L30-30 verbatim
@[expose] public section


-- @@ L32-32 verbatim
namespace KoalaBear


-- @@ L34-34 verbatim
open CompPoly.Extension Polynomial


-- @@ L36-43 verbatim
/--
The base-field cardinality as a bare numeral.

`reduce_mod_char` reads the modulus syntactically, so the irreducibility proof below needs a
numeral rather than the expression `fieldSize`. `qNum_eq` pins this second spelling to the first,
so the two cannot drift apart silently.
-/
private abbrev qNum : ℕ := 2130706433


-- @@ L45-45 verbatim
private theorem qNum_eq : qNum = fieldSize := by norm_num


-- @@ L47-53 verbatim
/-- The parameters of the quartic extension `KoalaBear[X] / (X^4 - 3)`. -/
def ext4Params : BinomialParams Field where
  d := 4
  W := 3
  two_le := by norm_num
  q := fieldSize
  card_eq := ZMod.card _


-- @@ L55-55 verbatim
@[simp] theorem ext4Params_d : ext4Params.d = 4 := rfl

-- @@ L56-56 verbatim
@[simp] theorem ext4Params_W : ext4Params.W = 3 := rfl

-- @@ L57-57 verbatim
@[simp] theorem ext4Params_q : ext4Params.q = fieldSize := rfl


-- @@ L59-68 verbatim
/-- `X^4 - 3` is irreducible over KoalaBear, by the collapsed Rabin criterion. -/
theorem ext4Params_poly_irreducible : Irreducible ext4Params.poly := by
  rw [BinomialParams.poly]
  refine irreducible_X_pow_four_sub_C_of_card (q := qNum) (ZMod.card _) (by decide)
    (by norm_num) (by norm_num) ?_ ?_
  · show (3 : ZMod qNum) ^ ((qNum ^ 4 - 1) / 4) = 1
    reduce_mod_char
  · show (3 : ZMod qNum) ^ ((qNum ^ 2 - 1) / 4) ≠ 1
    reduce_mod_char
    decide


-- @@ L70-70 verbatim
instance : Fact (Irreducible ext4Params.poly) := ⟨ext4Params_poly_irreducible⟩


-- @@ L72-74 verbatim
/-- The irreducibility fact in the form the general framework's `Field` instance consumes. -/
instance : Fact (Irreducible ext4Params.toExtensionParams.poly) :=
  ⟨ext4Params.toExtensionParams_poly ▸ ext4Params_poly_irreducible⟩


-- @@ L76-77 verbatim
/-- The degree-4 extension field of KoalaBear. -/
abbrev Ext4 : Type := CompPoly.Extension.Ext ext4Params.toExtensionParams


-- @@ L79-80 verbatim
/-- The adjoined fourth root of `3`, as an element of `Ext4`. -/
def ext4Gen : Ext4 := Ext.gen


-- @@ L82-90 verbatim
/--
`ext4Gen` is the framework's `Ext.gen`.

Deliberately **not** `@[simp]`: as a rewrite it fires before `ext4Gen_pow_four` can match, which
would knock that lemma out of the simp set. Use `simp [ext4Gen_eq_gen]` to reach the general
`Ext.gen` lemmas (`Ext.coeff_gen`, `Ext.gen_pow_d`) when the specialized ones below are not
enough.
-/
theorem ext4Gen_eq_gen : ext4Gen = Ext.gen := rfl


-- @@ L92-94 verbatim
/-- `ext4Gen` maps to the adjoined root of the specification. -/
@[simp] theorem toQuot_ext4Gen : Ext.toQuot ext4Gen = Ext.rt ext4Params.toExtensionParams :=
  Ext.toQuot_gen


-- @@ L96-98 verbatim
/-- **The defining relation**, as a theorem rather than only an executable check. -/
@[simp] theorem ext4Gen_pow_four : ext4Gen ^ 4 = Ext.ofBase (3 : Field) :=
  Ext.gen_pow_d_binomial ext4Params


-- @@ L100-102 verbatim
/-- `ext4Gen` is a root of `X^4 - 3`, in the form `aeval` expects. -/
theorem aeval_ext4Gen : aeval ext4Gen ext4Params.poly = 0 := by
  rw [← ext4Params.toExtensionParams_poly]; exact Ext.aeval_gen_poly


-- @@ L104-104 verbatim
@[simp] theorem card_ext4 : Fintype.card Ext4 = fieldSize ^ 4 := Ext.card_ext


-- @@ L106-106 verbatim
end KoalaBear
