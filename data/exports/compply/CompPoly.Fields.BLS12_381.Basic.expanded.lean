/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Fields.PrattCertificate

-- @@ L9-14 verbatim
/-!
  # The BLS12-381 scalar prime field

  `r` of the BLS12-381 curve, 255-bit, 2-adicity 32
  ([IETF pairing-friendly-curves draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-pairing-friendly-curves/)).
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace BLS12_381


-- @@ L20-22 verbatim
@[reducible]
def scalarFieldSize : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001


-- @@ L24-24 verbatim
abbrev ScalarField := ZMod scalarFieldSize


-- @@ L26-44 verbatim
theorem ScalarField_is_prime : Nat.Prime scalarFieldSize := by
  unfold scalarFieldSize
  refine PrattCertificate'.out (p := scalarFieldSize) ⟨7, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 32, 3, 11, 19, 10177, 125527, 859267, 906349 ^ 2, 2508409, 2529403, 52437899,
    254760293 ^ 2] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 32 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 19 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 10177 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 125527 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 859267 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 906349 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 2508409 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 2529403 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 52437899 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 254760293 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)


-- @@ L46-46 verbatim
instance : Fact (Nat.Prime scalarFieldSize) := ⟨ScalarField_is_prime⟩


-- @@ L48-48 verbatim
instance : Field ScalarField := ZMod.instField scalarFieldSize


-- @@ L50-50 verbatim
end BLS12_381
