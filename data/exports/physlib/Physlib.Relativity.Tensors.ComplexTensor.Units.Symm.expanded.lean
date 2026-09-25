/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Units.Basic

-- @@ L9-13 verbatim
/-!

## Symmetry lemmas relating to units

-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Matrix


-- @@ L19-19 verbatim
namespace complexLorentzTensor


-- @@ L21-25 verbatim
/-!

## Symmetry properties

-/

-- @@ L26-26 verbatim
open TensorSpecies

-- @@ L27-27 verbatim
open Tensor


-- @@ L29-32 verbatim
/-- Swapping indices of `coContrUnit` returns `contrCoUnit`: `{δ' | μ ν = δ | ν μ}ᵀ`. -/
lemma coContrUnit_symm : {δ' | μ ν = δ | ν μ}ᵀ := by
  rw [coContrUnit, unitTensor_eq_permT_dual]
  rfl


-- @@ L34-37 verbatim
/-- Swapping indices of `contrCoUnit` returns `coContrUnit`: `{δ | μ ν = δ' | ν μ}ᵀ`. -/
lemma contrCoUnit_symm : {δ | μ ν = δ' | ν μ}ᵀ := by
  rw [contrCoUnit, unitTensor_eq_permT_dual]
  rfl


-- @@ L39-43 verbatim
/-- Swapping indices of `dualLeftLeftUnit` returns
  `leftDualLeftUnit`: `{δL' | α α' = δL | α' α}ᵀ`. -/
lemma dualLeftLeftUnit_symm : {δL' | α α' = δL | α' α}ᵀ := by
  rw [dualLeftLeftUnit, unitTensor_eq_permT_dual]
  rfl


-- @@ L45-49 verbatim
/-- Swapping indices of `leftDualLeftUnit` returns
  `dualLeftLeftUnit`: `{δL | α α' = δL' | α' α}ᵀ`. -/
lemma leftDualLeftUnit_symm : {δL | α α' = δL' | α' α}ᵀ := by
  rw [leftDualLeftUnit, unitTensor_eq_permT_dual]
  rfl


-- @@ L51-56 verbatim
/-- Swapping indices of `dualRightRightUnit` returns `rightDualRightUnit`:
`{δR' | β β' = δR | β' β}ᵀ`.
-/
lemma dualRightRightUnit_symm : {δR' | β β' = δR | β' β}ᵀ := by
  rw [dualRightRightUnit, unitTensor_eq_permT_dual]
  rfl


-- @@ L58-63 verbatim
/-- Swapping indices of `rightDualRightUnit` returns `dualRightRightUnit`:
`{δR | β β' = δR' | β' β}ᵀ`.
-/
lemma rightDualRightUnit_symm : {δR | β β' = δR' | β' β}ᵀ := by
  rw [rightDualRightUnit, unitTensor_eq_permT_dual]
  rfl


-- @@ L65-65 verbatim
end complexLorentzTensor
