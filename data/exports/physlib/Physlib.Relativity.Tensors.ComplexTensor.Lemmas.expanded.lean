/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Basic

-- @@ L9-13 verbatim
/-!

## Lemmas related to complex Lorentz tensors.

-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Matrix

-- @@ L18-18 verbatim
open MatrixGroups

-- @@ L19-19 verbatim
open Complex

-- @@ L20-20 verbatim
open TensorProduct


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace complexLorentzTensor

-- @@ L25-25 verbatim
open TensorSpecies

-- @@ L26-26 verbatim
open Tensor


-- @@ L28-37 expanded
lemma antiSymm_contr_symm {A : complexLorentzTensor.Tensor (vecCons .up ![.up])}
    {S : complexLorentzTensor.Tensor (vecCons .down ![.down])} (hA : {A| μ ν=-(A| ν μ)}ᵀ)
    (hs : {S| μ ν=S| ν μ}ᵀ) : {A| μ ν⊗S| μ ν=-A| μ ν⊗S| μ ν}ᵀ :=
  by
  conv_lhs =>
    rw [hA, hs, prodT_permT_left, prodT_permT_right, contrT_comm, permT_permT, contrT_permT,
      contrT_permT, permT_permT]
  simp only [LinearMap.neg_apply, map_neg]
  congr 1
  apply permT_congr_eq_id
  decide


-- @@ L39-39 verbatim
end complexLorentzTensor


-- @@ L41-41 verbatim
end
