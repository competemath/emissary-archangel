/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.TransferMatrix
import QICLean.Kraus.Transfer


-- @@ L9-14 verbatim
/-!
# Transfer-matrix representation of MPS transfer maps

This file relates the generic transfer matrix of a linear map to the transfer
map associated with an MPS tensor.
-/


-- @@ L16-16 verbatim
open scoped Matrix BigOperators Kronecker


-- @@ L18-18 verbatim
namespace MPSTensor


-- @@ L20-20 verbatim
variable {d D : ℕ}


-- @@ L22-31 verbatim
/-- The MPS transfer map `E_A(X) = ∑ᵢ Aᵢ X Aᵢ†` has transfer matrix
`∑ᵢ Āᵢ ⊗ₖ Aᵢ`.

This relates Wolf's Section 2.2 transfer matrix for quantum channels to the MPS
transfer operator. -/
theorem transferMatrix_eq (A : MPSTensor d D) :
    transferMatrix (Kraus.transferMap A) =
      ∑ n : Fin d,
        (A n).map (starRingEnd ℂ) ⊗ₖ A n :=
  transferMatrix_kraus A _ (fun X => by simp)


-- @@ L33-33 verbatim
end MPSTensor
