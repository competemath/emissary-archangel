import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic


-- @@ L4-11 verbatim
/-!
  TubalTensor/TransformDomain/FacewiseProduct.lean
  Facewise product △ (Section 6).

  The frontal facewise product of two tensors (viewed as arrays of
  frontal slices): (A △ B)_k := A_k * B_k (matrix product on each
  frontal slice independently).
-/


-- @@ L13-13 verbatim
namespace TubalTensor


-- @@ L15-15 verbatim
open Matrix


-- @@ L17-17 verbatim
variable {n : ℕ} {m p l : ℕ}


-- @@ L19-19 verbatim
/-! ## Facewise product (Section 6) -/


-- @@ L21-27 verbatim
/-- Facewise product of two arrays of frontal slices.
    `(A △ B) k := A k * B k` (ordinary matrix product on each slice). -/
noncomputable def facewise
    (A : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (B : Fin n → Matrix (Fin p) (Fin l) ℂ) :
    Fin n → Matrix (Fin m) (Fin l) ℂ :=
  fun k => A k * B k


-- @@ L29-29 verbatim
scoped notation:70 A " △ " B => facewise A B


-- @@ L31-35 verbatim
@[simp]
theorem facewise_apply
    (A : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (B : Fin n → Matrix (Fin p) (Fin l) ℂ) (k : Fin n) :
    (A △ B) k = A k * B k := rfl


-- @@ L37-37 verbatim
end TubalTensor
