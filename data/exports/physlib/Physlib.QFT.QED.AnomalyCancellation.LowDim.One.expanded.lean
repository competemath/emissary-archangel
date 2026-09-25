/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.QED.AnomalyCancellation.Basic

-- @@ L9-13 verbatim
/-!
# The Pure U(1) case with 1 fermion

We show that in this case the charge must be zero.
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Nat

-- @@ L18-18 verbatim
open Finset


-- @@ L20-20 verbatim
namespace PureU1


-- @@ L22-22 verbatim
variable {n : ℕ}


-- @@ L24-24 verbatim
namespace One


-- @@ L26-30 verbatim
theorem solEqZero (S : (PureU1 1).LinSols) : S = 0 := by
  apply ACCSystemLinear.LinSols.ext
  funext i
  rw [Fin.fin_one_eq_zero i, ← Fin.sum_univ_one S.val]
  exact pureU1_linear S


-- @@ L32-32 verbatim
end One


-- @@ L34-34 verbatim
end PureU1
