/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Order.Interval.Finset.Fin


-- @@ L11-13 verbatim
/-!
# Order intervals in `Fin`
-/


-- @@ L15-15 verbatim
open Finset


-- @@ L17-17 verbatim
namespace Fin


-- @@ L19-20 verbatim
public
lemma Iio_succ_eq_Iic_castSucc {n : ℕ} (k : Fin n) : Iio k.succ = Iic k.castSucc := rfl


-- @@ L22-22 verbatim
end Fin
