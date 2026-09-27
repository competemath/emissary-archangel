/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import LeanPool.BrauerGroupNew.Subfield.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic


-- @@ L12-16 verbatim
/-!
# LeanPool.BrauerGroupNew.Subfield.FiniteDimensional

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Subfield.FiniteDimensional`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace SubField

-- @@ L21-21 verbatim
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] {L : SubField K A}


-- @@ L23-23 verbatim
instance [FiniteDimensional K A] : FiniteDimensional K L := .finiteDimensional_subalgebra L.1


-- @@ L25-25 verbatim
end SubField
