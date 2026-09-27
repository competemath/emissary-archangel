/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module


public import LeanPool.LeanModularForms.Modularforms.Eisenstein


-- @@ L12-12 verbatim
/-! # MDifferentiableFunProp -/



-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open scoped Manifold UpperHalfPlane EisensteinSeries


-- @@ L19-19 verbatim
theorem E₄_MDifferentiable : MDiff E₄.toFun := E₄.holo'


-- @@ L21-26 verbatim
theorem E₆_MDifferentiable : MDiff E₆.toFun := E₆.holo'

/-
Register `MDifferentiable` as a `fun_prop` so that we can use it in `fun_prop`-based proofs.
To be upstreamed in mathlib PR [#33808](https://github.com/leanprover-community/mathlib4/pull/33808)
-/

-- @@ L27-27 verbatim
attribute [fun_prop] MDifferentiable


-- @@ L29-38 verbatim
attribute [fun_prop]
  MDifferentiable.add
  MDifferentiable.sub
  MDifferentiable.neg
  MDifferentiable.mul
  MDifferentiable.pow
  MDifferentiable.const_smul
  mdifferentiable_const
  E₄_MDifferentiable
  E₆_MDifferentiable
