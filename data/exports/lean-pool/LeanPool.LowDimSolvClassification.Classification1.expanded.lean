/-
Copyright (c) 2026 the LieLean team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Lie.Solvable
import LeanPool.LowDimSolvClassification.GeneralResults
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.NormNum.GCD


-- @@ L18-20 verbatim
/-!
# LeanPool.LowDimSolvClassification.Classification1
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open Module

-- @@ L25-28 verbatim
open Submodule

-- `LieRing.ofAssociativeRing` is a local instance in Mathlib (a `def`, not a global instance), so
-- we re-enable it locally to view the commutative ring `K` as a Lie ring over itself.

-- @@ L29-29 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L31-31 verbatim
namespace LieAlgebra

-- @@ L32-32 verbatim
namespace Dim1


-- @@ L34-34 verbatim
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]


-- @@ L36-36 verbatim
section classification_dim_1


-- @@ L38-45 verbatim
theorem abelian (h : Module.finrank K L = 1) : IsLieAbelian L :=by
  simp only [IsLieAbelian]
  constructor
  intro x y
  have := Module.finite_of_finrank_eq_succ h
  have B := Module.finBasisOfFinrankEq K L h
  rw [Basis.repr_fin_one B x, Basis.repr_fin_one B y]
  simp


-- @@ L47-67 verbatim
theorem classification (h : Module.finrank K L = 1) :
    Nonempty (L ≃ₗ⁅K⁆ K) := by
  have := abelian h
  have := Module.finite_of_finrank_eq_succ h
  have B := Module.finBasisOfFinrankEq K L h
  constructor
  exact ({
    toFun := fun x ↦ B.repr x 0,
    invFun := fun x ↦ x • B 0,
    left_inv := by
      intro x
      simp only
      rw [← Basis.repr_fin_one B x]
    right_inv := fun _ => by simp
    map_add' := by simp
    map_smul' := by simp
    map_lie' := by
      intro x y
      rw [trivial_lie_zero L L x y]
      simp [Bracket.bracket, mul_comm]
  })


-- @@ L69-69 verbatim
end classification_dim_1


-- @@ L71-71 verbatim
section corollaries_dim_1


-- @@ L73-76 verbatim
theorem _root_.LieAlgebra.Dim1.solvable (dim1 : Module.finrank K L = 1) :
    LieAlgebra.IsSolvable L := by
  obtain a := abelian dim1
  apply LieAlgebra.ofAbelianIsSolvable


-- @@ L78-78 verbatim
end corollaries_dim_1


-- @@ L80-80 verbatim
end Dim1


-- @@ L82-82 verbatim
end LieAlgebra
