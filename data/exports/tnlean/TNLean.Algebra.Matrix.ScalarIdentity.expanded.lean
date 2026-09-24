/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace


-- @@ L9-13 verbatim
/-!
# Scalar identity matrices

This file records positivity and trace formulas for scalar multiples of identity matrices.
-/


-- @@ L15-15 verbatim
namespace Matrix


-- @@ L17-17 verbatim
namespace PosSemidef


-- @@ L19-24 verbatim
/-- A nonnegative scalar multiple of the identity matrix is positive semidefinite. -/
theorem smul_one {n α R : Type*} [DecidableEq n] [Ring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [CommSemiring α] [PartialOrder α] [StarRing α] [StarOrderedRing α]
    [Algebra α R] [StarModule α R] [PosSMulMono α R] {a : α} (ha : 0 ≤ a) :
    (a • (1 : Matrix n n R)).PosSemidef :=
  PosSemidef.one.smul ha


-- @@ L26-26 verbatim
end PosSemidef


-- @@ L28-28 verbatim
namespace PosDef


-- @@ L30-35 verbatim
/-- A positive scalar multiple of the identity matrix is positive definite. -/
theorem smul_one {n α R : Type*} [DecidableEq n] [Ring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [NoZeroDivisors R] [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulStrictMono α R] {a : α}
    (ha : 0 < a) : (a • (1 : Matrix n n R)).PosDef :=
  PosDef.one.smul ha


-- @@ L37-37 verbatim
end PosDef


-- @@ L39-43 verbatim
/-- The trace of a scalar multiple of the identity is the scalar multiple of the dimension. -/
theorem trace_smul_one {n α R : Type*} [Fintype n] [DecidableEq n] [AddCommMonoidWithOne R]
    [DistribSMul α R] (a : α) :
    trace (a • (1 : Matrix n n R)) = a • (Fintype.card n : R) := by
  rw [trace_smul, trace_one]


-- @@ L45-45 verbatim
end Matrix
