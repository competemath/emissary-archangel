/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesForMathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Defs


-- @@ L21-25 verbatim
/-!
# Right ideals

This file gives the basic API for right ideals.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
universe u


-- @@ L31-31 verbatim
namespace RightIdeal


-- @@ L33-33 verbatim
section Semiring


-- @@ L35-35 verbatim
variable {R : Type u} [Semiring R]


-- @@ L37-39 verbatim
@[ext]
theorem ext {I J : RightIdeal R} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  Submodule.ext h


-- @@ L41-43 verbatim
/-- A right ideal is closed under multiplication on the right. -/
theorem mul_mem_right (I : RightIdeal R) {a : R} (b : R) (ha : a ∈ I) : a * b ∈ I :=
  I.smul_mem (MulOpposite.op b) ha


-- @@ L45-45 verbatim
end Semiring


-- @@ L47-47 verbatim
section CommSemiring


-- @@ L49-49 verbatim
variable {R : Type u} [CommSemiring R]


-- @@ L51-59 verbatim
/-- A right ideal in a commutative semiring, regarded as an ideal. -/
def toIdeal (I : RightIdeal R) : Ideal R where
  carrier := (I : Set R)
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro r x hx
    rw [smul_eq_mul, mul_comm]
    exact I.mul_mem_right r hx


-- @@ L61-63 verbatim
@[simp]
theorem mem_toIdeal {I : RightIdeal R} {x : R} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl


-- @@ L65-73 verbatim
/-- An ideal in a commutative semiring, regarded as a right ideal. -/
def _root_.Ideal.toRightIdeal (I : Ideal R) : RightIdeal R where
  carrier := (I : Set R)
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro r x hx
    rw [MulOpposite.smul_eq_mul_unop, mul_comm]
    exact I.mul_mem_left r.unop hx


-- @@ L75-78 verbatim
@[simp]
theorem _root_.Ideal.mem_toRightIdeal {I : Ideal R} {x : R} :
    x ∈ I.toRightIdeal ↔ x ∈ I :=
  Iff.rfl


-- @@ L80-82 verbatim
@[simp]
theorem toIdeal_toRightIdeal (I : RightIdeal R) : I.toIdeal.toRightIdeal = I :=
  rfl


-- @@ L84-86 verbatim
@[simp]
theorem _root_.Ideal.toRightIdeal_toIdeal (I : Ideal R) : I.toRightIdeal.toIdeal = I :=
  rfl


-- @@ L88-94 verbatim
/-- Over a commutative semiring, right ideals and ideals are order isomorphic. -/
def orderIsoIdeal (R : Type u) [CommSemiring R] : RightIdeal R ≃o Ideal R where
  toFun := toIdeal
  invFun := Ideal.toRightIdeal
  left_inv := toIdeal_toRightIdeal
  right_inv := Ideal.toRightIdeal_toIdeal
  map_rel_iff' := Iff.rfl


-- @@ L96-96 verbatim
end CommSemiring


-- @@ L98-98 verbatim
end RightIdeal
