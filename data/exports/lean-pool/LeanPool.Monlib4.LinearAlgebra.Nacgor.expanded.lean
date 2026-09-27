/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp


-- @@ L10-15 verbatim
/-!
 # Normed additive commutative groups of rings

This file contains the `NormedAddCommGroupOfRing` class, which bundles the
ring structure together with the normed additive commutative group structure.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open scoped BigOperators


-- @@ L21-22 verbatim
/-- A ring whose additive group is a normed additive commutative group. -/
class NormedAddCommGroupOfRing (B : Type*) extends Ring B, NormedAddCommGroup B


-- @@ L24-24 verbatim
attribute [instance] NormedAddCommGroupOfRing.toNormedAddCommGroup

-- @@ L25-25 verbatim
attribute [instance] NormedAddCommGroupOfRing.toRing

-- @@ L26-26 verbatim
attribute [instance] NormedAddCommGroupOfRing.toNorm


-- @@ L28-32 verbatim
/-- The algebra structure coming from compatible scalar multiplication and multiplication. -/
@[reducible]
def Algebra.ofIsScalarTowerSmulCommClass {R A : Type*} [CommSemiring R] [Semiring A]
    [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm


-- @@ L34-34 verbatim
attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass


-- @@ L36-43 verbatim
/-- The pointwise ring with the `L^2` product norm is a normed additive group of rings. -/
@[reducible, instance]
noncomputable def PiNormedAddCommGroupOfRing {ι : Type*} [Fintype ι] {B : ι → Type*}
    [Π i, NormedAddCommGroupOfRing (B i)] : NormedAddCommGroupOfRing (Π i, B i) where
  toNorm := (PiLp.normedAddCommGroupToPi (2 : ENNReal) B).toNorm
  toRing := Pi.ring
  toMetricSpace := (PiLp.normedAddCommGroupToPi (2 : ENNReal) B).toMetricSpace
  dist_eq := (PiLp.normedAddCommGroupToPi (2 : ENNReal) B).dist_eq


-- @@ L45-52 verbatim
/-- The `L^2` norm on a finite product is the square root of the sum of squared norms. -/
theorem Pi.normedAddCommGroupOfRing.norm_eq_sum {ι : Type*} [Fintype ι] {B : ι → Type*}
    [Π i, NormedAddCommGroupOfRing (B i)] (x : Π i, B i) :
    PiNormedAddCommGroupOfRing.norm x = Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  have h2 : 0 < (2 : ENNReal).toReal := by norm_num
  change ‖WithLp.toLp (2 : ENNReal) x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2)
  rw [PiLp.norm_eq_sum h2]
  simp [Real.sqrt_eq_rpow]
