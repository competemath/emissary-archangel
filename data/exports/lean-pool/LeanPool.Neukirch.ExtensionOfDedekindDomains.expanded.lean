/-
Copyright (c) 2023 Hu Yongle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hu Yongle
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Tactic.Measurability.Init


-- @@ L14-18 verbatim
/-!
# LeanPool.Neukirch.ExtensionOfDedekindDomains

Imported Lean Pool material for `LeanPool.Neukirch.ExtensionOfDedekindDomains`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-23 verbatim
open IsDedekindDomain Algebra UniqueFactorizationMonoid Ideal.IsDedekindDomain Multiset
  Module


-- @@ L25-25 verbatim
attribute [local instance] Ideal.Quotient.field


-- @@ L27-27 verbatim
namespace Ideal


-- @@ L29-29 verbatim
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

-- @@ L30-30 verbatim
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]


-- @@ L32-40 verbatim
/-- Multiplicativity of the ramification index in a tower of Dedekind domains, stated with the
hypotheses used by the Hilbert ramification development. -/
theorem ramificationIdx_algebra_tower_of_eq [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : IsPrime P] [hqm : IsPrime Q]
    (_hf0 : map (algebraMap R S) p ≠ ⊥) (hg0 : map (algebraMap S T) P ≠ ⊥)
    (hfg : map (algebraMap R T) p ≠ ⊥) (_hp0 : P ≠ ⊥) (_hq0 : Q ≠ 0)
    (hg : P = comap (algebraMap S T) Q) : ramificationIdx' p Q =
    ramificationIdx' p P * ramificationIdx' P Q :=
  ramificationIdx'_algebra_tower hg0 hfg (map_le_iff_le_comap.mpr (le_of_eq hg))


-- @@ L42-60 verbatim
/-- The quotient-dimension tower law retains the former inertia-degree formula even when the
ideal upstairs is not prime, where the residue-field inertia degree is zero. -/
theorem quotient_finrank_algebra_tower_of_eq {p : Ideal R} {P : Ideal S} {I : Ideal T}
    [IsMaximal p] [IsMaximal P] (hp : p = comap (algebraMap R S) P)
    (hP : P = comap (algebraMap S T) I) :
    let : P.LiesOver p := ⟨hp⟩
    let : I.LiesOver P := ⟨hP⟩
    let : I.LiesOver p := LiesOver.trans I P p
    Module.finrank (R ⧸ p) (T ⧸ I) =
      Module.finrank (R ⧸ p) (S ⧸ P) * Module.finrank (S ⧸ P) (T ⧸ I) := by
  let : P.LiesOver p := ⟨hp⟩
  let : I.LiesOver P := ⟨hP⟩
  let : I.LiesOver p := LiesOver.trans I P p
  let : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun x => Quot.inductionOn x fun r => by
      change Ideal.Quotient.mk I (algebraMap R T r) =
        Ideal.Quotient.mk I (algebraMap S T (algebraMap R S r))
      rw [IsScalarTower.algebraMap_apply R S T]
  exact (Module.finrank_mul_finrank (R ⧸ p) (S ⧸ P) (T ⧸ I)).symm


-- @@ L62-69 verbatim
variable (R) in
/-- Multiplicativity of the inertia degree in a tower of Dedekind domains, stated with the
hypotheses used by the Hilbert ramification development. -/
theorem inertiaDeg_algebra_tower_of_eq {P : Ideal S} {I : Ideal T}
    (hP : P = comap (algebraMap S T) I) : I.inertiaDeg R =
    P.inertiaDeg R * I.inertiaDeg S :=
  letI : I.LiesOver P := ⟨hP⟩
  inertiaDeg_tower P I


-- @@ L71-75 verbatim
/-- The decomposition of a prime in a tower is `Nonsplit` when there is a unique prime above. -/
class Nonsplit {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : Ideal R) : Prop where
  /-- There is at most one maximal ideal lying over `p`. -/
  nonsplit : ∀ P : Ideal S, P.IsMaximal → p = comap f P →
    ∀ Q : Ideal S, Q.IsMaximal → p = comap f Q → P = Q


-- @@ L77-77 verbatim
end Ideal
