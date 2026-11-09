-- HAND-WRITTEN MIGRATION TABLE for the FATE-X statement attestation (PR 162). Not a Tengoku record, never banked.
--
-- FATE-X's statements were elaborated on Lean v4.28.0 with its Mathlib; the tree is Mathlib at Lean v4.34.0-rc2. Between the two, Mathlib renamed or restructured a handful of
-- INSTANCES and one definition that the statements mention by name. The originals' exports hold the library's own constants only, so these old names must exist in the
-- environment before the original statement can be read. Each definition below gives an old name the meaning the tree's own constants give the same thing:
--   * the value is what the old Mathlib source (v4.28.0) says, written with the tree's constants (the file and line are in the comment of each entry);
--   * it is `@[reducible]`, so the kernel and the elaborator see through it when they compare the original's statement with the translation;
--   * it is added for the check of ONE problem only (`#attest_env_save` ... `#attest_env_restore`), never visible to the next problem's statement or to the tree.
-- A pass in the attestation is therefore RELATIVE to this table: it says the translated statement implies the original one reading every name below as defined here. The table's
-- sha256 and the names each problem's original reaches are in the attestation (`interpretation`, `migrated`). A name that is missing, or stands on `sorryAx`, fails the check.
noncomputable section AttestMigration
universe u v u_1 u_2

-- Mathlib v4.28.0 Mathlib/Algebra/Group/Defs.lean:626 `instance Monoid.toNatPow {M} [Monoid M] : Pow M ℕ := ⟨fun x n ↦ Monoid.npow n x⟩`.
-- The tree: `Monoid` extends `NPow`, and `NPow.toPow` is `⟨fun x n ↦ NPow.npow n x⟩` (Mathlib/Algebra/Group/Monoid.lean): the same power.
@[reducible] def Monoid.toNatPow {M : Type u_1} [Monoid M] : Pow M ℕ := NPow.toPow

-- v4.28.0 Mathlib/Algebra/Group/Defs.lean `AddMonoid.toNatSMul`, the additive twin; the tree: `NSMul.toSMul`.
@[reducible] def AddMonoid.toNatSMul {M : Type u_1} [AddMonoid M] : SMul ℕ M := NSMul.toSMul

-- v4.28.0 Mathlib/Algebra/Algebra/Defs.lean:107 `def algebraMap (R A) ... : R →+* A := Algebra.algebraMap`. The tree: `Algebra.algebraMap` is the field itself (exported as `algebraMap`).
@[reducible] def algebraMap (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : R →+* A := Algebra.algebraMap R A

-- v4.28.0 Mathlib/Algebra/MvPolynomial/Basic.lean:96 `instance commSemiring [CommSemiring R] : CommSemiring (MvPolynomial σ R) := AddMonoidAlgebra.commSemiring`.
-- The tree: `MvPolynomial` is an abbreviation of `AddMonoidAlgebra R (σ →₀ ℕ)`, so the instance is the one found for that type.
@[reducible] def MvPolynomial.commSemiring {R : Type u} {σ : Type u_1} [CommSemiring R] : CommSemiring (MvPolynomial σ R) := inferInstance

-- v4.28.0 Mathlib/Algebra/MvPolynomial/CommRing.lean:57 `instance instCommRingMvPolynomial : CommRing (MvPolynomial σ R) := AddMonoidAlgebra.commRing`.
@[reducible] def MvPolynomial.instCommRingMvPolynomial {R : Type u} {σ : Type u_1} [CommRing R] : CommRing (MvPolynomial σ R) := inferInstance

-- v4.28.0 Mathlib/RingTheory/PowerSeries/Basic.lean:111 `instance [CommRing R] : CommRing R⟦X⟧ := by ...`. The tree: `PowerSeries R` is an abbreviation of `MvPowerSeries Unit R`.
@[reducible] def PowerSeries.instCommRing {R : Type u_1} [CommRing R] : CommRing (PowerSeries R) := inferInstance

-- v4.28.0 Mathlib/Algebra/Group/Submonoid/Defs.lean:362 `instance AddSubmonoidClass.nSMul ... (S : A) : SMul ℕ S := ⟨fun n a => ⟨n • a.1, nsmul_mem a.2 n⟩⟩`.
@[reducible] def AddSubmonoidClass.nSMul {M : Type u_1} [AddMonoid M] {A : Type u_2} [SetLike A M] [AddSubmonoidClass A M] (S : A) : SMul ℕ S :=
  ⟨fun n a => ⟨n • a.1, nsmul_mem a.2 n⟩⟩

-- v4.28.0 Mathlib/Algebra/MvPolynomial/Basic.lean:129 `instance algebra [CommSemiring R] [CommSemiring S₁] [Algebra R S₁] : Algebra R (MvPolynomial σ S₁) := AddMonoidAlgebra.algebra`.
@[reducible] def MvPolynomial.algebra {R : Type u} {S₁ : Type v} {σ : Type u_1} [CommSemiring R] [CommSemiring S₁] [Algebra R S₁] : Algebra R (MvPolynomial σ S₁) := inferInstance

-- v4.28.0 Mathlib/Algebra/MvPolynomial/Basic.lean:114 `instance module [Semiring R] [CommSemiring S₁] [Module R S₁] : Module R (MvPolynomial σ S₁) := AddMonoidAlgebra.module`.
@[reducible] def MvPolynomial.module {R : Type u} {S₁ : Type v} {σ : Type u_1} [Semiring R] [CommSemiring S₁] [Module R S₁] : Module R (MvPolynomial σ S₁) := inferInstance

-- v4.28.0 Mathlib/Algebra/Group/Submonoid/Defs.lean:369 `instance nPow {M} [Monoid M] {A} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S ℕ`; the tree: `SubmonoidClass.instPow`, the same.
@[reducible] def SubmonoidClass.nPow {M : Type u_1} [Monoid M] {A : Type u_2} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S ℕ := SubmonoidClass.instPow S

-- v4.28.0 Mathlib/Algebra/Group/Subgroup/Defs.lean:200 `instance zpow {M S} [DivInvMonoid M] [SetLike S M] [SubgroupClass S M] {H : S} : Pow H ℤ := ⟨fun a n => ⟨a.1 ^ n, zpow_mem a.2 n⟩⟩`.
@[reducible] def SubgroupClass.zpow {M : Type u_1} {S : Type u_2} [DivInvMonoid M] [SetLike S M] [SubgroupClass S M] {H : S} : Pow H ℤ := ⟨fun a n => ⟨a.1 ^ n, zpow_mem a.2 n⟩⟩

-- v4.28.0 Mathlib/Algebra/Group/Subgroup/Defs.lean:194 `instance AddSubgroupClass.zsmul {M S} [SubNegMonoid M] [SetLike S M] [AddSubgroupClass S M] {H : S} : SMul ℤ H := ⟨fun n a => ⟨n • a.1, zsmul_mem a.2 n⟩⟩`.
@[reducible] def AddSubgroupClass.zsmul {M : Type u_1} {S : Type u_2} [SubNegMonoid M] [SetLike S M] [AddSubgroupClass S M] {H : S} : SMul ℤ H := ⟨fun n a => ⟨n • a.1, zsmul_mem a.2 n⟩⟩

-- ---- constants whose SIGNATURE changed (migration.json `renames`): the original's reference to `Subring` is read as a reference to the wrapper below, which has the old signature ----

-- v4.28.0 `structure Subring (R : Type u) [Ring R]`; the tree: `Subring (R : Type u) [NonAssocRing R]`. Same subrings of the same ring.
@[reducible] def AttestOld.Subring (R : Type u) [Ring R] : Type u := Subring R

-- v4.28.0 `Subgroup.normalizer (H : Subgroup G) : Subgroup G`; the tree: it takes a `Set G` (`Subgroup.normalizer (s : Set G)`), the normalizer of the set `↑H`.
@[reducible] def AttestOld.Subgroup.normalizer {G : Type u_1} [Group G] (H : Subgroup G) : Subgroup G := Subgroup.normalizer (H : Set G)

-- v4.28.0 Mathlib/Algebra/Ring/Subring/Basic.lean:1072 `instance [AddCommMonoid α] [Module R α] (S : Subring R) : Module S α`.
@[reducible] def Subring.instModuleSubtypeMem {R : Type u_1} {α : Type u_2} [Ring R] [AddCommMonoid α] [Module R α] (S : AttestOld.Subring R) : Module S α := inferInstanceAs (Module (S : Subring R) α)

-- v4.28.0 Mathlib/Algebra/Algebra/Basic.lean:100 `instance ofSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subring R) : Algebra S A`.
@[reducible] def Algebra.ofSubring {R : Type u_1} {A : Type u_2} [CommRing R] [Ring A] [Algebra R A] (S : AttestOld.Subring R) : Algebra S A := inferInstanceAs (Algebra (S : Subring R) A)

end AttestMigration
