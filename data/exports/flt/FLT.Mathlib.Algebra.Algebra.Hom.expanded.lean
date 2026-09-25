/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.Prod


-- @@ L10-14 verbatim
/-!
# Hom

Material destined for Mathlib.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
section semialghom


-- @@ L20-26 verbatim
/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`).
-/
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B


-- @@ L28-29 verbatim
/-- Reinterpret a `SemialgHom` as a `RingHom`. -/
add_decl_doc SemialgHom.toRingHom


-- @@ L31-32 verbatim
@[inherit_doc SemialgHom]
infixr:25 " →ₛₐ " => SemialgHom _


-- @@ L34-35 verbatim
@[inherit_doc]
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B


-- @@ L37-38 verbatim
variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]


-- @@ L40-46 expanded
instance instFunLike : FunLike (SemialgHom φ A B) A B
    where
  coe f := f.toFun
  coe_injective f g
    h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h


-- @@ L48-50 expanded
variable {φ} {A} {B} in
lemma SemialgHom.map_smul (ψ : SemialgHom φ A B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x


-- @@ L52-54 expanded
@[simp]
theorem coe_mk (f : A →ₛₗ[φ] B) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : SemialgHom φ A B) : A → B) = f :=
  rfl


-- @@ L56-56 verbatim
end semialghom


-- @@ L58-58 verbatim
section semialghomclass


-- @@ L60-65 verbatim
/-- `SemialgHomClass F φ A B` states that `F` is a type of `φ`-semialgebra homomorphisms
from `A` to `B`, where `A` is an `R`-algebra, `B` is an `S`-algebra and `φ : R →+* S`. -/
class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B


-- @@ L67-70 verbatim
variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]


-- @@ L72-77 expanded
instance SemialgHomClass.instSemialgHom : SemialgHomClass (SemialgHom φ A B) φ A B
    where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero


-- @@ L79-82 expanded
variable {F} {φ} {A} {B} in
/-- Turn an element of `F` which satisfies `SemialgHomClass F φ A B` to a `SemialgHom`. -/
def SemialgHomClass.toSemialgHom (f : F) : SemialgHom φ A B :=
  { (f : A →ₛₗ[φ] B), (f : A →+* B) with }


-- @@ L84-85 expanded
instance : CoeTC F (SemialgHom φ A B) :=
  ⟨SemialgHomClass.toSemialgHom⟩


-- @@ L87-89 expanded
@[simp]
theorem SemialgHom.coe_coe (f : F) : ⇑(f : SemialgHom φ A B) = f :=
  rfl


-- @@ L91-91 verbatim
end semialghomclass


-- @@ L93-93 verbatim
section semialghom


-- @@ L95-96 verbatim
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]


-- @@ L98-102 expanded
lemma SemialgHom.commutes (ψ : SemialgHom φ A B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) :=
  by
  have := ψ.map_smul r 1
  rw [Algebra.smul_def, mul_one, map_one] at this
  rw [this, Algebra.smul_def, mul_one]


-- @@ L104-105 expanded
theorem SemialgHom.toLinearMap_eq_coe (f : SemialgHom φ A B) : f.toLinearMap = f :=
  rfl


-- @@ L107-108 expanded
theorem SemialgHom.toRingHom_eq_coe (f : SemialgHom φ A B) : f.toRingHom = f :=
  rfl


-- @@ L110-113 expanded
theorem SemialgHom.algebraMap_apply {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A]
    [Algebra S B] (f : SemialgHom φ A B) (a : A) :
    letI := f.toAlgebra
    algebraMap A B a = f a :=
  rfl


-- @@ L115-121 expanded
/-- The composition of two semi-algebra maps. -/
def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C] [Algebra T C]
    {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ] (g : SemialgHom ψ B C)
    (f : SemialgHom φ A B) : SemialgHom ξ A C
    where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom


-- @@ L123-128 expanded
/-- An algebra map defines a semi-algebra map using `RingHom.id` -/
def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) : SemialgHom (RingHom.id R) A B
    where
  __ := f
  map_smul' _ _ := by simp


-- @@ L130-138 expanded
/-- Promote a ring hom `f : A →+* B` which is `φ`-semilinear to a semi-algebra map.

This is *definitionally* `f` on the underlying ring hom, so any definitional equality satisfied
by `f` is inherited by the result. Use this in preference to transporting a semi-algebra map
along equivalences of `A` and `B`, which does not preserve such equalities. -/
def RingHom.toSemialgHom (f : A →+* B) (h : ∀ (r : R) (a : A), f (r • a) = φ r • f a) :
    SemialgHom φ A B where
  __ := f
  map_smul' := h


-- @@ L140-143 verbatim
@[simp]
theorem RingHom.coe_toSemialgHom (f : A →+* B) (h : ∀ (r : R) (a : A), f (r • a) = φ r • f a) :
    ⇑(RingHom.toSemialgHom f h) = ⇑f :=
  rfl


-- @@ L145-150 expanded
/-- The composition `(B →ₛₐ[ψ] C) ∘ (A →ₐ[S] B) → `A →ₛₐ[ψ] C` of a semi-algebra map with an
algebra map to give a semi-algebra map. -/
def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C] [Algebra T C]
    {ψ : S →+* T} [Algebra S A] (g : SemialgHom ψ B C) (f : A →ₐ[S] B) : SemialgHom ψ A C :=
  g.comp f.toSemialgHom


-- @@ L152-157 expanded
/-- The product of two semi-algebra maps on the same domain. -/
def SemialgHom.prod {C : Type*} [Semiring C] [Algebra S C] (f : SemialgHom φ A B)
    (g : SemialgHom φ A C) : SemialgHom φ A (B × C)
    where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp


-- @@ L159-163 expanded
/-- The product of two semi-algebra maps on separate domains. -/
def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D] [Algebra S C] [Algebra S D]
    [Algebra R B] (f : SemialgHom φ A C) (g : SemialgHom φ B D) : SemialgHom φ (A × B) (C × D) :=
  (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))


-- @@ L165-176 expanded
/-- Restrict the scalars of semialgebra map `f : A →ₛₐ[ψ] B` where `ψ : R' →ₛₐ[φ] S'`, to
`φ : R →+* S`. -/
@[simps!]
def SemialgHom.restrictScalars {R S R' S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] {φ : R →+* S}
    (ψ : SemialgHom φ R' S') {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [Algebra R' A] [Algebra S' B] [IsScalarTower R R' A] [IsScalarTower S S' B]
    (f : SemialgHom ψ.toRingHom A B) : SemialgHom φ A B
    where
  __ := f.toRingHom
  map_smul' r
    a := by
    have := f.map_smul (algebraMap R R' r) a
    simp_all [SemialgHom.toLinearMap_eq_coe, Algebra.algebraMap_eq_smul_one, ψ.map_smul]


-- @@ L178-178 verbatim
end semialghom
