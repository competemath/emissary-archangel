import Mathlib


-- @@ L3-3 verbatim
section


-- @@ L5-5 verbatim
section semialghom


-- @@ L7-13 verbatim
/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`).
-/
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B


-- @@ L15-16 verbatim
/-- Reinterpret a `SemialgHom` as a `RingHom`. -/
add_decl_doc SemialgHom.toRingHom


-- @@ L18-19 verbatim
@[inherit_doc SemialgHom]
infixr:25 " →ₛₐ " => SemialgHom _


-- @@ L21-22 verbatim
@[inherit_doc]
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B


-- @@ L24-25 verbatim
variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]


-- @@ L27-33 expanded
instance instFunLike : FunLike (SemialgHom φ A B) A B
    where
  coe f := f.toFun
  coe_injective f g
    h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h


-- @@ L35-37 expanded
variable {φ} {A} {B} in
lemma SemialgHom.map_smul (ψ : SemialgHom φ A B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x


-- @@ L39-41 expanded
@[simp]
theorem coe_mk (f : A →ₛₗ[φ] B) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : SemialgHom φ A B) : A → B) = f :=
  rfl


-- @@ L43-43 verbatim
end semialghom


-- @@ L45-45 verbatim
section semialghomclass


-- @@ L47-50 verbatim
class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B


-- @@ L52-55 verbatim
variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]


-- @@ L57-62 expanded
instance SemialgHomClass.instSemialgHom : SemialgHomClass (SemialgHom φ A B) φ A B
    where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero


-- @@ L64-67 expanded
variable {F} {φ} {A} {B} in
def SemialgHomClass.toSemialgHom (f : F) : SemialgHom φ A B :=
  { (f : A →ₛₗ[φ] B), (f : A →+* B) with }


-- @@ L69-70 expanded
instance : CoeTC F (SemialgHom φ A B) :=
  ⟨SemialgHomClass.toSemialgHom⟩


-- @@ L72-74 expanded
@[simp]
theorem SemialgHom.coe_coe (f : F) : ⇑(f : SemialgHom φ A B) = f :=
  rfl


-- @@ L76-76 verbatim
end semialghomclass


-- @@ L78-78 verbatim
section semialghom


-- @@ L80-81 verbatim
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]


-- @@ L83-87 expanded
lemma SemialgHom.commutes (ψ : SemialgHom φ A B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) :=
  by
  have := ψ.map_smul r 1
  rw [Algebra.smul_def, mul_one, map_one] at this
  rw [this, Algebra.smul_def, mul_one]


-- @@ L89-90 expanded
theorem SemialgHom.toLinearMap_eq_coe (f : SemialgHom φ A B) : f.toLinearMap = f :=
  rfl


-- @@ L92-93 expanded
theorem SemialgHom.toRingHom_eq_coe (f : SemialgHom φ A B) : f.toRingHom = f :=
  rfl


-- @@ L95-98 expanded
theorem SemialgHom.algebraMap_apply {A B : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A]
    [Algebra S B] (f : SemialgHom φ A B) (a : A) :
    letI := f.toAlgebra
    algebraMap A B a = f a :=
  rfl


-- @@ L100-105 expanded
def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C] [Algebra T C]
    {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ] (g : SemialgHom ψ B C)
    (f : SemialgHom φ A B) : SemialgHom ξ A C
    where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom


-- @@ L107-111 expanded
def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) : SemialgHom (RingHom.id R) A B
    where
  __ := f
  map_smul' _ _ := by simp


-- @@ L113-116 expanded
def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C] [Algebra T C]
    {ψ : S →+* T} [Algebra S A] (g : SemialgHom ψ B C) (f : A →ₐ[S] B) : SemialgHom ψ A C :=
  g.comp f.toSemialgHom


-- @@ L118-122 expanded
def SemialgHom.prod {C : Type*} [Semiring C] [Algebra S C] (f : SemialgHom φ A B)
    (g : SemialgHom φ A C) : SemialgHom φ A (B × C)
    where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp


-- @@ L124-127 expanded
def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D] [Algebra S C] [Algebra S D]
    [Algebra R B] (f : SemialgHom φ A C) (g : SemialgHom φ B D) : SemialgHom φ (A × B) (C × D) :=
  (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))


-- @@ L129-138 expanded
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


-- @@ L140-140 verbatim
end semialghom
