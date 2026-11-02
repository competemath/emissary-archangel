import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Forget
import DG.Algebra.Decompose
import DG.Module.PUnit
import DG.Module.Prod


-- @@ L10-33 verbatim
/-!
# The category of dg modules

`DG.DGModuleCat.{v} A` is the category of bundled dg `A`-modules with carrier in `Type v`, for a
dg ring `A`. It is built in the style of Mathlib's `ModuleCat`: objects are structures carrying
a type with its instances, and morphisms are a one-field structure wrapping
`DG.DGModuleHom A M N` (`M →ᵈᵍ[A] N`), so that `DGModuleCat A` is a concrete category.

The category is preadditive (morphisms form abelian groups under pointwise addition), has a zero
object (the zero module), and has finite biproducts (`M × N` with its componentwise dg
structure, `DG.Prod.instDGAddCommGroup`).

For a dg `R`-algebra `A`, the category is `R`-linear: `R` acts on `M →ᵈᵍ[A] N` through the
structure map, `(r • f) m = algebraMap R A r • f m` (`DG.DGModuleHom.instModule`). This action
is `A`-linear because `algebraMap R A r` is central in `A`, and commutes with `d` because the
image of `R` is killed by `d` and sits in degree `0`.

## Implementation notes

The `R`-module structure on `M →ᵈᵍ[A] N` and the `Linear R` instance are declared with a low
priority: for `R = ℤ` they agree with the integer action of the abelian group structure only
propositionally, and Mathlib's `AddCommGroup.toIntModule` and `Linear.preadditiveIntLinear`
should be found first.
-/


-- @@ L35-35 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L37-37 verbatim
universe v u


-- @@ L39-39 verbatim
namespace DG


-- @@ L41-41 verbatim
variable (A : Type u) [Ring A] [DGAddCommGroup A]


-- @@ L43-50 verbatim
/-- The category of dg `A`-modules with carriers in `Type v`. -/
structure DGModuleCat where
  /-- The underlying type of a dg module. -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isDGAddCommGroup : DGAddCommGroup carrier]
  [isModule : Module A carrier]
  [isDGModule : DGModule A carrier]


-- @@ L52-53 verbatim
attribute [instance] DGModuleCat.isAddCommGroup DGModuleCat.isDGAddCommGroup
  DGModuleCat.isModule DGModuleCat.isDGModule


-- @@ L55-55 verbatim
namespace DGModuleCat


-- @@ L57-58 verbatim
instance : CoeSort (DGModuleCat.{v} A) (Type v) :=
  ⟨DGModuleCat.carrier⟩


-- @@ L60-60 verbatim
attribute [coe] DGModuleCat.carrier


-- @@ L62-65 verbatim
/-- The object of `DGModuleCat A` associated to a type with a dg `A`-module structure. -/
abbrev of (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    DGModuleCat.{v} A :=
  ⟨M⟩


-- @@ L67-69 verbatim
theorem coe_of (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    (of A M : Type v) = M :=
  rfl


-- @@ L71-71 verbatim
variable {A}


-- @@ L73-77 expanded
/-- The type of morphisms in `DGModuleCat A`. -/
@[ext]
structure Hom (M N : DGModuleCat.{v} A) where
  /-- The underlying morphism of dg modules. -/
  hom' : DGModuleHom A M N


-- @@ L79-82 verbatim
instance category : Category.{v, max (v + 1) u} (DGModuleCat.{v} A) where
  Hom M N := Hom M N
  id _ := ⟨DGModuleHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩


-- @@ L84-86 expanded
instance concreteCategory : ConcreteCategory (DGModuleCat.{v} A) (DGModuleHom A · ·)
    where
  hom := Hom.hom'
  ofHom := Hom.mk


-- @@ L88-90 expanded
/-- The morphism of dg modules underlying a morphism in `DGModuleCat A`. -/
abbrev Hom.hom {M N : DGModuleCat.{v} A} (f : Hom M N) : DGModuleHom A M N :=
  ConcreteCategory.hom (C := DGModuleCat A) f


-- @@ L92-96 expanded
/-- A morphism of dg modules as a morphism in `DGModuleCat A`. -/
abbrev ofHom {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : DGModuleHom A M N) :
    of A M ⟶ of A N :=
  ConcreteCategory.ofHom (C := DGModuleCat A) f


-- @@ L98-100 verbatim
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : DGModuleCat.{v} A) (f : Hom M N) :=
  f.hom


-- @@ L102-102 verbatim
initialize_simps_projections Hom (hom' → hom)


-- @@ L104-105 verbatim
@[simp]
theorem hom_id {M : DGModuleCat.{v} A} : (𝟙 M : M ⟶ M).hom = DGModuleHom.id := rfl


-- @@ L107-107 verbatim
theorem id_apply (M : DGModuleCat.{v} A) (x : M) : (𝟙 M : M ⟶ M) x = x := rfl


-- @@ L109-111 verbatim
@[simp]
theorem hom_comp {M N P : DGModuleCat.{v} A} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl


-- @@ L113-114 verbatim
theorem comp_apply {M N P : DGModuleCat.{v} A} (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g) x = g (f x) := rfl


-- @@ L116-118 verbatim
@[ext]
theorem hom_ext {M N : DGModuleCat.{v} A} {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Hom.ext h


-- @@ L120-121 verbatim
theorem hom_ext_apply {M N : DGModuleCat.{v} A} {f g : M ⟶ N} (h : ∀ x, f x = g x) : f = g :=
  hom_ext (DGModuleHom.ext h)


-- @@ L123-126 expanded
theorem hom_bijective {M N : DGModuleCat.{v} A} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (DGModuleHom A M N))
    where
  left f g h := by cases f; cases g; exact congrArg _ h
  right f := ⟨⟨f⟩, rfl⟩


-- @@ L128-130 expanded
theorem hom_injective {M N : DGModuleCat.{v} A} :
    Function.Injective (Hom.hom : (M ⟶ N) → (DGModuleHom A M N)) :=
  hom_bijective.injective


-- @@ L132-134 expanded
theorem hom_surjective {M N : DGModuleCat.{v} A} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (DGModuleHom A M N)) :=
  hom_bijective.surjective


-- @@ L136-139 expanded
@[simp]
theorem hom_ofHom {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : DGModuleHom A M N) :
    (ofHom f).hom = f :=
  rfl


-- @@ L141-142 verbatim
@[simp]
theorem ofHom_hom {M N : DGModuleCat.{v} A} (f : M ⟶ N) : ofHom f.hom = f := rfl


-- @@ L144-146 expanded
@[simp]
theorem ofHom_id {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    ofHom (DGModuleHom.id : DGModuleHom A M M) = 𝟙 (of A M) :=
  rfl


-- @@ L148-152 expanded
@[simp]
theorem ofHom_comp {M N P : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] [AddCommGroup P]
    [DGAddCommGroup P] [Module A P] [DGModule A P] (f : DGModuleHom A M N) (g : DGModuleHom A N P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl


-- @@ L154-156 expanded
theorem ofHom_apply {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : DGModuleHom A M N)
    (x : M) : ofHom f x = f x :=
  rfl


-- @@ L158-163 expanded
/-- `DGModuleCat.Hom.hom` bundled as an equivalence. -/
def homEquiv {M N : DGModuleCat.{v} A} : (M ⟶ N) ≃ (DGModuleHom A M N)
    where
  toFun := Hom.hom
  invFun := ofHom
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L165-166 verbatim
instance : Inhabited (DGModuleCat.{v} A) :=
  ⟨of A PUnit⟩


-- @@ L168-168 verbatim
/-! ### Preadditive structure -/


-- @@ L170-170 verbatim
section AddCommGroup


-- @@ L172-172 verbatim
variable {M N : DGModuleCat.{v} A}


-- @@ L174-175 verbatim
instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom⟩


-- @@ L177-177 verbatim
@[simp] theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl


-- @@ L179-180 verbatim
instance : Zero (M ⟶ N) where
  zero := ⟨0⟩


-- @@ L182-182 verbatim
@[simp] theorem hom_zero : (0 : M ⟶ N).hom = 0 := rfl


-- @@ L184-185 verbatim
instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩


-- @@ L187-187 verbatim
@[simp] theorem hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl


-- @@ L189-190 verbatim
instance : Neg (M ⟶ N) where
  neg f := ⟨-f.hom⟩


-- @@ L192-192 verbatim
@[simp] theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl


-- @@ L194-195 verbatim
instance : Sub (M ⟶ N) where
  sub f g := ⟨f.hom - g.hom⟩


-- @@ L197-197 verbatim
@[simp] theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl


-- @@ L199-200 verbatim
instance : SMul ℤ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩


-- @@ L202-202 verbatim
@[simp] theorem hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl


-- @@ L204-206 verbatim
instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (Hom.hom) hom_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)


-- @@ L208-208 verbatim
@[simp] theorem add_apply (f g : M ⟶ N) (x : M) : (f + g) x = f x + g x := rfl

-- @@ L209-209 verbatim
@[simp] theorem zero_apply (x : M) : (0 : M ⟶ N) x = 0 := rfl

-- @@ L210-210 verbatim
@[simp] theorem neg_apply (f : M ⟶ N) (x : M) : (-f) x = -f x := rfl

-- @@ L211-211 verbatim
@[simp] theorem sub_apply (f g : M ⟶ N) (x : M) : (f - g) x = f x - g x := rfl


-- @@ L213-215 verbatim
instance preadditive : Preadditive (DGModuleCat.{v} A) where
  add_comp _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, add_apply, map_add]
  comp_add _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, add_apply]


-- @@ L217-220 expanded
/-- `DGModuleCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
def homAddEquiv : (M ⟶ N) ≃+ (DGModuleHom A M N) :=
  { homEquiv with map_add' := fun _ _ => rfl }


-- @@ L222-222 verbatim
end AddCommGroup


-- @@ L224-224 verbatim
/-! ### The zero object -/


-- @@ L226-229 verbatim
theorem isZero_of_subsingleton (M : DGModuleCat.{v} A) [Subsingleton M] : IsZero M where
  unique_to N := ⟨⟨⟨0⟩, fun f => hom_ext_apply fun x => by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  unique_from N := ⟨⟨⟨0⟩, fun _ => hom_ext_apply fun _ => Subsingleton.elim _ _⟩⟩


-- @@ L231-232 verbatim
instance hasZeroObject : HasZeroObject (DGModuleCat.{v} A) :=
  ⟨⟨of A PUnit, isZero_of_subsingleton _⟩⟩


-- @@ L234-234 verbatim
/-! ### Finite biproducts -/


-- @@ L236-236 verbatim
section Biproducts


-- @@ L238-238 verbatim
variable (M N : DGModuleCat.{v} A)


-- @@ L240-246 verbatim
/-- The binary product of two dg modules, computed on `M × N`. -/
def binaryProductLimitCone : LimitCone (pair M N) where
  cone := BinaryFan.mk (P := of A (M × N)) (ofHom (DGModuleHom.fst M N))
    (ofHom (DGModuleHom.snd M N))
  isLimit := BinaryFan.isLimitMk (fun s => ofHom (DGModuleHom.prod M N s.fst.hom s.snd.hom))
    (fun _ => rfl) (fun _ => rfl) fun s _ h₁ h₂ => hom_ext_apply fun x =>
      Prod.ext (congrArg (fun φ : s.pt ⟶ M => φ x) h₁) (congrArg (fun φ : s.pt ⟶ N => φ x) h₂)


-- @@ L248-249 verbatim
instance : HasLimit (pair M N) :=
  HasLimit.mk (binaryProductLimitCone M N)


-- @@ L251-252 verbatim
instance hasBinaryProducts : HasBinaryProducts (DGModuleCat.{v} A) :=
  hasBinaryProducts_of_hasLimit_pair _


-- @@ L254-255 verbatim
instance hasFiniteProducts : HasFiniteProducts (DGModuleCat.{v} A) :=
  hasFiniteProducts_of_has_binary_and_terminal


-- @@ L257-258 verbatim
instance hasBinaryBiproducts : HasBinaryBiproducts (DGModuleCat.{v} A) :=
  HasBinaryBiproducts.of_hasBinaryProducts


-- @@ L260-261 verbatim
instance hasFiniteBiproducts : HasFiniteBiproducts (DGModuleCat.{v} A) :=
  HasFiniteBiproducts.of_hasFiniteProducts


-- @@ L263-265 verbatim
/-- The biproduct in `DGModuleCat A` is the product `M × N` with its dg structure. -/
noncomputable def biprodIsoProd : (M ⊞ N : DGModuleCat.{v} A) ≅ of A (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).isLimit


-- @@ L267-270 verbatim
@[simp]
theorem biprodIsoProd_inv_comp_fst :
    (biprodIsoProd M N).inv ≫ biprod.fst = ofHom (DGModuleHom.fst M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)


-- @@ L272-275 verbatim
@[simp]
theorem biprodIsoProd_inv_comp_snd :
    (biprodIsoProd M N).inv ≫ biprod.snd = ofHom (DGModuleHom.snd M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)


-- @@ L277-277 verbatim
end Biproducts


-- @@ L279-279 verbatim
end DGModuleCat


-- @@ L281-281 verbatim
/-! ### Isomorphisms -/


-- @@ L283-283 verbatim
namespace DGModuleHom


-- @@ L285-286 verbatim
variable {A} {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]


-- @@ L288-305 expanded
/-- The inverse of a bijective morphism of dg modules is a morphism of dg modules. -/
noncomputable def inverse (f : DGModuleHom A M N) (hf : Function.Bijective f) : DGModuleHom A N M
    where
  __ := (LinearEquiv.ofBijective f.toLinearMap hf).symm
  map_mem' := by
    intro n x hx
    refine
      mem_grading_of_injective f.toLinearMap.toAddMonoidHom (fun h => f.map_mem h) hf.injective ?_
    have h := (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply x
    rw [LinearEquiv.ofBijective_apply] at h
    change f ((LinearEquiv.ofBijective f.toLinearMap hf).symm x) ∈ _
    rwa [← toLinearMap_apply, h]
  map_d'
    x := by
    apply hf.injective
    have h := fun y => (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply y
    simp only [LinearEquiv.ofBijective_apply] at h
    change
      f ((LinearEquiv.ofBijective f.toLinearMap hf).symm (d x)) =
        f (d ((LinearEquiv.ofBijective f.toLinearMap hf).symm x))
    rw [map_d, ← toLinearMap_apply, ← toLinearMap_apply, h, h]


-- @@ L307-310 expanded
@[simp]
theorem apply_inverse_apply (f : DGModuleHom A M N) (hf : Function.Bijective f) (x : N) :
    f (f.inverse hf x) = x :=
  (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply x


-- @@ L312-315 expanded
@[simp]
theorem inverse_apply_apply (f : DGModuleHom A M N) (hf : Function.Bijective f) (x : M) :
    f.inverse hf (f x) = x :=
  hf.injective (apply_inverse_apply f hf (f x))


-- @@ L317-317 verbatim
end DGModuleHom


-- @@ L319-319 verbatim
namespace DGModuleCat


-- @@ L321-321 verbatim
variable {A}


-- @@ L323-327 verbatim
/-- A bijective morphism in `DGModuleCat A` is an isomorphism. -/
theorem isIso_of_bijective {M N : DGModuleCat.{v} A} (f : M ⟶ N) (hf : Function.Bijective f) :
    IsIso f :=
  ⟨⟨ofHom (f.hom.inverse hf), hom_ext_apply fun x => DGModuleHom.inverse_apply_apply f.hom hf x,
    hom_ext_apply fun x => DGModuleHom.apply_inverse_apply f.hom hf x⟩⟩


-- @@ L329-331 verbatim
instance : (CategoryTheory.forget (DGModuleCat.{v} A)).ReflectsIsomorphisms where
  reflects f _ := isIso_of_bijective f
    ((isIso_iff_bijective ((CategoryTheory.forget (DGModuleCat.{v} A)).map f)).mp inferInstance)


-- @@ L333-333 verbatim
end DGModuleCat


-- @@ L335-335 verbatim
/-! ### `R`-linearity -/


-- @@ L337-337 verbatim
namespace DGModuleHom


-- @@ L339-342 verbatim
variable {A} {R : Type*} [CommRing R] [Algebra R A] [DGRing A] [DGAlgebra R A]
  {M N P : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]


-- @@ L344-357 expanded
/-- The action of `R` on `M →ᵈᵍ[A] N` for a dg `R`-algebra `A`:
`(r • f) m = algebraMap R A r • f m`.
See the implementation notes of `DG.Homotopy.ModuleCat` for the priority. -/
instance (priority := 100) instSMul : SMul R (DGModuleHom A M N) :=
  ⟨fun r f =>
    { toFun := fun m => algebraMap R A r • f m
      map_add' := fun m m' => by rw [map_add, smul_add]
      map_smul' := fun a m => by simp only [RingHom.id_apply, map_smul, smul_smul, Algebra.commutes]
      map_mem' := fun hm => by
        simpa using smul_mem_grading (algebraMap_mem_grading R (A := A) r) (f.map_mem hm)
      map_d' := fun m => by
        simp only [map_d, d_smul (algebraMap_mem_grading R (A := A) r), d_algebraMap, zero_smul,
          zero_add, koszulSign, Int.negOnePow_zero, one_smul] }⟩


-- @@ L359-360 expanded
@[simp]
theorem smul_apply (r : R) (f : DGModuleHom A M N) (m : M) : (r • f) m = algebraMap R A r • f m :=
  rfl


-- @@ L362-369 expanded
/-- `M →ᵈᵍ[A] N` is an `R`-module for a dg `R`-algebra `A`. -/
instance (priority := 100) instModule : Module R (DGModuleHom A M N)
    where
  one_smul f := ext fun m => by simp
  mul_smul r s f := ext fun m => by simp [mul_smul]
  smul_zero r := ext fun m => by simp
  smul_add r f g := ext fun m => by simp
  add_smul r s f := ext fun m => by simp [add_smul]
  zero_smul f := ext fun m => by simp


-- @@ L371-373 expanded
omit [DGModule A N] in
theorem smul_comp (r : R) (g : DGModuleHom A N P) (f : DGModuleHom A M N) :
    (r • g).comp f = r • g.comp f :=
  rfl


-- @@ L375-376 expanded
theorem comp_smul (r : R) (g : DGModuleHom A N P) (f : DGModuleHom A M N) :
    g.comp (r • f) = r • g.comp f :=
  ext fun m => by simp


-- @@ L378-378 verbatim
end DGModuleHom


-- @@ L380-380 verbatim
namespace DGModuleCat


-- @@ L382-382 verbatim
variable {A} {R : Type*} [CommRing R] [Algebra R A] [DGRing A] [DGAlgebra R A]


-- @@ L384-386 verbatim
/-- The action of `R` on the morphisms of `DGModuleCat A` for a dg `R`-algebra `A`. -/
instance (priority := 100) instSMulHom {M N : DGModuleCat.{v} A} : SMul R (M ⟶ N) where
  smul r f := ⟨r • f.hom⟩


-- @@ L388-389 verbatim
@[simp]
theorem hom_smul {M N : DGModuleCat.{v} A} (r : R) (f : M ⟶ N) : (r • f).hom = r • f.hom := rfl


-- @@ L391-393 verbatim
@[simp]
theorem smul_apply {M N : DGModuleCat.{v} A} (r : R) (f : M ⟶ N) (x : M) :
    (r • f) x = algebraMap R A r • f x := rfl


-- @@ L395-401 verbatim
/-- `DGModuleCat A` is an `R`-linear category for a dg `R`-algebra `A`. -/
instance (priority := 100) instLinear : Linear R (DGModuleCat.{v} A) where
  homModule M N := Function.Injective.module R
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add } hom_injective
    fun _ _ => rfl
  smul_comp _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, smul_apply, map_smul]
  comp_smul _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, smul_apply]


-- @@ L403-403 verbatim
end DGModuleCat


-- @@ L405-405 verbatim
end DG
