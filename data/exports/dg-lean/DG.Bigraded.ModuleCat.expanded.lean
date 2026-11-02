import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Shift.Basic
import DG.Bigraded.InternalShift
import DG.Homotopy.ModuleCat


-- @@ L6-30 verbatim
/-!
# The category of bigraded dg modules

For a ring `A` with a dg structure and an internal grading (`DG.InternalGrading A`), the
category `DG.BigradedDGModuleCat.{v} A` has as objects the dg `A`-modules with a compatible
internal grading (`DG.InternalGrading`, `DG.BigradedDGModule`), with carrier in `Type v`, and
as morphisms the morphisms of dg modules `M →ᵈᵍ[A] N` which preserve weights.

* The category is preadditive, and the forgetful functor
  `DG.BigradedDGModuleCat.toDGModuleCat : BigradedDGModuleCat A ⥤ DGModuleCat A` is additive and
  faithful.
* `DG.BigradedDGModuleCat.internalShiftFunctor k`: the internal shift `M ↦ M⟨k⟩`
  (`DG.InternalShift`), and `DG.BigradedDGModuleCat.internalHasShift`, the structure of a
  category with a shift by `ℤ` given by the internal shifts, built with `hasShiftMk`. It is a
  definition, not an instance, since the instance `HasShift (BigradedDGModuleCat A) ℤ` is the
  cohomological shift. Each internal shift is an autoequivalence
  (`DG.BigradedDGModuleCat.internalShiftEquiv`), and it is compatible with the forgetful
  functor (`DG.BigradedDGModuleCat.internalShiftForgetIso`).
* For a dg ring `A`, the cohomological shift `M ↦ M[n]` (`DG.Shift`), as the instance
  `HasShift (BigradedDGModuleCat A) ℤ`, and the natural isomorphism
  `DG.BigradedDGModuleCat.internalShiftShiftIso n k : M[n]⟨k⟩ ≅ M⟨k⟩[n]` expressing that the two
  shifts commute (the identity on elements, without sign).

All the structure isomorphisms are the identity on elements.
-/


-- @@ L32-32 verbatim
open CategoryTheory


-- @@ L34-34 verbatim
universe v u


-- @@ L36-36 verbatim
namespace DG


-- @@ L38-38 verbatim
variable (A : Type u) [Ring A] [DGAddCommGroup A] [InternalGrading A]


-- @@ L40-50 verbatim
/-- The category of bigraded dg `A`-modules with carriers in `Type v`: dg `A`-modules with a
compatible internal grading. -/
structure BigradedDGModuleCat where
  /-- The underlying type. -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isDGAddCommGroup : DGAddCommGroup carrier]
  [isModule : Module A carrier]
  [isDGModule : DGModule A carrier]
  [isInternalGrading : InternalGrading carrier]
  [isBigradedDGModule : BigradedDGModule A carrier]


-- @@ L52-54 verbatim
attribute [instance] BigradedDGModuleCat.isAddCommGroup BigradedDGModuleCat.isDGAddCommGroup
  BigradedDGModuleCat.isModule BigradedDGModuleCat.isDGModule
  BigradedDGModuleCat.isInternalGrading BigradedDGModuleCat.isBigradedDGModule


-- @@ L56-56 verbatim
namespace BigradedDGModuleCat


-- @@ L58-59 verbatim
instance : CoeSort (BigradedDGModuleCat.{v} A) (Type v) :=
  ⟨BigradedDGModuleCat.carrier⟩


-- @@ L61-61 verbatim
attribute [coe] BigradedDGModuleCat.carrier


-- @@ L63-67 verbatim
/-- The object of `BigradedDGModuleCat A` associated to a type with a bigraded dg `A`-module
structure. -/
abbrev of (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [InternalGrading M] [BigradedDGModule A M] : BigradedDGModuleCat.{v} A :=
  ⟨M⟩


-- @@ L69-69 verbatim
variable {A}


-- @@ L71-76 expanded
/-- The morphisms of bigraded dg modules: morphisms of dg modules preserving weights. -/
@[ext]
structure Hom (M N : BigradedDGModuleCat.{v} A) where
  /-- The underlying morphism of dg modules. -/
  hom : DGModuleHom A M N
  map_mem_wgrading : ∀ {k : ℤ} {m : M}, m ∈ wgrading k → hom m ∈ wgrading k


-- @@ L78-81 verbatim
instance category : Category.{v, max (v + 1) u} (BigradedDGModuleCat.{v} A) where
  Hom M N := Hom M N
  id _ := ⟨DGModuleHom.id, fun hm => hm⟩
  comp f g := ⟨g.hom.comp f.hom, fun hm => g.map_mem_wgrading (f.map_mem_wgrading hm)⟩


-- @@ L83-84 verbatim
@[simp]
theorem hom_id {M : BigradedDGModuleCat.{v} A} : (𝟙 M : M ⟶ M).hom = DGModuleHom.id := rfl


-- @@ L86-88 verbatim
@[simp]
theorem hom_comp {M N P : BigradedDGModuleCat.{v} A} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl


-- @@ L90-92 verbatim
@[ext]
theorem hom_ext {M N : BigradedDGModuleCat.{v} A} {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Hom.ext h


-- @@ L94-96 verbatim
theorem hom_ext_apply {M N : BigradedDGModuleCat.{v} A} {f g : M ⟶ N}
    (h : ∀ x, f.hom x = g.hom x) : f = g :=
  hom_ext (DGModuleHom.ext h)


-- @@ L98-100 expanded
theorem hom_injective {M N : BigradedDGModuleCat.{v} A} :
    Function.Injective (Hom.hom : (M ⟶ N) → (DGModuleHom A M N)) := fun _ _ h => hom_ext h


-- @@ L102-105 expanded
/-- A morphism of dg modules preserving weights, as a morphism of bigraded dg modules. -/
abbrev ofHom {M N : BigradedDGModuleCat.{v} A} (f : DGModuleHom A M N)
    (hf : ∀ {k : ℤ} {m : M}, m ∈ wgrading k → f m ∈ wgrading k) : M ⟶ N :=
  ⟨f, hf⟩


-- @@ L107-110 verbatim
theorem eqToHom_hom_apply {M N : BigradedDGModuleCat.{v} A} (h : M = N) (x : M) :
    (eqToHom h).hom x = cast (congrArg carrier h) x := by
  subst h
  rfl


-- @@ L112-120 expanded
/-- An isomorphism of dg modules preserving weights is an isomorphism of bigraded dg modules. -/
def isoMk {M N : BigradedDGModuleCat.{v} A} (e : DGModuleEquiv A M N)
    (he : ∀ {k : ℤ} {m : M}, e m ∈ wgrading k ↔ m ∈ wgrading k) : M ≅ N
    where
  hom := ⟨e.toDGModuleHom, fun hm => he.mpr hm⟩
  inv :=
    ⟨e.symm.toDGModuleHom, fun {k y} hy =>
      by
      rw [← he, DGModuleEquiv.coe_toDGModuleHom, DGModuleEquiv.apply_symm_apply]
      exact hy⟩
  hom_inv_id := hom_ext_apply fun x => e.symm_apply_apply x
  inv_hom_id := hom_ext_apply fun x => e.apply_symm_apply x


-- @@ L122-124 expanded
@[simp]
theorem isoMk_hom_hom {M N : BigradedDGModuleCat.{v} A} (e : DGModuleEquiv A M N)
    (he : ∀ {k : ℤ} {m : M}, e m ∈ wgrading k ↔ m ∈ wgrading k) :
    (isoMk e he).hom.hom = e.toDGModuleHom :=
  rfl


-- @@ L126-128 expanded
@[simp]
theorem isoMk_inv_hom {M N : BigradedDGModuleCat.{v} A} (e : DGModuleEquiv A M N)
    (he : ∀ {k : ℤ} {m : M}, e m ∈ wgrading k ↔ m ∈ wgrading k) :
    (isoMk e he).inv.hom = e.symm.toDGModuleHom :=
  rfl


-- @@ L130-130 verbatim
/-! ### Preadditive structure -/


-- @@ L132-132 verbatim
section AddCommGroup


-- @@ L134-134 verbatim
variable {M N : BigradedDGModuleCat.{v} A}


-- @@ L136-137 verbatim
instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom, fun hm => add_mem (f.map_mem_wgrading hm) (g.map_mem_wgrading hm)⟩


-- @@ L139-139 verbatim
@[simp] theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl


-- @@ L141-142 verbatim
instance : Zero (M ⟶ N) where
  zero := ⟨0, fun _ => zero_mem _⟩


-- @@ L144-144 verbatim
@[simp] theorem hom_zero : (0 : M ⟶ N).hom = 0 := rfl


-- @@ L146-147 verbatim
instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom, fun hm => nsmul_mem (f.map_mem_wgrading hm) n⟩


-- @@ L149-149 verbatim
@[simp] theorem hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl


-- @@ L151-152 verbatim
instance : Neg (M ⟶ N) where
  neg f := ⟨-f.hom, fun hm => neg_mem (f.map_mem_wgrading hm)⟩


-- @@ L154-154 verbatim
@[simp] theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl


-- @@ L156-157 verbatim
instance : Sub (M ⟶ N) where
  sub f g := ⟨f.hom - g.hom, fun hm => sub_mem (f.map_mem_wgrading hm) (g.map_mem_wgrading hm)⟩


-- @@ L159-159 verbatim
@[simp] theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl


-- @@ L161-162 verbatim
instance : SMul ℤ (M ⟶ N) where
  smul n f := ⟨n • f.hom, fun hm => zsmul_mem (f.map_mem_wgrading hm) n⟩


-- @@ L164-164 verbatim
@[simp] theorem hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl


-- @@ L166-168 verbatim
instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup Hom.hom hom_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)


-- @@ L170-172 verbatim
instance preadditive : Preadditive (BigradedDGModuleCat.{v} A) where
  add_comp _ _ _ _ _ _ := hom_ext_apply fun _ => by simp
  comp_add _ _ _ _ _ _ := hom_ext_apply fun _ => by simp


-- @@ L174-174 verbatim
end AddCommGroup


-- @@ L176-176 verbatim
/-! ### The forgetful functor -/


-- @@ L178-183 verbatim
variable (A) in
/-- The forgetful functor from bigraded dg modules to dg modules, forgetting the internal
grading. -/
def toDGModuleCat : BigradedDGModuleCat.{v} A ⥤ DGModuleCat.{v} A where
  obj M := DGModuleCat.of A M
  map f := DGModuleCat.ofHom f.hom


-- @@ L185-187 verbatim
@[simp]
theorem toDGModuleCat_map_hom {M N : BigradedDGModuleCat.{v} A} (f : M ⟶ N) :
    ((toDGModuleCat A).map f).hom = f.hom := rfl


-- @@ L189-190 verbatim
instance : (toDGModuleCat.{v} A).Faithful where
  map_injective h := hom_ext (congrArg DGModuleCat.Hom.hom h)


-- @@ L192-192 verbatim
instance : (toDGModuleCat.{v} A).Additive where


-- @@ L194-194 verbatim
/-! ### The internal shift -/


-- @@ L196-201 verbatim
/-- The internal shift functor `M ↦ M⟨k⟩` on bigraded dg modules. -/
@[simps obj]
def internalShiftFunctor (k : ℤ) : BigradedDGModuleCat.{v} A ⥤ BigradedDGModuleCat.{v} A where
  obj M := of A (InternalShift k M)
  map f := ⟨f.hom.internalShift k, fun hm => f.hom.internalShift_mem_wgrading k
    (fun hm' => f.map_mem_wgrading hm') hm⟩


-- @@ L203-205 verbatim
@[simp]
theorem internalShiftFunctor_map_hom (k : ℤ) {M N : BigradedDGModuleCat.{v} A} (f : M ⟶ N) :
    ((internalShiftFunctor k).map f).hom = f.hom.internalShift k := rfl


-- @@ L207-207 verbatim
instance (k : ℤ) : (internalShiftFunctor.{v} (A := A) k).Additive where


-- @@ L209-212 verbatim
/-- `M⟨0⟩ ≅ M`, naturally in `M`. -/
def internalShiftFunctorZero : internalShiftFunctor.{v} (A := A) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => isoMk (InternalShift.zeroEquiv (M := M) A)
    InternalShift.mem_wgrading_zeroEquiv_iff) fun _ => rfl


-- @@ L214-224 expanded
/-- The identity `M⟨k + l⟩ → (M⟨k⟩)⟨l⟩`, as an isomorphism of dg modules. -/
def internalShiftAddEquiv (k l : ℤ) (M : BigradedDGModuleCat.{v} A) :
    DGModuleEquiv A (InternalShift (k + l) M) (InternalShift l (InternalShift k M))
    where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' hm := hm
  map_d' _ := rfl


-- @@ L226-231 verbatim
theorem mem_wgrading_internalShiftAddEquiv_iff (k l : ℤ) (M : BigradedDGModuleCat.{v} A)
    {j : ℤ} {x : InternalShift (k + l) M} :
    internalShiftAddEquiv k l M x ∈ wgrading j ↔ x ∈ wgrading j := by
  rw [InternalShift.mem_wgrading_iff', InternalShift.mem_wgrading_iff',
    InternalShift.mem_wgrading_iff', add_assoc, add_comm l k]
  rfl


-- @@ L233-238 verbatim
/-- `M⟨k + l⟩ ≅ (M⟨k⟩)⟨l⟩`, naturally in `M`. -/
def internalShiftFunctorAdd (k l : ℤ) :
    internalShiftFunctor.{v} (A := A) (k + l) ≅
      internalShiftFunctor k ⋙ internalShiftFunctor l :=
  NatIso.ofComponents (fun M => isoMk (internalShiftAddEquiv k l M)
    (mem_wgrading_internalShiftAddEquiv_iff k l M)) fun _ => rfl


-- @@ L240-254 verbatim
variable (A) in
/-- The data of the internal shift as a shift of `BigradedDGModuleCat A` by `ℤ`. -/
def internalShiftMkCore : ShiftMkCore (BigradedDGModuleCat.{v} A) ℤ where
  F := internalShiftFunctor
  zero := internalShiftFunctorZero
  add := internalShiftFunctorAdd
  assoc_hom_app _ _ _ _ := hom_ext_apply fun x => by
    simp only [hom_comp, DGModuleHom.comp_apply, eqToHom_hom_apply]
    rfl
  zero_add_hom_app _ _ := hom_ext_apply fun x => by
    simp only [hom_comp, DGModuleHom.comp_apply, eqToHom_hom_apply]
    rfl
  add_zero_hom_app _ _ := hom_ext_apply fun x => by
    simp only [hom_comp, DGModuleHom.comp_apply, eqToHom_hom_apply]
    rfl


-- @@ L256-262 verbatim
variable (A) in
/-- The internal shift, as a shift of `BigradedDGModuleCat A` by `ℤ`: `M⟦k⟧ = M⟨k⟩`. This is
a definition, not an instance: the instance `HasShift (BigradedDGModuleCat A) ℤ` is the
cohomological shift. -/
@[instance_reducible]
def internalHasShift : HasShift (BigradedDGModuleCat.{v} A) ℤ :=
  hasShiftMk _ ℤ (internalShiftMkCore A)


-- @@ L264-266 verbatim
theorem internalHasShift_shiftFunctor (k : ℤ) :
    @shiftFunctor _ _ _ _ (internalHasShift.{v} A) k = internalShiftFunctor k :=
  rfl


-- @@ L268-271 verbatim
/-- The internal shift by `k` is an autoequivalence of `BigradedDGModuleCat A`, with inverse the
internal shift by `-k`. -/
def internalShiftEquiv (k : ℤ) : BigradedDGModuleCat.{v} A ≌ BigradedDGModuleCat.{v} A :=
  @shiftEquiv _ _ _ _ (internalHasShift.{v} A) k


-- @@ L273-276 verbatim
@[simp]
theorem internalShiftEquiv_functor (k : ℤ) :
    (internalShiftEquiv.{v} (A := A) k).functor = internalShiftFunctor k :=
  rfl


-- @@ L278-287 expanded
set_option backward.isDefEq.respectTransparency false in
/-- The internal shift is compatible with the forgetful functor: `M⟨k⟩` and `M` have the same
underlying dg module. -/
def internalShiftForgetIso (k : ℤ) :
    internalShiftFunctor k ⋙ toDGModuleCat.{v} A ≅ toDGModuleCat.{v} A :=
  NatIso.ofComponents
    (fun M =>
      { hom := DGModuleCat.ofHom (InternalShift.zeroEquiv A).toDGModuleHom
        inv := DGModuleCat.ofHom (DGModuleHom.id : DGModuleHom A M M)
        hom_inv_id := rfl
        inv_hom_id := rfl })
    fun _ => rfl


-- @@ L289-289 verbatim
/-! ### The cohomological shift -/


-- @@ L291-291 verbatim
section Shift


-- @@ L293-293 verbatim
variable [DGRing A]


-- @@ L295-299 verbatim
/-- The cohomological shift functor `M ↦ M[n]` on bigraded dg modules. -/
@[simps obj]
def cohShiftFunctor (n : ℤ) : BigradedDGModuleCat.{v} A ⥤ BigradedDGModuleCat.{v} A where
  obj M := of A (Shift n M)
  map f := ⟨f.hom.shift n, fun hm => f.map_mem_wgrading hm⟩


-- @@ L301-303 verbatim
@[simp]
theorem cohShiftFunctor_map_hom (n : ℤ) {M N : BigradedDGModuleCat.{v} A} (f : M ⟶ N) :
    ((cohShiftFunctor n).map f).hom = f.hom.shift n := rfl


-- @@ L305-307 verbatim
/-- `M[0] ≅ M`, naturally in `M`. -/
def cohShiftFunctorZero : cohShiftFunctor.{v} (A := A) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => isoMk (Shift.zeroEquiv (A := A) (M := M)) Iff.rfl) fun _ => rfl


-- @@ L309-327 expanded
/-- The identity `M[m + n] → (M[m])[n]`, as an isomorphism of dg modules. -/
def cohShiftAddEquiv (m n : ℤ) (M : BigradedDGModuleCat.{v} A) :
    DGModuleEquiv A (Shift (m + n) M) (Shift n (Shift m M))
    where
  toFun x := Shift.mk n (Shift.mk m (Shift.unmk (m + n) x))
  invFun y := Shift.mk (m + n) (Shift.unmk m (Shift.unmk n y))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a
    x :=
    by
    change
      Shift.mk n (Shift.mk m (Shift.unmk (m + n) (a • x))) =
        a • Shift.mk n (Shift.mk m (Shift.unmk (m + n) x))
    rw [Shift.unmk_smul_eq, Shift.smul_mk_eq, Shift.smul_mk_eq, Shift.twist_twist]
  map_mem' {k x}
    hx := by
    rw [Shift.mem_grading_iff, Shift.mem_grading_iff, add_assoc, add_comm n m]
    exact hx
  map_d'
    x :=
    by
    change
      koszulSign (m + n) • d (Shift.unmk (m + n) x) =
        koszulSign n • koszulSign m • d (Shift.unmk (m + n) x)
    rw [smul_smul, ← koszulSign_add, add_comm n m]


-- @@ L329-332 verbatim
/-- `M[m + n] ≅ (M[m])[n]`, naturally in `M`. -/
def cohShiftFunctorAdd (m n : ℤ) :
    cohShiftFunctor.{v} (A := A) (m + n) ≅ cohShiftFunctor m ⋙ cohShiftFunctor n :=
  NatIso.ofComponents (fun M => isoMk (cohShiftAddEquiv m n M) Iff.rfl) fun _ => rfl


-- @@ L334-348 verbatim
variable (A) in
/-- The data of the cohomological shift of `BigradedDGModuleCat A`. -/
def cohShiftMkCore : ShiftMkCore (BigradedDGModuleCat.{v} A) ℤ where
  F := cohShiftFunctor
  zero := cohShiftFunctorZero
  add := cohShiftFunctorAdd
  assoc_hom_app _ _ _ _ := hom_ext_apply fun x => by
    simp only [hom_comp, DGModuleHom.comp_apply, eqToHom_hom_apply]
    rfl
  zero_add_hom_app _ _ := hom_ext_apply fun x => by
    simp only [hom_comp, DGModuleHom.comp_apply, eqToHom_hom_apply]
    rfl
  add_zero_hom_app _ _ := hom_ext_apply fun x => by
    simp only [hom_comp, DGModuleHom.comp_apply, eqToHom_hom_apply]
    rfl


-- @@ L350-352 verbatim
/-- The cohomological shift `M⟦n⟧ = M[n]` of bigraded dg modules. -/
instance hasShift : HasShift (BigradedDGModuleCat.{v} A) ℤ :=
  hasShiftMk _ ℤ (cohShiftMkCore A)


-- @@ L354-356 verbatim
theorem shiftFunctor_eq (n : ℤ) :
    shiftFunctor (BigradedDGModuleCat.{v} A) n = cohShiftFunctor n :=
  rfl


-- @@ L358-358 verbatim
instance (n : ℤ) : (shiftFunctor (BigradedDGModuleCat.{v} A) n).Additive where


-- @@ L360-366 verbatim
/-- The internal and the cohomological shifts commute: `M[n]⟨k⟩ ≅ M⟨k⟩[n]`, naturally in `M`.
The isomorphism is the identity on elements, without sign (`DG.InternalShift.shiftEquiv`). -/
def internalShiftShiftIso (n k : ℤ) :
    shiftFunctor (BigradedDGModuleCat.{v} A) n ⋙ internalShiftFunctor k ≅
      internalShiftFunctor k ⋙ shiftFunctor (BigradedDGModuleCat.{v} A) n :=
  NatIso.ofComponents (fun M => isoMk (InternalShift.shiftEquiv (M := M) A n k) Iff.rfl)
    fun _ => rfl


-- @@ L368-372 verbatim
@[simp]
theorem internalShiftShiftIso_hom_app_hom (n k : ℤ) (M : BigradedDGModuleCat.{v} A) :
    ((internalShiftShiftIso n k).hom.app M).hom =
      (InternalShift.shiftEquiv (M := M) A n k).toDGModuleHom :=
  rfl


-- @@ L374-374 verbatim
end Shift


-- @@ L376-376 verbatim
end BigradedDGModuleCat


-- @@ L378-378 verbatim
end DG
