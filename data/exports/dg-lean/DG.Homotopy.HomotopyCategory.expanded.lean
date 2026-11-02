import Mathlib.CategoryTheory.Quotient.Linear
import Mathlib.CategoryTheory.Quotient.Preadditive
import DG.Homotopy.Homotopy
import DG.Homotopy.ModuleCat


-- @@ L6-37 verbatim
/-!
# The homotopy category of dg modules

Let `A` be a dg ring. The homotopy category `DG.HomotopyCategory A` is the quotient of the
category `DG.DGModuleCat A` of dg `A`-modules by the homotopy relation
(`DG.DGModuleCat.homotopic A`, i.e. `DG.Homotopic` on the underlying morphisms), built with
Mathlib's `CategoryTheory.Quotient`, exactly as Mathlib's `HomotopyCategory` of homological
complexes.

## Main definitions and results

* `DG.DGModuleCat.homotopic A : HomRel (DGModuleCat A)`, a congruence.
* `DG.HomotopyCategory A` and the quotient functor `DG.HomotopyCategory.quotient A`, which is
  full, essentially surjective and additive.
* The homotopy category is preadditive, has a zero object, and is `R`-linear for a dg
  `R`-algebra `A` (the quotient functor is then `R`-linear); for the latter we add
  `DG.DGHomotopy.smul`.
* `DG.HomotopyCategory.quotient_map_eq_iff`: two morphisms become equal in the homotopy category
  iff they are homotopic.
* `DG.HomotopyCategory.homAddEquivCohomology`:
  `Hom_{H(A)}(M, N) ≃+ H⁰(HOM_A(M, N))`, obtained from
  `DG.quotientNullHomotopicAddEquivCohomology`.
* `DG.HomotopyCategory.isoOfHomotopyEquiv`: homotopy equivalent dg modules become isomorphic;
  `DG.HomotopyCategory.isZero_quotient_obj_iff`: a dg module is zero in the homotopy category
  iff it is contractible.

## Implementation notes

The name `DG.HomotopyCategory` follows `docs/CONVENTIONS.md`. Inside `namespace DG` the name
`HomotopyCategory` refers to it; Mathlib's homotopy category of complexes is then written
`_root_.HomotopyCategory`.
-/


-- @@ L39-39 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L41-41 verbatim
universe v u


-- @@ L43-43 verbatim
namespace DG


-- @@ L45-45 verbatim
/-! ### Scalar multiples of homotopies -/


-- @@ L47-47 verbatim
section Smul


-- @@ L49-52 expanded
variable {R A : Type*} [CommRing R] [Ring A] [DGAddCommGroup A] [DGRing A] [Algebra R A]
  [DGAlgebra R A] {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] {f g : DGModuleHom A M N}


-- @@ L54-59 verbatim
/-- For a dg `R`-algebra `A`, a homotopy from `f` to `g` gives a homotopy from `r • f` to
`r • g`, namely `r • h = algebraMap R A r • h`. -/
@[simps]
def DGHomotopy.smul (r : R) (h : DGHomotopy f g) : DGHomotopy (r • f) (r • g) where
  hom := (Cochain.ofHom (r • DGModuleHom.id)).comp h.hom (add_zero _)
  ofHom_eq := (h.compRight (r • DGModuleHom.id)).ofHom_eq


-- @@ L61-62 verbatim
theorem Homotopic.smul (r : R) (h : Homotopic f g) : Homotopic (r • f) (r • g) :=
  ⟨h.some.smul r⟩


-- @@ L64-64 verbatim
end Smul


-- @@ L66-66 verbatim
variable (A : Type u) [Ring A] [DGAddCommGroup A]


-- @@ L68-68 verbatim
namespace DGModuleCat


-- @@ L70-71 verbatim
/-- The homotopy relation on the morphisms of `DGModuleCat A`. -/
def homotopic : HomRel (DGModuleCat.{v} A) := fun _ _ f g => Homotopic f.hom g.hom


-- @@ L73-79 verbatim
instance homotopic_congruence : Congruence (homotopic.{v} A) where
  equivalence :=
    { refl := fun f => Homotopic.refl f.hom
      symm := Homotopic.symm
      trans := Homotopic.trans }
  comp_left f _ _ h := Homotopic.comp_left h f.hom
  comp_right g h := Homotopic.comp_right h g.hom


-- @@ L81-81 verbatim
end DGModuleCat


-- @@ L83-86 verbatim
/-- The homotopy category of dg `A`-modules: the quotient of `DGModuleCat A` by the homotopy
relation. -/
def HomotopyCategory : Type (max (v + 1) u) :=
  CategoryTheory.Quotient (DGModuleCat.homotopic.{v} A)


-- @@ L88-88 verbatim
namespace HomotopyCategory


-- @@ L90-91 verbatim
instance : Category.{v} (HomotopyCategory.{v} A) :=
  inferInstanceAs (Category (CategoryTheory.Quotient (DGModuleCat.homotopic.{v} A)))


-- @@ L93-95 verbatim
/-- The quotient functor from dg modules to the homotopy category. -/
def quotient : DGModuleCat.{v} A ⥤ HomotopyCategory.{v} A :=
  CategoryTheory.Quotient.functor _


-- @@ L97-98 verbatim
instance : Preadditive (HomotopyCategory.{v} A) :=
  Quotient.preadditive _ fun _ _ _ _ _ _ h h' => Homotopic.add h h'


-- @@ L100-100 verbatim
instance : (quotient A).Full := Quotient.full_functor _


-- @@ L102-102 verbatim
instance : (quotient A).EssSurj := Quotient.essSurj_functor _


-- @@ L104-105 verbatim
instance : (quotient A).Additive where
  map_add := rfl


-- @@ L107-108 verbatim
instance : Preadditive (CategoryTheory.Quotient (DGModuleCat.homotopic.{v} A)) :=
  inferInstanceAs (Preadditive (HomotopyCategory.{v} A))


-- @@ L110-111 verbatim
instance : (CategoryTheory.Quotient.functor (DGModuleCat.homotopic.{v} A)).Additive where
  map_add := rfl


-- @@ L113-116 verbatim
open ZeroObject in
instance : HasZeroObject (HomotopyCategory.{v} A) :=
  ⟨(quotient A).obj 0, by
    rw [IsZero.iff_id_eq_zero, ← (quotient A).map_id, id_zero, Functor.map_zero]⟩


-- @@ L118-118 verbatim
section Linear


-- @@ L120-120 verbatim
variable {A} {R : Type*} [CommRing R] [DGRing A] [Algebra R A] [DGAlgebra R A]


-- @@ L122-124 verbatim
/-- The homotopy category of a dg `R`-algebra is `R`-linear. -/
instance (priority := 100) instLinear : Linear R (HomotopyCategory.{v} A) :=
  Quotient.linear R (DGModuleCat.homotopic.{v} A) fun r _ _ _ _ h => Homotopic.smul r h


-- @@ L126-127 verbatim
instance (priority := 100) quotient_linear : (quotient A).Linear R where
  map_smul _ _ := rfl


-- @@ L129-129 verbatim
end Linear


-- @@ L131-131 verbatim
variable {A}


-- @@ L133-135 verbatim
theorem quotient_obj_surjective (X : HomotopyCategory.{v} A) :
    ∃ M : DGModuleCat.{v} A, (quotient A).obj M = X :=
  ⟨_, rfl⟩


-- @@ L137-140 verbatim
@[simp]
theorem quotient_map_out {M N : HomotopyCategory.{v} A} (f : M ⟶ N) :
    (quotient A).map (Quot.out f) = f :=
  Quot.out_eq _


-- @@ L142-146 verbatim
/-- Two morphisms of dg modules become equal in the homotopy category iff they are
homotopic. -/
theorem quotient_map_eq_iff {M N : DGModuleCat.{v} A} (f g : M ⟶ N) :
    (quotient A).map f = (quotient A).map g ↔ Homotopic f.hom g.hom :=
  Quotient.functor_map_eq_iff _ _ _


-- @@ L148-150 verbatim
theorem eq_of_homotopy {M N : DGModuleCat.{v} A} (f g : M ⟶ N) (h : DGHomotopy f.hom g.hom) :
    (quotient A).map f = (quotient A).map g :=
  (quotient_map_eq_iff f g).mpr ⟨h⟩


-- @@ L152-155 verbatim
/-- A homotopy between two morphisms which become equal in the homotopy category. -/
noncomputable def homotopyOfEq {M N : DGModuleCat.{v} A} (f g : M ⟶ N)
    (w : (quotient A).map f = (quotient A).map g) : DGHomotopy f.hom g.hom :=
  ((quotient_map_eq_iff f g).mp w).some


-- @@ L157-168 verbatim
/-- Homotopy equivalent dg modules are isomorphic in the homotopy category. -/
@[simps]
def isoOfHomotopyEquiv {M N : DGModuleCat.{v} A} (e : DGHomotopyEquiv A M N) :
    (quotient A).obj M ≅ (quotient A).obj N where
  hom := (quotient A).map (DGModuleCat.ofHom e.hom)
  inv := (quotient A).map (DGModuleCat.ofHom e.inv)
  hom_inv_id := by
    rw [← (quotient A).map_comp, ← (quotient A).map_id]
    exact eq_of_homotopy _ _ e.homotopyHomInvId
  inv_hom_id := by
    rw [← (quotient A).map_comp, ← (quotient A).map_id]
    exact eq_of_homotopy _ _ e.homotopyInvHomId


-- @@ L170-175 verbatim
/-- A dg module is a zero object of the homotopy category iff it is contractible. -/
theorem isZero_quotient_obj_iff (M : DGModuleCat.{v} A) :
    IsZero ((quotient A).obj M) ↔ IsContractible A M := by
  rw [IsZero.iff_id_eq_zero, ← (quotient A).map_id, ← (quotient A).map_zero,
    quotient_map_eq_iff]
  rfl


-- @@ L177-177 verbatim
/-! ### Morphisms in the homotopy category -/


-- @@ L179-179 verbatim
section Hom


-- @@ L181-181 verbatim
variable (M N : DGModuleCat.{v} A)


-- @@ L183-192 expanded
/-- The additive map from morphisms of dg modules modulo null-homotopic ones to morphisms in
the homotopy category. -/
def quotientNullHomotopicAddHom :
    ((DGModuleHom A M N) ⧸ nullHomotopic A M N) →+ ((quotient A).obj M ⟶ (quotient A).obj N) :=
  QuotientAddGroup.lift _
    ((quotient A).mapAddHom.comp (DGModuleCat.homAddEquiv (M := M) (N := N)).symm.toAddMonoidHom)
    fun f hf => by
    change (quotient A).map (DGModuleCat.ofHom f) = 0
    rw [← (quotient A).map_zero M N, quotient_map_eq_iff]
    exact hf


-- @@ L194-198 expanded
@[simp]
theorem quotientNullHomotopicAddHom_mk (f : DGModuleHom A M N) :
    quotientNullHomotopicAddHom M N (QuotientAddGroup.mk f) =
      (quotient A).map (DGModuleCat.ofHom f) :=
  rfl


-- @@ L200-209 verbatim
theorem quotientNullHomotopicAddHom_bijective :
    Function.Bijective (quotientNullHomotopicAddHom M N) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun φ => ?_⟩
  · induction x using QuotientAddGroup.induction_on with
    | H f =>
      rw [quotientNullHomotopicAddHom_mk, ← (quotient A).map_zero M N,
        quotient_map_eq_iff] at hx
      exact (QuotientAddGroup.eq_zero_iff f).mpr hx
  · obtain ⟨f, rfl⟩ := (quotient A).map_surjective φ
    exact ⟨QuotientAddGroup.mk f.hom, rfl⟩


-- @@ L211-215 expanded
/-- Morphisms in the homotopy category are morphisms of dg modules modulo null-homotopic
ones. -/
noncomputable def homAddEquivQuotient :
    ((quotient A).obj M ⟶ (quotient A).obj N) ≃+ ((DGModuleHom A M N) ⧸ nullHomotopic A M N) :=
  (AddEquiv.ofBijective _ (quotientNullHomotopicAddHom_bijective M N)).symm


-- @@ L217-221 verbatim
@[simp]
theorem homAddEquivQuotient_quotient_map (f : M ⟶ N) :
    homAddEquivQuotient M N ((quotient A).map f) = QuotientAddGroup.mk f.hom := by
  rw [homAddEquivQuotient, AddEquiv.symm_apply_eq]
  rfl


-- @@ L223-227 verbatim
/-- `Hom_{H(A)}(M, N) ≅ H⁰(HOM_A(M, N))`: morphisms in the homotopy category are the `0`-th
cohomology of the Hom complex. -/
noncomputable def homAddEquivCohomology :
    ((quotient A).obj M ⟶ (quotient A).obj N) ≃+ cohomology (DGModule.HOM A M N) 0 :=
  (homAddEquivQuotient M N).trans (quotientNullHomotopicAddEquivCohomology A M N)


-- @@ L229-234 verbatim
@[simp]
theorem homAddEquivCohomology_quotient_map (f : M ⟶ N) :
    homAddEquivCohomology M N ((quotient A).map f) =
      cohomology.mk _ 0 (DGModule.HOM.cocyclesAddEquiv A M N 0 (Cocycle.ofHom f.hom)) := by
  rw [homAddEquivCohomology, AddEquiv.trans_apply, homAddEquivQuotient_quotient_map,
    quotientNullHomotopicAddEquivCohomology_mk]


-- @@ L236-236 verbatim
end Hom


-- @@ L238-238 verbatim
end HomotopyCategory


-- @@ L240-240 verbatim
end DG
