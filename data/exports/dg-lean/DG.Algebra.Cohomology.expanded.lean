import DG.Algebra.Hom
import DG.Module.Cohomology


-- @@ L4-16 verbatim
/-!
# Functoriality of the cohomology ring

For a morphism of dg rings `f : A →ᵈᵍ+* B`, the maps `Hⁿ(f) : Hⁿ(A) → Hⁿ(B)` are compatible with
the graded products, so that they assemble to a morphism of dg rings `H(f) : H(A) → H(B)` of the
cohomology rings (`DG.Cohomology A`, with zero differential).

* `DG.DGRingHom.cohomologyMap f n`: the map `Hⁿ(A) →+ Hⁿ(B)` (the map of `DG.cohomology`
  induced by the underlying chain map), with `cohomologyMap_one`, `cohomologyMap_mul`.
* `DG.DGRingHom.cohomologyRingMap f`: the morphism of dg rings `H(A) →ᵈᵍ+* H(B)`; identity and
  composition.
* `DG.DGRingHom.IsQuasiIso f`: `f` induces isomorphisms on all cohomology groups.
-/


-- @@ L18-18 verbatim
open DirectSum GradedMonoid


-- @@ L20-20 verbatim
namespace DG


-- @@ L22-22 verbatim
namespace DGRingHom


-- @@ L24-25 expanded
variable {A B C : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B] [Ring C]
  [DGAddCommGroup C] (f : DGRingHom A B)


-- @@ L27-29 verbatim
/-- The map on cocycles induced by a morphism of dg rings. -/
def cocyclesMap (n : ℤ) : cocycles A n →+ cocycles B n :=
  cocycles.mapAddMonoidHom f.toRingHom.toAddMonoidHom (fun ha => f.map_mem ha) f.map_d n


-- @@ L31-32 verbatim
@[simp]
theorem coe_cocyclesMap (n : ℤ) (a : cocycles A n) : (f.cocyclesMap n a : B) = f a := rfl


-- @@ L34-36 verbatim
/-- The map `Hⁿ(A) → Hⁿ(B)` induced by a morphism of dg rings. -/
def cohomologyMap (n : ℤ) : cohomology A n →+ cohomology B n :=
  cohomology.mapAddMonoidHom f.toRingHom.toAddMonoidHom (fun ha => f.map_mem ha) f.map_d n


-- @@ L38-41 verbatim
@[simp]
theorem cohomologyMap_mk (n : ℤ) (a : cocycles A n) :
    f.cohomologyMap n (cohomology.mk A n a) = cohomology.mk B n (f.cocyclesMap n a) :=
  cohomology.mapAddMonoidHom_mk _ _ _ n a


-- @@ L43-46 verbatim
theorem cohomologyMap_mkOf {n : ℤ} {a : A} (ha : a ∈ grading n) (hd : d a = 0) :
    f.cohomologyMap n (cohomology.mkOf ha hd) =
      cohomology.mkOf (f.map_mem ha) (by rw [← f.map_d, hd, map_zero]) :=
  cohomology.mapAddMonoidHom_mkOf _ _ _ ha hd


-- @@ L48-52 expanded
variable (A) in
theorem cohomologyMap_id (n : ℤ) :
    (DGRingHom.id : DGRingHom A A).cohomologyMap n = AddMonoidHom.id _ :=
  by
  ext a
  rfl


-- @@ L54-57 expanded
theorem cohomologyMap_comp (g : DGRingHom B C) (n : ℤ) :
    (g.comp f).cohomologyMap n = (g.cohomologyMap n).comp (f.cohomologyMap n) :=
  by
  ext a
  rfl


-- @@ L59-62 verbatim
/-- A morphism of dg rings is a quasi-isomorphism if it induces isomorphisms on all cohomology
groups. -/
def IsQuasiIso : Prop :=
  ∀ n : ℤ, Function.Bijective (f.cohomologyMap n)


-- @@ L64-67 expanded
variable (A) in
theorem isQuasiIso_id : IsQuasiIso (DGRingHom.id : DGRingHom A A) := fun n =>
  by
  rw [cohomologyMap_id]
  exact Function.bijective_id


-- @@ L69-72 expanded
theorem IsQuasiIso.comp {g : DGRingHom B C} {f : DGRingHom A B} (hg : IsQuasiIso g)
    (hf : IsQuasiIso f) : IsQuasiIso (g.comp f) := fun n =>
  by
  rw [cohomologyMap_comp]
  exact (hg n).comp (hf n)


-- @@ L74-74 verbatim
variable [DGRing A] [DGRing B] [DGRing C]


-- @@ L76-78 verbatim
theorem cohomologyMap_one : f.cohomologyMap 0 GOne.one = GOne.one := by
  rw [Cohomology.one_def, cohomologyMap_mk]
  exact congrArg (cohomology.mk B 0) (Subtype.ext (map_one f))


-- @@ L80-89 verbatim
theorem cohomologyMap_mul {i j : ℤ} (x : cohomology A i) (y : cohomology A j) :
    f.cohomologyMap (i + j) (GMul.mul x y) =
      GMul.mul (f.cohomologyMap i x) (f.cohomologyMap j y) := by
  induction x using cohomology.induction_on with
  | h a =>
  induction y using cohomology.induction_on with
  | h b =>
    rw [Cohomology.mk_mul_mk, cohomologyMap_mk, cohomologyMap_mk, cohomologyMap_mk,
      Cohomology.mk_mul_mk]
    exact congrArg (cohomology.mk B (i + j)) (Subtype.ext (by simp))


-- @@ L91-99 verbatim
/-- The ring homomorphism `H(A) →+* H(B)` induced by a morphism of dg rings `A → B`; see
`DGRingHom.cohomologyRingMap` for the morphism of dg rings. -/
def cohomologyRingHom : Cohomology A →+* Cohomology B :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (fun n => cohomology B n) n).comp (f.cohomologyMap n))
    (by rw [AddMonoidHom.comp_apply, cohomologyMap_one]; rfl)
    (fun {i j} x y => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        cohomologyMap_mul, DirectSum.of_mul_of])


-- @@ L101-105 verbatim
@[simp]
theorem cohomologyRingHom_of (n : ℤ) (x : cohomology A n) :
    f.cohomologyRingHom (DirectSum.of (fun n => cohomology A n) n x) =
      DirectSum.of (fun n => cohomology B n) n (f.cohomologyMap n x) :=
  DirectSum.toSemiring_of _ _ _ n x


-- @@ L107-113 expanded
/-- The morphism of dg rings `H(A) → H(B)` induced by a morphism of dg rings `A → B`. -/
def cohomologyRingMap : DGRingHom (Cohomology A) (Cohomology B)
    where
  __ := f.cohomologyRingHom
  map_mem' := by
    rintro n _ ⟨x, rfl⟩
    exact ⟨f.cohomologyMap n x, (f.cohomologyRingHom_of n x).symm⟩
  map_d' _ := by simp


-- @@ L115-119 verbatim
@[simp]
theorem cohomologyRingMap_of (n : ℤ) (x : cohomology A n) :
    f.cohomologyRingMap (DirectSum.of (fun n => cohomology A n) n x) =
      DirectSum.of (fun n => cohomology B n) n (f.cohomologyMap n x) :=
  f.cohomologyRingHom_of n x


-- @@ L121-128 expanded
variable (A) in
theorem cohomologyRingMap_id : (DGRingHom.id : DGRingHom A A).cohomologyRingMap = DGRingHom.id :=
  by
  refine DGRingHom.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x => rw [cohomologyRingMap_of, cohomologyMap_id]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]


-- @@ L130-139 expanded
theorem cohomologyRingMap_comp (g : DGRingHom B C) :
    (g.comp f).cohomologyRingMap = g.cohomologyRingMap.comp f.cohomologyRingMap :=
  by
  refine DGRingHom.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n
    x =>
    rw [cohomologyRingMap_of, cohomologyMap_comp, DGRingHom.comp_apply, cohomologyRingMap_of,
      cohomologyRingMap_of]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]


-- @@ L141-141 verbatim
end DGRingHom


-- @@ L143-143 verbatim
end DG
