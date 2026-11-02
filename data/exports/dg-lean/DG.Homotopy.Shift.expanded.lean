import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import DG.Homotopy.Forget
import DG.Homotopy.HomotopyCategory
import DG.Module.HomShift


-- @@ L6-31 verbatim
/-!
# The shift on dg modules and on the homotopy category

Let `A` be a dg ring. This file equips the category `DG.DGModuleCat A` of dg `A`-modules and
the homotopy category `DG.HomotopyCategory A` with shifts by `ℤ` (`CategoryTheory.HasShift`),
and shows that the forgetful functor to cochain complexes commutes with the shifts.

## Main definitions and results

* `DG.DGModuleCat.hasShift`: the shift on `DGModuleCat A`, built with Mathlib's `hasShiftMk`
  from `M ↦ DG.Shift n M` on objects and `DG.DGModuleHom.shift` on morphisms. The isomorphisms
  `M⟦0⟧ ≅ M` and `M⟦a + b⟧ ≅ M⟦a⟧⟦b⟧` are the identity on underlying elements
  (`DG.Shift.zeroEquiv`, `DG.Shift.shiftShiftEquiv`), so that all the coherences are checked
  elementwise. The shift functors are additive and, for a dg `R`-algebra, `R`-linear.
* `DG.DGHomotopy.shift`: a homotopy `h` from `f` to `g` gives a homotopy
  `(-1)ⁿ • h⟦n⟧` from `f⟦n⟧` to `g⟦n⟧` (Mathlib's `Homotopy.shift`, with the same sign).
* `DG.HomotopyCategory.hasShift`: the induced shift on the homotopy category
  (`CategoryTheory.HasShift.quotient`), for which the quotient functor commutes with the shift
  (`DG.HomotopyCategory.commShiftQuotient`).
* `DG.DGModuleCat.forgetCommShift`: the forgetful functor
  `DG.DGModuleCat.forget R A : DGModuleCat A ⥤ CochainComplex (ModuleCat R) ℤ` commutes with
  the shifts. In degree `i`, the component `(Shift n M)ⁱ = Mⁱ⁺ⁿ` is identified with
  `(K⟦n⟧).X i = K.X (i + n)`, and the differential `(-1)ⁿ d` of `Shift n M` is the differential
  `n.negOnePow • K.d` of Mathlib's shifted complex: this is the comparison of the sign
  conventions of `DG.Shift` and `CochainComplex.shiftFunctor`.
-/


-- @@ L33-33 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L35-35 verbatim
universe v u w


-- @@ L37-37 verbatim
namespace DG


-- @@ L39-39 verbatim
namespace Shift


-- @@ L41-42 verbatim
variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]


-- @@ L44-61 expanded
/-- The identification `M⟦c⟧ ≃ M⟦a⟧⟦b⟧` when `a + b = c`, the identity on underlying
elements. -/
def shiftShiftEquiv (a b c : ℤ) (h : a + b = c) : DGModuleEquiv A (Shift c M) (Shift b (Shift a M))
    where
  toFun x := mk b (mk a (unmk c x))
  invFun y := mk c (unmk a (unmk b y))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r
    x := by
    change mk b (mk a (unmk c (r • x))) = r • mk b (mk a (unmk c x))
    rw [unmk_smul_eq, smul_mk_eq, smul_mk_eq, twist_twist, ← h]
  map_mem' {k x}
    hx := by
    rw [mem_grading_iff', ← h] at hx
    rw [mem_grading_iff, mem_grading_iff, add_assoc, add_comm b a]
    exact hx
  map_d'
    x := by
    rw [unmk_d, d_mk, d_mk, ← h, koszulSign_add, mul_comm, ← smul_smul]
    rfl


-- @@ L63-65 verbatim
@[simp]
theorem shiftShiftEquiv_apply (a b c : ℤ) (h : a + b = c) (x : Shift c M) :
    shiftShiftEquiv (A := A) a b c h x = mk b (mk a (unmk c x)) := rfl


-- @@ L67-69 verbatim
@[simp]
theorem shiftShiftEquiv_symm_apply (a b c : ℤ) (h : a + b = c) (y : Shift b (Shift a M)) :
    (shiftShiftEquiv (A := A) a b c h).symm y = mk c (unmk a (unmk b y)) := rfl


-- @@ L71-73 expanded
/-- The identification `M⟦a⟧⟦b⟧ ≃ M⟦b⟧⟦a⟧`, the identity on underlying elements. -/
def shiftComm (a b : ℤ) : DGModuleEquiv A (Shift b (Shift a M)) (Shift a (Shift b M)) :=
  (shiftShiftEquiv a b (a + b) rfl).symm.trans (shiftShiftEquiv b a (a + b) (add_comm b a))


-- @@ L75-77 verbatim
@[simp]
theorem shiftComm_apply (a b : ℤ) (x : Shift b (Shift a M)) :
    shiftComm (A := A) a b x = mk a (mk b (unmk a (unmk b x))) := rfl


-- @@ L79-79 verbatim
variable (R : Type*) [CommRing R] [Algebra R A] [DGAlgebra R A]


-- @@ L81-82 verbatim
theorem twist_algebraMap (n : ℤ) (r : R) : twist A n (algebraMap R A r) = algebraMap R A r := by
  rw [twist_of_mem (algebraMap_mem_grading R r), mul_zero, koszulSign_zero, one_smul]


-- @@ L84-87 verbatim
omit [DGAddCommGroup M] in
theorem algebraMap_smul_mk (n : ℤ) (r : R) (m : M) :
    algebraMap R A r • mk n m = mk n (algebraMap R A r • m) := by
  rw [smul_mk_eq, twist_algebraMap]


-- @@ L89-89 verbatim
end Shift


-- @@ L91-100 expanded
/-- An isomorphism of dg modules as an isomorphism in `DGModuleCat A`. -/
@[simps]
def DGModuleEquiv.toDGModuleCatIso {A : Type u} [Ring A] [DGAddCommGroup A] {M N : Type v}
    [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] (e : DGModuleEquiv A M N) :
    DGModuleCat.of A M ≅ DGModuleCat.of A N
    where
  hom := DGModuleCat.ofHom e.toDGModuleHom
  inv := DGModuleCat.ofHom e.symm.toDGModuleHom
  hom_inv_id := DGModuleCat.hom_ext_apply fun x => e.symm_apply_apply x
  inv_hom_id := DGModuleCat.hom_ext_apply fun x => e.apply_symm_apply x


-- @@ L102-102 verbatim
/-! ### The shift on dg modules -/


-- @@ L104-104 verbatim
namespace DGModuleCat


-- @@ L106-106 verbatim
open Shift


-- @@ L108-108 verbatim
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]


-- @@ L110-115 verbatim
/-- The shift functor `M ↦ Shift n M` on dg modules (auxiliary definition for
`DG.DGModuleCat.hasShift`; use `shiftFunctor (DGModuleCat A) n`). -/
@[simps obj]
def shiftFunctorAux (n : ℤ) : DGModuleCat.{v} A ⥤ DGModuleCat.{v} A where
  obj M := of A (Shift n M)
  map f := ofHom (f.hom.shift n)


-- @@ L117-119 verbatim
/-- The shift by `0` is the identity (auxiliary definition for `DG.DGModuleCat.hasShift`). -/
def shiftFunctorZeroAux : shiftFunctorAux.{v} A 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => Shift.zeroEquiv.toDGModuleCatIso) fun _ => rfl


-- @@ L121-125 verbatim
/-- The shift by `a + b` is the shift by `a` followed by the shift by `b` (auxiliary definition
for `DG.DGModuleCat.hasShift`). -/
def shiftFunctorAddAux (a b : ℤ) :
    shiftFunctorAux.{v} A (a + b) ≅ shiftFunctorAux A a ⋙ shiftFunctorAux A b :=
  NatIso.ofComponents (fun _ => (shiftShiftEquiv a b (a + b) rfl).toDGModuleCatIso) fun _ => rfl


-- @@ L127-131 verbatim
theorem eqToHom_shift_apply {a b : ℤ} (h : a = b) (M : DGModuleCat.{v} A)
    (p : (shiftFunctorAux A a).obj M = (shiftFunctorAux A b).obj M) (x : Shift a M) :
    (eqToHom p) x = Shift.mk b (unmk a x) := by
  subst h
  rfl


-- @@ L133-150 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The shift on dg modules: `M⟦n⟧ = Shift n M`. -/
instance hasShift : HasShift (DGModuleCat.{v} A) ℤ :=
  hasShiftMk _ _
    { F := shiftFunctorAux A
      zero := shiftFunctorZeroAux A
      add := shiftFunctorAddAux A
      assoc_hom_app := fun m₁ m₂ m₃ X => hom_ext_apply fun x => by
        rw [comp_apply, comp_apply, comp_apply, eqToHom_shift_apply A (add_assoc m₁ m₂ m₃)]
        rfl
      zero_add_hom_app := fun n X => hom_ext_apply fun x => by
        rw [comp_apply]
        erw [eqToHom_shift_apply A (zero_add n)]
        rfl
      add_zero_hom_app := fun n X => hom_ext_apply fun x => by
        rw [comp_apply]
        erw [eqToHom_shift_apply A (add_zero n)]
        rfl }


-- @@ L152-152 verbatim
variable {A}


-- @@ L154-156 verbatim
@[simp]
theorem shiftFunctor_obj (n : ℤ) (M : DGModuleCat.{v} A) :
    (shiftFunctor (DGModuleCat.{v} A) n).obj M = of A (Shift n M) := rfl


-- @@ L158-160 verbatim
@[simp]
theorem shiftFunctor_map_hom (n : ℤ) {M N : DGModuleCat.{v} A} (f : M ⟶ N) :
    ((shiftFunctor (DGModuleCat.{v} A) n).map f).hom = f.hom.shift n := rfl


-- @@ L162-163 verbatim
theorem shiftFunctor_map_apply (n : ℤ) {M N : DGModuleCat.{v} A} (f : M ⟶ N) (x : Shift n M) :
    ((shiftFunctor (DGModuleCat.{v} A) n).map f) x = Shift.mk n (f (unmk n x)) := rfl


-- @@ L165-166 verbatim
theorem shiftFunctorZero_hom_app_apply (M : DGModuleCat.{v} A) (x : Shift 0 M) :
    ((shiftFunctorZero (DGModuleCat.{v} A) ℤ).hom.app M) x = unmk 0 x := rfl


-- @@ L168-169 verbatim
theorem shiftFunctorZero_inv_app_apply (M : DGModuleCat.{v} A) (x : M) :
    ((shiftFunctorZero (DGModuleCat.{v} A) ℤ).inv.app M) x = Shift.mk 0 x := rfl


-- @@ L171-176 verbatim
theorem shiftFunctorAdd'_hom_app_apply (a b c : ℤ) (h : a + b = c) (M : DGModuleCat.{v} A)
    (x : Shift c M) :
    ((shiftFunctorAdd' (DGModuleCat.{v} A) a b c h).hom.app M) x =
      Shift.mk b (Shift.mk a (unmk c x)) := by
  subst h
  rfl


-- @@ L178-183 verbatim
theorem shiftFunctorAdd'_inv_app_apply (a b c : ℤ) (h : a + b = c) (M : DGModuleCat.{v} A)
    (x : Shift b (Shift a M)) :
    ((shiftFunctorAdd' (DGModuleCat.{v} A) a b c h).inv.app M) x =
      Shift.mk c (unmk a (unmk b x)) := by
  subst h
  rfl


-- @@ L185-187 verbatim
theorem shiftFunctorAdd_hom_app_apply (a b : ℤ) (M : DGModuleCat.{v} A) (x : Shift (a + b) M) :
    ((shiftFunctorAdd (DGModuleCat.{v} A) a b).hom.app M) x =
      Shift.mk b (Shift.mk a (unmk (a + b) x)) := rfl


-- @@ L189-192 verbatim
theorem shiftFunctorAdd_inv_app_apply (a b : ℤ) (M : DGModuleCat.{v} A)
    (x : Shift b (Shift a M)) :
    ((shiftFunctorAdd (DGModuleCat.{v} A) a b).inv.app M) x =
      Shift.mk (a + b) (unmk a (unmk b x)) := rfl


-- @@ L194-201 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem shiftFunctorComm_hom_app_apply (a b : ℤ) (M : DGModuleCat.{v} A)
    (x : Shift b (Shift a M)) :
    ((shiftFunctorComm (DGModuleCat.{v} A) a b).hom.app M) x =
      Shift.mk a (Shift.mk b (unmk a (unmk b x))) := by
  rw [shiftFunctorComm_eq _ a b _ rfl, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    comp_apply, shiftFunctorAdd'_inv_app_apply, shiftFunctorAdd'_hom_app_apply]
  rfl


-- @@ L203-206 verbatim
theorem shiftFunctorComm_hom_app_eq (a b : ℤ) (M : DGModuleCat.{v} A) :
    (shiftFunctorComm (DGModuleCat.{v} A) a b).hom.app M =
      ofHom (Shift.shiftComm (M := M) a b).toDGModuleHom :=
  hom_ext_apply fun x => shiftFunctorComm_hom_app_apply a b M x


-- @@ L208-209 verbatim
instance (n : ℤ) : (shiftFunctor (DGModuleCat.{v} A) n).Additive where
  map_add := rfl


-- @@ L211-213 verbatim
instance (priority := 100) shiftFunctor_linear (R : Type*) [CommRing R] [Algebra R A]
    [DGAlgebra R A] (n : ℤ) : (shiftFunctor (DGModuleCat.{v} A) n).Linear R where
  map_smul f r := hom_ext_apply fun x => (Shift.algebraMap_smul_mk R n r (f (unmk n x))).symm


-- @@ L215-215 verbatim
end DGModuleCat


-- @@ L217-217 verbatim
/-! ### Shifts of homotopies -/


-- @@ L219-219 verbatim
namespace DGHomotopy


-- @@ L221-223 expanded
variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [DGModule A M] [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [DGModule A N] {f g : DGModuleHom A M N}


-- @@ L225-232 verbatim
/-- A homotopy `h` from `f` to `g` induces the homotopy `(-1)ⁿ • h⟦n⟧` from `f⟦n⟧` to `g⟦n⟧`
(Mathlib's `Homotopy.shift`, with the same sign). -/
@[simps]
def shift (h : DGHomotopy f g) (n : ℤ) : DGHomotopy (f.shift n) (g.shift n) where
  hom := koszulSign n • h.hom.shift n
  ofHom_eq := by
    rw [δ_units_smul, Cochain.δ_shift, smul_smul, Int.units_mul_self, one_smul,
      ← Cochain.shift_ofHom, ← Cochain.shift_ofHom, h.ofHom_eq, Cochain.shift_add]


-- @@ L234-234 verbatim
end DGHomotopy


-- @@ L236-240 expanded
theorem Homotopic.shift {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] [AddCommGroup N]
    [DGAddCommGroup N] [Module A N] [DGModule A N] {f g : DGModuleHom A M N} (h : Homotopic f g)
    (n : ℤ) : Homotopic (f.shift n) (g.shift n) :=
  ⟨h.some.shift n⟩


-- @@ L242-242 verbatim
/-! ### The shift on the homotopy category -/


-- @@ L244-244 verbatim
namespace HomotopyCategory


-- @@ L246-246 verbatim
variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]


-- @@ L248-249 verbatim
instance : (DGModuleCat.homotopic.{v} A).IsCompatibleWithShift ℤ :=
  ⟨fun n _ _ _ _ h => Homotopic.shift h n⟩


-- @@ L251-253 verbatim
/-- The shift on the homotopy category, induced by the shift on dg modules. -/
noncomputable instance hasShift : HasShift (HomotopyCategory.{v} A) ℤ :=
  HasShift.quotient (DGModuleCat.homotopic.{v} A) ℤ


-- @@ L255-257 verbatim
/-- The quotient functor from dg modules to the homotopy category commutes with the shift. -/
noncomputable instance commShiftQuotient : (quotient A).CommShift ℤ :=
  Quotient.functor_commShift (DGModuleCat.homotopic.{v} A) ℤ


-- @@ L259-262 verbatim
instance (n : ℤ) : (shiftFunctor (HomotopyCategory.{v} A) n).Additive := by
  have : (quotient A ⋙ shiftFunctor _ n).Additive :=
    Functor.additive_of_iso ((quotient A).commShiftIso n)
  exact Functor.additive_of_full_essSurj_comp (quotient A) _


-- @@ L264-264 verbatim
end HomotopyCategory


-- @@ L266-266 verbatim
/-! ### The forgetful functor commutes with the shifts -/


-- @@ L268-268 verbatim
namespace DGModuleCat


-- @@ L270-270 verbatim
open Shift DGModuleCat.Algebra


-- @@ L272-273 verbatim
variable (R : Type w) {A : Type u} [CommRing R] [Ring A] [DGAddCommGroup A] [Algebra R A]
  [DGRing A] [DGAlgebra R A]


-- @@ L275-280 verbatim
theorem toComplex_d_hom_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i + 1 = j)
    (x : DGModule.gradingSubmodule R A M i) :
    (((toComplex R M).d i j).hom x).1 = d (x : M) := by
  subst h
  rw [toComplex_d]
  rfl


-- @@ L282-286 verbatim
theorem toComplex_XIsoOfEq_hom_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i = j)
    (x : DGModule.gradingSubmodule R A M i) :
    (((toComplex R M).XIsoOfEq h).hom.hom x).1 = x := by
  subst h
  rfl


-- @@ L288-292 verbatim
theorem forget_obj_XIsoOfEq_hom_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i = j)
    (x : DGModule.gradingSubmodule R A M i) :
    ((((forget R A).obj M).XIsoOfEq h).hom.hom x).1 = x := by
  subst h
  rfl


-- @@ L294-298 verbatim
theorem toComplex_XIsoOfEq_inv_apply (M : DGModuleCat.{v} A) {i j : ℤ} (h : i = j)
    (x : DGModule.gradingSubmodule R A M j) :
    (((toComplex R M).XIsoOfEq h).inv.hom x).1 = x := by
  subst h
  rfl


-- @@ L300-312 verbatim
/-- The homogeneous component `(M⟦n⟧)ⁱ = Mⁱ⁺ⁿ`, as an `R`-linear equivalence. -/
def shiftGradingLinearEquiv (M : DGModuleCat.{v} A) (n i : ℤ) :
    DGModule.gradingSubmodule R A ((shiftFunctor (DGModuleCat.{v} A) n).obj M) i ≃ₗ[R]
      DGModule.gradingSubmodule R A M (i + n) where
  toFun x := ⟨unmk n x.1, x.2⟩
  invFun y := ⟨Shift.mk n y.1, y.2⟩
  map_add' _ _ := rfl
  map_smul' r x := Subtype.ext (by
    have h := unmk_smul_eq (n := n) (M := M) (algebraMap R A r) x.1
    rw [twist_algebraMap] at h
    exact h)
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L314-330 verbatim
/-- The underlying cochain complex of `M⟦n⟧` is the shifted underlying cochain complex of `M`:
in degree `i` both are `Mⁱ⁺ⁿ`, and the differentials are `(-1)ⁿ d`. -/
def forgetShiftIso (n : ℤ) (M : DGModuleCat.{v} A) :
    (forget R A).obj ((shiftFunctor (DGModuleCat.{v} A) n).obj M) ≅
      (shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) n).obj ((forget R A).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (shiftGradingLinearEquiv R M n i).toModuleIso) (by
      rintro i j (rfl : i + 1 = j)
      refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
      have h1 := toComplex_d_hom_apply R M (show i + n + 1 = i + 1 + n by ring)
        (shiftGradingLinearEquiv R M n i x)
      have h2 := toComplex_d_hom_apply R ((shiftFunctor (DGModuleCat.{v} A) n).obj M) rfl x
      change n.negOnePow • (((toComplex R M).d (i + n) (i + 1 + n)).hom
          (shiftGradingLinearEquiv R M n i x)).1 =
        unmk n (((toComplex R ((shiftFunctor (DGModuleCat.{v} A) n).obj M)).d i (i + 1)).hom x).1
      rw [h1, h2]
      rfl)


-- @@ L332-334 verbatim
theorem forgetShiftIso_hom_f_apply (n : ℤ) (M : DGModuleCat.{v} A) (i : ℤ)
    (x : DGModule.gradingSubmodule R A ((shiftFunctor (DGModuleCat.{v} A) n).obj M) i) :
    (((forgetShiftIso R n M).hom.f i).hom x).1 = unmk n x.1 := rfl


-- @@ L336-338 verbatim
theorem forgetShiftIso_inv_f_apply (n : ℤ) (M : DGModuleCat.{v} A) (i : ℤ)
    (x : DGModule.gradingSubmodule R A M (i + n)) :
    (((forgetShiftIso R n M).inv.f i).hom x).1 = Shift.mk n x.1 := rfl


-- @@ L340-342 verbatim
theorem forget_map_f_apply {M N : DGModuleCat.{v} A} (f : M ⟶ N) (i : ℤ)
    (x : DGModule.gradingSubmodule R A M i) :
    ((((forget R A).map f).f i).hom x).1 = f x.1 := rfl


-- @@ L344-349 verbatim
/-- The commutation of the forgetful functor with the shifts. -/
def forgetCommShiftIso (n : ℤ) :
    shiftFunctor (DGModuleCat.{v} A) n ⋙ forget R A ≅
      forget R A ⋙ shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ) n :=
  NatIso.ofComponents (forgetShiftIso R n) fun _ =>
    HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)


-- @@ L351-353 verbatim
theorem forgetCommShiftIso_hom_app_f_apply (n : ℤ) (M : DGModuleCat.{v} A) (i : ℤ)
    (x : DGModule.gradingSubmodule R A ((shiftFunctor (DGModuleCat.{v} A) n).obj M) i) :
    ((((forgetCommShiftIso R n).hom.app M).f i).hom x).1 = unmk n x.1 := rfl


-- @@ L355-376 verbatim
/-- The forgetful functor from dg modules to cochain complexes commutes with the shifts. -/
instance forgetCommShift : (forget R A).CommShift ℤ where
  commShiftIso := forgetCommShiftIso R
  commShiftIso_zero := by
    ext M : 3
    rw [Functor.CommShift.isoZero_hom_app]
    ext i x : 3
    apply Subtype.ext
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CochainComplex.shiftFunctorZero_inv_app_f]
    exact (forget_obj_XIsoOfEq_hom_apply R M (show i = i + 0 by omega)
      ((((forget R A).map ((shiftFunctorZero (DGModuleCat.{v} A) ℤ).hom.app M)).f i).hom x)).symm
  commShiftIso_add a b := by
    ext M : 3
    rw [Functor.CommShift.isoAdd_hom_app]
    ext i x : 3
    apply Subtype.ext
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      CochainComplex.shiftFunctorAdd_inv_app_f]
    symm
    refine (forget_obj_XIsoOfEq_hom_apply R M _ _).trans ?_
    rfl


-- @@ L378-378 verbatim
end DGModuleCat


-- @@ L380-380 verbatim
end DG
