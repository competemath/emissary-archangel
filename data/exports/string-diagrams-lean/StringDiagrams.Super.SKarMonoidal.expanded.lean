import StringDiagrams.Super.SKar
import StringDiagrams.Super.KaroubiMonoidal
import StringDiagrams.Super.MonoidalPi
import Mathlib.CategoryTheory.Idempotents.FunctorExtension


-- @@ L6-26 verbatim
/-!
# The super Karoubi envelope of a monoidal supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §1.5.

Let `A` be a monoidal supercategory. The underlying category `A̲_π` of its Π-envelope is a
monoidal category, hence so are its additive envelope and `SKar(A) = Kar(A̲_π)`
(`StringDiagrams.Super.KaroubiMonoidal`). We show:

* In `A̲_π` the functor `Π` is isomorphic to `π ⊗ -` and to `- ⊗ π` (`SKar.piIsoTensorLeft`,
  `SKar.piIsoTensorRight`), by the even isomorphisms `Π λ ≅ λ ≅ π ⊗ λ` built from the two odd
  isomorphisms `ζ`; these isomorphisms extend to `SKar(A)` (`SKar.piObjIsoTensorLeft`,
  `SKar.piObjIsoTensorRight`).
* `K₀(SKar(A))` is a ring (`K₀.instRing`) and a `Zπ`-algebra with `π ↦ [π]`
  (`SKar.instAlgebraZπ`): `[π]² = 1` and `[π]` is central. The resulting action of `π` is the
  involution `[V] ↦ [Π V]` of §1.5 (`SKar.algebraMap_π`, `SKar.π_smul_eq`,
  `SKar.π_smul_mk_algebra`).

The monoidal Π-category structure of `SKar(A)` (Definition 1.14: the half-braiding `β`, `ξ` and
(1.8)) is constructed in `StringDiagrams.Super.SKarMonoidalPi`.
-/


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace StringDiagrams


-- @@ L32-32 verbatim
open CategoryTheory MonoidalCategory Limits Idempotents Supercategory


-- @@ L34-34 verbatim
universe w v u


-- @@ L36-36 verbatim
/-! ## Natural isomorphisms on `Mat_` -/


-- @@ L38-38 verbatim
namespace Mat_


-- @@ L40-40 verbatim
variable {D : Type u} [Category.{v} D] [Preadditive D]


-- @@ L42-52 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- A natural isomorphism of additive functors extends to their matrix functors. -/
def mapMatNatIso {D' : Type*} [Category.{v} D'] [Preadditive D'] {F G : D ⥤ D'} [F.Additive]
    [G.Additive] (η : F ≅ G) : F.mapMat_ ≅ G.mapMat_ :=
  NatIso.ofComponents (fun M => diagIso (X := fun i => F.obj (M.X i)) (Y := fun i => G.obj (M.X i))
      fun i => η.app (M.X i))
    (fun {M N} f => by
      ext i k
      simp only [diagIso_hom]
      rw [comp_diag_apply, diag_comp_apply]
      exact η.hom.naturality (f i k))


-- @@ L54-54 verbatim
variable [MonoidalCategory D] [MonoidalPreadditive D]


-- @@ L56-83 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- `(X ⊗ Mᵢ)ᵢ ≅ X ⊗ (Mᵢ)ᵢ` in `Mat_ D`. -/
def mapMatTensorLeftIso (X : D) :
    (tensorLeft X).mapMat_ ≅ tensorLeft ((CategoryTheory.Mat_.embedding D).obj X) :=
  NatIso.ofComponents
    (fun M =>
      { hom := permMat (X := fun i => X ⊗ M.X i) (Y := fun x : PUnit × M.ι => X ⊗ M.X x.2)
          (Equiv.punitProd M.ι).symm fun _ => 𝟙 _
        inv := permMat (X := fun x : PUnit × M.ι => X ⊗ M.X x.2) (Y := fun i => X ⊗ M.X i)
          (Equiv.punitProd M.ι) fun _ => 𝟙 _
        hom_inv_id := by
          rw [permMat_comp_permMat]
          exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by simp
        inv_hom_id := by
          rw [permMat_comp_permMat]
          exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by simp })
    (fun {M N} f => by
      refine hom_ext_equiv (Equiv.punitProd N.ι).symm fun i j => ?_
      refine (comp_permMat_apply (X := fun i => X ⊗ N.X i)
        (Y := fun x : PUnit × N.ι => X ⊗ N.X x.2) (Equiv.punitProd N.ι).symm (fun _ => 𝟙 _)
        ((tensorLeft X).mapMat_.map f) i j).trans ?_
      refine Eq.trans ?_ (permMat_comp_apply (X := fun i => X ⊗ M.X i)
        (Y := fun x : PUnit × M.ι => X ⊗ M.X x.2) (Equiv.punitProd M.ι).symm (fun _ => 𝟙 _)
        _ i _).symm
      change (X ◁ f i j) ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 ((CategoryTheory.Mat_.embedding D).obj X) PUnit.unit
        PUnit.unit ⊗ₘ f i j)
      rw [CategoryTheory.Mat_.id_apply_self, id_tensorHom, Category.comp_id, Category.id_comp]
      rfl)


-- @@ L85-112 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- `(Mᵢ ⊗ X)ᵢ ≅ (Mᵢ)ᵢ ⊗ X` in `Mat_ D`. -/
def mapMatTensorRightIso (X : D) :
    (tensorRight X).mapMat_ ≅ tensorRight ((CategoryTheory.Mat_.embedding D).obj X) :=
  NatIso.ofComponents
    (fun M =>
      { hom := permMat (X := fun i => M.X i ⊗ X) (Y := fun x : M.ι × PUnit => M.X x.1 ⊗ X)
          (Equiv.prodPUnit M.ι).symm fun _ => 𝟙 _
        inv := permMat (X := fun x : M.ι × PUnit => M.X x.1 ⊗ X) (Y := fun i => M.X i ⊗ X)
          (Equiv.prodPUnit M.ι) fun _ => 𝟙 _
        hom_inv_id := by
          rw [permMat_comp_permMat]
          exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by simp
        inv_hom_id := by
          rw [permMat_comp_permMat]
          exact permMat_eq_id _ (fun _ => rfl) _ fun _ => by simp })
    (fun {M N} f => by
      refine hom_ext_equiv (Equiv.prodPUnit N.ι).symm fun i j => ?_
      refine (comp_permMat_apply (X := fun i => N.X i ⊗ X)
        (Y := fun x : N.ι × PUnit => N.X x.1 ⊗ X) (Equiv.prodPUnit N.ι).symm (fun _ => 𝟙 _)
        ((tensorRight X).mapMat_.map f) i j).trans ?_
      refine Eq.trans ?_ (permMat_comp_apply (X := fun i => M.X i ⊗ X)
        (Y := fun x : M.ι × PUnit => M.X x.1 ⊗ X) (Equiv.prodPUnit M.ι).symm (fun _ => 𝟙 _)
        _ i _).symm
      change (f i j ▷ X) ≫ 𝟙 _ = 𝟙 _ ≫ (f i j ⊗ₘ
        𝟙 ((CategoryTheory.Mat_.embedding D).obj X) PUnit.unit PUnit.unit)
      rw [CategoryTheory.Mat_.id_apply_self, tensorHom_id, Category.comp_id, Category.id_comp]
      rfl)


-- @@ L114-114 verbatim
end Mat_


-- @@ L116-116 verbatim
/-! ## `Π ≅ π ⊗ - ≅ - ⊗ π` on the underlying category -/


-- @@ L118-118 verbatim
namespace Underlying


-- @@ L120-122 verbatim
variable {R : Type w} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C] [PiSupercategory R C]
  [MonoidalPiSupercategory R C]


-- @@ L124-126 verbatim
variable (R C) in
/-- The object `π` of the underlying category. -/
def piUnit : Underlying R C := ⟨MonoidalPiSupercategory.pi (R := R) (C := C)⟩


-- @@ L128-133 verbatim
theorem ζ_comp_ζL_inv_mem (X : C) :
    ((PiSupercategory.ζ (R := R) X).hom ≫ (MonoidalPiSupercategory.ζL (R := R) X).inv) ∈
      parity (R := R) _ _ 0 := by
  have := comp_mem (PiSupercategory.ζ_hom_mem (R := R) X)
    (inv_mem _ (MonoidalPiSupercategory.ζL_hom_mem (R := R) X))
  simpa using! this


-- @@ L135-140 verbatim
theorem ζ_comp_ζR_inv_mem (X : C) :
    ((PiSupercategory.ζ (R := R) X).hom ≫ (MonoidalPiSupercategory.ζR (R := R) X).inv) ∈
      parity (R := R) _ _ 0 := by
  have := comp_mem (PiSupercategory.ζ_hom_mem (R := R) X)
    (inv_mem _ (MonoidalPiSupercategory.ζR_hom_mem (R := R) X))
  simpa using! this


-- @@ L142-160 verbatim
variable (R C) in
/-- In the underlying category of a supercategory with both a Π-supercategory structure and a
monoidal Π-supercategory structure, `Π ≅ π ⊗ -`, with components `ζL⁻¹ ∘ ζ`. -/
def piIsoTensorLeft : PiCategory.pi (R := R) (C := Underlying R C) ≅ tensorLeft (piUnit R C) :=
  NatIso.ofComponents
    (fun X => isoMk (PiSupercategory.ζ (R := R) X.obj ≪≫
      (MonoidalPiSupercategory.ζL (R := R) X.obj).symm) (ζ_comp_ζL_inv_mem X.obj))
    (fun {X Y} f => Subtype.ext (by
      change (PiSupercategory.pi (R := R)).map f.1 ≫ (PiSupercategory.ζ (R := R) Y.obj).hom ≫
          (MonoidalPiSupercategory.ζL (R := R) Y.obj).inv =
        ((PiSupercategory.ζ (R := R) X.obj).hom ≫ (MonoidalPiSupercategory.ζL (R := R) X.obj).inv) ≫
          MonoidalPiSupercategory.pi (R := R) (C := C) ◁ f.1
      have h1 := PiSupercategory.ζ_naturality_of_mem (R := R) f.2
      have h2 := MonoidalPiSupercategory.ζL_naturality (R := R) f.2
      rw [sign_zero, one_smul] at h1 h2
      rw [← Category.assoc, h1, Category.assoc, Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp, ← Category.assoc, ← h2, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]))


-- @@ L162-179 verbatim
variable (R C) in
/-- `Π ≅ - ⊗ π`, with components `ζR⁻¹ ∘ ζ`. -/
def piIsoTensorRight : PiCategory.pi (R := R) (C := Underlying R C) ≅ tensorRight (piUnit R C) :=
  NatIso.ofComponents
    (fun X => isoMk (PiSupercategory.ζ (R := R) X.obj ≪≫
      (MonoidalPiSupercategory.ζR (R := R) X.obj).symm) (ζ_comp_ζR_inv_mem X.obj))
    (fun {X Y} f => Subtype.ext (by
      change (PiSupercategory.pi (R := R)).map f.1 ≫ (PiSupercategory.ζ (R := R) Y.obj).hom ≫
          (MonoidalPiSupercategory.ζR (R := R) Y.obj).inv =
        ((PiSupercategory.ζ (R := R) X.obj).hom ≫ (MonoidalPiSupercategory.ζR (R := R) X.obj).inv) ≫
          f.1 ▷ MonoidalPiSupercategory.pi (R := R) (C := C)
      have h1 := PiSupercategory.ζ_naturality_of_mem (R := R) f.2
      have h2 := MonoidalPiSupercategory.ζR_naturality (R := R) f.2
      rw [sign_zero, one_smul] at h1 h2
      rw [← Category.assoc, h1, Category.assoc, Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp, ← Category.assoc, ← h2, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]))


-- @@ L181-181 verbatim
end Underlying


-- @@ L183-183 verbatim
/-! ## The super Karoubi envelope of a monoidal supercategory -/


-- @@ L185-185 verbatim
namespace SKar


-- @@ L187-188 verbatim
variable (R : Type w) [CommRing R] (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]


-- @@ L190-190 verbatim
example : MonoidalCategory (SKar R C) := inferInstance

-- @@ L191-191 verbatim
example : MonoidalPreadditive (SKar R C) := inferInstance


-- @@ L193-195 verbatim
/-- The object `π` of `SKar(A)`. -/
def piObj : SKar R C :=
  (toKaroubi _).obj ((CategoryTheory.Mat_.embedding _).obj (Underlying.piUnit R (Envelope R C)))


-- @@ L197-202 verbatim
/-- `Π ≅ π ⊗ -` on the additive envelope. -/
def piMatIsoTensorLeft :
    PiCategory.pi (R := R) (C := Mat_ (Underlying R (Envelope R C))) ≅
      tensorLeft ((CategoryTheory.Mat_.embedding _).obj (Underlying.piUnit R (Envelope R C))) :=
  Mat_.mapMatNatIso (Underlying.piIsoTensorLeft R (Envelope R C)) ≪≫
    Mat_.mapMatTensorLeftIso _


-- @@ L204-209 verbatim
/-- `Π ≅ - ⊗ π` on the additive envelope. -/
def piMatIsoTensorRight :
    PiCategory.pi (R := R) (C := Mat_ (Underlying R (Envelope R C))) ≅
      tensorRight ((CategoryTheory.Mat_.embedding _).obj (Underlying.piUnit R (Envelope R C))) :=
  Mat_.mapMatNatIso (Underlying.piIsoTensorRight R (Envelope R C)) ≪≫
    Mat_.mapMatTensorRightIso _


-- @@ L211-211 verbatim
variable {R C}


-- @@ L213-215 verbatim
/-- **Brundan–Ellis, §1.5.** In `SKar(A)`, `Π V ≅ π ⊗ V`. -/
def piObjIsoTensorLeft (P : SKar R C) : (PiCategory.pi (R := R)).obj P ≅ piObj R C ⊗ P :=
  ((functorExtension₂ _ _).mapIso (piMatIsoTensorLeft R C)).app P


-- @@ L217-219 verbatim
/-- **Brundan–Ellis, §1.5.** In `SKar(A)`, `Π V ≅ V ⊗ π`. -/
def piObjIsoTensorRight (P : SKar R C) : (PiCategory.pi (R := R)).obj P ≅ P ⊗ piObj R C :=
  ((functorExtension₂ _ _).mapIso (piMatIsoTensorRight R C)).app P


-- @@ L221-221 verbatim
/-! ## The `Zπ`-algebra `K₀(SKar(A))` -/


-- @@ L223-225 verbatim
theorem mk_pi_eq_piObj_mul (P : SKar R C) :
    K₀.mk ((PiCategory.pi (R := R)).obj P) = K₀.mk (piObj R C) * K₀.mk P := by
  rw [K₀.mk_mul_mk]; exact K₀.mk_eq_mk_of_iso (piObjIsoTensorLeft P)


-- @@ L227-229 verbatim
theorem mk_pi_eq_mul_piObj (P : SKar R C) :
    K₀.mk ((PiCategory.pi (R := R)).obj P) = K₀.mk P * K₀.mk (piObj R C) := by
  rw [K₀.mk_mul_mk]; exact K₀.mk_eq_mk_of_iso (piObjIsoTensorRight P)


-- @@ L231-237 verbatim
theorem piObj_mul (x : K₀ (SKar R C)) :
    K₀.mk (piObj R C) * x = K₀.piInvolution R (SKar R C) x := by
  induction x using K₀.induction_on with
  | mk P => rw [K₀.piInvolution_mk, mk_pi_eq_piObj_mul]
  | zero => rw [K₀.mul_zero, map_zero]
  | add x y hx hy => rw [K₀.mul_add, hx, hy, map_add]
  | neg x hx => rw [K₀.mul_neg, hx, map_neg]


-- @@ L239-245 verbatim
theorem mul_piObj (x : K₀ (SKar R C)) :
    x * K₀.mk (piObj R C) = K₀.piInvolution R (SKar R C) x := by
  induction x using K₀.induction_on with
  | mk P => rw [K₀.piInvolution_mk, mk_pi_eq_mul_piObj]
  | zero => rw [K₀.zero_mul, map_zero]
  | add x y hx hy => rw [K₀.add_mul, hx, hy, map_add]
  | neg x hx => rw [K₀.neg_mul, hx, map_neg]


-- @@ L247-249 verbatim
/-- `[π]` is central. -/
theorem piObj_commute (x : K₀ (SKar R C)) : Commute (K₀.mk (piObj R C)) x := by
  rw [Commute, SemiconjBy, piObj_mul, mul_piObj]


-- @@ L251-255 verbatim
/-- `[π]² = 1`. -/
theorem piObj_mul_piObj : K₀.mk (piObj R C) * K₀.mk (piObj R C) = 1 := by
  have h : K₀.mk (piObj R C) = K₀.piInvolution R (SKar R C) 1 := by
    rw [← piObj_mul, mul_one]
  rw [piObj_mul, h, K₀.piInvolution_piInvolution]


-- @@ L257-268 verbatim
open Polynomial in
/-- The ring homomorphism `Zπ → K₀(SKar(A))`, `π ↦ [π]`. -/
def toK₀ : Zπ →+* K₀ (SKar R C) :=
  Ideal.Quotient.lift _
    (eval₂RingHom' (Int.castRingHom _) (K₀.mk (piObj R C)) fun n => Int.cast_commute n _)
    (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul]
      convert mul_zero _
      change eval₂ (Int.castRingHom _) (K₀.mk (piObj R C)) (X ^ 2 - 1) = 0
      rw [eval₂_sub, eval₂_X_pow, eval₂_one, sub_eq_zero, pow_two, piObj_mul_piObj])


-- @@ L270-271 verbatim
theorem toK₀_π : toK₀ (R := R) (C := C) Zπ.π = K₀.mk (piObj R C) := by
  simp [toK₀, Zπ.π, Polynomial.eval₂RingHom']


-- @@ L273-289 verbatim
open Polynomial in
theorem toK₀_commute (c : Zπ) (x : K₀ (SKar R C)) : Commute (toK₀ c) x := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective c
  change Commute (eval₂RingHom' (Int.castRingHom _) (K₀.mk (piObj R C))
    (fun n => Int.cast_commute n _) q) x
  induction q using Polynomial.induction_on with
  | C a =>
    rw [eval₂RingHom', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, eval₂_C]
    exact Int.cast_commute a x
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n a _ =>
    rw [map_mul, map_pow]
    refine Commute.mul_left ?_ (Commute.pow_left ?_ _)
    · rw [eval₂RingHom', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, eval₂_C]
      exact Int.cast_commute a x
    · rw [eval₂RingHom', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, eval₂_X]
      exact piObj_commute x


-- @@ L291-294 verbatim
/-- **Brundan–Ellis, §1.5.** For a monoidal supercategory `A`, `K₀(SKar(A))` is a `Zπ`-algebra
with `π ↦ [π]`. -/
instance instAlgebraZπ : Algebra Zπ (K₀ (SKar R C)) :=
  toK₀.toAlgebra' fun c x => (toK₀_commute c x).eq


-- @@ L296-296 verbatim
theorem algebraMap_π : algebraMap Zπ (K₀ (SKar R C)) Zπ.π = K₀.mk (piObj R C) := toK₀_π


-- @@ L298-300 verbatim
/-- The action of `π` in the `Zπ`-algebra structure is the involution `[V] ↦ [Π V]`. -/
theorem π_smul_eq (x : K₀ (SKar R C)) : Zπ.π • x = K₀.piInvolution R (SKar R C) x := by
  rw [Algebra.smul_def, algebraMap_π, piObj_mul]


-- @@ L302-304 verbatim
theorem π_smul_mk_algebra (V : SKar R C) :
    Zπ.π • K₀.mk V = K₀.mk ((PiCategory.pi (R := R)).obj V) := by
  rw [π_smul_eq, K₀.piInvolution_mk]


-- @@ L306-306 verbatim
end SKar


-- @@ L308-308 verbatim
end StringDiagrams
