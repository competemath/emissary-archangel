import OAI.RingTheory.Tachikawa.TwistHom


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace Tachikawa.OuterTensor

-- @@ L8-8 verbatim
open CategoryTheory

-- @@ L9-9 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L10-10 verbatim
universe u

-- @@ L11-11 verbatim
variable {k A B : Type u} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]


-- @@ L13-18 verbatim
lemma map_add_left {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f f' : M ⟶ M') (g : N ⟶ N') : map (k := k) (f+f') g = map f g + map f' g := by
  apply LinearMap.restrictScalars_injective k
  change TensorProduct.map ((f.hom.restrictScalars k)+(f'.hom.restrictScalars k))
    (g.hom.restrictScalars k) = _
  exact TensorProduct.map_add_left _ _ _


-- @@ L20-25 verbatim
lemma map_add_right {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g g' : N ⟶ N') : map (k := k) f (g+g') = map f g + map f g' := by
  apply LinearMap.restrictScalars_injective k
  change TensorProduct.map (f.hom.restrictScalars k)
    ((g.hom.restrictScalars k)+(g'.hom.restrictScalars k)) = _
  exact TensorProduct.map_add_right _ _ _


-- @@ L27-28 verbatim
instance (M : ModuleCat.{u} A) : ((bifunctor k A B).obj M).Additive where
  map_add {_X _Y} g g' := ModuleCat.hom_ext (map_add_right (k := k) (𝟙 M) g g')


-- @@ L30-34 verbatim
instance : (bifunctor k A B).Additive where
  map_add {_X _Y} f f' := by
    apply NatTrans.ext
    funext N
    exact ModuleCat.hom_ext (map_add_left f f' (𝟙 N))


-- @@ L36-36 verbatim
end Tachikawa.OuterTensor




-- @@ L40-40 verbatim
namespace Tachikawa.TotalMap

-- @@ L41-41 verbatim
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂

-- @@ L42-42 verbatim
universe u

-- @@ L43-43 verbatim
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

-- @@ L44-44 verbatim
variable {I₁ I₂ J : Type u} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

-- @@ L45-45 verbatim
variable (F : C ⥤ D) [F.Additive] (K : HomologicalComplex₂ C c₁ c₂)

-- @@ L46-46 verbatim
variable (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]


-- @@ L48-49 verbatim
abbrev map₂ : HomologicalComplex₂ D c₁ c₂ :=
  ((F.mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj K


-- @@ L51-51 verbatim
variable [K.HasTotal c] [(map₂ F K).HasTotal c]


-- @@ L53-55 verbatim
instance sourceHasCoproduct (j : J) : HasCoproduct
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) :=
  (inferInstance : K.HasTotal c) j


-- @@ L57-59 verbatim
instance targetHasCoproduct (j : J) : HasCoproduct
    (fun t => F.obj (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j t)) :=
  (inferInstance : (map₂ F K).HasTotal c) j


-- @@ L61-62 verbatim
abbrev compareX (j : J) : ((map₂ F K).total c).X j ⟶ F.obj ((K.total c).X j) :=
  sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)


-- @@ L64-70 verbatim
@[reassoc (attr := simp)]
lemma ι_compareX (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    (map₂ F K).ιTotal c i₁ i₂ j h ≫ compareX F K c j =
      F.map (K.ιTotal c i₁ i₂ j h) := by
  exact ι_comp_sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) ⟨(i₁,i₂), h⟩


-- @@ L72-78 verbatim
@[reassoc]
lemma ιOrZero_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).ιTotalOrZero c i₁ i₂ j ≫ compareX F K c j =
      F.map (K.ιTotalOrZero c i₁ i₂ j) := by
  by_cases h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j
  · simp only [ιTotalOrZero_eq _ _ _ _ _ h, ι_compareX]
  · simp only [ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp, F.map_zero]


-- @@ L80-87 verbatim
lemma d₁_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).d₁ c i₁ i₂ j ≫ compareX F K c j = F.map (K.d₁ c i₁ i₂ j) := by
  change (ComplexShape.ε₁ c₁ c₂ c (i₁,i₂) •
    (F.map ((K.d i₁ (c₁.next i₁)).f i₂) ≫ (map₂ F K).ιTotalOrZero c _ _ j)) ≫
      compareX F K c j = F.map (ComplexShape.ε₁ c₁ c₂ c (i₁,i₂) •
        ((K.d i₁ (c₁.next i₁)).f i₂ ≫ K.ιTotalOrZero c _ _ j))
  rw [Linear.units_smul_comp, Category.assoc, ιOrZero_compareX,
    F.map_units_smul, F.map_comp]


-- @@ L89-96 verbatim
lemma d₂_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).d₂ c i₁ i₂ j ≫ compareX F K c j = F.map (K.d₂ c i₁ i₂ j) := by
  change (ComplexShape.ε₂ c₁ c₂ c (i₁,i₂) •
    (F.map ((K.X i₁).d i₂ (c₂.next i₂)) ≫ (map₂ F K).ιTotalOrZero c _ _ j)) ≫
      compareX F K c j = F.map (ComplexShape.ε₂ c₁ c₂ c (i₁,i₂) •
        ((K.X i₁).d i₂ (c₂.next i₂) ≫ K.ιTotalOrZero c _ _ j))
  rw [Linear.units_smul_comp, Category.assoc, ιOrZero_compareX,
    F.map_units_smul, F.map_comp]


-- @@ L98-105 verbatim
def comparison : (map₂ F K).total c ⟶ (F.mapHomologicalComplex c).obj (K.total c) where
  f := compareX F K c
  comm' j j' _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ h
    simp only [ι_compareX_assoc, Functor.mapHomologicalComplex_obj_d,
      ← F.map_comp, total_d, Preadditive.comp_add, ι_D₁, ι_D₂, F.map_add,
      Preadditive.add_comp, ι_D₁_assoc, ι_D₂_assoc, d₁_compareX, d₂_compareX]


-- @@ L107-108 verbatim
variable [∀ j, PreservesColimit
  (Discrete.functor (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F]


-- @@ L110-115 verbatim
instance (j : J) : IsIso (compareX F K c j) := by
  have : PreservesColimit (Discrete.functor
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F := inferInstance
  change IsIso (sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j))
  rw [← PreservesCoproduct.inv_hom]
  infer_instance


-- @@ L117-120 verbatim
instance : IsIso (comparison F K c) := by
  have (j : J) : IsIso ((comparison F K c).f j) :=
    inferInstanceAs (IsIso (compareX F K c j))
  exact HomologicalComplex.Hom.isIso_of_components _


-- @@ L122-123 verbatim
def iso : (map₂ F K).total c ≅ (F.mapHomologicalComplex c).obj (K.total c) :=
  asIso (comparison F K c)


-- @@ L125-125 verbatim
end Tachikawa.TotalMap




-- @@ L129-129 verbatim
namespace Tachikawa.OuterTensor

-- @@ L130-130 verbatim
open CategoryTheory HomologicalComplex

-- @@ L131-131 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L132-132 verbatim
universe u

-- @@ L133-133 verbatim
variable (k A B : Type u) [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]


-- @@ L135-135 verbatim
abbrev forgetA := ModuleCat.restrictScalars (algebraMap k A)

-- @@ L136-136 verbatim
abbrev forgetB := ModuleCat.restrictScalars (algebraMap k B)

-- @@ L137-137 verbatim
abbrev forgetE := ModuleCat.restrictScalars (algebraMap k (A ⊗[k] B))

-- @@ L138-138 verbatim
abbrev tensorF := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} k)


-- @@ L140-153 verbatim
def forgetObjIso (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    (forgetE k A B).obj ((bifunctor k A B).obj M |>.obj N) ≅
      ((tensorF k).obj ((forgetA k A).obj M)).obj ((forgetB k B).obj N) :=
  LinearEquiv.toModuleIso
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (algebraMap k (A ⊗[k] B) r) • (show Obj k A B M N from x) = r • (show M ⊗[k] N from x)
        change action k A B M N (algebraMap k (A ⊗[k] B) r) x = r • (show M ⊗[k] N from x)
        rw [AlgHom.commutes]
        rfl }


-- @@ L155-168 verbatim
@[reassoc]
lemma forgetObjIso_natural {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (forgetE k A B).map (ModuleCat.ofHom (map (k := k) f g)) ≫ (forgetObjIso k A B M' N').hom =
      (forgetObjIso k A B M N).hom ≫
        ((tensorF k).map ((forgetA k A).map f)).app ((forgetB k B).obj N) ≫
          ((tensorF k).obj ((forgetA k A).obj M')).map ((forgetB k B).map g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)


-- @@ L170-185 verbatim
@[reassoc]
lemma forgetBifunctor_natural {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (forgetE k A B).map ((bifunctor k A B).map f |>.app N) ≫
      (forgetE k A B).map (((bifunctor k A B).obj M').map g) ≫
      (forgetObjIso k A B M' N').hom =
    (forgetObjIso k A B M N).hom ≫
      ((tensorF k).map ((forgetA k A).map f)).app ((forgetB k B).obj N) ≫
        ((tensorF k).obj ((forgetA k A).obj M')).map ((forgetB k B).map g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)


-- @@ L187-187 verbatim
end Tachikawa.OuterTensor


-- @@ L189-189 verbatim
namespace Tachikawa.OuterTensor

-- @@ L190-190 verbatim
open CategoryTheory HomologicalComplex

-- @@ L191-191 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L192-192 verbatim
universe u

-- @@ L193-193 verbatim
variable (k A B : Type u) [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

-- @@ L194-195 verbatim
variable {I₁ I₂ : Type u} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K : HomologicalComplex (ModuleCat.{u} A) c₁) (L : HomologicalComplex (ModuleCat.{u} B) c₂)


-- @@ L197-197 verbatim
abbrev outerBicomplex := ((bifunctor k A B).mapBifunctorHomologicalComplex c₁ c₂).obj K |>.obj L

-- @@ L198-200 verbatim
abbrev vectorBicomplex := ((tensorF k).mapBifunctorHomologicalComplex c₁ c₂).obj
  (((forgetA k A).mapHomologicalComplex c₁).obj K) |>.obj
    (((forgetB k B).mapHomologicalComplex c₂).obj L)


-- @@ L202-226 verbatim
def forgetBicomplexIso :
    TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L) ≅ vectorBicomplex k A B K L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => forgetObjIso k A B (K.X i) (L.X j)) (by
        intro j j' _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul x y => rfl
        | add x y hx hy =>
          exact (map_add _ x y).trans
            ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))) (by
      intro i i' _
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add x y hx hy =>
        exact (map_add _ x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))


-- @@ L228-233 verbatim
variable {J : Type u} (c : ComplexShape J) [DecidableEq J]
  [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K L (bifunctor k A B) c]
  [HasMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
    (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c]
  [(TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L)).HasTotal c]


-- @@ L235-241 verbatim
def forgetTotalIso :
    ((forgetE k A B).mapHomologicalComplex c).obj
      (mapBifunctor K L (bifunctor k A B) c) ≅
    mapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
      (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c :=
  (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).symm ≪≫
    HomologicalComplex₂.total.mapIso (forgetBicomplexIso k A B K L) c


-- @@ L243-262 verbatim
@[reassoc]
lemma ι_forgetTotalIso (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁,i₂) = j) :
    (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
      (forgetTotalIso k A B K L c).hom.f j =
    (forgetObjIso k A B (K.X i₁) (L.X i₂)).hom ≫
      ιMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
        (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c i₁ i₂ j h := by
  erw [← TotalMap.ι_compareX (forgetE k A B) (outerBicomplex k A B K L) c i₁ i₂ j h]
  change (_ ≫ (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j) ≫
    ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).inv ≫
      (HomologicalComplex₂.total.mapIso (forgetBicomplexIso k A B K L) c).hom).f j = _
  erw [HomologicalComplex.comp_f, Category.assoc, ← Category.assoc
    ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j)
      ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).inv.f j)]
  have hh := HomologicalComplex.congr_hom
    (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom_inv_id j
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hh
  erw [hh, Category.id_comp]
  exact HomologicalComplex₂.ιTotal_map _ _ (forgetBicomplexIso k A B K L).hom c i₁ i₂ j h


-- @@ L264-269 verbatim
variable (K' : HomologicalComplex (ModuleCat.{u} A) c₁)
  (L' : HomologicalComplex (ModuleCat.{u} B) c₂)
  [HasMapBifunctor K' L' (bifunctor k A B) c]
  [HasMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K')
    (((forgetB k B).mapHomologicalComplex c₂).obj L') (tensorF k) c]
  [(TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K' L')).HasTotal c]


-- @@ L271-298 verbatim
@[reassoc]
lemma forgetTotalIso_natural (f : K ⟶ K') (g : L ⟶ L') :
    ((forgetE k A B).mapHomologicalComplex c).map
      (mapBifunctorMap f g (bifunctor k A B) c) ≫ (forgetTotalIso k A B K' L' c).hom =
    (forgetTotalIso k A B K L c).hom ≫
      mapBifunctorMap (((forgetA k A).mapHomologicalComplex c₁).map f)
        (((forgetB k B).mapHomologicalComplex c₂).map g) (tensorF k) c := by
  apply HomologicalComplex.Hom.ext
  funext j
  rw [← cancel_epi ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j)]
  apply HomologicalComplex₂.total.hom_ext
  intro i₁ i₂ h
  have hh : (TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L)).ιTotal c i₁ i₂ j h ≫
      (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j =
      (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) :=
    TotalMap.ι_compareX (forgetE k A B) (outerBicomplex k A B K L) c i₁ i₂ j h
  rw [← Category.assoc, ← Category.assoc, hh]
  change (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
    ((forgetE k A B).map ((mapBifunctorMap f g (bifunctor k A B) c).f j) ≫ _) =
      (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
        ((forgetTotalIso k A B K L c).hom.f j ≫ _)
  rw [← Category.assoc, ← Functor.map_comp, ι_mapBifunctorMap,
    Functor.map_comp, Functor.map_comp]
  rw [Category.assoc, Category.assoc, ι_forgetTotalIso,
    ι_forgetTotalIso_assoc, ι_mapBifunctorMap]
  exact forgetBifunctor_natural_assoc k A B (f.f i₁) (g.f i₂)
    (ιMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K')
      (((forgetB k B).mapHomologicalComplex c₂).obj L') (tensorF k) c i₁ i₂ j h)


-- @@ L300-300 verbatim
end Tachikawa.OuterTensor




-- @@ L304-304 verbatim
namespace Tachikawa.AlgebraInduction

-- @@ L305-305 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L306-307 verbatim
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)


-- @@ L309-312 verbatim
lemma res_map_exact (T : ShortComplex (ModuleCat.{0} S)) (h : T.Exact) :
    (T.map (res φ)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h


-- @@ L314-316 verbatim
instance : PreservesFiniteLimits (res φ) := by
  have h := ((Functor.exact_tfae (res φ)).out 2 4).mp (res_map_exact φ)
  exact h.1

-- @@ L317-319 verbatim
instance : PreservesFiniteColimits (res φ) := by
  have h := ((Functor.exact_tfae (res φ)).out 2 4).mp (res_map_exact φ)
  exact h.2


-- @@ L321-321 verbatim
end Tachikawa.AlgebraInduction




-- @@ L325-325 verbatim
namespace Tachikawa.OuterTensor

-- @@ L326-326 verbatim
open CategoryTheory

-- @@ L327-327 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L328-328 verbatim
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]


-- @@ L330-330 verbatim
def freeObj (m : ℕ) : ModuleCat A := ModuleCat.of A (Fin m → A)


-- @@ L332-341 verbatim
def underlyingFree (m : ℕ) : (freeObj A m) ≃ₗ[k] (Fin m → A) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    ext i
    change (algebraMap k A r) * x i = r • x i
    exact (Algebra.smul_def r (x i)).symm


-- @@ L343-348 verbatim
def freeEquivLinear (m n : ℕ) :
    ((freeObj A m) ⊗[k] (freeObj B n)) ≃ₗ[k]
      (Fin m → Fin n → A ⊗[k] B) :=
  (TensorProduct.congr (underlyingFree k A m) (underlyingFree k B n)).trans
    ((TensorProduct.piLeft k (Fin n → B) (fun _ : Fin m => A)).trans
      (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight k k A (fun _ : Fin n => B)))


-- @@ L350-352 verbatim
lemma freeEquivLinear_tmul (m n : ℕ) (x : freeObj A m)
    (y : freeObj B n) :
    freeEquivLinear k A B m n (x ⊗ₜ[k] y) = fun i j => x i ⊗ₜ[k] y j := rfl


-- @@ L354-367 verbatim
lemma freeEquivLinear_action (m n : ℕ) (r : A ⊗[k] B) :
    (freeEquivLinear k A B m n).toLinearMap.comp
      (action k A B (freeObj A m) (freeObj B n) r) =
      (Algebra.lsmul k k (Fin m → Fin n → A ⊗[k] B) r).comp
      (freeEquivLinear k A B m n).toLinearMap := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    ext i j
    change (a * x i) ⊗ₜ[k] (b * y j) = (a ⊗ₜ[k] b) * (x i ⊗ₜ[k] y j)
    exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm
  | add r s hr hs =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hr, hs]


-- @@ L369-373 verbatim
def freeEquiv (m n : ℕ) :
    Obj k A B (freeObj A m) (freeObj B n) ≃ₗ[A ⊗[k] B]
      (Fin m → Fin n → A ⊗[k] B) where
  __ := (freeEquivLinear k A B m n).toAddEquiv
  map_smul' r z := LinearMap.congr_fun (freeEquivLinear_action k A B m n r) z


-- @@ L375-378 verbatim
instance freeProjective (m n : ℕ) :
    Module.Projective (A ⊗[k] B)
      (Obj k A B (freeObj A m) (freeObj B n)) :=
  Module.Projective.of_equiv' (freeEquiv k A B m n).symm


-- @@ L380-396 verbatim
lemma projective (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N] :
    Module.Projective (A ⊗[k] B) (Obj k A B M N) := by
  let c := finiteFreeCover (R := A) (M := M)
  let d := finiteFreeCover (R := B) (M := N)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  obtain ⟨j,hj⟩ := Module.projective_lifting_property d.map LinearMap.id d.surjective
  have : Module.Projective (A ⊗[k] B)
      (Obj k A B (ModuleCat.of A (Fin c.rank → A))
        (ModuleCat.of B (Fin d.rank → B))) := freeProjective k A B c.rank d.rank
  apply Module.Projective.of_split
    (map (k := k) (ModuleCat.ofHom i) (ModuleCat.ofHom j))
    (map (k := k) (ModuleCat.ofHom c.map) (ModuleCat.ofHom d.map))
  rw [map_comp]
  have hi' : ModuleCat.ofHom i ≫ ModuleCat.ofHom c.map = 𝟙 M := ModuleCat.hom_ext hi
  have hj' : ModuleCat.ofHom j ≫ ModuleCat.ofHom d.map = 𝟙 N := ModuleCat.hom_ext hj
  rw [hi',hj',map_id]


-- @@ L398-398 verbatim
end Tachikawa.OuterTensor




-- @@ L402-402 verbatim
namespace Tachikawa.OuterTensor

-- @@ L403-403 verbatim
open CategoryTheory

-- @@ L404-404 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L405-406 verbatim
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M U : ModuleCat A} {N V : ModuleCat B}


-- @@ L408-410 verbatim
def morphism (f : M ⟶ U) (g : N ⟶ V) :
    (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  ModuleCat.ofHom (map (k := k) f g)


-- @@ L412-428 verbatim
lemma map_smul_left (r : k) (f : M ⟶ U) (g : N ⟶ V) :
    morphism (k := k) (r • f) g = r • morphism (k := k) f g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change map (k := k) _ _ z = (algebraMap k (A ⊗[k] B) r) • (map (k := k) f g z)
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change (r • f x) ⊗ₜ[k] g y = (algebraMap k (A ⊗[k] B) r) • (show Obj k A B U V from f x ⊗ₜ[k] g y)
    change (r • f x) ⊗ₜ[k] g y = action k A B U V (algebraMap k (A ⊗[k] B) r) _
    rw [AlgHom.commutes]
    exact TensorProduct.smul_tmul' _ _ _
  | add z z' hz hz' =>
    exact ((map (k := k) _ _).map_add z z').trans
      ((congrArg₂ (· + ·) hz hz').trans ((smul_add _ _ _).symm.trans
      (congrArg (fun w : Obj k A B U V => (algebraMap k (A ⊗[k] B) r) • w)
        ((map (k := k) f g).map_add z z').symm)))


-- @@ L430-446 verbatim
lemma map_smul_right (r : k) (f : M ⟶ U) (g : N ⟶ V) :
    morphism (k := k) f (r • g) = r • morphism (k := k) f g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change map (k := k) _ _ z = (algebraMap k (A ⊗[k] B) r) • (map (k := k) f g z)
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change f x ⊗ₜ[k] (r • g y) = (algebraMap k (A ⊗[k] B) r) • (show Obj k A B U V from f x ⊗ₜ[k] g y)
    change f x ⊗ₜ[k] (r • g y) = action k A B U V (algebraMap k (A ⊗[k] B) r) _
    rw [AlgHom.commutes]
    exact TensorProduct.tmul_smul _ _ _
  | add z z' hz hz' =>
    exact ((map (k := k) _ _).map_add z z').trans
      ((congrArg₂ (· + ·) hz hz').trans ((smul_add _ _ _).symm.trans
      (congrArg (fun w : Obj k A B U V => (algebraMap k (A ⊗[k] B) r) • w)
        ((map (k := k) f g).map_add z z').symm)))


-- @@ L448-456 verbatim
def homMap : (M ⟶ U) ⊗[k] (N ⟶ V) →ₗ[k]
    (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun g => morphism (k := k) f g
          map_add' := fun g g' => ModuleCat.hom_ext (map_add_right f g g')
          map_smul' := fun r g => map_smul_right r f g }
      map_add' := fun f f' => LinearMap.ext fun g => ModuleCat.hom_ext (map_add_left f f' g)
      map_smul' := fun r f => LinearMap.ext fun g => map_smul_left r f g }


-- @@ L458-459 verbatim
@[simp] lemma homMap_tmul (f : M ⟶ U) (g : N ⟶ V) :
    homMap (f ⊗ₜ[k] g) = morphism (k := k) f g := rfl


-- @@ L461-464 verbatim
def restrictHom : (M ⟶ U) →ₗ[k] (M →ₗ[k] U) where
  toFun f := f.hom.restrictScalars k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L466-468 verbatim
lemma restrictHom_injective : Function.Injective (restrictHom (k := k) (M := M) (U := U)) := by
  intro f g h
  exact ModuleCat.hom_ext (LinearMap.restrictScalars_injective k h)


-- @@ L470-479 verbatim
def underlyingHom (f : ((bifunctor k A B).obj M |>.obj N) ⟶
    ((bifunctor k A B).obj U |>.obj V)) : M ⊗[k] N →ₗ[k] U ⊗[k] V where
  toFun := f.hom
  map_add' := f.hom.map_add
  map_smul' r z := by
    have h := f.hom.map_smul (algebraMap k (A ⊗[k] B) r) z
    change f.hom (action k A B M N (algebraMap k (A ⊗[k] B) r) z) =
      action k A B U V (algebraMap k (A ⊗[k] B) r) (f.hom z) at h
    rw [AlgHom.commutes, AlgHom.commutes] at h
    exact h


-- @@ L481-490 verbatim
lemma homMap_underlying (z : (M ⟶ U) ⊗[k] (N ⟶ V)) :
    underlyingHom (homMap z) =
      TensorProduct.homTensorHomMap (RingHom.id k) M N U V
        (TensorProduct.map (restrictHom (k := k)) (restrictHom (k := k)) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul f g => rfl
  | add z z' hz hz' =>
    rw [map_add]
    change underlyingHom (homMap z) + underlyingHom (homMap z') = _
    simp only [map_add, hz, hz']


-- @@ L492-500 verbatim
lemma homMap_injective [FiniteDimensional k M] [FiniteDimensional k N] :
    Function.Injective (homMap (k := k) (M := M) (N := N) (U := U) (V := V)) := by
  intro x y h
  have h' := congrArg underlyingHom h
  rw [homMap_underlying, homMap_underlying,
    ← homTensorHomEquiv_apply, ← homTensorHomEquiv_apply] at h'
  have h'' := (homTensorHomEquiv k M N U V).injective h'
  exact TensorProduct.map_injective_of_flat_flat _ _ (restrictHom_injective (k := k))
    (restrictHom_injective (k := k)) h''


-- @@ L502-502 verbatim
end Tachikawa.OuterTensor




-- @@ L506-506 verbatim
namespace Tachikawa.AlgebraInduction

-- @@ L507-507 verbatim
open CategoryTheory

-- @@ L508-508 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L509-509 verbatim
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]


-- @@ L511-519 verbatim
def unitLinear (φ : R →ₐ[k] S) (M : ModuleCat R) : M →ₗ[k] (functor φ).obj M where
  toFun := unit φ M
  map_add' := (unit φ M).hom.map_add
  map_smul' c x := by
    have h := (unit φ M).hom.map_smul (algebraMap k R c) x
    change (show (functor φ).obj M from unit φ M ((algebraMap k R c) • x)) =
      φ (algebraMap k R c) • (show (functor φ).obj M from unit φ M x) at h
    rw [IsScalarTower.algebraMap_smul, φ.commutes, IsScalarTower.algebraMap_smul] at h
    exact h


-- @@ L521-522 verbatim
lemma unitLinear_smul (φ : R →ₐ[k] S) (M : ModuleCat R) (r : R) (m : M) :
    unitLinear φ M (r • m) = φ r • unitLinear φ M m := (unit φ M).hom.map_smul r m


-- @@ L524-524 verbatim
end Tachikawa.AlgebraInduction


-- @@ L526-526 verbatim
namespace Tachikawa.OuterTensor

-- @@ L527-527 verbatim
open CategoryTheory

-- @@ L528-528 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L529-531 verbatim
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)


-- @@ L533-534 verbatim
abbrev inductionTarget := (bifunctor k S T).obj ((AlgebraInduction.functor φ).obj M) |>.obj
  ((AlgebraInduction.functor ψ).obj N)


-- @@ L536-559 verbatim
def inductionUnit : ((bifunctor k A B).obj M).obj N ⟶
    (AlgebraInduction.res (Algebra.TensorProduct.map φ ψ)).obj (inductionTarget φ ψ M N) :=
  ModuleCat.ofHom
    (X := ((bifunctor k A B).obj M).obj N)
    (Y := (AlgebraInduction.res (Algebra.TensorProduct.map φ ψ)).obj (inductionTarget φ ψ M N))
    { toFun := TensorProduct.map (AlgebraInduction.unitLinear φ M) (AlgebraInduction.unitLinear ψ N)
      map_add' := map_add _
      map_smul' := by
        intro r z
        induction r using TensorProduct.inductionOn with
        | add a b ha hb =>
          erw [add_smul, map_add, ha, hb, RingHom.id_apply, add_smul]
          rfl
        | tmul a b =>
          induction z using TensorProduct.inductionOn with
          | add x y hx hy =>
            erw [smul_add, map_add, hx, hy, map_add, smul_add]
            rfl
          | tmul x y =>
            change AlgebraInduction.unitLinear φ M (a • x) ⊗ₜ[k]
                AlgebraInduction.unitLinear ψ N (b • y) =
              (φ a • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
                (ψ b • AlgebraInduction.unitLinear ψ N y)
            rw [AlgebraInduction.unitLinear_smul, AlgebraInduction.unitLinear_smul] }


-- @@ L561-564 verbatim
def inductionComparison :
    (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).obj
      (((bifunctor k A B).obj M).obj N) ⟶ inductionTarget φ ψ M N :=
  AlgebraInduction.extend (Algebra.TensorProduct.map φ ψ) (inductionUnit φ ψ M N)


-- @@ L566-572 verbatim
@[simp] lemma inductionComparison_pure (s : S) (t : T) (x : M) (y : N) :
    inductionComparison φ ψ M N
      (BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
        (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from s ⊗ₜ[k] t)
        (show Obj k A B M N from x ⊗ₜ[k] y)) =
      (s • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
        (t • AlgebraInduction.unitLinear ψ N y) := rfl


-- @@ L574-605 verbatim
lemma inductionComparison_surjective : Function.Surjective (inductionComparison φ ψ M N) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    obtain ⟨a,ha⟩ := hz
    obtain ⟨b,hb⟩ := hw
    exact ⟨a+b, by erw [map_add,ha,hb]; rfl⟩
  | tmul u v =>
    refine BalancedTensor.induction_on (k := k) (R := A) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := M) u ?_ ?_ ?_
    · exact ⟨0, by erw [map_zero, TensorProduct.zero_tmul]; rfl⟩
    · intro s x
      refine BalancedTensor.induction_on (k := k) (R := B) (S := T)
        (M := AlgebraInduction.Bimod ψ) (N := N) v ?_ ?_ ?_
      · exact ⟨0, by erw [map_zero, TensorProduct.tmul_zero]; rfl⟩
      · intro t y
        refine ⟨BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
          (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
            (show S from s) ⊗ₜ[k] (show T from t))
          (show Obj k A B M N from x ⊗ₜ[k] y), ?_⟩
        rw [inductionComparison_pure]
        congr 1
        · exact (AlgebraInduction.mk_one_smul φ M (show S from s) x).symm
        · exact (AlgebraInduction.mk_one_smul ψ N (show T from t) y).symm
      · intro v w hv hw
        obtain ⟨a,ha⟩ := hv
        obtain ⟨b,hb⟩ := hw
        exact ⟨a+b, by erw [map_add,ha,hb,TensorProduct.tmul_add]; rfl⟩
    · intro u w hu hw
      obtain ⟨a,ha⟩ := hu
      obtain ⟨b,hb⟩ := hw
      exact ⟨a+b, by erw [map_add,ha,hb,TensorProduct.add_tmul]; rfl⟩


-- @@ L607-634 verbatim
@[reassoc] lemma inductionComparison_natural {M' : ModuleCat A} {N' : ModuleCat B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).map (ModuleCat.ofHom (map f g)) ≫
        inductionComparison φ ψ M' N' =
      inductionComparison φ ψ M N ≫ ModuleCat.ofHom
        (map ((AlgebraInduction.functor φ).map f) ((AlgebraInduction.functor ψ).map g)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
  intro s z
  change (show S ⊗[k] T from s) •
      (show inductionTarget φ ψ M' N' from inductionUnit φ ψ M' N' (map f g z)) =
    (map ((AlgebraInduction.functor φ).map f) ((AlgebraInduction.functor ψ).map g))
      ((show S ⊗[k] T from s) • (show inductionTarget φ ψ M N from inductionUnit φ ψ M N z))
  erw [map_smul]
  congr 1
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((congrArg (inductionUnit φ ψ M' N') (map_add (map f g) x y)).trans
      (map_add (inductionUnit φ ψ M' N').hom _ _)).trans
        ((congrArg₂ (· + ·) hx hy).trans
          ((map_add (map ((AlgebraInduction.functor φ).map f)
            ((AlgebraInduction.functor ψ).map g)) _ _).symm.trans
              (congrArg (map ((AlgebraInduction.functor φ).map f)
                ((AlgebraInduction.functor ψ).map g))
                  (map_add (inductionUnit φ ψ M N).hom x y).symm)))
  | tmul x y => rfl


-- @@ L636-636 verbatim
end Tachikawa.OuterTensor




-- @@ L640-640 verbatim
namespace Tachikawa.BalancedTensor

-- @@ L641-645 verbatim
variable {k R S M N P : Type*} [Field k] [Ring R] [Ring S] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module R N]
  [AddCommGroup P] [Module k P]


-- @@ L647-650 verbatim
def liftGround (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n)) :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[k] P :=
  (lift (S := k) f hf).comp restrictEquiv.toLinearMap


-- @@ L652-655 verbatim
@[simp] lemma liftGround_mk (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (m : M) (n : N) :
    liftGround (S := S) f hf (mk (k := k) (R := R) (S := S) m n) = f m n := rfl


-- @@ L657-666 verbatim
omit [SMulCommClass S Rᵐᵒᵖ M] in
@[ext] theorem hom_ext_ground
    {f g : T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[k] P}
    (h : ∀ m n, f (mk m n) = g (mk m n)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | h0 => simp only [map_zero]
  | ht m n => exact h m n
  | ha x y hx hy => simp only [map_add, hx, hy]


-- @@ L668-675 verbatim
lemma liftGround_add (f g : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (hg : ∀ (r : R) (m : M) (n : N), g (MulOpposite.op r • m) n = g m (r • n))
    (hfg : ∀ (r : R) (m : M) (n : N), (f+g) (MulOpposite.op r • m) n = (f+g) m (r • n)) :
    liftGround (S := S) (f+g) hfg = liftGround f hf + liftGround g hg := by
  apply hom_ext_ground
  intro m n
  rfl


-- @@ L677-683 verbatim
lemma liftGround_smul (c : k) (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (hcf : ∀ (r : R) (m : M) (n : N), (c • f) (MulOpposite.op r • m) n = (c • f) m (r • n)) :
    liftGround (S := S) (c • f) hcf = c • liftGround f hf := by
  apply hom_ext_ground
  intro m n
  rfl


-- @@ L685-685 verbatim
end Tachikawa.BalancedTensor




-- @@ L689-689 verbatim
namespace Tachikawa.OuterTensor

-- @@ L690-690 verbatim
open CategoryTheory

-- @@ L691-691 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L692-694 verbatim
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)


-- @@ L696-697 verbatim
abbrev inductionSource := (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).obj
  (((bifunctor k A B).obj M).obj N)


-- @@ L699-707 verbatim
def underlyingEquiv (M : ModuleCat A) (N : ModuleCat B) :
    (((bifunctor k A B).obj M).obj N) ≃ₗ[k] (M ⊗[k] N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := IsScalarTower.algebraMap_smul (A ⊗[k] B) c
    (show Obj k A B M N from x)


-- @@ L709-715 verbatim
def inductionSourceMk : (S ⊗[k] T) →ₗ[k] (M ⊗[k] N) →ₗ[k] inductionSource φ ψ M N :=
  (((BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
      (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
      (N := ((bifunctor k A B).obj M).obj N)).restrictScalars k).compl₂
        (underlyingEquiv M N).symm.toLinearMap).compr₂
          (AlgebraInduction.underlyingEquiv (Algebra.TensorProduct.map φ ψ)
            (((bifunctor k A B).obj M).obj N)).symm.toLinearMap


-- @@ L717-762 verbatim
def inductionPure : AlgebraInduction.Bimod φ →ₗ[k] M →ₗ[k]
    AlgebraInduction.Bimod ψ →ₗ[k] N →ₗ[k] inductionSource φ ψ M N where
  toFun s :=
    { toFun := fun x =>
        { toFun := fun t =>
            { toFun := fun y => inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
              map_add' := by
                intro y z
                simp only [TensorProduct.tmul_add, map_add]
              map_smul' := by
                intro c y
                simp only [TensorProduct.tmul_smul, map_smul]
                rfl }
          map_add' := by
            intro t u
            ext y
            change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] ((show T from t)+(show T from u))) (x ⊗ₜ[k] y) = _
            erw [TensorProduct.tmul_add, map_add, LinearMap.add_apply]
          map_smul' := by
            intro c t
            ext y
            change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (c • (show T from t))) (x ⊗ₜ[k] y) = _
            erw [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply] }
      map_add' := by
        intro x z
        ext t y
        change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) ((x+z) ⊗ₜ[k] y) = _
        simp only [TensorProduct.add_tmul, map_add]
        rfl
      map_smul' := by
        intro c x
        ext t y
        change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) ((c • x) ⊗ₜ[k] y) = _
        simp only [← TensorProduct.smul_tmul', map_smul]
        rfl }
  map_add' s u := by
    refine LinearMap.ext fun x => LinearMap.ext fun t => LinearMap.ext fun y => ?_
    change inductionSourceMk φ ψ M N (((show S from s)+(show S from u)) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) =
      inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) +
        inductionSourceMk φ ψ M N ((show S from u) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
    rw [TensorProduct.add_tmul, map_add, LinearMap.add_apply]
  map_smul' c s := by
    refine LinearMap.ext fun x => LinearMap.ext fun t => LinearMap.ext fun y => ?_
    change inductionSourceMk φ ψ M N ((c • (show S from s)) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) =
      c • inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
    rw [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply]


-- @@ L764-781 verbatim
lemma inductionPure_balance_left (a : A) (s : AlgebraInduction.Bimod φ) (x : M) :
    inductionPure φ ψ M N (MulOpposite.op a • s) x = inductionPure φ ψ M N s (a • x) := by
  ext t y
  have h := BalancedTensor.balance (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
    (a ⊗ₜ[k] (1 : B)) ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
  have h₁ : MulOpposite.op (a ⊗ₜ[k] (1 : B)) •
      (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
        ((show S from s) ⊗ₜ[k] (show T from t))) = ((show S from s) * φ a) ⊗ₜ[k] (show T from t) := by
    change ((show S from s) ⊗ₜ[k] (show T from t)) * (φ a ⊗ₜ[k] ψ 1) = _
    erw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h₂ : (a ⊗ₜ[k] (1 : B)) •
      (show ((bifunctor k A B).obj M).obj N from x ⊗ₜ[k] y) = (a • x) ⊗ₜ[k] y := by
    change (a • x) ⊗ₜ[k] ((1 : B) • y) = _
    rw [one_smul]
  rw [h₁, h₂] at h
  exact h


-- @@ L783-801 verbatim
lemma inductionPure_balance_right (b : B) (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionPure φ ψ M N s x (MulOpposite.op b • t) y =
      inductionPure φ ψ M N s x t (b • y) := by
  have h := BalancedTensor.balance (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
    ((1 : A) ⊗ₜ[k] b) ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
  have h₁ : MulOpposite.op ((1 : A) ⊗ₜ[k] b) •
      (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
        ((show S from s) ⊗ₜ[k] (show T from t))) = (show S from s) ⊗ₜ[k] ((show T from t) * ψ b) := by
    change ((show S from s) ⊗ₜ[k] (show T from t)) * (φ 1 ⊗ₜ[k] ψ b) = _
    erw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h₂ : ((1 : A) ⊗ₜ[k] b) •
      (show ((bifunctor k A B).obj M).obj N from x ⊗ₜ[k] y) = x ⊗ₜ[k] (b • y) := by
    change ((1 : A) • x) ⊗ₜ[k] (b • y) = _
    rw [one_smul]
  rw [h₁, h₂] at h
  exact h


-- @@ L803-806 verbatim
def inductionLeftLift : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M) →ₗ[k]
    AlgebraInduction.Bimod ψ →ₗ[k] N →ₗ[k] inductionSource φ ψ M N :=
  (BalancedTensor.liftGround (S := S) (inductionPure φ ψ M N)
    (inductionPure_balance_left φ ψ M N))


-- @@ L808-811 verbatim
@[simp] lemma inductionLeftLift_mk (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionLeftLift φ ψ M N (BalancedTensor.mk (k := k) (R := A) (S := S) s x) t y =
      inductionPure φ ψ M N s x t y := rfl


-- @@ L813-820 verbatim
lemma inductionLeftLift_balance (z : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M)) (b : B)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionLeftLift φ ψ M N z (MulOpposite.op b • t) y =
      inductionLeftLift φ ψ M N z t (b • y) := by
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ha z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw]
  | ht s x => exact inductionPure_balance_right φ ψ M N b s x t y


-- @@ L822-827 verbatim
def inductionRightLift
    (z : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M)) :
    BalancedTensor.T (k := k) (R := B) (S := T) (M := AlgebraInduction.Bimod ψ) (N := N) →ₗ[k]
      inductionSource φ ψ M N :=
  BalancedTensor.liftGround (S := T) (inductionLeftLift φ ψ M N z)
    (inductionLeftLift_balance φ ψ M N z)


-- @@ L829-835 verbatim
lemma inductionRightLift_add (z w : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M)) :
    inductionRightLift φ ψ M N (z+w) =
      inductionRightLift φ ψ M N z + inductionRightLift φ ψ M N w := by
  unfold inductionRightLift
  simp only [map_add]
  apply BalancedTensor.liftGround_add


-- @@ L837-842 verbatim
lemma inductionRightLift_smul (c : k) (z : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M)) :
    inductionRightLift φ ψ M N (c • z) = c • inductionRightLift φ ψ M N z := by
  unfold inductionRightLift
  simp only [map_smul]
  apply BalancedTensor.liftGround_smul


-- @@ L844-850 verbatim
def inductionInverseBilinear : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M) →ₗ[k]
    BalancedTensor.T (k := k) (R := B) (S := T) (M := AlgebraInduction.Bimod ψ) (N := N) →ₗ[k]
      inductionSource φ ψ M N where
  toFun := inductionRightLift φ ψ M N
  map_add' := inductionRightLift_add φ ψ M N
  map_smul' := inductionRightLift_smul φ ψ M N


-- @@ L852-857 verbatim
def inductionInverseLinear : inductionTarget φ ψ M N →ₗ[k] inductionSource φ ψ M N :=
  (TensorProduct.lift (inductionInverseBilinear φ ψ M N)).comp
    ((TensorProduct.map (AlgebraInduction.underlyingEquiv φ M).toLinearMap
      (AlgebraInduction.underlyingEquiv ψ N).toLinearMap).comp
        (underlyingEquiv ((AlgebraInduction.functor φ).obj M)
          ((AlgebraInduction.functor ψ).obj N)).toLinearMap)


-- @@ L859-864 verbatim
@[simp] lemma inductionInverseLinear_pure (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionInverseLinear φ ψ M N
      (BalancedTensor.mk (k := k) (R := A) (S := S) s x ⊗ₜ[k]
        BalancedTensor.mk (k := k) (R := B) (S := T) t y) =
      inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y) := rfl


-- @@ L866-883 verbatim
lemma inductionInverse_comparison_pure (s : S) (t : T) (x : M) (y : N) :
    inductionInverseLinear φ ψ M N
      (inductionComparison φ ψ M N (inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y))) =
      inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y) := by
  change inductionInverseLinear φ ψ M N
    ((s • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
      (t • AlgebraInduction.unitLinear ψ N y)) = _
  have hs : (s • AlgebraInduction.unitLinear φ M x : (AlgebraInduction.functor φ).obj M) =
      BalancedTensor.mk (k := k) (R := A) (S := S) (show AlgebraInduction.Bimod φ from s) x :=
    (AlgebraInduction.mk_one_smul φ M s x).symm
  have ht : (t • AlgebraInduction.unitLinear ψ N y : (AlgebraInduction.functor ψ).obj N) =
      BalancedTensor.mk (k := k) (R := B) (S := T) (show AlgebraInduction.Bimod ψ from t) y :=
    (AlgebraInduction.mk_one_smul ψ N t y).symm
  exact (congrArg (inductionInverseLinear φ ψ M N)
    (congrArg₂ (fun (u : (AlgebraInduction.functor φ).obj M)
      (v : (AlgebraInduction.functor ψ).obj N) =>
        (show inductionTarget φ ψ M N from u ⊗ₜ[k] v)) hs ht)).trans
      (inductionInverseLinear_pure φ ψ M N s x t y)


-- @@ L885-915 verbatim
lemma inductionInverse_comparison :
    (inductionInverseLinear φ ψ M N).comp
      ((inductionComparison φ ψ M N).hom.restrictScalars k) = LinearMap.id := by
  let e := AlgebraInduction.underlyingEquiv (Algebra.TensorProduct.map φ ψ)
    (((bifunctor k A B).obj M).obj N)
  let f := ((inductionInverseLinear φ ψ M N).comp
      ((inductionComparison φ ψ M N).hom.restrictScalars k)).comp e.symm.toLinearMap
  have hfg : f = e.symm.toLinearMap := by
    apply BalancedTensor.hom_ext_ground
    intro s z
    change (f.comp ((BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
      (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
      (N := ((bifunctor k A B).obj M).obj N)) s)) z = _
    let F : (S ⊗[k] T) →ₗ[k] (M ⊗[k] N) →ₗ[k] inductionSource φ ψ M N :=
      (inductionSourceMk φ ψ M N).compr₂
        ((inductionInverseLinear φ ψ M N).comp
          ((inductionComparison φ ψ M N).hom.restrictScalars k))
    have hF : F = inductionSourceMk φ ψ M N := by
      apply LinearMap.ext
      intro st
      induction st using TensorProduct.inductionOn with
      | add st uv hst huv => simp only [map_add, hst, huv]
      | tmul s t =>
        apply TensorProduct.ext'
        intro x y
        exact inductionInverse_comparison_pure φ ψ M N s t x y
    exact LinearMap.congr_fun (LinearMap.congr_fun hF (show S ⊗[k] T from s))
      (show M ⊗[k] N from z)
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun hfg (e z)


-- @@ L917-921 verbatim
lemma inductionComparison_injective : Function.Injective (inductionComparison φ ψ M N) := by
  apply Function.LeftInverse.injective (f := inductionComparison φ ψ M N)
    (g := inductionInverseLinear φ ψ M N)
  intro z
  exact LinearMap.congr_fun (inductionInverse_comparison φ ψ M N) z


-- @@ L923-925 verbatim
def inductionIso : inductionSource φ ψ M N ≅ inductionTarget φ ψ M N :=
  (LinearEquiv.ofBijective (inductionComparison φ ψ M N).hom
    ⟨inductionComparison_injective φ ψ M N, inductionComparison_surjective φ ψ M N⟩).toModuleIso


-- @@ L927-927 verbatim
@[simp] lemma inductionIso_hom : (inductionIso φ ψ M N).hom = inductionComparison φ ψ M N := rfl


-- @@ L929-929 verbatim
end Tachikawa.OuterTensor




-- @@ L933-933 verbatim
namespace Tachikawa.OuterTensor

-- @@ L934-934 verbatim
open CategoryTheory

-- @@ L935-935 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L936-937 verbatim
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)


-- @@ L939-940 verbatim
abbrev algebraTwist {R : Type} [Ring R] [Algebra k R] (ρ : R ≃ₐ[k] R) :=
  AlgebraInduction.res ρ.symm.toAlgHom


-- @@ L942-952 verbatim
def restrictionGround {R : Type} [Ring R] [Algebra k R] (ρ : R ≃ₐ[k] R)
    (M : ModuleCat R) : (algebraTwist ρ).obj M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change ρ.symm (algebraMap k R c) • (show M from x) = c • (show M from x)
    rw [ρ.symm.commutes]
    rfl


-- @@ L954-979 verbatim
def twistObjIso (M : ModuleCat A) (N : ModuleCat B) :
    ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N) ≅
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) := by
  let eq := TensorProduct.congr (restrictionGround σ M) (restrictionGround τ N)
  let e : Obj k A B ((algebraTwist σ).obj M) ((algebraTwist τ).obj N) ≃ₗ[k]
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) :=
    eq.trans ((underlyingEquiv M N).symm.trans
      (restrictionGround (Algebra.TensorProduct.congr σ τ) (((bifunctor k A B).obj M).obj N)).symm)
  let f : ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N) ⟶
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) :=
    ModuleCat.ofHom (X := ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N))
      (Y := (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N))
    { toFun := e
      map_add' := e.map_add
      map_smul' a z := by
        induction a using TensorProduct.inductionOn with
        | tmul a b =>
          induction z using TensorProduct.inductionOn with
          | tmul x y => rfl
          | add x y hx hy =>
            erw [smul_add, map_add, hx, hy, map_add, smul_add]
            rfl
        | add a b ha hb =>
          erw [add_smul, map_add, ha, hb, RingHom.id_apply, add_smul]
          rfl }
  exact (LinearEquiv.ofBijective f.hom e.bijective).toModuleIso


-- @@ L981-992 verbatim
@[reassoc]
lemma twistObjIso_natural {M M' : ModuleCat A} {N N' : ModuleCat B}
    (f : M ⟶ M') (g : N ⟶ N') :
    morphism ((algebraTwist σ).map f) ((algebraTwist τ).map g) ≫ (twistObjIso σ τ M' N').hom =
      (twistObjIso σ τ M N).hom ≫ (algebraTwist (Algebra.TensorProduct.congr σ τ)).map (morphism f g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)


-- @@ L994-994 verbatim
end Tachikawa.OuterTensor




-- @@ L998-998 verbatim
namespace Tachikawa.OuterTensor

-- @@ L999-999 verbatim
open CategoryTheory HomologicalComplex

-- @@ L1000-1000 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L1001-1002 verbatim
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)

-- @@ L1003-1004 verbatim
variable {I₁ I₂ : Type} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (P : HomologicalComplex (ModuleCat A) c₁) (Q : HomologicalComplex (ModuleCat B) c₂)


-- @@ L1006-1008 verbatim
abbrev twistComplex {R : Type} [Ring R] [Algebra k R] {I : Type} {c : ComplexShape I}
    (ρ : R ≃ₐ[k] R) (K : HomologicalComplex (ModuleCat R) c) :=
  ((algebraTwist ρ).mapHomologicalComplex c).obj K


-- @@ L1010-1035 verbatim
def twistBicomplexIso :
    outerBicomplex k A B (twistComplex σ P) (twistComplex τ Q) ≅
      TotalMap.map₂ (algebraTwist (Algebra.TensorProduct.congr σ τ)) (outerBicomplex k A B P Q) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => twistObjIso σ τ (P.X i) (Q.X j)) (by
        intro j j' _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul x y => rfl
        | add x y hx hy =>
          exact (map_add _ x y).trans
            ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))) (by
      intro i i' _
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add x y hx hy =>
        exact (map_add _ x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))


-- @@ L1037-1041 verbatim
variable {J : Type} (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor P Q (bifunctor k A B) c]
  [HasMapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c]
  [(TotalMap.map₂ (algebraTwist (Algebra.TensorProduct.congr σ τ))
    (outerBicomplex k A B P Q)).HasTotal c]


-- @@ L1043-1047 verbatim
def twistTotalIso :
    mapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c ≅
      twistComplex (Algebra.TensorProduct.congr σ τ) (mapBifunctor P Q (bifunctor k A B) c) :=
  HomologicalComplex₂.total.mapIso (twistBicomplexIso σ τ P Q) c ≪≫
    TotalMap.iso (algebraTwist (Algebra.TensorProduct.congr σ τ)) (outerBicomplex k A B P Q) c


-- @@ L1049-1065 verbatim
@[reassoc]
lemma ι_twistTotalIso (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁,i₂) = j) :
    ιMapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c i₁ i₂ j h ≫
      (twistTotalIso σ τ P Q c).hom.f j =
    (twistObjIso σ τ (P.X i₁) (Q.X i₂)).hom ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map
        (ιMapBifunctor P Q (bifunctor k A B) c i₁ i₂ j h) := by
  change _ ≫ ((HomologicalComplex₂.total.mapIso (twistBicomplexIso σ τ P Q) c).hom.f j ≫ _) = _
  change HomologicalComplex₂.ιTotal _ c i₁ i₂ j h ≫
    ((HomologicalComplex₂.total.map (twistBicomplexIso σ τ P Q).hom c).f j ≫ _) = _
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map,Category.assoc]
  change (twistObjIso σ τ (P.X i₁) (Q.X i₂)).hom ≫ _ ≫
    TotalMap.compareX (algebraTwist (Algebra.TensorProduct.congr σ τ))
      (outerBicomplex k A B P Q) c j = _
  erw [TotalMap.ι_compareX]
  rfl


-- @@ L1067-1067 verbatim
end Tachikawa.OuterTensor




-- @@ L1071-1071 verbatim
namespace Tachikawa.OuterTensor

-- @@ L1072-1072 verbatim
open CategoryTheory

-- @@ L1073-1073 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L1074-1074 verbatim
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]


-- @@ L1076-1076 verbatim
def freeBasis {m : ℕ} (A : Type) [Ring A] (i : Fin m) : freeObj A m := Pi.single i 1


-- @@ L1078-1079 verbatim
def freeTensorBasis {m n : ℕ} (i : Fin m) (j : Fin n) :
    (((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n)) := freeBasis A i ⊗ₜ[k] freeBasis B j


-- @@ L1081-1087 verbatim
def freeAt {m : ℕ} (i : Fin m) (U : ModuleCat A) : U →ₗ[k] (freeObj A m ⟶ U) where
  toFun u := ModuleCat.ofHom
    { toFun := fun x => x i • u
      map_add' := fun x y => add_smul (x i) (y i) u
      map_smul' := fun r x => mul_smul r (x i) u }
  map_add' u v := ModuleCat.hom_ext (LinearMap.ext fun x => smul_add (x i) u v)
  map_smul' r u := ModuleCat.hom_ext (LinearMap.ext fun x => smul_comm (x i) r u)


-- @@ L1089-1094 verbatim
@[simp] lemma freeAt_single {m : ℕ} (i j : Fin m) (U : ModuleCat A) (u : U) :
    freeAt (k := k) i U u (freeBasis A j) = if i = j then u else 0 := by
  change ((Pi.single j 1 : Fin m → A) i) • u = _
  by_cases h : i = j
  · subst j; simp
  · simp [h]


-- @@ L1096-1096 verbatim
variable {U : ModuleCat A} {V : ModuleCat B}


-- @@ L1098-1101 verbatim
def freeValue {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) (i : Fin m) (j : Fin n) : U ⊗[k] V :=
  f.hom (freeTensorBasis (k := k) i j)


-- @@ L1103-1108 verbatim
def freeLift {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) :
    (freeObj A m ⟶ U) ⊗[k] (freeObj B n ⟶ V) :=
  ∑ i, ∑ j, TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V)
    (freeValue f i j)


-- @@ L1110-1129 verbatim
lemma freeLift_single_component {m n : ℕ} (i i' : Fin m) (j j' : Fin n) (z : U ⊗[k] V) :
    (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) z)).hom
      (freeTensorBasis (k := k) (A := A) (B := B) i' j') =
      if i = i' ∧ j = j' then z else 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
    change (freeAt (k := k) i U u (freeBasis A i')) ⊗ₜ[k]
      (freeAt (k := k) j V v (freeBasis B j')) = _
    simp only [freeAt_single]
    split_ifs <;> simp_all
  | add z w hz hw =>
    simp only [map_add, ModuleCat.hom_add]
    change (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) z)).hom
        (freeTensorBasis (k := k) i' j') +
      (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) w)).hom
        (freeTensorBasis (k := k) i' j') = _
    rw [hz, hw]
    split_ifs
    · rfl
    · exact zero_add _


-- @@ L1131-1153 verbatim
lemma homMap_freeLift_single {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) (i : Fin m) (j : Fin n) :
    (homMap (freeLift f)).hom (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      f.hom (freeTensorBasis (k := k) (A := A) (B := B) i j) := by
  classical
  let ev : (((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) →+ (U ⊗[k] V) :=
    { toFun := fun g => g.hom (freeTensorBasis (k := k) i j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (homMap (freeLift f)) = _
  simp only [freeLift, map_sum]
  change (∑ a, ∑ b, (homMap (TensorProduct.map (freeAt (k := k) a U)
    (freeAt (k := k) b V) (freeValue f a b))).hom
    (freeTensorBasis (k := k) i j)) = _
  simp only [freeLift_single_component]
  change (∑ a : Fin m, ∑ b : Fin n,
    (if a = i ∧ b = j then freeValue f a b else 0) : U ⊗[k] V) = freeValue f i j
  have hs (v : Fin m → Fin n → U ⊗[k] V) :
      (∑ a, ∑ b, if a = i ∧ b = j then v a b else 0) = v i j := by
    simp [ite_and, Finset.sum_ite_irrel]
  exact hs (freeValue f)


-- @@ L1155-1161 verbatim
lemma freeEquiv_single {m n : ℕ} (i : Fin m) (j : Fin n) :
    freeEquiv k A B m n (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      Pi.single i (Pi.single j 1) := by
  ext a b
  change ((Pi.single i 1 : Fin m → A) a) ⊗ₜ[k] ((Pi.single j 1 : Fin n → B) b) = _
  by_cases ha : a = i <;> by_cases hb : b = j <;> subst_vars <;>
    simp_all [Algebra.TensorProduct.one_def]


-- @@ L1163-1188 verbatim
lemma freeHom_ext {m n : ℕ}
    (f g : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V)
    (h : ∀ i j, f.hom (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      g.hom (freeTensorBasis (k := k) (A := A) (B := B) i j)) : f = g := by
  let e := freeEquiv k A B m n
  have hs (i : Fin m) (j : Fin n) : e.symm (Pi.single i (Pi.single j 1)) =
      freeTensorBasis (k := k) (A := A) (B := B) i j :=
    e.symm_apply_eq.mpr (freeEquiv_single (k := k) i j).symm
  have he : f.hom.comp e.symm.toLinearMap = g.hom.comp e.symm.toLinearMap := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    change f.hom (e.symm (Pi.single i (Pi.single j 1))) =
      g.hom (e.symm (Pi.single i (Pi.single j 1)))
    rw [hs]
    exact h i j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun he (e z)
  change f.hom (e.symm (e z)) = g.hom (e.symm (e z)) at hz
  exact (congrArg f.hom (e.symm_apply_apply z)).symm.trans
    (hz.trans (congrArg g.hom (e.symm_apply_apply z)))


-- @@ L1190-1193 verbatim
lemma homMap_freeLift {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) : homMap (freeLift f) = f :=
  freeHom_ext _ _ (homMap_freeLift_single f)


-- @@ L1195-1197 verbatim
lemma homMap_free_surjective (m n : ℕ) :
    Function.Surjective (homMap (k := k) (M := freeObj A m) (N := freeObj B n)
      (U := U) (V := V)) := fun f => ⟨freeLift f, homMap_freeLift f⟩


-- @@ L1199-1199 verbatim
end Tachikawa.OuterTensor




-- @@ L1203-1203 verbatim
namespace Tachikawa.OuterTensor

-- @@ L1204-1204 verbatim
open CategoryTheory

-- @@ L1205-1205 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L1206-1206 verbatim
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]


-- @@ L1208-1211 verbatim
lemma morphism_comp {M M' M'' : ModuleCat A} {N N' N'' : ModuleCat B}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    morphism (k := k) f g ≫ morphism f' g' = morphism (f ≫ f') (g ≫ g') :=
  ModuleCat.hom_ext (map_comp f f' g g')


-- @@ L1213-1215 verbatim
@[simp] lemma morphism_id (M : ModuleCat A) (N : ModuleCat B) :
    morphism (k := k) (𝟙 M) (𝟙 N) = 𝟙 (((bifunctor k A B).obj M).obj N) :=
  ModuleCat.hom_ext (map_id M N)


-- @@ L1217-1220 verbatim
def precompose {M M' U : ModuleCat A} (p : M' ⟶ M) : (M ⟶ U) →ₗ[k] (M' ⟶ U) where
  toFun f := p ≫ f
  map_add' _ _ := by simp only [Preadditive.comp_add]
  map_smul' _ _ := by simp only [CategoryTheory.Linear.comp_smul, RingHom.id_apply]


-- @@ L1222-1230 verbatim
lemma homMap_precompose {M M' U : ModuleCat A} {N N' V : ModuleCat B}
    (p : M' ⟶ M) (q : N' ⟶ N) (z : (M ⟶ U) ⊗[k] (N ⟶ V)) :
    homMap (TensorProduct.map (precompose (k := k) p) (precompose (k := k) q) z) =
      morphism p q ≫ homMap z := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    change morphism (p ≫ f) (q ≫ g) = morphism p q ≫ morphism f g
    exact (morphism_comp p f q g).symm
  | add z w hz hw => simp only [map_add, Preadditive.comp_add, hz, hw]


-- @@ L1232-1249 verbatim
lemma homMap_surjective (M U : ModuleCat A) (N V : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N] :
    Function.Surjective (homMap (k := k) (M := M) (N := N) (U := U) (V := V)) := by
  let c := finiteFreeCover (R := A) (M := M)
  let d := finiteFreeCover (R := B) (M := N)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  obtain ⟨j,hj⟩ := Module.projective_lifting_property d.map LinearMap.id d.surjective
  intro f
  let p : freeObj A c.rank ⟶ M := ModuleCat.ofHom c.map
  let q : freeObj B d.rank ⟶ N := ModuleCat.ofHom d.map
  let u : M ⟶ freeObj A c.rank := ModuleCat.ofHom i
  let v : N ⟶ freeObj B d.rank := ModuleCat.ofHom j
  obtain ⟨z,hz⟩ := homMap_free_surjective (k := k) c.rank d.rank (morphism p q ≫ f)
  refine ⟨TensorProduct.map (precompose (k := k) u) (precompose (k := k) v) z, ?_⟩
  rw [homMap_precompose, hz, ← Category.assoc, morphism_comp]
  have hu : u ≫ p = 𝟙 M := ModuleCat.hom_ext hi
  have hv : v ≫ q = 𝟙 N := ModuleCat.hom_ext hj
  rw [hu,hv,morphism_id,Category.id_comp]


-- @@ L1251-1256 verbatim
def homEquiv (M U : ModuleCat A) (N V : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    [FiniteDimensional k M] [FiniteDimensional k N] :
    (M ⟶ U) ⊗[k] (N ⟶ V) ≃ₗ[k]
      (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  LinearEquiv.ofBijective homMap ⟨homMap_injective,homMap_surjective M U N V⟩


-- @@ L1258-1258 verbatim
end Tachikawa.OuterTensor


-- @@ L1260-1260 verbatim
end


-- @@ L1262-1262 verbatim
end OAI
