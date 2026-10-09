import OAI.RingTheory.Tachikawa.Perfect


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace Tachikawa

-- @@ L8-8 verbatim
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

-- @@ L9-9 verbatim
universe u v

-- @@ L10-10 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt C]


-- @@ L12-23 verbatim
lemma projective_dimension_of_bounded_resolution {X : C} (P : ProjectiveResolution X)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) :
    HasProjectiveDimensionLE X d := by
  apply HasProjectiveDimensionLT.mk
  intro n hn Y e
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let : Subsingleton (Ext X Y (m+1)) := ext_subsingleton_of_boundaries P m (by
    intro f hf
    refine ⟨0, ?_⟩
    rw [comp_zero]
    exact (h (m+1) (by omega)).eq_of_src 0 f)
  exact Subsingleton.elim _ _


-- @@ L25-31 verbatim
lemma InAdd.projectiveDimension {W V : C} (h : InAdd W V) (n : ℕ)
    [HasProjectiveDimensionLT W n] : HasProjectiveDimensionLT V n := by
  apply HasProjectiveDimensionLT.mk
  intro i hi Y e
  let := HasProjectiveDimensionLT.subsingleton W n i hi Y
  let := ext_subsingleton_inAdd_left h i (Y := Y)
  exact Subsingleton.elim _ _


-- @@ L33-33 verbatim
end Tachikawa




-- @@ L37-37 verbatim
namespace Tachikawa

-- @@ L38-38 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L39-39 verbatim
universe u v w t

-- @@ L40-40 verbatim
attribute [local instance] Abelian.hasFiniteBiproducts

-- @@ L41-41 verbatim
variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{t} D] [Abelian C] [Abelian D]


-- @@ L43-46 verbatim
lemma InAdd.map (F : C ⥤ D) [F.Additive] {W V : C} (h : InAdd W V) :
    InAdd (F.obj W) (F.obj V) := by
  obtain ⟨n,⟨r⟩⟩ := h
  exact ⟨n,⟨(r.map F).trans (F.mapBiproduct (fun _ : Fin n => W)).retract⟩⟩


-- @@ L48-50 verbatim
lemma InAdd.iso {W V V' : C} (h : InAdd W V) (e : V' ≅ V) : InAdd W V' := by
  obtain ⟨n,⟨r⟩⟩ := h
  exact ⟨n,⟨e.retract.trans r⟩⟩


-- @@ L52-54 verbatim
lemma InAdd.retract {W V V' : C} (h : InAdd W V) (r : Retract V' V) : InAdd W V' := by
  obtain ⟨n,⟨r'⟩⟩ := h
  exact ⟨n,⟨r.trans r'⟩⟩


-- @@ L56-56 verbatim
end Tachikawa




-- @@ L60-60 verbatim
namespace Tachikawa

-- @@ L61-61 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L62-62 verbatim
open scoped ModuleCat.Algebra

-- @@ L63-63 verbatim
attribute [local instance] Abelian.hasFiniteBiproducts

-- @@ L64-64 verbatim
variable {R : Type} [Ring R]


-- @@ L66-73 verbatim
lemma finiteProjective_inAdd (M : ModuleCat R) [Module.Finite R M] [Module.Projective R M] :
    InAdd (ModuleCat.of R R) M := by
  let c := finiteFreeCover (R := R) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let e := ModuleCat.biproductIsoPi (fun _ : Fin c.rank => ModuleCat.of R R)
  refine ⟨c.rank,⟨{ i := ModuleCat.ofHom i ≫ e.inv, r := e.hom ≫ ModuleCat.ofHom c.map, retract := ?_ }⟩⟩
  rw [Category.assoc,← Category.assoc e.inv,e.inv_hom_id,Category.id_comp]
  exact ModuleCat.hom_ext hi


-- @@ L75-75 verbatim
end Tachikawa




-- @@ L79-79 verbatim
namespace Tachikawa.Construction

-- @@ L80-80 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L81-81 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L82-82 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)


-- @@ L84-87 verbatim
lemma restrictedLeftResolution_finite (n : ℕ) :
    Module.Finite (B q) ((restrictedLeftResolution q hq).complex.X n) :=
  OuterTensor.total_finite (tLeftResolution q hq).complex (tLeftResolution q hq).complex
    (tLeftResolution_finite q hq) (tLeftResolution_finite q hq) n


-- @@ L89-112 verbatim
lemma restrictedRightResolution_finite (n : ℕ) :
    Module.Finite (B q)ᵐᵒᵖ ((restrictedRightResolution q hq).complex.X n) := by
  let : Module.Finite ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ)
      ((eRightResolution q hq).complex.X n) :=
    OuterTensor.total_finite (tRightResolution q hq).complex (tRightResolution q hq).complex
      (tRightResolution_finite q hq) (tRightResolution_finite q hq) n
  let : FiniteDimensional k ((eRightResolution q hq).complex.X n) :=
    Module.Finite.trans ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ) _
  change Module.Finite (B q)ᵐᵒᵖ ((opTensorRestriction q).obj ((eRightResolution q hq).complex.X n))
  let e : (opTensorRestriction q).obj ((eRightResolution q hq).complex.X n) ≃ₗ[k]
      (eRightResolution q hq).complex.X n :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' c x := by
        change ((opTensorB q).symm (algebraMap k (B q)ᵐᵒᵖ c)) •
          (show (eRightResolution q hq).complex.X n from x) = c • _
        rw [AlgEquiv.commutes]
        rfl }
  let : FiniteDimensional k ((opTensorRestriction q).obj ((eRightResolution q hq).complex.X n)) :=
    Module.Finite.equiv e.symm
  exact Module.Finite.of_restrictScalars_finite k _ _


-- @@ L114-122 verbatim
def restrictedBimoduleResolution : ProjectiveResolution
    ((AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
      (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q))).obj
      (ModuleCat.of (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)))) :=
  transportResolution
    (OuterTensor.resolution k (B q) (B q)ᵐᵒᵖ
      (restrictedLeftResolution q hq) (restrictedRightResolution q hq)
      (restrictedLeftResolution_finite q hq) (restrictedRightResolution_finite q hq))
    (Enveloping.restrictedOuterRegularIso (inclusionB q))


-- @@ L124-127 verbatim
lemma restrictedBimoduleResolution_above (n : ℕ) (hn : 8 < n) :
    IsZero ((restrictedBimoduleResolution q hq).complex.X n) :=
  OuterTensor.total_isZero_above _ _ 4 4
    (restrictedLeftResolution_above q hq) (restrictedRightResolution_above q hq) n hn


-- @@ L129-135 verbatim
include hq in
lemma restrictedBimodule_pd : HasProjectiveDimensionLE
    ((AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
      (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q))).obj
      (ModuleCat.of (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)))) 8 :=
  projective_dimension_of_bounded_resolution (restrictedBimoduleResolution q hq) 8
    (restrictedBimoduleResolution_above q hq)


-- @@ L137-148 verbatim
include hq in

lemma restrictedProjective_pd (P : ModuleCat (Enveloping.Alg k (E q) (E q)))
    [Module.Finite (Enveloping.Alg k (E q) (E q)) P]
    [Module.Projective (Enveloping.Alg k (E q) (E q)) P] :
    HasProjectiveDimensionLE
      ((AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
      (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q))).obj P) 8 := by
  let := restrictedBimodule_pd q hq
  exact ((finiteProjective_inAdd P).map
    (AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
      (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q)))).projectiveDimension 9


-- @@ L150-150 verbatim
end Tachikawa.Construction




-- @@ L154-154 verbatim
namespace Tachikawa

-- @@ L155-155 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L156-156 verbatim
open scoped ModuleCat.Algebra

-- @@ L157-157 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]


-- @@ L159-160 verbatim
def freeEndo : ModuleCat R ⥤ ModuleCat R :=
  AlgebraInduction.res (Algebra.ofId k R) ⋙ AlgebraInduction.functor (Algebra.ofId k R)

-- @@ L161-162 verbatim
instance : (freeEndo (k := k) (R := R)).Additive := inferInstanceAs
  ((AlgebraInduction.res (Algebra.ofId k R) ⋙ AlgebraInduction.functor (Algebra.ofId k R)).Additive)


-- @@ L164-165 verbatim
def freeCounit (M : ModuleCat R) : (freeEndo (k := k)).obj M ⟶ M :=
  AlgebraInduction.extend (Algebra.ofId k R) (𝟙 _)


-- @@ L167-173 verbatim
lemma freeCounit_surjective (M : ModuleCat R) : Function.Surjective (freeCounit (k := k) M) := by
  intro x
  refine ⟨BalancedTensor.mk (k := k) (R := k) (S := R)
    (show AlgebraInduction.Bimod (Algebra.ofId k R) from (1 : R))
    (show (AlgebraInduction.res (Algebra.ofId k R)).obj M from x), ?_⟩
  change (1 : R) • x = x
  exact one_smul R x


-- @@ L175-176 verbatim
instance (M : ModuleCat R) : Epi (freeCounit (k := k) M) :=
  (ModuleCat.epi_iff_surjective _).2 (freeCounit_surjective M)


-- @@ L178-185 verbatim
def freeCounitNat : freeEndo (k := k) (R := R) ⟶ 𝟭 _ where
  app := freeCounit
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro r x
    change (show R from r) • f (show M from x) = f ((show R from r) • (show M from x))
    exact (f.hom.map_smul _ _).symm


-- @@ L187-189 verbatim
instance : Epi (freeCounitNat (k := k) (R := R)) := by
  let (M : ModuleCat R) : Epi ((freeCounitNat (k := k)).app M) := inferInstanceAs (Epi (freeCounit (k := k) M))
  exact NatTrans.epi_of_epi_app _


-- @@ L191-191 verbatim
def freeKernel : ModuleCat R ⥤ ModuleCat R := kernel (freeCounitNat (k := k) (R := R))

-- @@ L192-200 verbatim
instance : (freeKernel (k := k) (R := R)).Additive := by
  constructor
  intro X Y f g
  dsimp only [freeKernel]
  let ι := kernel.ι (freeCounitNat (k := k) (R := R))
  let : Mono (ι.app Y) := inferInstance
  apply (cancel_mono (ι.app Y)).1
  erw [ι.naturality,Functor.map_add,Preadditive.comp_add,
    Preadditive.add_comp,ι.naturality,ι.naturality]


-- @@ L202-203 verbatim
def freeι (M : ModuleCat R) : (freeKernel (k := k)).obj M ⟶ (freeEndo (k := k)).obj M :=
  (kernel.ι (freeCounitNat (k := k))).app M


-- @@ L205-206 verbatim
lemma freeι_counit (M : ModuleCat R) : freeι (k := k) M ≫ freeCounit M = 0 :=
  congrArg (fun f => f.app M) (kernel.condition (freeCounitNat (k := k)))


-- @@ L208-209 verbatim
def freeShort (M : ModuleCat R) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (freeι (k := k) M) (freeCounit M) (freeι_counit M)


-- @@ L211-215 verbatim
lemma freeShort_exact (M : ModuleCat R) : (freeShort (k := k) M).ShortExact := by
  let T : ShortComplex (ModuleCat R ⥤ ModuleCat R) :=
    ShortComplex.mk (kernel.ι (freeCounitNat (k := k))) freeCounitNat (kernel.condition _)
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel _ }
  exact hT.map ((evaluation _ _).obj M)


-- @@ L217-223 verbatim
instance freeEndo_projective (M : ModuleCat R) [FiniteDimensional k M] :
    Projective ((freeEndo (k := k)).obj M) := by
  let : Module.Finite k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) :=
    inferInstanceAs (Module.Finite k M)
  let : Module.Projective k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) := inferInstance
  change Projective ((AlgebraInduction.functor (Algebra.ofId k R)).obj _)
  infer_instance


-- @@ L225-225 verbatim
variable [FiniteDimensional k R]

-- @@ L226-231 verbatim
instance freeEndo_finite (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((freeEndo (k := k)).obj M) := by
  let : FiniteDimensional k ((AlgebraInduction.res (Algebra.ofId k R)).obj M) :=
    inferInstanceAs (FiniteDimensional k M)
  change FiniteDimensional k ((AlgebraInduction.functor (Algebra.ofId k R)).obj _)
  infer_instance


-- @@ L233-239 verbatim
instance freeKernel_finite (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((freeKernel (k := k)).obj M) := by
  have : Mono (freeι (k := k) M) := inferInstanceAs
    (Mono ((kernel.ι (freeCounitNat (k := k))).app M))
  have hi : Function.Injective (freeι (k := k) M) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact Module.Finite.of_injective ((freeι M).hom.restrictScalars k) hi


-- @@ L241-248 verbatim
omit [FiniteDimensional k R] in
lemma freeKernel_pd (M : ModuleCat R) [FiniteDimensional k M] (n : ℕ)
    [HasProjectiveDimensionLE M (n+1)] :
    HasProjectiveDimensionLE ((freeKernel (k := k)).obj M) n := by
  apply (freeShort_exact (k := k) M).hasProjectiveDimensionLT_X₁ (n+1)
  · change HasProjectiveDimensionLT ((freeEndo (k := k)).obj M) (n+1)
    exact hasProjectiveDimensionLT_of_ge _ 1 (n+1) (by omega)
  · exact inferInstanceAs (HasProjectiveDimensionLE M (n+1))


-- @@ L250-250 verbatim
end Tachikawa




-- @@ L254-254 verbatim
namespace Tachikawa.Enveloping

-- @@ L255-255 verbatim
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

-- @@ L256-256 verbatim
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]


-- @@ L258-259 verbatim
abbrev coindComplex (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ((coindEndo (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P


-- @@ L261-262 verbatim
abbrev cokerComplex (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ((coindCoker (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P


-- @@ L264-266 verbatim
def coindComplexUnit (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) : P ⟶ coindComplex P where
  f i := coindUnit (P.X i)
  comm' i j _ := (coindUnitNat.naturality (P.d i j)).symm


-- @@ L268-270 verbatim
def coindComplexπ (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) : coindComplex P ⟶ cokerComplex P where
  f i := coindπ (P.X i)
  comm' i j _ := ((cokernel.π (coindUnitNat (k := k))).naturality (P.d i j)).symm


-- @@ L272-277 verbatim
def coindComplexShort (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :
    ShortComplex (CochainComplex (ModuleCat (Alg k R S)) ℤ) :=
  ShortComplex.mk (coindComplexUnit P) (coindComplexπ P) (by
    apply HomologicalComplex.Hom.ext
    funext i
    exact coindUnit_π (P.X i))


-- @@ L279-283 verbatim
lemma coindComplexShort_exact (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) :
    (coindComplexShort P).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact coindShort_exact (P.X i)


-- @@ L285-285 verbatim
end Tachikawa.Enveloping




-- @@ L289-289 verbatim
namespace Tachikawa

-- @@ L290-290 verbatim
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

-- @@ L291-291 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]


-- @@ L293-294 verbatim
abbrev freeComplex (P : CochainComplex (ModuleCat R) ℤ) :=
  ((freeEndo (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

-- @@ L295-296 verbatim
abbrev kernelComplex (P : CochainComplex (ModuleCat R) ℤ) :=
  ((freeKernel (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P


-- @@ L298-300 verbatim
def freeComplexCounit (P : CochainComplex (ModuleCat R) ℤ) : freeComplex (k := k) P ⟶ P where
  f i := freeCounit (P.X i)
  comm' i j _ := ((freeCounitNat (k := k)).naturality (P.d i j)).symm


-- @@ L302-304 verbatim
def freeComplexι (P : CochainComplex (ModuleCat R) ℤ) : kernelComplex (k := k) P ⟶ freeComplex (k := k) P where
  f i := freeι (P.X i)
  comm' i j _ := ((kernel.ι (freeCounitNat (k := k))).naturality (P.d i j)).symm


-- @@ L306-311 verbatim
def freeComplexShort (P : CochainComplex (ModuleCat R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (freeComplexι (k := k) P) (freeComplexCounit (k := k) P) (by
    apply HomologicalComplex.Hom.ext
    funext i
    exact freeι_counit (P.X i))


-- @@ L313-317 verbatim
lemma freeComplexShort_exact (P : CochainComplex (ModuleCat R) ℤ) :
    (freeComplexShort (k := k) P).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact freeShort_exact (P.X i)


-- @@ L319-319 verbatim
end Tachikawa




-- @@ L323-323 verbatim
namespace Tachikawa

-- @@ L324-324 verbatim
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

-- @@ L325-325 verbatim
open HomologicalComplex CochainComplex

-- @@ L326-326 verbatim
universe u v

-- @@ L327-327 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C]

-- @@ L328-328 verbatim
attribute [local instance] HasDerivedCategory.standard


-- @@ L330-343 verbatim
lemma mappingCone_map_quasiIso {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map f g a b h) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  let t := DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap f g a b h)
  have h1 : IsIso t.hom₁ := by
    change IsIso (DerivedCategory.Q.map a)
    infer_instance
  have h2 : IsIso t.hom₂ := by
    change IsIso (DerivedCategory.Q.map b)
    infer_instance
  exact isIso₃_of_isIso₁₂ t (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g) h1 h2


-- @@ L345-345 verbatim
end Tachikawa




-- @@ L349-349 verbatim
namespace Tachikawa

-- @@ L350-350 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L351-351 verbatim
open HomologicalComplex CochainComplex

-- @@ L352-352 verbatim
universe u v

-- @@ L353-353 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C]


-- @@ L355-357 verbatim
def shortExactReplacementMapDual (S : ShortComplex (CochainComplex C ℤ))
    {Q : CochainComplex C ℤ} (α : Q ⟶ S.X₁) : mappingCone (α ≫ S.f) ⟶ S.X₃ :=
  mappingCone.map (α ≫ S.f) S.f α (𝟙 S.X₂) (by simp) ≫ mappingCone.descShortComplex S


-- @@ L359-364 verbatim
lemma shortExactReplacementMapDual_quasiIso (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) {Q : CochainComplex C ℤ} (α : Q ⟶ S.X₁) [QuasiIso α] :
    QuasiIso (shortExactReplacementMapDual S α) := by
  have := mappingCone_map_quasiIso (α ≫ S.f) S.f α (𝟙 S.X₂) (by simp)
  have := mappingCone.quasiIso_descShortComplex hS
  exact quasiIso_comp _ _


-- @@ L366-366 verbatim
end Tachikawa




-- @@ L370-370 verbatim
namespace Tachikawa

-- @@ L371-371 verbatim
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

-- @@ L372-372 verbatim
open scoped ModuleCat.Algebra

-- @@ L373-373 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]


-- @@ L375-378 verbatim
structure IndReplacement (P : CochainComplex (ModuleCat.{0} R) ℤ) where
  complex : CochainComplex (ModuleCat.{0} R) ℤ
  map : complex ⟶ P
  quasiIso : QuasiIso map

-- @@ L379-379 verbatim
attribute [instance] IndReplacement.quasiIso


-- @@ L381-389 verbatim
def indReplacement : (n : ℕ) → (P : CochainComplex (ModuleCat.{0} R) ℤ) → IndReplacement P
  | 0, P => ⟨P,𝟙 P,inferInstance⟩
  | n+1, P =>
    let t := indReplacement n (kernelComplex (k := k) P)
    { complex := mappingCone (t.map ≫ freeComplexι P)
      map := shortExactReplacementMapDual (freeComplexShort P) t.map
      quasiIso := by
        exact @shortExactReplacementMapDual_quasiIso _ _ _ (freeComplexShort P)
          (freeComplexShort_exact P) _ t.map t.quasiIso }


-- @@ L391-396 verbatim
lemma mappingCone_projective {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L)
    (hK : ∀ i, Projective (K.X i)) (hL : ∀ i, Projective (L.X i)) (i : ℤ) :
    Projective ((mappingCone f).X i) := by
  let := hK (i+1)
  let := hL i
  exact Projective.of_iso (homotopyCofiber.XIsoBiprod f i (i+1) (by rfl)).symm inferInstance


-- @@ L398-404 verbatim
lemma mappingCone_finite {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L)
    (hK : ∀ i, FiniteDimensional k (K.X i)) (hL : ∀ i, FiniteDimensional k (L.X i)) (i : ℤ) :
    FiniteDimensional k ((mappingCone f).X i) := by
  let := hK (i+1)
  let := hL i
  let e := homotopyCofiber.XIsoBiprod f i (i+1) (by rfl) ≪≫ ModuleCat.biprodIsoProd _ _
  exact Module.Finite.equiv (e.toLinearEquiv.restrictScalars k).symm


-- @@ L406-409 verbatim
lemma mappingCone_isZero_X {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L) (i : ℤ)
    (hK : IsZero (K.X (i+1))) (hL : IsZero (L.X i)) : IsZero ((mappingCone f).X i) :=
  IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hK,hL⟩)
    (homotopyCofiber.XIsoBiprod f i (i+1) (by rfl))


-- @@ L411-423 verbatim
lemma indReplacement_bounded (n : ℕ) (P : CochainComplex (ModuleCat.{0} R) ℤ) (l u : ℤ)
    (hP : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∀ i, i < l - n ∨ u < i → IsZero ((indReplacement (k := k) n P).complex.X i) := by
  induction n generalizing P with
  | zero => simpa only [indReplacement,Nat.cast_zero,sub_zero] using hP
  | succ n ih =>
    intro i hi
    apply mappingCone_isZero_X
    · apply ih (kernelComplex P)
      · intro j hj
        exact (freeKernel (k := k)).map_isZero (hP j hj)
      · omega
    · exact (freeEndo (k := k)).map_isZero (hP i (by omega))


-- @@ L425-425 verbatim
variable [FiniteDimensional k R]

-- @@ L426-443 verbatim
lemma indReplacement_terms (n : ℕ) (P : CochainComplex (ModuleCat.{0} R) ℤ)
    (hfin : ∀ i, FiniteDimensional k (P.X i))
    (hpd : ∀ i, HasProjectiveDimensionLE (P.X i) n) :
    (∀ i, Projective ((indReplacement (k := k) n P).complex.X i)) ∧
    (∀ i, FiniteDimensional k ((indReplacement (k := k) n P).complex.X i)) := by
  induction n generalizing P with
  | zero =>
    refine ⟨?_,hfin⟩
    intro i
    exact (projective_iff_hasProjectiveDimensionLE_zero (P.X i)).2 (hpd i)
  | succ n ih =>
    obtain ⟨hp,hf⟩ := ih (kernelComplex (k := k) P)
      (fun i => by let := hfin i; exact freeKernel_finite (k := k) (P.X i))
      (fun i => by let := hfin i; let := hpd i; exact freeKernel_pd (k := k) (P.X i) n)
    exact ⟨mappingCone_projective _ hp
      (fun i => by let := hfin i; exact freeEndo_projective (k := k) (P.X i)),
      mappingCone_finite _ hf
      (fun i => by let := hfin i; exact freeEndo_finite (k := k) (P.X i))⟩


-- @@ L445-454 verbatim
theorem bounded_projective_replacement (P : CochainComplex (ModuleCat.{0} R) ℤ) (n : ℕ)
    (hfin : ∀ i, FiniteDimensional k (P.X i))
    (hpd : ∀ i, HasProjectiveDimensionLE (P.X i) n)
    (l u : ℤ) (hb : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℤ) (f : Q ⟶ P), QuasiIso f ∧
      (∀ i, Projective (Q.X i)) ∧ (∀ i, FiniteDimensional k (Q.X i)) ∧
      (∀ i, i < l-n ∨ u < i → IsZero (Q.X i)) :=
  ⟨(indReplacement (k := k) n P).complex,(indReplacement (k := k) n P).map,inferInstance,
    (indReplacement_terms n P hfin hpd).1,(indReplacement_terms n P hfin hpd).2,
    indReplacement_bounded n P l u hb⟩


-- @@ L456-456 verbatim
end Tachikawa




-- @@ L460-460 verbatim
namespace Tachikawa.Construction

-- @@ L461-461 verbatim
open CategoryTheory CategoryTheory.Limits HomologicalComplex

-- @@ L462-462 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L463-463 verbatim
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)


-- @@ L465-468 verbatim
abbrev bimoduleRestriction : ModuleCat.{0} (Enveloping.Alg k (E q) (E q)) ⥤
    ModuleCat.{0} (Enveloping.Alg k (B q) (B q)) :=
  AlgebraInduction.res (k := k) (R := Enveloping.Alg k (B q) (B q))
    (S := Enveloping.Alg k (E q) (E q)) (Enveloping.envelopingMap (inclusionB q))


-- @@ L470-506 verbatim
include hq in

theorem restricted_perfect_replacement
    (P : CochainComplex (ModuleCat.{0} (Enveloping.Alg k (E q) (E q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (E q) (E q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (E q) (E q)) (P.X i))
    (l u : ℤ) (hb : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (Q : CochainComplex (ModuleCat.{0} (Enveloping.Alg k (B q) (B q))) ℤ)
      (f : Q ⟶ ((bimoduleRestriction q).mapHomologicalComplex (.up ℤ)).obj P),
      QuasiIso f ∧
      (∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (Q.X i)) ∧
      (∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (Q.X i)) ∧
      (∀ i, i < l-8 ∨ u < i → IsZero (Q.X i)) := by
  have hfin' (i : ℤ) : FiniteDimensional k ((bimoduleRestriction q).obj (P.X i)) := by
    let := hfin i
    let : IsScalarTower k (Enveloping.Alg k (E q) (E q)) (P.X i) :=
      ModuleCat.Algebra.instIsScalarTowerCarrier (S₀ := k)
        (S := Enveloping.Alg k (E q) (E q)) (M := P.X i)
    let : FiniteDimensional k (P.X i) := Module.Finite.trans (Enveloping.Alg k (E q) (E q)) _
    exact AlgebraInduction.resFinite _ _
  have hpd (i : ℤ) : HasProjectiveDimensionLE ((bimoduleRestriction q).obj (P.X i)) 8 := by
    let := hfin i
    let := hproj i
    exact restrictedProjective_pd q hq (P.X i)
  obtain ⟨Q,f,hf,hp,hf',hb'⟩ := bounded_projective_replacement
    (((bimoduleRestriction q).mapHomologicalComplex (.up ℤ)).obj P) 8 hfin' hpd l u
    (fun i hi => (bimoduleRestriction q).map_isZero (hb i hi))
  refine ⟨Q,f,hf,?_,?_,hb'⟩
  · intro i
    let := hp i
    infer_instance
  · intro i
    let := hf' i
    let : IsScalarTower k (Enveloping.Alg k (B q) (B q)) (Q.X i) :=
      ModuleCat.Algebra.instIsScalarTowerCarrier (S₀ := k)
        (S := Enveloping.Alg k (B q) (B q)) (M := Q.X i)
    exact Module.Finite.of_restrictScalars_finite k _ _


-- @@ L508-508 verbatim
end Tachikawa.Construction




-- @@ L512-512 verbatim
namespace Tachikawa.Construction

-- @@ L513-513 verbatim
open CategoryTheory

-- @@ L514-514 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L515-520 verbatim
def restrictedTwistedUnderlying {k R S : Type} [Field k] [Ring R] [Ring S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (σ : S ≃ₐ[k] S) :
    (AlgebraInduction.res (Enveloping.envelopingMap φ)).obj
      (Enveloping.twistedRegular σ) ≃ₗ[k] S :=
  (AlgebraInduction.resUnderlyingEquiv (Enveloping.envelopingMap φ)
    (Enveloping.twistedRegular σ)).trans (Enveloping.twistedUnderlying σ)


-- @@ L522-522 verbatim
variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)


-- @@ L524-525 verbatim
def restrictedUUnderlying : (bimoduleRestriction q).obj (U q H hH) ≃ₗ[k] E q :=
  restrictedTwistedUnderlying (inclusionB q) (sigma q H hH)


-- @@ L527-530 verbatim
def rhoBimoduleLinear : (bimoduleRestriction q).obj (U q H hH) →ₗ[k]
    Enveloping.dualRegularObj (k := k) (R := B q) :=
  (Enveloping.dualRegularUnderlying (k := k) (R := B q)).symm.toLinearMap.comp
    ((rho q).comp (restrictedUUnderlying q H hH).toLinearMap)


-- @@ L532-539 verbatim
lemma rhoBimoduleLinear_tensor (r : B q) (s : (B q)ᵐᵒᵖ)
    (x : (bimoduleRestriction q).obj (U q H hH)) :
    rhoBimoduleLinear q H hH ((r ⊗ₜ[k] s) • x) =
      (r ⊗ₜ[k] s) • rhoBimoduleLinear q H hH x := by
  apply Enveloping.dualRegularUnderlying.injective
  change rho q (inclusionB q r * ((show E q from x) * sigma q H hH (inclusionB q s.unop))) =
    r • MulOpposite.op s.unop • rho q (show E q from x)
  rw [sigma_inclusionB,rho_left,rho_right]


-- @@ L541-543 verbatim
def rhoBimodule : (bimoduleRestriction q).obj (U q H hH) ⟶
    Enveloping.dualRegularObj (k := k) (R := B q) :=
  Enveloping.homOfLinear (rhoBimoduleLinear q H hH) (rhoBimoduleLinear_tensor q H hH)


-- @@ L545-554 verbatim
lemma restricted_socle_character :
    Enveloping.restrictedRegularMap (inclusionB q) ≫
      (bimoduleRestriction q).map
        (HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
          socleBimoduleMap q H hH) ≫ rhoBimodule q H hH = characterBimoduleMap q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Enveloping.dualRegularUnderlying.injective
  exact rho_representation_socle q H hH (Enveloping.regularUnderlyingEquiv x)


-- @@ L556-556 verbatim
end Tachikawa.Construction




-- @@ L560-560 verbatim
namespace Tachikawa.Enveloping

-- @@ L561-561 verbatim
open CategoryTheory HomologicalComplex

-- @@ L562-562 verbatim
open scoped TensorProduct ModuleCat.Algebra

-- @@ L563-564 verbatim
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)


-- @@ L566-569 verbatim
def regularUnit : (regularResolution (k := k) (R := R)).cochainComplex ⟶
    ((AlgebraInduction.res (envelopingMap φ)).mapHomologicalComplex (.up ℤ)).obj
      (inducedRegularCochain φ) :=
  AlgebraInduction.complexUnit (envelopingMap φ) (.up ℤ) _


-- @@ L571-576 verbatim
def restrictedSingleMap {U : ModuleCat.{0} (Alg k S S)} {N : ModuleCat.{0} (Alg k R R)}
    (b : (AlgebraInduction.res (envelopingMap φ)).obj U ⟶ N) :
    ((AlgebraInduction.res (envelopingMap φ)).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj U) ⟶ (CochainComplex.singleFunctor _ 0).obj N :=
  (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app U ≫
    (CochainComplex.singleFunctor _ 0).map b


-- @@ L578-586 verbatim
lemma regularUnit_square {U : ModuleCat.{0} (Alg k S S)} {N : ModuleCat.{0} (Alg k R R)}
    (v : regular (k := k) (R := S) ⟶ U)
    (b : (AlgebraInduction.res (envelopingMap φ)).obj U ⟶ N) :
    regularUnit φ ≫ ((AlgebraInduction.res (envelopingMap φ)).mapHomologicalComplex (.up ℤ)).map
      (inducedRegularAugmentation φ ≫ (CochainComplex.singleFunctor _ 0).map v) ≫
      restrictedSingleMap φ b = (regularResolution (k := k) (R := R)).π' ≫
        (CochainComplex.singleFunctor _ 0).map
          (restrictedRegularMap φ ≫ (AlgebraInduction.res (envelopingMap φ)).map v ≫ b) :=
  induced_regular_square φ v b


-- @@ L588-588 verbatim
end Tachikawa.Enveloping




-- @@ L592-592 verbatim
namespace Tachikawa

-- @@ L593-593 verbatim
open CategoryTheory CategoryTheory.Limits

-- @@ L594-596 verbatim
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]


-- @@ L598-603 verbatim
def exactDerivedHom {X Y : CochainComplex C ℤ}
    (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj X) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Y) :=
  F.mapDerivedCategoryFactors.inv.app X ≫ F.mapDerivedCategory.map f ≫
    F.mapDerivedCategoryFactors.hom.app Y


-- @@ L605-610 verbatim
lemma exactDerivedHom_comp {X Y Z : CochainComplex C ℤ}
    (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y)
    (g : DerivedCategory.Q.obj Y ⟶ DerivedCategory.Q.obj Z) :
    exactDerivedHom F (f ≫ g) = exactDerivedHom F f ≫ exactDerivedHom F g := by
  simp only [exactDerivedHom,Functor.map_comp,Category.assoc,
    Iso.hom_inv_id_app_assoc]


-- @@ L612-616 verbatim
lemma exactDerivedHom_map {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    exactDerivedHom F (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  dsimp only [exactDerivedHom]
  rw [F.mapDerivedCategoryFactors_hom_naturality,Iso.inv_hom_id_app_assoc]


-- @@ L618-618 verbatim
end Tachikawa




-- @@ L622-622 verbatim
namespace Tachikawa

-- @@ L623-623 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L624-624 verbatim
variable {C : Type*} [Category C] [Abelian C]

-- @@ L625-625 verbatim
variable {K L : CochainComplex C ℤ}


-- @@ L627-631 verbatim
def HomColumnBoundaries (K L : CochainComplex C ℤ) : Prop :=
  ∀ (n : ℕ) (a : K.X (-(n+1 : ℤ)) ⟶ L.X (-(n+1 : ℤ))),
    K.d (-(n+2 : ℤ)) (-(n+1 : ℤ)) ≫ a = 0 →
    ∃ b : K.X (-(n : ℤ)) ⟶ L.X (-(n+1 : ℤ)),
      K.d (-(n+1 : ℤ)) (-(n : ℤ)) ≫ b = a


-- @@ L633-672 verbatim
lemma raise_cochain_map (n : ℕ) (f : K ⟶ L)
    (hf : ∀ j, j < -(n+1 : ℤ) → f.f j = 0) (hb : HomColumnBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, j < -(n : ℤ) → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  classical
  have hc : K.d (-(n+2 : ℤ)) (-(n+1 : ℤ)) ≫ f.f (-(n+1 : ℤ)) = 0 := by
    rw [← f.comm, hf _ (by omega), zero_comp]
  obtain ⟨g,hg⟩ := hb n (f.f (-(n+1 : ℤ))) hc
  let h : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = -(n : ℤ) then if hj : j = -(n+1 : ℤ) then
      eqToHom (congrArg K.X hi) ≫ g ≫ eqToHom (congrArg L.X hj.symm)
      else 0 else 0
  have hh : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0 := by
    intro i j hij
    dsimp only [h]
    split_ifs with hi hj
    · subst i; subst j
      exact False.elim (hij (by change -(n+1 : ℤ)+1= -(n : ℤ); omega))
    all_goals rfl
  let z := Homotopy.nullHomotopicMap h
  have hz (j : ℤ) : z.f j = K.d j (j+1) ≫ h (j+1) j + h j (j-1) ≫ L.d (j-1) j :=
    Homotopy.nullHomotopicMap_f (by change j-1+1=j; omega) rfl h
  refine ⟨f-z, ?_, ?_⟩
  · intro j hj
    change f.f j - z.f j = 0
    rw [hz]
    have h1 : j ≠ -(n : ℤ) := by omega
    by_cases h2 : j = -(n+1 : ℤ)
    · subst j
      have hi : -(n+1 : ℤ)+1= -(n : ℤ) := by omega
      rw [hi]
      simp only [h, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id,
        dite_eq_right h1, zero_comp, add_zero, hg, sub_self]
    · have h3 : j+1 ≠ -(n : ℤ) := by omega
      simp only [h, dite_eq_right h1, dite_eq_right h3, comp_zero, zero_comp, add_zero,
        hf j (by omega), sub_self]
  · apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have he : f-(f-z)=z := by abel
    rw [he]
    exact Homotopy.nullHomotopy h hh


-- @@ L674-682 verbatim
theorem cochain_map_supported_nonnegative (N : ℕ) (f : K ⟶ L)
    (hf : ∀ j, j < -(N : ℤ) → f.f j = 0) (hb : HomColumnBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, j < 0 → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  induction N generalizing f with
  | zero => exact ⟨f,by simpa using hf,⟨Homotopy.refl f⟩⟩
  | succ N ih =>
    obtain ⟨g,hg,⟨H⟩⟩ := raise_cochain_map N f (by simpa using hf) hb
    obtain ⟨f',hf',⟨H'⟩⟩ := ih g hg
    exact ⟨f',hf',⟨H.trans H'⟩⟩


-- @@ L684-684 verbatim
end Tachikawa




-- @@ L688-688 verbatim
namespace Tachikawa

-- @@ L689-689 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L690-690 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- @@ L691-691 verbatim
variable {X : C} (P : ProjectiveResolution X) (L : CochainComplex C ℤ)


-- @@ L693-721 verbatim
lemma resolution_HomColumnBoundaries
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1))) :
    HomColumnBoundaries (P.complex.extend ComplexShape.embeddingDownNat) L := by
  intro n a ha
  let e (j : ℕ) := P.complex.extendXIso ComplexShape.embeddingDownNat
    (i := j) (i' := -(j : ℤ)) rfl
  have d (i j : ℕ) : (P.complex.extend ComplexShape.embeddingDownNat).d (-(i : ℤ)) (-(j : ℤ)) =
      (e i).hom ≫ P.complex.d i j ≫ (e j).inv :=
    P.complex.extend_d_eq ComplexShape.embeddingDownNat rfl rfl
  have he1 : -(↑(n+1) : ℤ) = -(n+1 : ℤ) := by push_cast; rfl
  have he2 : -(↑(n+2) : ℤ) = -(n+2 : ℤ) := by push_cast; rfl
  let e1 : (P.complex.extend ComplexShape.embeddingDownNat).X (-(n+1 : ℤ)) ≅ P.complex.X (n+1) :=
    eqToIso (congrArg _ he1.symm) ≪≫ e (n+1)
  let e2 : (P.complex.extend ComplexShape.embeddingDownNat).X (-(n+2 : ℤ)) ≅ P.complex.X (n+2) :=
    eqToIso (congrArg _ he2.symm) ≪≫ e (n+2)
  have hd1 : (P.complex.extend ComplexShape.embeddingDownNat).d (-(n+2 : ℤ)) (-(n+1 : ℤ)) =
      e2.hom ≫ P.complex.d (n+2) (n+1) ≫ e1.inv := by
    simpa [e1,e2,he1,he2] using d (n+2) (n+1)
  have hd0 : (P.complex.extend ComplexShape.embeddingDownNat).d (-(n+1 : ℤ)) (-(n : ℤ)) =
      e1.hom ≫ P.complex.d (n+1) n ≫ (e n).inv := by
    simpa [e1,he1] using d (n+1) n
  have ha' : P.complex.d (n+2) (n+1) ≫ e1.inv ≫ a = 0 := by
    have hs := congrArg (fun t => e2.inv ≫ t) ha
    simpa only [hd1, Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using hs
  let := hExt n
  obtain ⟨b,hb⟩ := boundaries_of_ext_subsingleton P n (e1.inv ≫ a) ha'
  refine ⟨(e n).hom ≫ b, ?_⟩
  rw [hd0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hb, Iso.hom_inv_id_assoc]


-- @@ L723-723 verbatim
end Tachikawa




-- @@ L727-727 verbatim
namespace Tachikawa

-- @@ L728-728 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L729-729 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- @@ L730-730 verbatim
variable {X : C} (P : ProjectiveResolution X) {L : CochainComplex C ℤ}


-- @@ L732-777 verbatim
theorem bounded_cochain_resolution_descends (N : ℕ) (f : P.cochainComplex ⟶ L)
    (hL : ∀ j, j < -(N : ℤ) → IsZero (L.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1))) :
    ∃ g : (CochainComplex.singleFunctor C 0).obj X ⟶ L,
      Nonempty (Homotopy f (P.π' ≫ g)) := by
  obtain ⟨f',hf',H⟩ := cochain_map_supported_nonnegative N f
    (fun j hj => (hL j hj).eq_of_tgt _ _)
    (resolution_HomColumnBoundaries P L hExt)
  let e0 := P.cochainComplexXIso 0 0 rfl
  let e1 := P.cochainComplexXIso (-1) 1 rfl
  have hc : P.cochainComplex.d (-1) 0 ≫ f'.f 0 = 0 := by
    rw [← f'.comm, hf' (-1) (by omega), zero_comp]
  have hc' : P.complex.d 1 0 ≫ e0.inv ≫ f'.f 0 = 0 := by
    have hs := congrArg (fun t => e1.inv ≫ t) hc
    rw [P.cochainComplex_d (-1) 0 1 0 rfl rfl] at hs
    simpa only [e0,e1,Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using hs
  let s : CokernelCofork (P.complex.d 1 0) := CokernelCofork.ofπ (e0.inv ≫ f'.f 0) hc'
  let a : X ⟶ L.X 0 := P.isColimitCokernelCofork.desc s
  have ha : P.π.f 0 ≫ a = e0.inv ≫ f'.f 0 :=
    P.isColimitCokernelCofork.fac s WalkingParallelPair.one
  have hd : P.cochainComplex.d 0 1 = 0 :=
    (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 1).eq_of_tgt _ _
  have hca : ∀ j, (ComplexShape.up ℤ).Rel 0 j → a ≫ L.d 0 j = 0 := by
    intro j hj
    have hj' : j=1 := by change 0+1=j at hj; omega
    rw [hj']
    apply (cancel_epi (P.π.f 0)).1
    erw [← Category.assoc, ha, Category.assoc, f'.comm]
    change e0.inv ≫ P.cochainComplex.d 0 1 ≫ f'.f 1 = P.π.f 0 ≫ 0
    rw [hd,zero_comp,comp_zero,comp_zero]
  let g : (CochainComplex.singleFunctor C 0).obj X ⟶ L := mkHomFromSingle a hca
  have he : P.π' ≫ g = f' := by
    apply HomologicalComplex.Hom.ext
    funext j
    by_cases hj : j=0
    · subst j
      simp only [comp_f, g, mkHomFromSingle_f, P.π'_f_zero, Category.assoc]
      erw [Category.assoc, Iso.inv_hom_id_assoc, ha]
      simp only [e0, Iso.hom_inv_id_assoc]
    · by_cases hneg : j<0
      · rw [comp_f, hf' j hneg]
        have hp : P.π'.f j = 0 :=
          (isZero_single_obj_X (ComplexShape.up ℤ) 0 X j hj).eq_of_tgt _ _
        rw [hp,zero_comp]
      · exact (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 j (by omega)).eq_of_src _ _
  exact ⟨g, he.symm ▸ H⟩


-- @@ L779-779 verbatim
end Tachikawa




-- @@ L783-783 verbatim
namespace Tachikawa

-- @@ L784-784 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L785-785 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]

-- @@ L786-786 verbatim
variable {X : C} (P : ProjectiveResolution X) (L : CochainComplex C ℤ)


-- @@ L788-799 verbatim
theorem bounded_orthogonal_derived_descent (P : ProjectiveResolution X) (N : ℕ)
    (hL : ∀ j, j < -(N : ℤ) → IsZero (L.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1)))
    (a : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
      DerivedCategory.Q.obj L) :
    ∃ g : (CochainComplex.singleFunctor C 0).obj X ⟶ L,
      DerivedCategory.Q.map g = a := by
  obtain ⟨f,hf⟩ := kProjective_chain_representative P.cochainComplex L
    (DerivedCategory.Q.map P.π' ≫ a)
  obtain ⟨g,⟨H⟩⟩ := bounded_cochain_resolution_descends P N f hL hExt
  refine ⟨g, (cancel_epi (DerivedCategory.Q.map P.π')).1 ?_⟩
  rw [← Functor.map_comp, ← DerivedCategory.Q_map_eq_of_homotopy C H, hf]


-- @@ L801-801 verbatim
end Tachikawa




-- @@ L805-805 verbatim
namespace Tachikawa

-- @@ L806-806 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L807-807 verbatim
variable {C : Type*} [Category C] [Abelian C]

-- @@ L808-808 verbatim
variable {K L : CochainComplex C ℤ}


-- @@ L810-814 verbatim
def HomRowBoundaries (K L : CochainComplex C ℤ) : Prop :=
  ∀ (n : ℕ) (a : K.X (n+1 : ℤ) ⟶ L.X (n+1 : ℤ)),
    a ≫ L.d (n+1 : ℤ) (n+2 : ℤ) = 0 →
    ∃ b : K.X (n+1 : ℤ) ⟶ L.X (n : ℤ),
      b ≫ L.d (n : ℤ) (n+1 : ℤ) = a


-- @@ L816-854 verbatim
lemma lower_cochain_map (n : ℕ) (f : K ⟶ L)
    (hf : ∀ j, (n+1 : ℤ) < j → f.f j = 0) (hb : HomRowBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, (n : ℤ) < j → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  classical
  have hc : f.f (n+1 : ℤ) ≫ L.d (n+1 : ℤ) (n+2 : ℤ) = 0 := by
    rw [f.comm, hf _ (by omega), comp_zero]
  obtain ⟨g,hg⟩ := hb n (f.f (n+1 : ℤ)) hc
  let h : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = (n+1 : ℤ) then if hj : j = (n : ℤ) then
      eqToHom (congrArg K.X hi) ≫ g ≫ eqToHom (congrArg L.X hj.symm)
      else 0 else 0
  have hh : ∀ i j, ¬ (ComplexShape.up ℤ).Rel j i → h i j = 0 := by
    intro i j hij
    dsimp only [h]
    split_ifs with hi hj
    · subst i; subst j
      exact False.elim (hij (by rfl))
    all_goals rfl
  let z := Homotopy.nullHomotopicMap h
  have hz (j : ℤ) : z.f j = K.d j (j+1) ≫ h (j+1) j + h j (j-1) ≫ L.d (j-1) j :=
    Homotopy.nullHomotopicMap_f (by change j-1+1=j; omega) rfl h
  refine ⟨f-z, ?_, ?_⟩
  · intro j hj
    change f.f j - z.f j = 0
    rw [hz]
    have h1 : j+1 ≠ (n+1 : ℤ) := by omega
    by_cases h2 : j = (n+1 : ℤ)
    · subst j
      have hi : (n+1 : ℤ)-1= (n : ℤ) := by omega
      rw [hi]
      simp only [h, dite_eq_left rfl, eqToHom_refl, Category.id_comp, Category.comp_id,
        dite_eq_right h1, comp_zero, zero_add, hg, sub_self]
    · simp only [h, dite_eq_right h1, dite_eq_right h2, comp_zero, zero_comp, add_zero,
        hf j (by omega), sub_self]
  · apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have he : f-(f-z)=z := by abel
    rw [he]
    exact Homotopy.nullHomotopy h hh


-- @@ L856-864 verbatim
theorem cochain_map_supported_nonpositive (N : ℕ) (f : K ⟶ L)
    (hf : ∀ j, (N : ℤ) < j → f.f j = 0) (hb : HomRowBoundaries K L) :
    ∃ f' : K ⟶ L, (∀ j, 0 < j → f'.f j = 0) ∧ Nonempty (Homotopy f f') := by
  induction N generalizing f with
  | zero => exact ⟨f,by simpa using hf,⟨Homotopy.refl f⟩⟩
  | succ N ih =>
    obtain ⟨g,hg,⟨H⟩⟩ := lower_cochain_map N f (by simpa using hf) hb
    obtain ⟨f',hf',⟨H'⟩⟩ := ih g hg
    exact ⟨f',hf',⟨H.trans H'⟩⟩


-- @@ L866-866 verbatim
end Tachikawa




-- @@ L870-870 verbatim
namespace Tachikawa

-- @@ L871-871 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L872-872 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- @@ L873-873 verbatim
variable {Y : C} (R : InjectiveResolution Y) (K : CochainComplex C ℤ)


-- @@ L875-901 verbatim
lemma coresolution_HomRowBoundaries
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1))) :
    HomRowBoundaries K R.cochainComplex := by
  intro n a ha
  let e (j : ℕ) := R.cochainComplexXIso (j : ℤ) j rfl
  have he1 : (↑(n+1) : ℤ) = (n+1 : ℤ) := by push_cast; rfl
  have he2 : (↑(n+2) : ℤ) = (n+2 : ℤ) := by push_cast; rfl
  let e1 : R.cochainComplex.X (n+1 : ℤ) ≅ R.cocomplex.X (n+1) :=
    eqToIso (congrArg _ he1.symm) ≪≫ e (n+1)
  let e2 : R.cochainComplex.X (n+2 : ℤ) ≅ R.cocomplex.X (n+2) :=
    eqToIso (congrArg _ he2.symm) ≪≫ e (n+2)
  have hd1 : R.cochainComplex.d (n+1 : ℤ) (n+2 : ℤ) =
      e1.hom ≫ R.cocomplex.d (n+1) (n+2) ≫ e2.inv := by
    simpa [e1,e2,e,he1,he2] using R.cochainComplex_d (n+1 : ℤ) (n+2 : ℤ) (n+1) (n+2) he1 he2
  have hd0 : R.cochainComplex.d (n : ℤ) (n+1 : ℤ) =
      (e n).hom ≫ R.cocomplex.d n (n+1) ≫ e1.inv := by
    simpa [e1,e,he1] using R.cochainComplex_d (n : ℤ) (n+1 : ℤ) n (n+1) rfl he1
  have ha' : (a ≫ e1.hom) ≫ R.cocomplex.d (n+1) (n+2) = 0 := by
    have hs := congrArg (fun t => t ≫ e2.hom) ha
    simpa only [hd1, Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using hs
  let := hExt n
  obtain ⟨b,hb⟩ := (R.extMk_eq_zero_iff (a ≫ e1.hom) (n+2) rfl ha' n rfl).mp
    (Subsingleton.elim _ 0)
  refine ⟨b ≫ (e n).inv, ?_⟩
  rw [hd0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]


-- @@ L903-903 verbatim
end Tachikawa




-- @@ L907-907 verbatim
namespace Tachikawa

-- @@ L908-908 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L909-909 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- @@ L910-910 verbatim
variable {Y : C} (R : InjectiveResolution Y) {K : CochainComplex C ℤ}


-- @@ L912-958 verbatim
theorem bounded_cochain_coresolution_descends (N : ℕ) (f : K ⟶ R.cochainComplex)
    (hK : ∀ j, (N : ℤ) < j → IsZero (K.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1))) :
    ∃ g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y,
      Nonempty (Homotopy f (g ≫ R.ι')) := by
  obtain ⟨f',hf',H⟩ := cochain_map_supported_nonpositive N f
    (fun j hj => (hK j hj).eq_of_src _ _)
    (coresolution_HomRowBoundaries R K hExt)
  let e0 := R.cochainComplexXIso 0 0 rfl
  let e1 := R.cochainComplexXIso 1 1 rfl
  have hc : f'.f 0 ≫ R.cochainComplex.d 0 1 = 0 := by
    rw [f'.comm, hf' 1 (by omega), comp_zero]
  have hc' : (f'.f 0 ≫ e0.hom) ≫ R.cocomplex.d 0 1 = 0 := by
    have hs := congrArg (fun t => t ≫ e1.hom) hc
    rw [R.cochainComplex_d 0 1 0 1 rfl rfl] at hs
    simpa only [e0,e1,Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using hs
  let s : KernelFork (R.cocomplex.d 0 1) := KernelFork.ofι (f'.f 0 ≫ e0.hom) hc'
  let a : K.X 0 ⟶ Y := R.isLimitKernelFork.lift s
  have ha : a ≫ R.ι.f 0 = f'.f 0 ≫ e0.hom :=
    R.isLimitKernelFork.fac s WalkingParallelPair.zero
  have hd : R.cochainComplex.d (-1) 0 = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1)).eq_of_src _ _
  have hca : ∀ j, (ComplexShape.up ℤ).Rel j 0 → K.d j 0 ≫ a = 0 := by
    intro j hj
    have hj' : j = -1 := by change j+1=0 at hj; omega
    rw [hj']
    apply (cancel_mono (R.ι.f 0)).1
    erw [Category.assoc, ha, ← Category.assoc, ← f'.comm]
    change (f'.f (-1) ≫ R.cochainComplex.d (-1) 0) ≫ e0.hom = 0 ≫ R.ι.f 0
    rw [hd,comp_zero,zero_comp,zero_comp]
  let g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y := mkHomToSingle a hca
  have he : g ≫ R.ι' = f' := by
    apply HomologicalComplex.Hom.ext
    funext j
    by_cases hj : j=0
    · subst j
      simp only [comp_f, g, mkHomToSingle_f, R.ι'_f_zero, Category.assoc,
        Iso.inv_hom_id_assoc]
      erw [← Category.assoc, ha]
      simp only [Category.assoc, e0, Iso.hom_inv_id, Category.comp_id]
    · by_cases hpos : 0<j
      · rw [comp_f, hf' j hpos]
        have hp : R.ι'.f j = 0 :=
          (isZero_single_obj_X (ComplexShape.up ℤ) 0 Y j hj).eq_of_src _ _
        rw [hp,comp_zero]
      · exact (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 j (by omega)).eq_of_tgt _ _
  exact ⟨g, he.symm ▸ H⟩


-- @@ L960-960 verbatim
end Tachikawa




-- @@ L964-964 verbatim
namespace Tachikawa

-- @@ L965-965 verbatim
open CategoryTheory HomologicalComplex

-- @@ L966-966 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]


-- @@ L968-980 verbatim
lemma kInjective_chain_representative (K L : CochainComplex C ℤ) [L.IsKInjective]
    (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = a := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨b,hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) L).surjective
      ((e.app K).hom ≫ a ≫ (e.app L).inv)
  obtain ⟨f,rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective b
  refine ⟨f,?_⟩
  have ht := congrArg (fun t => (e.app K).inv ≫ t ≫ (e.app L).hom) hb
  change e.inv.app K ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫ e.hom.app L =
    e.inv.app K ≫ (e.hom.app K ≫ a ≫ e.inv.app L) ≫ e.hom.app L at ht
  simpa [e] using ht


-- @@ L982-982 verbatim
end Tachikawa




-- @@ L986-986 verbatim
namespace Tachikawa

-- @@ L987-987 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L988-988 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]

-- @@ L989-989 verbatim
variable {Y : C} (K : CochainComplex C ℤ)


-- @@ L991-1002 verbatim
theorem bounded_orthogonal_derived_descent_dual (R : InjectiveResolution Y) (N : ℕ)
    (hK : ∀ j, (N : ℤ) < j → IsZero (K.X j))
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1)))
    (a : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y)) :
    ∃ g : K ⟶ (CochainComplex.singleFunctor C 0).obj Y,
      DerivedCategory.Q.map g = a := by
  obtain ⟨f,hf⟩ := kInjective_chain_representative K R.cochainComplex
    (a ≫ DerivedCategory.Q.map R.ι')
  obtain ⟨g,⟨H⟩⟩ := bounded_cochain_coresolution_descends R N f hK hExt
  refine ⟨g, (cancel_mono (DerivedCategory.Q.map R.ι')).1 ?_⟩
  rw [← Functor.map_comp, ← DerivedCategory.Q_map_eq_of_homotopy C H, hf]


-- @@ L1004-1004 verbatim
end Tachikawa




-- @@ L1008-1008 verbatim
namespace Tachikawa

-- @@ L1009-1009 verbatim
open CategoryTheory HomologicalComplex CategoryTheory.Limits

-- @@ L1010-1010 verbatim
variable {C : Type*} [Category C] [Abelian C] [HasExt C] [HasDerivedCategory C]

-- @@ L1011-1011 verbatim
variable {X Y W : C}


-- @@ L1013-1054 verbatim
theorem bounded_ordinary_factorization (P : ProjectiveResolution X)
    (R : InjectiveResolution Y) (L : CochainComplex C ℤ) (l u : ℤ)
    (hbound : ∀ j, j < l ∨ u < j → IsZero (L.X j))
    (hterms : ∀ j, InAdd W (L.X j))
    (hleft : ∀ n : ℕ, Subsingleton (Abelian.Ext X W (n+1)))
    (hright : ∀ n : ℕ, Subsingleton (Abelian.Ext W Y (n+1)))
    (v : X ⟶ Y)
    (α : DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶ DerivedCategory.Q.obj L)
    (β : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y))
    (hv : α ≫ β = DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map v)) :
    ∃ (a : X ⟶ L.X 0) (b : L.X 0 ⟶ Y), a ≫ b = v := by
  obtain ⟨a,ha⟩ := bounded_orthogonal_derived_descent L P l.natAbs
    (fun j hj => hbound j (Or.inl (by have h : -l ≤ ((-l).natAbs : ℤ) := Int.le_natAbs; rw [Int.natAbs_neg] at h; omega)))
    (fun n => by
      let := hleft n
      exact ext_subsingleton_inAdd_right (hterms _) _) α
  obtain ⟨b,hb⟩ := bounded_orthogonal_derived_descent_dual L R u.natAbs
    (fun j hj => hbound j (Or.inr (by have h : u ≤ (u.natAbs : ℤ) := Int.le_natAbs; omega)))
    (fun n => by
      let := hright n
      exact ext_subsingleton_inAdd_left (hterms _) _) β
  let eX := singleObjXSelf (.up ℤ) 0 X
  let eY := singleObjXSelf (.up ℤ) 0 Y
  refine ⟨eX.inv ≫ a.f 0, b.f 0 ≫ eY.hom, ?_⟩
  have hab : DerivedCategory.Q.map (a ≫ b) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map v) := by
    rw [Functor.map_comp,ha,hb,hv]
  let S := CochainComplex.singleFunctor C 0
  let c := S.preimage (a ≫ b)
  have hcmap : S.map c = a ≫ b := S.map_preimage _
  have hc : c = v := by
    apply (DerivedCategory.singleFunctor C 0).map_injective
    change DerivedCategory.Q.map (S.map c) = DerivedCategory.Q.map (S.map v)
    rw [hcmap]
    exact hab
  have he : S.map v = a ≫ b := hc ▸ hcmap
  have he0 := congrArg (fun t => t.f 0) he
  change ((HomologicalComplex.single C (.up ℤ) 0).map v).f 0 = (a ≫ b).f 0 at he0
  rw [single_map_f_self,comp_f] at he0
  have h := congrArg (fun t => eX.inv ≫ t ≫ eY.hom) he0
  simpa only [eX,eY,Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,
    Category.comp_id] using h.symm


-- @@ L1056-1056 verbatim
end Tachikawa


-- @@ L1058-1058 verbatim
end


-- @@ L1060-1060 verbatim
end OAI
