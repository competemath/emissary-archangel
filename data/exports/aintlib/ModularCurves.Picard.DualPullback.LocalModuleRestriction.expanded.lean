import ModularCurves.Picard.DualPullback.OverRestriction


-- @@ L3-8 verbatim
/-!
# Restriction of the local pullback module comparison

A staged, option-free proof that `localPullbackModuleIso` is compatible with shrinking
the target open.
-/


-- @@ L10-10 verbatim
open AlgebraicGeometry CategoryTheory Opposite


-- @@ L12-12 verbatim
universe u v


-- @@ L14-14 verbatim
namespace CategoryTheory


-- @@ L16-25 verbatim
theorem comp_two_eq_two_assoc
    {𝒞 : Type u} [Category.{v} 𝒞] {A B C D E F : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D}
    {d : B ⟶ E} {e : E ⟶ D} (h : b ≫ c = d ≫ e) (z : D ⟶ F) :
    a ≫ b ≫ c ≫ z = a ≫ d ≫ e ≫ z := by
  calc
    a ≫ b ≫ c ≫ z = (a ≫ (b ≫ c)) ≫ z := by
      simp only [Category.assoc]
    _ = (a ≫ (d ≫ e)) ≫ z := congrArg (fun k => (a ≫ k) ≫ z) h
    _ = a ≫ d ≫ e ≫ z := by simp only [Category.assoc]


-- @@ L27-35 verbatim
theorem two_eq_two_assoc
    {𝒞 : Type u} [Category.{v} 𝒞] {A B C D E : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : A ⟶ D} {d : D ⟶ C}
    (h : a ≫ b = c ≫ d) (z : C ⟶ E) :
    a ≫ b ≫ z = c ≫ d ≫ z := by
  calc
    a ≫ b ≫ z = (a ≫ b) ≫ z := (Category.assoc _ _ _).symm
    _ = (c ≫ d) ≫ z := congrArg (fun k => k ≫ z) h
    _ = c ≫ d ≫ z := Category.assoc _ _ _


-- @@ L37-46 verbatim
theorem comp_three_eq_two_assoc
    {𝒞 : Type u} [Category.{v} 𝒞] {A B C D E F G : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {d : D ⟶ E}
    {e : B ⟶ F} {q : F ⟶ E} (h : b ≫ c ≫ d = e ≫ q) (z : E ⟶ G) :
    a ≫ b ≫ c ≫ d ≫ z = a ≫ e ≫ q ≫ z := by
  calc
    a ≫ b ≫ c ≫ d ≫ z = (a ≫ (b ≫ c ≫ d)) ≫ z := by
      simp only [Category.assoc]
    _ = (a ≫ (e ≫ q)) ≫ z := congrArg (fun k => (a ≫ k) ≫ z) h
    _ = a ≫ e ≫ q ≫ z := by simp only [Category.assoc]


-- @@ L48-63 verbatim
theorem Iso.inv_comp_eq_comp_inv_of_comp_eq
    {𝒞 : Type u} [Category.{v} 𝒞] {A B C D : 𝒞}
    (e : A ≅ B) (g : C ≅ D) (b : A ⟶ C) (d : B ⟶ D)
    (h : b ≫ g.hom = e.hom ≫ d) :
    e.inv ≫ b = d ≫ g.inv := by
  calc
    e.inv ≫ b = (e.inv ≫ b) ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = (e.inv ≫ b) ≫ (g.hom ≫ g.inv) :=
      congrArg (fun k => (e.inv ≫ b) ≫ k) g.hom_inv_id.symm
    _ = e.inv ≫ (b ≫ g.hom) ≫ g.inv := by simp only [Category.assoc]
    _ = e.inv ≫ (e.hom ≫ d) ≫ g.inv :=
      congrArg (fun k => e.inv ≫ k ≫ g.inv) h
    _ = (e.inv ≫ e.hom) ≫ d ≫ g.inv := by simp only [Category.assoc]
    _ = 𝟙 _ ≫ d ≫ g.inv :=
      congrArg (fun k => k ≫ d ≫ g.inv) e.inv_hom_id
    _ = d ≫ g.inv := by rw [Category.id_comp]


-- @@ L65-65 verbatim
end CategoryTheory


-- @@ L67-67 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L69-69 verbatim
variable {X Y : Scheme.{u}}


-- @@ L71-77 verbatim
theorem localPullbackModuleIso_hom_eqS (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) :
    (localPullbackModuleIso f M U).hom =
      (pullback (f ∣_ U)).map ((overFunctorEquiv U).hom.app M) ≫
        (localPullbackRestrictIso f M U).hom ≫
        (overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj M) := by
  rfl


-- @@ L79-81 verbatim
noncomputable def moduleNatRestrictMapS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (f ∣_ V)).map (overRestrictModuleIso M i).hom


-- @@ L83-85 verbatim
noncomputable def moduleNatOpenOverS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (openPullbackRestrictIso f i).hom.app ((overEquiv U).functor.obj (M.over U))


-- @@ L87-90 verbatim
noncomputable def moduleNatPullAfterS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (restrictFunctor (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
    ((pullback (f ∣_ U)).map ((overFunctorEquiv U).hom.app M))


-- @@ L92-96 verbatim
noncomputable def moduleNatPullBeforeS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (f ∣_ V)).map
    ((restrictFunctor (X.homOfLE (leOfHom i))).map
      ((overFunctorEquiv U).hom.app M))


-- @@ L98-100 verbatim
noncomputable def moduleNatOpenRestrictS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (openPullbackRestrictIso f i).hom.app ((restrictFunctor U.ι).obj M)


-- @@ L102-105 verbatim
noncomputable def moduleNatRestrictBUS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (restrictFunctor (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
    (localPullbackRestrictIso f M U).hom


-- @@ L107-110 verbatim
noncomputable def moduleNatRestrictEYUS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (restrictFunctor (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
    ((overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj M))


-- @@ L112-114 verbatim
noncomputable def moduleNatPullEXVS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (_i : V ⟶ U) :=
  (pullback (f ∣_ V)).map ((overFunctorEquiv V).hom.app M)


-- @@ L116-118 verbatim
noncomputable def moduleNatPullCXS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (f ∣_ V)).map ((restrictOpenCompIso i).hom.app M)


-- @@ L120-122 verbatim
noncomputable def moduleNatBVS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (_i : V ⟶ U) :=
  (localPullbackRestrictIso f M V).hom


-- @@ L124-127 verbatim
noncomputable def moduleNatCYS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (restrictOpenCompIso ((TopologicalSpace.Opens.map f.base).map i)).hom.app
    ((pullback f).obj M)


-- @@ L129-131 verbatim
noncomputable def moduleNatEYVS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (_i : V ⟶ U) :=
  (overFunctorEquiv (f ⁻¹ᵁ V)).inv.app ((pullback f).obj M)


-- @@ L133-136 verbatim
noncomputable def moduleNatRYS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (overRestrictModuleIso ((pullback f).obj M)
    ((TopologicalSpace.Opens.map f.base).map i)).hom


-- @@ L138-140 verbatim
noncomputable def moduleNatTailUS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  moduleNatRestrictBUS f M i ≫ moduleNatRestrictEYUS f M i


-- @@ L142-147 verbatim
theorem moduleNat_open_naturalityS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatOpenOverS f M i ≫ moduleNatPullAfterS f M i =
      moduleNatPullBeforeS f M i ≫ moduleNatOpenRestrictS f M i := by
  exact (openPullbackRestrictIso f i).hom.naturality
    ((overFunctorEquiv U).hom.app M) |>.symm


-- @@ L149-160 verbatim
theorem moduleNat_over_pullbackS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatRestrictMapS f M i ≫ moduleNatPullBeforeS f M i =
      moduleNatPullEXVS f M i ≫ moduleNatPullCXS f M i := by
  let P := pullback (f ∣_ V)
  change P.map (overRestrictModuleIso M i).hom ≫
      P.map ((restrictFunctor (X.homOfLE (leOfHom i))).map
        ((overFunctorEquiv U).hom.app M)) =
    P.map ((overFunctorEquiv V).hom.app M) ≫
      P.map ((restrictOpenCompIso i).hom.app M)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg P.map (overRestrictModuleIso_comp_overFunctorEquiv M i)


-- @@ L162-167 verbatim
theorem moduleNat_local_pullbackS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatPullCXS f M i ≫ moduleNatOpenRestrictS f M i ≫
        moduleNatRestrictBUS f M i =
      moduleNatBVS f M i ≫ moduleNatCYS f M i :=
  localPullbackRestrictIso_naturality f M i


-- @@ L169-174 verbatim
theorem moduleNat_over_sourceS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatCYS f M i ≫ moduleNatRestrictEYUS f M i =
      moduleNatEYVS f M i ≫ moduleNatRYS f M i :=
  (overRestrictionComparison_inv ((pullback f).obj M)
    ((TopologicalSpace.Opens.map f.base).map i)).symm


-- @@ L176-179 verbatim
noncomputable def moduleNatStage0S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  moduleNatRestrictMapS f M i ≫ moduleNatOpenOverS f M i ≫
    moduleNatPullAfterS f M i ≫ moduleNatTailUS f M i


-- @@ L181-184 verbatim
noncomputable def moduleNatStage1S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  moduleNatRestrictMapS f M i ≫ moduleNatPullBeforeS f M i ≫
    moduleNatOpenRestrictS f M i ≫ moduleNatTailUS f M i


-- @@ L186-190 verbatim
theorem moduleNat_stage0_eq_stage1S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatStage0S f M i = moduleNatStage1S f M i :=
  comp_two_eq_two_assoc (moduleNat_open_naturalityS f M i)
    (moduleNatTailUS f M i)


-- @@ L192-195 verbatim
noncomputable def moduleNatStage2S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  moduleNatPullEXVS f M i ≫ moduleNatPullCXS f M i ≫
    moduleNatOpenRestrictS f M i ≫ moduleNatTailUS f M i


-- @@ L197-201 verbatim
theorem moduleNat_stage1_eq_stage2S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatStage1S f M i = moduleNatStage2S f M i :=
  two_eq_two_assoc (moduleNat_over_pullbackS f M i)
    (moduleNatOpenRestrictS f M i ≫ moduleNatTailUS f M i)


-- @@ L203-206 verbatim
noncomputable def moduleNatStage3S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  moduleNatPullEXVS f M i ≫ moduleNatBVS f M i ≫
    moduleNatCYS f M i ≫ moduleNatRestrictEYUS f M i


-- @@ L208-215 verbatim
theorem moduleNat_stage2_eq_stage3S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatStage2S f M i = moduleNatStage3S f M i := by
  change moduleNatPullEXVS f M i ≫ moduleNatPullCXS f M i ≫
      moduleNatOpenRestrictS f M i ≫ moduleNatRestrictBUS f M i ≫
        moduleNatRestrictEYUS f M i = _
  exact comp_three_eq_two_assoc (moduleNat_local_pullbackS f M i)
    (moduleNatRestrictEYUS f M i)


-- @@ L217-220 verbatim
noncomputable def moduleNatStage4S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  moduleNatPullEXVS f M i ≫ moduleNatBVS f M i ≫
    moduleNatEYVS f M i ≫ moduleNatRYS f M i


-- @@ L222-227 verbatim
theorem moduleNat_stage3_eq_stage4S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatStage3S f M i = moduleNatStage4S f M i :=
  congrArg
    (fun k => moduleNatPullEXVS f M i ≫ moduleNatBVS f M i ≫ k)
    (moduleNat_over_sourceS f M i)


-- @@ L229-247 verbatim
theorem moduleNat_map_localIsoS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    (restrictFunctor
      (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
        (localPullbackModuleIso f M U).hom =
      moduleNatPullAfterS f M i ≫ moduleNatRestrictBUS f M i ≫
        moduleNatRestrictEYUS f M i := by
  let R := restrictFunctor (Y.homOfLE (f.preimage_mono (leOfHom i)))
  let a := (pullback (f ∣_ U)).map ((overFunctorEquiv U).hom.app M)
  let b := (localPullbackRestrictIso f M U).hom
  let c := (overFunctorEquiv (f ⁻¹ᵁ U)).inv.app ((pullback f).obj M)
  have hlocal := congrArg R.map (localPullbackModuleIso_hom_eqS f M U)
  have hmap : R.map (a ≫ b ≫ c) = R.map a ≫ R.map b ≫ R.map c := by
    calc
      R.map (a ≫ b ≫ c) = R.map a ≫ R.map (b ≫ c) :=
        R.map_comp a (b ≫ c)
      _ = R.map a ≫ (R.map b ≫ R.map c) :=
        congrArg (fun k => R.map a ≫ k) (R.map_comp b c)
  exact hlocal.trans hmap


-- @@ L249-261 verbatim
theorem moduleNat_left_eq_stage0S (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    ((pullback (f ∣_ V)).map (overRestrictModuleIso M i).hom ≫
        (openPullbackRestrictIso f i).hom.app
          ((overEquiv U).functor.obj (M.over U))) ≫
      (restrictFunctor
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
          (localPullbackModuleIso f M U).hom = moduleNatStage0S f M i := by
  rw [moduleNat_map_localIsoS]
  change (moduleNatRestrictMapS f M i ≫ moduleNatOpenOverS f M i) ≫
      (moduleNatPullAfterS f M i ≫ moduleNatRestrictBUS f M i ≫
        moduleNatRestrictEYUS f M i) = moduleNatStage0S f M i
  simp only [moduleNatStage0S, moduleNatTailUS, Category.assoc]


-- @@ L263-270 verbatim
theorem moduleNat_stage4_eq_rightS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    moduleNatStage4S f M i =
      (localPullbackModuleIso f M V).hom ≫
        (overRestrictModuleIso ((pullback f).obj M)
          ((TopologicalSpace.Opens.map f.base).map i)).hom := by
  rw [localPullbackModuleIso_hom_eqS]
  rfl


-- @@ L272-288 verbatim
theorem localPullbackModuleIso_restrict_homS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    ((pullback (f ∣_ V)).map (overRestrictModuleIso M i).hom ≫
        (openPullbackRestrictIso f i).hom.app
          ((overEquiv U).functor.obj (M.over U))) ≫
      (restrictFunctor
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
          (localPullbackModuleIso f M U).hom =
    (localPullbackModuleIso f M V).hom ≫
      (overRestrictModuleIso ((pullback f).obj M)
        ((TopologicalSpace.Opens.map f.base).map i)).hom := by
  exact (moduleNat_left_eq_stage0S f M i).trans
    ((moduleNat_stage0_eq_stage1S f M i).trans
      ((moduleNat_stage1_eq_stage2S f M i).trans
        ((moduleNat_stage2_eq_stage3S f M i).trans
          ((moduleNat_stage3_eq_stage4S f M i).trans
            (moduleNat_stage4_eq_rightS f M i)))))


-- @@ L290-311 verbatim
theorem localPullbackModuleIso_restrictS (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    (localPullbackModuleIso f M V).inv ≫
        (pullback (f ∣_ V)).map (overRestrictModuleIso M i).hom ≫
        (openPullbackRestrictIso f i).hom.app
          ((overEquiv U).functor.obj (M.over U)) =
      (overRestrictModuleIso ((pullback f).obj M)
          ((TopologicalSpace.Opens.map f.base).map i)).hom ≫
        (restrictFunctor
          (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
            (localPullbackModuleIso f M U).inv := by
  let R := restrictFunctor (Y.homOfLE (f.preimage_mono (leOfHom i)))
  let eV := localPullbackModuleIso f M V
  let eU := R.mapIso (localPullbackModuleIso f M U)
  let b := (pullback (f ∣_ V)).map (overRestrictModuleIso M i).hom ≫
    (openPullbackRestrictIso f i).hom.app
      ((overEquiv U).functor.obj (M.over U))
  let d := (overRestrictModuleIso ((pullback f).obj M)
    ((TopologicalSpace.Opens.map f.base).map i)).hom
  have h : b ≫ eU.hom = eV.hom ≫ d :=
    localPullbackModuleIso_restrict_homS f M i
  exact Iso.inv_comp_eq_comp_inv_of_comp_eq eV eU b d h


-- @@ L313-313 verbatim
end AlgebraicGeometry.Scheme.Modules
