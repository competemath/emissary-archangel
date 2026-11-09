import ModularCurves.ForMathlib.SheafOrderedCechCohomologyFiniteProducts
import ModularCurves.ForMathlib.SheafOrderedCechSheafResolution
import ModularCurves.ForMathlib.SheafCechAcyclicComparison


-- @@ L5-11 verbatim
/-!
# Ordered Cech comparison for acyclic covers

The augmented ordered Cech resolution gives short exact sequences between
successive cycle sheaves. Dimension shifting along these sequences compares
positive sheaf cohomology with exactness of ordered Cech global sections.
-/


-- @@ L13-13 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite


-- @@ L15-15 verbatim
universe u


-- @@ L17-17 verbatim
namespace TopCat.Sheaf


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
variable {X : TopCat.{u}}

-- @@ L22-22 verbatim
variable (F : Sheaf AddCommGrpCat.{u} X)

-- @@ L23-23 verbatim
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)


-- @@ L25-29 verbatim
private noncomputable abbrev orderedCechPositiveShortComplex (n : ℕ) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (orderedCechDifferential F U n)
    (orderedCechDifferential F U (n + 1))
    (orderedCechDifferential_comp F U n)


-- @@ L31-37 verbatim
private noncomputable abbrev orderedCechCycleStepShortComplex (n : ℕ) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  let T := orderedCechPositiveShortComplex F U n
  let T' := orderedCechPositiveShortComplex F U (n + 1)
  ShortComplex.mk T.iCycles T'.toCycles (by
    rw [← cancel_mono T'.iCycles, Category.assoc, T'.toCycles_i, zero_comp]
    exact T.iCycles_g)


-- @@ L39-46 verbatim
private noncomputable abbrev orderedCechInitialCycleShortComplex :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  let T := orderedCechPositiveShortComplex F U 0
  ShortComplex.mk (orderedCechAugmentation F U) T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp]
    rw [orderedCechAugmentation, Category.assoc,
      ← cechToOrderedF_comp_d, ← Category.assoc,
      cechAugmentation_comp, zero_comp])


-- @@ L48-53 verbatim
private noncomputable def cechOrderedZeroIso :
    cechTerm F U 0 ≅ orderedCechTerm F U 0 where
  hom := cechToOrderedF F U 0
  inv := orderedToCechAlternatingF F U 0
  hom_inv_id := cechToOrderedF_comp_orderedToCechAlternatingF_zero F U
  inv_hom_id := orderedToCechAlternatingF_comp_cechToOrderedF F U 0


-- @@ L55-64 verbatim
private theorem orderedCechAugmentation_mono
    (hU : ⨆ i, U i = ⊤) :
    Mono (orderedCechAugmentation F U) := by
  letI : Mono (cechAugmentation F U) :=
    cechAugmentation_mono F U hU
  letI : IsIso (cechToOrderedF F U 0) := by
    change IsIso (cechOrderedZeroIso F U).hom
    infer_instance
  rw [orderedCechAugmentation]
  infer_instance


-- @@ L66-79 verbatim
private theorem orderedCechPositiveShortComplex_exact
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (orderedCechPositiveShortComplex F U n).Exact := by
  have h := orderedCechAugmentedComplex_acyclic F U hU
  rw [HomologicalComplex.acyclic_iff] at h
  have hn := h (n + 2)
  rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3)
    (by simp) (by simp)] at hn
  simpa only [HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor',
    orderedCechAugmentedComplex, CochainComplex.augment,
    CochainComplex.augment_X_succ, CochainComplex.augment_d_succ_succ,
    orderedCechComplex_X, orderedCechComplex_d,
    orderedCechPositiveShortComplex] using hn


-- @@ L81-114 verbatim
private theorem orderedCechAugmentedShortComplex_exact
    (hU : ⨆ i, U i = ⊤) :
    (ShortComplex.mk (orderedCechAugmentation F U)
      (orderedCechDifferential F U 0)
      (by
        rw [orderedCechAugmentation, Category.assoc,
          ← cechToOrderedF_comp_d, ← Category.assoc,
          cechAugmentation_comp, zero_comp])).Exact := by
  have h := orderedCechAugmentedComplex_acyclic F U hU
  rw [HomologicalComplex.acyclic_iff] at h
  have h1 := h 1
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2
    (by simp) (by simp)] at h1
  let S := ShortComplex.mk (orderedCechAugmentation F U)
    (orderedCechDifferential F U 0)
    (by
      rw [orderedCechAugmentation, Category.assoc,
        ← cechToOrderedF_comp_d, ← Category.assoc,
        cechAugmentation_comp, zero_comp])
  let C := (orderedCechAugmentedComplex F U).sc' 0 1 2
  let e : S ≅ C :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom]
        change orderedCechAugmentation F U =
          (orderedCechAugmentedComplex F U).d 0 1
        rfl)
      (by
        simp only [Iso.refl_hom]
        change orderedCechDifferential F U 0 =
          (orderedCechAugmentedComplex F U).d 1 2
        rfl)
  change S.Exact
  exact ShortComplex.exact_of_iso e.symm h1


-- @@ L116-142 verbatim
private theorem orderedCechInitialCycleShortComplex_shortExact
    (hU : ⨆ i, U i = ⊤) :
    (orderedCechInitialCycleShortComplex F U).ShortExact := by
  let T := orderedCechPositiveShortComplex F U 0
  let S := orderedCechInitialCycleShortComplex F U
  let A := ShortComplex.mk (orderedCechAugmentation F U)
    (orderedCechDifferential F U 0)
    (by
      rw [orderedCechAugmentation, Category.assoc,
        ← cechToOrderedF_comp_d, ← Category.assoc,
        cechAugmentation_comp, zero_comp])
  have hA : A.Exact := orderedCechAugmentedShortComplex_exact F U hU
  haveI : Mono S.f := by
    change Mono (orderedCechAugmentation F U)
    exact orderedCechAugmentation_mono F U hU
  haveI : Mono A.f := by
    change Mono (orderedCechAugmentation F U)
    exact orderedCechAugmentation_mono F U hU
  have hker : IsLimit (KernelFork.ofι S.f S.zero) :=
    isKernelOfComp T.iCycles T.f hA.fIsKernel S.zero T.toCycles_i
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hker
  have hT : T.Exact :=
    orderedCechPositiveShortComplex_exact F U hU 0
  haveI : Epi S.g := by
    change Epi T.toCycles
    exact hT.epi_toCycles
  exact { exact := hS }


-- @@ L144-162 verbatim
private theorem orderedCechCycleStepShortComplex_shortExact
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (orderedCechCycleStepShortComplex F U n).ShortExact := by
  let T := orderedCechPositiveShortComplex F U n
  let T' := orderedCechPositiveShortComplex F U (n + 1)
  let S := orderedCechCycleStepShortComplex F U n
  have hT' : T'.Exact :=
    orderedCechPositiveShortComplex_exact F U hU (n + 1)
  haveI : Mono S.f := by
    change Mono T.iCycles
    infer_instance
  have hker : IsLimit (KernelFork.ofι S.f S.zero) :=
    isKernelOfComp T'.iCycles T'.f T.cyclesIsKernel S.zero
      T'.toCycles_i
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hker
  haveI : Epi S.g := by
    change Epi T'.toCycles
    exact hT'.epi_toCycles
  exact { exact := hS }


-- @@ L164-195 verbatim
private theorem orderedCechPositiveCycles_subsingleton_H
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n q : ℕ) (hq : 1 ≤ q)
    (hF : Subsingleton
      (CategoryTheory.Sheaf.H F (q + n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H
      (orderedCechPositiveShortComplex F U n).cycles q) := by
  induction n generalizing q with
  | zero =>
      have hF' : Subsingleton
          (CategoryTheory.Sheaf.H F (q + 1)) := by
        simpa using hF
      simpa [orderedCechInitialCycleShortComplex,
        orderedCechPositiveShortComplex] using
        subsingleton_H_X₃_of_shortExact
          (orderedCechInitialCycleShortComplex_shortExact F U hU) q
          (hterm 0 q hq) hF'
  | succ n ih =>
      have hleft : Subsingleton (CategoryTheory.Sheaf.H
          (orderedCechPositiveShortComplex F U n).cycles
          (q + 1)) := by
        apply ih (q + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hF
      simpa [orderedCechCycleStepShortComplex,
        orderedCechPositiveShortComplex] using
        subsingleton_H_X₃_of_shortExact
          (orderedCechCycleStepShortComplex_shortExact F U hU n) q
          (hterm (n + 1) q hq) hleft


-- @@ L197-257 verbatim
private theorem orderedCechTopSections_exact_succ
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n : ℕ)
    (hF : Subsingleton (CategoryTheory.Sheaf.H F (n + 1)))
    (x : (orderedCechTerm F U (n + 1)).obj.obj (op ⊤))
    (hx : (orderedCechDifferential F U (n + 1)).hom.app
      (op ⊤) x = 0) :
    ∃ y : (orderedCechTerm F U n).obj.obj (op ⊤),
      (orderedCechDifferential F U n).hom.app (op ⊤) y = x := by
  let T := orderedCechPositiveShortComplex F U n
  let K := ShortComplex.mk T.iCycles T.g T.iCycles_g
  have hK : K.Exact :=
    ShortComplex.exact_of_f_is_kernel K T.cyclesIsKernel
  obtain ⟨z, hz⟩ := Sheaf.sections_exact_of_left_exact hK
    (inferInstance : Mono K.f) x hx
  cases n with
  | zero =>
      let S := orderedCechInitialCycleShortComplex F U
      have hS : S.ShortExact :=
        orderedCechInitialCycleShortComplex_shortExact F U hU
      letI : Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
        change Subsingleton (CategoryTheory.Sheaf.H F 1)
        simpa using hF
      obtain ⟨y, hy⟩ :=
        CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
          hS isTerminalTop z
      refine ⟨y, ?_⟩
      calc
        T.f.hom.app (op (⊤ : Opens X)) y =
            (T.toCycles ≫ T.iCycles).hom.app (op ⊤) y := by
              rw [T.toCycles_i]
        _ = T.iCycles.hom.app (op ⊤)
            (T.toCycles.hom.app (op ⊤) y) := rfl
        _ = T.iCycles.hom.app (op ⊤) z := congrArg _ hy
        _ = x := hz
  | succ n =>
      let S := orderedCechCycleStepShortComplex F U n
      have hS : S.ShortExact :=
        orderedCechCycleStepShortComplex_shortExact F U hU n
      letI : Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
        change Subsingleton (CategoryTheory.Sheaf.H
          (orderedCechPositiveShortComplex F U n).cycles 1)
        apply orderedCechPositiveCycles_subsingleton_H
          F U hU hterm n 1 (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hF
      obtain ⟨y, hy⟩ :=
        CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
          hS isTerminalTop z
      refine ⟨y, ?_⟩
      calc
        T.f.hom.app (op (⊤ : Opens X)) y =
            (T.toCycles ≫ T.iCycles).hom.app (op ⊤) y := by
              rw [T.toCycles_i]
        _ = T.iCycles.hom.app (op ⊤)
            (T.toCycles.hom.app (op ⊤) y) := rfl
        _ = T.iCycles.hom.app (op ⊤) z := congrArg _ hy
        _ = x := hz


-- @@ L259-264 verbatim
private abbrev globalSections (X : TopCat.{u}) :
    CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
        AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}


-- @@ L266-270 verbatim
noncomputable local instance orderedAcyclicComparison_globalSections_additive :
    (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).right_adjoint_additive


-- @@ L272-276 verbatim
noncomputable local instance
    orderedAcyclicComparison_globalSections_preservesZeroMorphisms :
    (globalSections X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive
    (F := globalSections X)


-- @@ L278-284 verbatim
private noncomputable def globalSectionsTopIso
    (G : Sheaf AddCommGrpCat.{u} X) :
    (globalSections X).obj (toSiteSheaf G) ≅
      G.obj.obj (op ⊤) :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop).app (toSiteSheaf G)


-- @@ L286-295 verbatim
private theorem globalSectionsTopIso_naturality
    {G H : Sheaf AddCommGrpCat.{u} X} (f : G ⟶ H) :
    (globalSections X).map (show toSiteSheaf G ⟶
        toSiteSheaf H from f) ≫
        (globalSectionsTopIso H).hom =
      (globalSectionsTopIso G).hom ≫
        f.hom.app (op ⊤) :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop).hom.naturality f


-- @@ L297-302 verbatim
private theorem globalSectionsTopIso_hom_inv_apply
    (G : Sheaf AddCommGrpCat.{u} X)
    (x : G.obj.obj (op ⊤)) :
    (globalSectionsTopIso G).hom
        ((globalSectionsTopIso G).inv x) = x :=
  Iso.inv_hom_id_apply (globalSectionsTopIso G) x


-- @@ L304-327 verbatim
private theorem globalSectionsTopIso_map_inv_eq_zero
    {G H : Sheaf AddCommGrpCat.{u} X} (f : G ⟶ H)
    (x : G.obj.obj (op ⊤))
    (hx : f.hom.app (op ⊤) x = 0) :
    (globalSections X).map
        (show toSiteSheaf G ⟶ toSiteSheaf H from f)
        ((globalSectionsTopIso G).inv x) = 0 := by
  apply (AddCommGrpCat.mono_iff_injective
    (globalSectionsTopIso H).hom).mp inferInstance
  calc
    (globalSectionsTopIso H).hom
        ((globalSections X).map
          (show toSiteSheaf G ⟶ toSiteSheaf H from f)
          ((globalSectionsTopIso G).inv x)) =
      f.hom.app (op ⊤)
        ((globalSectionsTopIso G).hom
          ((globalSectionsTopIso G).inv x)) :=
      ConcreteCategory.congr_hom
        (globalSectionsTopIso_naturality f)
        ((globalSectionsTopIso G).inv x)
    _ = 0 := by
      rw [globalSectionsTopIso_hom_inv_apply G x, hx]
    _ = (globalSectionsTopIso H).hom 0 :=
      (globalSectionsTopIso H).hom.hom.map_zero.symm


-- @@ L329-332 verbatim
private abbrev orderedCechSiteDifferential (n : ℕ) :
    toSiteSheaf (orderedCechTerm F U n) ⟶
      toSiteSheaf (orderedCechTerm F U (n + 1)) :=
  orderedCechDifferential F U n


-- @@ L334-348 verbatim
private theorem orderedCechGlobalSections_comp (n : ℕ) :
    (globalSections X).map (orderedCechSiteDifferential F U n) ≫
        (globalSections X).map
          (orderedCechSiteDifferential F U (n + 1)) = 0 := by
  calc
    _ = (globalSections X).map
        (orderedCechSiteDifferential F U n ≫
          orderedCechSiteDifferential F U (n + 1)) :=
      ((globalSections X).map_comp _ _).symm
    _ = (globalSections X).map 0 :=
      congrArg (globalSections X).map
        (orderedCechDifferential_comp F U n)
    _ = 0 := (globalSections X).map_zero
      (toSiteSheaf (orderedCechTerm F U n))
      (toSiteSheaf (orderedCechTerm F U (n + 2)))


-- @@ L350-356 verbatim
private noncomputable abbrev orderedCechGlobalSectionsShortComplex
    (n : ℕ) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    ((globalSections X).map (orderedCechSiteDifferential F U n))
    ((globalSections X).map
      (orderedCechSiteDifferential F U (n + 1)))
    (orderedCechGlobalSections_comp F U n)


-- @@ L358-380 verbatim
private noncomputable def orderedCechGlobalSectionsShortComplexIso
    (n : ℕ) :
    orderedCechGlobalSectionsShortComplex F U n ≅
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).sc' n (n + 1) ((n + 1) + 1) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom]
      change (globalSections X).map
          ((orderedCechComplex F U).d n (n + 1)) =
        (globalSections X).map
          (orderedCechSiteDifferential F U n)
      exact congrArg (globalSections X).map
        (orderedCechComplex_d F U n))
    (by
      simp only [Iso.refl_hom]
      change (globalSections X).map
          ((orderedCechComplex F U).d
            (n + 1) ((n + 1) + 1)) =
        (globalSections X).map
          (orderedCechSiteDifferential F U (n + 1))
      exact congrArg (globalSections X).map
        (orderedCechComplex_d F U (n + 1)))


-- @@ L382-391 verbatim
private theorem orderedCechGlobalSectionsShortComplex_exact_of_exactAt
    (n : ℕ)
    (h :
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).ExactAt (n + 1)) :
    (orderedCechGlobalSectionsShortComplex F U n).Exact := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1)
    ((n + 1) + 1) (by simp) (by simp)] at h
  exact ShortComplex.exact_of_iso
    (orderedCechGlobalSectionsShortComplexIso F U n).symm h


-- @@ L393-495 verbatim
/-- If all positive cohomology of the ordered Cech terms vanishes, vanishing
of `H^(n+1)(F)` implies exactness of ordered Cech global sections in degree
`n+1`. -/
theorem orderedCechGlobalSections_exactAt_succ_of_subsingleton_H
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n : ℕ)
    (hF : Subsingleton (CategoryTheory.Sheaf.H F (n + 1))) :
    (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
      (orderedCechComplex F U)).ExactAt (n + 1) := by
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk
      ((globalSections X).map (orderedCechSiteDifferential F U n))
      ((globalSections X).map
        (orderedCechSiteDifferential F U (n + 1))) (by
        calc
          _ = (globalSections X).map
              (orderedCechSiteDifferential F U n ≫
                orderedCechSiteDifferential F U (n + 1)) :=
            ((globalSections X).map_comp _ _).symm
          _ = (globalSections X).map 0 :=
            congrArg (globalSections X).map
              (orderedCechDifferential_comp F U n)
          _ = 0 := (globalSections X).map_zero
            (toSiteSheaf (orderedCechTerm F U n))
            (toSiteSheaf (orderedCechTerm F U (n + 2))))
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop
    let xTop := eΓ.hom.app
      (toSiteSheaf (orderedCechTerm F U (n + 1))) x
    have hxTop :
        (orderedCechDifferential F U (n + 1)).hom.app
          (op ⊤) xTop = 0 := by
      calc
        _ = eΓ.hom.app
            (toSiteSheaf (orderedCechTerm F U (n + 2)))
            ((globalSections X).map
              (orderedCechSiteDifferential F U (n + 1)) x) :=
          (ConcreteCategory.congr_hom
            (eΓ.hom.naturality
              (orderedCechSiteDifferential F U (n + 1))) x).symm
        _ = 0 := by rw [hx, map_zero]
    obtain ⟨yTop, hyTop⟩ :=
      orderedCechTopSections_exact_succ
        F U hU hterm n hF xTop hxTop
    let y := eΓ.inv.app
      (toSiteSheaf (orderedCechTerm F U n)) yTop
    have hyInv :
        eΓ.hom.app (toSiteSheaf (orderedCechTerm F U n)) y =
          yTop :=
      Iso.inv_hom_id_apply
        (eΓ.app (toSiteSheaf (orderedCechTerm F U n))) yTop
    refine ⟨y, ?_⟩
    change (globalSections X).map
      (orderedCechSiteDifferential F U n) y = x
    apply (AddCommGrpCat.mono_iff_injective
      (eΓ.hom.app
        (toSiteSheaf (orderedCechTerm F U (n + 1))))).mp
          inferInstance
    have hnat :
        eΓ.hom.app
            (toSiteSheaf (orderedCechTerm F U (n + 1)))
            ((globalSections X).map
              (orderedCechSiteDifferential F U n) y) =
          (orderedCechDifferential F U n).hom.app (op ⊤)
            (eΓ.hom.app
              (toSiteSheaf (orderedCechTerm F U n)) y) :=
      ConcreteCategory.congr_hom
        (eΓ.hom.naturality
          (orderedCechSiteDifferential F U n)) y
    refine hnat.trans ?_
    rw [hyInv]
    exact hyTop
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1)
    ((n + 1) + 1) (by simp) (by simp)]
  let C := ((globalSections X).mapHomologicalComplex (.up ℕ)).obj
    (orderedCechComplex F U)
  let e : S ≅ C.sc' n (n + 1) ((n + 1) + 1) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom]
        change (globalSections X).map
            ((orderedCechComplex F U).d n (n + 1)) =
          (globalSections X).map
            (orderedCechSiteDifferential F U n)
        exact congrArg (globalSections X).map
          (orderedCechComplex_d F U n))
      (by
        simp only [Iso.refl_hom]
        change (globalSections X).map
            ((orderedCechComplex F U).d
              (n + 1) ((n + 1) + 1)) =
          (globalSections X).map
            (orderedCechSiteDifferential F U (n + 1))
        exact congrArg (globalSections X).map
          (orderedCechComplex_d F U (n + 1)))
  exact ShortComplex.exact_of_iso e hS


-- @@ L497-517 verbatim
private theorem orderedCechGlobalSections_element_exact_succ
    (n : ℕ)
    (h :
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).ExactAt (n + 1))
    (x :
      (globalSections X).obj
        (toSiteSheaf (orderedCechTerm F U (n + 1))))
    (hx :
      (globalSections X).map
        (orderedCechSiteDifferential F U (n + 1)) x = 0) :
    ∃ y :
        (globalSections X).obj
          (toSiteSheaf (orderedCechTerm F U n)),
      (globalSections X).map
        (orderedCechSiteDifferential F U n) y = x := by
  have hS :=
    orderedCechGlobalSectionsShortComplex_exact_of_exactAt
      F U n h
  rw [ShortComplex.ab_exact_iff] at hS
  exact hS x hx


-- @@ L519-536 verbatim
private theorem orderedCechGlobalCycle_of_topCycle
    (n : ℕ)
    (x : (orderedCechTerm F U (n + 1)).obj.obj (op ⊤))
    (hx : (orderedCechDifferential F U (n + 1)).hom.app
      (op ⊤) x = 0) :
    ∃ xΓ :
        (globalSections X).obj
          (toSiteSheaf (orderedCechTerm F U (n + 1))),
      (globalSections X).map
          (orderedCechSiteDifferential F U (n + 1)) xΓ = 0 ∧
        (globalSectionsTopIso
          (orderedCechTerm F U (n + 1))).hom xΓ = x := by
  refine ⟨(globalSectionsTopIso
    (orderedCechTerm F U (n + 1))).inv x, ?_, ?_⟩
  · exact globalSectionsTopIso_map_inv_eq_zero
      (orderedCechDifferential F U (n + 1)) x hx
  · exact globalSectionsTopIso_hom_inv_apply
      (orderedCechTerm F U (n + 1)) x


-- @@ L538-568 verbatim
private theorem orderedCechTopBoundary_of_globalBoundary
    (n : ℕ)
    (x : (orderedCechTerm F U (n + 1)).obj.obj (op ⊤))
    (xΓ :
      (globalSections X).obj
        (toSiteSheaf (orderedCechTerm F U (n + 1))))
    (hxΓ :
      (globalSectionsTopIso
        (orderedCechTerm F U (n + 1))).hom xΓ = x)
    (yΓ :
      (globalSections X).obj
        (toSiteSheaf (orderedCechTerm F U n)))
    (hyΓ :
      (globalSections X).map
        (orderedCechSiteDifferential F U n) yΓ = xΓ) :
    ∃ y : (orderedCechTerm F U n).obj.obj (op ⊤),
      (orderedCechDifferential F U n).hom.app (op ⊤) y = x := by
  refine ⟨(globalSectionsTopIso
    (orderedCechTerm F U n)).hom yΓ, ?_⟩
  calc
    (orderedCechDifferential F U n).hom.app (op ⊤)
        ((globalSectionsTopIso
          (orderedCechTerm F U n)).hom yΓ) =
      (globalSectionsTopIso
        (orderedCechTerm F U (n + 1))).hom
        ((globalSections X).map
          (orderedCechSiteDifferential F U n) yΓ) :=
      (ConcreteCategory.congr_hom
        (globalSectionsTopIso_naturality
          (orderedCechDifferential F U n)) yΓ).symm
    _ = x := by rw [hyΓ, hxΓ]


-- @@ L570-586 verbatim
private theorem orderedCechTopSections_exact_succ_of_globalSections
    (n : ℕ)
    (h :
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).ExactAt (n + 1))
    (x : (orderedCechTerm F U (n + 1)).obj.obj (op ⊤))
    (hx : (orderedCechDifferential F U (n + 1)).hom.app
      (op ⊤) x = 0) :
    ∃ y : (orderedCechTerm F U n).obj.obj (op ⊤),
      (orderedCechDifferential F U n).hom.app (op ⊤) y = x := by
  obtain ⟨xΓ, hxΓcycle, hxΓ⟩ :=
    orderedCechGlobalCycle_of_topCycle F U n x hx
  obtain ⟨yΓ, hyΓ⟩ :=
    orderedCechGlobalSections_element_exact_succ
      F U n h xΓ hxΓcycle
  exact orderedCechTopBoundary_of_globalBoundary
    F U n x xΓ hxΓ yΓ hyΓ


-- @@ L588-622 verbatim
private theorem orderedCechToCycles_sections_surjective_of_exactAt
    (n : ℕ)
    (h :
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).ExactAt (n + 1)) :
    Function.Surjective
      ((orderedCechPositiveShortComplex F U n).toCycles.hom.app
        (op ⊤)) := by
  let T := orderedCechPositiveShortComplex F U n
  intro z
  have hz :
      T.g.hom.app (op ⊤)
        (T.iCycles.hom.app (op ⊤) z) = 0 := by
    change (T.iCycles ≫ T.g).hom.app (op ⊤) z = 0
    rw [T.iCycles_g]
    rfl
  obtain ⟨y, hy⟩ :=
    orderedCechTopSections_exact_succ_of_globalSections
      F U n h (T.iCycles.hom.app (op ⊤) z) hz
  refine ⟨y, ?_⟩
  haveI : Mono T.iCycles.hom := by
    change Mono
      ((TopCat.Sheaf.forget AddCommGrpCat X).map T.iCycles)
    infer_instance
  haveI : Mono (T.iCycles.hom.app (op ⊤)) := by
    infer_instance
  apply (AddCommGrpCat.mono_iff_injective
    (T.iCycles.hom.app (op ⊤))).mp inferInstance
  calc
    T.iCycles.hom.app (op ⊤)
        (T.toCycles.hom.app (op ⊤) y) =
      (T.toCycles ≫ T.iCycles).hom.app (op ⊤) y := rfl
    _ = T.f.hom.app (op ⊤) y := by
      rw [T.toCycles_i]
    _ = T.iCycles.hom.app (op ⊤) z := hy


-- @@ L624-641 verbatim
private theorem H_map_zero_surjective_of_top_sections_surjective
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)}
    (h :
      Function.Surjective (S.g.hom.app (op ⊤))) :
    Function.Surjective
      (CategoryTheory.Sheaf.H.map S.g 0) := by
  intro x
  obtain ⟨yTop, hyTop⟩ :=
    h (CategoryTheory.Sheaf.H.equiv₀
      (toSiteSheaf S.X₃) isTerminalTop x)
  let y := (CategoryTheory.Sheaf.H.equiv₀
    (toSiteSheaf S.X₂) isTerminalTop).symm yTop
  refine ⟨y, ?_⟩
  apply (CategoryTheory.Sheaf.H.equiv₀
    (toSiteSheaf S.X₃) isTerminalTop).injective
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality
    (f := show toSiteSheaf S.X₂ ⟶ toSiteSheaf S.X₃ from S.g)]
  simp only [y, AddEquiv.apply_symm_apply, hyTop]


-- @@ L643-673 verbatim
private theorem orderedCechCycles_backshift
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n q : ℕ)
    (hcycle : Subsingleton (CategoryTheory.Sheaf.H
      (orderedCechPositiveShortComplex F U n).cycles q)) :
    Subsingleton
      (CategoryTheory.Sheaf.H F (q + n + 1)) := by
  induction n generalizing q with
  | zero =>
      have hF :=
        CategoryTheory.Sheaf.H.subsingleton_H_X₁_succ_of_shortExact
          (orderedCechInitialCycleShortComplex_shortExact F U hU)
          q hcycle (hterm 0 (q + 1) (by omega))
      simpa [orderedCechInitialCycleShortComplex,
        orderedCechPositiveShortComplex] using hF
  | succ n ih =>
      have hprevious : Subsingleton (CategoryTheory.Sheaf.H
          (orderedCechPositiveShortComplex F U n).cycles
          (q + 1)) := by
        simpa [orderedCechCycleStepShortComplex,
          orderedCechPositiveShortComplex] using
          CategoryTheory.Sheaf.H.subsingleton_H_X₁_succ_of_shortExact
              (orderedCechCycleStepShortComplex_shortExact
                F U hU n)
              q hcycle (hterm (n + 1) (q + 1) (by omega))
      have hresult := ih (q + 1) hprevious
      simpa only [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hresult


-- @@ L675-702 verbatim
private theorem orderedCech_H_one_of_globalSections_exactAt_one
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (h :
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).ExactAt 1) :
    Subsingleton (CategoryTheory.Sheaf.H F 1) := by
  let S := orderedCechInitialCycleShortComplex F U
  have hsections :
      Function.Surjective (S.g.hom.app (op ⊤)) := by
    change Function.Surjective
      ((orderedCechPositiveShortComplex F U 0).toCycles.hom.app
        (op ⊤))
    exact orderedCechToCycles_sections_surjective_of_exactAt
      F U 0 h
  have hHZero :
      Function.Surjective
        (CategoryTheory.Sheaf.H.map S.g 0) :=
    H_map_zero_surjective_of_top_sections_surjective hsections
  have hF :=
    CategoryTheory.Sheaf.H.subsingleton_H_X₁_succ_of_shortExact_of_surjective
        (orderedCechInitialCycleShortComplex_shortExact
          F U hU)
        0 hHZero (hterm 0 1 (by omega))
  simpa [S, orderedCechInitialCycleShortComplex,
    orderedCechPositiveShortComplex] using hF


-- @@ L704-737 verbatim
private theorem orderedCech_H_succ_succ_of_globalSections_exactAt
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n : ℕ)
    (h :
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).ExactAt (n + 2)) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 2)) := by
  let S := orderedCechCycleStepShortComplex F U n
  have hsections :
      Function.Surjective (S.g.hom.app (op ⊤)) := by
    change Function.Surjective
      ((orderedCechPositiveShortComplex F U (n + 1)).toCycles.hom.app
        (op ⊤))
    exact orderedCechToCycles_sections_surjective_of_exactAt
      F U (n + 1) h
  have hHZero :
      Function.Surjective
        (CategoryTheory.Sheaf.H.map S.g 0) :=
    H_map_zero_surjective_of_top_sections_surjective hsections
  have hcycle : Subsingleton (CategoryTheory.Sheaf.H
      (orderedCechPositiveShortComplex F U n).cycles 1) := by
    simpa [S, orderedCechCycleStepShortComplex,
      orderedCechPositiveShortComplex] using
      CategoryTheory.Sheaf.H.subsingleton_H_X₁_succ_of_shortExact_of_surjective
          (orderedCechCycleStepShortComplex_shortExact
            F U hU n)
          0 hHZero (hterm (n + 1) 1 (by omega))
  have hF :=
    orderedCechCycles_backshift F U hU hterm n 1 hcycle
  simpa only [Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hF


-- @@ L739-758 verbatim
/-- If all positive cohomology of the ordered Cech terms vanishes, exactness
of ordered Cech global sections in degree `n+1` implies vanishing of
`H^(n+1)(F)`. -/
theorem subsingleton_H_of_orderedCechGlobalSections_exactAt_succ
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n : ℕ)
    (h :
      (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).ExactAt (n + 1)) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  cases n with
  | zero =>
      exact orderedCech_H_one_of_globalSections_exactAt_one
        F U hU hterm h
  | succ n =>
      exact orderedCech_H_succ_succ_of_globalSections_exactAt
        F U hU hterm n h


-- @@ L760-774 verbatim
/-- On an acyclic ordered cover, exactness of ordered Cech global
sections in degree `n+1` is equivalent to vanishing of `H^(n+1)(F)`. -/
theorem orderedCechGlobalSections_exactAt_succ_iff_subsingleton_H
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n : ℕ) :
    ((((globalSections X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex F U)).ExactAt (n + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) :=
  ⟨subsingleton_H_of_orderedCechGlobalSections_exactAt_succ
      F U hU hterm n,
    orderedCechGlobalSections_exactAt_succ_of_subsingleton_H
      F U hU hterm n⟩


-- @@ L776-776 verbatim
end


-- @@ L778-778 verbatim
end TopCat.Sheaf
