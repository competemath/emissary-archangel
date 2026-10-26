/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.RelativeRiemannRoch.KahlerRingTransportH2


-- @@ L9-28 verbatim
/-!
# Actual affine native Kähler pullback and conormal exactness for H2

The original standard-smooth presentation gives quasicoherence of the actual
native relative sheaf on Spec. The genuine QC counit and original-ring Kähler
Iso give its native sheaf Iso, retaining the original unit and D/Esec formulas.
The actual pullback tensor Iso preserves unit differential generators. The
unchanged TF3.c is exactly the original Extension cotangent differential under
these constructed source and target normalizations.

The original library conormal comparison and this actual native differential
form a short exact complex on affine global sections. Both closed immersions
are constructed from the single original surjection R → B in the wrapper API.
Only the ambient A/R is standard smooth. No base or quotient smoothness,
quotient regularity, reducedness or flatness is assumed. Desired comparison
squares and bijective units are conclusions, never input hypotheses.

Compatible closed-chart transport, global sheaf short exactness and actual
virtual cotangent cancellation remain subsequent H2 gates.
-/


-- @@ L30-30 verbatim
set_option autoImplicit false

-- @@ L31-31 verbatim
noncomputable section

-- @@ L32-32 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

-- @@ L33-33 verbatim
open Algebra Algebra.Extension

-- @@ L34-34 verbatim
open SchemeKTheory.Cotangent SchemeKTheory.KahlerRingTransportH2

-- @@ L35-35 verbatim
open SchemeKTheory.ConormalTensorH2 SchemeKTheory.KoszulComplexSheaf

-- @@ L36-36 verbatim
open scoped TensorProduct ChangeOfRings

-- @@ L37-37 verbatim
universe u

-- @@ L38-38 verbatim
namespace SchemeKTheory.NativeKahlerPullbackH2


-- @@ L40-46 verbatim
/-- The original adjunction unit followed by the mapped mate recovers its section map. -/
theorem unit_map_mate {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {N : C} {M : D} (f : N ⟶ G.obj M) :
    adj.unit.app N ≫ G.map (F.map f ≫ adj.counit.app M) = f := by
  have h := (adj.homEquiv N M).apply_symm_apply f
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at h
  exact h


-- @@ L48-51 verbatim
/-- Actual affine functor maps evaluate through the unchanged native section morphism. -/
theorem affineSections_map_apply {A : CommRingCat.{u}} {M N : (Spec A).Modules}
    (f : M ⟶ N) (x : (affineGlobalSectionsFunctor A).obj M) :
    (affineGlobalSectionsFunctor A).map f x = f.app ⊤ x := rfl


-- @@ L53-71 verbatim
/-- The actual standard-smooth affine ambient has a quasicoherent native relative sheaf,
by its actual submersive Gamma-ring presentation and original relative local frames. -/
theorem specRelativeSheaf_isQuasicoherent {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hsm : RingHom.IsStandardSmooth φ.hom) :
    (relativeSheaf (Spec.map φ)).IsQuasicoherent := by
  letI := (gammaRingHom φ).hom.toAlgebra
  letI : Algebra.IsStandardSmooth Γ(Spec R, ⊤) Γ(Spec A, ⊤) :=
    gammaRingHom_isStandardSmooth φ hsm
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ :=
    Algebra.IsStandardSmooth.out (R := Γ(Spec R, ⊤)) (S := Γ(Spec A, ⊤))
  letI : Finite σ := hσ
  letI : Finite ι := hι
  let n := P.dimension
  letI : SmoothOfRelativeDimension n (Spec.map φ) := ⟨fun _ =>
    ⟨⊤, isAffineOpen_top _, ⊤, isAffineOpen_top _, by trivial, le_top,
      P.isStandardSmoothOfRelativeDimension rfl⟩⟩
  letI : (relativeSheaf (Spec.map φ)).IsFinitePresentation :=
    (relativeSheaf_isFiniteLocallyFree (Spec.map φ) n).isFinitePresentation
  infer_instance


-- @@ L73-83 verbatim
/-- The actual native affine relative sheaf is the tilde of original ring differentials,
through the genuine QC counit and independently constructed original section Iso. -/
def specRelativeSheafIsoTilde {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hsm : RingHom.IsStandardSmooth φ.hom) :
    relativeSheaf (Spec.map φ) ≅ tilde (CommRingCat.KaehlerDifferential φ) := by
  let M := relativeSheaf (Spec.map φ)
  letI : M.IsQuasicoherent := specRelativeSheaf_isQuasicoherent φ hsm
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := A) M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact (asIso (Scheme.Modules.fromTildeΓ (R := A) M)).symm ≪≫
    (tilde.functor A).mapIso (affineDifferentialIsoOfStandardSmooth φ hsm).symm



-- @@ L86-101 verbatim
/-- The constructed native sheaf Iso preserves the original tilde adjunction unit on sections. -/
theorem specRelativeSheafIsoTilde_unit {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hsm : RingHom.IsStandardSmooth φ.hom) :
    (tilde.isoTop (R := A) (CommRingCat.KaehlerDifferential φ)).hom ≫
      (moduleSpecΓFunctor (R := A)).map (specRelativeSheafIsoTilde φ hsm).inv =
    (affineDifferentialIsoOfStandardSmooth φ hsm).hom := by
  let adj := tilde.adjunction (R := A)
  let M := relativeSheaf (Spec.map φ)
  let e := affineDifferentialIsoOfStandardSmooth φ hsm
  letI : M.IsQuasicoherent := specRelativeSheaf_isQuasicoherent φ hsm
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := A) M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  change adj.unit.app (CommRingCat.KaehlerDifferential φ) ≫
    (moduleSpecΓFunctor (R := A)).map
      ((tilde.functor A).map e.hom ≫ adj.counit.app M) = e.hom
  exact unit_map_mate adj e.hom


-- @@ L103-112 verbatim
/-- Original tilde differential generators become the unchanged native sheaf derivation. -/
theorem specRelativeSheafIsoTilde_inv_d {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hsm : RingHom.IsStandardSmooth φ.hom) (a : A) :
    (specRelativeSheafIsoTilde φ hsm).inv.app ⊤
      ((tilde.isoTop (R := A) (CommRingCat.KaehlerDifferential φ)).hom
        (CommRingCat.KaehlerDifferential.d (f := φ) a)) =
      TF2.Esec (Spec.map φ) ⊤ ((Scheme.ΓSpecIso A).inv a) :=
  (ConcreteCategory.congr_hom (specRelativeSheafIsoTilde_unit φ hsm)
    (CommRingCat.KaehlerDifferential.d (f := φ) a)).trans
      (affineDifferentialIsoOfStandardSmooth_d φ hsm a)


-- @@ L114-119 verbatim
/-- The inverse original tensor-dictionary normalization preserves actual tensor generators. -/
theorem algebraTensorIso_inv_tmul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat A) (b : B) (m : M) :
    (algebraTensorIso (B := B) M).inv (b ⊗ₜ[A] m) = b ⊗ₜ[A,algebraMap A B] m :=
  (congrArg (algebraTensorIso (B := B) M).inv (algebraTensorIso_apply M b m).symm).trans
    (ConcreteCategory.congr_hom (algebraTensorIso (B := B) M).hom_inv_id _)


-- @@ L121-121 verbatim
section Algebra

-- @@ L122-123 verbatim
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra.IsStandardSmooth R A]


-- @@ L125-129 verbatim
/-- Actual original-algebra relative sheaf QC, without smoothness of base or quotient. -/
theorem algebraRelativeSheaf_isQuasicoherent :
    (relativeSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A)))).IsQuasicoherent :=
  specRelativeSheaf_isQuasicoherent (CommRingCat.ofHom (algebraMap R A))
    (RingHom.isStandardSmooth_algebraMap.mpr inferInstance)


-- @@ L131-143 verbatim
/-- The actual tensor target Iso transports original algebra Omega to genuine native
pulled relative sheaf sections, retaining both original algebra dictionaries. -/
def pulledOmegaSectionsIso : ModuleCat.of B (B ⊗[A] Ω[A⁄R]) ≅
    (affineGlobalSectionsFunctor (.of B)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (relativeSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A))))) := by
  letI : (relativeSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A)))).IsQuasicoherent :=
    algebraRelativeSheaf_isQuasicoherent (R := R) (A := A)
  exact (algebraTensorIso (B := B) (ModuleCat.of A Ω[A⁄R])).symm ≪≫
    (ModuleCat.extendScalars (algebraMap A B)).mapIso
      (algebraAffineDifferentialIsoOfStandardSmooth (R := R) (A := A)) ≪≫
        cosectionSpecNativeTensorIso (algebraMap A B)
          (relativeSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A))))


-- @@ L145-170 verbatim
/-- The actual pullback target Iso retains the original native unit on differential generators. -/
theorem pulledOmegaSectionsIso_one_tmul_D (a : A) :
    (pulledOmegaSectionsIso (R := R) (A := A) (B := B)).hom
      ((1 : B) ⊗ₜ[A] KaehlerDifferential.D R A a) =
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).unit.app
        (relativeSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A))))).app ⊤
      (TF2.Esec (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⊤
        ((Scheme.ΓSpecIso (.of A)).inv a)) := by
  let M := relativeSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  letI : M.IsQuasicoherent := algebraRelativeSheaf_isQuasicoherent (R := R) (A := A)
  let e := algebraAffineDifferentialIsoOfStandardSmooth (R := R) (A := A)
  let t := (ModuleCat.extendScalars (algebraMap A B)).map e.hom
  change cosectionSpecNativeTensorMap (algebraMap A B) M
    (t ((algebraTensorIso (B := B) (ModuleCat.of A Ω[A⁄R])).inv
      ((1 : B) ⊗ₜ[A] KaehlerDifferential.D R A a))) = _
  have h₁ := algebraTensorIso_inv_tmul (B := B) (ModuleCat.of A Ω[A⁄R])
    1 (KaehlerDifferential.D R A a)
  have h₂ := ModuleCat.ExtendScalars.map_tmul (algebraMap A B) e.hom
    1 (KaehlerDifferential.D R A a)
  have h₃ := algebraAffineDifferentialIsoOfStandardSmooth_D (R := R) (A := A) a
  exact (congrArg (fun z => cosectionSpecNativeTensorMap (algebraMap A B) M (t z)) h₁).trans
    ((congrArg (cosectionSpecNativeTensorMap (algebraMap A B) M) h₂).trans
      ((congrArg (fun z => cosectionSpecNativeTensorMap (algebraMap A B) M
        ((1 : B) ⊗ₜ[A,algebraMap A B] z)) h₃).trans
          (nativeTensorMap_one_tmul (algebraMap A B) M _)))


-- @@ L172-172 verbatim
end Algebra

-- @@ L173-173 verbatim
section Extension

-- @@ L174-175 verbatim
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (P : Extension.{u} R B) [Algebra.IsStandardSmooth R P.Ring]

-- @@ L176-176 verbatim
open ConormalNativeDifferentialH2


-- @@ L178-180 verbatim
local instance extensionQuotientSpecClosed : IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap P.Ring B))) :=
  IsClosedImmersion.spec_of_surjective _ P.algebraMap_surjective


-- @@ L182-192 verbatim
omit [Algebra.IsStandardSmooth R P.Ring] in
/-- The original library source Iso evaluates through the unchanged conormal normalization. -/
theorem libraryCotangentSectionsIso_hom_apply
    (x : (affineGlobalSectionsFunctor (.of B)).obj
      (AlgebraicGeometry.Chow.M7.CIICLASS.T1N23.libConormalAmb
        (Spec.map (CommRingCat.ofHom (algebraMap P.Ring B))))) :
    (libraryCotangentSectionsIso P).hom x =
      (pulledIdealCotangentSectionsIso P).hom
        ((affineGlobalSectionsFunctor (.of B)).map
          (TF3.conormalIso (Spec.map (CommRingCat.ofHom (algebraMap P.Ring B)))).hom x) :=
  ConcreteCategory.comp_apply _ _ x


-- @@ L194-208 verbatim
/-- Every actual extension quotient class identifies the native differential with the genuine
original Extension differential, through the constructed native pullback target Iso. -/
theorem cotangentDifferentialSections_eq_extension :
    cotangentDifferentialSections P (Spec.map (CommRingCat.ofHom (algebraMap R P.Ring))) =
      ModuleCat.ofHom P.cotangentComplex ≫
        (pulledOmegaSectionsIso (R := R) (A := P.Ring) (B := B)).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective y
  exact (cotangentDifferentialSections_mk P
    (Spec.map (CommRingCat.ofHom (algebraMap R P.Ring))) x).trans
      ((pulledOmegaSectionsIso_one_tmul_D (R := R) (A := P.Ring) (B := B) x.val).symm.trans
        (congrArg (pulledOmegaSectionsIso (R := R) (A := P.Ring) (B := B)).hom
          (P.cotangentComplex_mk x)).symm)


-- @@ L210-218 verbatim
/-- The unchanged actual TF3.c has both original affine source and native tensor target
normalizations, and is exactly the genuine Extension differential between them. -/
theorem originalConormalDifferential_extension_square :
    (affineGlobalSectionsFunctor (.of B)).map
      (TF3.c (Spec.map (CommRingCat.ofHom (algebraMap R P.Ring)))
        (Spec.map (CommRingCat.ofHom (algebraMap P.Ring B)))) =
    (libraryCotangentSectionsIso P).hom ≫ ModuleCat.ofHom P.cotangentComplex ≫
      (pulledOmegaSectionsIso (R := R) (A := P.Ring) (B := B)).hom := by
  rw [originalConormalDifferential_square, cotangentDifferentialSections_eq_extension]


-- @@ L220-220 verbatim
end Extension

-- @@ L221-225 verbatim
/-- Cancellation of a constructed target Iso preserves an original differential square. -/
theorem isoTarget_cancel {C : Type*} [Category C] {A B D : C}
    (e : B ≅ D) (f : A ⟶ B) (g : A ⟶ D) (h : f = g ≫ e.inv) :
    f ≫ e.hom = g := by
  rw [h, Category.assoc, e.inv_hom_id, Category.comp_id]


-- @@ L227-246 verbatim
/-- Exactness transports through an actual surjective source normalization and
injective middle and target normalizations with both pointwise squares proved. -/
theorem functionExact_transport {X Y Z X' Y' Z' : Type*} [Zero Z] [Zero Z']
    (f : X → Y) (g : Y → Z) (f' : X' → Y') (g' : Y' → Z')
    (a : X → X') (b : Y → Y') (c : Z → Z')
    (ha : Function.Surjective a) (hb : Function.Injective b) (hc : Function.Injective c)
    (hc0 : c 0 = 0) (hf : ∀ x, b (f x) = f' (a x))
    (hg : ∀ y, c (g y) = g' (b y)) (he : Function.Exact f' g') :
    Function.Exact f g := by
  intro y
  constructor
  · intro hy
    have hy' : g' (b y) = 0 := (hg y).symm.trans ((congrArg c hy).trans hc0)
    obtain ⟨x', hx'⟩ := (he (b y)).mp hy'
    obtain ⟨x, hx⟩ := ha x'
    exact ⟨x, hb ((hf x).trans ((congrArg f' hx).trans hx'))⟩
  · rintro ⟨x, rfl⟩
    apply hc
    exact (hg (f x)).trans ((congrArg g' (hf x)).trans
      (((he (f' (a x))).mpr ⟨a x, rfl⟩).trans hc0.symm))


-- @@ L248-257 verbatim
/-- Surjectivity transports through actual surjective middle and bijective target maps. -/
theorem functionSurjective_transport {Y Z Y' Z' : Type*}
    (g : Y → Z) (g' : Y' → Z') (b : Y → Y') (c : Z → Z')
    (hb : Function.Surjective b) (hc : Function.Bijective c)
    (hg : ∀ y, c (g y) = g' (b y)) (hs : Function.Surjective g') :
    Function.Surjective g := by
  intro z
  obtain ⟨y', hy'⟩ := hs (c z)
  obtain ⟨y, hy⟩ := hb y'
  exact ⟨y, hc.injective ((hg y).trans ((congrArg g' hy).trans hy'))⟩


-- @@ L259-259 verbatim
section Tower

-- @@ L260-262 verbatim
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra.IsStandardSmooth R A] [hquot : Fact (Function.Surjective (algebraMap R B))]

-- @@ L263-263 verbatim
open ConormalComparisonH2 ConormalComparisonSheafH2 ConormalNativeMapH2

-- @@ L264-264 verbatim
open ConormalNativeDifferentialH2

-- @@ L265-265 verbatim
local notation "hf" => hquot.out

-- @@ L266-266 verbatim
local notation "j" => Spec.map (CommRingCat.ofHom (algebraMap A B))

-- @@ L267-267 verbatim
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap R A))


-- @@ L269-269 verbatim
variable [hamb : Fact (Function.Surjective (algebraMap A B))]


-- @@ L271-272 verbatim
attribute [local instance] ConormalNativeMapH2.baseSpecClosed
  ConormalNativeMapH2.ambientSpecClosed ConormalNativeMapH2.compositeSpecClosed


-- @@ L274-280 verbatim
/-- The actual composite library conormal sections normalize to the original base quotient. -/
def nativeSourceSectionsIso :
    (affineGlobalSectionsFunctor (.of B)).obj
      (AlgebraicGeometry.Chow.M7.CIICLASS.T1N23.libConormalAmb (j ≫ p)) ≅
    ModuleCat.of B (baseExtension hf).Cotangent :=
  (affineGlobalSectionsFunctor (.of B)).mapIso (TF3.conormalIso (j ≫ p)) ≪≫
    sourcePulledSectionsIso (R := R) (A := A) (B := B)


-- @@ L282-291 verbatim
/-- The actual composite source normalization on native sections, without expanding
an entire composed Iso in a kernel conversion. -/
def nativeSourceNormalizer :
    (affineGlobalSectionsFunctor (.of B)).obj
      (AlgebraicGeometry.Chow.M7.CIICLASS.T1N23.libConormalAmb (j ≫ p)) →
      (baseExtension hf).Cotangent := fun x =>
  (pulledIdealCotangentSectionsIso (baseExtension hf)).hom
    ((affineGlobalSectionsFunctor (.of B)).map
      (pulledIdealCongr (specTower_comp (R := R) (A := A) (B := B))).hom
      ((affineGlobalSectionsFunctor (.of B)).map (TF3.conormalIso (j ≫ p)).hom x))


-- @@ L293-303 verbatim
omit [Algebra.IsStandardSmooth R A] hamb in
/-- Every base class has a preimage under the actual boxed native normalization. -/
theorem nativeSourceNormalizer_surjective :
    Function.Surjective (nativeSourceNormalizer (R := R) (A := A) (B := B)) :=
  (ConcreteCategory.bijective_of_isIso
    (pulledIdealCotangentSectionsIso (baseExtension hf)).hom).surjective.comp
    ((ConcreteCategory.bijective_of_isIso
      ((affineGlobalSectionsFunctor (.of B)).mapIso
        (pulledIdealCongr (specTower_comp (R := R) (A := A) (B := B)))).hom).surjective.comp
      (ConcreteCategory.bijective_of_isIso
        ((affineGlobalSectionsFunctor (.of B)).mapIso (TF3.conormalIso (j ≫ p))).hom).surjective)


-- @@ L305-363 verbatim
omit [Algebra.IsStandardSmooth R A] in
/-- The genuine native comparison square, in syntactically fixed affine module objects. -/
theorem nativeComparison_sections_apply
    (x : (affineGlobalSectionsFunctor (.of B)).obj
      (AlgebraicGeometry.Chow.M7.CIICLASS.T1N23.libConormalAmb (j ≫ p))) :
    (libraryCotangentSectionsIso (ambientExtension (A := A) hf)).hom
      ((affineGlobalSectionsFunctor (.of B)).map (conormalComparison j p) x) =
      conormalMap (A := A) hf (nativeSourceNormalizer (R := R) (A := A) (B := B) x) := by
  have h₁ : (libraryCotangentSectionsIso (ambientExtension (A := A) hf)).hom
      ((affineGlobalSectionsFunctor (.of B)).map (conormalComparison j p) x) =
      (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
        ((affineGlobalSectionsFunctor (.of B)).map (TF3.conormalIso j).hom
        ((affineGlobalSectionsFunctor (.of B)).map (conormalComparison j p) x)) :=
    libraryCotangentSectionsIso_hom_apply (ambientExtension (A := A) hf) _
  have h₂ : (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
    ((affineGlobalSectionsFunctor (.of B)).map (TF3.conormalIso j).hom
    ((affineGlobalSectionsFunctor (.of B)).map (conormalComparison j p) x)) =
      conormalMap (A := A) hf (nativeSourceNormalizer (R := R) (A := A) (B := B) x) := by
    have hn := @nativeConormalComparison_sections R A B
      (inferInstanceAs (CommRing R)) (inferInstanceAs (CommRing A))
      (inferInstanceAs (CommRing B)) (inferInstanceAs (Algebra R A))
      (inferInstanceAs (Algebra R B)) (inferInstanceAs (Algebra A B))
      (inferInstanceAs (IsScalarTower R A B)) hquot hamb x
    have hm₁ := affineSections_map_apply (conormalComparison j p) x
    have hm₂ := affineSections_map_apply (TF3.conormalIso j).hom
      ((affineGlobalSectionsFunctor (.of B)).map (conormalComparison j p) x)
    have hL : (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
      ((affineGlobalSectionsFunctor (.of B)).map (TF3.conormalIso j).hom
      ((affineGlobalSectionsFunctor (.of B)).map (conormalComparison j p) x)) =
        (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
          ((TF3.conormalIso j).hom.app ⊤ ((conormalComparison j p).app ⊤ x)) :=
      (congrArg (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom hm₂).trans
        (congrArg (fun q => (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
          ((TF3.conormalIso j).hom.app ⊤ q)) hm₁)
    have hs₁ := affineSections_map_apply (TF3.conormalIso (j ≫ p)).hom x
    have hs₂ := affineSections_map_apply
      (pulledIdealCongr (specTower_comp (R := R) (A := A) (B := B))).hom
      ((affineGlobalSectionsFunctor (.of B)).map (TF3.conormalIso (j ≫ p)).hom x)
    have hS : nativeSourceNormalizer (R := R) (A := A) (B := B) x =
        (pulledIdealCotangentSectionsIso (baseExtension hf)).hom
          ((pulledIdealCongr (specTower_comp (R := R) (A := A) (B := B))).hom.app ⊤
          ((TF3.conormalIso (j ≫ p)).hom.app ⊤ x)) :=
      (congrArg (pulledIdealCotangentSectionsIso (baseExtension hf)).hom hs₂).trans
        (congrArg (fun q => (pulledIdealCotangentSectionsIso (baseExtension hf)).hom
          ((pulledIdealCongr (specTower_comp (R := R) (A := A) (B := B))).hom.app ⊤ q)) hs₁)
    have hN : (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
      ((TF3.conormalIso j).hom.app ⊤ ((conormalComparison j p).app ⊤ x)) =
        conormalMap (A := A) hf
          ((pulledIdealCotangentSectionsIso (baseExtension hf)).hom
            ((pulledIdealCongr (specTower_comp (R := R) (A := A) (B := B))).hom.app ⊤
            ((TF3.conormalIso (j ≫ p)).hom.app ⊤ x))) := hn
    have hC : conormalMap (A := A) hf
          ((pulledIdealCotangentSectionsIso (baseExtension hf)).hom
            ((pulledIdealCongr (specTower_comp (R := R) (A := A) (B := B))).hom.app ⊤
            ((TF3.conormalIso (j ≫ p)).hom.app ⊤ x))) =
        conormalMap (A := A) hf (nativeSourceNormalizer (R := R) (A := A) (B := B) x) :=
      congrArg (conormalMap (A := A) hf) hS.symm
    exact hL.trans (hN.trans hC)
  exact h₁.trans h₂


-- @@ L365-376 verbatim
/-- The actual native differential agrees with the Extension differential after the
constructed target inverse; the square is derived from original class generators. -/
theorem nativeDifferential_sections_square :
    (affineGlobalSectionsFunctor (.of B)).map (TF3.c p j) ≫
      (pulledOmegaSectionsIso (R := R) (A := A) (B := B)).inv =
    (libraryCotangentSectionsIso (ambientExtension (A := A) hf)).hom ≫
      ModuleCat.ofHom (ambientExtension (A := A) hf).cotangentComplex := by
  letI : Algebra.IsStandardSmooth R (ambientExtension (A := A) hf).Ring :=
    inferInstanceAs (Algebra.IsStandardSmooth R A)
  apply isoTarget_cancel (pulledOmegaSectionsIso (R := R) (A := A) (B := B)).symm
  exact (originalConormalDifferential_extension_square (ambientExtension (A := A) hf)).trans
    (Category.assoc _ _ _).symm


-- @@ L378-387 verbatim
/-- The inverse target normalization identifies actual differential values. -/
theorem nativeDifferential_sections_apply
    (x : (affineGlobalSectionsFunctor (.of B)).obj
      (AlgebraicGeometry.Chow.M7.CIICLASS.T1N23.libConormalAmb j)) :
    (pulledOmegaSectionsIso (R := R) (A := A) (B := B)).inv
      ((affineGlobalSectionsFunctor (.of B)).map (TF3.c p j) x) =
      (ambientExtension (A := A) hf).cotangentComplex
        ((libraryCotangentSectionsIso (ambientExtension (A := A) hf)).hom x) :=
  ConcreteCategory.congr_hom (nativeDifferential_sections_square
    (R := R) (A := A) (B := B)) x


-- @@ L389-404 verbatim
/-- The actual native comparison and actual native differential are exact on affine modules. -/
theorem nativeAffine_maps_exact : Function.Exact
    ((affineGlobalSectionsFunctor (.of B)).map (conormalComparison j p))
    ((affineGlobalSectionsFunctor (.of B)).map (TF3.c p j)) :=
  functionExact_transport _ _ (conormalMap (A := A) hf)
    (ambientExtension (A := A) hf).cotangentComplex
    (nativeSourceNormalizer (R := R) (A := A) (B := B))
    (libraryCotangentSectionsIso (ambientExtension (A := A) hf)).hom
    (pulledOmegaSectionsIso (R := R) (A := A) (B := B)).inv
    (nativeSourceNormalizer_surjective (R := R) (A := A) (B := B))
    (ConcreteCategory.bijective_of_isIso _).injective
    (ConcreteCategory.bijective_of_isIso _).injective
    (map_zero _)
    (nativeComparison_sections_apply (R := R) (A := A) (B := B))
    (nativeDifferential_sections_apply (R := R) (A := A) (B := B))
    (conormalMap_exact (A := A) hf)


-- @@ L406-415 verbatim
/-- The actual native differential surjects without quotient smoothness or regularity. -/
theorem nativeAffine_differential_surjective : Function.Surjective
    ((affineGlobalSectionsFunctor (.of B)).map (TF3.c p j)) :=
  functionSurjective_transport _ _
    (libraryCotangentSectionsIso (ambientExtension (A := A) hf)).hom
    (pulledOmegaSectionsIso (R := R) (A := A) (B := B)).inv
    (ConcreteCategory.bijective_of_isIso _).surjective
    (ConcreteCategory.bijective_of_isIso _)
    (nativeDifferential_sections_apply (R := R) (A := A) (B := B))
    (conormalDifferential_surjective (A := A) hf)


-- @@ L417-424 verbatim
/-- The unchanged native sheaf comparison complex on actual affine global sections. -/
def nativeAffineSequence : ShortComplex (ModuleCat B) := by
  letI : (affineGlobalSectionsFunctor (.of B)).Additive :=
    affineGlobalSectionsFunctor_additive_pinned _
  letI : (affineGlobalSectionsFunctor (.of B)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact (ConormalComparisonSheafH2.conormalSequence j p).map
    (affineGlobalSectionsFunctor (.of B))


-- @@ L426-436 verbatim
/-- The unchanged actual native affine comparison complex is short exact. -/
theorem nativeAffineSequence_shortExact :
    (nativeAffineSequence (R := R) (A := A) (B := B)).ShortExact := by
  haveI : Mono (nativeAffineSequence (R := R) (A := A) (B := B)).f :=
    (ModuleCat.mono_iff_injective _).mpr
      (nativeConormalComparison_injective (R := R) (A := A) (B := B))
  haveI : Epi (nativeAffineSequence (R := R) (A := A) (B := B)).g :=
    (ModuleCat.epi_iff_surjective _).mpr
      (nativeAffine_differential_surjective (R := R) (A := A) (B := B))
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (nativeAffine_maps_exact (R := R) (A := A) (B := B))⟩


-- @@ L438-438 verbatim
end Tower

-- @@ L439-439 verbatim
section BaseSurjective

-- @@ L440-442 verbatim
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (hf : Function.Surjective (algebraMap R B))


-- @@ L444-450 verbatim
/-- The unchanged actual affine native complex, with both closed-immersion witnesses
constructed from the single original base surjection. -/
def nativeAffineSequenceOfSurjective : ShortComplex (ModuleCat B) := by
  letI : Fact (Function.Surjective (algebraMap R B)) := ⟨hf⟩
  letI : Fact (Function.Surjective (algebraMap A B)) :=
    ⟨ConormalComparisonH2.ambient_surjective (A := A) hf⟩
  exact nativeAffineSequence (R := R) (A := A) (B := B)


-- @@ L452-459 verbatim
/-- Actual affine native short exactness requires a standard-smooth ambient and one
base surjection; it requires no quotient smoothness, regularity, reducedness or flatness. -/
theorem nativeAffineSequenceOfSurjective_shortExact [Algebra.IsStandardSmooth R A] :
    (nativeAffineSequenceOfSurjective (A := A) hf).ShortExact := by
  letI : Fact (Function.Surjective (algebraMap R B)) := ⟨hf⟩
  letI : Fact (Function.Surjective (algebraMap A B)) :=
    ⟨ConormalComparisonH2.ambient_surjective (A := A) hf⟩
  exact nativeAffineSequence_shortExact (R := R) (A := A) (B := B)


-- @@ L461-461 verbatim
end BaseSurjective

-- @@ L462-462 verbatim
end SchemeKTheory.NativeKahlerPullbackH2
