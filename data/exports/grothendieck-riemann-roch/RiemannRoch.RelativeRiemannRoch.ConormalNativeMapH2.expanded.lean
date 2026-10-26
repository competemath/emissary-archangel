/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.Chow.C1CapFrames
import RiemannRoch.RelativeRiemannRoch.ConormalTensorH2


-- @@ L10-32 verbatim
/-!
# The original affine conormal comparison and its actual cotangent map

For the original scalar tower `R → A → B`, derive the equality of composite
Spec maps. Equality transport preserves the actual native ideal inclusion and
pullback unit. The actual composite pullback comparison preserves unit sections,
and its kernel-coefficient square is proved from the original ideal inclusion
and Gamma--Spec naturality. No comparison square is assumed.

Every native pulled ideal section comes from a quotient-unit section. The
unchanged pulled comparison, and then the original library conormal comparison,
agree with the actual Extension cotangent map on all affine global sections.
They are injective when `A/R` is formally smooth. There is no smoothness,
regularity, or flatness assumption on the quotient `B`.

The API uses Fact witnesses for the two surjections so that the native closed
immersion instances can be inferred without reconstructing a hidden base ring.
The second witness follows from the first by `ambient_surjective`.

Normalization of the native relative differential, compatible chart/stalk
transport, global sheaf short exactness and virtual cotangent independence
remain separate steps.
-/


-- @@ L34-34 verbatim
set_option autoImplicit false

-- @@ L35-35 verbatim
noncomputable section

-- @@ L36-36 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Algebra Algebra.Extension

-- @@ L37-37 verbatim
open SchemeNormalCone.AlgebraicGeometry

-- @@ L38-38 verbatim
universe u

-- @@ L39-39 verbatim
namespace SchemeKTheory.ConormalNativeMapH2

-- @@ L40-40 verbatim
open ConormalComparisonSheafH2 ConormalSectionsH2 ConormalTensorH2 ConormalComparisonH2


-- @@ L42-46 verbatim
/-- The inverse of a native module-sheaf isomorphism is surjective on sections. -/
theorem sheafIso_inv_surjective {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (V : X.Opens) : Function.Surjective (e.inv.app V) := by
  intro x
  exact ⟨e.hom.app V x, congrArg (fun f => f.app V x) e.hom_inv_id⟩


-- @@ L48-54 verbatim
/-- A native module-sheaf isomorphism is injective on each section module. -/
theorem sheafIso_hom_injective {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (V : X.Opens) : Function.Injective (e.hom.app V) := by
  intro x y hxy
  exact (congrArg (fun f => f.app V x) e.hom_inv_id).symm.trans
    ((congrArg (fun z => e.inv.app V z) hxy).trans
      (congrArg (fun f => f.app V y) e.hom_inv_id))


-- @@ L56-60 verbatim
/-- The actual native hom component cancels its inverse component. -/
theorem sheafIso_hom_inv_apply {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (V : X.Opens) (x : Γ(N, V)) :
    e.hom.app V (e.inv.app V x) = x :=
  congrArg (fun f => f.app V x) e.inv_hom_id


-- @@ L62-72 verbatim
/-- Equality on surjective generators transports through the actual native sheaf inverse. -/
theorem sheafIso_eq_of_generators {X : Scheme.{u}} {M N : X.Modules}
    {S T : Type*} (e : M ≅ N) (V : X.Opens) (a : S → Γ(N, V))
    (ha : Function.Surjective a) (b : Γ(M, V) → T) (c : Γ(N, V) → T)
    (hgen : ∀ s, b (e.inv.app V (a s)) = c (a s)) (x : Γ(M, V)) :
    b x = c (e.hom.app V x) := by
  obtain ⟨s, hs⟩ := ha (e.hom.app V x)
  have hx : e.inv.app V (a s) = x :=
    (congrArg (fun z => e.inv.app V z) hs).trans
      (congrArg (fun f => f.app V x) e.hom_inv_id)
  exact (congrArg b hx).symm.trans ((hgen s).trans (congrArg c hs))


-- @@ L74-84 verbatim
/-- A square with an injective section map transports injectivity to its native source. -/
theorem sheafSquare_injective {X : Scheme.{u}} {M N P Q : X.Modules}
    (e : M ≅ P) (t : N ≅ Q) (f : M ⟶ N) (g : P ⟶ Q)
    (hs : f ≫ t.hom = e.hom ≫ g) (V : X.Opens)
    (hg : Function.Injective (g.app V)) : Function.Injective (f.app V) := by
  intro x y hxy
  apply sheafIso_hom_injective e V
  apply hg
  exact (congrArg (fun k => k.app V x) hs).symm.trans
    ((congrArg (fun z => t.hom.app V z) hxy).trans
      (congrArg (fun k => k.app V y) hs))


-- @@ L86-93 verbatim
/-- A native sheaf square transports a normalized equality of section functions. -/
theorem sheafSquare_sections {X : Scheme.{u}} {M N P Q : X.Modules} {T : Type*}
    (e : M ≅ P) (t : N ≅ Q) (f : M ⟶ N) (g : P ⟶ Q)
    (hs : f ≫ t.hom = e.hom ≫ g) (V : X.Opens)
    (a : Γ(Q, V) → T) (b : Γ(P, V) → T)
    (hb : ∀ z, a (g.app V z) = b z) (x : Γ(M, V)) :
    a (t.hom.app V (f.app V x)) = b (e.hom.app V x) :=
  (congrArg a (congrArg (fun k => k.app V x) hs)).trans (hb (e.hom.app V x))


-- @@ L95-102 verbatim
/-- Affine global-section normalization respects the actual inverse sheaf map. -/
theorem affineIso_comp_inv_apply {S : CommRingCat.{u}} {M N : (Spec S).Modules}
    {L : ModuleCat S} (e : M ≅ N)
    (f : (affineGlobalSectionsFunctor S).obj N ≅ L)
    (x : Γ(N, ⊤)) :
    ((affineGlobalSectionsFunctor S).mapIso e ≪≫ f).hom (e.inv.app ⊤ x) = f.hom x := by
  change f.hom (e.hom.app ⊤ (e.inv.app ⊤ x)) = _
  exact congrArg f.hom.hom (congrArg (fun g => g.app ⊤ x) e.inv_hom_id)


-- @@ L104-104 verbatim
section Congruence

-- @@ L105-105 verbatim
variable {X P : Scheme.{u}} {i i' : X ⟶ P}


-- @@ L107-109 verbatim
/-- Equality of the original immersion maps transports their actual native ideals. -/
def idealCongr (h : i = i') : TF3.idealOf i ≅ TF3.idealOf i' :=
  eqToIso (congrArg TF3.idealOf h)


-- @@ L111-115 verbatim
/-- Equality of immersion maps transports the original pulled ideal objects. -/
def pulledIdealCongr (h : i = i') :
    (Scheme.Modules.pullback i).obj (TF3.idealOf i) ≅
      (Scheme.Modules.pullback i').obj (TF3.idealOf i') :=
  eqToIso (congrArg (fun f => (Scheme.Modules.pullback f).obj (TF3.idealOf f)) h)


-- @@ L117-121 verbatim
/-- The actual equality transport preserves the original ideal inclusion on top sections. -/
theorem idealCongr_inv_inclusion (h : i = i') (s : Γ(TF3.idealOf i', ⊤)) :
    TF3.ιapp i ⊤ ((idealCongr h).inv.app ⊤ s) = TF3.ιapp i' ⊤ s := by
  cases h
  rfl


-- @@ L123-130 verbatim
/-- Original pullback-unit sections are preserved by the equality transport. -/
theorem pulledIdealCongr_inv_unit (h : i = i') (s : Γ(TF3.idealOf i', ⊤)) :
    (pulledIdealCongr h).inv.app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app (TF3.idealOf i')).app ⊤ s) =
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (TF3.idealOf i)).app ⊤
      ((idealCongr h).inv.app ⊤ s) := by
  cases h
  rfl

-- @@ L131-131 verbatim
end Congruence


-- @@ L133-133 verbatim
section Native

-- @@ L134-135 verbatim
variable {X P Q : Scheme.{u}} (j : X ⟶ Q) (p : Q ⟶ P)
  [IsClosedImmersion j] [IsClosedImmersion (j ≫ p)]


-- @@ L137-142 verbatim
/-- The original native comparison before the library conormal isomorphisms. -/
def pulledComparison :
    (Scheme.Modules.pullback (j ≫ p)).obj (TF3.idealOf (j ≫ p)) ⟶
      (Scheme.Modules.pullback j).obj (TF3.idealOf j) :=
  (Scheme.Modules.pullbackComp j p).inv.app (TF3.idealOf (j ≫ p)) ≫
    (Scheme.Modules.pullback j).map (idealComparison j p)


-- @@ L144-155 verbatim
/-- The unchanged pulled comparison maps a composite unit to the iterated coefficient-ideal unit. -/
theorem pulledComparison_unit (V : P.Opens) (s : Γ(TF3.idealOf (j ≫ p), V)) :
    (pulledComparison j p).app ((j ≫ p) ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ p)).unit.app
        (TF3.idealOf (j ≫ p))).app V s) =
    ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (TF3.idealOf j)).app (p ⁻¹ᵁ V)
      ((idealComparison j p).app (p ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          (TF3.idealOf (j ≫ p))).app V s)) := by
  exact (congrArg (fun x => ((Scheme.Modules.pullback j).map (idealComparison j p)).app
    ((j ≫ p) ⁻¹ᵁ V) x) (Chow.C1Cap.pullbackComp_inv_unit j p _ V s)).trans
      (Chow.C1Cap.pullback_map_unit j (idealComparison j p) (p ⁻¹ᵁ V) _)

-- @@ L156-160 verbatim
/-- The original comparison is the pulled comparison under the native library isomorphisms. -/
theorem conormalComparison_pulled :
    conormalComparison j p ≫ (TF3.conormalIso j).hom =
      (TF3.conormalIso (j ≫ p)).hom ≫ pulledComparison j p := by
  simp only [conormalComparison, pulledComparison, Category.assoc, Iso.inv_hom_id, Category.comp_id]


-- @@ L162-162 verbatim
end Native

-- @@ L163-163 verbatim
section Tower

-- @@ L164-166 verbatim
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [hquot : Fact (Function.Surjective (algebraMap R B))]


-- @@ L168-168 verbatim
local notation "hf" => hquot.out


-- @@ L170-179 verbatim
omit hquot in
/-- The original scalar tower yields the actual equality of composite Spec maps. -/
theorem specTower_comp :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
    Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R A B).symm


-- @@ L181-183 verbatim
local instance baseSpecClosed : IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
  IsClosedImmersion.spec_of_surjective _ hf


-- @@ L185-185 verbatim
variable [hamb : Fact (Function.Surjective (algebraMap A B))]


-- @@ L187-190 verbatim
omit [CommRing R] [Algebra R A] [Algebra R B] [IsScalarTower R A B] hquot in
local instance ambientSpecClosed : IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  IsClosedImmersion.spec_of_surjective _ hamb.out


-- @@ L192-196 verbatim
local instance compositeSpecClosed : IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  rw [specTower_comp]
  infer_instance


-- @@ L198-223 verbatim
/-- The native ideal comparison has exactly the original scalar-tower coefficient action. -/
theorem nativeIdeal_kernel_value
    (s : Γ(TF3.idealOf (Spec.map (CommRingCat.ofHom (algebraMap R B))), ⊤)) :
    specIdealSectionsEquiv (CommRingCat.ofHom (algebraMap A B))
      ((idealComparison (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))).unit.app
            (TF3.idealOf (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R A))))).app ⊤
          ((idealCongr (specTower_comp (R := R) (A := A) (B := B))).inv.app ⊤ s))) =
    kernelToAmbient (R := R) (A := A) (B := B)
      (specIdealSectionsEquiv (CommRingCat.ofHom (algebraMap R B)) s) := by
  apply Subtype.ext
  have hi := idealComparison_app_inclusion
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⊤
    ((idealCongr (specTower_comp (R := R) (A := A) (B := B))).inv.app ⊤ s)
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A)))
    (TF3.ιapp (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) ⊤
        ((idealCongr (specTower_comp (R := R) (A := A) (B := B))).inv.app ⊤ s))
  exact (congrArg ((Scheme.ΓSpecIso (.of A)).hom) hi).trans
    (hn.trans (congrArg (fun x => algebraMap R A ((Scheme.ΓSpecIso (.of R)).hom x))
      (idealCongr_inv_inclusion (specTower_comp (R := R) (A := A) (B := B)) s)))

-- @@ L224-224 verbatim
local notation "j" => Spec.map (CommRingCat.ofHom (algebraMap A B))

-- @@ L225-225 verbatim
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap R A))

-- @@ L226-226 verbatim
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap R B))

-- @@ L227-227 verbatim
local notation "h" => specTower_comp (R := R) (A := A) (B := B)



-- @@ L230-236 verbatim
/-- The source normalization uses only the proved equality of original Spec maps. -/
def sourcePulledSectionsIso :
    (affineGlobalSectionsFunctor (.of B)).obj
      ((Scheme.Modules.pullback (j ≫ p)).obj (TF3.idealOf (j ≫ p))) ≅
    ModuleCat.of B (baseExtension hf).Cotangent :=
  (affineGlobalSectionsFunctor (.of B)).mapIso (pulledIdealCongr h) ≪≫
    pulledIdealCotangentSectionsIso (baseExtension hf)


-- @@ L238-264 verbatim
/-- The native pulled comparison agrees with the true cotangent map on original unit generators. -/
theorem nativePulledComparison_unit
    (s : Γ(TF3.idealOf i, ⊤)) :
    (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
      ((pulledComparison j p).app ⊤ ((pulledIdealCongr h).inv.app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (TF3.idealOf i)).app ⊤ s))) =
    conormalMap (A := A) hf ((pulledIdealCotangentSectionsIso (baseExtension hf)).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (TF3.idealOf i)).app ⊤ s)) := by
  have h₁ := congrArg (fun x => (pulledComparison j p).app ⊤ x)
    (pulledIdealCongr_inv_unit h s)
  have h₂ := pulledComparison_unit j p ⊤ ((idealCongr h).inv.app ⊤ s)
  have h₃ := pulledIdealCotangentSectionsIso_unit (ambientExtension (A := A) hf)
    ((idealComparison j p).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
        (TF3.idealOf (j ≫ p))).app ⊤ ((idealCongr h).inv.app ⊤ s)))
  have h₄ := congrArg (Extension.Cotangent.mk (P := ambientExtension (A := A) hf))
    (nativeIdeal_kernel_value (A := A) s)
  have hm : conormalMap (A := A) hf
      (Extension.Cotangent.mk (specIdealSectionsEquiv (CommRingCat.ofHom (algebraMap R B)) s)) =
      Extension.Cotangent.mk (kernelToAmbient (R := R) (A := A) (B := B)
        (specIdealSectionsEquiv (CommRingCat.ofHom (algebraMap R B)) s)) := rfl
  exact (congrArg (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom.hom
    (h₁.trans h₂)).trans (h₃.trans (h₄.trans (hm.symm.trans
      (congrArg (conormalMap (A := A) hf)
        (pulledIdealCotangentSectionsIso_unit (baseExtension hf) s)).symm)))

-- @@ L265-273 verbatim
omit hamb in
/-- Every composite pulled ideal section is a transported original quotient-unit section. -/
theorem nativeCompositeUnit_surjective : Function.Surjective
    (fun s : Γ(TF3.idealOf i, ⊤) => (pulledIdealCongr h).inv.app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (TF3.idealOf i)).app ⊤ s)) := by
  letI : (TF3.idealOf i).IsQuasicoherent := specIdeal_isQuasicoherent _
  exact (sheafIso_inv_surjective (pulledIdealCongr h) ⊤).comp
    (nativePullbackUnit_surjective (algebraMap R B) hf (TF3.idealOf i))


-- @@ L275-286 verbatim
omit hamb in
/-- The source normalization evaluates transported quotient-unit sections canonically. -/
theorem sourcePulledSectionsIso_inv_unit (s : Γ(TF3.idealOf i, ⊤)) :
    (sourcePulledSectionsIso (R := R) (A := A) (B := B)).hom
      ((pulledIdealCongr h).inv.app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (TF3.idealOf i)).app ⊤ s)) =
    (pulledIdealCotangentSectionsIso (baseExtension hf)).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (TF3.idealOf i)).app ⊤ s) :=
  affineIso_comp_inv_apply (pulledIdealCongr h)
    (pulledIdealCotangentSectionsIso (baseExtension hf)) _


-- @@ L288-302 verbatim
/-- The original Spec comparison and true cotangent map agree on every native pulled section. -/
theorem nativePulledComparison_sections
    (x : Γ((Scheme.Modules.pullback (j ≫ p)).obj (TF3.idealOf (j ≫ p)), ⊤)) :
    (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
      ((pulledComparison j p).app ⊤ x) =
    conormalMap (A := A) hf ((pulledIdealCotangentSectionsIso (baseExtension hf)).hom
      ((pulledIdealCongr h).hom.app ⊤ x)) := by
  letI : (TF3.idealOf i).IsQuasicoherent := specIdeal_isQuasicoherent _
  exact sheafIso_eq_of_generators (pulledIdealCongr h) ⊤
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (TF3.idealOf i)).app ⊤)
    (nativePullbackUnit_surjective (algebraMap R B) hf (TF3.idealOf i))
    (fun q => (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
      ((pulledComparison j p).app ⊤ q))
    (fun q => conormalMap (A := A) hf ((pulledIdealCotangentSectionsIso (baseExtension hf)).hom q))
    (nativePulledComparison_unit (A := A)) x


-- @@ L304-314 verbatim
/-- The actual pulled comparison is injective on global sections for a formally smooth ambient. -/
theorem nativePulledComparison_injective [FormallySmooth R A] :
    Function.Injective ((pulledComparison j p).app ⊤) := by
  intro x y hxy
  apply sheafIso_hom_injective (pulledIdealCongr h) ⊤
  apply (ConcreteCategory.bijective_of_isIso
    (pulledIdealCotangentSectionsIso (baseExtension hf)).hom).injective
  apply conormalMap_injective (A := A) hf
  exact (nativePulledComparison_sections (A := A) x).symm.trans
    ((congrArg (fun q => (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom q)
      hxy).trans (nativePulledComparison_sections (A := A) y))

-- @@ L315-327 verbatim
/-- The unchanged library conormal comparison agrees with the actual cotangent map on sections. -/
theorem nativeConormalComparison_sections
    (x : Γ(AlgebraicGeometry.Chow.M7.CIICLASS.T1N23.libConormalAmb (j ≫ p), ⊤)) :
    (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom
      ((TF3.conormalIso j).hom.app ⊤ ((conormalComparison j p).app ⊤ x)) =
    conormalMap (A := A) hf ((pulledIdealCotangentSectionsIso (baseExtension hf)).hom
      ((pulledIdealCongr h).hom.app ⊤ ((TF3.conormalIso (j ≫ p)).hom.app ⊤ x))) := by
  exact sheafSquare_sections (TF3.conormalIso (j ≫ p)) (TF3.conormalIso j)
    (conormalComparison j p) (pulledComparison j p) (conormalComparison_pulled j p) ⊤
    (pulledIdealCotangentSectionsIso (ambientExtension (A := A) hf)).hom.hom
    (fun q => conormalMap (A := A) hf ((pulledIdealCotangentSectionsIso (baseExtension hf)).hom
      ((pulledIdealCongr h).hom.app ⊤ q)))
    (nativePulledComparison_sections (R := R) (A := A) (B := B)) x


-- @@ L329-335 verbatim
/-- The original library conormal comparison is injective on affine global sections,
without smoothness or regularity of the quotient. -/
theorem nativeConormalComparison_injective [FormallySmooth R A] :
    Function.Injective ((conormalComparison j p).app ⊤) :=
  sheafSquare_injective (TF3.conormalIso (j ≫ p)) (TF3.conormalIso j)
    (conormalComparison j p) (pulledComparison j p) (conormalComparison_pulled j p) ⊤
    (nativePulledComparison_injective (R := R) (A := A) (B := B))

-- @@ L336-336 verbatim
end Tower

-- @@ L337-337 verbatim
end SchemeKTheory.ConormalNativeMapH2
