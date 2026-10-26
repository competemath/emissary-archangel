/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.RelativeRiemannRoch.NativeKahlerPullbackH2
import RiemannRoch.KTheory.AffinePullback


-- @@ L10-25 verbatim
/-!
# Actual native conormal short exactness on Spec for H2

The original conormal source and middle term are quasicoherent through the
constructed tilde Isos. Standard smoothness of the ambient gives quasicoherence
of its actual relative sheaf; genuine affine pullback preserves this property.
The proved exactness of the unchanged native complex on affine global sections
therefore reflects to short exactness of the original sheaf complex on Spec B.

Both closed immersion witnesses are derived from the single original base
surjection R → B. Only A/R is standard smooth: the base and quotient may be
non-smooth or nonreduced. No desired comparison square or exactness is assumed.

Compatible closed charts, global short exactness and genuine K0 virtual
cotangent cancellation remain subsequent gates for nonsmooth H2 independence.
-/


-- @@ L27-27 verbatim
set_option autoImplicit false

-- @@ L28-28 verbatim
noncomputable section

-- @@ L29-29 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Algebra Algebra.Extension

-- @@ L30-30 verbatim
open SchemeKTheory.Cotangent SchemeKTheory.ConormalComparisonH2

-- @@ L31-31 verbatim
open SchemeKTheory.ConormalComparisonSheafH2 SchemeKTheory.ConormalNativeMapH2

-- @@ L32-32 verbatim
open SchemeKTheory.ConormalSectionsH2 SchemeKTheory.ConormalTensorH2

-- @@ L33-33 verbatim
open SchemeKTheory.NativeKahlerPullbackH2

-- @@ L34-34 verbatim
universe u

-- @@ L35-35 verbatim
namespace SchemeKTheory.NativeConormalExactH2


-- @@ L37-42 verbatim
/-- Equality of actual immersion maps transports the original library conormal object. -/
def conormalCongr {X P : Scheme.{u}} {i i' : X ⟶ P}
    (h : i = i') :
    Chow.M7.CIICLASS.T1N23.libConormalAmb i ≅
      Chow.M7.CIICLASS.T1N23.libConormalAmb i' :=
  TF3.conormalIso i ≪≫ pulledIdealCongr h ≪≫ (TF3.conormalIso i').symm


-- @@ L44-49 verbatim
/-- The original native conormal on Spec is quasicoherent through its actual tilde Iso. -/
theorem specConormal_isQuasicoherent {R B : CommRingCat.{u}} (φ : R ⟶ B)
    [IsClosedImmersion (Spec.map φ)] :
    (Chow.M7.CIICLASS.T1N23.libConormalAmb (Spec.map φ)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf).prop_of_iso
    (specConormalIsoTilde φ).symm inferInstance


-- @@ L51-51 verbatim
section Tower

-- @@ L52-55 verbatim
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [hquot : Fact (Function.Surjective (algebraMap R B))]
  [hamb : Fact (Function.Surjective (algebraMap A B))]

-- @@ L56-56 verbatim
local notation "j" => Spec.map (CommRingCat.ofHom (algebraMap A B))

-- @@ L57-57 verbatim
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap R A))

-- @@ L58-59 verbatim
attribute [local instance] ConormalNativeMapH2.baseSpecClosed
  ConormalNativeMapH2.ambientSpecClosed ConormalNativeMapH2.compositeSpecClosed


-- @@ L61-69 verbatim
omit hamb in
/-- The actual composite source is quasicoherent using the proved original Spec equality. -/
theorem nativeSource_isQuasicoherent :
    (Chow.M7.CIICLASS.T1N23.libConormalAmb (j ≫ p)).IsQuasicoherent := by
  letI : (Chow.M7.CIICLASS.T1N23.libConormalAmb
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).IsQuasicoherent :=
    specConormal_isQuasicoherent _
  exact (SheafOfModules.isQuasicoherent (Spec (.of B)).ringCatSheaf).prop_of_iso
    (conormalCongr (specTower_comp (R := R) (A := A) (B := B))).symm inferInstance


-- @@ L71-74 verbatim
/-- The actual middle library conormal is quasicoherent, with no quotient regularity. -/
theorem nativeMiddle_isQuasicoherent :
    (Chow.M7.CIICLASS.T1N23.libConormalAmb j).IsQuasicoherent :=
  specConormal_isQuasicoherent _


-- @@ L76-76 verbatim
variable [Algebra.IsStandardSmooth R A]


-- @@ L78-84 verbatim
omit [Algebra R B] [IsScalarTower R A B] hquot hamb in
/-- The actual pulled relative target is quasicoherent without quotient smoothness. -/
theorem nativeTarget_isQuasicoherent :
    ((Scheme.Modules.pullback j).obj (relativeSheaf p)).IsQuasicoherent := by
  letI : (relativeSheaf p).IsQuasicoherent :=
    algebraRelativeSheaf_isQuasicoherent (R := R) (A := A)
  exact pullback_specMap_isQuasicoherent (algebraMap A B) (relativeSheaf p)


-- @@ L86-101 verbatim
/-- The unchanged actual conormal complex is short exact as native sheaves on Spec B. -/
theorem nativeSpecSequence_shortExact :
    (ConormalComparisonSheafH2.conormalSequence j p).ShortExact := by
  let T := ConormalComparisonSheafH2.conormalSequence j p
  letI : T.X₁.IsQuasicoherent := by
    change (Chow.M7.CIICLASS.T1N23.libConormalAmb (j ≫ p)).IsQuasicoherent
    exact nativeSource_isQuasicoherent (R := R) (A := A) (B := B)
  letI : T.X₂.IsQuasicoherent := by
    change (Chow.M7.CIICLASS.T1N23.libConormalAmb j).IsQuasicoherent
    exact nativeMiddle_isQuasicoherent (A := A) (B := B)
  letI : T.X₃.IsQuasicoherent := by
    change ((Scheme.Modules.pullback j).obj (relativeSheaf p)).IsQuasicoherent
    exact nativeTarget_isQuasicoherent (R := R) (A := A) (B := B)
  exact (moduleSpecΓ_map_shortExact_iff
    T).mp
      (nativeAffineSequence_shortExact (R := R) (A := A) (B := B))


-- @@ L103-103 verbatim
end Tower


-- @@ L105-105 verbatim
section BaseSurjective

-- @@ L106-108 verbatim
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (hf : Function.Surjective (algebraMap R B))

-- @@ L109-110 verbatim
attribute [local instance] ConormalNativeMapH2.baseSpecClosed
  ConormalNativeMapH2.ambientSpecClosed ConormalNativeMapH2.compositeSpecClosed


-- @@ L112-119 verbatim
/-- The original native sheaf complex with both immersion witnesses derived from R → B. -/
def nativeSpecSequenceOfSurjective : ShortComplex (Spec (.of B)).Modules := by
  letI : Fact (Function.Surjective (algebraMap R B)) := ⟨hf⟩
  letI : Fact (Function.Surjective (algebraMap A B)) :=
    ⟨ConormalComparisonH2.ambient_surjective (A := A) hf⟩
  exact ConormalComparisonSheafH2.conormalSequence
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))


-- @@ L121-128 verbatim
/-- The actual native sheaf complex is short exact for a standard-smooth ambient
and one base surjection, including non-smooth and nonreduced quotients. -/
theorem nativeSpecSequenceOfSurjective_shortExact [Algebra.IsStandardSmooth R A] :
    (nativeSpecSequenceOfSurjective (A := A) hf).ShortExact := by
  letI : Fact (Function.Surjective (algebraMap R B)) := ⟨hf⟩
  letI : Fact (Function.Surjective (algebraMap A B)) :=
    ⟨ConormalComparisonH2.ambient_surjective (A := A) hf⟩
  exact nativeSpecSequence_shortExact (R := R) (A := A) (B := B)


-- @@ L130-130 verbatim
end BaseSurjective

-- @@ L131-131 verbatim
end SchemeKTheory.NativeConormalExactH2
