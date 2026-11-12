/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Algebra.Homology.TensorProductConstruction
import RepresentationTheory.Algebra.Homology.LinearYoneda


-- @@ L9-14 verbatim
/-!
# Comparison maps for projective resolutions

This module constructs canonical comparison maps on homology, Tor, and Ext from projective
resolutions and proves their independence, identity, and composition properties.
-/


-- @@ L16-16 verbatim
set_option backward.isDefEq.respectTransparency false


-- @@ L18-18 verbatim
namespace RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.Comparison


-- @@ L20-20 verbatim
open CategoryTheory


-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
namespace CategoryTheory.ProjectiveResolution


-- @@ L26-26 verbatim
variable {A : Type u} [Ring A] {M : ModuleCat.{u} A}


-- @@ L28-34 verbatim
/-- Between two projective resolutions of the same module, there exists a complex morphism
satisfying the displayed composition equality. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
theorem existsHom_comp_pi
    (P Q : ProjectiveResolution M) :
    ∃ f : P.complex ⟶ Q.complex, f ≫ Q.π = P.π :=
  ⟨ProjectiveResolution.lift (𝟙 M) P Q, by simp⟩


-- @@ L36-41 verbatim
/-- Any two projective resolutions of the same module have a nonempty type of homotopy
equivalences between their complexes. -/
theorem homotopyEquivNonempty
    (P Q : ProjectiveResolution M) :
    Nonempty (HomotopyEquiv P.complex Q.complex) :=
  ⟨ProjectiveResolution.homotopyEquiv P Q⟩


-- @@ L43-43 verbatim
/-! ## The source-level comparison maps -/


-- @@ L45-45 verbatim
open Limits


-- @@ L47-47 verbatim
universe v


-- @@ L49-49 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]

-- @@ L50-50 verbatim
variable {D : Type*} [Category* D] [Abelian D]


-- @@ L52-58 verbatim
/-- Applying an additive functor to two projective resolutions gives an isomorphism between their
homology objects in every degree. -/
noncomputable def functorHomologyIso (F : C ⥤ D) [F.Additive] {X : C}
    (P Q : ProjectiveResolution X) (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology n ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology n :=
  (P.isoLeftDerivedObj F n).symm ≪≫ Q.isoLeftDerivedObj F n


-- @@ L60-71 verbatim
/-- The homology map induced by a compatible morphism of projective resolutions is the hom of the
comparison isomorphism after applying an additive functor. -/
theorem functorHomologyMap_eq_isoHom (F : C ⥤ D) [F.Additive] {X : C}
    (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n =
      (functorHomologyIso F P Q n).hom := by
  change _ = (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom
  rw [← cancel_epi (P.isoLeftDerivedObj F n).hom, Iso.hom_inv_id_assoc]
  simpa using (ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    (𝟙 X) P Q φ (by simpa using hφ) F n).symm


-- @@ L73-84 verbatim
/-- Two morphisms satisfying the displayed degree-zero composition equalities induce equal homology
maps after applying an additive functor. -/
theorem functorHomologyMap_eq_of_comm (F : C ⥤ D) [F.Additive] {X : C}
    (P Q : ProjectiveResolution X) (φ ψ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0)
    (hψ : ψ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n =
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ) n := by
  rw [functorHomologyMap_eq_isoHom F P Q φ hφ n,
    functorHomologyMap_eq_isoHom F P Q ψ hψ n]


-- @@ L86-91 verbatim
/-- The hom of the additive-functor homology comparison isomorphism from a projective resolution to
itself is the identity. -/
theorem functorHomologyIso_self_hom (F : C ⥤ D) [F.Additive] {X : C}
    (P : ProjectiveResolution X) (n : ℕ) :
    (functorHomologyIso F P P n).hom = 𝟙 _ := by
  simp [functorHomologyIso]


-- @@ L93-99 verbatim
/-- The composite of two additive-functor homology comparison isomorphisms agrees with the direct
comparison isomorphism. -/
theorem functorHomologyIso_comp_hom (F : C ⥤ D) [F.Additive] {X : C}
    (P Q R : ProjectiveResolution X) (n : ℕ) :
    (functorHomologyIso F P Q n).hom ≫ (functorHomologyIso F Q R n).hom =
      (functorHomologyIso F P R n).hom := by
  simp [functorHomologyIso, Category.assoc]


-- @@ L101-101 verbatim
end CategoryTheory.ProjectiveResolution


-- @@ L103-103 verbatim
namespace HomotopyEquiv


-- @@ L105-125 verbatim
/-- A homotopy equivalence of complexes in an opposite category yields a reversed homotopy
equivalence between their unop complexes. -/
def unopComplex {ι V : Type*} [Category* V] [Preadditive V]
    {c : ComplexShape ι} {K L : HomologicalComplex Vᵒᵖ c} (h : HomotopyEquiv K L) :
    HomotopyEquiv
      ((HomologicalComplex.unopFunctor V c).obj (Opposite.op L))
      ((HomologicalComplex.unopFunctor V c).obj (Opposite.op K)) where
  hom := (HomologicalComplex.unopFunctor V c).map h.hom.op
  inv := (HomologicalComplex.unopFunctor V c).map h.inv.op
  homotopyHomInvId := by
    let F := HomologicalComplex.unopFunctor V c
    have h₁ : Homotopy (F.map h.hom.op ≫ F.map h.inv.op) (F.map (𝟙 (Opposite.op L))) := by
      simpa only [op_comp, op_id, Functor.map_comp] using
        Homotopy.unop h.homotopyInvHomId
    exact h₁.trans (Homotopy.ofEq (F.map_id (Opposite.op L)))
  homotopyInvHomId := by
    let F := HomologicalComplex.unopFunctor V c
    have h₁ : Homotopy (F.map h.inv.op ≫ F.map h.hom.op) (F.map (𝟙 (Opposite.op K))) := by
      simpa only [op_comp, op_id, Functor.map_comp] using
        Homotopy.unop h.homotopyHomInvId
    exact h₁.trans (Homotopy.ofEq (F.map_id (Opposite.op K)))


-- @@ L127-127 verbatim
end HomotopyEquiv


-- @@ L129-129 verbatim
namespace CategoryTheory.ProjectiveResolution


-- @@ L131-131 verbatim
section Tor


-- @@ L133-133 verbatim
variable {A : Type u} [Ring A] (N : ModuleCat.{u} A)

-- @@ L134-134 verbatim
variable {M : ModuleCat.{u} Aᵐᵒᵖ}


-- @@ L136-140 verbatim
/-- The degree-n additive commutative group attached to a left module and a projective resolution of
an opposite-ring module. -/
noncomputable abbrev modulePairGroup (P : ProjectiveResolution M) (n : ℕ) : AddCommGrpCat.{u} :=
  (((RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
    A N).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology n


-- @@ L142-149 verbatim
/-- The degree-n groups attached to a left module and two projective resolutions of an opposite-ring
module are isomorphic. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
noncomputable def modulePairGroupIso (P Q : ProjectiveResolution M) (n : ℕ) :
    modulePairGroup N P n ≅ modulePairGroup N Q n :=
  functorHomologyIso
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
      A N) P Q n


-- @@ L151-158 verbatim
/-- A morphism of projective-resolution complexes induces a map on the associated degree-n
module-pair groups. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
noncomputable def modulePairGroupMap (P Q : ProjectiveResolution M)
    (φ : P.complex ⟶ Q.complex) (n : ℕ) : modulePairGroup N P n ⟶ modulePairGroup N Q n :=
  HomologicalComplex.homologyMap
    (((RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
      A N).mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n


-- @@ L160-168 verbatim
/-- Under the displayed composition equality, the induced map on degree-n module-pair groups is the
hom of the specified isomorphism. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
theorem modulePairGroupMap_eq_isoHom (P Q : ProjectiveResolution M)
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    modulePairGroupMap N P Q φ n = (modulePairGroupIso N P Q n).hom :=
  functorHomologyMap_eq_isoHom
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
      A N) P Q φ hφ n


-- @@ L170-179 verbatim
/-- Two complex morphisms satisfying the displayed composition equalities induce equal maps on
degree-n module-pair groups. -/
@[source_ref "Chapter8/Problem8.2.5" (role := primary)]
theorem modulePairGroupMap_eq_of_comm (P Q : ProjectiveResolution M)
    (φ ψ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0)
    (hψ : ψ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    modulePairGroupMap N P Q φ n = modulePairGroupMap N P Q ψ n := by
  rw [modulePairGroupMap_eq_isoHom N P Q φ hφ n,
    modulePairGroupMap_eq_isoHom N P Q ψ hψ n]


-- @@ L181-188 verbatim
/-- The hom of the module-pair group isomorphism from a projective resolution to itself is the
identity. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
theorem modulePairGroupIso_self_hom (P : ProjectiveResolution M) (n : ℕ) :
    (modulePairGroupIso N P P n).hom = 𝟙 _ :=
  functorHomologyIso_self_hom
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
      A N) P n


-- @@ L190-197 verbatim
/-- The composite of two module-pair group isomorphisms equals the direct isomorphism. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
theorem modulePairGroupIso_comp_hom (P Q R : ProjectiveResolution M) (n : ℕ) :
    (modulePairGroupIso N P Q n).hom ≫ (modulePairGroupIso N Q R n).hom =
      (modulePairGroupIso N P R n).hom :=
  functorHomologyIso_comp_hom
    (RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor
      A N) P Q R n


-- @@ L199-199 verbatim
end Tor


-- @@ L201-201 verbatim
section Ext


-- @@ L203-203 verbatim
variable (k : Type u) [Field k] {A : Type u} [Ring A] [Algebra k A]

-- @@ L204-204 verbatim
variable (N : ModuleCat.{u} A) {M : ModuleCat.{u} A}


-- @@ L206-209 verbatim
/-- The degree-n k-module obtained from the linear Yoneda complex associated to a projective
resolution and a coefficient module. -/
noncomputable abbrev linearYonedaObj (P : ProjectiveResolution M) (n : ℕ) : ModuleCat.{u} k :=
  (ChainComplex.linearYonedaObj P.complex k N).homology n


-- @@ L211-220 verbatim
/-- A morphism between projective resolution complexes induces a morphism between their linear
Yoneda complexes in the reversed direction. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
noncomputable def linearYonedaMapOfResolutionHom (P Q : ProjectiveResolution M)
    (φ : Q.complex ⟶ P.complex) :
    ChainComplex.linearYonedaObj P.complex k N ⟶
      ChainComplex.linearYonedaObj Q.complex k N := by
  let F := ((linearYoneda k (ModuleCat.{u} A)).obj N).rightOp
  exact (HomologicalComplex.unopFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ))


-- @@ L222-228 verbatim
/-- A morphism of projective-resolution complexes induces, in the displayed direction, a map
between degree-n linear Yoneda objects. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
noncomputable def linearYonedaObjMap (P Q : ProjectiveResolution M)
    (φ : Q.complex ⟶ P.complex) (n : ℕ) :
    linearYonedaObj k N P n ⟶ linearYonedaObj k N Q n :=
  HomologicalComplex.homologyMap (linearYonedaMapOfResolutionHom k N P Q φ) n


-- @@ L230-242 verbatim
/-- Two complex morphisms satisfying the displayed composition equalities induce equal maps on
degree-n linear Yoneda objects. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
theorem linearYonedaObjMap_eq_of_comm (P Q : ProjectiveResolution M)
    (φ ψ : Q.complex ⟶ P.complex)
    (hφ : φ ≫ P.π = Q.π)
    (hψ : ψ ≫ P.π = Q.π) (n : ℕ) :
    linearYonedaObjMap k N P Q φ n = linearYonedaObjMap k N P Q ψ n := by
  let F := ((linearYoneda k (ModuleCat.{u} A)).obj N).rightOp
  have h : Homotopy φ ψ := ProjectiveResolution.liftHomotopy (𝟙 M) φ ψ
    (by simpa using hφ) (by simpa using hψ)
  have hF := F.mapHomotopy h
  exact (Homotopy.unop hF).homologyMap_eq n


-- @@ L244-251 verbatim
/-- The linear Yoneda complexes associated to two projective resolutions are homotopy equivalent. -/
noncomputable def linearYonedaHomotopyEquiv (P Q : ProjectiveResolution M) :
    HomotopyEquiv (ChainComplex.linearYonedaObj P.complex k N)
      (ChainComplex.linearYonedaObj Q.complex k N) := by
  let F := ((linearYoneda k (ModuleCat.{u} A)).obj N).rightOp
  exact
    RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.Comparison.HomotopyEquiv.unopComplex
      (F.mapHomotopyEquiv (ProjectiveResolution.homotopyEquiv Q P))


-- @@ L253-257 verbatim
/-- The degree-n linear Yoneda objects for two projective resolutions are isomorphic. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
noncomputable def linearYonedaObjIso (P Q : ProjectiveResolution M) (n : ℕ) :
    linearYonedaObj k N P n ≅ linearYonedaObj k N Q n :=
  (linearYonedaHomotopyEquiv k N P Q).toHomologyIso n


-- @@ L259-267 verbatim
/-- Under the displayed composition equality, the induced map on degree-n linear Yoneda objects is
the hom of the specified isomorphism. -/
@[source_ref "Chapter8/Problem8.2.5" (role := supporting)]
theorem linearYonedaObjMap_eq_isoHom (P Q : ProjectiveResolution M)
    (φ : Q.complex ⟶ P.complex) (hφ : φ ≫ P.π = Q.π) (n : ℕ) :
    linearYonedaObjMap k N P Q φ n = (linearYonedaObjIso k N P Q n).hom := by
  rw [linearYonedaObjMap_eq_of_comm k N P Q φ
    (ProjectiveResolution.homotopyEquiv Q P).hom hφ (by simp) n]
  rfl


-- @@ L269-269 verbatim
end Ext


-- @@ L271-271 verbatim
end CategoryTheory.ProjectiveResolution


-- @@ L273-273 verbatim
end RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.Comparison
