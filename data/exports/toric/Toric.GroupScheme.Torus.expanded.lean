/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.FieldTheory.Separable
public import Toric.GroupScheme.Diagonalizable
public import Toric.MvLaurentPolynomial


-- @@ L13-17 verbatim
/-!
# The standard algebraic torus

This file defines the standard algebraic torus over `Spec R` as `Spec (R ⊗ ℤ[Fₙ])`.
-/


-- @@ L19-19 verbatim
public noncomputable section


-- @@ L21-21 verbatim
open CategoryTheory Opposite Limits

-- @@ L22-22 verbatim
open scoped AddMonoidAlgebra


-- @@ L24-24 verbatim
universe u


-- @@ L26-26 verbatim
namespace AlgebraicGeometry.Scheme

-- @@ L27-27 verbatim
section IsSplitTorusOver

-- @@ L28-31 verbatim
variable {G H S : Scheme.{u}} [G.Over S] [H.Over S] [GrpObj (asOver G S)]
  [GrpObj (asOver H S)]

-- TODO: Move me!

-- @@ L32-33 verbatim
instance {M N : Scheme.{u}} [M.Over S] [N.Over S] [MonObj (asOver M S)] [MonObj (asOver N S)]
    (e : M ≅ N) [e.hom.IsOver S] [IsMonHom (e.hom.asOver S)] : IsMonHom (e.asOver S).hom := ‹_›


-- @@ L35-40 verbatim
variable (G S) in
@[mk_iff]
class IsSplitTorusOver : Prop where
  existsIso :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module.Free ℤ A) (e : G ≅ Diag S A)
      (_ : e.hom.IsOver S), IsMonHom (e.hom.asOver S)


-- @@ L42-46 verbatim
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance diag_isSplitTorusOver {A : Type u} [AddCommGroup A] [Module.Free ℤ A] :
    (Diag S A).IsSplitTorusOver S :=
  ⟨A, ‹_›, ‹_›, by exact .refl (S.Diag A), by dsimp; infer_instance, by dsimp; infer_instance⟩


-- @@ L48-53 verbatim
set_option backward.defeqAttrib.useBackward true in
lemma IsSplitTorusOver.of_isIso [H.IsSplitTorusOver S] (f : G ⟶ H) [IsIso f] [f.IsOver S]
    [IsMonHom (f.asOver S)] : G.IsSplitTorusOver S :=
  have : IsMonHom ((asIso f).hom.asOver S) := ‹_›
  let ⟨A, _, _, e, _, _⟩ := ‹H.IsSplitTorusOver S›
  ⟨A, _, ‹_›, (asIso f).trans e, by dsimp; infer_instance, by dsimp; infer_instance⟩


-- @@ L55-59 verbatim
lemma IsSplitTorusOver.of_isIso' [G.IsSplitTorusOver S]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMonHom (f.asOver S)] : H.IsSplitTorusOver S :=
  have : IsMonHom ((inv f).asOver S) := by
    simpa using inferInstanceAs <| IsMonHom (asIso <| f.asOver S).inv
  .of_isIso (inv f)


-- @@ L61-62 verbatim
lemma IsSplitTorusOver.of_iso [H.IsSplitTorusOver S] (e : G ≅ H) [e.hom.IsOver S]
    [IsMonHom (e.hom.asOver S)] : G.IsSplitTorusOver S := of_isIso e.hom


-- @@ L64-81 verbatim
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (G S) in
/-- Every split torus that's locally of finite type is isomorphic to `𝔾ₘⁿ` for some `n`. -/
lemma exists_iso_diag_finite_of_isSplitTorusOver_locallyOfFiniteType [G.IsSplitTorusOver S]
    [hG : LocallyOfFiniteType (G ↘ S)] [Nonempty S] :
    ∃ (ι : Type u) (_ : Finite ι) (e : G ≅ Diag S ℤ[ι]) (_ : e.hom.IsOver S),
      IsMonHom (e.hom.asOver S) := by
  obtain ⟨A, _, _, e, _, _⟩ := ‹G.IsSplitTorusOver S›
  replace hG : LocallyOfFiniteType (Diag S A ↘ S) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType e.hom]
    erw [comp_over e.hom]
    assumption
  rw [locallyOfFiniteType_diag_iff] at hG
  exact ⟨Module.Free.ChooseBasisIndex ℤ A, inferInstance,
    e.trans <| Diag.mapIso S <| (Module.Free.chooseBasis ℤ A).repr.toAddEquiv.trans
      AddMonoidAlgebra.coeffAddEquiv.symm,
    by dsimp; infer_instance, by dsimp; infer_instance⟩


-- @@ L83-83 verbatim
end IsSplitTorusOver


-- @@ L85-85 verbatim
section IsTorusOver

-- @@ L86-87 verbatim
variable {k : Type u} [Field k] {G H : Scheme.{u}} [G.Over (Spec ↧k)] [H.Over (Spec ↧k)]
  [GrpObj (G.asOver (Spec ↧k))] [GrpObj (H.asOver (Spec ↧k))]


-- @@ L89-95 verbatim
variable (k G) in
@[mk_iff]
class IsTorusOver : Prop where
  existsSplit :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra.IsSeparable k L),
      (pullback (G ↘ Spec ↧k) <| Spec.map <| CommRingCat.ofHom <|
        algebraMap k L).IsSplitTorusOver (Spec ↧L)


-- @@ L97-103 verbatim
set_option backward.isDefEq.respectTransparency false in
instance [G.IsSplitTorusOver (Spec ↧k)] : G.IsTorusOver k := by
  refine ⟨k, ‹_›, inferInstance, inferInstance, ?_⟩
  simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id]
  suffices (pullback (G ↘ Spec ↧k) (𝟙 _)).IsSplitTorusOver (Spec ↧k) by
    convert this <;> simp
  exact .of_isIso (pullback.fst (G ↘ Spec ↧k) (𝟙 _))


-- @@ L105-118 verbatim
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma IsTorusOver.of_iso (e : G ≅ H) [e.hom.IsOver <| Spec ↧k]
    [IsMonHom <| e.hom.asOver <| Spec ↧k] [H.IsTorusOver k] : G.IsTorusOver k := by
  obtain ⟨L, _, _, _, hH⟩ := ‹H.IsTorusOver k›
  refine ⟨L, _, ‹_›, ‹_›, ?_⟩
  let e'' := (Over.pullback <| Spec.map <| CommRingCat.ofHom <| algebraMap k L).mapGrp.mapIso <|
    Grp.mkIso' <| e.asOver <| Spec ↧k
  let e' := (Grp.forget _ ⋙ Over.forget _).mapIso e''
  dsimp at e'
  have : e'.hom.IsOver (Spec ↧L) := by simp [e', e'']
  have : IsMonHom <| e'.hom.asOver <| Spec ↧L := by
    simpa using! Mon.instIsMonHomHom e''.hom.hom
  exact .of_iso e'


-- @@ L120-124 verbatim
lemma IsTorusOver.of_isIso [H.IsTorusOver k]
    (f : G ⟶ H) [IsIso f] [f.IsOver <| Spec ↧k] [IsMonHom <| f.asOver <| Spec ↧k] :
    G.IsTorusOver k :=
  have : IsMonHom ((asIso f).hom.asOver <| Spec ↧k) := ‹_›
  .of_iso (asIso f)


-- @@ L126-126 verbatim
end IsTorusOver


-- @@ L128-129 verbatim
/-- The (split) algebraic torus over `S` indexed by `σ`. -/
abbrev SplitTorus (S : Scheme) (σ : Type u) : Scheme.{u} := Diag S <| FreeAbelianGroup σ


-- @@ L131-132 verbatim
@[inherit_doc SplitTorus]
notation3 "𝔾ₘ[" S ", " σ "]" => SplitTorus S σ


-- @@ L134-158 expanded
/-- The multiplicative group over `S`. -/
notation3 "𝔾ₘ[" S "]" => SplitTorus S PUnit


-- @@ L160-170 verbatim
set_option backward.defeqAttrib.useBackward true in
variable (G S : Scheme.{u}) [G.Over S] [GrpObj (G.asOver S)] in
/-- Every split torus that's locally of finite type is isomorphic to `𝔾ₘⁿ` for some `n`. -/
lemma exists_iso_splitTorus_of_isSplitTorusOver [G.IsSplitTorusOver S] :
    ∃ (σ : Type u) (e : G ≅ SplitTorus S σ) (_ : e.hom.IsOver S),
      IsMonHom (e.hom.asOver S) := by
  obtain ⟨A, _, _, e, _, _⟩ := ‹G.IsSplitTorusOver S›
  exact ⟨Module.Free.ChooseBasisIndex ℤ A,
    e.trans <| Diag.mapIso S ((Module.Free.chooseBasis ℤ A).repr.toAddEquiv.trans
      (FreeAbelianGroup.equivFinsupp _).symm),
    by dsimp; infer_instance, by dsimp; infer_instance⟩


-- @@ L172-172 verbatim
variable {R : CommRingCat} {σ : Type*}


-- @@ L174-177 expanded
variable (R σ) in
/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
abbrev splitTorusIso (R : CommRingCat) (σ : Type*) :
    SplitTorus (Spec R) σ ≅ Spec ↧(MvLaurentPolynomial σ R) :=
  diagSpecIso _ _


-- @@ L179-179 verbatim
end AlgebraicGeometry.Scheme
