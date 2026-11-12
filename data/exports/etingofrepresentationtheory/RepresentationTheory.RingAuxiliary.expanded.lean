/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import RepresentationTheory.Alignment.Attribute


-- @@ L15-20 verbatim
/-!
# Auxiliary relations between rings and algebras

This module defines auxiliary equivalence relations between module categories and their linear
refinements over a common field.
-/


-- @@ L22-22 verbatim
universe u v


-- @@ L24-24 verbatim
open CategoryTheory


-- @@ L26-29 verbatim
/-- An auxiliary relation between two rings in the same universe. -/
def RepresentationTheory.RingAuxiliary.RingAuxiliary' (A : Type u) [Ring A]
    (B : Type u) [Ring B] : Prop :=
  Nonempty (FGModuleCat.{u} A ≌ FGModuleCat.{u} B)


-- @@ L31-34 verbatim
/-- An auxiliary relation between two rings, with independently varying universe levels. -/
def RepresentationTheory.RingAuxiliary.RingAuxiliary (A : Type u) [Ring A]
    (B : Type v) [Ring B] : Prop :=
  Nonempty (ModuleCat.{max u v} A ≌ ModuleCat.{max u v} B)


-- @@ L36-44 verbatim
/-- An auxiliary relation between two rings equipped with algebra structures over a common field. -/
def RepresentationTheory.RingAuxiliary.AlgebraAuxiliary (k : Type*) [Field k]
    (A : Type u) [Ring A] [Algebra k A]
    (B : Type u) [Ring B] [Algebra k B] : Prop :=
  ∃ (E : ModuleCat.{u} A ≌ ModuleCat.{u} B),
    haveI : E.functor.Additive :=
      letI : E.functor.IsEquivalence := E.isEquivalence_functor
      Functor.additive_of_preserves_binary_products E.functor
    E.functor.Linear k


-- @@ L46-50 verbatim
/-- An auxiliary relation between two rings equipped with algebra structures over a common field. -/
def RepresentationTheory.RingAuxiliary.AlgebraAuxiliary' (k : Type*) [Field k]
    (A : Type u) [Ring A] [Algebra k A]
    (B : Type u) [Ring B] [Algebra k B] : Prop :=
  ∃ (E : FGModuleCat.{u} A ≌ FGModuleCat.{u} B), E.functor.Linear k


-- @@ L52-52 verbatim
namespace RepresentationTheory.RingAuxiliary


-- @@ L54-60 verbatim
/-- The auxiliary algebra relation implies the associated auxiliary relation on the underlying
rings. -/
lemma AlgebraAuxiliary.toRingAuxiliary {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary k A B) : RingAuxiliary A B :=
  let ⟨E, _⟩ := h; ⟨E⟩


-- @@ L62-73 verbatim
/-- The auxiliary algebra relation is unchanged when its two ring arguments are exchanged. -/
lemma AlgebraAuxiliary.symm {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary k A B) : AlgebraAuxiliary k B A := by
  obtain ⟨E, hlin⟩ := h
  haveI : E.functor.Additive :=
    letI : E.functor.IsEquivalence := E.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E.functor
  haveI := hlin
  haveI : E.inverse.Additive := Equivalence.inverse_additive E
  exact ⟨E.symm, Equivalence.inverseLinear k E⟩


-- @@ L75-94 verbatim
/-- The auxiliary algebra relation composes through an intermediate algebra. -/
lemma AlgebraAuxiliary.trans {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    {C : Type u} [Ring C] [Algebra k C]
    (h₁ : AlgebraAuxiliary k A B)
    (h₂ : AlgebraAuxiliary k B C) : AlgebraAuxiliary k A C := by
  obtain ⟨E₁, hlin₁⟩ := h₁
  obtain ⟨E₂, hlin₂⟩ := h₂
  haveI : E₁.functor.Additive :=
    letI : E₁.functor.IsEquivalence := E₁.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E₁.functor
  haveI := hlin₁
  haveI : E₂.functor.Additive :=
    letI : E₂.functor.IsEquivalence := E₂.isEquivalence_functor
    Functor.additive_of_preserves_binary_products E₂.functor
  haveI := hlin₂
  refine ⟨E₁.trans E₂, ?_⟩
  change (E₁.functor ⋙ E₂.functor).Linear k
  infer_instance


-- @@ L96-98 verbatim
/-- Every ring is related to itself by the auxiliary ring relation. -/
lemma RingAuxiliary'.refl (A : Type u) [Ring A] : RingAuxiliary' A A :=
  ⟨CategoryTheory.Equivalence.refl⟩


-- @@ L100-103 verbatim
/-- The auxiliary ring relation is invariant under swapping its ring arguments. -/
lemma RingAuxiliary'.symm {A : Type u} [Ring A] {B : Type u} [Ring B]
    (h : RingAuxiliary' A B) : RingAuxiliary' B A :=
  h.map CategoryTheory.Equivalence.symm


-- @@ L105-112 verbatim
/-- The auxiliary ring relation composes through an intermediate ring. -/
lemma RingAuxiliary'.trans {A : Type u} [Ring A] {B : Type u} [Ring B]
    {C : Type u} [Ring C]
    (h₁ : RingAuxiliary' A B) (h₂ : RingAuxiliary' B C) :
    RingAuxiliary' A C := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact ⟨e₁.trans e₂⟩


-- @@ L114-120 verbatim
/-- The auxiliary algebra relation implies the associated auxiliary relation on the underlying
rings. -/
lemma AlgebraAuxiliary'.toRingAuxiliary {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary' k A B) : RingAuxiliary' A B :=
  let ⟨E, _⟩ := h; ⟨E⟩


-- @@ L122-129 verbatim
/-- The auxiliary algebra relation is unchanged when its two ring arguments are exchanged. -/
lemma AlgebraAuxiliary'.symm {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    (h : AlgebraAuxiliary' k A B) : AlgebraAuxiliary' k B A := by
  obtain ⟨E, hlin⟩ := h
  haveI := hlin
  exact ⟨E.symm, Equivalence.inverseLinear k E⟩


-- @@ L131-144 verbatim
/-- The auxiliary algebra relation composes through an intermediate algebra. -/
lemma AlgebraAuxiliary'.trans {k : Type*} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    {B : Type u} [Ring B] [Algebra k B]
    {C : Type u} [Ring C] [Algebra k C]
    (h₁ : AlgebraAuxiliary' k A B)
    (h₂ : AlgebraAuxiliary' k B C) : AlgebraAuxiliary' k A C := by
  obtain ⟨E₁, hlin₁⟩ := h₁
  obtain ⟨E₂, hlin₂⟩ := h₂
  haveI := hlin₁
  haveI := hlin₂
  refine ⟨E₁.trans E₂, ?_⟩
  change (E₁.functor ⋙ E₂.functor).Linear k
  infer_instance


-- @@ L146-148 verbatim
end RepresentationTheory.RingAuxiliary

-- Recovered exact-module book alignment.

-- @@ L149-149 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := primary)] _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary

-- @@ L150-150 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := primary)] _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary

-- @@ L151-151 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary'

-- @@ L152-152 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary'.symm

-- @@ L153-153 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary'.toRingAuxiliary

-- @@ L154-154 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary'.trans

-- @@ L155-155 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary.symm

-- @@ L156-156 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary.toRingAuxiliary

-- @@ L157-157 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.AlgebraAuxiliary.trans

-- @@ L158-158 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary'

-- @@ L159-159 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary'.refl

-- @@ L160-160 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary'.symm

-- @@ L161-161 verbatim
attribute [source_ref "Chapter9/Definition9.7.1" (role := supporting)] _root_.RepresentationTheory.RingAuxiliary.RingAuxiliary'.trans
