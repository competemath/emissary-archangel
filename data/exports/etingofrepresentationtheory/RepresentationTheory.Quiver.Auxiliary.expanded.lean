/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.QuiverRepresentation.VertexCompositionSeries
import RepresentationTheory.Alignment.Attribute


-- @@ L12-14 verbatim
/-!
# Auxiliary constructions for quiver representations
-/


-- @@ L16-16 verbatim
namespace RepresentationTheory.Quiver.Auxiliary


-- @@ L18-18 verbatim
open Module


-- @@ L20-20 verbatim
variable {k Q : Type*} [Field k] [Quiver Q]


-- @@ L22-26 verbatim
/-- The additive commutative group structure induced on a module over a field. -/
@[reducible]
noncomputable def addCommGroupOfModule {M : Type*} [inst : AddCommMonoid M] [Module k M] :
    AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup k


-- @@ L28-31 verbatim
/-- Maps a vertex to an opaque value parameterized by a field and a quiver. -/
abbrev auxiliaryObjectAtVertex [DecidableEq Q] (i : Q) :
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q :=
  RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.representationAtVertex i


-- @@ L33-34 verbatim
/-- The second auxiliary predicate on a vertex of a quiver. -/
def auxiliaryVertexPropertyTwo (i : Q) : Prop := ∀ j, IsEmpty (j ⟶ i)


-- @@ L36-37 verbatim
/-- The first auxiliary predicate on a vertex of a quiver. -/
def auxiliaryVertexPropertyOne (i : Q) : Prop := ∀ j, IsEmpty (i ⟶ j)


-- @@ L39-46 verbatim
/-- An auxiliary construction whose elaborated type is unavailable in this interface. -/
noncomputable def auxiliaryElidedDefinition
    (V W : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) :
    (∀ i, V.obj i →ₗ[k] W.obj i) →
      (∀ p : (Σ i j, (i ⟶ j)), V.obj p.1 →ₗ[k] W.obj p.2.1) :=
  fun f p =>
    letI : AddCommGroup (W.obj p.2.1) := addCommGroupOfModule (k := k)
    W.map p.2.2 ∘ₗ f p.1 - f p.2.1 ∘ₗ V.map p.2.2


-- @@ L48-51 verbatim
/-- A binary proposition on two opaque values parameterized by a field and a quiver. -/
def auxiliaryRelation
    (V W : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) : Prop :=
  Function.Surjective (auxiliaryElidedDefinition V W)


-- @@ L53-71 verbatim
/--
At a vertex satisfying the second distinguished property, every value of the displayed
quiver-indexed type is related to its associated auxiliary object.
-/
@[source_ref "Chapter6/Problem6.9.3" (role := supporting)]
theorem any_relates_to_auxiliaryObjectAtVertex [DecidableEq Q]
    (i : Q) (hi : auxiliaryVertexPropertyTwo i)
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) :
    auxiliaryRelation V (auxiliaryObjectAtVertex i) := by
  intro g
  refine ⟨0, funext fun p => ?_⟩
  have hbne : p.2.1 ≠ i := by
    intro h
    exact (hi p.1).elim (h ▸ p.2.2)
  have hsub : Subsingleton ((auxiliaryObjectAtVertex (k := k) i).obj p.2.1) := by
    change Subsingleton (Fin (if p.2.1 = i then 1 else 0) → k)
    rw [if_neg hbne]
    exact ⟨fun a b => funext fun x => x.elim0⟩
  exact LinearMap.ext fun x => hsub.elim _ _


-- @@ L73-91 verbatim
/--
At a vertex satisfying the first distinguished property, its associated auxiliary object is
related to every value of the displayed quiver-indexed type.
-/
@[source_ref "Chapter6/Problem6.9.3" (role := supporting)]
theorem auxiliaryObjectAtVertex_relates_to_any [DecidableEq Q]
    (i : Q) (hi : auxiliaryVertexPropertyOne i)
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q) :
    auxiliaryRelation (auxiliaryObjectAtVertex i) V := by
  intro g
  refine ⟨0, funext fun p => ?_⟩
  have hane : p.1 ≠ i := by
    intro h
    exact (hi p.2.1).elim (h ▸ p.2.2)
  have hsub : Subsingleton ((auxiliaryObjectAtVertex (k := k) i).obj p.1) := by
    change Subsingleton (Fin (if p.1 = i then 1 else 0) → k)
    rw [if_neg hane]
    exact ⟨fun a b => funext fun x => x.elim0⟩
  exact LinearMap.ext fun x => by rw [hsub.elim x 0, map_zero, map_zero]


-- @@ L93-97 verbatim
/-- A natural-number-valued function on the vertices associated with an opaque value. -/
noncomputable def auxiliaryVertexValue
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (i : Q) : ℕ :=
  finrank k (V.obj i)


-- @@ L99-104 verbatim
/-- Under the displayed finite-basis hypothesis, the auxiliary value at a vertex equals the supplied natural number. -/
theorem auxiliaryVertexValue_eq_of_fin_basis
    {Vα : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q}
    {α : Q → ℕ} (basis : ∀ v, Basis (Fin (α v)) k (Vα.obj v)) (v : Q) :
    auxiliaryVertexValue Vα v = α v := by
  rw [auxiliaryVertexValue, Module.finrank_eq_card_basis (basis v), Fintype.card_fin]


-- @@ L106-121 verbatim
/-- Under the displayed ordering and finite-basis hypotheses, there is auxiliary data satisfying the two stated equalities. -/
@[source_ref "Chapter6/Problem6.9.3" (role := supporting),
  source_ref "Chapter6/Section6.9_heading" (role := supporting)]
theorem existsAuxiliaryDataWithVertexValues [DecidableEq Q]
    (Vα : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k Q)
    (n : ℕ) (order : Q ≃ Fin n)
    (horder : ∀ {v w : Q}, (v ⟶ w) → (order w : ℕ) < (order v : ℕ))
    (α : Q → ℕ) (basis : ∀ v, Basis (Fin (α v)) k (Vα.obj v)) :
    ∃ s : RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.VertexCompositionSeries Vα,
      s.length = ∑ l : Fin n, α (order.symm l) ∧
        ∀ i, s.multiplicity i = auxiliaryVertexValue Vα i := by
  obtain ⟨s, hlen, hmult⟩ :=
    RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.exists_vertexCompositionSeries_with_multiplicity
      Vα n order horder α basis
  exact ⟨s, hlen, fun i => (hmult i).trans
    (auxiliaryVertexValue_eq_of_fin_basis basis i).symm⟩


-- @@ L123-123 verbatim
end RepresentationTheory.Quiver.Auxiliary


-- @@ L125-126 verbatim
/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.Auxiliary.Auxiliary.statement013184 := _root_.RepresentationTheory.Quiver.Auxiliary.auxiliaryElidedDefinition
