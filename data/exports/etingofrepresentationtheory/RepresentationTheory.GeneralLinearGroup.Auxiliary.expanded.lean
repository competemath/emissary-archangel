/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
namespace RepresentationTheory.GeneralLinearGroup.Auxiliary


-- @@ L12-13 verbatim
/-- An auxiliary family of index types parametrized by a natural number. -/
abbrev AuxiliaryIndex (n : ℕ) := (Fin n × Fin n) ⊕ Unit


-- @@ L15-22 verbatim
/-- An auxiliary scalar-valued operation on a general linear group element and a multivariable polynomial. -/
noncomputable def auxiliaryPolynomialEvaluation {k : Type*} [Field k] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (p : MvPolynomial (AuxiliaryIndex n) k) : k :=
  MvPolynomial.eval
    (Sum.elim (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2)
              (fun _ => ((g : Matrix (Fin n) (Fin n) k).det)⁻¹))
    p


-- @@ L24-34 verbatim
/-- An auxiliary property of maps from a general linear group to linear endomorphisms. -/
@[source_ref "Chapter5/Definition5.23.1" (role := supporting)]
def HasAuxiliaryMapProperty
    {k : Type*} [Field k]
    (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k Y)
    (P : Fin m → Fin m → MvPolynomial (AuxiliaryIndex n) k),
    ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (a c : Fin m),
      b.repr (ρ g (b c)) a = auxiliaryPolynomialEvaluation g (P a c)


-- @@ L36-43 verbatim
/-- An auxiliary property of finite-dimensional representations of a general linear group. -/
@[source_ref "Chapter5/Definition5.23.1" (role := supporting)]
def HasAuxiliaryRepresentationProperty
    {k : Type*} [Field k]
    (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y) : Prop :=
  HasAuxiliaryMapProperty n (fun g => ρ g)


-- @@ L45-53 verbatim
/-- The auxiliary representation property is equivalent to the auxiliary map property for its underlying function. -/
@[source_ref "Chapter5/Definition5.23.1" (role := supporting)]
theorem auxiliaryRepresentationProperty_iff_mapProperty
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y) :
    HasAuxiliaryRepresentationProperty n ρ ↔
      HasAuxiliaryMapProperty n (fun g => ρ g) :=
  Iff.rfl


-- @@ L55-61 verbatim
/-- The auxiliary map property for the underlying function of a representation implies the auxiliary representation property. -/
theorem HasAuxiliaryMapProperty.impliesRepresentationProperty
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y}
    (h : HasAuxiliaryMapProperty n (fun g => ρ g)) :
    HasAuxiliaryRepresentationProperty n ρ := h


-- @@ L63-79 verbatim
/-- There exists a map with the auxiliary property whose value at the identity is not the identity linear map. -/
@[source_ref "Chapter5/Definition5.23.1" (role := supporting)]
theorem exists_auxiliaryMap_ne_id_at_one
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [Nontrivial Y] :
    ∃ ρ : Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y,
      HasAuxiliaryMapProperty n ρ ∧ ρ 1 ≠ LinearMap.id := by
  classical
  refine ⟨fun _ => 0, ?_, ?_⟩
  · refine ⟨_, Module.finBasis k Y, fun _ _ => 0, fun g a c => ?_⟩
    simp [auxiliaryPolynomialEvaluation]
  · intro h
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    have hz := congrArg (fun f : Y →ₗ[k] Y => f y) h
    simp only [LinearMap.zero_apply, LinearMap.id_apply] at hz
    exact hy hz.symm


-- @@ L81-81 verbatim
end RepresentationTheory.GeneralLinearGroup.Auxiliary
