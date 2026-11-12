/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Batteries.Util.ProofWanted
import RepresentationTheory.Algebra.Lie.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L14-14 verbatim
/-! # Auxiliary injectivity and existence equivalences -/


-- @@ L16-16 verbatim
namespace RepresentationTheory.Algebra.Lie.InjectivityExistenceAuxiliary


-- @@ L18-18 verbatim
universe u


-- @@ L20-20 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L22-22 verbatim
variable (k : Type u) [Field k]

-- @@ L23-23 verbatim
variable (L : Type u) [LieRing L] [LieAlgebra k L]


-- @@ L25-32 verbatim
/-- An injective Lie homomorphism into a finite-dimensional algebra yields the displayed existential data with an injective map. -/
theorem auxiliary_exists_of_injective_lieHom {A : Type u} [Ring A] [Algebra k A]
    [FiniteDimensional k A] (f : L →ₗ⁅k⁆ A) (hf : Function.Injective f) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ := by
  refine ⟨A, inferInstance, inferInstance, inferInstance,
    (Algebra.lmul k A).toLieHom.comp f, ?_⟩
  exact Algebra.lmul_injective.comp hf


-- @@ L34-42 verbatim
/-- An algebra homomorphism from the universal enveloping algebra that is injective on the displayed Lie image yields the displayed existential data. -/
theorem auxiliary_exists_of_envelopingMap_injective {A : Type u} [Ring A] [Algebra k A]
    [FiniteDimensional k A]
    (q : UniversalEnvelopingAlgebra k L →ₐ[k] A)
    (hq : Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x))) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ := by
  exact auxiliary_exists_of_injective_lieHom k L
    (q.toLieHom.comp (UniversalEnvelopingAlgebra.ι k)) hq


-- @@ L44-55 verbatim
/-- An injective Lie homomorphism into endomorphisms of a finite-dimensional module yields the displayed algebraic data with injectivity on the displayed Lie image. -/
theorem auxiliary_exists_envelopingMap_injective_of_injective_lieHom
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : L →ₗ⁅k⁆ Module.End k V) (hρ : Function.Injective ρ) :
    ∃ (A : Type u) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
      (q : UniversalEnvelopingAlgebra k L →ₐ[k] A),
        Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x)) := by
  refine ⟨Module.End k V, inferInstance, inferInstance, inferInstance,
    UniversalEnvelopingAlgebra.lift k ρ, ?_⟩
  intro x y hxy
  apply hρ
  simpa using hxy


-- @@ L57-68 verbatim
/-- The first displayed existential statement is equivalent to the existence of algebraic data whose map is injective on the displayed Lie image. -/
theorem auxiliary_exists_iff_exists_envelopingMap_injective :
    (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
        (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ) ↔
      ∃ (A : Type u) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
        (q : UniversalEnvelopingAlgebra k L →ₐ[k] A),
          Function.Injective (fun x : L ↦ q (UniversalEnvelopingAlgebra.ι k x)) := by
  constructor
  · rintro ⟨V, _, _, _, ρ, hρ⟩
    exact auxiliary_exists_envelopingMap_injective_of_injective_lieHom k L ρ hρ
  · rintro ⟨A, _, _, _, q, hq⟩
    exact auxiliary_exists_of_envelopingMap_injective k L q hq


-- @@ L70-72 verbatim
proof_wanted ado [FiniteDimensional k L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (ρ : L →ₗ⁅k⁆ Module.End k V), Function.Injective ρ


-- @@ L74-76 verbatim
end RepresentationTheory.Algebra.Lie.InjectivityExistenceAuxiliary

-- Recovered additional exact-module book alignment.

-- @@ L77-77 verbatim
attribute [source_ref "Chapter2/Remark2.9.3" (role := supporting)] _root_.RepresentationTheory.Algebra.Lie.InjectivityExistenceAuxiliary.auxiliary_exists_envelopingMap_injective_of_injective_lieHom

-- @@ L78-78 verbatim
attribute [source_ref "Chapter2/Remark2.9.3" (role := supporting)] _root_.RepresentationTheory.Algebra.Lie.InjectivityExistenceAuxiliary.auxiliary_exists_iff_exists_envelopingMap_injective

-- @@ L79-79 verbatim
attribute [source_ref "Chapter2/Remark2.9.3" (role := supporting)] _root_.RepresentationTheory.Algebra.Lie.InjectivityExistenceAuxiliary.auxiliary_exists_of_envelopingMap_injective

-- @@ L80-80 verbatim
attribute [source_ref "Chapter2/Remark2.9.3" (role := supporting)] _root_.RepresentationTheory.Algebra.Lie.InjectivityExistenceAuxiliary.auxiliary_exists_of_injective_lieHom
