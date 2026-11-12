/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.InductionAndCoinduction
import RepresentationTheory.AuxiliaryUnavailableStatement
import RepresentationTheory.Alignment.Attribute


-- @@ L12-16 verbatim
/-!
# Auxiliary Unavailable Statement

An auxiliary trace identity in the nested `RepresentationTheory.Auxiliary` namespace.
-/


-- @@ L18-18 verbatim
open Representation

-- @@ L19-19 verbatim
open scoped TensorProduct


-- @@ L21-35 verbatim
/-- Auxiliary theorem. -/
theorem RepresentationTheory.Auxiliary.UnavailableStatement.auxiliary
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H V)
    (g : G) :
    LinearMap.trace ℂ (Representation.IndV H.subtype ρ)
        (RepresentationTheory.InductionAndCoinduction.finiteIndexInduced H ρ g)
      = (Fintype.card H : ℂ)⁻¹ *
          ∑ x : G,
            if h : x * g * x⁻¹ ∈ H then
              LinearMap.trace ℂ V (ρ ⟨x * g * x⁻¹, h⟩)
            else 0 :=
  RepresentationTheory.AuxiliaryUnavailableStatement.auxiliary_theorem H ρ g


-- @@ L37-38 verbatim
/-- An auxiliary statement whose displayed formal type is unavailable. -/
alias _root_.RepresentationTheory.Auxiliary.UnavailableStatement.Auxiliary.statement015437 := _root_.RepresentationTheory.Auxiliary.UnavailableStatement.auxiliary


-- @@ L40-40 verbatim
attribute [source_ref "Chapter5/Remark5.9.2" (role := supporting)] _root_.RepresentationTheory.Auxiliary.UnavailableStatement.Auxiliary.statement015437
