/-
Copyright (c) 2026 Zachary Feng, Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Feng, Y. Samanda Zhang
-/
module

public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop


-- @@ L10-16 verbatim
/-!
# Compatibility aliases for the original odd-representation namespace

The maintained proof of the odd-representation irreducibility criterion now lives in
`FLT.Slop.RepresentationTheory.OddAbsIrredSlop`, under `Slop.OddRep`.  This file keeps the old
`Slop.OddRepOrig` names available without recompiling a duplicate copy of the same proofs.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open scoped TensorProduct


-- @@ L22-22 verbatim
open Module


-- @@ L24-24 verbatim
namespace Slop

-- @@ L25-25 verbatim
namespace OddRepOrig


-- @@ L27-27 verbatim
variable {k : Type*} [Field k]

-- @@ L28-28 verbatim
variable {G : Type*} [Monoid G]

-- @@ L29-29 verbatim
variable {V : Type*} [AddCommGroup V] [Module k V]


-- @@ L31-34 verbatim
/-- Compatibility alias for `Slop.OddRep.baseChange`. -/
noncomputable abbrev baseChange (l : Type*) [Field l] [Algebra k l]
    (ρ : Representation k G V) : Representation l G (l ⊗[k] V) :=
  _root_.Slop.OddRep.baseChange l ρ


-- @@ L36-38 verbatim
/-- Compatibility alias for `Slop.OddRep.adjoinRange`. -/
abbrev adjoinRange (ρ : Representation k G V) : Subalgebra k (Module.End k V) :=
  _root_.Slop.OddRep.adjoinRange ρ


-- @@ L40-42 verbatim
/-- Compatibility alias for `Slop.OddRep.IsAbsolutelyIrreducible`. -/
abbrev IsAbsolutelyIrreducible (ρ : Representation k G V) : Prop :=
  _root_.Slop.OddRep.IsAbsolutelyIrreducible ρ


-- @@ L44-48 verbatim
lemma isIrreducible_iff_forall (ρ : Representation k G V) :
    ρ.IsIrreducible ↔
      Nontrivial V ∧
        ∀ W : Submodule k V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ :=
  _root_.Slop.OddRep.isIrreducible_iff_forall ρ


-- @@ L50-54 verbatim
lemma smul_tmul_mem_range_iff (l : Type*) [Field l] [Algebra k l]
    {e : V} (he : e ≠ 0) (c : l) :
    c ⊗ₜ[k] e ∈ LinearMap.range (TensorProduct.mk k l V 1) ↔
      ∃ a : k, algebraMap k l a = c :=
  _root_.Slop.OddRep.smul_tmul_mem_range_iff l he c


-- @@ L56-62 verbatim
lemma exists_smul_eq_of_commute
    (ρ : Representation k G V)
    (hirr : ρ.IsIrreducible)
    {g : G} (hg : finrank k (Module.End.eigenspace (ρ g) 1) = 1)
    (T : Module.End k V) (hT : ∀ h : G, Commute (ρ h) T) :
    ∃ μ : k, T = μ • (1 : Module.End k V) :=
  _root_.Slop.OddRep.exists_smul_eq_of_commute ρ hirr hg T hT


-- @@ L64-69 verbatim
lemma adjoinRange_eq_top (ρ : Representation k G V) [FiniteDimensional k V]
    (hirr : ρ.IsIrreducible)
    (hEnd : ∀ T : Module.End k V, (∀ h : G, Commute (ρ h) T) →
      ∃ μ : k, T = μ • (1 : Module.End k V)) :
    adjoinRange ρ = ⊤ :=
  _root_.Slop.OddRep.adjoinRange_eq_top ρ hirr hEnd


-- @@ L71-75 verbatim
lemma adjoinRange_baseChange_eq_top (ρ : Representation k G V) [FiniteDimensional k V]
    (l : Type*) [Field l] [Algebra k l]
    (h : adjoinRange ρ = ⊤) :
    adjoinRange (baseChange l ρ) = ⊤ :=
  _root_.Slop.OddRep.adjoinRange_baseChange_eq_top ρ l h


-- @@ L77-80 verbatim
lemma isIrreducible_of_adjoinRange_eq_top (ρ : Representation k G V) [Nontrivial V]
    (h : adjoinRange ρ = ⊤) :
    ρ.IsIrreducible :=
  _root_.Slop.OddRep.isIrreducible_of_adjoinRange_eq_top ρ h


-- @@ L82-86 verbatim
lemma isIrreducible_of_baseChange (ρ : Representation k G V)
    (l : Type*) [Field l] [Algebra k l]
    (h : (baseChange l ρ).IsIrreducible) :
    ρ.IsIrreducible :=
  _root_.Slop.OddRep.isIrreducible_of_baseChange ρ l h


-- @@ L88-94 verbatim
theorem isIrreducible_baseChange_of_finrank_eigenspace_eq_one
    (ρ : Representation k G V) [FiniteDimensional k V]
    (l : Type*) [Field l] [Algebra k l]
    (hirr : ρ.IsIrreducible)
    {g : G} (hg : finrank k (Module.End.eigenspace (ρ g) 1) = 1) :
    (baseChange l ρ).IsIrreducible :=
  _root_.Slop.OddRep.isIrreducible_baseChange_of_finrank_eigenspace_eq_one ρ l hirr hg


-- @@ L96-100 verbatim
theorem isIrreducible_iff_isAbsolutelyIrreducible
    (ρ : Representation k G V) [FiniteDimensional k V]
    {g : G} (hg : finrank k (Module.End.eigenspace (ρ g) 1) = 1) :
    ρ.IsIrreducible ↔ IsAbsolutelyIrreducible ρ :=
  _root_.Slop.OddRep.isIrreducible_iff_isAbsolutelyIrreducible_slop ρ hg


-- @@ L102-102 verbatim
end OddRepOrig

-- @@ L103-103 verbatim
end Slop
