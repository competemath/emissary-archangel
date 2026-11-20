/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Mathlib
import Tnorms.Basic.Defs


-- @@ L10-14 verbatim
/-!
TODOs:
  * General proof cleanup
  * File docstring
-/



-- @@ L17-17 verbatim
variable {M : Type*} [CompleteLinearOrder M] [UniformSpace M] [Tnorm M] [IsFuzzyLogic M]

-- @@ L18-18 verbatim
variable {X : Type*} [UniformSpace X]


-- @@ L20-23 expanded
open Classical in
noncomputable abbrev PC_Imp (f : X → M) (U : Set (X × X)) : X → X → M := fun x y ↦
  if (x, y) ∈ U then LImp ((f x) * 1) (f y) else LImp ((f x) * 0) (f y)


-- @@ L25-27 verbatim
noncomputable
abbrev PrincipleOfCharity (f : X → M) (U : Set (X × X)) : M :=
  sInf (Set.range (Function.uncurry (PC_Imp f U)))


-- @@ L29-30 verbatim
def PrincipleOfCharityAlmostTrue (f : X → M) : Prop :=
  ∀ p < (1 : M), ∃ U ∈ uniformity X, p ≤ PrincipleOfCharity f U


-- @@ L32-37 verbatim
def IsCharitableOn (X M : Type*) [UniformSpace X]
    [CompleteLinearOrder M] [UniformSpace M] [Tnorm M] [IsFuzzyLogic M] : Prop :=
  ∀ f : X → M, UniformContinuous f → PrincipleOfCharityAlmostTrue f


-- Proposition 1

-- @@ L38-52 verbatim
omit [UniformSpace X] [IsFuzzyLogic M] in
theorem poc_anti (f : X → M) : Antitone (PrincipleOfCharity f) := by
  intro U V h
  simp [PrincipleOfCharity]
  intro p x y hp
  subst hp
  by_cases hU : (x, y) ∈ U
  · refine sInf_le ?_
    simp [PC_Imp]
    have hV : (x, y) ∈ V := h hU
    grind
  · simp [PC_Imp, le_one, hU]


-- Theorem 8

-- @@ L53-76 verbatim
theorem charitableOn_of_charitableOn {M N : Type*}
    [CompleteLinearOrder M] [CompleteLinearOrder N]
    [UniformSpace M] [UniformSpace N]
    [Tnorm M] [Tnorm N]
    [IsFuzzyLogic M] [IsFuzzyLogic N] (e : M ≃*o N) (h : IsCharitableOn X M) :
    IsCharitableOn X N := by
  intro f hf
  let g : X → M := e.symm ∘ f
  have hug := UniformContinuous.comp (CompactSpace.uniformContinuous_of_continuous
    (OrderIso.continuous e.symm.toOrderIso)) hf

  intro p hp
  specialize h g hug (e.symm p) ?_
  · rw [← map_one e.symm, map_lt_map_iff]
    exact hp
  obtain ⟨U, hU, h⟩ := h
  use U
  constructor; exact hU
  unfold PrincipleOfCharity at h ⊢
  rw [← le_map_inv_iff] at h
  simp [PC_Imp] at h ⊢
  simp_rw [apply_ite e, map_LImp] at h
  simp [g] at h
  exact h


-- @@ L78-86 verbatim
theorem charitableOn_iff_charitableOn {M N : Type*}
    [CompleteLinearOrder M] [CompleteLinearOrder N]
    [UniformSpace M] [UniformSpace N]
    [Tnorm M] [Tnorm N]
    [IsFuzzyLogic M] [IsFuzzyLogic N] (e : M ≃*o N) :
    IsCharitableOn X M ↔ IsCharitableOn X N := by
  constructor
  · exact charitableOn_of_charitableOn e
  · exact charitableOn_of_charitableOn e.symm


-- @@ L88-91 verbatim
lemma charitableOn_of_subsingleton [Subsingleton M] : IsCharitableOn X M := by
  intro f hf p hp
  use Set.univ
  simp
