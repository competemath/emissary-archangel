/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Completion


-- @@ L11-15 verbatim
/-!
# Infinite Adele Ring

Material destined for Mathlib.
-/


-- @@ L17-19 verbatim
@[expose] public section

-- TODO upstream

-- @@ L20-20 verbatim
variable (K : Type*) [Field K]


-- @@ L22-22 verbatim
open NumberField InfinitePlace


-- @@ L24-26 verbatim
@[simp]
lemma NumberField.InfiniteAdeleRing.mul_apply (x y : InfiniteAdeleRing K) (v : InfinitePlace K) :
    (x * y) v = x v * y v := rfl


-- @@ L28-29 verbatim
instance : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs <| T2Space (Π _, _)


-- @@ L31-33 verbatim
variable [NumberField K] in
instance : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs <| SecondCountableTopology (Π _, _)


-- @@ L35-37 verbatim
/-- The ℝ algebra structure on InfiniteAdeleRing K. -/
noncomputable instance : Algebra ℝ (InfiniteAdeleRing K) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K|>.symm.toRingHom.comp (algebraMap ℝ _)).toAlgebra


-- @@ L39-47 verbatim
/-- If `K` is a number field, this is the ℝ-linear iso between ∏_v|∞ K_v and ℝ^r × ℂ^s,
with the usual notation. -/
noncomputable def NumberField.InfiniteAdeleRing.algEquivMixedSpace :
    InfiniteAdeleRing K ≃ₗ[ℝ] (mixedEmbedding.mixedSpace K) := LinearEquiv.symm {
  __ := (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
  map_smul' m x := by
    rw [Algebra.smul_def]
    exact map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm _ _
    }


-- @@ L49-53 verbatim
variable [NumberField K] in
instance : Module.Finite ℝ (InfiniteAdeleRing K) :=
  Module.Finite.equiv (NumberField.InfiniteAdeleRing.algEquivMixedSpace K).symm

-- should be elsewhere

-- @@ L54-54 verbatim
instance : IsModuleTopology ℝ ℂ := .iso Complex.equivRealProdCLM.symm


-- @@ L56-86 verbatim
/-- If `K` is a number field, this is the continuous ℝ-linear iso between ∏_v|∞ K_v and ℝ^r × ℂ^s,
with the usual notation. -/
noncomputable def NumberField.InfiniteAdeleRing.continuousAlgEquivMixedSpace :
    InfiniteAdeleRing K ≃L[ℝ] (mixedEmbedding.mixedSpace K)  where
  __ := NumberField.InfiniteAdeleRing.algEquivMixedSpace K
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      rintro ⟨v, hv⟩
      change Continuous fun (a : InfiniteAdeleRing K) ↦
        (Completion.isometryEquivRealOfIsReal hv) (a v)
      fun_prop
    · apply continuous_pi
      rintro ⟨v, hv⟩
      change Continuous fun (a : InfiniteAdeleRing K) ↦
        (Completion.isometryEquivComplexOfIsComplex hv) (a v)
      fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro v
    classical
    change Continuous fun (a : mixedEmbedding.mixedSpace K) ↦ if h : v.IsReal then _ else _
    split_ifs with h
    · let f : v.Completion ≃+* ℝ := Completion.ringEquivRealOfIsReal h
      change Continuous fun (a : mixedEmbedding.mixedSpace K) ↦
        (Completion.isometryEquivRealOfIsReal h).symm (a.1 ⟨v, h⟩)
      fun_prop
    · rw [NumberField.InfinitePlace.not_isReal_iff_isComplex] at h
      change Continuous fun (a : mixedEmbedding.mixedSpace K) ↦
        (Completion.isometryEquivComplexOfIsComplex h).symm (a.2 ⟨v, h⟩)
      fun_prop


-- @@ L88-90 verbatim
variable [NumberField K] in
instance : IsModuleTopology ℝ (InfiniteAdeleRing K) :=
  .iso (NumberField.InfiniteAdeleRing.continuousAlgEquivMixedSpace K).symm


-- @@ L92-101 verbatim
/-- The continuous `ℤ`-algebra isomorphism between `Rat.infinitePlace.Completion` and `ℝ`.
(We use continuous `ℤ`-algebra equivalences in place of continuous ring equivalences
since we don't have the latter.) -/
noncomputable def Rat.infinitePlaceCompletionContinuousAlgEquiv :
    Rat.infinitePlace.Completion ≃A[ℤ] ℝ :=
  {
    __ := (Completion.isometryEquivRealOfIsReal isReal_infinitePlace).toHomeomorph
    __ := Completion.ringEquivRealOfIsReal isReal_infinitePlace
    commutes' := by simp [Completion.isometryEquivRealOfIsReal]
  }


-- @@ L103-105 verbatim
lemma Rat.infinitePlace_completion_continuousAlgEquiv_apply_algebraMap (x : ℚ) :
    infinitePlaceCompletionContinuousAlgEquiv
      (algebraMap ℚ infinitePlace.Completion x) = (x : ℝ) := by simp
