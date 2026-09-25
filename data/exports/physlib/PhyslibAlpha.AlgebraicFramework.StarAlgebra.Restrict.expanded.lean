/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.SelfAdjoint


-- @@ L11-18 verbatim
/-!

# Restriction of unital positive linear maps to submodules

We define restriction of positive and unital positive linear maps to
submodules, in particular to self-adjoint elements.

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
section Restrict


-- @@ L24-29 verbatim
variable {R S E₁ E₂ : Type*}
    [Semiring R] [Semiring S]
    [AddCommMonoid E₁] [AddCommMonoid E₂]
    [PartialOrder E₁] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [Module S E₁] [Module S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R]


-- @@ L31-36 verbatim
/-- Restrict a positive linear map to submodules it preserves. -/
@[simps!]
def PositiveLinearMap.restrict (f : E₁ →ₚ[R] E₂) {F₁ : Submodule S E₁} {F₂ : Submodule S E₂}
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : F₁ →ₚ[S] F₂ where
  toLinearMap := (f.toLinearMap.restrictScalars S).restrict (by simpa)
  monotone' a b h := f.monotone (by simpa)


-- @@ L38-38 verbatim
variable [One E₁] [One E₂]


-- @@ L40-48 expanded
/-- Restrict a unital positive linear map to submodules it preserves. -/
@[simps! apply]
def UnitalPositiveLinearMap.restrict (f : UnitalPositiveLinearMap R E₁ E₂) {F₁ : Submodule S E₁}
    {F₂ : Submodule S E₂} [One F₁] [One F₂] (h₁ : ↑(1 : F₁) = (1 : E₁)) (h₂ : ↑(1 : F₂) = (1 : E₂))
    (h : ∀ ⦃x⦄, x ∈ F₁ → f x ∈ F₂) : UnitalPositiveLinearMap S F₁ F₂
    where
  toPositiveLinearMap := f.toPositiveLinearMap.restrict h
  map_one' := by
    ext
    simp [h₁, h₂]


-- @@ L50-50 verbatim
end Restrict


-- @@ L52-52 verbatim
section SelfAdjoint


-- @@ L54-54 verbatim
variable {A₁ A₂ : Type*}


-- @@ L56-58 verbatim
namespace PositiveLinearMap

-- `IsSelfAdjoint.map` needs Mathlib's `StarHomClass` instance for positive linear maps.

-- @@ L59-65 verbatim
variable
    [AddCommGroup A₁] [PartialOrder A₁] [StarAddMonoid A₁]
    [NonUnitalRing A₂] [PartialOrder A₂] [StarRing A₂]
    [SelfAdjointDecompose A₁]
    [Module ℂ A₁] [Module ℂ A₂]
    [StarModule ℂ A₁] [StarModule ℂ A₂]
    [StarOrderedRing A₂]


-- @@ L67-67 verbatim
open selfAdjoint


-- @@ L69-72 verbatim
/-- A positive linear map induces a positive real-linear map on self-adjoint elements. -/
noncomputable def restrictSA (f : A₁ →ₚ[ℂ] A₂) : selfAdjoint A₁ →ₚ[ℝ] selfAdjoint A₂ :=
  submodulePLM.comp <|
    (f.restrict (by simp_all [IsSelfAdjoint.map])).comp <| submodulePLMSymm ℝ


-- @@ L74-77 verbatim
@[simp, norm_cast]
lemma coe_restrictSA_apply (f : A₁ →ₚ[ℂ] A₂) (x : selfAdjoint A₁) :
    ↑(f.restrictSA x) = f ↑x := by
  simp [restrictSA]


-- @@ L79-79 verbatim
section Complex


-- @@ L81-81 verbatim
open Complex ComplexOrder ComplexConjugate


-- @@ L83-86 verbatim
/-- A positive complex-linear functional induces a positive real-linear functional on
self-adjoint elements. -/
noncomputable def restrictSAC (f : A₁ →ₚ[ℂ] ℂ) : selfAdjoint A₁ →ₚ[ℝ] ℝ :=
  Complex.selfAdjointUPLM.toPositiveLinearMap.comp f.restrictSA


-- @@ L88-94 verbatim
@[simp, norm_cast]
lemma coe_restrictSAC_apply (f : A₁ →ₚ[ℂ] ℂ) (x : selfAdjoint A₁) :
    (f.restrictSAC x : ℂ) = f (x : A₁) := by
  have : conj (f x) = f x := by
    rw [← star_def, ← isSelfAdjoint_iff]
    exact IsSelfAdjoint.map isSelfAdjoint f
  simpa [restrictSAC] using (conj_eq_iff_re.mp this)


-- @@ L96-96 verbatim
end Complex


-- @@ L98-98 verbatim
end PositiveLinearMap


-- @@ L100-100 verbatim
namespace UnitalPositiveLinearMap


-- @@ L102-108 verbatim
variable
    [Ring A₁] [PartialOrder A₁] [StarRing A₁]
    [Ring A₂] [PartialOrder A₂] [StarRing A₂]
    [SelfAdjointDecompose A₁]
    [Module ℂ A₁] [Module ℂ A₂]
    [StarModule ℂ A₁] [StarModule ℂ A₂]
    [StarOrderedRing A₂]


-- @@ L110-110 verbatim
open selfAdjoint


-- @@ L112-112 expanded
variable (f : UnitalPositiveLinearMap ℂ A₁ A₂)


-- @@ L114-119 expanded
/-- A unital positive linear map induces a unital positive real-linear map on
self-adjoint elements. -/
noncomputable def restrictSA (f : UnitalPositiveLinearMap ℂ A₁ A₂) :
    UnitalPositiveLinearMap ℝ (selfAdjoint A₁) (selfAdjoint A₂) :=
  submoduleUPLM.comp <|
    (f.restrict val_one val_one (by simp_all [IsSelfAdjoint.map])).comp <| submoduleUPLMSymm ℝ


-- @@ L121-125 expanded
@[simp, norm_cast]
lemma coe_restrictSA_apply (f : UnitalPositiveLinearMap ℂ A₁ A₂) (x : selfAdjoint A₁) :
    ↑(f.restrictSA x) = f ↑x :=
  by
  change f ↑((submoduleEquiv (R := ℝ) (A := A₁)).symm x) = f ↑x
  exact congrArg f (submoduleEquiv_symm_apply_coe x)


-- @@ L127-127 verbatim
open Complex ComplexOrder ComplexConjugate


-- @@ L129-132 expanded
/-- A unital positive complex-linear functional induces a unital positive real-linear functional
on self-adjoint elements. -/
noncomputable def restrictSAC (f : UnitalPositiveLinearMap ℂ A₁ ℂ) :
    UnitalPositiveLinearMap ℝ (selfAdjoint A₁) ℝ :=
  Complex.selfAdjointUPLM.comp f.restrictSA


-- @@ L134-140 expanded
@[simp, norm_cast]
lemma coe_restrictSAC_apply (f : UnitalPositiveLinearMap ℂ A₁ ℂ) (x : selfAdjoint A₁) :
    (f.restrictSAC x : ℂ) = f (x : A₁) :=
  by
  have : conj (f x) = f x := by
    rw [← star_def, ← isSelfAdjoint_iff]
    exact IsSelfAdjoint.map isSelfAdjoint f
  simpa [restrictSAC] using (conj_eq_iff_re.mp this)


-- @@ L142-142 verbatim
end UnitalPositiveLinearMap


-- @@ L144-144 verbatim
end SelfAdjoint
