/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Basic
public import Physlib.Mathematics.Distribution.Basic

-- @@ L10-40 verbatim
/-!

# Lorentz group actions related to SpaceTime

## i. Overview

We already have a Lorentz group action on `SpaceTime d`, in this module
we define the induced action on Schwartz functions and distributions.

## ii. Key results

- `schwartzAction` : Defines the action of the Lorentz group on Schwartz functions.
- An instance of `DistribMulAction` for the Lorentz group acting on distributions.

## iii. Table of contents

- A. Lorentz group action on Schwartz functions
  - A.1. The definition of the action
  - A.2. Basic properties of the action
  - A.3. Injectivity of the action
  - A.4. Surjectivity of the action
- B. Lorentz group action on distributions
  - B.1. The SMul instance
  - B.2. The DistribMulAction instance
  - B.3. The SMulCommClass instance
  - B.4. Action as a linear map

## iv. References

* None.
-/


-- @@ L42-42 verbatim
@[expose] public section

-- @@ L43-43 verbatim
noncomputable section


-- @@ L45-45 verbatim
namespace SpaceTime


-- @@ L47-47 verbatim
open Manifold

-- @@ L48-48 verbatim
open Matrix

-- @@ L49-49 verbatim
open Complex

-- @@ L50-50 verbatim
open ComplexConjugate

-- @@ L51-51 verbatim
open TensorSpecies

-- @@ L52-52 verbatim
open SchwartzMap Physlib

-- @@ L53-53 verbatim
attribute [-simp] Fintype.sum_sum_type


-- @@ L55-59 verbatim
/-!

## A. Lorentz group action on Schwartz functions

-/


-- @@ L61-65 verbatim
/-!

### A.1. The definition of the action

-/


-- @@ L67-86 verbatim
/-- The Lorentz group action on Schwartz functions taking the Lorentz group to
  continuous linear maps. -/
def schwartzAction {d} : LorentzGroup d →* 𝓢(SpaceTime d, ℝ) →L[ℝ] 𝓢(SpaceTime d, ℝ) where
  toFun Λ := SchwartzMap.compCLM (𝕜 := ℝ)
    (Lorentz.Vector.actionCLM Λ⁻¹).hasTemperateGrowth <| by
      use 1, ‖Lorentz.Vector.actionCLM Λ‖
      simp only [pow_one]
      intro x
      obtain ⟨x, rfl⟩ := Lorentz.Vector.actionCLM_surjective Λ x
      apply (ContinuousLinearMap.le_opNorm (Lorentz.Vector.actionCLM Λ) x).trans
      simp [Lorentz.Vector.actionCLM_apply, mul_add]
  map_one' := by
    ext η x
    simp [Lorentz.Vector.actionCLM_apply]
  map_mul' Λ₁ Λ₂ := by
    ext η x
    simp only [_root_.mul_inv_rev, compCLM_apply, Function.comp_apply,
      Lorentz.Vector.actionCLM_apply]
    rw [SemigroupAction.mul_smul]
    rfl


-- @@ L88-92 verbatim
/-!

### A.2. Basic properties of the action

-/


-- @@ L94-98 verbatim
lemma schwartzAction_mul_apply {d} (Λ₁ Λ₂ : LorentzGroup d)
    (η : 𝓢(SpaceTime d, ℝ)) :
    schwartzAction Λ₂ (schwartzAction (Λ₁) η) =
    schwartzAction (Λ₂ * Λ₁) η := by
  simp


-- @@ L100-102 verbatim
lemma schwartzAction_apply {d} (Λ : LorentzGroup d)
    (η : 𝓢(SpaceTime d, ℝ)) (x : SpaceTime d) :
    (schwartzAction Λ η) x = η (Λ⁻¹ • x) := rfl


-- @@ L104-108 verbatim
/-!

### A.3. Injectivity of the action

-/


-- @@ L110-118 verbatim
lemma schwartzAction_injective {d} (Λ : LorentzGroup d) :
    Function.Injective (schwartzAction Λ) := by
  intro η1 η2 h
  ext x
  have h1 : (schwartzAction Λ⁻¹ * schwartzAction Λ) η1 =
    (schwartzAction Λ⁻¹ * schwartzAction Λ) η2 := by simp [h]
  rw [← map_mul] at h1
  simp at h1
  rw [h1]


-- @@ L120-124 verbatim
/-!

### A.4. Surjectivity of the action

-/


-- @@ L126-132 verbatim
lemma schwartzAction_surjective {d} (Λ : LorentzGroup d) :
    Function.Surjective (schwartzAction Λ) := by
  intro η
  use (schwartzAction Λ⁻¹ η)
  change (schwartzAction Λ * schwartzAction Λ⁻¹) η = _
  rw [← map_mul]
  simp


-- @@ L134-138 verbatim
/-!

## B. Lorentz group action on distributions

-/

-- @@ L139-139 verbatim
section Distribution


-- @@ L141-145 verbatim
/-!

### B.1. The SMul instance

-/

-- @@ L146-148 verbatim
variable
    {c : Fin n → realLorentzTensor.Color} {M : Type} [NormedAddCommGroup M]
      [NormedSpace ℝ M] [Tensorial (realLorentzTensor d) c M] [T2Space M]


-- @@ L150-150 verbatim
open Distribution

-- @@ L151-152 expanded
instance : SMul (LorentzGroup d) (Distribution ℝ (SpaceTime d) M) where
  smul Λ f := (Tensorial.actionCLM (realLorentzTensor d) Λ) ∘L f ∘L (schwartzAction Λ⁻¹)


-- @@ L154-155 expanded
lemma lorentzGroup_smul_dist_apply (Λ : LorentzGroup d) (f : Distribution ℝ (SpaceTime d) M)
    (η : 𝓢(SpaceTime d, ℝ)) : (Λ • f) η = Λ • (f (schwartzAction Λ⁻¹ η)) :=
  rfl


-- @@ L157-161 verbatim
/-!

### B.2. The DistribMulAction instance

-/


-- @@ L163-163 verbatim
set_option synthInstance.maxHeartbeats 40000

-- @@ L164-178 expanded
instance : DistribMulAction (LorentzGroup d) (Distribution ℝ (SpaceTime d) M)
    where
  one_smul
    f := by
    ext η
    simp [lorentzGroup_smul_dist_apply]
  mul_smul Λ₁ Λ₂
    f := by
    ext η
    simp [lorentzGroup_smul_dist_apply, SemigroupAction.mul_smul]
  smul_zero
    Λ := by
    ext η
    rw [lorentzGroup_smul_dist_apply]
    simp
  smul_add Λ f1
    f2 := by
    ext η
    rw [lorentzGroup_smul_dist_apply]
    simp only [_root_.add_apply, smul_add, lorentzGroup_smul_dist_apply]


-- @@ L180-184 verbatim
/-!

### B.3. The SMulCommClass instance

-/


-- @@ L186-190 expanded
instance : SMulCommClass ℝ (LorentzGroup d) (Distribution ℝ (SpaceTime d) M) where
  smul_comm a Λ
    f := by
    ext η
    simp [lorentzGroup_smul_dist_apply]
    rw [SMulCommClass.smul_comm]


-- @@ L192-196 verbatim
/-!

### B.4. Action as a linear map

-/


-- @@ L198-209 expanded
/-- The Lorentz action on distributions as a linear map. -/
def distActionLinearMap {d} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [Tensorial (realLorentzTensor d) c M] [T2Space M] (Λ : LorentzGroup d) :
    (Distribution ℝ (SpaceTime d) M) →ₗ[ℝ] (Distribution ℝ (SpaceTime d) M)
    where
  toFun f := Λ • f
  map_add' f1
    f2 := by
    ext η
    simp [lorentzGroup_smul_dist_apply, _root_.add_apply, smul_add]
  map_smul' a
    f := by
    ext η
    simp [lorentzGroup_smul_dist_apply]
    rw [← @smul_comm]


-- @@ L210-210 verbatim
end Distribution

-- @@ L211-211 verbatim
end SpaceTime


-- @@ L213-213 verbatim
end
