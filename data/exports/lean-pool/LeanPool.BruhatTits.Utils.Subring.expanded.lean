/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Module

-- @@ L12-14 verbatim
/-!
# LeanPool.BruhatTits.Utils.Subring
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open Module


-- @@ L20-20 verbatim
variable {ι : Type*} [DecidableEq ι]

-- @@ L21-21 verbatim
variable {R : Type*} [Ring R]

-- @@ L22-22 verbatim
variable {A : Subring R}


-- @@ L24-28 verbatim
@[simp]
lemma Subtype.val_comp_single (i : ι) (a : A) :
    Subtype.val ∘ Pi.single i a = Pi.single i a := by
  ext j
  by_cases h : i = j <;> aesop


-- @@ L30-30 verbatim
omit [DecidableEq ι]

-- @@ L31-35 verbatim
@[simp]
lemma Subtype.val_comp_add (v w : ι → A) :
    Subtype.val ∘ (v + w) = Subtype.val ∘ v + Subtype.val ∘ w := by
  ext j
  simp


-- @@ L37-42 verbatim
@[simp]
lemma Subtype.val_comp_smul (a : A) (v : ι → A) :
    Subtype.val ∘ (a • v) = a • Subtype.val ∘ v := by
  ext j
  simp
  rfl


-- @@ L44-44 verbatim
section


-- @@ L46-46 verbatim
variable {K : Type*} [Field K]

-- @@ L47-47 verbatim
variable {R : Subring K} [IsFractionRing R K]


-- @@ L49-55 verbatim
lemma Module.Basis.linearIndependent_of_submodule {κ : Type*} {M : Submodule R (ι → K)}
    (b : Basis κ R M) :
    LinearIndependent K (fun i ↦ (b i).val) := by
  rw [← LinearIndependent.iff_fractionRing (R := R), linearIndependent_iff']
  intro s g hs
  simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
  exact linearIndependent_iff'.mp b.linearIndependent s g hs


-- @@ L57-57 verbatim
end
