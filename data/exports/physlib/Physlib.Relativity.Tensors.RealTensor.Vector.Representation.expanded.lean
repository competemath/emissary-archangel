/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Physlib.Relativity.LorentzGroup.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic

-- @@ L11-19 verbatim
/-!

# Representation of the Lorentz group on Lorentz vectors

In this module we define the representation of the Lorentz group on Lorentz vectors.
This does not define the MulAction on `Lorentz.Vector`, which is induced
by its tensor structure.

-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
open Module Matrix MatrixGroups Complex TensorProduct


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace Lorentz


-- @@ L30-30 verbatim
namespace Vector

-- @@ L31-31 verbatim
attribute [-simp] Fintype.sum_sum_type


-- @@ L33-37 verbatim
/-- The representation of the Lorentz group on Lorentz vectors. -/
def rep {d : ℕ} : Representation ℝ (LorentzGroup d) (Vector d) where
  toFun Λ := Matrix.toLinAlgEquiv basis Λ
  map_one' := EmbeddingLike.map_eq_one_iff.mpr rfl
  map_mul' x y := by simp only [lorentzGroupIsGroup_mul_coe, _root_.map_mul]


-- @@ L39-43 verbatim
/-!

## Properties of the representation.

-/


-- @@ L45-46 verbatim
lemma rep_apply_eq_mulVec (d : ℕ) (Λ : LorentzGroup d) (v : Vector d) :
    rep Λ v = Λ *ᵥ v := by rfl


-- @@ L48-49 verbatim
lemma rep_apply_eq_sum (d : ℕ) (Λ : LorentzGroup d) (v : Vector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, Λ.1 k j • v j := rfl


-- @@ L51-54 verbatim
lemma rep_apply_basis {d} (μ : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) :
    rep Λ (basis μ) = ∑ j, Λ.1 j μ • basis j := by
  ext k
  simp [rep_apply_eq_sum, apply_sum]


-- @@ L56-58 verbatim
lemma rep_toMatrix (d : ℕ) (Λ : LorentzGroup d) :
    LinearMap.toMatrix basis basis (rep Λ) = Λ.1 :=
  (LinearEquiv.eq_symm_apply (LinearMap.toMatrix basis basis)).mp rfl


-- @@ L60-61 verbatim
lemma rep_injective (d : ℕ) (Λ : LorentzGroup d) : Function.Injective (rep Λ) :=
  fun _ _ h => Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible Λ.1) h


-- @@ L63-64 verbatim
lemma rep_surjective (d : ℕ) (Λ : LorentzGroup d) : Function.Surjective (rep Λ) :=
  fun v => ⟨Λ⁻¹ *ᵥ v, by simp [rep_apply_eq_mulVec]⟩


-- @@ L66-67 verbatim
lemma rep_bijective (d : ℕ) (Λ : LorentzGroup d) : Function.Bijective (rep Λ) :=
  ⟨rep_injective d Λ, rep_surjective d Λ⟩


-- @@ L69-73 verbatim
@[fun_prop]
lemma rep_contDiff (d : ℕ) {n} (Λ : LorentzGroup d) : ContDiff ℝ n (rep Λ) := by
  refine (contDiff_apply _).mp fun μ => ?_
  simp only [rep_apply_eq_sum, smul_eq_mul]
  fun_prop


-- @@ L75-76 verbatim
lemma rep_left_injective (d : ℕ) : Function.Injective (rep (d := d)) :=
  fun _ _ h => LorentzGroup.eq_of_mulVec_eq (LinearMap.congr_fun h)


-- @@ L78-78 verbatim
end Vector


-- @@ L80-80 verbatim
end Lorentz
