/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.EffectivePotential
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Degrees

-- @@ L11-38 verbatim
/-!
# Swapping the two Higgs doublets

## i. Overview

Exchanging the two doublets `Φ1 ↔ Φ2` is an `ℝ`-linear map `swapDoublet` that commutes with the
gauge action. It therefore preserves gauge invariance and the maximum mass dimension, while turning
the alignment of `Φ1` into the alignment of `Φ2`. This is precisely the symmetry used to clear the
`‖Φ2‖²` factor when writing the potential through the gauge invariants, mirroring the `‖Φ1‖²`
clearing.

## ii. Key results

* `swapDoublet` — the doublet exchange, as an `ℝ`-linear map.
* `swapDoublet_smul` — it commutes with the gauge action.
* `gramVector_swapDoublet_*` — its effect on the Gram vector (a sign flip on the imaginary and
  difference components).
* `IsInvariant.comp_swapDoublet`, `HasMaxMassDimLE.comp_swapDoublet` — it preserves gauge invariance
  and bounded mass dimension.

## iii. Table of contents

* A. The doublet-swap map and its components
* B. Commutation with the gauge action
* C. The action on the Gram vector
* D. Effect on gauge invariance and mass dimension

-/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
namespace TwoHiggsDoublet

-- @@ L45-45 verbatim
open InnerProductSpace

-- @@ L46-46 verbatim
open StandardModel


-- @@ L48-48 verbatim
namespace EffectivePotential


-- @@ L50-52 verbatim
/-!
## A. The doublet-swap map and its components
-/


-- @@ L54-60 verbatim
/-- Swapping the two doublets, as an `ℝ`-linear map. It commutes with the gauge action, so it sends
  gauge-invariant polynomial potentials to gauge-invariant polynomial potentials, but turns the
  alignment of `Φ1` into the alignment of `Φ2`. -/
def swapDoublet : TwoHiggsDoublet →ₗ[ℝ] TwoHiggsDoublet where
  toFun φ := { Φ1 := φ.Φ2, Φ2 := φ.Φ1 }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L62-62 verbatim
@[simp] lemma swapDoublet_Φ1 (φ : TwoHiggsDoublet) : (swapDoublet φ).Φ1 = φ.Φ2 := rfl

-- @@ L63-63 verbatim
@[simp] lemma swapDoublet_Φ2 (φ : TwoHiggsDoublet) : (swapDoublet φ).Φ2 = φ.Φ1 := rfl


-- @@ L65-66 verbatim
@[simp] lemma swapDoublet_swapDoublet (φ : TwoHiggsDoublet) : swapDoublet (swapDoublet φ) = φ := by
  apply ext_of_fst_snd <;> rfl


-- @@ L68-70 verbatim
/-!
## B. Commutation with the gauge action
-/


-- @@ L72-74 verbatim
lemma swapDoublet_smul (g : StandardModel.GaugeGroupI) (φ : TwoHiggsDoublet) :
    swapDoublet (g • φ) = g • swapDoublet φ := by
  apply ext_of_fst_snd <;> simp


-- @@ L76-78 verbatim
/-!
## C. The action on the Gram vector
-/


-- @@ L80-84 verbatim
/-- Swapping the doublets sends the gram vector through the sign flip of the imaginary and
  difference components. -/
lemma gramVector_swapDoublet_inl (φ : TwoHiggsDoublet) :
    (swapDoublet φ).gramVector (Sum.inl 0) = φ.gramVector (Sum.inl 0) := by
  rw [gramVector_inl_zero_eq, gramVector_inl_zero_eq, swapDoublet_Φ1, swapDoublet_Φ2]; ring


-- @@ L86-89 verbatim
lemma gramVector_swapDoublet_inr0 (φ : TwoHiggsDoublet) :
    (swapDoublet φ).gramVector (Sum.inr 0) = φ.gramVector (Sum.inr 0) := by
  rw [gramVector_inr_zero_eq, gramVector_inr_zero_eq, swapDoublet_Φ1, swapDoublet_Φ2,
    ← inner_conj_symm, Complex.conj_re]


-- @@ L91-94 verbatim
lemma gramVector_swapDoublet_inr1 (φ : TwoHiggsDoublet) :
    (swapDoublet φ).gramVector (Sum.inr 1) = -φ.gramVector (Sum.inr 1) := by
  rw [gramVector_inr_one_eq, gramVector_inr_one_eq, swapDoublet_Φ1, swapDoublet_Φ2,
    ← inner_conj_symm, Complex.conj_im]; ring


-- @@ L96-98 verbatim
lemma gramVector_swapDoublet_inr2 (φ : TwoHiggsDoublet) :
    (swapDoublet φ).gramVector (Sum.inr 2) = -φ.gramVector (Sum.inr 2) := by
  rw [gramVector_inr_two_eq, gramVector_inr_two_eq, swapDoublet_Φ1, swapDoublet_Φ2]; ring


-- @@ L100-102 verbatim
/-!
## D. Effect on gauge invariance and mass dimension
-/


-- @@ L104-111 verbatim
lemma HasMaxMassDimLE.comp_swapDoublet {V : EffectivePotential} {n : ℕ}
    (h : HasMaxMassDimLE V n) : HasMaxMassDimLE (fun φ => V (swapDoublet φ)) n := by
  obtain ⟨p, hp, hdeg⟩ := h
  refine ⟨MvPolynomial.rename
    (fun i : Module.Dual ℝ TwoHiggsDoublet => i.comp swapDoublet) p, fun φ => ?_, ?_⟩
  · change V (swapDoublet φ) = _
    rw [MvPolynomial.eval_rename, hp (swapDoublet φ)]; rfl
  · exact le_trans (MvPolynomial.totalDegree_rename_le _ _) hdeg


-- @@ L113-117 verbatim
lemma IsInvariant.comp_swapDoublet {V : EffectivePotential} (hI : IsInvariant V) :
    IsInvariant (fun φ => V (swapDoublet φ)) := by
  intro g φ
  show V (swapDoublet (g • φ)) = V (swapDoublet φ)
  rw [swapDoublet_smul, hI g]


-- @@ L119-119 verbatim
end EffectivePotential


-- @@ L121-121 verbatim
end TwoHiggsDoublet
