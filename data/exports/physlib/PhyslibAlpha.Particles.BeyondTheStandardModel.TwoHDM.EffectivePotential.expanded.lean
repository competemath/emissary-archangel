/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.Module
public import Mathlib.RingTheory.MvPolynomial.Tower

-- @@ L11-36 verbatim
/-!
# The effective potential of the two Higgs doublet model

## i. Overview

An *effective potential* of the two Higgs doublet model is a real-valued function
`V : TwoHiggsDoublet → ℝ` of the field configuration. This file introduces the two physical
properties of such a potential used when expressing it through the gauge-invariant bilinears:

* `IsInvariant V` — invariance under the global gauge group, and
* `HasMaxMassDimLE V n` — being a polynomial in the field components of mass dimension `≤ n`.

## ii. Key results

* `EffectivePotential` — the type of effective potentials.
* `IsInvariant` — gauge invariance of a potential.
* `HasMaxMassDimLE` — being a bounded-degree polynomial in the field components.
* `HasMaxMassDimLE.exists_comp_linear_poly` — a polynomial potential, restricted along any
  real-linear parametrisation of configurations, is a polynomial in the parameters.

## iii. Table of contents

* A. The effective potential and its gauge invariance
* B. Maximum mass dimension

-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
namespace TwoHiggsDoublet

-- @@ L43-43 verbatim
open InnerProductSpace

-- @@ L44-44 verbatim
open StandardModel


-- @@ L46-47 verbatim
/-- A general potential of the Higgs field. -/
abbrev EffectivePotential : Type := TwoHiggsDoublet → ℝ


-- @@ L49-49 verbatim
namespace EffectivePotential


-- @@ L51-53 verbatim
/-!
## A. The effective potential and its gauge invariance
-/


-- @@ L55-58 verbatim
/-- The proposition that the general potential is invariant under
  the global action of the gauge group. -/
def IsInvariant (V : EffectivePotential) : Prop :=
  ∀ (g : GaugeGroupI), ∀ (φ : TwoHiggsDoublet), V (g • φ) = V φ


-- @@ L60-62 verbatim
/-!
## B. Maximum mass dimension
-/


-- @@ L64-68 verbatim
/-- The proposition that the potential `V` has a maximum mass dimension
  less then or equal to `n` - also implying it is a polynomial. -/
def HasMaxMassDimLE (V : EffectivePotential) (n : ℕ) : Prop :=
  ∃ p : MvPolynomial (Module.Dual ℝ TwoHiggsDoublet) ℝ, (∀ φ : TwoHiggsDoublet, V φ = p.eval
   (fun i => i φ) ) ∧ p.totalDegree ≤ n


-- @@ L70-94 verbatim
/-- A polynomial potential, restricted along any real-linear parametrisation `L` of field
  configurations, is a genuine polynomial in the parameters. This is the bookkeeping that lets the
  potential be evaluated on the field components of a gauge slice. -/
lemma HasMaxMassDimLE.exists_comp_linear_poly {V : EffectivePotential} {n : ℕ}
    (h : HasMaxMassDimLE V n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →ₗ[ℝ] TwoHiggsDoublet) :
    ∃ P : MvPolynomial ι ℝ, ∀ a : ι → ℝ, V (L a) = P.eval a := by
  obtain ⟨p, hp, -⟩ := h
  refine ⟨MvPolynomial.aeval
    (fun i => ∑ k : ι, MvPolynomial.C (i (L (Pi.single k 1))) * MvPolynomial.X k) p, fun a => ?_⟩
  have key : (fun i : Module.Dual ℝ TwoHiggsDoublet => i (L a))
      = fun i => MvPolynomial.eval a
        (∑ k : ι, MvPolynomial.C (i (L (Pi.single k 1))) * MvPolynomial.X k) := by
    funext i
    have ha : a = ∑ k : ι, a k • (Pi.single k 1 : ι → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    rw [map_sum]
    conv_lhs => rw [ha, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, map_smul, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      smul_eq_mul, mul_comm]
  rw [hp, key, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq, ← MvPolynomial.eval_assoc]
  rfl


-- @@ L96-96 verbatim
end EffectivePotential


-- @@ L98-98 verbatim
end TwoHiggsDoublet
