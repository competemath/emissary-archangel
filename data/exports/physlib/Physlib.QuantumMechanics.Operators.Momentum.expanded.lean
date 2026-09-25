/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
public import Physlib.QuantumMechanics.PlanckConstant
public import Physlib.SpaceAndTime.Space.Derivatives.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star

-- @@ L13-40 verbatim
/-!

# Momentum operators

## i. Overview

In this module we introduce several momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `momentumCLM` : (components of) the momentum vector operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `-iℏ∂ᵢ`.
- `momentumOperator` : a symmetric unbounded operator acting on the Schwartz submodule
    of the Hilbert space `SpaceDHilbertSpace d`.

Notation:
- `𝐩` for `momentumOperator`

## iii. Table of contents

- A. Momentum vector operator
- B. Unbounded momentum vector operator

## iv. References

* None.
-/


-- @@ L42-42 verbatim
TODO "Extend the domain of the momentum operator to the Sobolev space `H¹`."


-- @@ L44-44 verbatim
TODO "Prove that the momentum operator is self-adjoint (relies on 15310236534648318597)."


-- @@ L46-46 verbatim
@[expose] public section


-- @@ L48-48 verbatim
namespace QuantumMechanics

-- @@ L49-49 verbatim
noncomputable section

-- @@ L50-50 verbatim
open Constants Complex

-- @@ L51-51 verbatim
open Space

-- @@ L52-52 verbatim
open ContDiff SchwartzMap


-- @@ L54-54 verbatim
variable {d : ℕ} (i : Fin d)


-- @@ L56-60 verbatim
/-!

## A. Momentum vector operator

-/


-- @@ L62-66 verbatim
/-- Component `i` of the momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`. -/
def momentumCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (- Complex.I * ℏ) • (SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ∘L
    (SchwartzMap.fderivCLM ℂ (Space d) ℂ)


-- @@ L68-69 verbatim
@[inherit_doc momentumCLM]
notation "𝐩" => momentumCLM


-- @@ L71-72 verbatim
@[inherit_doc momentumCLM]
notation "𝐩[" d' "]" => momentumCLM (d := d')


-- @@ L74-74 expanded
lemma momentumCLM_apply_fun (ψ : 𝓢(Space d, ℂ)) : momentumCLM i ψ = (-I * ℏ) • (deriv i) ψ :=
  rfl


-- @@ L76-78 expanded
@[simp]
lemma momentumCLM_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    momentumCLM i ψ x = -I * ℏ * (deriv i) ψ x :=
  rfl


-- @@ L80-84 verbatim
/-!

## B. Unbounded momentum vector operator

-/


-- @@ L86-86 verbatim
open LinearPMap

-- @@ L87-87 verbatim
open MeasureTheory

-- @@ L88-88 verbatim
open SpaceDHilbertSpace

-- @@ L89-89 verbatim
open SchwartzSubmodule


-- @@ L91-94 expanded
/-- The momentum operator as a LinearPMap with domain the Schwartz submodule. -/
def momentumOperator : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d
    where
  domain := SchwartzSubmodule d
  toFun := (schwartzIncl volume).1 ∘ₗ (momentumCLM i).1 ∘ₗ (schwartzEquiv volume).symm.1


-- @@ L96-97 verbatim
@[inherit_doc momentumOperator]
notation "𝓟" => momentumOperator


-- @@ L99-100 expanded
lemma momentumOperator_apply (ψ : SchwartzSubmodule d) :
    momentumOperator i ψ = schwartzEquiv volume (momentumCLM i ((schwartzEquiv volume).symm ψ)) :=
  rfl


-- @@ L102-104 expanded
lemma momentumOperator_apply_ae (ψ : SchwartzSubmodule d) :
    momentumOperator i ψ =ᵐ[volume] momentumCLM i ((schwartzEquiv volume).symm ψ) :=
  schwartzEquiv_coe_ae _


-- @@ L106-107 expanded
lemma momentumOperator_range (ψ : SchwartzSubmodule d) :
    momentumOperator i ψ ∈ SchwartzSubmodule d := by simp [momentumOperator_apply]


-- @@ L109-109 expanded
lemma momentumOperator_hasDenseDomain : (momentumOperator i).HasDenseDomain :=
  SchwartzSubmodule.dense d _


-- @@ L111-138 expanded
lemma momentumOperator_isSymmetric : (momentumOperator i).IsSymmetric :=
  by
  intro ψ φ
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  obtain ⟨g, rfl⟩ := (schwartzEquiv volume).surjective φ
  simp only [momentumOperator_apply, ← Submodule.coe_inner, schwartzEquiv_inner,
    (schwartzEquiv volume).symm_apply_apply, momentumCLM_apply]
  have heq : ∀ x, fderiv ℝ (star ∘ f) x = (starL' ℝ).toContinuousLinearMap ∘L (fderiv ℝ f x) :=
    fun _ ↦ fderiv_star
  have hI₁ : Integrable fun x ↦ star (f x) := (starL' ℝ).integrable_comp_iff.mpr f.integrable
  have hI₂ : Integrable fun x ↦ fderiv ℝ g x (basis i) * star (f x) :=
    by
    refine hI₁.mul_of_top_right ?_
    exact ((g.fderivCLM ℂ _ _).evalCLM ℂ _ _ _).memLp_top
  have hI₃ : Integrable fun x ↦ g x * fderiv ℝ (star ∘ f) x (basis i) :=
    by
    simp_rw [heq]
    refine Integrable.mul_of_top_right ?_ g.memLp_top
    apply (starL' ℝ).integrable_comp_iff.mpr
    exact ((f.fderivCLM ℂ _ _).evalCLM ℂ _ _ _).integrable
  have hI₄ : Integrable fun x ↦ g x * star (f x) := hI₁.mul_of_top_right g.memLp_top
  trans I * ℏ * ∫ x, g x * fderiv ℝ (star ∘ f) x (basis i)
  · simp_rw [← integral_const_mul_of_integrable hI₃, heq]
    simp [mul_comm, mul_left_comm, Space.deriv_eq]
  symm
  trans I * ℏ * -∫ x, fderiv ℝ (⇑g) x (basis i) * star (f x)
  · rw [mul_neg, ← neg_mul, ← integral_const_mul_of_integrable hI₂]
    simp [mul_left_comm, mul_comm, Space.deriv_eq]
  symm
  congr 2
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI₂ hI₃ hI₄ (by fun_prop) (by fun_prop)


-- @@ L140-143 expanded
lemma momentumOperator_isUnbounded : (momentumOperator i).IsUnbounded :=
  by
  refine (LinearPMap.IsSymmetric.isUnbounded_iff_hasDenseDomain ?_).mpr ?_
  · exact momentumOperator_isSymmetric i
  · exact momentumOperator_hasDenseDomain i


-- @@ L145-147 expanded
/-- The square of the momentum operator. -/
def momentumSqOperator : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  sum fun i ↦ (momentumOperator i).comp (momentumOperator i) (momentumOperator_range i)


-- @@ L149-150 expanded
lemma momentumSqOperator_eq :
    momentumSqOperator (d := d) =
      sum fun i ↦ (momentumOperator i).comp (momentumOperator i) (momentumOperator_range i) :=
  rfl


-- @@ L152-158 verbatim
lemma momentumSqOperator_domain_eq : momentumSqOperator.domain = SchwartzSubmodule d := by
  rw [momentumSqOperator_eq, sum_domain]
  rcases eq_zero_or_pos d with rfl | hd
  · simp [SchwartzSubmodule.zero_eq_top]
  · let := Fin.pos_iff_nonempty.mp hd
    rw [← iInf_const (a := SchwartzSubmodule d) (ι := Fin d)]
    congr


-- @@ L160-160 verbatim
end

-- @@ L161-161 verbatim
end QuantumMechanics
