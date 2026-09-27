/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic


-- @@ L10-15 verbatim
/-!
# Hölder bounds for the parabolic metric

This module names the seminorm used by the space-time regularity statements.
The measure-theoretic representative predicate records agreement on a set.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open scoped ENNReal NNReal Topology


-- @@ L21-21 verbatim
open MeasureTheory Set



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace CKN.Foundation.Parabolic


-- @@ L28-33 verbatim
/-- Pointwise Hölder seminorm bound with respect to parabolic distance. -/
def ParabolicHolderSeminormLE
    (U : Set ParabolicPoint) (g : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |g x - g y| ≤ K * parabolicDist x y ^ α


-- @@ L35-41 verbatim
/-- Existence of an a.e.-equal representative satisfying a parabolic Hölder bound. -/
def HasParabolicHolderRepresentativeOn
    (U : Set ParabolicPoint) (f : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∃ g : ParabolicPoint → ℝ,
    g =ᵐ[volume.restrict U] f ∧
      ParabolicHolderSeminormLE U g α K


-- @@ L43-45 verbatim
lemma parabolicDist_nonneg (x y : ParabolicPoint) :
    0 ≤ parabolicDist x y := by
  exact (vec3EuclideanNorm_nonneg _).trans (le_max_left _ _)


-- @@ L47-47 verbatim
namespace ParabolicHolderSeminormLE


-- @@ L49-52 verbatim
theorem mono_set {U V : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    {α K : ℝ} (h : ParabolicHolderSeminormLE U g α K) (hVU : V ⊆ U) :
    ParabolicHolderSeminormLE V g α K :=
  fun x hx y hy => h x (hVU hx) y (hVU hy)


-- @@ L54-54 verbatim
end ParabolicHolderSeminormLE


-- @@ L56-60 verbatim
theorem ParabolicHolderSeminormLE.hasRepresentative
    {U : Set ParabolicPoint} {f : ParabolicPoint → ℝ} {α K : ℝ}
    (h : ParabolicHolderSeminormLE U f α K) :
    HasParabolicHolderRepresentativeOn U f α K :=
  ⟨f, Filter.Eventually.of_forall fun _ => rfl, h⟩


-- @@ L62-62 verbatim
end CKN.Foundation.Parabolic
