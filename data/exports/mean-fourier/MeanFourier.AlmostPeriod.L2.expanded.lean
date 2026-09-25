/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.CovBySMul
public import MeanFourier.InvtMean.Defs


-- @@ L11-13 verbatim
/-!
# L^2(m)
-/


-- @@ L15-15 verbatim
public section


-- @@ L17-17 verbatim
open scoped ComplexOrder Indicator Pointwise


-- @@ L19-19 verbatim
namespace InvtMean

-- @@ L20-21 verbatim
variable {G : Type*} [Group G] {m : InvtMean G ℂ ℂ} {f : G → ℂ} {A : Set G} {t : G} {K : ℝ → ℝ}
  {ε : ℝ}


-- @@ L23-24 verbatim
variable (m f ε) in
def l2AP : Set G := {t | m.l2Norm ((fun g ↦ f (t⁻¹ * g)) - f) ≤ ε * m.l2Norm f}


-- @@ L26-26 verbatim
notation3 "AP_L^2(" m ")(" f ", " ε ")" => l2AP m f ε


-- @@ L28-29 expanded
@[simp]
lemma mem_l2AP : t ∈ l2AP m f ε ↔ m.l2Norm ((fun g ↦ f (t⁻¹ * g)) - f) ≤ ε * m.l2Norm f :=
  .rfl


-- @@ L31-34 expanded
@[simp high]
lemma mem_l2AP_indicator_one : t ∈ l2AP m 𝟭_[A] ε ↔ m (|𝟭_[t • A] - 𝟭_[A]|) ≤ ε ^ 2 * m 𝟭_[A] := by
  sorry


-- @@ L36-37 expanded
variable (m K f) in
def IsL2APWith : Prop :=
  ∀ ε > 0, CovBySMul G (K ε) .univ (l2AP m f ε)


-- @@ L39-39 verbatim
end InvtMean
